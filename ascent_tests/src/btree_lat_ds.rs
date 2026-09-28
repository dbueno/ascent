//! A lattice `#[lds(..)]` data structure provider whose indices are all backed by a single `BTreeMap`.
//!
//! It serves `lattice rel(Node, Node, L)` relations (e.g. `shortest_path(from, to, Dual<weight>)`). The
//! provider's `lat_ind_common!` value holds one `BTreeMap<(from, to), row>` per relation version, and every
//! index Ascent asks for is a zero-sized marker that answers its lookups from that map, through
//! `ToRelIndex`:
//!
//! - `[0, 1]`, the lattice full index (key columns to row): an exact `BTreeMap` lookup.
//! - `[0]`, rows by source node: a `BTreeMap` range query over the `(from, _)` prefix.
//! - `[]`, all rows: the map's values.
//! - `[0, 1, 2]`, the relation's all-columns index: never read by these programs, so it stores nothing.
//!
//! So however many indices Ascent derives for the relation, it holds exactly one data structure per
//! version, instead of one `HashMap` per index. A program that needs any other index (e.g. lookups by
//! destination) fails to compile, because `lat_rel_ind!` has no arm for it.

use std::collections::BTreeMap;
use std::collections::btree_map;
use std::marker::PhantomData;

use ascent::internal::{
   Freezable, LatIndCommon, RelIndexMerge, RelIndexRead, RelIndexReadAll, RelIndexWrite, ToRelIndex,
};

pub type Node = i32;
/// The key columns of the lattice: `(from, to)`.
pub type Key = (Node, Node);
/// Key columns to row index in the lattice's row store.
type Map = BTreeMap<Key, usize>;

/// The lattice full index `[0, 1]`.
#[derive(Default)]
pub struct ByKey;
/// The index `[0]`, by source node.
#[derive(Default)]
pub struct BySrc;
/// The index `[]`, over all rows.
#[derive(Default)]
pub struct All;
/// An index this provider never serves reads from (`[0, 1, 2]`); inserts into it are dropped. `K` is its
/// key type.
pub struct Unread<K>(PhantomData<fn() -> K>);

impl<K> Default for Unread<K> {
   fn default() -> Self { Unread(PhantomData) }
}

// The markers hold no data, so there is nothing to freeze (only parallel Ascent freezes indices).
impl Freezable for ByKey {}
impl Freezable for BySrc {}
impl Freezable for All {}
impl<K> Freezable for Unread<K> {}

// Lookups shared by the serial and parallel versions of the provider.

fn key_get<'a>(map: &'a Map, key: &Key) -> Option<std::option::IntoIter<&'a usize>> {
   map.get(key).map(|row| Some(row).into_iter())
}

type SrcIter<'a> = std::iter::Map<btree_map::Range<'a, Key, usize>, fn((&'a Key, &'a usize)) -> &'a usize>;

fn src_get<'a>(map: &'a Map, src: Node) -> Option<SrcIter<'a>> {
   fn row<'a>((_, row): (&'a Key, &'a usize)) -> &'a usize { row }
   let rows: SrcIter<'a> = map.range((src, Node::MIN)..=(src, Node::MAX)).map(row);
   if rows.clone().next().is_none() { None } else { Some(rows) }
}

/// Rows grouped by source node, in source order.
fn src_groups(map: &Map) -> Vec<(&Node, Vec<&usize>)> {
   let mut groups: Vec<(&Node, Vec<&usize>)> = vec![];
   for ((src, _), row) in map.iter() {
      match groups.last_mut() {
         Some((last, rows)) if *last == src => rows.push(row),
         _ => groups.push((src, vec![row])),
      }
   }
   groups
}

// ---------------------------------------------------------------------------------------------------------
// Serial Ascent
// ---------------------------------------------------------------------------------------------------------

/// The `lat_ind_common!` value in serial Ascent: the one data structure behind every index of a version.
#[derive(Default)]
pub struct Common {
   map: Map,
}

impl Common {
   /// The number of distinct keys stored, i.e. the number of rows of this version.
   pub fn len(&self) -> usize { self.map.len() }
}

impl RelIndexMerge for Common {
   fn move_index_contents(from: &mut Self, to: &mut Self) {
      // A key's row never moves, so a key present in both maps maps to the same row in each.
      to.map.append(&mut from.map);
   }
}

impl<L> LatIndCommon<Key, L> for Common {}

/// A read view of one index, backed by its version's map.
pub struct Read<'a, M>(&'a Map, PhantomData<M>);
/// A write view of one index, backed by its version's map.
pub struct Write<'a, M>(&'a mut Map, PhantomData<M>);

// Merging happens once, on `Common`; the views have nothing of their own to merge.
impl<M> RelIndexMerge for Write<'_, M> {
   fn move_index_contents(_from: &mut Self, _to: &mut Self) {}
   fn merge_delta_to_total_new_to_delta(_new: &mut Self, _delta: &mut Self, _total: &mut Self) {}
}

macro_rules! to_rel_index_via_common {
   ($([$($gen: tt)*] $marker: ty),*) => {$(
      impl<$($gen)*> ToRelIndex<Common> for $marker {
         type RelIndex<'a> = Read<'a, $marker> where Self: 'a, Common: 'a;
         fn to_rel_index<'a>(&'a self, common: &'a Common) -> Self::RelIndex<'a> { Read(&common.map, PhantomData) }

         type RelIndexWrite<'a> = Write<'a, $marker> where Self: 'a, Common: 'a;
         fn to_rel_index_write<'a>(&'a mut self, common: &'a mut Common) -> Self::RelIndexWrite<'a> {
            Write(&mut common.map, PhantomData)
         }
      }
   )*};
}
to_rel_index_via_common!([] ByKey, [] BySrc, [] All, [K] Unread<K>);

impl<'a> RelIndexRead<'a> for Read<'a, ByKey> {
   type Key = Key;
   type Value = &'a usize;
   type IteratorType = std::option::IntoIter<&'a usize>;
   fn index_get(&'a self, key: &Key) -> Option<Self::IteratorType> { key_get(self.0, key) }
   fn len_estimate(&'a self) -> usize { self.0.len() }
   fn is_empty(&'a self) -> bool { self.0.is_empty() }
}

impl<'a> RelIndexReadAll<'a> for Read<'a, ByKey> {
   type Key = &'a Key;
   type Value = &'a usize;
   type ValueIteratorType = std::option::IntoIter<&'a usize>;
   type AllIteratorType =
      std::iter::Map<btree_map::Iter<'a, Key, usize>, fn((&'a Key, &'a usize)) -> (&'a Key, Self::ValueIteratorType)>;
   fn iter_all(&'a self) -> Self::AllIteratorType {
      fn entry<'a>((key, row): (&'a Key, &'a usize)) -> (&'a Key, std::option::IntoIter<&'a usize>) {
         (key, Some(row).into_iter())
      }
      self.0.iter().map(entry)
   }
}

impl<'a> RelIndexRead<'a> for Read<'a, BySrc> {
   type Key = (Node,);
   type Value = &'a usize;
   type IteratorType = SrcIter<'a>;
   fn index_get(&'a self, key: &(Node,)) -> Option<Self::IteratorType> { src_get(self.0, key.0) }
   fn len_estimate(&'a self) -> usize { self.0.len() }
   fn is_empty(&'a self) -> bool { self.0.is_empty() }
}

impl<'a> RelIndexReadAll<'a> for Read<'a, BySrc> {
   type Key = (&'a Node,);
   type Value = &'a usize;
   type ValueIteratorType = std::vec::IntoIter<&'a usize>;
   type AllIteratorType = std::vec::IntoIter<((&'a Node,), Self::ValueIteratorType)>;
   fn iter_all(&'a self) -> Self::AllIteratorType {
      src_groups(self.0).into_iter().map(|(src, rows)| ((src,), rows.into_iter())).collect::<Vec<_>>().into_iter()
   }
}

impl<'a> RelIndexRead<'a> for Read<'a, All> {
   type Key = ();
   type Value = &'a usize;
   type IteratorType = btree_map::Values<'a, Key, usize>;
   fn index_get(&'a self, _key: &()) -> Option<Self::IteratorType> {
      if self.0.is_empty() { None } else { Some(self.0.values()) }
   }
   fn len_estimate(&'a self) -> usize { 1 }
   fn is_empty(&'a self) -> bool { self.0.is_empty() }
}

impl<'a> RelIndexReadAll<'a> for Read<'a, All> {
   type Key = &'a ();
   type Value = &'a usize;
   type ValueIteratorType = btree_map::Values<'a, Key, usize>;
   type AllIteratorType = std::option::IntoIter<(&'a (), Self::ValueIteratorType)>;
   fn iter_all(&'a self) -> Self::AllIteratorType {
      if self.0.is_empty() { None } else { Some((&(), self.0.values())) }.into_iter()
   }
}

impl RelIndexWrite for Write<'_, ByKey> {
   type Key = Key;
   type Value = usize;
   fn index_insert(&mut self, key: Key, row: usize) { self.0.insert(key, row); }
}

// Every row inserted into these indices is also inserted into the full index `[0, 1]`, i.e. into the map.
impl RelIndexWrite for Write<'_, BySrc> {
   type Key = (Node,);
   type Value = usize;
   fn index_insert(&mut self, _key: (Node,), _row: usize) {}
}

impl RelIndexWrite for Write<'_, All> {
   type Key = ();
   type Value = usize;
   fn index_insert(&mut self, _key: (), _row: usize) {}
}

impl<K> RelIndexWrite for Write<'_, Unread<K>> {
   type Key = K;
   type Value = usize;
   fn index_insert(&mut self, _key: K, _row: usize) {}
}

// ---------------------------------------------------------------------------------------------------------
// Parallel Ascent
// ---------------------------------------------------------------------------------------------------------

#[cfg(feature = "par")]
pub mod par {
   use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
   use std::marker::PhantomData;
   use std::sync::RwLock;

   use ascent::internal::{
      CLatFullIndexRead, CLatIndCommon, CRelIndexRead, CRelIndexReadAll, CRelIndexWrite, Freezable, RelIndexMerge,
      RelIndexRead, RelIndexReadAll, ToRelIndex,
   };
   use ascent::rayon::iter::IntoParallelIterator;

   use super::{All, ByKey, BySrc, Key, Map, Node, SrcIter, Unread, key_get, src_get, src_groups};

   /// The `lat_ind_common!` value in parallel Ascent. Rules only read frozen versions (delta and total) and
   /// only write the unfrozen one (new), so a frozen version's map is read without locking.
   #[derive(Default)]
   pub struct CCommon {
      unfrozen: RwLock<Map>,
      frozen: Option<Map>,
   }

   impl CCommon {
      /// The number of distinct keys stored, i.e. the number of rows of this version.
      pub fn len(&self) -> usize {
         match &self.frozen {
            Some(map) => map.len(),
            None => self.unfrozen.read().unwrap().len(),
         }
      }

      fn frozen_map(&self) -> &Map { self.frozen.as_ref().expect("btree_lat_ds: read of an unfrozen index") }

      fn thaw(&mut self) {
         if let Some(map) = self.frozen.take() {
            *self.unfrozen.get_mut().unwrap() = map;
         }
      }
   }

   impl Freezable for CCommon {
      fn freeze(&mut self) {
         if self.frozen.is_none() {
            self.frozen = Some(std::mem::take(self.unfrozen.get_mut().unwrap()));
         }
      }
      fn unfreeze(&mut self) { self.thaw() }
   }

   impl RelIndexMerge for CCommon {
      fn move_index_contents(from: &mut Self, to: &mut Self) {
         from.thaw();
         to.thaw();
         to.unfrozen.get_mut().unwrap().append(from.unfrozen.get_mut().unwrap());
      }
   }

   impl<L> CLatIndCommon<Key, L> for CCommon {}

   /// A view of one index, backed by its version's `CCommon`. Parallel Ascent reads and writes indices
   /// through the same view.
   pub struct CRead<'a, M>(&'a CCommon, PhantomData<M>);
   /// A mutable view of one index; only used to merge versions, which happens on `CCommon`, so it holds
   /// nothing.
   pub struct CWrite<'a, M>(PhantomData<(&'a mut CCommon, M)>);

   impl<M> RelIndexMerge for CWrite<'_, M> {
      fn move_index_contents(_from: &mut Self, _to: &mut Self) {}
      fn merge_delta_to_total_new_to_delta(_new: &mut Self, _delta: &mut Self, _total: &mut Self) {}
   }

   macro_rules! to_rel_index_via_c_common {
      ($([$($gen: tt)*] $marker: ty),*) => {$(
         impl<$($gen)*> ToRelIndex<CCommon> for $marker {
            type RelIndex<'a> = CRead<'a, $marker> where Self: 'a, CCommon: 'a;
            fn to_rel_index<'a>(&'a self, common: &'a CCommon) -> Self::RelIndex<'a> { CRead(common, PhantomData) }

            type RelIndexWrite<'a> = CWrite<'a, $marker> where Self: 'a, CCommon: 'a;
            fn to_rel_index_write<'a>(&'a mut self, _common: &'a mut CCommon) -> Self::RelIndexWrite<'a> {
               CWrite(PhantomData)
            }
         }
      )*};
   }
   to_rel_index_via_c_common!([] ByKey, [] BySrc, [] All, [K] Unread<K>);

   type ParRows<'a> = ascent::rayon::vec::IntoIter<&'a usize>;

   impl CLatFullIndexRead for CRead<'_, ByKey> {
      type Key = Key;
      type Value = usize;
      fn hash_usize(&self, key: &Key) -> usize { BuildHasherDefault::<DefaultHasher>::default().hash_one(key) as usize }
      fn get_cloned(&self, key: &Key) -> Option<usize> {
         match &self.0.frozen {
            Some(map) => map.get(key).copied(),
            None => self.0.unfrozen.read().unwrap().get(key).copied(),
         }
      }
   }

   impl CRelIndexWrite for CRead<'_, ByKey> {
      type Key = Key;
      type Value = usize;
      fn index_insert(&self, key: Key, row: usize) {
         assert!(self.0.frozen.is_none(), "btree_lat_ds: write to a frozen index");
         self.0.unfrozen.write().unwrap().insert(key, row);
      }
   }

   impl CRelIndexWrite for CRead<'_, BySrc> {
      type Key = (Node,);
      type Value = usize;
      fn index_insert(&self, _key: (Node,), _row: usize) {}
   }

   impl CRelIndexWrite for CRead<'_, All> {
      type Key = ();
      type Value = usize;
      fn index_insert(&self, _key: (), _row: usize) {}
   }

   impl<K> CRelIndexWrite for CRead<'_, Unread<K>> {
      type Key = K;
      type Value = usize;
      fn index_insert(&self, _key: K, _row: usize) {}
   }

   // Serial reads, used by parallel Ascent for the inner loops of a rule.

   impl<'a> RelIndexRead<'a> for CRead<'a, ByKey> {
      type Key = Key;
      type Value = &'a usize;
      type IteratorType = std::option::IntoIter<&'a usize>;
      fn index_get(&'a self, key: &Key) -> Option<Self::IteratorType> { key_get(self.0.frozen_map(), key) }
      fn len_estimate(&'a self) -> usize { self.0.len() }
   }

   impl<'a> RelIndexRead<'a> for CRead<'a, BySrc> {
      type Key = (Node,);
      type Value = &'a usize;
      type IteratorType = SrcIter<'a>;
      fn index_get(&'a self, key: &(Node,)) -> Option<Self::IteratorType> { src_get(self.0.frozen_map(), key.0) }
      fn len_estimate(&'a self) -> usize { self.0.len() }
   }

   impl<'a> RelIndexReadAll<'a> for CRead<'a, BySrc> {
      type Key = (&'a Node,);
      type Value = &'a usize;
      type ValueIteratorType = std::vec::IntoIter<&'a usize>;
      type AllIteratorType = std::vec::IntoIter<((&'a Node,), Self::ValueIteratorType)>;
      fn iter_all(&'a self) -> Self::AllIteratorType {
         let groups = src_groups(self.0.frozen_map());
         groups.into_iter().map(|(src, rows)| ((src,), rows.into_iter())).collect::<Vec<_>>().into_iter()
      }
   }

   impl<'a> RelIndexRead<'a> for CRead<'a, All> {
      type Key = ();
      type Value = &'a usize;
      type IteratorType = std::collections::btree_map::Values<'a, Key, usize>;
      fn index_get(&'a self, _key: &()) -> Option<Self::IteratorType> {
         let map = self.0.frozen_map();
         if map.is_empty() { None } else { Some(map.values()) }
      }
      fn len_estimate(&'a self) -> usize { 1 }
   }

   // Parallel reads, used by parallel Ascent for the outer loops of a rule.

   impl<'a> CRelIndexRead<'a> for CRead<'a, ByKey> {
      type Key = Key;
      type Value = &'a usize;
      type IteratorType = ParRows<'a>;
      fn c_index_get(&'a self, key: &Key) -> Option<Self::IteratorType> {
         key_get(self.0.frozen_map(), key).map(|rows| rows.collect::<Vec<_>>().into_par_iter())
      }
   }

   impl<'a> CRelIndexRead<'a> for CRead<'a, BySrc> {
      type Key = (Node,);
      type Value = &'a usize;
      type IteratorType = ParRows<'a>;
      fn c_index_get(&'a self, key: &(Node,)) -> Option<Self::IteratorType> {
         src_get(self.0.frozen_map(), key.0).map(|rows| rows.collect::<Vec<_>>().into_par_iter())
      }
   }

   impl<'a> CRelIndexReadAll<'a> for CRead<'a, BySrc> {
      type Key = (&'a Node,);
      type Value = &'a usize;
      type ValueIteratorType = ParRows<'a>;
      type AllIteratorType = ascent::rayon::vec::IntoIter<((&'a Node,), ParRows<'a>)>;
      fn c_iter_all(&'a self) -> Self::AllIteratorType {
         let groups = src_groups(self.0.frozen_map());
         groups.into_iter().map(|(src, rows)| ((src,), rows.into_par_iter())).collect::<Vec<_>>().into_par_iter()
      }
   }

   impl<'a> CRelIndexRead<'a> for CRead<'a, All> {
      type Key = ();
      type Value = &'a usize;
      type IteratorType = ParRows<'a>;
      fn c_index_get(&'a self, _key: &()) -> Option<Self::IteratorType> {
         let map = self.0.frozen_map();
         if map.is_empty() { None } else { Some(map.values().collect::<Vec<_>>().into_par_iter()) }
      }
   }
}

#[macro_export]
macro_rules! btree_lat_ds_rel_codegen {
   ($($tt: tt)*) => {};
}
pub use btree_lat_ds_rel_codegen as rel_codegen;

#[macro_export]
macro_rules! btree_lat_ds_lat_ind_common {
   ($name: ident, $ft: ty, $indices: expr, ser, ()) => {
      $crate::btree_lat_ds::Common
   };
   ($name: ident, $ft: ty, $indices: expr, par, ()) => {
      $crate::btree_lat_ds::par::CCommon
   };
}
pub use btree_lat_ds_lat_ind_common as lat_ind_common;

#[macro_export]
macro_rules! btree_lat_ds_lat_full_ind {
   ($name: ident, $ft: ty, $indices: expr, $par: tt, (), $key: ty, $val: ty) => {
      $crate::btree_lat_ds::ByKey
   };
}
pub use btree_lat_ds_lat_full_ind as lat_full_ind;

#[macro_export]
macro_rules! btree_lat_ds_lat_rel_ind {
   ($name: ident, $ft: ty, $indices: expr, $par: tt, (), [0], $key: ty, $val: ty) => {
      $crate::btree_lat_ds::BySrc
   };
   ($name: ident, $ft: ty, $indices: expr, $par: tt, (), [], $key: ty, $val: ty) => {
      $crate::btree_lat_ds::All
   };
   ($name: ident, $ft: ty, $indices: expr, $par: tt, (), [0, 1, 2], $key: ty, $val: ty) => {
      $crate::btree_lat_ds::Unread<$key>
   };
}
pub use btree_lat_ds_lat_rel_ind as lat_rel_ind;
