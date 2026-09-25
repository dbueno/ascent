//! The default data structure provider for Ascent relations

macro_rules! _rel_type_template {
   ($field_types: ty, $indices: expr, $par: ident) => {};
}

macro_rules! _rel_ind_template {
   ($field_types: ty, $indices: expr, $par: ident, $ind: expr) => {};
}

#[doc(hidden)]
#[macro_export]
macro_rules! rel_codegen {
   ( $($tt: tt)* ) => { };
}
pub use rel_codegen;

#[doc(hidden)]
#[macro_export]
macro_rules! rel {
   ($name: ident, $field_types: ty, $indices: expr, ser, ()) => {
      ::std::vec::Vec<$field_types>
   };
   ($name: ident, $field_types: ty, $indices: expr, par, ()) => {
      ::ascent::boxcar::Vec<$field_types>
   };
}
pub use rel;

#[doc(hidden)]
#[macro_export]
macro_rules! rel_ind_common {
   ($name: ident, $field_types: ty, $indices: expr, ser, ()) => {
      ()
   };
   ($name: ident, $field_types: ty, $indices: expr, par, ()) => {
      ()
   };
}
pub use rel_ind_common;

#[doc(hidden)]
#[macro_export]
macro_rules! rel_full_ind {
   ($name: ident, $field_types: ty, $indices: expr, ser, (), $key: ty, $val: ty) => {
      ascent::internal::RelFullIndexType<$key, $val>
   };
   ($name: ident, $field_types: ty, $indices: expr, par, (), $key: ty, $val: ty) => {
      ascent::internal::CRelFullIndex<$key, $val>
   };
}
pub use rel_full_ind;

#[doc(hidden)]
#[macro_export]
macro_rules! rel_ind {
   ($name: ident, $field_types: ty, $indices: expr, ser, (), $ind: expr, $key: ty, $val: ty) => {
      ascent::rel::ToRelIndexType<$key, $val>
   };
   ($name: ident, $field_types: ty, $indices: expr, par, (), [], $key: ty, $val: ty) => {
      ascent::internal::CRelNoIndex<$val>
   };
   ($name: ident, $field_types: ty, $indices: expr, par, (), $ind: expr, $key: ty, $val: ty) => {
      ascent::internal::CRelIndex<$key, $val>
   };
}
pub use rel_ind;

// The macros below define the default data structure provider for `lattice` relations, used both for
// lattices without a `#[lds(..)]` attribute and for `#[lds(ascent::rel)]`. A lattice's rows live in the
// built-in row store, so a lattice provider only customizes the index types: `lat_full_ind!` yields the
// "full index" mapping the key columns (all but the lattice column) to the single row holding the joined
// value, and `lat_rel_ind!` yields every other (multi-valued, set-semantics) index. `$val` is always
// `usize` (a row reference).

#[doc(hidden)]
#[macro_export]
macro_rules! lat_full_ind {
   ($name: ident, $field_types: ty, $indices: expr, ser, (), $key: ty, $val: ty) => {
      ascent::internal::RelFullIndexType<$key, $val>
   };
   ($name: ident, $field_types: ty, $indices: expr, par, (), $key: ty, $val: ty) => {
      ascent::internal::CRelFullIndex<$key, $val>
   };
}
pub use lat_full_ind;

#[doc(hidden)]
#[macro_export]
macro_rules! lat_rel_ind {
   ($name: ident, $field_types: ty, $indices: expr, ser, (), $ind: expr, $key: ty, $val: ty) => {
      ascent::internal::LatticeIndexType<$key, $val>
   };
   ($name: ident, $field_types: ty, $indices: expr, par, (), [], $key: ty, $val: ty) => {
      ascent::internal::CRelNoIndex<$val>
   };
   ($name: ident, $field_types: ty, $indices: expr, par, (), $ind: expr, $key: ty, $val: ty) => {
      ascent::internal::CRelIndex<$key, $val>
   };
}
pub use lat_rel_ind;

// `lat_state!` is the type of a lattice `lds` provider's own state. One value of it is stored in the
// generated program struct per `#[lds(..)]` lattice, is never versioned or swapped by the fixpoint loop,
// and is handed to `lat_observe!` by shared reference — so a provider that wants to accumulate anything
// puts it here rather than in globals. In parallel Ascent it is shared across rayon worker threads, so it
// must be `Sync` and use interior mutability. The default provider keeps no state.
#[doc(hidden)]
#[macro_export]
macro_rules! lat_state {
   ($name: ident, $field_types: ty, $indices: expr, $par: tt, ()) => {
      ()
   };
}
pub use lat_state;

// `lat_observe!` is the hook through which a lattice `lds` provider sees each (key, lattice value) pair
// that actually enters the relation, separately from the index types (which only ever see a `usize` row
// reference). The default provider keeps no derived view, so this expands to nothing. `$par` is `ser` or
// `par`; `$state` is a shared reference to this relation's `lat_state!` value, and `$key` and `$val` are
// references to the key tuple and the (already joined) lattice value.
#[doc(hidden)]
#[macro_export]
macro_rules! lat_observe {
   ($name: ident, $field_types: ty, $indices: expr, $par: tt, (), $state: expr, $key: expr, $val: expr) => {};
}
pub use lat_observe;

#[derive(Clone)]
pub struct ToRelIndexType<K, V>(pub RelIndexType1<K, V>);

impl<K, V> Default for ToRelIndexType<K, V> {
   #[inline(always)]
   fn default() -> Self { Self(Default::default()) }
}

impl<K, V, R> ToRelIndex<R> for ToRelIndexType<K, V> {
   type RelIndex<'a>
      = &'a RelIndexType1<K, V>
   where
      Self: 'a,
      R: 'a;

   #[inline(always)]
   fn to_rel_index<'a>(&'a self, _rel: &'a R) -> Self::RelIndex<'a> { &self.0 }

   type RelIndexWrite<'a>
      = &'a mut RelIndexType1<K, V>
   where
      Self: 'a,
      R: 'a;

   #[inline(always)]
   fn to_rel_index_write<'a>(&'a mut self, _rel: &'a mut R) -> Self::RelIndexWrite<'a> { &mut self.0 }
}

use crate::internal::{Freezable, RelFullIndexType, RelIndexMerge, RelIndexType1};
use crate::to_rel_index::ToRelIndex;

impl<K, V, Rel> ToRelIndex<Rel> for RelIndexType1<K, V> {
   type RelIndex<'a>
      = &'a Self
   where
      Self: 'a,
      Rel: 'a;
   #[inline(always)]
   fn to_rel_index<'a>(&'a self, _rel: &'a Rel) -> Self::RelIndex<'a> { self }

   type RelIndexWrite<'a>
      = &'a mut Self
   where
      Self: 'a,
      Rel: 'a;
   #[inline(always)]
   fn to_rel_index_write<'a>(&'a mut self, _rel: &'a mut Rel) -> Self::RelIndexWrite<'a> { self }
}

impl<K, V, Rel> ToRelIndex<Rel> for RelFullIndexType<K, V> {
   type RelIndex<'a>
      = &'a Self
   where
      Self: 'a,
      Rel: 'a;
   #[inline(always)]
   fn to_rel_index<'a>(&'a self, _rel: &'a Rel) -> Self::RelIndex<'a> { self }

   type RelIndexWrite<'a>
      = &'a mut Self
   where
      Self: 'a,
      Rel: 'a;
   #[inline(always)]
   fn to_rel_index_write<'a>(&'a mut self, _rel: &'a mut Rel) -> Self::RelIndexWrite<'a> { self }
}

#[cfg(feature = "par")]
mod par {
   use crate::c_rel_full_index::CRelFullIndex;
   use crate::c_rel_index::CRelIndex;
   use crate::c_rel_no_index::CRelNoIndex;
   use crate::to_rel_index::ToRelIndex;

   impl<K, V, Rel> ToRelIndex<Rel> for CRelIndex<K, V> {
      type RelIndex<'a>
         = &'a Self
      where
         Self: 'a,
         Rel: 'a;
      #[inline(always)]
      fn to_rel_index<'a>(&'a self, _rel: &'a Rel) -> Self::RelIndex<'a> { self }

      type RelIndexWrite<'a>
         = &'a mut Self
      where
         Self: 'a,
         Rel: 'a;
      #[inline(always)]
      fn to_rel_index_write<'a>(&'a mut self, _rel: &'a mut Rel) -> Self::RelIndexWrite<'a> { self }
   }

   impl<V, Rel> ToRelIndex<Rel> for CRelNoIndex<V> {
      type RelIndex<'a>
         = &'a Self
      where
         Self: 'a,
         Rel: 'a;
      #[inline(always)]
      fn to_rel_index<'a>(&'a self, _rel: &'a Rel) -> Self::RelIndex<'a> { self }

      type RelIndexWrite<'a>
         = &'a mut Self
      where
         Self: 'a,
         Rel: 'a;
      #[inline(always)]
      fn to_rel_index_write<'a>(&'a mut self, _rel: &'a mut Rel) -> Self::RelIndexWrite<'a> { self }
   }

   impl<K, V, Rel> ToRelIndex<Rel> for CRelFullIndex<K, V> {
      type RelIndex<'a>
         = &'a Self
      where
         Self: 'a,
         Rel: 'a;
      #[inline(always)]
      fn to_rel_index<'a>(&'a self, _rel: &'a Rel) -> Self::RelIndex<'a> { self }

      type RelIndexWrite<'a>
         = &'a mut Self
      where
         Self: 'a,
         Rel: 'a;
      #[inline(always)]
      fn to_rel_index_write<'a>(&'a mut self, _rel: &'a mut Rel) -> Self::RelIndexWrite<'a> { self }
   }
}

impl RelIndexMerge for () {
   #[inline(always)]
   fn move_index_contents(_from: &mut Self, _to: &mut Self) {}

   #[inline(always)]
   fn merge_delta_to_total_new_to_delta(_new: &mut Self, _delta: &mut Self, _total: &mut Self) {}
}

impl Freezable for () {
   fn freeze(&mut self) {}
   fn unfreeze(&mut self) {}
}
