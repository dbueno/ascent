#![cfg(test)]
#![allow(irrefutable_let_patterns)]
use std::cmp::max;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Deref;
use std::primitive;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Duration;

use LambdaCalcExpr::*;
use ascent::{Dual, ascent, ascent_run};
use itertools::Itertools;

use crate::ascent_maybe_par::{lat_from_vec, lat_to_vec};
use crate::utils::*;
use crate::{ascent_m_par, ascent_run_m_par, assert_rels_eq};

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum LambdaCalcExpr {
   Ref(&'static str),
   Lam(&'static str, Arc<LambdaCalcExpr>),
   App(Arc<LambdaCalcExpr>, Arc<LambdaCalcExpr>),
}

impl LambdaCalcExpr {
   #[allow(dead_code)]
   fn depth(&self) -> usize {
      match self {
         LambdaCalcExpr::Ref(_) => 0,
         LambdaCalcExpr::Lam(_x, b) => 1 + b.depth(),
         LambdaCalcExpr::App(f, e) => 1 + max(f.depth(), e.depth()),
      }
   }
}
fn app(f: LambdaCalcExpr, a: LambdaCalcExpr) -> LambdaCalcExpr { App(Arc::new(f), Arc::new(a)) }
fn lam(x: &'static str, e: LambdaCalcExpr) -> LambdaCalcExpr { Lam(x, Arc::new(e)) }

fn sub(exp: &LambdaCalcExpr, var: &str, e: &LambdaCalcExpr) -> LambdaCalcExpr {
   match exp {
      Ref(x) if *x == var => e.clone(),
      Ref(_x) => exp.clone(),
      App(ef, ea) => app(sub(ef, var, e), sub(ea, var, e)),
      Lam(x, _eb) if *x == var => exp.clone(),
      Lam(x, eb) => lam(x, sub(eb, var, e)),
   }
}

#[allow(non_snake_case)]
fn U() -> LambdaCalcExpr { lam("x", app(Ref("x"), Ref("x"))) }
#[allow(non_snake_case)]
fn I() -> LambdaCalcExpr { lam("x", Ref("x")) }

#[test]
fn test_dl_lambda() {
   ascent_m_par! {
      relation output(LambdaCalcExpr);
      relation input(LambdaCalcExpr);
      relation eval(LambdaCalcExpr, LambdaCalcExpr);
      relation do_eval(LambdaCalcExpr);

      input(app(U(), I()));
      do_eval(exp.clone()) <-- input(exp);
      output(res.clone()) <-- input(exp), eval(exp, res);

      eval(exp.clone(), exp.clone()) <-- do_eval(?exp @Ref(_));

      eval(exp.clone(), exp.clone()) <-- do_eval(?exp @Lam(_,_));

      do_eval(ef.as_ref().clone()) <-- do_eval(?App(ef,_ea));

      do_eval(sub(fb, fx, ea)) <--
         do_eval(?App(ef, ea)),
         eval(ef.deref(), ?Lam(fx, fb));

      eval(exp.clone(), final_res.clone()) <--
         do_eval(?exp @ App(ef, ea)), // this requires nightly
         eval(ef.deref(), ?Lam(fx, fb)),
         eval(sub(fb, fx, ea), final_res);
   };

   let mut prog = AscentProgram::default();
   // println!("{}", AscentProgram::summary());
   prog.run();
   // println!("input:{:?}\n", prog.input);
   // println!("eval: {}\n", prog.eval.iter().map(|(e,v)| format!("{:?} ===> {:?}", e, v)).join("\n"));
   println!("output: {:?}", prog.output);
   assert!(prog.output.iter().contains(&(I(),)));
   assert!(prog.output.len() == 1);
}

#[allow(dead_code)]
fn _test_dl_lambda2() {
   type Time = u32;
   type Addr = u32;
   #[derive(Clone, Hash, PartialEq, Eq, Debug)]
   enum Storable {
      Value(LambdaCalcExpr, Env),
      Kont(Continuation),
   }
   use Storable::*;
   #[derive(Clone, Hash, PartialEq, Eq, Debug)]
   enum Continuation {
      Fn(LambdaCalcExpr, Env, Addr),
      Ar(LambdaCalcExpr, Env, Addr),
   }
   use Continuation::*;
   type Env = Rc<BTreeMap<&'static str, Addr>>;
   fn tick(_t: &Time, _k: &Continuation) -> Time { todo!() }
   fn alloc(_e: &LambdaCalcExpr, _ρ: &Env, _a: &Addr, _t: &Time, _k: &Continuation) -> Addr { todo!() }
   fn upd(ρ: &Env, var: &'static str, addr: Addr) -> Env {
      let mut ρ = ρ.deref().clone();
      ρ.insert(var, addr);
      Rc::new(ρ)
   }
   // #[derive(Clone, Hash, PartialEq, Eq)]
   // struct State(LambdaCalcExpr, Env, Addr, Time);
   ascent! {
      struct CESK;
      relation output(LambdaCalcExpr);
      relation input(LambdaCalcExpr);
      relation σ(Addr, Storable);
      relation ς(LambdaCalcExpr, Env, Addr, Time);
      input(app(U(), I()));


      ς(v, ρ2, a, tick(t, k)) <--
         ς(?Ref(x), ρ, a, t),
         σ(ρ[x], ?Value(v, ρ2)),
         σ(a, ?Kont(k));

      σ(b, Kont(Ar(e1.deref().clone(), ρ.clone(), *a))),
      ς(e0.deref().clone(), ρ, b, tick(t, k)) <--
         ς(?e@App(e0, e1), ρ, addr, t),
         σ(a, ?Kont(k)),
         let b = alloc(e, ρ, addr, t, k);

      σ(b, Kont(Fn(v.clone(), ρ.clone(), *c))),
      ς(e, ρ2, b, tick(t, k)) <--
         ς(?v@Lam(..), ρ, a, t),
         σ(a, ?Kont(k)),
         if let Ar(e, ρ2, c) = k,
         let b = alloc(v, ρ, a, t, k);

      σ(b, Value(v.clone(), ρ.clone())),
      ς(e, upd(&ρ2, x, b), b, tick(t, k)) <--
         ς(?v@Lam(..), ρ, a, t),
         σ(a, ?Kont(k)),
         if let Fn(Lam(x, e), ρ2, c) = k,
         let b = alloc(v, ρ, a, t, k);
   };
   use std::collections::HashSet;
   type Store = Rc<BTreeMap<Addr, BTreeSet<Storable>>>;
   ascent! {
      struct CeskLocalStore;
      relation output(LambdaCalcExpr);
      relation input(LambdaCalcExpr);
      relation ς(LambdaCalcExpr, Env, Store, Addr, Time);
      // rule 1:
      ς(v.clone(), ρ2.clone(), σ.clone(), *a, tick(t, k)) <--
         ς(?Ref(x), ρ, σ, a, t),
         for sv in σ[&ρ[x]].iter(), if let Value(v, ρ2) = sv,
         for sa in σ[a].iter(), if let Kont(k) = sa;
      // ...
   }
   let mut prog = CESK::default();
   // println!("{}", AscentProgram::summary());
   prog.run();
   // println!("input:{:?}\n", prog.input);
   // println!("eval: {}\n", prog.eval.iter().map(|(e,v)| format!("{:?} ===> {:?}", e, v)).join("\n"));
}

#[test]
fn test_dl_patterns() {
   // ascent!{
   ascent_m_par! {
      #![measure_rule_times]
      relation foo(i32, Option<i32>);
      relation bar(i32, i32);
      foo(1, None);
      foo(2, Some(2));
      foo(3, Some(30));
      bar(*x, *y) <-- foo(x, y_opt) if let Some(y) = y_opt if y != x;
   };
   let mut prog = AscentProgram::default();
   prog.run();
   println!("bar: {:?}", prog.bar);
   assert!(prog.bar.iter().contains(&(3, 30)));
   assert!(prog.bar.len() == 1);
}

#[test]
fn test_dl_pattern_args() {
   ascent_m_par! {
      relation foo(i32, Option<i32>);
      relation bar(i32, i32);
      foo(1, None);
      foo(2, Some(2));
      foo(3, Some(30));
      foo(3, None);
      bar(*x, *y) <-- foo(x, ?Some(y)) if y != x;
   };
   let mut prog = AscentProgram::default();
   prog.run();
   println!("bar: {:?}", prog.bar);
   assert!(prog.bar.iter().contains(&(3, 30)));
   assert!(prog.bar.len() == 1);
}

#[test]
fn test_dl2() {
   ascent_m_par! {
      relation bar(i32, i32);
      relation foo1(i32, i32);
      relation foo2(i32, i32);

      foo1(1, 2);
      foo1(10, 20);
      foo1(0, 2);

      bar(*x, y + z) <-- foo1(x, y) if *x != 0, foo2(y, z);
   }

   let mut prog = AscentProgram::default();

   let foo2 = vec![(2, 4), (2, 1), (20, 40), (20, 0)];
   prog.foo2 = FromIterator::from_iter(foo2);

   prog.run();

   println!("bar: {:?}", prog.bar);
   assert!(rels_equal([(1, 3), (1, 6), (10, 60), (10, 20)], prog.bar));
}

#[test]
fn test_ascent_expressions_and_inits() {
   ascent_m_par! {
      relation foo(i32, i32) = vec![(1, 2)].into_iter().collect();
      foo(2, 3);
      foo(3, 5);

      relation bar(i32, i32);
      relation baz(i32, i32, i32);

      bar(3, 6);
      bar(5, 10);

      baz(*x, *y, *z) <-- foo(x, y), bar(x + y , z);
   };
   let mut prog = AscentProgram::default();
   prog.run();
   println!("baz: {:?}", prog.baz);
   assert!(rels_equal([(1, 2, 6), (2, 3, 10)], prog.baz));
}

#[test]
fn test_dl_cross_join() {
   ascent_m_par! {
      relation foo(i32, i32);
      relation bar(i32, i32);
      relation baz(i32, i32, i32, i32);
      foo(x, x + 1) <-- for x in 0..5;

      bar(11, 12);
      bar(12, 13);

      baz(a, b, c, d) <-- foo(a, b), bar(c , d);
   }
   let mut prog = AscentProgram::default();
   prog.run();
   println!("baz: {:?}", prog.baz);
   assert_eq!(prog.baz.len(), prog.foo.len() * prog.bar.len());
}

#[test]
fn test_dl_vars_bound_in_patterns() {
   ascent_m_par! {
      relation foo(i32, Option<i32>);
      relation bar(i32, i32);
      relation baz(i32, i32, i32);
      foo(1, Some(2));
      foo(2, None);
      foo(3, Some(5));
      foo(4, Some(10));


      bar(3, 6);
      bar(5, 10);
      bar(10, 20);

      baz(*x, *y, *z) <-- foo(x, ?Some(y)), bar(y , z);
   };
   let mut prog = AscentProgram::default();
   prog.run();
   println!("baz: {:?}", prog.baz);
   assert!(rels_equal([(3, 5, 10), (4, 10, 20)], prog.baz));
}

#[test]
fn test_dl_generators() {
   ascent! {
      relation foo(i32, i32);
      relation bar(i32);

      foo(x, y) <-- for x in 0..10, for y in (x+1)..10;

      bar(*x) <-- foo(x, y);
      bar(*y) <-- foo(x, y);
   };
   let mut prog = AscentProgram::default();
   prog.run();
   println!("foo: {:?}", prog.foo);
   assert_eq!(prog.foo.len(), 45);
}

#[test]
fn test_dl_generators2() {
   ascent! {
      relation foo(i32, i32);
      relation bar(i32);

      foo(3, 4);
      foo(4, 6);
      foo(20, 21);
      bar(x) <-- for (x, y) in (0..10).map(|x| (x, x+1)), foo(x, y);

   };
   let mut prog = AscentProgram::default();
   prog.run();
   println!("bar: {:?}", prog.bar);
   assert!(rels_equal([(3,)], prog.bar));
}

#[test]
fn test_dl_multiple_head_clauses() {
   ascent_m_par! {
      relation foo(Vec<i32>, Vec<i32>);
      relation foo2(Vec<i32>);
      relation foo1(Vec<i32>);

      relation bar(i32);

      foo(vec![3], vec![4]);
      foo(vec![1, 2], vec![4, 5]);
      foo(vec![10, 11], vec![20]);

      foo1(x.clone()), foo2(y.clone()) <-- foo(x, y) if x.len() > 1;
   };
   let mut prog = AscentProgram::default();
   prog.run();
   println!("foo1: {:?}", prog.foo1);
   println!("foo2: {:?}", prog.foo2);

   assert!(rels_equal([(vec![1, 2],), (vec![10, 11],)], prog.foo1));
   assert!(rels_equal([(vec![4, 5],), (vec![20],)], prog.foo2));
}

#[test]
fn test_dl_multiple_head_clauses2() {
   ascent_m_par! {
      relation foo(Vec<i32>);
      relation foo_left(Vec<i32>);
      relation foo_right(Vec<i32>);

      foo(vec![1,2,3,4]);

      foo_left(xs[..i].into()), foo_right(xs[i..].into()) <-- foo(xs), for i in 0..xs.len();
      foo(xs.clone()) <-- foo_left(xs);
      foo(xs.clone()) <-- foo_right(xs);
   };

   let mut prog = AscentProgram::default();
   prog.run();
   println!("foo: {:?}", prog.foo);

   assert!(rels_equal(
      [
         (vec![],),
         (vec![1],),
         (vec![1, 2],),
         (vec![1, 2, 3],),
         (vec![1, 2, 3, 4],),
         (vec![2],),
         (vec![2, 3],),
         (vec![2, 3, 4],),
         (vec![3],),
         (vec![3, 4],),
         (vec![4],)
      ],
      prog.foo
   ));
}

#[test]
fn test_dl_disjunctions() {
   ascent! {
      relation foo1(i32, i32);
      relation foo2(i32, i32);
      relation small(i32);
      relation bar(i32, i32);

      small(x) <-- for x in 0..5;
      foo1(0, 4); foo1(1, 4); foo1(2, 6);

      foo2(3, 30); foo2(2, 20); foo2(8, 21); foo2(9, 21);

      bar(x.clone(), y.clone()) <-- ((for x in 3..10), small(x) || foo1(x,_y)), (foo2(x,y));
   };
   let mut prog = AscentProgram::default();
   prog.run();
   println!("bar: {:?}", prog.bar);
   assert_rels_eq!([(3, 30), (2, 20)], prog.bar);
}

#[test]
fn test_dl_disjunctions2() {
   let res = ascent_run! {
      relation road(&'static str, &'static str);
      relation rail(&'static str, &'static str);

      road("A", "B"); road("B", "C"); rail("C", "D");

      relation connected(&'static str, &'static str);

      connected(x, y) <-- (road(x, y) | rail(x, y));
      connected(x, z) <-- connected(x, y), (road(y, z) | rail(y, z));
   };
   assert!(res.connected.contains(&("A", "D")));
}

#[test]
fn test_dl_repeated_vars() {
   ascent_m_par! {
      relation foo(i32);
      relation bar(i32, i32);
      relation res(i32);
      relation bar_refl(i32);
      relation bar3(i32, i32, i32);
      relation bar3_res(i32);

      foo(3);
      bar(2, 1);
      bar(1, 1);
      bar(3, 3);

      bar_refl(*x) <-- bar(x, x);

      res(*x) <-- foo(x), bar(x, x);

      bar3(10,10,11);
      bar3(1,1,1);
      bar3(1,2,3);
      bar3(2,1,3);

      bar3_res(*x) <-- bar3(x, x, *x + 1);
   };
   let mut prog = AscentProgram::default();
   prog.run();
   println!("res: {:?}", prog.res);
   assert!(rels_equal([(3,)], prog.res));
   assert!(rels_equal([(1,), (3,)], prog.bar_refl));
   assert!(rels_equal([(10,)], prog.bar3_res));
}

#[test]
fn test_dl_lattice1() {
   ascent_m_par! {
      lattice shortest_path(i32, i32, Dual<u32>);
      relation edge(i32, i32, u32);

      shortest_path(*x, *y, Dual(*w)) <-- edge(x, y, w);
      shortest_path(*x, *z, Dual(w + l.0)) <-- edge(x, y, w), shortest_path(y, z, l);

      edge(1, 2, x + 30)  <-- for x in 0..100;
      edge(2, 3, x + 50)  <-- for x in 0..100;
      edge(1, 3, x + 40)  <-- for x in 0..100;
      edge(2, 4, x + 100) <-- for x in 0..100;
      edge(1, 4, x + 200) <-- for x in 0..100;
   }
   let mut prog = AscentProgram::default();
   prog.run();
   println!("shortest_path ({} tuples):", prog.shortest_path.len());
   println!("\n{:?}", prog.shortest_path);
   println!("{}", AscentProgram::summary());
   assert!(rels_equal(lat_to_vec(prog.shortest_path), [
      (1, 2, Dual(30)),
      (1, 3, Dual(40)),
      (1, 4, Dual(130)),
      (2, 3, Dual(50)),
      (2, 4, Dual(100))
   ]))
}

/// A custom lattice data-structure provider, used to exercise the `#[lds(..)]` feature with a
/// non-`ascent::rel` provider path. It delegates to the built-in lattice index data structures and shares
/// nothing between them, demonstrating that an arbitrary provider path is resolved and its macros are
/// invoked. See `crate::btree_lat_ds` for a provider with index data structures of its own.
mod my_lattice_ds {
   #[macro_export]
   macro_rules! my_lattice_ds_rel_codegen {
      ($($tt: tt)*) => {};
   }
   pub use my_lattice_ds_rel_codegen as rel_codegen;

   #[macro_export]
   macro_rules! my_lattice_ds_lat_ind_common {
      ($name: ident, $field_types: ty, $indices: expr, $par: tt, ()) => {
         ()
      };
   }
   pub use my_lattice_ds_lat_ind_common as lat_ind_common;

   #[macro_export]
   macro_rules! my_lattice_ds_lat_full_ind {
      ($name: ident, $field_types: ty, $indices: expr, ser, (), $key: ty, $val: ty) => {
         ascent::internal::RelFullIndexType<$key, $val>
      };
      ($name: ident, $field_types: ty, $indices: expr, par, (), $key: ty, $val: ty) => {
         ascent::internal::CRelFullIndex<$key, $val>
      };
   }
   pub use my_lattice_ds_lat_full_ind as lat_full_ind;

   #[macro_export]
   macro_rules! my_lattice_ds_lat_rel_ind {
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
   pub use my_lattice_ds_lat_rel_ind as lat_rel_ind;
}

/// Same program as `test_dl_lattice1`, but the lattice relation uses the default data structure
/// provider explicitly via `#[lds(ascent::rel)]`. Exercises the lattice BYODS code path.
#[test]
fn test_dl_lattice_lds_default() {
   ascent_m_par! {
      #[lds(ascent::rel)]
      lattice shortest_path(i32, i32, Dual<u32>);
      relation edge(i32, i32, u32);

      shortest_path(*x, *y, Dual(*w)) <-- edge(x, y, w);
      shortest_path(*x, *z, Dual(w + l.0)) <-- edge(x, y, w), shortest_path(y, z, l);

      edge(1, 2, x + 30)  <-- for x in 0..100;
      edge(2, 3, x + 50)  <-- for x in 0..100;
      edge(1, 3, x + 40)  <-- for x in 0..100;
      edge(2, 4, x + 100) <-- for x in 0..100;
      edge(1, 4, x + 200) <-- for x in 0..100;
   }
   let mut prog = AscentProgram::default();
   prog.run();
   assert!(rels_equal(lat_to_vec(prog.shortest_path), [
      (1, 2, Dual(30)),
      (1, 3, Dual(40)),
      (1, 4, Dual(130)),
      (2, 3, Dual(50)),
      (2, 4, Dual(100))
   ]))
}

/// Same program, but the lattice relation uses a user-defined data structure provider via
/// `#[lds(crate::tests::my_lattice_ds)]`. Exercises lattice BYODS with a custom provider path.
#[test]
fn test_dl_lattice_lds_custom() {
   ascent_m_par! {
      #[lds(crate::tests::my_lattice_ds)]
      lattice shortest_path(i32, i32, Dual<u32>);
      relation edge(i32, i32, u32);

      shortest_path(*x, *y, Dual(*w)) <-- edge(x, y, w);
      shortest_path(*x, *z, Dual(w + l.0)) <-- edge(x, y, w), shortest_path(y, z, l);

      edge(1, 2, x + 30)  <-- for x in 0..100;
      edge(2, 3, x + 50)  <-- for x in 0..100;
      edge(1, 3, x + 40)  <-- for x in 0..100;
      edge(2, 4, x + 100) <-- for x in 0..100;
      edge(1, 4, x + 200) <-- for x in 0..100;
   }
   let mut prog = AscentProgram::default();
   prog.run();
   assert!(rels_equal(lat_to_vec(prog.shortest_path), [
      (1, 2, Dual(30)),
      (1, 3, Dual(40)),
      (1, 4, Dual(130)),
      (2, 3, Dual(50)),
      (2, 4, Dual(100))
   ]))
}

/// A lattice data-structure provider that records every `observe` call verbatim, used to pin down *which*
/// rows the hook is invoked for. Its `lat_ind_common!` value is a `Recorder`; the fixpoint loop merges the
/// recorders of the relation's versions into the one left in the program struct.
mod recording_ds {
   use std::sync::Mutex;

   use ascent::Dual;
   use ascent::internal::{CLatIndCommon, Freezable, LatIndCommon, RelIndexMerge};

   /// Every `(key, lattice value)` pair handed to `observe`, in observation order.
   #[derive(Default)]
   pub struct Recorder(Mutex<Vec<((i32, i32), u32)>>);

   impl Recorder {
      pub fn observations(&self) -> Vec<((i32, i32), u32)> { self.0.lock().unwrap().clone() }

      /// The observed values for `key`, in observation order.
      pub fn values_for(&self, key: (i32, i32)) -> Vec<u32> {
         self.observations().into_iter().filter(|&(k, _)| k == key).map(|(_, v)| v).collect()
      }

      pub fn keys(&self) -> std::collections::HashSet<(i32, i32)> {
         self.observations().into_iter().map(|(k, _)| k).collect()
      }
   }

   impl LatIndCommon<(i32, i32), Dual<u32>> for Recorder {
      fn observe(&mut self, key: &(i32, i32), val: &Dual<u32>) { self.0.get_mut().unwrap().push((*key, val.0)); }
   }

   impl CLatIndCommon<(i32, i32), Dual<u32>> for Recorder {
      fn c_observe(&self, key: &(i32, i32), val: &Dual<u32>) { self.0.lock().unwrap().push((*key, val.0)); }
   }

   impl RelIndexMerge for Recorder {
      // Older versions' observations come first, so the merged recorder stays in observation order.
      fn move_index_contents(from: &mut Self, to: &mut Self) {
         to.0.get_mut().unwrap().append(from.0.get_mut().unwrap());
      }
   }

   impl Freezable for Recorder {}

   #[macro_export]
   macro_rules! recording_ds_rel_codegen {
      ($($tt: tt)*) => {};
   }
   pub use recording_ds_rel_codegen as rel_codegen;

   #[macro_export]
   macro_rules! recording_ds_lat_ind_common {
      ($name: ident, $ft: ty, $indices: expr, $par: tt, ()) => {
         $crate::tests::recording_ds::Recorder
      };
   }
   pub use recording_ds_lat_ind_common as lat_ind_common;

   #[macro_export]
   macro_rules! recording_ds_lat_full_ind {
      ($name: ident, $ft: ty, $indices: expr, ser, (), $key: ty, $val: ty) => {
         ascent::internal::RelFullIndexType<$key, $val>
      };
      ($name: ident, $ft: ty, $indices: expr, par, (), $key: ty, $val: ty) => {
         ascent::internal::CRelFullIndex<$key, $val>
      };
   }
   pub use recording_ds_lat_full_ind as lat_full_ind;

   #[macro_export]
   macro_rules! recording_ds_lat_rel_ind {
      ($name: ident, $ft: ty, $indices: expr, ser, (), $ind: expr, $key: ty, $val: ty) => {
         ascent::internal::LatticeIndexType<$key, $val>
      };
      ($name: ident, $ft: ty, $indices: expr, par, (), [], $key: ty, $val: ty) => {
         ascent::internal::CRelNoIndex<$val>
      };
      ($name: ident, $ft: ty, $indices: expr, par, (), $ind: expr, $key: ty, $val: ty) => {
         ascent::internal::CRelIndex<$key, $val>
      };
   }
   pub use recording_ds_lat_rel_ind as lat_rel_ind;
}

ascent_m_par! {
   /// A `Dual<u32>` shortest-path lattice whose provider records every `observe` call.
   pub struct RecordingProg;

   #[lds(crate::tests::recording_ds)]
   lattice shortest_path(i32, i32, Dual<u32>);
   relation edge(i32, i32, u32);

   shortest_path(*x, *y, Dual(*w)) <-- edge(x, y, w);
   shortest_path(*x, *z, Dual(w + l.0)) <-- edge(x, y, w), shortest_path(y, z, l);
}

/// `observe` must only ever see values that the row actually holds, never a proposed value that lost
/// the lattice join. Because `Dual<u32>`'s join is `min`, a row's value only ever decreases, so the values
/// observed for a key must form a strictly decreasing sequence ending at the row's final value. Observing
/// discarded proposals (as an earlier version of this feature did, by running the hook before the join)
/// breaks that monotonicity: with these edges, `(1, 3)` gets a direct edge of 40 and a derived path of 80,
/// and 80 must never be observed after 40.
#[test]
fn test_lds_observe_only_accepted_values() {
   let mut prog = RecordingProg::default();
   prog.edge = vec![(1, 2, 30), (2, 3, 50), (1, 3, 40)].into_iter().collect();
   prog.run();

   let recorder = std::mem::take(&mut prog.__shortest_path_ind_common);
   let final_values: HashMap<(i32, i32), u32> =
      lat_to_vec(prog.shortest_path).into_iter().map(|(x, y, Dual(w))| ((x, y), w)).collect();

   // Exactly the keys that ended up in the relation were observed.
   assert_eq!(recorder.keys(), final_values.keys().cloned().collect());

   for (&key, &final_value) in final_values.iter() {
      let observed = recorder.values_for(key);
      assert!(!observed.is_empty(), "key {key:?} was never observed");
      // Strictly decreasing: every observation improved on the previous value the row held.
      assert!(
         observed.windows(2).all(|w| w[0] > w[1]),
         "observations for {key:?} are not strictly decreasing: {observed:?} \
          (a discarded proposal was observed)"
      );
      // The last observation is the value the row settled on.
      assert_eq!(*observed.last().unwrap(), final_value, "last observation for {key:?} is not the final value");
   }

   // Specifically: the losing 1 -> 2 -> 3 path of weight 80 never reaches the provider, because the direct
   // edge of weight 40 is derived first and the join discards 80.
   assert_eq!(recorder.values_for((1, 3)), vec![40]);
}

/// Rows put into a lattice directly — rather than derived by a rule — must also reach `observe`;
/// indexing is the only point at which Ascent learns of them. Re-running the program must not observe
/// those rows (or any already-observed row) a second time.
#[test]
fn test_lds_observes_prepopulated_rows() {
   let mut prog = RecordingProg::default();
   prog.shortest_path = lat_from_vec(vec![(7, 8, Dual(1))]);
   prog.edge = vec![(1, 2, 30)].into_iter().collect();
   prog.run();

   let observations = prog.__shortest_path_ind_common.observations();
   assert!(observations.contains(&((7, 8), 1)), "pre-populated row was not observed: {observations:?}");
   assert!(observations.contains(&((1, 2), 30)), "derived row was not observed: {observations:?}");

   // A second run re-indexes every row but derives nothing new, so it must observe nothing new. Only
   // checked in serial Ascent: calling `run()` twice already panics in parallel Ascent, `lds` or not.
   #[cfg(not(feature = "par"))]
   {
      let before = prog.__shortest_path_ind_common.observations();
      prog.run();
      assert_eq!(prog.__shortest_path_ind_common.observations(), before, "re-running observed rows a second time");
   }
}

ascent_m_par! {
   /// A lattice seeded by a relation initialization, whose provider records every `observe` call.
   pub struct RecordingInitProg;

   #[lds(crate::tests::recording_ds)]
   lattice shortest_path(i32, i32, Dual<u32>) = lat_from_vec(vec![(5, 6, Dual(9))]);
   relation edge(i32, i32, u32);

   shortest_path(*x, *y, Dual(*w)) <-- edge(x, y, w);
}

/// A `= expr` relation initialization indexes the lattice twice: once when `Default::default()` applies the
/// initialization, and again at the start of `run()`. The initialized row must still be observed exactly
/// once.
#[test]
fn test_lds_observes_initialized_rows_once() {
   let mut prog = RecordingInitProg::default();
   prog.run();
   assert_eq!(prog.__shortest_path_ind_common.observations(), vec![((5, 6), 9)]);
}

/// The `test_dl_lattice1` program, with the lattice backed by `crate::btree_lat_ds`: every index of
/// `shortest_path` is answered from one `BTreeMap` per relation version, and none of Ascent's built-in
/// lattice index data structures exist.
#[test]
fn test_dl_lattice_lds_btree() {
   ascent_m_par! {
      #[lds(crate::btree_lat_ds)]
      lattice shortest_path(i32, i32, Dual<u32>);
      relation edge(i32, i32, u32);

      shortest_path(*x, *y, Dual(*w)) <-- edge(x, y, w);
      shortest_path(*x, *z, Dual(w + l.0)) <-- edge(x, y, w), shortest_path(y, z, l);

      edge(1, 2, x + 30)  <-- for x in 0..100;
      edge(2, 3, x + 50)  <-- for x in 0..100;
      edge(1, 3, x + 40)  <-- for x in 0..100;
      edge(2, 4, x + 100) <-- for x in 0..100;
      edge(1, 4, x + 200) <-- for x in 0..100;
   }
   let mut prog = AscentProgram::default();
   prog.run();
   // The provider's map holds exactly one entry per row: it is the only index storage there is.
   assert_eq!(prog.__shortest_path_ind_common.len(), prog.shortest_path.len());
   assert!(rels_equal(lat_to_vec(prog.shortest_path), [
      (1, 2, Dual(30)),
      (1, 3, Dual(40)),
      (1, 4, Dual(130)),
      (2, 3, Dual(50)),
      (2, 4, Dual(100))
   ]))
}

/// All-pairs shortest distances between distinct nodes, by Floyd-Warshall: the oracle for
/// `test_dl_lattice_lds_shortest_path`.
fn floyd_warshall(edges: &[(i32, i32, u32)]) -> HashMap<(i32, i32), u32> {
   let nodes = edges.iter().flat_map(|&(a, b, _)| [a, b]).sorted().dedup().collect_vec();
   let mut dist: HashMap<(i32, i32), u32> = HashMap::new();
   for &(a, b, w) in edges {
      let d = dist.entry((a, b)).or_insert(w);
      *d = (*d).min(w);
   }
   for &k in &nodes {
      for &i in &nodes {
         let Some(&d_ik) = dist.get(&(i, k)) else { continue };
         for &j in &nodes {
            let Some(&d_kj) = dist.get(&(k, j)) else { continue };
            if dist.get(&(i, j)).is_none_or(|&d| d_ik + d_kj < d) {
               dist.insert((i, j), d_ik + d_kj);
            }
         }
      }
   }
   dist.retain(|&(i, j), _| i != j);
   dist
}

/// Shortest paths computed by Datalog through `crate::btree_lat_ds`'s indices, checked against
/// Floyd-Warshall on a pseudo-random graph with cycles. The recursive rule joins on the lattice's `[0]`
/// index (a `BTreeMap` range query), the lattice join looks rows up in its `[0, 1]` full index, and the
/// two query rules read it through `[0]` with a constant and through `[]`.
#[test]
fn test_dl_lattice_lds_shortest_path() {
   ascent_m_par! {
      #[lds(crate::btree_lat_ds)]
      lattice shortest_path(i32, i32, Dual<u32>);
      relation edge(i32, i32, u32);
      relation from_origin(i32, u32);
      relation all_dist(i32, i32, u32);

      shortest_path(*x, *y, Dual(*w)) <-- edge(x, y, w);
      shortest_path(*x, *z, Dual(w + l.0)) <-- edge(x, y, w), shortest_path(y, z, l);

      from_origin(*y, l.0) <-- shortest_path(0, y, l);
      all_dist(*x, *y, l.0) <-- shortest_path(x, y, l);
   }

   // A deterministic pseudo-random graph on 25 nodes, dense enough to have many cycles and many paths
   // that improve on direct edges.
   let mut seed: u64 = 0x5eed;
   let mut next = move |n: u64| {
      seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
      (seed >> 33) % n
   };
   let edges = (0..120).map(|_| (next(25) as i32, next(25) as i32, next(50) as u32 + 1)).collect_vec();
   let expected = floyd_warshall(&edges);

   let mut prog = AscentProgram::default();
   prog.edge = edges.iter().cloned().collect();
   prog.run();

   // `shortest_path` also holds self-loops (i, i) for nodes on a cycle, which the oracle leaves out.
   let computed: HashMap<(i32, i32), u32> =
      lat_to_vec(prog.shortest_path).into_iter().map(|(x, y, Dual(w))| ((x, y), w)).collect();
   let computed_non_loops: HashMap<(i32, i32), u32> =
      computed.iter().filter(|((i, j), _)| i != j).map(|(&k, &v)| (k, v)).collect();
   assert_eq!(computed_non_loops, expected);
   assert!(computed.len() > 100, "graph too sparse to exercise the indices: {} paths", computed.len());

   assert!(rels_equal(prog.all_dist, computed.iter().map(|(&(x, y), &w)| (x, y, w))));
   assert!(rels_equal(
      prog.from_origin,
      computed.iter().filter(|((x, _), _)| *x == 0).map(|(&(_, y), &w)| (y, w))
   ));
   assert_eq!(prog.__shortest_path_ind_common.len(), computed.len());
}

#[test]
fn test_dl_lattice2() {
   ascent! {
      lattice shortest_path(i32, i32, Dual<u32>);
      relation edge(i32, i32, u32);

      shortest_path(*x,*y, {println!("adding sp({},{},{})?", x, y, w ); Dual(*w)}) <-- edge(x, y, w);
      shortest_path(*x, *z, {println!("adding sp({},{},{})?", x, z, *w + len.0); Dual(w + len.0)}) <-- edge(x, y, w), shortest_path(y, z, len);

      edge(1, 2, 30);
      edge(2, 3, 50);
      edge(1, 3, 40);
      edge(2, 4, 100);
      edge(4, 1, 1000);

   };
   let mut prog = AscentProgram::default();
   prog.run();
   println!("shortest_path ({} tuples):\n{:?}", prog.shortest_path.len(), prog.shortest_path);
}

#[test]
fn test_ascent_run() {
   let foo_contents = (0..10).flat_map(|x| (x + 1..10).map(move |y| (x, y))).collect_vec();
   let res = ascent_run! {
      relation foo(i32, i32);
      relation bar(i32);

      foo(x,y) <-- for &(x,y) in foo_contents.iter();

      bar(*x) <-- foo(x, y);
      bar(*y) <-- foo(x, y);
   };

   let _res2 = ascent_run! {
      relation foo(i32);
      foo(42);
   };
   println!("foo: {:?}", res.foo);
   assert_eq!(res.foo.len(), 45);
}

#[test]
fn test_ascent_run_rel_init() {
   let foo_contents = (0..10).flat_map(|x| (x + 1..10).map(move |y| (x, y))).collect_vec();
   let res = ascent_run! {
      relation foo(i32, i32) = foo_contents;
      relation bar(i32);

      bar(*x), bar(*y) <-- foo(x, y);
   };

   println!("foo: {:?}", res.foo);
   assert_eq!(res.foo.len(), 45);
}

#[test]
fn test_ascentception() {
   let res = ascent_run! {
      relation ascentception_input(i32);
      ascentception_input(0);
      ascentception_input(100);

      relation funny(i32, i32);
      funny(x, y) <-- ascentception_input(inp), for (x, y) in {
         ascent_run! {
            relation ascentception(i32, i32);
            ascentception(x, x + 1) <-- for x in *inp..(inp + 10);
         }.ascentception
      };
   };
   println!("funny: {:?}", res.funny);
   assert_eq!(res.funny.len(), 20);
}

#[test]
fn test_ascent_run_tc() {
   fn compute_tc(inp: Vec<(i32, i32)>) -> Vec<(i32, i32)> {
      ascent_run_m_par! {
         relation r(i32, i32) = FromIterator::from_iter(inp);
         relation tc(i32, i32);
         tc(x, y) <-- r(x, y);
         tc(x, z) <-- r(x, y), tc(y, z);
      }
      .tc
      .into_iter()
      .collect()
   }
   assert!(rels_equal([(1, 2), (2, 3), (1, 3)], compute_tc(vec![(1, 2), (2, 3)])));
}

#[test]
fn test_ascent_run_tc_generic() {
   fn compute_tc<TNode: Clone + Hash + Eq + Sync + Send>(r: &[(TNode, TNode)]) -> Vec<(TNode, TNode)> {
      ascent_run_m_par! {
         struct TC<TNode: Clone + Hash + Eq + Sync + Send>;
         relation tc(TNode, TNode);
         tc(x.clone(), y.clone()) <-- for (x, y) in r.iter();
         tc(x.clone(), z.clone()) <-- for (x, y) in r.iter(), tc(y, z);
      }
      .tc
      .into_iter()
      .collect()
   }
   assert!(rels_equal([(1, 2), (2, 3), (1, 3)], compute_tc(&[(1, 2), (2, 3)])));
}

#[test]
fn test_ascent_tc_generic() {
   ascent! {
      struct TC<TNode: Clone + Hash + Eq>;
      relation tc(TNode, TNode);
      relation r(TNode, TNode);
      tc(x.clone(), y.clone()) <-- r(x,y);
      tc(x.clone(), z.clone()) <-- r(x, y), tc(y, z);
   }
   let mut prog = TC::default();
   prog.r = vec![(1, 2), (2, 3)];
   prog.run();
   assert!(rels_equal([(1, 2), (2, 3), (1, 3)], prog.tc));
}

#[test]
fn test_ascent_negation_through_lattices() {
   use ascent::lattice::set::Set;
   let res = ascent_run_m_par! {
      relation foo(i32, i32);
      relation bar(i32, i32);

      bar(x, x+1) <-- for x in 0..10;
      foo(*x, *y) <-- bar(x, y);

      lattice foo_as_set(Set<(i32, i32)>);
      foo_as_set(Set::singleton((*x, *y))) <-- foo(x, y);

      relation baz(i32, i32);
      baz(1, 2);
      baz(1, 3);

      relation res(i32, i32);
      res(*x, *y) <-- baz(x, y), foo_as_set(all_foos), if !all_foos.contains(&(*x, *y));
   };
   println!("res: {:?}", res.res);
   assert!(rels_equal([(1, 3)], res.res));
}

#[test]
fn test_ascent_run_explicit_decl() {
   fn compute_tc<TNode: Clone + Eq + Hash>(edges: &[(TNode, TNode)]) -> Vec<(TNode, TNode)> {
      ascent_run! {
         struct TC<TNode> where TNode: Clone + Eq + Hash;
         relation edge(TNode, TNode);
         relation path(TNode, TNode);
         edge(x.clone(), y.clone()) <-- for (x, y) in edges.iter();

         path(x.clone(), y.clone()) <-- edge(x,y);
         path(x.clone(), z.clone()) <-- edge(x,y), path(y, z);
      }
      .path
   }

   let res = compute_tc(&[(1, 2), (2, 3)]);
   println!("res: {:?}", res);
   assert!(rels_equal([(1, 2), (2, 3), (1, 3)], res));
}

#[test]
fn test_ascent_fac() {
   ascent_m_par! {
      struct Fac;
      relation fac(u64, u64);
      relation do_fac(u64);

      fac(0, 1) <-- do_fac(0);
      do_fac(x - 1) <-- do_fac(x), if *x > 0;
      fac(*x, x * sub1fac) <-- do_fac(x) if *x > 0, fac(x - 1, sub1fac);

      do_fac(10);
   }
   let mut prog = Fac::default();
   prog.run();
   println!("fac: {:?}", prog.fac);
   println!("{}", Fac::summary());
   println!("{}", prog.relation_sizes_summary());
   println!("{}", prog.scc_times_summary());

   assert!(prog.fac.iter().contains(&(5, 120)));
}

#[test]
fn test_consuming_ascent_run_tc() {
   fn compute_tc(inp: impl Iterator<Item = (i32, i32)>) -> Vec<(i32, i32)> {
      ascent_run! {
         relation tc(i32, i32);
         relation r(i32, i32);

         r(x, y) <-- for (x, y) in inp;
         tc(*x, *y) <-- r(x, y);
         tc(*x, *z) <-- r(x, y), tc(y, z);
      }
      .tc
   }
   let res = compute_tc([(1, 2), (2, 3)].into_iter());
   println!("res: {:?}", res);
   assert!(rels_equal([(1, 2), (2, 3), (1, 3)], compute_tc([(1, 2), (2, 3)].into_iter())));
}

#[test]
fn test_ascent_simple_join() {
   let res = ascent_run_m_par! {
      relation bar(i32, i32);
      relation foo(i32, i32);
      relation baz(i32, i32);

      bar(2, 3);
      foo(1, 2);
      bar(2, 1);

      baz(*x, *z) <-- foo(x, y), bar(y, z), if x != z;
      foo(*x, *y), bar(*x, y) <-- baz(x, y);
   };
   println!("baz: {:?}", res.baz);
   assert!(rels_equal([(1, 3)], res.baz));
}

#[test]
fn test_ascent_simple_join2() {
   let res = ascent_run_m_par! {
      relation bar(i32, i32);
      relation foo(i32, i32);
      relation baz(i32, i32);

      foo(1, 2);
      foo(10, 2);
      bar(2, 3);
      bar(2, 1);

      baz(*x, *z) <-- foo(x, y) if *x != 10, bar(y, z), if x != z;
      foo(*x, *y), bar(*x, *y) <-- baz(x, y);
   };
   println!("baz: {:?}", res.baz);
   assert_rels_eq!([(1, 3)], res.baz);
}

#[test]
fn test_ascent_simple_join3() {
   let res = ascent_run_m_par! {
      relation bar(i32, i32);
      relation foo(i32, i32);
      relation baz(i32, i32);

      foo(1, 2);
      foo(10, 2);
      bar(2, 3);
      bar(2, 1);

      baz(*x, *z) <-- foo(x, y) if *x != 10, bar(y, ?z) if *z < 4, if x != z;

      baz(*x, *z) <-- foo(x, y) if *x != 10, bar(y, z) if *z * x != 444, if x != z;
      foo(*x, *y), bar(*x, *y) <-- baz(x, y);
   };
   println!("baz: {:?}", res.baz);
   assert_rels_eq!([(1, 3)], res.baz);
}

#[test]
fn test_ascent_simple_join4() {
   #[derive(Default, Clone, Copy)]
   struct Prop {
      transitive: bool,
      reflexive: bool,
      symmetric: bool,
   }
   let no_prop = Prop::default();

   let input_rel = vec![(1, 2), (2, 3)];

   let test_cases = vec![
      (Prop { transitive: true, ..no_prop }, vec![(1, 2), (2, 3), (1, 3)]),
      (Prop { reflexive: true, ..no_prop }, vec![(1, 2), (2, 3), (1, 1), (2, 2), (3, 3)]),
      (Prop { symmetric: true, ..no_prop }, vec![(1, 2), (2, 3), (3, 2), (2, 1)]),
      (Prop { reflexive: true, transitive: true, symmetric: true }, vec![
         (1, 2),
         (2, 3),
         (1, 3),
         (1, 1),
         (2, 2),
         (3, 3),
         (2, 1),
         (3, 2),
         (3, 1),
      ]),
   ];

   for (prop, expected) in test_cases {
      let res = ascent_run_m_par! {
         relation rel(i32, i32) = input_rel.iter().cloned().collect();

         rel(y, x) <-- if prop.symmetric, rel(x, y);
         rel(y, y), rel(x, x) <-- if prop.reflexive, rel(x, y);
         rel(x, z) <-- if prop.transitive, rel(x, y), rel(y, z);
      };
      assert_rels_eq!(res.rel, expected);
   }
}

#[test]
fn test_ascent_simple_join5() {
   let res = ascent_run_m_par! {
      relation foo(i32, i32);
      foo(1,2), foo(2, 3);
      foo(x, z) <-- let x = &42, foo(x, y), foo(y, z);

      relation bar(i32, i32);
      bar(1, 2), bar(2, 3);
      bar(x, z) <-- let z = &42, bar(x, y), bar(y, z);

      relation baz(i32, i32);
      baz(x, y) <-- foo(x, y), bar(x, y);
      baz(x, z) <-- let _ = 42, if let Some(w) = Some(42), baz(x, y), baz(y, z);

   };

   assert_rels_eq!(res.foo, [(1, 2), (2, 3)]);
   assert_rels_eq!(res.bar, [(1, 2), (2, 3)]);
   assert_rels_eq!(res.baz, [(1, 2), (2, 3), (1, 3)]);
}

#[test]
fn test_ascent_wildcards() {
   let res = ascent_run_m_par! {
      relation foo(i32, i32, i32);
      relation bar(i32, i32);
      relation baz(i32);

      foo(1, 2, 3);
      foo(2, 3, 4);
      bar(1, 1);
      bar(1, 2);
      bar(1, 3);

      baz(x) <--
         foo(x, _, _),
         bar(_, x);
   };
   println!("baz: {:?}", res.baz);
   assert_rels_eq!([(1,), (2,)], res.baz);
}

fn min<'a>(inp: impl Iterator<Item = (&'a i32,)>) -> impl Iterator<Item = i32> {
   inp.map(|tuple| tuple.0).min().cloned().into_iter()
}

#[test]
fn test_ascent_agg() {
   let res = ascent_run_m_par! {
      relation foo(i32, i32);
      relation bar(i32, i32, i32);
      relation baz(i32, i32, i32);

      foo(1, 2);
      foo(2, 3);
      bar(1, 2, 10);
      bar(1, 2, 100);

      baz(x, y, min_z) <--
         foo(x, y),
         agg min_z = min(z) in bar(x, y, z);
   };
   println!("{}", res.summary());
   println!("baz: {:?}", res.baz);
   assert_rels_eq!([(1, 2, 10)], res.baz);
}

#[test]
fn test_run_timeout() {
   ascent! {
      #![generate_run_timeout]
      /// A diverging Ascent program
      struct Diverging;
      /// foooooooooooo
      relation foo(u128);
      foo(0);
      foo(x + 1) <-- foo(x);
   }

   let mut prog = Diverging::default();
   prog.foo = vec![(1,), (2,)];
   let run_timeout_res = prog.run_timeout(Duration::from_millis(5));
   assert!(!run_timeout_res);
}

#[test]
fn test_run_timeout_keeps_results() {
   ascent_m_par! {
      #![generate_run_timeout]
      struct TimeoutTC;
      relation edge(u32, u32);
      relation path(u32, u32);
      lattice shortest(u32, u32, Dual<u32>);
      path(x, y), shortest(x, y, Dual(1)) <-- edge(x, y);
      path(x, z) <-- edge(x, y), path(y, z);
      shortest(x, z, Dual(d.0 + 1)) <-- edge(x, y), shortest(y, z, d);
   }

   let edges = (0..30).map(|x| (x, x + 1)).collect_vec();
   let mut full = TimeoutTC::default();
   full.edge = edges.iter().cloned().collect();
   full.run();

   let mut prog = TimeoutTC::default();
   prog.edge = edges.into_iter().collect();
   assert!(!prog.run_timeout(Duration::ZERO));
   assert!(!prog.path.is_empty() && prog.path.len() < full.path.len());

   // finishing the run after a timeout reaches the same fixed point
   prog.run();
   assert!(rels_equal(prog.path, full.path));
   assert!(rels_equal(lat_to_vec(prog.shortest), lat_to_vec(full.shortest)));
}

#[test]
fn test_ascent_bounded_set() {
   use ascent::lattice::bounded_set::BoundedSet;
   ascent_m_par! { struct AscentProgram<const N: usize>;

      lattice num_store(BoundedSet<N, i32>);
      relation init(i32);

      init(x) <-- for x in 0..20;
      num_store(BoundedSet::singleton(*x)) <--
         init(x);
   }

   let mut prog = AscentProgram::<10>::default();
   prog.run();
   let store = &lat_to_vec(prog.num_store)[0].0;
   for (x,) in prog.init.iter() {
      assert!(store.contains(x));
   }
}

#[test]
fn test_issue3() {
   #![allow(non_snake_case)]

   ascent_m_par! {
      relation a__(i32, i32);
      relation c__(i32, i32, i32);
      relation e__(i32);
      relation h__(i32, i32, i32);

      e__(a) <-- a__(b, a);
      h__(e, e, e) <-- a__(d, e), c__(e, f, e), e__(e);
   }
   let mut prog = AscentProgram::default();
   prog.a__ = FromIterator::from_iter(vec![(88, 5), (37, 24), (11, 91)]);
   prog.c__ = FromIterator::from_iter(vec![(32, 83, 88), (2, 8, 5)]);
   prog.e__ = FromIterator::from_iter(vec![(44,), (83,)]);
   prog.h__ = FromIterator::from_iter(vec![(38, 88, 18), (76, 18, 65), (86, 73, 91), (98, 26, 91), (76, 10, 14)]);

   prog.run();
   println!("h__: {:?}", prog.h__);
   assert_rels_eq!(prog.h__, [(38, 88, 18), (76, 18, 65), (86, 73, 91), (98, 26, 91), (76, 10, 14)]);
}

#[test]
fn test_repeated_vars_simple_joins() {
   ascent_m_par! {
      relation foo1(i32, i32);
      relation foo2(i32, i32);
      relation bar(i32, i32);

      // filler:
      foo2(100, 100), foo2(101, 101), foo2(102, 102);

      foo1(1, 1), foo2(1, 2), foo1(10, 11), foo2(11, 12);

      bar(x, y) <-- foo2(x, y), foo1(x, x);
   }
   let mut prog = AscentProgram::default();
   prog.run();

   println!("bar: {:?}", prog.bar);
   assert_rels_eq!(prog.bar, [(1, 2)]);
}

#[test]
fn test_aggregated_lattice() {
   let res = ascent::ascent_run! {
      relation foo(i32, i32);
      lattice bar(i32, i32);

      bar(x, y) <-- for x in 0..2, for y in 5..10;

      foo(x, z) <--
         for x in 0..2,
         agg z = ascent::aggregators::sum(y) in bar(x, y);
   };
   assert_rels_eq!(res.bar, [(0, 9), (1, 9)]);
}

#[test]
fn test_ds_attr() {
   use ascent::rel as my_rel;
   let res = ascent::ascent_run! {
      #![ds(my_rel)]

      #[ds(ascent::rel)]
      relation foo(i32, i32) = vec![(0, 1), (1, 0)];

      relation bar(i32, i32);

      bar(x, y) <-- foo(x, y), if x < y;
   };

   assert_rels_eq!(res.bar, [(0, 1)]);
}

#[test]
fn test_rel_empty_check() {
   let res = ascent_run_m_par! {
      relation edge(i32, i32);
      relation path(i32, i32);
      relation legit(i32);

      path(x, z) <-- edge(x, y), path(y, z), legit(x);
      path(x, y) <-- edge(x, y), legit(*&x);

      legit(0);
      legit(y) <-- legit(x), path(x, y);

      edge(x, x + 1) <-- for x in 0..9;
   };

   println!("{:?}", res.path);
   assert_eq!(res.path.len(), 9 * 10 / 2);
}

#[test]
fn test_multiple_rel_definitions() {
   // When there are multiple definitions of a relation that agree on arity and column types,
   // the last one wins
   let res = ascent_run! {
      relation r1(usize);
      relation r1(usize) = vec![(1,), (2,)];

      relation r2(usize) = vec![(3,), (4,)];
      relation r2(usize);

      r2(x) <-- r1(x);
   };

   assert_rels_eq!(res.r2, vec![(1,), (2,)]);
}