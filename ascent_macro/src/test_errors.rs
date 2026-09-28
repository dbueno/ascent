#![cfg(test)]
use crate::{AscentMacroKind, ascent_impl};

#[test]
fn test_agg_not_stratifiable() {
   let inp = quote! {
      relation foo(i32, i32, i32);
      relation bar(i32, i32);
      relation baz(i32);

      baz(x) <--
         foo(x, _, _),
         !bar(_, x);

      bar(x, x + 1) <-- baz(x);
   };
   let res = ascent_impl(inp, AscentMacroKind::default());
   println!("res: {:?}", res);
   assert!(res.is_err());
   assert!(res.unwrap_err().to_string().contains("bar"));
}

#[test]
fn test_ds_on_lattice_is_error() {
   let inp = quote! {
      #[ds(ascent::rel)]
      lattice foo(i32, i32, u32);
   };
   let res = ascent_impl(inp, AscentMacroKind::default());
   assert!(res.is_err());
   assert!(res.unwrap_err().to_string().contains("lds"));
}

#[test]
fn test_lds_on_relation_is_error() {
   let inp = quote! {
      #[lds(ascent::rel)]
      relation foo(i32, i32);
   };
   let res = ascent_impl(inp, AscentMacroKind::default());
   assert!(res.is_err());
   assert!(res.unwrap_err().to_string().contains("lattice"));
}
