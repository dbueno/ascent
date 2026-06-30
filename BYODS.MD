BYODS is an extension of Ascent that allows custom data structures backing relations. The OOPSLA paper [Bring Your Own Data Structures to Datalog](https://dl.acm.org/doi/pdf/10.1145/3622840) describes the semantics and high-level design of BYODS, and presents a number of experiments demonstrating the capabilities of BYODS.

With BYODS, any relation in an Ascent program can be tagged with a data structure provider:

```Rust
ascent! {
    #[ds(ascent_byods_rels::eqrel)]
    relation rel(u32, u32);
    // ...
}
```

In the above example, relation `rel` is backed by the `eqrel` data structure provider, which makes `rel` an equivalence relation.

In the above example, `ascent_byods_rels::eqrel` is the path of the module containing the macros required of a data structure provider. You can define your own data structure providers. To see what macros are required of a data structure provider, see `ascent::rel`, which is the default data structure provider.

The most important macros of a data structure privider are `rel_ind` and `rel_ind_common`. 

Macro invocations for `rel_ind_common` and other macros look like this:

```Rust
my_provider::rel_ind_common!(
  rel,          // rel name 
  (u32, u32),   // column types
  [[1]],        // logical indices
  ser,          // parallel (par) or serial (ser)
  (),           // user-specified params
)
```

These macro invocations evaluate to types that implement certain traits. `rel_ind!` returned types must implement `ToRelIndex`. This trait provides an indirection, allowing relation indices to share data (the type returned by `rel_ind_common!`). The type returned by the `to_rel_index` function of this trait is used to read the relation data, and must implement `RelIndexRead` and `RelIndexReadAll` traits. The type returned by `to_rel_index_write` is used to write new values to an index, and must implement `RelIndexWrite` and `RelIndexMerge`. 

These traits have `Key` and `Value` associated types. `Key` is the tuple of the indexed-on columns, and `Value` is the tuple of the remaining columns. For example, for an index [1, 2] of a relation `relation rel(Col0, Col1, Col2)`, the `Key` type would be `(Col1, Col2)` and the `Value` type would be `(Col0,)`. For `RelIndexReadAll`, the `Key` and `Value` types are references to tuples, or tuples of references (see `TupleOfBorrowed`). The same is true for the `Value` type of `RelIndexRead`.  

`rel_ind_common!` provides sharing of data between indices of a relation. Types returned by this macro invocation only need to implement `RelIndexMerge`.


To support parallel Ascent, relation indices need to implement parallel versions of the above traits. For example, `CRelIndexRead`, `CRelIndexReadAll`, and `CRelIndexWrite`.

## Lattices

`lattice` relations can also use custom data structure providers, via the `#[lds(..)]` attribute (the
ordinary `#[ds(..)]` attribute is rejected on lattices, and `#[lds(..)]` is rejected on non-lattice
relations):

```Rust
ascent! {
    #[lds(my_provider)]
    lattice shortest_path(u32, u32, Dual<u32>);
    // ...
}
```

A lattice keeps its rows in the built-in row store (rows are mutated in place by the lattice `join`
operation), so an `lds` provider only customizes the *index* data structures. The contract differs from a
plain `ds` provider in two ways, reflected in a separate set of macros:

- `lat_full_ind!` returns the type of the lattice "full index", which maps the key columns (all columns
  except the final lattice column) to the single row holding the joined value for that key. The returned
  type must support `index_get` (`RelIndexRead`), and, for parallel Ascent, `get_cloned` and `hash_usize`.
- `lat_rel_ind!` returns the type of every other (multi-valued) index. Because a row reference is
  re-inserted whenever its lattice value is joined upward, these indices must have *set* semantics (no
  duplicate row references).

In both cases the `Value` type is always `usize` (a reference into the row store). A provider that does not
define these macros simply cannot be used on a lattice. See `ascent::rel` for the default implementation,
which maps `lat_full_ind!` to `RelFullIndexType`/`CRelFullIndex` and `lat_rel_ind!` to
`LatticeIndexType`/`CRelIndex`/`CRelNoIndex`.

**TODO**: finish the guide