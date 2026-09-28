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
operation), so an `lds` provider supplies the relation's *index* data structures. It does so the same way a
`ds` provider does, through a shared value and the `ToRelIndex` indirection, so a provider can back all of
a lattice's indices with a single data structure instead of one per index. The macros are:

- `rel_codegen!`, invoked exactly as it is for a `ds` provider, for any item the provider needs to emit.
- `lat_ind_common!(name, field_types, [indices], ser|par, ())` returns the type of the value shared by all
  of the relation's indices, the lattice counterpart of `rel_ind_common!`. Ascent keeps one per relation
  version (total, delta and new), merges them with `RelIndexMerge` (and freezes them with `Freezable` in
  parallel Ascent) like any index, and stores the total one in the program struct as `__<relation>_ind_common`.
  It must also implement `LatIndCommon<Key, Lat>` (serial) or `CLatIndCommon<Key, Lat>` (parallel), whose
  `observe` hook is described below; both methods default to doing nothing.
- `lat_full_ind!(.., key_type, value_type)` returns the type of the lattice "full index", which maps the key
  columns (all columns except the final lattice column) to the single row holding the joined value for that key.
- `lat_rel_ind!(.., [index], key_type, value_type)` returns the type of every other (multi-valued) index,
  including the index over all columns. Because a row reference is re-inserted whenever its lattice value is
  joined upward, these indices must have *set* semantics (no duplicate row references).

Both index types must implement `ToRelIndex<C>`, where `C` is the `lat_ind_common!` type, and generated code
reads and writes them only through the views that returns, exactly as for a `ds` provider:
`RelIndexRead`/`RelIndexReadAll` and `RelIndexWrite`/`RelIndexMerge` in serial Ascent, and in parallel Ascent
also `CRelIndexRead`/`CRelIndexReadAll` and `CRelIndexWrite`, plus `Freezable` on the index type itself. The
full index's view must additionally implement `CLatFullIndexRead` in parallel Ascent, which provides the
`get_cloned` and `hash_usize` lookups used when inserting under the lattice insertion mutex. Only the traits
used by a given program are needed: an index that is never read needs no read views. The `Value` of every
lattice index is `usize`, a row reference into the built-in row store.

### The `observe` hook

The views only ever see `usize` row references. `LatIndCommon::observe(&mut self, key, value)` (and
`CLatIndCommon::c_observe(&self, key, value)` in parallel Ascent) is the one place a provider sees a row's
key columns and lattice value, letting it maintain a derived view of the relation. It is called on the
`lat_ind_common!` value of the relation's *new* version for every row that actually enters the relation,
and again whenever an existing row's lattice value changes:

- Once per row derived by a rule, after it is pushed, and once more for each subsequent `join` that
  changes its value. A proposed value that *loses* the join — one that is already subsumed by the row's
  current value — is never observed.
- Once per row placed in the relation directly, rather than derived: a pre-populated relation field, or a
  `= expr` relation initialization. Those rows are observed on the program struct's
  `__<relation>_ind_common` when they are first indexed. Re-indexing (a second `run()`, or an explicit
  `update_indices()`) does not observe an already-observed row again.

Anything `observe` records reaches the program struct's `__<relation>_ind_common` only through the
provider's `RelIndexMerge` implementation, which must therefore carry it from version to version.

`value` is always the value the row holds *after* the join, never the value that was proposed. So for each
key, the values a provider observes are strictly increasing in the lattice order, and the last one it
observes is the value the row settles on. In parallel Ascent `c_observe` runs on rayon worker threads and may
be called concurrently for different keys, and for the same key in a nondeterministic order — but each
observed value is one the row genuinely held, and the final value of every key is always observed.

A provider that does not define all four macros cannot be used on a lattice. See `ascent::rel` for the
default implementation, which maps `lat_ind_common!` to `()`, `lat_full_ind!` to
`RelFullIndexType`/`CRelFullIndex`, and `lat_rel_ind!` to `LatticeIndexType`/`CRelIndex`/`CRelNoIndex`. For a
provider that backs all of a lattice's indices with one `BTreeMap`, in both serial and parallel Ascent, see
`ascent_tests/src/btree_lat_ds.rs`.

**TODO**: finish the guide