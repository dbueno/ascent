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
operation), so an `lds` provider only customizes the *index* data structures, plus a state value of its own.
The contract differs from a plain `ds` provider, and is expressed by a separate set of macros:

- `rel_codegen!` is invoked exactly as it is for a `ds` provider, for any item the provider needs to emit.
- `lat_full_ind!` returns the type of the lattice "full index", which maps the key columns (all columns
  except the final lattice column) to the single row holding the joined value for that key.
- `lat_rel_ind!` returns the type of every other (multi-valued) index. Because a row reference is
  re-inserted whenever its lattice value is joined upward, these indices must have *set* semantics (no
  duplicate row references).
- `lat_state!` returns the type of a value of the provider's own, one per lattice, stored in the generated
  program struct (as a `pub` field named `__<relation>_lat_state`). The fixpoint loop never versions,
  swaps, or clears it, so it is where a provider accumulates anything it derives. It must implement
  `Default`, and in parallel Ascent it is shared across rayon worker threads, so it must be `Sync` and use
  interior mutability.
- `lat_observe!` is a hook that hands the provider a row's key columns and lattice value:
  `lat_observe!(name, field_types, [indices], ser|par, (), &state, &key, &value)`. Unlike the index macros
  (whose `Value` is always `usize`), this is the one place a provider sees the lattice value itself,
  letting it maintain a derived view of the relation — e.g. an all-pairs shortest-paths matrix computed
  from the edge weights. The default provider leaves it as a no-op.

Both index types must be drop-in replacements for the built-in ones: generated code drives them through
the same traits (`RelIndexRead`/`RelIndexWrite`/`RelIndexMerge`, and their `CRel` counterparts plus
`Freezable` in parallel Ascent) and uses the `usize` values it gets back to index into the built-in row
store. For `lat_full_ind!` and `lat_rel_ind!` the `Value` type is therefore always `usize`.

### When `lat_observe!` is called

`lat_observe!` is called for every row that actually enters the relation, and again whenever an existing
row's lattice value changes:

- Once per row derived by a rule, after it is pushed, and once more for each subsequent `join` that
  changes its value. A proposed value that *loses* the join — one that is already subsumed by the row's
  current value — is never observed.
- Once per row placed in the relation directly, rather than derived: a pre-populated relation field, or a
  `= expr` relation initialization. Those rows are observed when they are first indexed. Re-indexing (a
  second `run()`, or an explicit `update_indices()`) does not observe an already-observed row again.

`$val` is always the value the row holds *after* the join, never the value that was proposed. So for each
key, the values a provider observes are strictly increasing in the lattice order, and the last one it
observes is the value the row settles on. In parallel Ascent the hook runs on rayon worker threads and may
be called concurrently for different keys, and for the same key in a nondeterministic order — but each
observed value is one the row genuinely held, and the final value of every key is always observed.

A provider that does not define all five macros simply cannot be used on a lattice. See `ascent::rel` for
the default implementation, which maps `lat_full_ind!` to `RelFullIndexType`/`CRelFullIndex`,
`lat_rel_ind!` to `LatticeIndexType`/`CRelIndex`/`CRelNoIndex`, `lat_state!` to `()`, and `lat_observe!` to
a no-op. For a worked example of a provider that uses `lat_state!` and `lat_observe!` to do real work, see
`shortest_path_ds` in `ascent_tests/src/tests.rs`.

**TODO**: finish the guide