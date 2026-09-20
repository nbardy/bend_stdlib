# bend-stdlib cheatsheet

**Hosted cheatsheet: [nbardy.github.io/bend_stdlib](https://nbardy.github.io/bend_stdlib/)** (pretty, filterable — same content as below).

Proof-carrying standard library for Bend: 59 checked laws across
6 modules, zero runtime cost (proofs erase). Every entry below
is implemented and gated — `bend src/<mod>.bend` checks it,
`bend tests/test_<mod>.bend` runs its oracles (31 checks).

Modules: `order` (13, Bool/Cmp/Nat starter + twins) ·
`kernel` (15, LE relations + goals A/B/C) · `absurd` (5) ·
`perfect` (4, Array invariant) · `sorted` (16, flagship port) ·
`queue` (7, banker's queue).

Tags: **[def]** runs · **[law]** proves (checked at build, erased
at run) · **[type]** classifies. Import once per file:
`import ../src/order.bend as O` (or `kernel` / `absurd` /
`perfect` / `sorted`). Philosophy: `PHILOSOPHY.md`. Roadmap:
`docs/stdlibs.md`. Validation log: `docs/validation.md`.
Pretty HTML version of this page: `docs/cheatsheet.html`.

## Order & comparison

| | signature | what |
|---|---|---|
| [def] `SMax(a,b)` | `Nat, Nat -> Nat` | structural max, unfolds with `Nat.cmp` (`order`) |
| [def] `SMin(a,b)` | `Nat, Nat -> Nat` | structural min (`order`, `kernel`) |
| [law] `cmp_refl(a)` | `{Nat.cmp(a,a) == EQ}` | order reflexivity |
| [law] `ge_refl(a)` | `{Nat.is_ge(a,a) == True}` | via `cong` over `cmp_refl` |
| [law] `smax_ge_l/r` | `{is_ge(SMax(a,b),a/b) == True}` | twin max dominates both args |
| [law] `smin_le_l/r` | `{is_le(SMin(a,b),a/b) == True}` | twin min duals |
| [law] `max_bridge` | `{SMax(a,b) == Nat.max(a,b)}` | transport twin→Base; consumed by `nat_max_ge_*` |
| [law] `nat_max_ge_l/r` | `{is_ge(Nat.max(a,b),a/b) == True}` | Base-max facts via the bridge |
| [law] `pick_succ` | `pick(c,1+y,1+x) == 1+pick(c,y,x)` | branch commutes with `Succ` |
| [type] `LE(a,b)` | `Nat, Nat -> Data` | computed order: `Unit`/`Empty`, the evidence you pass as premise (`kernel`) |
| [law] `le_trans` | `LE(a,b) → LE(b,c) → LE(a,c)` | 3-way induction; everything ordering composes through this |
| [law] `le_add_r` | `LE(a,b) → LE(c+a,c+b)` | monotonicity, 5 lines |
| [law] `le_eq_r` | `{a==b} → LE(c,a) → LE(c,b)` | transport along equality |

## Bool & branching

| | signature | what |
|---|---|---|
| [law] `and_false` | `{Bool.and(a,False) == False}` | annihilation |
| [law] `and_comm` | `{and(a,b) == and(b,a)}` | four-case split |

`Bool.pick` is Bend's `if`; `pick_merge` (commute any `f`
through a branch) is next up, subsuming `pick_succ`.

## Nat arithmetic

| | signature | what |
|---|---|---|
| [law] `add_succ` | `{add(a,1+b) == 1+add(a,b)}` | induction on `a` |
| [def] `dbl(d)` | `Nat -> U32` | doubling spec of `Array.size` (`perfect`) |
| [law] `min_le_r` | `SMin`-driven min bound (`kernel`) | feeds `blit_bounds` |
| [law] `add_sub_cancel` | cancellation shape (`kernel`) | feeds `blit_bounds` |

## Impossible (absurdity)

| | signature | what |
|---|---|---|
| [law] `bool_absurd` | `{False == True} -> A` | ex falso via the `IsFalse` motive |
| [law] `cmp_absurd_lt_eq/lt_gt/eq_gt` | two positive `Cmp` views `-> A` | one arm each reduces to `False==True` |
| [law] `nat_absurd_zero_succ` | `{0n == 1n+x} -> A` | zero/succ discriminate via `IsZero` |

Premises are uninhabited by construction — these prove
*by checking*. Needed in every impossible arm of order proofs.

## Arrays & shape

| | signature | what |
|---|---|---|
| [type] `Perfect(T,d,a)` | `Type` | the missing invariant: depth-`d` perfect tree. Every Array law takes it first |
| [def] `snd_size(p)` | `Array<T> & U32 -> U32` | pair projection (Base only destructures; this names it) |
| [law] `size_node_snd` | `snd(size.node(ys,r)) == shl(snd(r))` | one-level size algebra |
| [law] `size_node_shl` | `snd(size(ANode)) == shl(snd(size(xs)))` | composed one level — the most composition linear affinity permits |
| [law] `perfect_new` | `Perfect(d, Array.new(d,v))` | constructors preserve it (Data-only, like `List.replicate`) |

Known wall, documented in `perfect.bend`: full `size` induction
needs the subtree twice — impossible on linear `Type`.

## Sorting

| | signature | what |
|---|---|---|
| [def] `LL.length(xs)` | `List -> Nat` | local length (concrete, no template trouble) |
| [type] `LEOr<x,h>` | `Data` | evidence sum the comparator returns — proof matches what the program branched on |
| [def] `le_case(x,h)` | `Nat, Nat -> LEOr` | total order decision |
| [def] `dec/insert/isort` | insertion sort, concrete Nat comparator | sidesteps the generic-comparator template ban |
| [type] `SortedB(xs,lo)` | `Type` | sortedness with lower-bound accumulator |
| [law] `sorted_ins/sorted_isort` | insert/sort preserve `SortedB` | ported flagship, 221 lines |
| [law] `len_ins/len_isort` | length preservation | no element lost |

## Containers (queue)

| | signature | what |
|---|---|---|
| [type] `Queue{f,r}` | `Data` | persistent banker's queue, Nat elements |
| [def] `push(q,x)` | `Queue, Nat -> Queue` | cons onto rear |
| [def] `pop(fuel,q)` | `Nat, Queue -> Queue & Maybe Nat` | fuel-bounded (classic pop isn't structural); `1+len` suffices, 0 answers `None` |
| [def] `to_list(q)` | `Queue -> List Nat` | logical contents: front ++ reverse rear |
| [law] `qapp_assoc` | append associativity | the composition everything stands on |
| [law] `qrev_acc` | `rev(r,acc) == append(rev(r,[]),acc)` | triple-use `+` binders |
| [law] `len_push` | `len(push) == 1+len` | via `order.add_succ` (cross-module reuse) |
| [law] `to_list_push` | push snocs the logical list | composes assoc + rev_acc |
| [law] `pop_cons/pop_rotate/pop_empty` | pop dispatch by equations | total spec, no cases missing |

## Intervals & matrices

| | signature | what |
|---|---|---|
| [type] `Iv{s,e,wf}` | `Data` | interval carrying its own `LE(s,e)` well-formedness |
| [type] `NoOv(xs,lo)` | `Type` | adjacency: next start bounded by previous end — the calendar premise |
| [type] `AllGE(xs,lo)` | `Type` | every start globally bounded |
| [law] `allge_weak` | push a bound down the list | `le_trans` consumer #1 |
| [law] `noov_allge` | `NoOv → AllGE` | adjacency implies global bound — goal A |
| [type] `SameLen(xs,ys)` | `Data` | computed length relation; mismatch arms are `Empty` |
| [def] `dot(xs,ys,e)` | `Nat` | total dot product, no runtime length check, no fallback |
| [type] `Conform(rows,v)` | `Type` | every row matches the vector — the matmul shape premise |
| [def] `matvec(rows,v,e)` | `List Nat` | shape-safe matvec |
| [law] `blit_bounds` | `LE(add(x,min(sw,sub(d,x))), d)` | writes stay on canvas — goal B |

## Against the Clojure cheatsheet

What maps, what deliberately doesn't (reasons: PHILOSOPHY F5):

| Clojure section | Bend status |
|---|---|
| Special forms, macros | N/A by design — no macros (termination + checker simplicity) |
| Lists, seqs (`map/filter/reduce`) | Present in Base; *laws* about them blocked by the template rule — per-comparator statements only |
| Vectors | Linear `Array` exists; persistent vector proposed (L5) |
| Maps, sets, sorted collections | String-only today; int/sorted maps proposed (L5) |
| Transients | N/A — linear `Array` *is* the transient story, different cut |
| Transducers, reducers, laziness | Blocked (no runtime closures, no infinites); fixed monomorphic kernels + fuel colists instead |
| Atoms, refs, agents, STM | Rejected by design — linear state + `Chan` cover it |
| Futures, promises, `core.async` | `fork`/`join` are futures; channels exist; `alt!` needs a runtime primitive (L9) |
| Multimethods, hierarchies | Rejected by design — type-directed dispatch |
| IO, files, network | Host ops exist; safe `Result` wrappers proposed |
| Coercions (`show`/`read`) | Exist in Base; roundtrip laws missing |
| Java interop | N/A — C/JS `effs` instead |
| `blit_bounds`-class laws | No counterpart anywhere — build-time bounds proofs that erase are this library's alone |

## Gates & upkeep

- `bend src/<mod>.bend` per module; `bend tests/test_<mod>.bend`
  runs 31 oracles (all PASS required).
- No new axioms beyond Base's host laws. Every new law names
  the consumer above it or the bug it prevents, in a comment.
- This page and `docs/cheatsheet.html` mirror each other —
  update both when adding functions.
