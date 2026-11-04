# relax-completeness — Completeness theory for capped-relaxation SSSP

Lean 4 / Mathlib formalization. Package `relax-completeness`, default target `RelaxLFP`.
Toolchain `leanprover/lean4:v4.34.1`, Mathlib pinned at `d13f23b7` (copied from the
proven-working sssp-bridge scaffold; manifest copied verbatim — it has no root entry).

## The three pillars (fixed architecture)

**(i) Fair-schedule iteration → canonical point.** FINITE case, direct proof.
Any fair schedule of capped point-relaxations converges, and its limit is characterized
order-theoretically. Tonight's work; see statement below.

**(ii) That point = the true distances.** DONE — `Pillar2.lean` + the value-universe half of
`RelaxLFP.lean`, zero sorries. Headline: `canonical_point_eq_distV` — the fair-iteration
limit is the greatest fixed point of `T_BF` below `dInit` and equals `distV` (infimum of
walk costs). `≤` arm: post-fixed points sit below every walk cost (`le_cost_of_le_T_BF`,
the AFP `dist_le_cost` template :73–100) hence below `distV` (`le_distV_of_le_T_BF`).
`≥` arm: `distV` is itself post-fixed and below `dInit` (`distV_le_T_BF`, `distV_le_dInit`),
absorbed by pillar (i)'s greatestness. The AFP `num`/`just`/`witness_path` machinery is
NOT needed: defining `d*` as an infimum over walks (not an attained minimum) deletes
`witness_path` — the NOTE's biggest rebuild item — entirely. The seam
(`iterate_range_finite`: every iterate value is `⊤` or a simple-walk cost) is closed via
`iterate_value_universe` with a prefix-tightness invariant (`Walk.Tight`, `Walk.IsPrefix`):
when the proposal attains at a `u₀` whose witness walk passes through the updated vertex,
the walk's prefix squeezes the stored value onto a simple-walk cost.
Deviation (documented in `Pillar2.lean`): `lfp T_BF` is degenerate (0-weight self-loop),
so the identification proved is greatest-fixed-point-below-`dInit` = `distV`, not lfp.

**(iii) Box-certification.** DONE — `Pillar3.lean`, zero sorries. Headline:
`CertifiedRun.certified_settled_final` — **settlement under a certified boundary implies
finality** (`v ∈ U_t ⇒ d_t v = distV w s v`) for the minimal synchronous engine
(`CertState = (d, U, B)`; steps: `relax` at `u ∈ U` fires the out-edge push
`pushUpdate`, `settle` at `v ∉ U` under rule `d v ≤ B` + box condition
`B ≤ ⨅ (u ∉ insert v U), d u` — the beyond-dijkstra `dB[D] ≥ B′` invariant — and fires
the push at `v` **atomically**). Support: invariant 1 `distV_le_d` (values overestimate
truth), `d_antitone` (monotone nonincreasing), `settled_edges_relaxed` (settled out-edges
stay relaxed — the induction fuel), `frozen_lock` (Zhao: settled ⇒ value never changes
again; two-line consequence of certification + overestimation), `trivialRun`
(non-vacuity: settle `s` first, re-relax forever; the `⊤` start boundary forces the
first settlement to be the source).
**Two forced modelling decisions (honesty ledger):**
1. *Settle-without-relaxation is a real loophole.* A pure settle step (no atomic push)
   makes the certification theorem FALSE: on `s →(1) a →(1) v`, `s →(5) v` — settle `s`
   (B=1), relax at `s`, settle `a` with B=5 (rule `1≤5` ✓, box `5 ≤ d v = 5` ✓), then
   settle `v` with stale `d v = 5 ≤ B` over the empty frontier — while `distV v = 2`.
   The synchronous engine therefore fires the out-edge updates as part of settling
   ("settlement of u fires T_u", Dijkstra/FMM semantics). The proof consumes this via
   `settled_edges_relaxed`.
2. *The box ranges over the post-settle unsettled set* (`u ∉ insert v U` — "boundary
   never exceeds the *remaining* unsettled values"). Ranging over `u ∉ U` (incl. `v`)
   would force `d v = B` at every settle: extract-min with a frozen boundary, a strictly
   smaller engine class. Present rules = weaker premises = stronger theorem; with `B`
   existentially quantified they collapse exactly to Dijkstra extract-min
   (`∃ B, d v ≤ B ≤ ⨅ frontier d ↔ d v ≤ ⨅ frontier d`). The async echo-sweep engine is
   the refinement: echo sweeps re-fire `relax` steps and `frozen_lock` licenses skipping
   re-expansion of certified vertices.
Proof shape: simultaneous induction (certification + relaxed-out-edges); the settle case
runs the first-unsettled-on-shortest-walk argument as a two-bound walk induction
(`cost Q < x` ∧ `cost Q < d y` ⇒ False): settled penultimate vertex ⇒ relaxed-edge cap
contradiction; unsettled penultimate ⇒ box condition chains the bound and the shorter
prefix recurses; `nil` ⇒ `0 < d s = 0`.

## Setting

- `V` finite (`Fintype`, `DecidableEq`), weights `w : V → V → ℝ≥0∞`, source `s`.
- `T : (V → α) →o (V → α)` a monotone (OrderHom) "proposal" operator on a lattice `α`
  (instance `T_BF w s` with `T d s = 0`, `T d v = ⨅ u, d u + w u v` on `ℝ≥0∞`).
- **Capped** point update: `capUpdate T v d = fun w => if w = v then d v ⊓ T d v else d w`
  — the cap is what makes iterates antitone without any assumption on `T` beyond
  monotonicity.
- Iterates: `iterate T seq d₀ 0 = d₀`, `iterate (n+1) = capUpdate T (seq n) (iterate n)`.
- **Fairness**: `∀ v N, ∃ n ≥ N, seq n = v` (definitionally `Filter.Frequently
  (fun n => seq n = v) atTop`; stated arithmetically to avoid filter-API friction).

## Pillar (i) statement (Lean-ish)

```
theorem converge_of_stable (T : (V → α) →o (V → α)) (seq : ℕ → V) (d₀ : V → α)
    (hStable : ∃/∀ N, ∀ n ≥ N, iterate T seq d₀ n = iterate T seq d₀ N)
    (hFair   : ∀ v N, ∃ n ≥ N, seq n = v) :
    (∀ v, c v ≤ T c v)                -- post-fixed point of T
    ∧ c ≤ d₀                          -- below start
    ∧ ∀ x, x ≤ d₀ → x ≤ T x → x ≤ c   -- GREATEST post-fixed point below d₀
where c = iterate T seq d₀ N

theorem iterate_eventuallyConstant (hrange : ∀ v, (range fun n => iterate T seq d₀ n v).Finite) :
    ∃ N, ∀ n ≥ N, iterate T seq d₀ n = iterate T seq d₀ N
```

## Well-foundedness design (the key discreteness)

No ω-cpo/ω-continuity, no pseudoperiod machinery, no topology on ℝ: the value universe
per component is the set of **simple-path sums** (plus ⊤). On a finite graph that set is
finite, so each component's iterate sequence is antitone with finite range ⇒ eventually
constant (strict-drop indices inject into the finite range); `Fintype V` promotes
per-component stabilization to a uniform `N`. The instance lemma "every value ever taken
is a simple-path sum" (`iterate_value_universe` ⇒ `iterate_range_finite`) was the
pillar-(ii) seam and is now CLOSED (prefix-tightness induction, see pillar (ii) above).

## Deviation from Daggitt (arXiv 2012.01686) — deliberate

With capping, the honest abstract conclusion is **greatest post-fixed point of T below
`d₀`**, not "least fixed point of T below start": `x ≤ d₀ ∧ x ≤ T x` admits degenerate
elements (e.g. the constant-0 function with nonnegative weights), so "least" is false in
general. When `T d₀ ≤ d₀` (true for the SSSP ⊤-start: `T d₀ ≤ d₀`), greatest-post-fixed
below `d₀` coincides with the least fixed point of `T` in `↓d₀`; that identification is
assigned to pillar (ii). All finite-setting proofs here are elementary lattice arguments.
**Pillar-(ii) resolution:** for `T_BF` the lfp identification is FALSE as stated (a
`0`-weight self-loop makes constant-`0` a fixed point below `dInit`, so the lfp in `↓d₀`
is degenerate); what pillar (ii) proves instead — and what SSSP needs — is that the
canonical point is the GREATEST fixed point below `dInit` and equals `distV`
(`fixed_of_greatest_postFixed` + `canonical_point_eq_distV`).

## Citations

- Michael J. Daggitt, arXiv:2012.01686 — asymptotic/relaxation fixed-point framework.
  **Cite-only, unlicensed**; we deliberately simplify to the finite setting rather than
  port any proof structure.
- arXiv:2106.01184 — ideas-only (asymptotics of relaxed Bellmann–Ford).
- AFP `ShortestPath` (Blechschmidt) — pillar (ii) pattern for distance characterization.
- Zhao, fast-sweeping methods — frozen-lock device for pillar (iii).

## API landmine bank (carried from tonight's sibling work; add new hits here)

| Landmine | Workaround |
|---|---|
| `Real.log_pow` takes explicit base | pass it |
| `Real.rpow_one` explicit | pass it |
| `Real.log_le_self` wants `0 ≤` | supply explicitly |
| `Real.zero_rpow` wants `≠ 0` | case-split first |
| `Nat.sqrt_pos` is an IFF | use `nat_sqrt_pos.mp` shape |
| `linarith` can't see division-atom nonnegativity | add `div_nonneg` haves |
| rpow nonneg wrappers must COMPOSE | chain `RealMath.rpow_nonneg`-style, don't rewrite |
| (new) `min`/`⊓`: use `le_inf`/`inf_le_left/right` in plain `Lattice` (no `min` lemmas); `inf_le_right` takes NO explicit args in this pin | |
| (new) Pi-level `≤`: `intro w` works after instance unfold; `‹_›` + `split` on `ite` with `x = x` condition yields `¬True` hypothesis — handle via `simp at h` | |
| (new, pin d13f23b7) module moves: `Mathlib.Order.CompleteLattice` → `.Basic`/`.Lemmas` (dir); `Mathlib.Data.Finset.Lattice` → `.Fold` (has `sup`/`le_sup`); `Mathlib.Data.ENNReal.Basic` → `Mathlib.Basic.ENNReal.Basic`, `ℝ≥0∞` is SCOPED notation → `open ENNReal` | |
| (new, pin d13f23b7) `Set.Finite.ofInjOn` → snake_case `Set.Finite.of_injOn (mapsTo) (injOn) (finite)`; `s.toFinset` → `h.toFinset` on the FINITE PROOF, membership `h.mem_toFinset` | |
| (new, pin d13f23b7) core `if_pos`/`if_neg` deprecated → `ite_eq_left hc` (= then-branch!) / `ite_eq_right hnc` (= else-branch!) — names are reversed vs intuition | |
| (new, pin d13f23b7) `add_le_add_left (h) (c) : b*a ≤ c*a` — left/right SWAPPED vs classic; check orientation before use | |
| (new, pin d13f23b7) `iInf_le`/`le_iSup` take `(f) (i)` BOTH explicit; `le_iInf (h)` fine; `iInf_mono (h : ∀ i, f i ≤ g i)` fine (to_dual of `iSup_mono`) | |
| (new, pin d13f23b7) `Finset.le_sup` cannot infer `f` from a bare-variable goal — pass `(f := id)` explicitly | |
| (new) `rw` is syntactic: `M+1+(k+1)` ≠ `M+1+k+1` — `rw [Nat.add_succ]` first | |
| (new) anonymous `⟨a,b,c,d⟩` must match the statement's right-nested `∧` structure — parenthesize sub-conjunctions explicitly | |
| (new, pillar ii) `subst h` with `h : x = y` where BOTH sides are free locals may eliminate the WRONG one — it ate the section var `s` (3x) and a `cases` binder `b` (1x), leaving "Unknown identifier". Always write `subst v` naming the variable to eliminate | |
| (new, pillar ii) this pin's `zero_le : ∀ {α} [LE α] [Zero α] [IsBotZeroClass α] {a : α}, 0 ≤ a` is ALL-IMPLICIT — `zero_le _` fails "Function expected"; use bare `zero_le` | |
| (new, pillar ii) `ENNReal.iInf_add` lives in `Mathlib.Basic.ENNReal.Operations`, NOT imported by `Mathlib.Basic.ENNReal.Basic` | |
| (new, pillar ii) `List.nodup_append` yields `l.Nodup ∧ l'.Nodup ∧ ∀ a ∈ l, ∀ b ∈ l', a ≠ b` — the third component is the UNFOLDED disjoint; `.disjoint` dot-projection fails, apply it as a 4-arg function | |
| (new, pillar ii) `simp ... at h` AUTO-CLOSES the goal when `h` simplifies to `False` — any chained tactic (`; omega`) then dies "No goals to be solved". Same with `rw` on `x ≤ x` goals (le_rfl is `@[refl]`): drop the trailing `exact le_rfl` | |
| (new, pillar ii) `omega` cannot see through `p ∈ {q | cond}` membership — insert `show <arith statement>` (defeq via `Set.mem_setOf`) before `omega` | |
| (new, pillar ii) `Finset.induction_on` IH is gated on `a ∉ s` — unusable when the `a ∈ s` case needs it. For ℝ≥0∞ iInf attainment use `Set.exists_min_image s f (hfin : s.Finite) (hne : s.Nonempty)` from `Mathlib.Data.Set.Finite.Lemmas`. ABSENT in this pin: `Finset.min'`, `Set.Finite.min'`, `Set.Finite.exists_eq_iInf`, `ENNReal.iInf_eq_iMin`, `Finset.iInf_eq_sInf` | |
| (new, pillar ii) `Set.finite_iUnion` lives in `Mathlib.Data.Set.Finite.Lattice`; `List.Nodup.length_le_card` and `List.finite_length_le` exist | |
| (new, pillar ii) `rw` through a dependent proof arg fails "motive is not type correct" (e.g. rewriting `insert a ∅` inside `(insert a ∅).inf' H f` where `H` mentions it) — prefer formulations without dependent proof args | |
| (new, pillar ii) `cases` on a term whose family INDEX is a non-variable (e.g. `q : Walk s (seq n)`) cannot substitute the index in constructor branches — factor decomposition lemmas with a free endpoint var (`exists_step_of_endpoint_ne`) and instantiate | |
| (new, pillar ii) `obtain ⟨n, rfl⟩` from `Set.mem_range` leaves a beta-redex `(fun n => f n) n` in the goal that `rw [h : f n = _]` cannot match — `dsimp only` first | |
| (new, pillar ii) `le_antisymm` takes (A ≤ B) then (B ≤ A); with `⊓` displayed as `min` in ℝ≥0∞ it is easy to flip — check which side is the goal's LHS | |
| (new, pillar iii) `Finset.insert` is NOT a constant in this pin — use generic `insert` (Insert.insert); `le_of_not_lt`/`lt_of_not_le` ABSENT — use `not_lt.mp`/`not_le.mp`; `Finset.not_mem_singleton` ABSENT — derive `v ≠ s` from `v ∉ insert s ∅` by `intro heq; exact h (by rw [heq])` (the rw CLOSES the goal by defeq — a trailing `simp` then dies "No goals") | |
| (new, pillar iii) `cases Q` on `Q : Walk s y` with `y` a LOCAL: the endpoint index ABSORBS the `step` binder — `\| step a b q` leaves `b` "Unknown identifier" (replaced by `y` everywhere). Write `\| step a _ q` and refer to the endpoint as `y`. (Sibling of the non-variable-index landmine above.) | |
| (new, pillar iii) `obtain ⟨k, rfl⟩ := Nat.le.dest h` then `induction k`: the residual `h : m ≤ m + k` mentions `k` and gets swept into the motive (IH gains a hypothesis arrow) — `clear h` before inducting | |
| (new, pillar iii) `structure Foo where` under section variables auto-includes them as EXPLICIT params — `CertState` became `CertState V`; declare `(V : Type u)` in the header yourself. Dot-notation `run.lemma` needs the lemma named inside `namespace CertifiedRun` | |
| (new, pillar iii) `set_option linter.unusedSectionVars false in universe u v` is a syntax ERROR and bare `... false` before other commands must be standalone (with `in` it applies to only the next decl); `omit [X] in` may NOT follow a doc comment ("unexpected token") — set the option file-wide instead | |

## Status / next step

All three pillars COMPLETE, `lake build` green, zero sorries. See the status ledger
docstrings at the end of `RelaxLFP.lean`, `Pillar2.lean` (headline:
`canonical_point_eq_distV`), and `Pillar3.lean` (headline:
`certified_settled_final` + `frozen_lock`). `lakefile.toml` defaultTargets:
`RelaxLFP`, `Pillar2`, `Pillar3`. Next (successor's choice): the async echo-sweep
refinement of `Pillar3` (echo sweeps as re-fired `relax` steps, `frozen_lock` as the
skip-re-expansion license), or wiring the certification layer to the beyond-dijkstra
engine's `dB[D] ≥ B′` cut sets (Lemmas W/V/d2 of the cousot recast are the missing
box verification there).
