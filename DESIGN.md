# relax-completeness — Completeness theory for capped-relaxation SSSP

Lean 4 / Mathlib formalization. Package `relax-completeness`, default target `RelaxLFP`.
Toolchain `leanprover/lean4:v4.34.1`, Mathlib pinned at `d13f23b7` (copied from the
proven-working sssp-bridge scaffold; manifest copied verbatim — it has no root entry).

## The three pillars (fixed architecture)

**(i) Fair-schedule iteration → canonical point.** FINITE case, direct proof.
Any fair schedule of capped point-relaxations converges, and its limit is characterized
order-theoretically. Tonight's work; see statement below.

**(ii) That point = the true distances.** Via the AFP ShortestPath pattern: the limit
`c ≤ T c`, `c ≤ d₀` gives `c ≤ δ` by path telescoping; the invariant `δ ≤ dₙ` for all `n`
(monotonicity + `δ = T δ` + capping) gives `δ ≤ c`. Together with (i)'s greatestness this
also identifies `c` with `lfp T` inside `↓d₀` when `T d₀ ≤ d₀`. Later.

**(iii) Box-certification.** `settled-under-monotone-cut ⇒ final + frozen-lock`, the
frozen-lock device from Zhao's fast-sweeping method. Later.

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
is a simple-path sum" is the pillar-(ii) seam and is left as a named sorry.

## Deviation from Daggitt (arXiv 2012.01686) — deliberate

With capping, the honest abstract conclusion is **greatest post-fixed point of T below
`d₀`**, not "least fixed point of T below start": `x ≤ d₀ ∧ x ≤ T x` admits degenerate
elements (e.g. the constant-0 function with nonnegative weights), so "least" is false in
general. When `T d₀ ≤ d₀` (true for the SSSP ⊤-start: `T d₀ ≤ d₀`), greatest-post-fixed
below `d₀` coincides with the least fixed point of `T` in `↓d₀`; that identification is
assigned to pillar (ii). All finite-setting proofs here are elementary lattice arguments.

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

## Status / next step

See `RelaxLFP.lean` docstring at the end for the honest status ledger.
