/-
Copyright (c) 2026. Capped-relaxation SSSP completeness (pillar ii).
-/
import RelaxLFP
import Mathlib.Basic.ENNReal.Operations

open ENNReal

namespace RelaxLFP

universe u v

/-!
# Pillar (ii): the canonical point is the true shortest-distance vector

Deviation from the planned `lfp T_BF = d*` headline (fully documented in
`DESIGN.md`): the *least* fixed point of `T_BF` is degenerate in general — a
`0`-weight self-loop at `v` makes every constant-at-`v` value a fixed point, so
`T_BF`'s least fixed point is `0` at `v` while the true distance is `⊤`.  What
SSSP needs — and what this file proves — is that pillar (i)'s canonical point
(the greatest post-fixed point of `T_BF` below `dInit`, i.e. the fair-iteration
limit) is the *greatest* fixed point of `T_BF` below `dInit` and equals the true
shortest-distance vector `distV` (infimum of walk costs, cf. the AFP `μ`).

Proof architecture (per `/private/tmp/afp-uniqueness/NOTE.md`):
* `≤` arm: any post-fixed point of `T_BF` lies below every walk cost
  (`le_cost_of_le_T_BF`, the AFP `dist_le_cost` template :73–100, pure
  induction on the walk; only the triangle inequality is used, and `ℝ≥0∞`
  weights are nonnegative by construction).
* `≥` arm: `distV` is itself a post-fixed point below `dInit`
  (`distV_le_T_BF`, `distV_le_dInit`), so it lies below the canonical point by
  pillar (i) greatestness.  The AFP `num`/`just` machinery is not needed: the
  `just` axiom is the free post-fixed inequality, and defining `d*` as an
  infimum over walks (not an attained minimum) deletes `witness_path` — the
  biggest rebuild item flagged in the NOTE — entirely.
-/

/-! ## SSSP instance: the start vector is a pre-fixed point (job 1)

The walk machinery (`Walk`, `cost`, `verts`, `IsSimple`, `IsPrefix`, `Tight`) now lives
in `RelaxLFP.lean` — it is what closes the value-universe seam there. -/

section SSSP

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Job 1.**  The standard `⊤`-start vector is a pre-fixed point of `T_BF`
(the subsidized-start invariant: the initial overestimate is sound). -/
theorem T_BF_le_dInit (w : V → V → ℝ≥0∞) (s : V) : T_BF w s (dInit s) ≤ dInit s := by
  intro v
  by_cases h : v = s
  · subst h; simp [T_BF_apply]
  · simp only [T_BF_apply, dInit, ite_eq_right h]
    exact le_top

end SSSP

/-! ## Greatest post-fixed below `d₀` = greatest fixed below `d₀` (job 2) -/

section Bridge

variable {V : Type u} {α : Type v} [Lattice α] [DecidableEq V]
    {T : (V → α) →o (V → α)} {d₀ c : V → α}

/-- **Job 2.**  If `T d₀ ≤ d₀` and `c` is the greatest post-fixed point of `T`
below `d₀`, then `c` is a fixed point and dominates every fixed point of `T`
below `d₀` — i.e. `c` is the **greatest fixed point of `T` in `↓d₀`**.

Note (deviation, see DESIGN.md): the original DESIGN.md pillar-(ii) sketch
announced "the lfp of `T` in `↓d₀`".  That identification is false in general
(a `0`-weight self-loop gives `T_BF` degenerate fixed points in `↓d₀` including
the constant-`0` vector), so the greatest-fixed-point statement is what is
proved; for `T_BF` the greatest fixed point below `dInit` is the true distance
vector, which is the content Bellman–Ford correctness needs. -/
theorem fixed_of_greatest_postFixed (hd₀ : T d₀ ≤ d₀) (hc₀ : c ≤ d₀) (hc : c ≤ T c)
    (hgreatest : ∀ x, x ≤ d₀ → x ≤ T x → x ≤ c) :
    T c = c ∧ ∀ x, x ≤ d₀ → T x = x → x ≤ c := by
  refine ⟨le_antisymm ?_ hc, fun x hx₀ hx => hgreatest x hx₀ (le_of_eq hx.symm)⟩
  exact hgreatest (T c) ((T.monotone' hc₀).trans hd₀) (T.monotone' hc)

end Bridge

/-! ## True distances as walk-cost infima (job 4 core) -/

section Dist

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The true shortest-distance vector: for each `v`, the infimum of the costs
of all walks `s → v`.  Nonempty index (`Walk.step Walk.nil v`), but the infimum
would be `⊤` on an empty family anyway, matching "unreachable". -/
noncomputable def distV (w : V → V → ℝ≥0∞) (s : V) : V → ℝ≥0∞ :=
  fun v => ⨅ p : Walk s v, Walk.cost w p

/-- Post-fixed points of `T_BF` sit below the cost of every walk (AFP
`dist_le_cost` template, ShortestPath.thy:73–100). -/
theorem le_cost_of_le_T_BF {w : V → V → ℝ≥0∞} {s : V} {x : V → ℝ≥0∞}
    (hx : x ≤ T_BF w s x) {v : V} (p : Walk s v) : x v ≤ Walk.cost w p := by
  induction p with
  | nil =>
      have h0 : x s ≤ 0 := by simpa [T_BF_apply] using hx s
      simpa using h0
  | step a b q ih =>
      by_cases hsb : b = s
      · subst b
        have h0 : x s ≤ 0 := by simpa [T_BF_apply] using hx s
        exact h0.trans zero_le
      · have h2 : x a + w a b ≤ Walk.cost w q + w a b := add_le_add_left ih (w a b)
        calc x b ≤ T_BF w s x b := hx b
          _ ≤ x a + w a b := T_BF_le_edge hsb a
          _ ≤ Walk.cost w (Walk.step a b q) := by
              rw [Walk.cost_step]; exact h2

/-- The true-distance vector is a post-fixed point of `T_BF` (triangle
property: one more hop cannot beat the infimum). -/
theorem distV_le_T_BF (w : V → V → ℝ≥0∞) (s : V) : distV w s ≤ T_BF w s (distV w s) := by
  intro v
  by_cases h : v = s
  · subst v
    have h0 : T_BF w s (distV w s) s = 0 := by simp
    rw [h0]
    exact (iInf_le _ (Walk.nil : Walk s s)).trans_eq (Walk.cost_nil w s)
  · rw [T_BF_apply_of_ne h]
    apply le_iInf
    intro u
    show ⨅ p : Walk s v, Walk.cost w p ≤ (⨅ q : Walk s u, Walk.cost w q) + w u v
    rw [ENNReal.iInf_add]
    apply le_iInf
    intro q
    exact iInf_le _ (Walk.step u v q)

/-- The true distances sit below the standard start vector. -/
theorem distV_le_dInit (w : V → V → ℝ≥0∞) (s : V) : distV w s ≤ dInit s := by
  intro v
  by_cases h : v = s
  · subst v
    have h0 : dInit s s = 0 := by simp [dInit]
    rw [h0]
    exact (iInf_le _ (Walk.nil : Walk s s)).trans_eq (Walk.cost_nil w s)
  · have h0 : dInit s v = ⊤ := by simp [dInit, h]
    rw [h0]
    exact le_top

end Dist

/-! ## Assembly: the canonical point is the true distance vector (jobs 1 + 3) -/

section Assembly

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Job 1 (the ≤ arm).**  Any post-fixed point of `T_BF` lies below the true distance
vector: by `le_cost_of_le_T_BF` it lies below the cost of every walk `s → v`, hence below
their infimum `distV w s v`. -/
theorem le_distV_of_le_T_BF {w : V → V → ℝ≥0∞} {s : V} {c : V → ℝ≥0∞}
    (hc : c ≤ T_BF w s c) : c ≤ distV w s :=
  fun v => le_iInf fun p => le_cost_of_le_T_BF hc p

/-- **Job 3 — THE HEADLINE.**  The fair capped-relaxation limit — pillar (i)'s canonical
point, i.e. the greatest post-fixed point of `T_BF` below `dInit` — is the greatest FIXED
point of `T_BF` below `dInit` and equals the true shortest-distance vector `distV` (the
infimum of walk costs).

`≤ distV`: job 1, since the canonical point is post-fixed (`c ≤ T c`).
`≥ distV`: `distV` is itself post-fixed and below `dInit` (`distV_le_T_BF`,
`distV_le_dInit`), so pillar (i)'s greatestness absorbs it.
Fixedness: `fixed_of_greatest_postFixed` + `T_BF_le_dInit`.

Depends on `iterate_range_finite` in `RelaxLFP.lean` — the value-universe seam,
now CLOSED there via `iterate_value_universe` (simple-walk costs + prefix tightness). -/
theorem canonical_point_eq_distV (w : V → V → ℝ≥0∞) (s : V) (seq : ℕ → V)
    (hFair : ∀ (v : V) (M : ℕ), ∃ n, M ≤ n ∧ seq n = v) :
    ∃ N c, T_BF w s c = c
      ∧ (∀ n, N ≤ n → iterate (T_BF w s) seq (dInit s) n = c)
      ∧ c = distV w s := by
  obtain ⟨N, c, ⟨hcT, hc0, hmax⟩, hstable⟩ :=
    fair_iteration_complete (T_BF w s) seq (dInit s) hFair (iterate_range_finite w s seq)
  have hfix : T_BF w s c = c :=
    (fixed_of_greatest_postFixed (T_BF_le_dInit w s) hc0 hcT hmax).1
  refine ⟨N, c, hfix, hstable, le_antisymm ?_ ?_⟩
  · exact le_distV_of_le_T_BF hcT
  · exact hmax (distV w s) (distV_le_dInit w s) (distV_le_T_BF w s)

end Assembly

end RelaxLFP
