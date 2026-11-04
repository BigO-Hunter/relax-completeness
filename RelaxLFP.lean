/-
Copyright (c) 2026. Capped-relaxation SSSP completeness (pillar i).
-/
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Hom.Lattice

open ENNReal

/-!
# Capped relaxation SSSP — completeness theory, Pillar (i)

Fair-schedule capped relaxation converges to the canonical post-fixed point below the
start vector.  Architecture (see `DESIGN.md`):

* (i) fair-schedule iteration → canonical point — THIS FILE, finite case, direct proof;
* (ii) that point = true distances — later (AFP ShortestPath pattern);
* (iii) box-certification / frozen-lock — later (Zhao fast-sweeping).

Design notes:
* The update is **capped** (`d v ⊓ T d v`), so iterates are antitone with *no* assumption
  on `T` beyond monotonicity (`OrderHom`).
* Discreteness replaces topology: no ω-cpo, no pseudoperiod machinery.  An antitone
  sequence with finite range is eventually constant (`exists_eventuallyConstant_of_antitone`);
  `Fintype V` promotes per-component stabilization to a uniform index
  (`iterate_eventuallyConstant`).
* The honest abstract conclusion is **greatest post-fixed point of `T` below `d₀`**,
  not "least fixed point of T below start": `x ≤ d₀ ∧ x ≤ T x` admits degenerate elements
  (constant 0 with nonneg weights), so "least" is false in general.  When `T d₀ ≤ d₀`,
  greatest-post-fixed below `d₀` = lfp of `T` in `↓d₀`; that identification belongs to
  pillar (ii).  Cf. Daggitt, arXiv:2012.01686 (cite-only, unlicensed).
-/

namespace RelaxLFP

universe u v

variable {V : Type u} {α : Type v} [Lattice α] [DecidableEq V]

/-! ## Capped point update and its iterates -/

/-- Capped point update: component `v` of `d` descends to `d v ⊓ T d v`; every other
component is left unchanged.  The cap makes the update antitone unconditionally. -/
def capUpdate (T : (V → α) →o (V → α)) (v : V) (d : V → α) : V → α :=
  fun w => if w = v then d v ⊓ T d v else d w

lemma capUpdate_self (T : (V → α) →o (V → α)) (v : V) (d : V → α) :
    capUpdate T v d v = d v ⊓ T d v := by
  rw [capUpdate]
  split
  next _ => rfl
  next h => simp at h

lemma capUpdate_of_ne {w v : V} (T : (V → α) →o (V → α)) (d : V → α) (h : w ≠ v) :
    capUpdate T v d w = d w := by
  rw [capUpdate]
  split
  next h' => exact absurd h' h
  next _ => rfl

lemma capUpdate_le (T : (V → α) →o (V → α)) (v : V) (d : V → α) : capUpdate T v d ≤ d := by
  intro w
  by_cases h : w = v
  · subst h
    rw [capUpdate_self]
    exact inf_le_left
  · rw [capUpdate_of_ne T d h]

/-- Iterates of capped relaxation from `d₀`, driven by the schedule `seq : ℕ → V`. -/
def iterate (T : (V → α) →o (V → α)) (seq : ℕ → V) (d₀ : V → α) : ℕ → (V → α)
  | 0 => d₀
  | n + 1 => capUpdate T (seq n) (iterate T seq d₀ n)

lemma iterate_succ (T : (V → α) →o (V → α)) (seq : ℕ → V) (d₀ : V → α) (n : ℕ) :
    iterate T seq d₀ (n + 1) = capUpdate T (seq n) (iterate T seq d₀ n) := rfl

lemma iterate_succ_le (T : (V → α) →o (V → α)) (seq : ℕ → V) (d₀ : V → α) (n : ℕ) :
    iterate T seq d₀ (n + 1) ≤ iterate T seq d₀ n :=
  capUpdate_le _ _ _

lemma iterate_le_of_le (T : (V → α) →o (V → α)) (seq : ℕ → V) (d₀ : V → α) (n k : ℕ) :
    iterate T seq d₀ (n + k) ≤ iterate T seq d₀ n := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      calc iterate T seq d₀ (n + (k + 1)) ≤ iterate T seq d₀ (n + k) :=
            iterate_succ_le T seq d₀ (n + k)
        _ ≤ iterate T seq d₀ n := ih

lemma iterate_antitone (T : (V → α) →o (V → α)) (seq : ℕ → V) (d₀ : V → α) :
    Antitone (iterate T seq d₀) := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.le.dest hmn
  exact iterate_le_of_le T seq d₀ m k

/-! ## The convergence theorem (abstract core) -/

/-- Any post-fixed point of `T` below the start stays below every iterate.  This is the
invariant that makes the eventual limit the *greatest* post-fixed point below `d₀`. -/
theorem le_iterate {T : (V → α) →o (V → α)} {seq : ℕ → V} {d₀ x : V → α}
    (hx₀ : x ≤ d₀) (hxT : x ≤ T x) (n : ℕ) : x ≤ iterate T seq d₀ n := by
  induction n with
  | zero => exact hx₀
  | succ n ih =>
      intro w
      rw [iterate_succ]
      by_cases h : w = seq n
      · subst h
        rw [capUpdate_self]
        exact le_inf (ih _) ((hxT _).trans (T.monotone' ih _))
      · rw [capUpdate_of_ne T _ h]
        exact ih w

/-- **Pillar (i), abstract core.**  If the capped iterates eventually stabilize at
index `N` and the schedule is fair (`∀ v M, ∃ n ≥ M, seq n = v`, i.e. `Frequently
(fun n => seq n = v) atTop`), then the stabilized vector `c = iterate … N` is a
post-fixed point of `T`, lies below `d₀`, and dominates every post-fixed point of `T`
below `d₀` (i.e. `c` is the *greatest* post-fixed point below `d₀`). -/
theorem converge_of_stable (T : (V → α) →o (V → α)) (seq : ℕ → V) (d₀ : V → α)
    (N : ℕ) (hStable : ∀ n, N ≤ n → iterate T seq d₀ n = iterate T seq d₀ N)
    (hFair : ∀ (v : V) (M : ℕ), ∃ n, M ≤ n ∧ seq n = v) :
    (∀ v, iterate T seq d₀ N v ≤ T (iterate T seq d₀ N) v)
      ∧ iterate T seq d₀ N ≤ d₀
      ∧ ∀ x : V → α, x ≤ d₀ → x ≤ T x → x ≤ iterate T seq d₀ N := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    obtain ⟨n, hnN, hnseq⟩ := hFair v N
    have hn : iterate T seq d₀ n = iterate T seq d₀ N := hStable n hnN
    have hnsucc : iterate T seq d₀ (n + 1) = iterate T seq d₀ N :=
      hStable (n + 1) (by omega)
    have hupd : capUpdate T v (iterate T seq d₀ N) = iterate T seq d₀ N := by
      rw [iterate_succ, hnseq, hn] at hnsucc
      exact hnsucc
    have hcapv : capUpdate T v (iterate T seq d₀ N) v = iterate T seq d₀ N v := by
      rw [hupd]
    rw [capUpdate_self] at hcapv
    rw [← hcapv]
    exact inf_le_right
  · exact iterate_antitone T seq d₀ (Nat.zero_le N)
  · intro x hx₀ hxT
    exact le_iterate hx₀ hxT N

/-! ## Discreteness: antitone + finite range ⇒ eventually constant -/

section FiniteRange

variable {β : Type v} [PartialOrder β]

/-- An antitone sequence taking only finitely many values is eventually constant.
The strict-drop indices inject into the (finite) range, hence are finitely many;
after the last drop the sequence is constant. -/
theorem exists_eventuallyConstant_of_antitone (f : ℕ → β) (hanti : Antitone f)
    (hrange : (Set.range f).Finite) : ∃ N, ∀ n, N ≤ n → f n = f N := by
  classical
  set D : Set ℕ := {n | f (n + 1) ≠ f n} with hD
  have hinj : Set.InjOn f D := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hab' | hab' | hab'
    · have h1 : f (a + 1) ≤ f a := hanti (Nat.le_succ a)
      have h2 : f b ≤ f (a + 1) := hanti (by omega)
      rw [← hab] at h2
      exact absurd (le_antisymm h1 h2) ha
    · exact hab'
    · have h1 : f (b + 1) ≤ f b := hanti (Nat.le_succ b)
      have h2 : f a ≤ f (b + 1) := hanti (by omega)
      rw [hab] at h2
      exact absurd (le_antisymm h1 h2) hb
  have hDfin : D.Finite := Set.Finite.of_injOn (fun n _ => Set.mem_range_self n) hinj hrange
  obtain ⟨M, hM⟩ : ∃ M, ∀ n ∈ D, n ≤ M :=
    ⟨hDfin.toFinset.sup id, fun n hn => Finset.le_sup (f := id) (hDfin.mem_toFinset.mpr hn)⟩
  have htel : ∀ k, f (M + 1 + k) = f (M + 1) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        have hstep : f (M + 1 + k + 1) = f (M + 1 + k) := by
          by_contra hne
          have hmem : M + 1 + k ∈ D := hne
          have := hM (M + 1 + k) hmem
          omega
        rw [Nat.add_succ, hstep, ih]
  refine ⟨M + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  exact htel k

end FiniteRange

/-- Eventual constancy of the whole iterate vector, from per-component finite ranges
plus `Fintype V`.  This is where the "finite value universe" discreteness enters. -/
theorem iterate_eventuallyConstant {V : Type u} {α : Type v} [Lattice α] [DecidableEq V]
    [Fintype V] (T : (V → α) →o (V → α)) (seq : ℕ → V) (d₀ : V → α)
    (hrange : ∀ v, (Set.range fun n => iterate T seq d₀ n v).Finite) :
    ∃ N, ∀ n, N ≤ n → iterate T seq d₀ n = iterate T seq d₀ N := by
  classical
  choose Nv hNv using fun v =>
    exists_eventuallyConstant_of_antitone (fun n => iterate T seq d₀ n v)
      (fun a b hab => iterate_antitone T seq d₀ hab v) (hrange v)
  refine ⟨Finset.sup Finset.univ Nv, fun n hn => ?_⟩
  funext v
  have h1 : iterate T seq d₀ n v = iterate T seq d₀ (Nv v) v :=
    hNv v n ((Finset.le_sup (Finset.mem_univ v)).trans hn)
  have h2 : iterate T seq d₀ (Finset.sup Finset.univ Nv) v = iterate T seq d₀ (Nv v) v :=
    hNv v _ (Finset.le_sup (Finset.mem_univ v))
  rw [h1, h2]

/-- **Pillar (i), finite setting.**  A fair schedule of capped relaxations whose
per-component value range is finite converges, and its limit `c` is the greatest
post-fixed point of `T` below `d₀`.  For SSSP instances (`T_BF`, `⊤`-start), the range
finiteness comes from the finite value universe of simple-path sums (pillar-(ii) seam). -/
theorem fair_iteration_complete {V : Type u} {α : Type v} [Lattice α] [DecidableEq V]
    [Fintype V] (T : (V → α) →o (V → α)) (seq : ℕ → V) (d₀ : V → α)
    (hFair : ∀ (v : V) (M : ℕ), ∃ n, M ≤ n ∧ seq n = v)
    (hrange : ∀ v, (Set.range fun n => iterate T seq d₀ n v).Finite) :
    ∃ N c, ((∀ v, c v ≤ T c v) ∧ c ≤ d₀ ∧ ∀ x : V → α, x ≤ d₀ → x ≤ T x → x ≤ c)
      ∧ ∀ n, N ≤ n → iterate T seq d₀ n = c := by
  obtain ⟨N, hStable⟩ := iterate_eventuallyConstant T seq d₀ hrange
  exact ⟨N, iterate T seq d₀ N, converge_of_stable T seq d₀ N hStable hFair, hStable⟩

/-! ## The limit is the infimum of the iterates (complete-lattice refinement) -/

section CompleteLattice

variable {α : Type v} [CompleteLattice α]

/-- With stability at `N`, the eventual value is literally the infimum of the iterate
sequence — order-theoretic convergence, no topology needed. -/
theorem iInf_eq_of_stable (T : (V → α) →o (V → α)) (seq : ℕ → V) (d₀ : V → α) (N : ℕ)
    (hStable : ∀ n, N ≤ n → iterate T seq d₀ n = iterate T seq d₀ N) :
    ⨅ n, iterate T seq d₀ n = iterate T seq d₀ N := by
  refine le_antisymm ?_ (le_iInf fun n => ?_)
  · exact iInf_le _ N
  · rcases Nat.lt_or_ge n N with h | h
    · exact iterate_antitone T seq d₀ (le_of_lt h)
    · exact (hStable n h).symm.le

end CompleteLattice

/-! ## SSSP instance: the Bellman–Ford proposal operator -/

section Instance

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem T_BF_mono (w : V → V → ℝ≥0∞) (s : V) :
    Monotone (fun (d : V → ℝ≥0∞) (v : V) => if v = s then 0 else ⨅ u : V, d u + w u v) := by
  intro a b hab v
  by_cases h : v = s
  · subst h
    simp
  · simp only [ite_eq_right h]
    exact iInf_mono fun u => add_le_add_left (hab u) (w u v)

/-- Bellman–Ford proposal operator on `ℝ≥0∞`: pin the source at `0`, elsewhere propose
the infimum over in-edges of `d u + w u v`.  `T_BF` is monotone; the *capped* update
`d v ⊓ T_BF d v` is the usual relaxation step. -/
noncomputable def T_BF (w : V → V → ℝ≥0∞) (s : V) : (V → ℝ≥0∞) →o (V → ℝ≥0∞) :=
  ⟨fun d v => if v = s then 0 else ⨅ u : V, d u + w u v, T_BF_mono w s⟩

@[simp]
lemma T_BF_apply (w : V → V → ℝ≥0∞) (s : V) (d : V → ℝ≥0∞) (v : V) :
    T_BF w s d v = if v = s then 0 else ⨅ u : V, d u + w u v := rfl

/-- Standard SSSP start vector: `0` at the source, `⊤` elsewhere. -/
def dInit (s : V) : V → ℝ≥0∞ := fun v => if v = s then 0 else ⊤

/-- PILLAR-(ii) SEAM — named `sorry_pillar2_value_universe`, deliberately open tonight.
Every value ever held by component `v` while iterating capped `T_BF w s` from `dInit s`
is `⊤` or the `ℝ≥0∞`-sum of weights along a *simple* path from `s` to `v`.  A `Fintype`
graph has finitely many simple paths, so each component's range is finite — exactly the
discreteness hypothesis `fair_iteration_complete` needs.  Proof strategy (pillar ii):
induction over the update history with a "new value ⇒ new simple path" witness. -/
theorem iterate_range_finite (w : V → V → ℝ≥0∞) (s : V) (seq : ℕ → V) :
    ∀ v, (Set.range fun n => iterate (T_BF w s) seq (dInit s) n v).Finite := by
  sorry -- sorry_pillar2_value_universe

end Instance

end RelaxLFP

/-! ## Status ledger (honest)

Proved tonight: `capUpdate`/`iterate` basics; antitonicity (`iterate_antitone`);
invariant `le_iterate`; abstract convergence `converge_of_stable`; discreteness lemma
`exists_eventuallyConstant_of_antitone`; uniform stabilization `iterate_eventuallyConstant`;
combined `fair_iteration_complete`; `iInf_eq_of_stable`; `T_BF` definition + monotonicity.

Open (named): `sorry_pillar2_value_universe` (simple-path value universe; pillar ii).

Next step for pillar (i): close `sorry_pillar2_value_universe` OR — cleaner — prove the
pillar-(i)+(ii) bridge: with `T d₀ ≤ d₀` and finite chains, greatest-post-fixed-below-`d₀`
= least fixed point of `T` in `↓d₀` (Knaster–Tarski flavor, ascending side).
-/
