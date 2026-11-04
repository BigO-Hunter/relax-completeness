/-
Copyright (c) 2026. Capped-relaxation SSSP completeness (pillar i).
-/
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Lemmas
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

/-! ## Walks over the complete hop graph (pillar-(ii) value universe) -/

section Walks

/-- A walk from `s` to `v`, grown one hop at a time. Hops are unrestricted: a hop of
`⊤`-weight simply contributes `⊤` to the cost. -/
inductive Walk (s : V) : V → Type u where
  | nil : Walk s s
  | step (a b : V) (p : Walk s a) : Walk s b

namespace Walk

variable {w : V → V → ℝ≥0∞} {s v : V}

/-- Total weight of a walk: sum of `w` along its hops (`nil` costs `0`). -/
def cost (w : V → V → ℝ≥0∞) {s v : V} : Walk s v → ℝ≥0∞
  | nil => 0
  | step a b p => cost w p + w a b

/-- Vertices visited by a walk, in order. -/
def verts {s v : V} : Walk s v → List V
  | nil => [s]
  | step _ b p => verts p ++ [b]

/-- Hop count. -/
def length {s v : V} : Walk s v → ℕ
  | nil => 0
  | step _ _ p => p.length + 1

/-- A walk is *simple* when it visits no vertex twice. -/
def IsSimple {s v : V} (p : Walk s v) : Prop := (verts p).Nodup

@[simp] lemma cost_nil (w : V → V → ℝ≥0∞) (s : V) :
    (Walk.nil : Walk s s).cost w = 0 := rfl

@[simp] lemma cost_step (w : V → V → ℝ≥0∞) (a : V) (p : Walk s a) (b : V) :
    (Walk.step a b p).cost w = p.cost w + w a b := rfl

@[simp] lemma verts_nil (s : V) : (Walk.nil : Walk s s).verts = [s] := rfl

@[simp] lemma verts_step (a : V) (p : Walk s a) (b : V) :
    (Walk.step a b p).verts = p.verts ++ [b] := rfl

@[simp] lemma length_step (a : V) (p : Walk s a) (b : V) :
    (Walk.step a b p).length = p.length + 1 := rfl

lemma verts_length {s v : V} (p : Walk s v) : (verts p).length = p.length + 1 := by
  induction p with
  | nil => rfl
  | step a b q ih => simp [verts_step, ih]

lemma nodup_of_isSimple_step {a : V} {p : Walk s a} {b : V}
    (h : (Walk.step a b p).IsSimple) : p.IsSimple ∧ b ∉ p.verts := by
  rw [Walk.IsSimple, verts_step, List.nodup_append] at h
  exact ⟨h.1, fun hv => h.2.2 b hv b (List.mem_singleton.mpr rfl) rfl⟩

/-- Extending a simple walk by a fresh vertex keeps it simple. -/
lemma isSimple_step {a : V} {p : Walk s a} {b : V}
    (hp : p.IsSimple) (hb : b ∉ p.verts) : (Walk.step a b p).IsSimple := by
  rw [IsSimple, verts_step, List.nodup_append]
  refine ⟨hp, List.nodup_singleton b, fun x hx y hy hxy => hb ?_⟩
  have hyb : y = b := List.mem_singleton.mp hy
  rw [hxy, hyb] at hx
  exact hx

/-- A walk with endpoint provably distinct from the source is a final hop onto a
shorter walk.  (Stated with `b` a free variable so that `cases` can unify indices;
callers instantiate `b` with an arbitrary term.) -/
theorem exists_step_of_endpoint_ne {b : V} (q : Walk s b) (hb : ¬(b = s)) :
    ∃ a : V, ∃ r : Walk s a, q = Walk.step a b r := by
  cases q with
  | nil => exact absurd rfl hb
  | step a b' r => exact ⟨a, r, rfl⟩

/-- `Tight w d p`: every prefix `q` of `p` (including `p` itself) satisfies
`d (endpoint q) ≤ cost w q` — the vector `d` already certifies all of `p`'s prefixes.
Structural conjunct chain, so prefix-tightness is just projection along `IsPrefix`. -/
def Tight (w : V → V → ℝ≥0∞) {s v : V} (d : V → ℝ≥0∞) : Walk s v → Prop
  | nil => d s ≤ 0
  | step a b p => Tight w d p ∧ d b ≤ cost w p + w a b

theorem Tight.end_bound {d : V → ℝ≥0∞} {p : Walk s v} (h : Tight w d p) :
    d v ≤ cost w p := by
  induction p with
  | nil => exact h
  | step a b q ih => exact h.2

theorem Tight.mono {d d' : V → ℝ≥0∞} (hdd : ∀ u, d' u ≤ d u) {p : Walk s v}
    (h : Tight w d p) : Tight w d' p := by
  induction p with
  | nil => exact (hdd s).trans h
  | step a b q ih => exact ⟨ih h.1, (hdd b).trans h.2⟩

/-- `IsPrefix q p`: `q` is `p` truncated at some vertex it visits (possibly all of `p`). -/
inductive IsPrefix : ∀ {e e' : V}, Walk s e → Walk s e' → Prop where
  | refl {e : V} (p : Walk s e) : IsPrefix p p
  | cons {e e' b : V} {q : Walk s e} {p : Walk s e'} (h : IsPrefix q p) :
      IsPrefix q (Walk.step e' b p)

namespace IsPrefix

theorem trans {e e' e'' : V} {q : Walk s e} {p : Walk s e'} {t : Walk s e''}
    (h2 : IsPrefix p t) : IsPrefix q p → IsPrefix q t := by
  induction h2 with
  | refl => exact fun h => h
  | cons h2' ih => exact fun h => IsPrefix.cons (ih h)

theorem cost_le {e e' : V} {q : Walk s e} {p : Walk s e'} (h : IsPrefix q p) :
    Walk.cost w q ≤ Walk.cost w p := by
  induction h with
  | refl => exact le_rfl
  | cons h' ih => exact ih.trans le_self_add

theorem simple {e e' : V} {q : Walk s e} {p : Walk s e'} (h : IsPrefix q p)
    (hs : p.IsSimple) : q.IsSimple := by
  induction h with
  | refl => exact hs
  | cons h' ih =>
      rw [Walk.IsSimple, Walk.verts_step, List.nodup_append] at hs
      exact ih hs.1

theorem tight {e e' : V} {q : Walk s e} {p : Walk s e'} (h : IsPrefix q p)
    {d : V → ℝ≥0∞} (ht : Walk.Tight w d p) : Walk.Tight w d q := by
  induction h with
  | refl => exact ht
  | cons h' ih => exact ih ht.1

theorem exists_of_mem_verts : ∀ {e : V} (p : Walk s e) (x : V),
    x ∈ Walk.verts p → ∃ q : Walk s x, IsPrefix q p := by
  intro e p
  induction p with
  | nil =>
      intro x hx
      rw [Walk.verts_nil, List.mem_singleton] at hx
      subst x
      exact ⟨Walk.nil, IsPrefix.refl _⟩
  | step a b p' ih =>
      intro x hx
      rw [Walk.verts_step, List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨q, hq⟩ := ih x hx
        exact ⟨q, IsPrefix.cons hq⟩
      · rw [List.mem_singleton] at hx
        subst x
        exact ⟨Walk.step a b p', IsPrefix.refl _⟩

end IsPrefix

end Walk

end Walks

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

theorem T_BF_apply_of_ne {w : V → V → ℝ≥0∞} {s : V} {d : V → ℝ≥0∞} {v : V} (h : v ≠ s) :
    T_BF w s d v = ⨅ u, d u + w u v := by
  rw [T_BF_apply, ite_eq_right h]

theorem T_BF_le_edge {w : V → V → ℝ≥0∞} {s : V} {d : V → ℝ≥0∞} {v : V} (h : v ≠ s) (u : V) :
    T_BF w s d v ≤ d u + w u v := by
  rw [T_BF_apply_of_ne h]
  exact iInf_le _ u

/-- Over a `Fintype`, an `ℝ≥0∞`-valued infimum is attained: the inf of finitely many
values is one of them.  Via `Set.exists_min_image` on `univ` — the direct `Finset.inf'`
fold induction runs into the `Finset.induction_on` disjointness gate and dependent-proof
rewrite motives; this pin has no `Set.Finite.exists_eq_iInf`/`Finset.min'`. -/
theorem iInf_attained [Nonempty V] (f : V → ℝ≥0∞) : ∃ u₀, ⨅ u, f u = f u₀ := by
  obtain ⟨u₀, -, hu₀⟩ :=
    Set.exists_min_image (Set.univ : Set V) f Set.finite_univ Set.univ_nonempty
  refine ⟨u₀, le_antisymm (iInf_le f u₀) (le_iInf fun u => hu₀ u (Set.mem_univ u))⟩

/-- Walks of bounded hop count from a fixed source to a fixed endpoint are finite:
peel the last hop, finite union over the (finitely many) penultimate vertices. -/
theorem Walk.finite_length_le (s v : V) (k : ℕ) :
    Set.Finite {p : Walk s v | p.length ≤ k} := by
  induction k generalizing s v with
  | zero =>
      by_cases hvs : v = s
      · subst v
        refine Set.Finite.subset (Set.finite_singleton (Walk.nil : Walk s s)) ?_
        intro p hp
        cases p with
        | nil => exact Set.mem_singleton _
        | step a b q => simp [Walk.length] at hp
      · refine Set.Finite.subset Set.finite_empty ?_
        intro p hp
        cases p with
        | nil => exact (hvs rfl).elim
        | step a b q => simp [Walk.length] at hp
  | succ k ih =>
      by_cases hvs : v = s
      · subst v
        have h1 : Set.Finite ({Walk.nil} : Set (Walk s s)) := Set.finite_singleton _
        have h2 : Set.Finite (⋃ a : V, (Walk.step a s) '' {q : Walk s a | q.length ≤ k}) :=
          Set.finite_iUnion fun a : V => Set.Finite.image (Walk.step a s) (ih s a)
        refine Set.Finite.subset (h1.union h2) ?_
        intro p hp
        cases p with
        | nil => exact Or.inl (Set.mem_singleton _)
        | step a b q =>
            exact Or.inr (Set.mem_iUnion_of_mem a (Set.mem_image_of_mem (Walk.step a s)
              (by simp [Walk.length] at hp; show q.length ≤ k; omega)))
      · have h2 : Set.Finite (⋃ a : V, (Walk.step a v) '' {q : Walk s a | q.length ≤ k}) :=
          Set.finite_iUnion fun a : V => Set.Finite.image (Walk.step a v) (ih s a)
        refine Set.Finite.subset h2 ?_
        intro p hp
        cases p with
        | nil => exact (hvs rfl).elim
        | step a b q =>
            exact Set.mem_iUnion_of_mem a (Set.mem_image_of_mem (Walk.step a v)
              (by simp [Walk.length] at hp; show q.length ≤ k; omega))

/-- Simple walks between two fixed vertices are finite: a simple walk has at most
`Fintype.card V` hops (its vertex list is nodup, hence length-bounded). -/
theorem Walk.finite_simple (s v : V) :
    Set.Finite {p : Walk s v | p.IsSimple} :=
  Set.Finite.subset (Walk.finite_length_le s v (Fintype.card V)) fun p hp => by
    have h1 : (Walk.verts p).length = p.length + 1 := Walk.verts_length p
    have h2 : (Walk.verts p).length ≤ Fintype.card V := List.Nodup.length_le_card hp
    show p.length ≤ Fintype.card V
    omega

/-- **Pillar (ii) value-universe theorem** — closes the seam `fair_iteration_complete`
needs.  Every value component `v` ever holds while iterating capped `T_BF w s` from
`dInit s` is `⊤` or the cost of a *simple* walk `s → v`, witnessed with a **tightness**
side-condition: the current iterate already lies at or below the cost of every prefix
of the witness.  Tightness is the inductive fuel for the hard case — when the proposal
`⨅ u, d u + w u v` attains at a `u₀` whose witness walk `p₀` passes *through* `v`
(non-simple at storage time): the prefix `q` of `p₀` ending at `v` satisfies
`q ≤ p₀ ≤ proposal = q` (proposal ≤ `q` because `q`'s own penultimate vertex is
prefix-tight), forcing the stored value to equal `cost q` — a simple-walk cost after
all.  This is the "new value ⇒ new simple path" induction promised in the seam. -/
theorem iterate_value_universe (w : V → V → ℝ≥0∞) (s : V) (seq : ℕ → V) :
    ∀ (n : ℕ) (v : V),
      iterate (T_BF w s) seq (dInit s) n v = ⊤ ∨
      ∃ p : Walk s v, p.IsSimple ∧ Walk.cost w p = iterate (T_BF w s) seq (dInit s) n v ∧
        Walk.Tight w (iterate (T_BF w s) seq (dInit s) n) p := by
  intro n
  induction n with
  | zero =>
      intro v
      by_cases hvs : v = s
      · subst v
        right
        refine ⟨Walk.nil, List.nodup_singleton s, ?_, ?_⟩
        · simp [iterate, dInit]
        · simp [iterate, dInit, Walk.Tight]
      · left
        simp [iterate, dInit, hvs]
  | succ n ih =>
      intro v
      by_cases hupd : v = seq n
      · subst hupd
        have hsucc : iterate (T_BF w s) seq (dInit s) (n + 1) (seq n)
            = iterate (T_BF w s) seq (dInit s) n (seq n)
              ⊓ T_BF w s (iterate (T_BF w s) seq (dInit s) n) (seq n) := by
          rw [iterate_succ, capUpdate_self]
        rcases le_total (iterate (T_BF w s) seq (dInit s) n (seq n))
            (T_BF w s (iterate (T_BF w s) seq (dInit s) n) (seq n)) with hle | hle
        · -- the cap keeps the old value
          have hval : iterate (T_BF w s) seq (dInit s) (n + 1) (seq n)
              = iterate (T_BF w s) seq (dInit s) n (seq n) :=
            hsucc.trans (le_antisymm inf_le_left (le_inf le_rfl hle))
          rcases ih (seq n) with htop | ⟨p, hps, hcost, htight⟩
          · left; exact hval.trans htop
          · right
            refine ⟨p, hps, hcost.trans hval.symm, Walk.Tight.mono ?_ htight⟩
            exact fun u => iterate_succ_le (T_BF w s) seq (dInit s) n u
        · -- the cap takes the proposal
          have hval : iterate (T_BF w s) seq (dInit s) (n + 1) (seq n)
              = T_BF w s (iterate (T_BF w s) seq (dInit s) n) (seq n) :=
            hsucc.trans (le_antisymm inf_le_right (le_inf hle le_rfl))
          by_cases hsv : seq n = s
          · -- updated vertex is the source: proposal is `0` = cost of `nil`
            subst hsv
            right
            refine ⟨Walk.nil, List.nodup_singleton _, ?_, ?_⟩
            · simp [hval]
            · simp [hval, Walk.Tight]
          · have hprop : T_BF w s (iterate (T_BF w s) seq (dInit s) n) (seq n)
                = ⨅ u, iterate (T_BF w s) seq (dInit s) n u + w u (seq n) :=
              T_BF_apply_of_ne hsv
            by_cases htop : ⨅ u, iterate (T_BF w s) seq (dInit s) n u + w u (seq n) = ⊤
            · left; exact (hval.trans hprop).trans htop
            · right
              haveI : Nonempty V := ⟨s⟩
              obtain ⟨u₀, hu₀⟩ := iInf_attained
                (fun u => iterate (T_BF w s) seq (dInit s) n u + w u (seq n))
              have hu₀' : ⨅ u, iterate (T_BF w s) seq (dInit s) n u + w u (seq n)
                  = iterate (T_BF w s) seq (dInit s) n u₀ + w u₀ (seq n) := hu₀
              rcases ih u₀ with htop₀ | ⟨p₀, hp₀s, hp₀cost, hp₀tight⟩
              · exfalso; exact htop (by rw [hu₀', htop₀]; simp)
              · by_cases hmem : seq n ∈ Walk.verts p₀
                · -- proposal routes THROUGH `seq n`: the prefix squeeze
                  obtain ⟨q, hq⟩ := Walk.IsPrefix.exists_of_mem_verts p₀ (seq n) hmem
                  obtain ⟨a', r, hqeq⟩ := Walk.exists_step_of_endpoint_ne q hsv
                  have hrq : Walk.IsPrefix r q := by
                    rw [hqeq]
                    exact Walk.IsPrefix.cons (Walk.IsPrefix.refl r)
                  have htr : Walk.Tight w (iterate (T_BF w s) seq (dInit s) n) r :=
                    Walk.IsPrefix.tight (Walk.IsPrefix.trans hq hrq) hp₀tight
                  have hdle : iterate (T_BF w s) seq (dInit s) n a' ≤ Walk.cost w r :=
                    Walk.Tight.end_bound htr
                  have hleq : ⨅ u, iterate (T_BF w s) seq (dInit s) n u + w u (seq n)
                      ≤ Walk.cost w q := by
                    rw [hqeq]
                    calc ⨅ u, iterate (T_BF w s) seq (dInit s) n u + w u (seq n)
                        ≤ iterate (T_BF w s) seq (dInit s) n a' + w a' (seq n) :=
                          iInf_le _ a'
                      _ ≤ Walk.cost w r + w a' (seq n) :=
                          add_le_add_left hdle (w a' (seq n))
                      _ = Walk.cost w (Walk.step a' (seq n) r) :=
                          (Walk.cost_step w a' r (seq n)).symm
                  have hqlep₀ : Walk.cost w q ≤ Walk.cost w p₀ := Walk.IsPrefix.cost_le hq
                  have hp₀le : Walk.cost w p₀
                      ≤ ⨅ u, iterate (T_BF w s) seq (dInit s) n u + w u (seq n) := by
                    rw [hu₀', ← hp₀cost]
                    exact le_self_add
                  have hchain : iterate (T_BF w s) seq (dInit s) (n + 1) (seq n)
                      = ⨅ u, iterate (T_BF w s) seq (dInit s) n u + w u (seq n) :=
                    hval.trans hprop
                  refine ⟨q, Walk.IsPrefix.simple hq hp₀s, ?_, ?_⟩
                  · exact le_antisymm
                      ((hqlep₀.trans hp₀le).trans_eq hchain.symm)
                      (hchain.le.trans hleq)
                  · exact Walk.Tight.mono
                      (fun u => iterate_succ_le (T_BF w s) seq (dInit s) n u)
                      (Walk.IsPrefix.tight hq hp₀tight)
                · -- `seq n` is fresh for `p₀`: extend by one hop
                  refine ⟨Walk.step u₀ (seq n) p₀, Walk.isSimple_step hp₀s hmem, ?_, ?_⟩
                  · rw [Walk.cost_step, hval, hprop, hu₀', hp₀cost]
                  · refine ⟨Walk.Tight.mono
                        (fun u => iterate_succ_le (T_BF w s) seq (dInit s) n u)
                        hp₀tight, ?_⟩
                    rw [hval, hprop, hu₀', ← hp₀cost]
      · -- vertex not updated this step
        have hne : iterate (T_BF w s) seq (dInit s) (n + 1) v
              = iterate (T_BF w s) seq (dInit s) n v := by
          rw [iterate_succ, capUpdate_of_ne (T_BF w s) _ hupd]
        rcases ih v with htop | ⟨p, hps, hcost, htight⟩
        · left; exact hne.trans htop
        · right
          refine ⟨p, hps, hcost.trans hne.symm,
            Walk.Tight.mono (fun u => iterate_succ_le (T_BF w s) seq (dInit s) n u) htight⟩

/-- **Seam CLOSED** (was the named sorry `sorry_pillar2_value_universe`).  Every value
component `v` ever holds is `⊤` or a simple-walk cost (`iterate_value_universe`);
simple walks `s → v` are finitely many (`Walk.finite_simple`), so each component's
iterate range is finite — exactly the discreteness hypothesis
`fair_iteration_complete` needs. -/
theorem iterate_range_finite (w : V → V → ℝ≥0∞) (s : V) (seq : ℕ → V) :
    ∀ v, (Set.range fun n => iterate (T_BF w s) seq (dInit s) n v).Finite := by
  intro v
  have huniv : Set.range (fun n => iterate (T_BF w s) seq (dInit s) n v) ⊆
      insert ⊤ (Walk.cost w '' {p : Walk s v | p.IsSimple}) := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    dsimp only
    rcases iterate_value_universe w s seq n v with htop | ⟨p, hps, hcost, -⟩
    · rw [htop]; exact Set.mem_insert _ _
    · rw [← hcost]
      exact Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ hps)
  exact Set.Finite.subset
    ((Set.finite_singleton ⊤).union
      (Set.Finite.image (Walk.cost w) (Walk.finite_simple s v)))
    huniv

end Instance

end RelaxLFP

/-! ## Status ledger (honest)

Pillar (i) — proved: `capUpdate`/`iterate` basics; antitonicity (`iterate_antitone`);
invariant `le_iterate`; abstract convergence `converge_of_stable`; discreteness lemma
`exists_eventuallyConstant_of_antitone`; uniform stabilization `iterate_eventuallyConstant`;
combined `fair_iteration_complete`; `iInf_eq_of_stable`; `T_BF` definition + monotonicity.

Pillar (ii) — proved, NO remaining sorries: the walk machinery (`Walk`, `cost`, `verts`,
`IsSimple`, `length`); the prefix order (`IsPrefix` with `trans`/`cost_le`/`simple`/`tight`/
`exists_of_mem_verts`); the prefix-tightness invariant (`Tight` with `end_bound`/`mono`);
`ℝ≥0∞` infimum attainment over `Fintype` (`iInf_attained` via `Set.exists_min_image`);
finiteness of length-bounded and simple walks (`Walk.finite_length_le`,
`Walk.finite_simple`); the value-universe theorem `iterate_value_universe`; and the
**seam closed**: `iterate_range_finite`. In `Pillar2.lean`: `T_BF_le_dInit`,
`fixed_of_greatest_postFixed`, `distV_le_T_BF`, `distV_le_dInit`, `le_cost_of_le_T_BF`,
`le_distV_of_le_T_BF`, and the headline `canonical_point_eq_distV` — the fair-iteration
limit IS the true shortest-distance vector.

Next: pillar (iii) — box certification / frozen-lock (Zhao fast-sweeping).
-/
