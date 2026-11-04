/-
Copyright (c) 2026. Capped-relaxation SSSP completeness (pillar iii).
-/
import Pillar2

open ENNReal

namespace RelaxLFP

universe u v

set_option linter.unusedSectionVars false

/-!
# Pillar (iii): box certification — settled under a certified boundary ⇒ final

The first-of-class theorem for this line of work: **settlement under a certified
boundary implies finality** — no verified Dijkstra in existence treats
re-expansion/certified settling, and this file gives the synchronous core of it.

## Model (minimal synchronous engine)

A state is `(d, U, B)`: estimates `d : V → ℝ≥0∞`, settled set `U : Finset V`,
boundary `B : ℝ≥0∞`.  Two legal transitions (`LegalStep`):

* **relax** at `u ∈ U`: fire the push-relaxation of `u`'s out-edges
  (`pushUpdate`: `d' x = d x ⊓ (d u + w u x)` for every `x`); `U`, `B` unchanged.
* **settle** at `v ∉ U`: the settle **rule** `d v ≤ B` certifies `v` inside the
  box, and the **box condition** `B ≤ ⨅ (u ∉ insert v U), d u` — the
  beyond-dijkstra invariant `dB[D] ≥ B′` — keeps every vertex that *remains*
  unsettled at or above the boundary.  The step atomically fires the
  push-relaxation at `v` (the synchronous Dijkstra/FMM semantics: "settlement of
  `u` fires the out-edge updates `T_u`") and the next boundary is unconstrained
  (per-event data in the async refinement).

Two deliberate modelling decisions, both forced (see `DESIGN.md`, pillar (iii)):

1. **Settle fires the relaxation at `v` atomically.**  A settle-without-relaxation
   engine is FALSE for the certification theorem: on `s →(1) a →(1) v` with
   `s →(5) v`, settle `s` (B=1), relax at `s` (`d a = 1`, `d v = 5`), settle `a`
   with `B = 5` (rule `1 ≤ 5` ✓, box `5 ≤ d v = 5` ✓), then settle `v` with the
   stale `d v = 5 ≤ B = 5` (box over the empty frontier ✓) — while `distV v = 2`.
   The synchronous engine closes the loophole by construction.
2. **The box ranges over the post-settle unsettled set** (`u ∉ insert v U`), the
   "boundary never exceeds the *remaining* unsettled values" reading.  Ranging
   over `u ∉ U` (including `v` itself) would force `d v = B` at every settle —
   extract-min with a frozen boundary, a strictly smaller engine class.  The
   present rule set is weaker premises, hence a stronger theorem; with `B`
   existentially quantified it collapses exactly to Dijkstra extract-min
   (`∃ B, d v ≤ B ≤ ⨅ frontier d` ↔ `d v ≤ ⨅ frontier d`, and `v` is then a
   frontier minimum).

The async echo-sweep engine is the refinement: echo sweeps are re-firings of
`relax` steps, and `frozen_lock` below (Zhao's lock invariant) is exactly the
lemma that lets certified vertices skip re-expansion.

## Results

* `distV_le_d` — values overestimate truth: `distV w s ≤ d_t` at every time.
* `certified_settled_final` — THE CERTIFICATION THEOREM: `v ∈ U_t ⇒ d_t v = distV w s v`.
* `settled_edges_relaxed` — out-edges of settled vertices are always relaxed.
* `frozen_lock` — Zhao fast-sweeping lock: once settled, `d v` never changes again.
* `trivialRun_legal` — the engine is non-vacuous (and the first settle is forced
  to be the source while the boundary starts at `⊤`).
-/

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## The synchronous engine -/

/-- Push-relaxation of every out-edge of `u`: each estimate descends to its cap
by the `u`-route `d u + w u x`.  Complete-hop-graph convention: a non-edge has
weight `⊤` and the update is a no-op there (`d x ⊓ ⊤ = d x`) — no assumption on
`w` is needed. -/
def pushUpdate (w : V → V → ℝ≥0∞) (u : V) (d : V → ℝ≥0∞) : V → ℝ≥0∞ :=
  fun x => d x ⊓ (d u + w u x)

@[simp] lemma pushUpdate_apply (w : V → V → ℝ≥0∞) (u x : V) (d : V → ℝ≥0∞) :
    pushUpdate w u d x = d x ⊓ (d u + w u x) := rfl

lemma pushUpdate_le (w : V → V → ℝ≥0∞) (u : V) (d : V → ℝ≥0∞) :
    pushUpdate w u d ≤ d := fun _ => inf_le_left

/-- Pushing at `u` never changes `d u` itself: `d u ⊓ (d u + c) = d u` since
weights are nonnegative. -/
lemma pushUpdate_self (w : V → V → ℝ≥0∞) (u : V) (d : V → ℝ≥0∞) :
    pushUpdate w u d u = d u :=
  le_antisymm inf_le_left (le_inf le_rfl le_self_add)

/-- State of the minimal synchronous certification engine. -/
structure CertState (V : Type u) where
  d : V → ℝ≥0∞
  U : Finset V
  B : ℝ≥0∞

/-- One legal transition.  `relax` at a settled vertex; `settle` at an unsettled
vertex under the rule `d v ≤ B` and the box condition `B ≤ ⨅ (u ∉ insert v U), d u`
(pointwise-`⨅` form: `pre.B ≤ ⨅ u ∈ univ \ insert v pre.U, pre.d u`), firing the
push-relaxation at `v` atomically.  The new boundary is unconstrained. -/
def LegalStep (w : V → V → ℝ≥0∞) (pre post : CertState V) : Prop :=
  (∃ u ∈ pre.U, post.d = pushUpdate w u pre.d ∧ post.U = pre.U ∧ post.B = pre.B) ∨
  (∃ v, v ∉ pre.U ∧ post.d = pushUpdate w v pre.d ∧
    post.U = insert v pre.U ∧
    pre.d v ≤ pre.B ∧
    pre.B ≤ ⨅ u ∈ Finset.univ \ insert v pre.U, pre.d u)

/-- A legal run from the standard start: `d = dInit s`, nothing settled, boundary
`⊤` (which forces the first settlement to be the source: while `s` with `d s = 0`
remains unsettled, the box `⊤ ≤ ⨅ frontier dInit` fails for every other vertex). -/
structure CertifiedRun (w : V → V → ℝ≥0∞) (s : V) where
  σ : ℕ → CertState V
  init : σ 0 = { d := dInit s, U := ∅, B := ⊤ }
  legal : ∀ t, LegalStep w (σ t) (σ (t + 1))

/-! ## Distance-vector helpers -/

/-- The true distance to the source is `0`. -/
lemma distV_s (w : V → V → ℝ≥0∞) (s : V) : distV w s s = 0 :=
  le_antisymm ((iInf_le _ (Walk.nil : Walk s s)).trans_eq (Walk.cost_nil w s)) zero_le

/-- One more hop cannot beat the infimum: the triangle inequality for `distV`. -/
lemma distV_le_add (w : V → V → ℝ≥0∞) (s u x : V) :
    distV w s x ≤ distV w s u + w u x := by
  by_cases hx : x = s
  · subst x
    rw [distV_s]
    exact zero_le
  · exact (distV_le_T_BF w s x).trans (T_BF_le_edge hx u)

/-- If the infimum of walk costs to `y` is below `a`, some walk witnesses it. -/
lemma exists_walk_cost_lt {w : V → V → ℝ≥0∞} {s y : V} {a : ℝ≥0∞}
    (h : distV w s y < a) : ∃ P : Walk s y, Walk.cost w P < a := by
  by_contra hc
  have h' : ∀ P : Walk s y, a ≤ Walk.cost w P :=
    fun P => not_lt.mp (not_exists.mp hc P)
  exact lt_irrefl _ (h.trans_le (le_iInf h'))

/-! ## Run-level invariants -/

namespace CertifiedRun

variable {w : V → V → ℝ≥0∞} {s : V} (run : CertifiedRun w s)

lemma d0 : (run.σ 0).d = dInit s := by rw [run.init]

lemma U0 : (run.σ 0).U = ∅ := by rw [run.init]

/-- Every step only lowers estimates (both step kinds are push-updates). -/
lemma d_le_of_step (t : ℕ) : (run.σ (t + 1)).d ≤ (run.σ t).d := by
  rcases run.legal t with ⟨u, -, hd, -, -⟩ | ⟨v, -, hd, -, -, -⟩
  · rw [hd]; exact pushUpdate_le w u _
  · rw [hd]; exact pushUpdate_le w v _

/-- Estimates are antitone in time — "d(u) at settle time ≤ d(u) later" reversed:
later values are below earlier ones. -/
lemma d_antitone {m n : ℕ} (h : m ≤ n) : (run.σ n).d ≤ (run.σ m).d := by
  obtain ⟨k, rfl⟩ := Nat.le.dest h
  clear h
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [Nat.add_succ]
      exact (run.d_le_of_step (m + k)).trans ih

/-- **Invariant 1 — values overestimate truth**: `distV w s v ≤ d_t v` at every
time.  Induction: `dInit ≥ distV` (pillar ii), and a push-update keeps the bound
because `distV x ≤ distV u + w u x ≤ d u + w u x` (triangle inequality). -/
theorem distV_le_d (t : ℕ) : distV w s ≤ (run.σ t).d := by
  induction t with
  | zero => rw [run.d0]; exact distV_le_dInit w s
  | succ t ih =>
      intro x
      rcases run.legal t with ⟨u, -, hd, -, -⟩ | ⟨v, -, hd, -, -, -⟩
      · rw [hd, pushUpdate_apply w u x]
        exact le_inf (ih x)
          ((distV_le_add w s u x).trans (add_le_add_left (ih u) (w u x)))
      · rw [hd, pushUpdate_apply w v x]
        exact le_inf (ih x)
          ((distV_le_add w s v x).trans (add_le_add_left (ih v) (w v x)))

/-- The source always holds its final value `0`. -/
lemma d_s (t : ℕ) : (run.σ t).d s = 0 := by
  refine le_antisymm ?_ ?_
  · have h1 : (run.σ t).d s ≤ (run.σ 0).d s := run.d_antitone (Nat.zero_le t) s
    have h2 : (run.σ 0).d s = 0 := by rw [run.d0]; simp [dInit]
    exact h1.trans_eq h2
  · rw [← distV_s w s]
    exact run.distV_le_d t s

/-- **The certification theorem — workhorse form.**  Simultaneous induction:

1. `v ∈ U_t ⇒ d_t v = distV w s v` — settlement under a certified boundary is final;
2. `b ∈ U_t ⇒ ∀ y, d_t y ≤ distV w s b + w b y` — every settled vertex's out-edges
   are relaxed (the synchronous "settlement fires the out-edge updates" invariant).

The settle case runs the first-unsettled-on-shortest-walk argument as a two-bound
walk induction (`key`): a walk `Q` with `cost Q < x := d_t v₀` (the value being
certified) and `cost Q < d_t y` cannot exist.  Decompose `Q = step a y q`:
* `a` settled: (2) at time `t` caps `d_t y ≤ distV a + w a y ≤ cost q + w a y = cost Q`,
  contradicting the second bound — this is where the atomic settle-relaxation pays;
* `a = v₀`: recurse on the shorter prefix `q` (second bound via `d_t a = x`);
* `a` unsettled, `a ≠ v₀`: the box condition gives `cost q ≤ cost Q < x ≤ B ≤ d_t a`,
  so the prefix recurses with both bounds intact.

`⊥`-cases: `Q = nil` forces `0 = cost Q < d_t s = 0`.  The top call instantiates
`y := v₀`, where the two bounds coincide; extracting a walk from `distV v₀ < x`
gives the contradiction, hence `x ≤ distV v₀`, and invariant 1 closes the equality. -/
theorem certify_and_relaxed (t : ℕ) :
    (∀ v ∈ (run.σ t).U, (run.σ t).d v = distV w s v) ∧
    (∀ b ∈ (run.σ t).U, ∀ y, (run.σ t).d y ≤ distV w s b + w b y) := by
  induction t with
  | zero =>
      refine ⟨fun v hv => ?_, fun b hb y => ?_⟩
      · rw [run.U0] at hv; simp at hv
      · rw [run.U0] at hb; simp at hb
  | succ t ih =>
      rcases run.legal t with ⟨u, -, hd, hU, -⟩ | ⟨v₀, -, hd, hU, hrule, hbox⟩
      · -- relax step: `U` unchanged; squeeze between the antitone step and invariant 1
        refine ⟨?_, ?_⟩
        · intro v hv
          rw [hU] at hv
          have hfin : (run.σ t).d v = distV w s v := ih.1 v hv
          exact le_antisymm ((run.d_le_of_step t v).trans hfin.le)
            (run.distV_le_d (t + 1) v)
        · intro b hb y
          rw [hU] at hb
          exact (run.d_le_of_step t y).trans (ih.2 b hb y)
      · -- settle step at `v₀` under rule `d v₀ ≤ B` and box `B ≤ ⨅ remaining frontier`
        let x := (run.σ t).d v₀
        have hx : x = (run.σ t).d v₀ := rfl
        have key : ∀ (k : ℕ) (y : V) (Q : Walk s y), Q.length ≤ k →
            Walk.cost w Q < x → Walk.cost w Q < (run.σ t).d y → False := by
          intro k
          induction k with
          | zero =>
              intro y Q hlen hcx hcd
              cases Q with
              | nil =>
                  rw [Walk.cost_nil, run.d_s t] at hcd
                  exact lt_irrefl _ hcd
              | step a b q => simp [Walk.length] at hlen
          | succ k ihk =>
              intro y Q hlen hcx hcd
              cases Q with
              | nil =>
                  rw [Walk.cost_nil, run.d_s t] at hcd
                  exact lt_irrefl _ hcd
              | step a _ q =>
                  have hqk : q.length ≤ k := by
                    simp [Walk.length] at hlen
                    omega
                  rw [Walk.cost_step] at hcx hcd
                  have hle : Walk.cost w q ≤ Walk.cost w q + w a y := le_self_add
                  by_cases hab : a ∈ (run.σ t).U
                  · -- settled penultimate vertex: its out-edges are relaxed (IH part 2)
                    have hR : (run.σ t).d y ≤ distV w s a + w a y := ih.2 a hab y
                    have h1 : distV w s a ≤ Walk.cost w q := iInf_le _ q
                    exact lt_irrefl _
                      ((hR.trans (add_le_add_left h1 (w a y))).trans_lt hcd)
                  · -- unsettled penultimate vertex: recurse on the shorter prefix
                    have hqx : Walk.cost w q < x := hle.trans_lt hcx
                    by_cases hav : a = v₀
                    · have hda : (run.σ t).d a = x := by rw [hav, hx]
                      exact ihk a q hqk hqx (by rw [hda]; exact hqx)
                    · have hmem : a ∈ Finset.univ \ insert v₀ (run.σ t).U :=
                        Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, by
                          rw [Finset.mem_insert]; exact fun h => h.elim hav hab⟩
                      have hboxa : (run.σ t).B ≤ (run.σ t).d a :=
                        (hbox.trans (iInf_le _ a)).trans (iInf_le _ hmem)
                      exact ihk a q hqk hqx
                        (hle.trans_lt (hcx.trans_le (hx.le.trans hrule) |>.trans_le hboxa))
        have hcert : x ≤ distV w s v₀ := by
          by_contra h
          obtain ⟨P, hP⟩ := exists_walk_cost_lt (not_le.mp h)
          exact key P.length v₀ P le_rfl hP (by rw [← hx]; exact hP)
        have hcert' : (run.σ t).d v₀ ≤ distV w s v₀ := by rw [← hx]; exact hcert
        refine ⟨?_, ?_⟩
        · intro v hv
          rw [hU, Finset.mem_insert] at hv
          rcases hv with hev | hv
          · subst v
            have h2 : (run.σ (t + 1)).d v₀ = (run.σ t).d v₀ := by
              rw [hd, pushUpdate_self]
            rw [h2]
            exact le_antisymm hcert' (run.distV_le_d t v₀)
          · have hfin : (run.σ t).d v = distV w s v := ih.1 v hv
            exact le_antisymm ((run.d_le_of_step t v).trans hfin.le)
              (run.distV_le_d (t + 1) v)
        · intro b hb y
          rw [hU, Finset.mem_insert] at hb
          rcases hb with heb | hb
          · subst b
            have h1 : (run.σ (t + 1)).d y ≤ (run.σ t).d v₀ + w v₀ y := by
              rw [hd, pushUpdate_apply w v₀ y]
              exact inf_le_right
            exact h1.trans (add_le_add_left hcert' (w v₀ y))
          · exact (run.d_le_of_step t y).trans (ih.2 b hb y)

/-- **THE CERTIFICATION THEOREM.**  A vertex settled at any time of a legal run
carries its true shortest distance: settlement under a certified boundary
(settle rule + box condition) implies finality. -/
theorem certified_settled_final (t : ℕ) {v : V} (hv : v ∈ (run.σ t).U) :
    (run.σ t).d v = distV w s v :=
  (run.certify_and_relaxed t).1 v hv

/-- Out-edges of settled vertices are relaxed at every later-or-equal time:
`d_t y ≤ distV b + w b y` for `b ∈ U_t`. -/
theorem settled_edges_relaxed (t : ℕ) {b : V} (hb : b ∈ (run.σ t).U) (y : V) :
    (run.σ t).d y ≤ distV w s b + w b y :=
  (run.certify_and_relaxed t).2 b hb y

/-- **FROZEN-LOCK corollary** (Zhao fast-sweeping lock invariant: "whenever a grid
point obtains the minimal value it can reach, the value is the correct value and
will not be changed in later iterations").  Once `v` is settled, no later step —
relax or settle — changes `d v`: later values are still caps of walk-cost
upper bounds (antitone) and still overestimate `distV` (invariant 1), which now
equals the settled value.  This is the two-line consequence of certification +
overestimation, and the lemma that lets the async echo-sweep refinement skip
re-expansion of certified vertices. -/
theorem frozen_lock (t : ℕ) {v : V} (hv : v ∈ (run.σ t).U) (n : ℕ) (ht : t ≤ n) :
    (run.σ n).d v = (run.σ t).d v := by
  refine le_antisymm (run.d_antitone ht v) ?_
  rw [run.certified_settled_final t hv]
  exact run.distV_le_d n v

end CertifiedRun

/-! ## Non-vacuity -/

/-- A concrete legal run: settle the source at step 0 (always legal from the `⊤`
boundary), then re-relax at `s` forever. -/
def trivialSigma (w : V → V → ℝ≥0∞) (s : V) : ℕ → CertState V
  | 0 => { d := dInit s, U := ∅, B := ⊤ }
  | t + 1 => { d := pushUpdate w s (trivialSigma w s t).d, U := {s}, B := ⊤ }

/-- `CertifiedRun w s` is inhabited for every graph: the certification theorem is
not vacuous.  (The `⊤` initial boundary also *forces* the first settlement to be
the source: while `s` sits unsettled with `d s = 0` in the box range, the box
`⊤ ≤ ⨅ frontier dInit` fails for every other vertex.) -/
def trivialRun (w : V → V → ℝ≥0∞) (s : V) : CertifiedRun w s where
  σ := trivialSigma w s
  init := rfl
  legal := by
    intro t
    rcases t with _ | t
    · -- step 0: settle the source
      refine Or.inr ⟨s, ?_, ?_, ?_, ?_, ?_⟩
      · simp [trivialSigma]
      · rfl
      · rfl
      · simp [trivialSigma, dInit]
      · refine le_iInf fun v => le_iInf fun hv => ?_
        have hne : v ≠ s := by
          have hv' := (Finset.mem_sdiff.mp hv).2
          simp [trivialSigma] at hv'
          intro heq
          exact hv' (by rw [heq])
        have hB : (trivialSigma w s 0).B = ⊤ := by simp [trivialSigma]
        rw [hB]
        simp [trivialSigma, dInit, hne]
    · -- steps t+1: re-relax at the source
      refine Or.inl ⟨s, ?_, ?_, ?_, ?_⟩
      · simp [trivialSigma]
      · rfl
      · rfl
      · rfl

end RelaxLFP

/-! ## Status ledger (honest)

Pillar (iii) — proved, ZERO sorries:

* the synchronous certification engine (`pushUpdate`, `CertState`, `LegalStep`,
  `CertifiedRun`) — settle fires the out-edge push atomically (the
  settle-without-relaxation loophole is a genuine counterexample without it,
  documented above and in `DESIGN.md`);
* invariant 1 `CertifiedRun.distV_le_d` — values overestimate truth at every time;
* `CertifiedRun.d_antitone` — estimates are monotone nonincreasing across steps;
* `CertifiedRun.settled_edges_relaxed` — settled vertices' out-edges stay relaxed;
* **THE CERTIFICATION THEOREM** `CertifiedRun.certified_settled_final` —
  `v ∈ U_t ⇒ d_t v = distV w s v`: settlement under a certified boundary
  (rule `d v ≤ B` + box `B ≤ ⨅ remaining frontier`) implies finality;
* **FROZEN-LOCK** `CertifiedRun.frozen_lock` (Zhao fast-sweeping lock invariant) —
  a settled vertex's value never changes again;
* `trivialRun` — the engine class is inhabited (non-vacuity).

The async echo-sweep engine is the refinement: echo sweeps re-fire `relax` steps,
and `frozen_lock` is exactly the lemma licensing skipped re-expansion of
certified vertices.
-/



