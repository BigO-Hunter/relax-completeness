/-
Copyright (c) 2026. Capped-relaxation SSSP completeness (pillar iv — async).
-/
import Pillar3

open ENNReal

namespace RelaxLFP

universe u v

set_option linter.unusedSectionVars false

/-!
# Pillar (iv): the async engine — pending pushes, the lookahead box, and healing

Pillar (iii) certified a SYNCHRONOUS engine: `settle v` fires the push-relaxation at
`v` atomically.  Its honesty ledger records that this is forced — settle-without-
relaxation admits the counterexample `s →(1) a →(1) v`, `s →(5) v` (settle `v` at the
stale `5` while `distV v = 2`).  The real engine (beyond-dijkstra V5, auditing
arXiv:2602.07868) is ASYNC: relaxation arrives later, via delayed echo sweeps —
pending pushes that fire after settlement.

## Model

`AsyncState V = (d, U, B, P)`: estimates, settled set, boundary, and a **pending-push
set** `P : Finset (V × V)` — edges whose relaxation `d v ⊓= d u + w u v` has not yet
been applied.  A push carries NO value: applying `(u, x)` re-reads the CURRENT `d u`
(echo-sweep semantics: the message means "re-relax edge `(u,x)`", not "here is a
number").  This is what makes the invariant `d y ≤ d b + w b y ∨ (b,y) ∈ P` hold with
*current* values — a value-carrying message would need a staleness side-condition
instead.  Three transitions (`BlindStep`):

* **apply** `(u,x) ∈ P`: `d x ⊓= d u + w u x` (current reads), `P \= {(u,x)}`;
* **echo** at `u ∈ U` (re-settlement / echo sweep): all out-edges of `u` enter `P`;
* **settle** `v ∉ U` under rule `d v ≤ B` and box `B ≤ ⨅ (u ∉ insert v U), d u` —
  `d` is UNCHANGED (no atomic push!), `v`'s out-edges enter `P`, `post.B`
  unconstrained.

## The central question, answered

**The blind engine (rule + box, no lookahead) does NOT certify** —
`cexRun` below is the rowh-shaped concrete counterexample: on `s →(1) a →(1) v`,
`s →(5) v` it settles `v` at the stale `5 = distV ≠ 2`, exactly because the pending
push `(a,v)` (potential `1 + 1 = 2 < B = 5`) is invisible to the box.

**The exact soundness condition is the null-message/lookahead box** (boundedlag
NOTE: `certified := below GVT` — the channel-clock floor in event time): at every
settle, IN ADDITION to the frontier box,

    B ≤ ⨅ (u,x) ∈ P, d u + w u x        (`LookaheadBoxed`)

— no pending push can produce a value below `B`.  Ranged over `pre.P` (pre-settle:
the pushes `v`'s own settlement creates have potential `d v + w v x` which may
legitimately sit below `B`; they threaten FUTURE settles, which run their own
lookahead check).  `certified_settled_final_async` proves it sufficient: the
pillar-(iii) walk induction extends with one new case split — the penultimate
vertex `a` of a too-cheap walk is settled, so its edge to `y` is *relaxed or
pending*; relaxed caps `d y ≤ cost`, pending is bounded below by the lookahead box.
Necessity is witnessed by `cexRun` + `cex_lookahead_violated` (the box fails at
precisely the fatal settle, and the certification conclusion fails on the run).

**Healing** (`healing_of_stable_and_edgeFair`): WITHOUT lookahead, if the value
vector stabilizes and every edge is re-relaxed infinitely often (fairness must cover
pushes: `RelaxesEdge` for every `(u,x)` cofinally often — which in this model
presupposes every vertex settles/echo-sweeps cofinally often, since only settled
sources are ever enqueued), then `d` converges to `distV`: the stable vector is
edge-relaxed everywhere, hence post-fixed for `T_BF`, hence `≤ distV` (pillar ii's
`le_distV_of_le_T_BF`), while invariant 1 gives `distV ≤ d`.  Stability itself is
supplied by pillar (i)'s discreteness (`exists_eventuallyConstant_of_antitone`)
under a finite-value-range hypothesis — see the honest seam note there.

**Frozen lock / skip-re-expansion** (fastsweep NOTE): under sound certification,
`frozen_lock_async` — a settled vertex's value never changes again — and
`settled_push_noop`: applying ANY push to a settled target is provably a no-op, so
echo sweeps may skip certified vertices (or fire at them harmlessly).
-/

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## The async engine -/

/-- Single-edge relaxation: apply the pending push `p = (u,x)`, re-reading the
CURRENT `d u`.  Only the target `p.2` changes. -/
def applyPush (w : V → V → ℝ≥0∞) (p : V × V) (d : V → ℝ≥0∞) : V → ℝ≥0∞ :=
  fun x => if x = p.2 then d x ⊓ (d p.1 + w p.1 x) else d x

lemma applyPush_target (w : V → V → ℝ≥0∞) (p : V × V) (d : V → ℝ≥0∞) :
    applyPush w p d p.2 = d p.2 ⊓ (d p.1 + w p.1 p.2) := by
  rw [applyPush]
  split
  next _ => rfl
  next h => simp at h

lemma applyPush_of_ne {w : V → V → ℝ≥0∞} {p : V × V} {d : V → ℝ≥0∞} {x : V}
    (h : x ≠ p.2) : applyPush w p d x = d x := by
  rw [applyPush]
  split
  next h' => exact absurd h' h
  next _ => rfl

lemma applyPush_le (w : V → V → ℝ≥0∞) (p : V × V) (d : V → ℝ≥0∞) :
    applyPush w p d ≤ d := by
  intro x
  by_cases h : x = p.2
  · subst h; rw [applyPush_target]; exact inf_le_left
  · rw [applyPush_of_ne h]

/-- State of the async certification engine: estimates, settled set, boundary, and
the pending-push set `P` of edges whose relaxation has not yet been applied. -/
structure AsyncState (V : Type u) where
  d : V → ℝ≥0∞
  U : Finset V
  B : ℝ≥0∞
  P : Finset (V × V)

/-- One legal transition of the BLIND async engine: apply a pending push, echo-sweep
at a settled vertex (all its out-edges enter `P`), or settle `v ∉ U` under the rule
`d v ≤ B` and the frontier box `B ≤ ⨅ (u ∉ insert v U), d u` — with `d` UNCHANGED
(no atomic push: `v`'s out-edges merely enter `P`) and `post.B` unconstrained. -/
def BlindStep (w : V → V → ℝ≥0∞) (pre post : AsyncState V) : Prop :=
  (∃ p ∈ pre.P, post.d = applyPush w p pre.d ∧ post.U = pre.U ∧ post.B = pre.B ∧
    post.P = pre.P \ {p}) ∨
  (∃ u ∈ pre.U, post.d = pre.d ∧ post.U = pre.U ∧ post.B = pre.B ∧
    post.P = pre.P ∪ Finset.image (fun x => (u, x)) Finset.univ) ∨
  (∃ v, v ∉ pre.U ∧ post.d = pre.d ∧ post.U = insert v pre.U ∧
    pre.d v ≤ pre.B ∧
    pre.B ≤ ⨅ u ∈ Finset.univ \ insert v pre.U, pre.d u ∧
    post.P = pre.P ∪ Finset.image (fun x => (v, x)) Finset.univ)

/-- A legal blind run from the standard start (`d = dInit s`, `U = ∅`, `B = ⊤`,
`P = ∅`; the `⊤` boundary forces the first settlement to be the source, as in
pillar iii). -/
structure AsyncRun (w : V → V → ℝ≥0∞) (s : V) where
  σ : ℕ → AsyncState V
  init : σ 0 = { d := dInit s, U := ∅, B := ⊤, P := ∅ }
  legal : ∀ t, BlindStep w (σ t) (σ (t + 1))

/-- **The null-message / lookahead box** (the exact soundness condition): at every
settle step of the run — detected by `U` gaining an element, which apply/echo steps
never do — every pending push's current potential `d u + w u x` is at or above the
boundary `B`.  Pointwise-`⨅` form: `B ≤ ⨅ p ∈ P, d p.1 + w p.1 p.2`; empty `P` is
vacuous, matching `⨅ ∅ = ⊤`.  Ranged over the PRE-settle `P`: the pushes created by
the settlement itself may sit below `B` (they are the settlement's own relaxation
work; they threaten only future settles, which run their own check). -/
def LookaheadBoxed (w : V → V → ℝ≥0∞) {s : V} (run : AsyncRun w s) : Prop :=
  ∀ t, (∃ v, v ∉ (run.σ t).U ∧ (run.σ (t + 1)).U = insert v (run.σ t).U) →
    ∀ p ∈ (run.σ t).P, (run.σ t).B ≤ (run.σ t).d p.1 + w p.1 p.2

/-! ## Run-level invariants (blind engine — no lookahead needed) -/

namespace AsyncRun

variable {w : V → V → ℝ≥0∞} {s : V} (run : AsyncRun w s)

lemma d0 : (run.σ 0).d = dInit s := by rw [run.init]

lemma U0 : (run.σ 0).U = ∅ := by rw [run.init]

lemma P0 : (run.σ 0).P = ∅ := by rw [run.init]

/-- Every step only lowers estimates: apply-pushes cap the target; echo and settle
leave `d` untouched. -/
lemma d_le_of_step (t : ℕ) : (run.σ (t + 1)).d ≤ (run.σ t).d := by
  set pre := run.σ t
  set post := run.σ (t + 1)
  have hleg : BlindStep w pre post := run.legal t
  rcases hleg with ⟨p, -, hd, -, -, -⟩ | ⟨u, -, hd, -, -, -⟩ | ⟨v, -, hd, -, -, -, -⟩
  · rw [hd]; exact applyPush_le w p _
  · rw [hd]
  · rw [hd]

/-- Estimates are antitone in time. -/
lemma d_antitone {m n : ℕ} (h : m ≤ n) : (run.σ n).d ≤ (run.σ m).d := by
  obtain ⟨k, rfl⟩ := Nat.le.dest h
  clear h
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [Nat.add_succ]
      exact (run.d_le_of_step (m + k)).trans ih

/-- **Invariant 1 — values overestimate truth**: `distV w s ≤ d_t` at every time,
for the blind engine.  The apply case is the pillar-(iii) push argument (triangle
inequality on the re-read source value); echo and settle do not touch `d`. -/
theorem distV_le_d (t : ℕ) : distV w s ≤ (run.σ t).d := by
  induction t with
  | zero => rw [run.d0]; exact distV_le_dInit w s
  | succ t ih =>
      intro x
      set pre := run.σ t
      set post := run.σ (t + 1)
      have hleg : BlindStep w pre post := run.legal t
      rcases hleg with ⟨p, -, hd, -, -, -⟩ | ⟨u, -, hd, -, -, -⟩ | ⟨v, -, hd, -, -, -, -⟩
      · rw [hd]
        by_cases hx : x = p.2
        · subst x
          rw [applyPush_target]
          exact le_inf (ih p.2)
            ((distV_le_add w s p.1 p.2).trans (add_le_add_left (ih p.1) (w p.1 p.2)))
        · rw [applyPush_of_ne hx]; exact ih x
      · rw [hd]; exact ih x
      · rw [hd]; exact ih x

/-- The source always holds its final value `0`. -/
lemma d_s (t : ℕ) : (run.σ t).d s = 0 := by
  refine le_antisymm ?_ ?_
  · have h1 : (run.σ t).d s ≤ (run.σ 0).d s := run.d_antitone (Nat.zero_le t) s
    have h2 : (run.σ 0).d s = 0 := by rw [run.d0]; simp [dInit]
    exact h1.trans_eq h2
  · rw [← distV_s w s]
    exact run.distV_le_d t s

/-! ## The async certification theorem -/

/-- **Async edge accounting.**  For a settled vertex `b`, every out-edge is either
already relaxed against the CURRENT value (`d y ≤ d b + w b y`) or still pending
(`(b,y) ∈ P`).  This replaces pillar (iii)'s `settled_edges_relaxed` (which held
unconditionally because settle fired the push atomically): here settle only
enqueues, so the invariant is a disjunction.  Its maintenance under `apply` uses
part 1 essentially: applying a push `(p₁, p₂)` can lower `d p₂`, which would break
the left arm for a settled TARGET `b = p₂` — unless `b` is certified, hence frozen
(`post.d b = pre.d b` by antitonicity + invariant 1).  This is why the two parts
are proved simultaneously, and why the theorem needs the run to be sound: for a
blind run the invariant is false (settled values can drop — that is the healing
regime). -/
theorem certify_and_relaxed_async (hLA : LookaheadBoxed w run) (t : ℕ) :
    (∀ v ∈ (run.σ t).U, (run.σ t).d v = distV w s v) ∧
    (∀ b ∈ (run.σ t).U, ∀ y,
      (run.σ t).d y ≤ (run.σ t).d b + w b y ∨ (b, y) ∈ (run.σ t).P) := by
  induction t with
  | zero =>
      refine ⟨fun v hv => ?_, fun b hb y => ?_⟩
      · rw [run.U0] at hv; simp at hv
      · rw [run.U0] at hb; simp at hb
  | succ t ih =>
      set pre := run.σ t
      set post := run.σ (t + 1)
      have hleg : BlindStep w pre post := run.legal t
      rcases hleg with ⟨p, -, hd, hU, -, hP⟩ | ⟨u, -, hd, hU, -, hP⟩
          | ⟨v₀, hv₀, hd, hU, hrule, hbox, hP⟩
      · -- apply-push step
        refine ⟨?_, ?_⟩
        · intro v hv
          rw [hU] at hv
          have hfin : pre.d v = distV w s v := ih.1 v hv
          exact le_antisymm ((run.d_le_of_step t v).trans hfin.le)
            (run.distV_le_d (t + 1) v)
        · intro b hb y
          rw [hU] at hb
          -- settled vertices are certified at `t`, hence frozen across the step
          have hfreeze : post.d b = pre.d b :=
            le_antisymm (run.d_le_of_step t b)
              (by rw [ih.1 b hb]; exact run.distV_le_d (t + 1) b)
          by_cases hbp : (b, y) = p
          · -- the applied push IS the edge `(b,y)`: the cap gives the left arm
            obtain ⟨hb1, hb2⟩ := Prod.ext_iff.mp hbp
            have hb1' : b = p.1 := hb1
            have hb2' : y = p.2 := hb2
            rw [hb1', hb2']
            have hcap : post.d p.2 ≤ pre.d p.1 + w p.1 p.2 := by
              rw [hd, applyPush_target]
              exact inf_le_right
            by_cases hself : p.1 = p.2
            · rw [hself]
              exact Or.inl le_self_add
            · have hb1' : post.d p.1 = pre.d p.1 := by rw [hd, applyPush_of_ne hself]
              exact Or.inl (by rw [hb1']; exact hcap)
          · -- a different edge: membership survives the removal
            rcases ih.2 b hb y with hl | hr
            · exact Or.inl (by rw [hfreeze]; exact (run.d_le_of_step t y).trans hl)
            · refine Or.inr ?_
              rw [hP]
              exact Finset.mem_sdiff.mpr ⟨hr, fun h => hbp (Finset.mem_singleton.mp h)⟩
      · -- echo-sweep step: `d` unchanged, `P` grows
        refine ⟨?_, ?_⟩
        · intro v hv
          rw [hU] at hv
          rw [hd]
          exact ih.1 v hv
        · intro b hb y
          rw [hU] at hb
          rcases ih.2 b hb y with hl | hr
          · exact Or.inl (by rw [hd]; exact hl)
          · exact Or.inr (by rw [hP]; exact Finset.mem_union.mpr (Or.inl hr))
      · -- settle step at `v₀`: `d` unchanged, box + rule + LOOKAHEAD do the work
        have hB2 : ∀ q ∈ pre.P, pre.B ≤ pre.d q.1 + w q.1 q.2 :=
          hLA t ⟨v₀, hv₀, hU⟩
        let x := pre.d v₀
        have hx : x = pre.d v₀ := rfl
        have key : ∀ (k : ℕ) (y : V) (Q : Walk s y), Q.length ≤ k →
            Walk.cost w Q < x → Walk.cost w Q < pre.d y → False := by
          intro k
          induction k with
          | zero =>
              intro y Q hlen hcx hcd
              cases Q with
              | nil =>
                  have hds : pre.d s = 0 := run.d_s t
                  rw [Walk.cost_nil, hds] at hcd
                  exact lt_irrefl _ hcd
              | step a b q => simp [Walk.length] at hlen
          | succ k ihk =>
              intro y Q hlen hcx hcd
              cases Q with
              | nil =>
                  have hds : pre.d s = 0 := run.d_s t
                  rw [Walk.cost_nil, hds] at hcd
                  exact lt_irrefl _ hcd
              | step a _ q =>
                  have hqk : q.length ≤ k := by
                    simp [Walk.length] at hlen
                    omega
                  rw [Walk.cost_step] at hcx hcd
                  have hle : Walk.cost w q ≤ Walk.cost w q + w a y := le_self_add
                  have h1 : distV w s a ≤ Walk.cost w q := iInf_le _ q
                  by_cases hab : a ∈ pre.U
                  · -- settled penultimate vertex: relaxed OR pending (IH part 2)
                    rcases ih.2 a hab y with hl | hr
                    · -- relaxed arm: cap contradiction, as in pillar (iii)
                      have hda : pre.d a = distV w s a := ih.1 a hab
                      have h2 : pre.d a ≤ Walk.cost w q := by rw [hda]; exact h1
                      have h3 : pre.d a + w a y ≤ Walk.cost w q + w a y :=
                        add_le_add_left h2 (w a y)
                      exact lt_irrefl _ ((hl.trans h3).trans_lt hcd)
                    · -- PENDING arm: the lookahead box bounds the push potential
                      have hb2 : pre.B ≤ pre.d a + w a y := hB2 (a, y) hr
                      have hda : pre.d a = distV w s a := ih.1 a hab
                      have h2 : pre.d a ≤ Walk.cost w q := by rw [hda]; exact h1
                      have h3 : pre.d a + w a y ≤ Walk.cost w q + w a y :=
                        add_le_add_left h2 (w a y)
                      have h4 : x ≤ Walk.cost w q + w a y :=
                        (hrule.trans hb2).trans h3
                      exact lt_irrefl _ (hcx.trans_le h4)
                  · -- unsettled penultimate vertex: recurse on the shorter prefix
                    have hqx : Walk.cost w q < x := hle.trans_lt hcx
                    by_cases hav : a = v₀
                    · have hda : pre.d a = x := by rw [hav, hx]
                      exact ihk a q hqk hqx (by rw [hda]; exact hqx)
                    · have hmem : a ∈ Finset.univ \ insert v₀ pre.U :=
                        Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, by
                          rw [Finset.mem_insert]; exact fun h => h.elim hav hab⟩
                      have hboxa : pre.B ≤ pre.d a :=
                        (hbox.trans (iInf_le _ a)).trans (iInf_le _ hmem)
                      exact ihk a q hqk hqx
                        (hle.trans_lt (hcx.trans_le (hx.le.trans hrule) |>.trans_le hboxa))
        have hcert : x ≤ distV w s v₀ := by
          by_contra h
          obtain ⟨P, hP⟩ := exists_walk_cost_lt (not_le.mp h)
          exact key P.length v₀ P le_rfl hP (by rw [← hx]; exact hP)
        have hcert' : pre.d v₀ ≤ distV w s v₀ := by rw [← hx]; exact hcert
        refine ⟨?_, ?_⟩
        · intro v hv
          rw [hU, Finset.mem_insert] at hv
          rcases hv with hev | hv
          · subst v
            rw [hd]
            exact le_antisymm hcert' (run.distV_le_d t v₀)
          · rw [hd]
            exact ih.1 v hv
        · intro b hb y
          rw [hU, Finset.mem_insert] at hb
          rcases hb with heb | hb
          · subst b
            refine Or.inr ?_
            rw [hP]
            exact Finset.mem_union.mpr (Or.inr
              (Finset.mem_image.mpr ⟨y, Finset.mem_univ y, rfl⟩))
          · rcases ih.2 b hb y with hl | hr
            · exact Or.inl (by rw [hd]; exact hl)
            · exact Or.inr (by rw [hP]; exact Finset.mem_union.mpr (Or.inl hr))

/-- **THE ASYNC CERTIFICATION THEOREM.**  A vertex settled by a run whose settles
respect the null-message/lookahead box carries its true shortest distance at every
later-or-equal time: `v ∈ U_t ⇒ d_t v = distV w s v`.  The pillar-(iii) induction
extends: the first-unsettled-on-shortest-walk argument routes through pending
pushes — the penultimate vertex's edge is either applied (`d y` already capped) or
pending (bounded by the lookahead box). -/
theorem certified_settled_final_async (hLA : LookaheadBoxed w run) (t : ℕ)
    {v : V} (hv : v ∈ (run.σ t).U) : (run.σ t).d v = distV w s v :=
  (run.certify_and_relaxed_async hLA t).1 v hv

/-- Settled out-edges are relaxed-or-pending at every time (async edge accounting). -/
theorem settled_edges_accounted (hLA : LookaheadBoxed w run) (t : ℕ)
    {b : V} (hb : b ∈ (run.σ t).U) (y : V) :
    (run.σ t).d y ≤ (run.σ t).d b + w b y ∨ (b, y) ∈ (run.σ t).P :=
  (run.certify_and_relaxed_async hLA t).2 b hb y

/-- **FROZEN LOCK, async** (Zhao fast-sweeping lock invariant): under sound
certification a settled vertex's value never changes again. -/
theorem frozen_lock_async (hLA : LookaheadBoxed w run) (t : ℕ)
    {v : V} (hv : v ∈ (run.σ t).U) (n : ℕ) (ht : t ≤ n) :
    (run.σ n).d v = (run.σ t).d v := by
  refine le_antisymm (run.d_antitone ht v) ?_
  rw [run.certified_settled_final_async hLA t hv]
  exact run.distV_le_d n v

/-- **SKIP-RE-EXPANSION LICENSE** (fastsweep NOTE, frozen-lock): applying any step —
including an echo-sweep push aimed at a certified vertex — leaves a settled vertex's
value untouched, so echo sweeps may skip settled vertices (or fire at them
harmlessly: the push is a provable no-op on the target). -/
theorem settled_push_noop (hLA : LookaheadBoxed w run) (t : ℕ)
    {p : V × V} (hp : p.2 ∈ (run.σ t).U) :
    (run.σ (t + 1)).d p.2 = (run.σ t).d p.2 :=
  run.frozen_lock_async hLA t hp (t + 1) (Nat.le_succ t)

end AsyncRun

/-! ## The negative result: without the lookahead box, certification FAILS

The rowh-shaped counterexample, as a concrete blind run.  Graph: `0 = s`, `1 = a`,
`2 = v`; edges `s →(1) a`, `a →(1) v`, `s →(5) v`; everything else `⊤`.  The run
settles `s` with boundary `5`, applies `(s,a)` (`d a = 1`), settles `a` (box over the
remaining frontier `{v}` with `d v = ⊤` passes — the push `(s,v)` is still pending but
its potential `0 + 5 = 5 ≥ B` would pass lookahead anyway), applies `(s,v)`
(`d v = 5`), then settles `v` with the STALE `d v = 5 ≤ B = 5` over the empty frontier
— while the pending push `(a,v)` has potential `1 + 1 = 2 < 5 = B` and `distV v = 2`.
Every step is `BlindStep`-legal (rule + frontier box); the lookahead box fails at
precisely the fatal settle (`cex_lookahead_violated`), and the settled vertex carries
a wrong value (`certification_fails_without_lookahead`).  This is the pillar-(iii)
settle-without-relaxation counterexample reborn as pure scheduling: the relaxation
was fired, but too late. -/

section Counterexample

/-- The counterexample graph (complete-hop-graph convention: non-edges are `⊤`). -/
def cw : Fin 3 → Fin 3 → ℝ≥0∞ := fun a b =>
  if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 2 then 1 else
    if a = 0 ∧ b = 2 then 5 else ⊤

private lemma fin3_eq_two {x : Fin 3} (h1 : x ≠ 1) (h0 : x ≠ 0) : x = 2 := by
  rcases x with ⟨n, hn⟩
  have hn1 : n ≠ 1 := fun hh => h1 (Fin.ext_iff.mpr hh)
  have hn0 : n ≠ 0 := fun hh => h0 (Fin.ext_iff.mpr hh)
  exact Fin.ext_iff.mpr (by omega)

def cexP1 : Finset (Fin 3 × Fin 3) := Finset.image (fun x => ((0 : Fin 3), x)) Finset.univ
def cexdA : Fin 3 → ℝ≥0∞ := applyPush cw (0, 1) (dInit (0 : Fin 3))
def cexP2 : Finset (Fin 3 × Fin 3) := cexP1 \ {((0 : Fin 3), 1)}
def cexP3 : Finset (Fin 3 × Fin 3) :=
  cexP2 ∪ Finset.image (fun x => ((1 : Fin 3), x)) Finset.univ
def cexdB : Fin 3 → ℝ≥0∞ := applyPush cw (0, 2) cexdA
def cexP4 : Finset (Fin 3 × Fin 3) := cexP3 \ {((0 : Fin 3), 2)}
def cexP5 : Finset (Fin 3 × Fin 3) :=
  cexP4 ∪ Finset.image (fun x => ((2 : Fin 3), x)) Finset.univ

/-- The run: settle `s` (B := 5), apply `(s,a)`, settle `a`, apply `(s,v)`, settle
`v` at the stale `5`, then echo-sweep at `v` forever (a no-op union). -/
def cexSigma (t : ℕ) : AsyncState (Fin 3) :=
  if t = 0 then { d := dInit 0, U := ∅, B := ⊤, P := ∅ }
  else if t = 1 then { d := dInit 0, U := {0}, B := 5, P := cexP1 }
  else if t = 2 then { d := cexdA, U := {0}, B := 5, P := cexP2 }
  else if t = 3 then { d := cexdA, U := {0, 1}, B := 5, P := cexP3 }
  else if t = 4 then { d := cexdB, U := {0, 1}, B := 5, P := cexP4 }
  else { d := cexdB, U := {0, 1, 2}, B := 5, P := cexP5 }

private lemma cexdA_one : cexdA (1 : Fin 3) = 1 := by
  have h1 : cexdA 1 = dInit (0 : Fin 3) 1 ⊓ (dInit (0 : Fin 3) 0 + cw 0 1) := by
    rw [cexdA, applyPush_target]
  have h2 : dInit (0 : Fin 3) 1 = ⊤ := by simp [dInit]
  have h3 : dInit (0 : Fin 3) 0 = 0 := by simp [dInit]
  have h4 : cw (0 : Fin 3) 1 = 1 := by simp [cw]
  have h5 : (0 : ℝ≥0∞) + 1 = 1 := by norm_num
  rw [h1, h2, h3, h4, h5]
  exact le_antisymm inf_le_right (le_inf le_top le_rfl)

private lemma cexdA_two : cexdA (2 : Fin 3) = ⊤ := by simp [cexdA, applyPush, dInit]

private lemma cexdA_zero : cexdA (0 : Fin 3) = 0 := by simp [cexdA, applyPush, dInit]

private lemma cexdB_two : cexdB (2 : Fin 3) = 5 := by
  have h1 : cexdB 2 = cexdA 2 ⊓ (cexdA 0 + cw 0 2) := by rw [cexdB, applyPush_target]
  have h4 : cw (0 : Fin 3) 2 = 5 := by simp [cw]
  have h5 : (0 : ℝ≥0∞) + 5 = 5 := by norm_num
  rw [h1, cexdA_two, cexdA_zero, h4, h5]
  exact le_antisymm inf_le_right (le_inf le_top le_rfl)

private lemma cexdB_one : cexdB (1 : Fin 3) = 1 := by
  have h : cexdB 1 = cexdA 1 := by simp [cexdB, applyPush]
  rw [h, cexdA_one]

def cexRun : AsyncRun cw (0 : Fin 3) where
  σ := cexSigma
  init := by simp [cexSigma]
  legal := by
    intro t
    rcases t with _ | _ | _ | _ | _ | _ | t
    · -- step 0: settle the source at boundary 5
      refine Or.inr (Or.inr ⟨0, by decide, rfl, by decide, ?_, ?_, by decide⟩)
      · show dInit (0 : Fin 3) 0 ≤ (⊤ : ℝ≥0∞)
        have : dInit (0 : Fin 3) 0 = 0 := by simp [dInit]
        rw [this]
        exact le_top
      · show (⊤ : ℝ≥0∞) ≤ ⨅ u ∈ Finset.univ \ insert (0 : Fin 3) (∅ : Finset (Fin 3)),
          dInit (0 : Fin 3) u
        refine le_iInf fun u => le_iInf fun hu => ?_
        have hne : u ≠ 0 := by
          have h1 := (Finset.mem_sdiff.mp hu).2
          simpa using h1
        have : dInit (0 : Fin 3) u = ⊤ := by simp [dInit, hne]
        rw [this]
    · -- step 1: apply the pending push (s,a); d a := ⊤ ⊓ (0 + 1) = 1
      refine Or.inl ⟨(0, 1), by decide, rfl, rfl, rfl, by decide⟩
    · -- step 2: settle a — the frontier box passes over the still-⊤ vertex v
      refine Or.inr (Or.inr ⟨1, by decide, rfl, by decide, ?_, ?_, rfl⟩)
      · show cexdA (1 : Fin 3) ≤ (5 : ℝ≥0∞)
        rw [cexdA_one]
        norm_num
      · show (5 : ℝ≥0∞) ≤ ⨅ u ∈ Finset.univ \ insert (1 : Fin 3) ({0} : Finset (Fin 3)),
          cexdA u
        refine le_iInf fun u => le_iInf fun hu => ?_
        have h1 := (Finset.mem_sdiff.mp hu).2
        have h2 : ¬(u = 1 ∨ u = 0) := by simpa using h1
        have hu2 : u = 2 := fin3_eq_two (fun hh => h2 (Or.inl hh)) (fun hh => h2 (Or.inr hh))
        rw [hu2, cexdA_two]
        exact le_top
    · -- step 3: apply the pending push (s,v); d v := ⊤ ⊓ (0 + 5) = 5
      refine Or.inl ⟨(0, 2), by decide, rfl, rfl, rfl, by decide⟩
    · -- step 4: settle v at the STALE 5 — rule 5 ≤ 5 ✓, empty-frontier box ✓,
        -- but the pending push (a,v) has potential 2 < 5: lookahead would refuse
      refine Or.inr (Or.inr ⟨2, by decide, rfl, by decide, ?_, ?_, rfl⟩)
      · show cexdB (2 : Fin 3) ≤ (5 : ℝ≥0∞)
        rw [cexdB_two]
      · show (5 : ℝ≥0∞) ≤ ⨅ u ∈ Finset.univ \ insert (2 : Fin 3) ({0, 1} : Finset (Fin 3)),
          cexdB u
        refine le_iInf fun u => le_iInf fun hu => ?_
        have hall : ∀ x : Fin 3, x ∈ insert (2 : Fin 3) ({0, 1} : Finset (Fin 3)) := by decide
        exact absurd (hall u) ((Finset.mem_sdiff.mp hu).2)
    · -- step 5: echo-sweep at the settled v — a no-op union
      refine Or.inr (Or.inl ⟨2, by decide, rfl, rfl, rfl, by decide⟩)
    · -- steps t+6: echo-sweep at the settled v — a no-op union
      rw [show t + 1 + 1 + 1 + 1 + 1 + 1 = t + 6 by omega]
      have h6 : cexSigma (t + 6) = cexSigma 5 := by
        simp [cexSigma, show t + 6 ≠ 1 by omega,
          show t + 6 ≠ 2 by omega, show t + 6 ≠ 3 by omega, show t + 6 ≠ 4 by omega]
      have h7 : cexSigma (t + 6 + 1) = cexSigma 5 := by
        simp [cexSigma, show t + 6 + 1 ≠ 1 by omega,
          show t + 6 + 1 ≠ 2 by omega, show t + 6 + 1 ≠ 3 by omega,
          show t + 6 + 1 ≠ 4 by omega]
      rw [h6, h7]
      refine Or.inr (Or.inl ⟨2, by decide, rfl, rfl, rfl, by decide⟩)

/-- The true distance to `v = 2` is at most 2 (the walk `s →(1) a →(1) v`). -/
theorem cex_distV_le : distV cw (0 : Fin 3) 2 ≤ 2 :=
  (iInf_le _ (Walk.step 1 2 (Walk.step (0 : Fin 3) 1 Walk.nil))).trans_eq (by
    rw [Walk.cost_step, Walk.cost_step, Walk.cost_nil]
    have h1 : cw (0 : Fin 3) 1 = 1 := by simp [cw]
    have h2 : cw (1 : Fin 3) 2 = 1 := by simp [cw]
    rw [h1, h2]
    norm_num)

/-- **NEGATIVE RESULT.**  The blind async engine (settle rule + frontier box, no
lookahead) does NOT certify: this concrete legal run settles vertex `2` at time `5`
with value `5 ≠ distV = 2`. -/
theorem certification_fails_without_lookahead :
    ∃ t : ℕ, ∃ vtx : Fin 3, vtx ∈ (cexRun.σ t).U ∧
      (cexRun.σ t).d vtx ≠ distV cw (0 : Fin 3) vtx :=
  ⟨5, 2, by decide, fun heq =>
    (by norm_num : ¬((5 : ℝ≥0∞) ≤ 2)) (by
      have h5 : (cexRun.σ 5).d (2 : Fin 3) = 5 := cexdB_two
      have h6 : distV cw (0 : Fin 3) 2 = 5 := heq.symm.trans h5
      rw [← h6]
      exact cex_distV_le)⟩

/-- The counterexample run violates the lookahead box at precisely the fatal settle
(step 4): the pending push `(a,v) = (1,2)` has potential `d a + w a v = 1 + 1 = 2`
below the boundary `B = 5`.  The sound engine refuses that settle; together with
`certified_settled_final_async` this pins the lookahead box as the exact gap. -/
theorem cex_lookahead_violated : ¬ LookaheadBoxed cw cexRun := by
  intro hLB
  have h := hLB 4 ⟨2, by decide, by decide⟩ ((1, 2)) (by decide)
  have hcontra : (5 : ℝ≥0∞) ≤ 1 + 1 := by
    have hcalc : (cexSigma 4).B ≤ (cexSigma 4).d (1 : Fin 3) + cw 1 2 := h
    have hB : (cexSigma 4).B = (5 : ℝ≥0∞) := rfl
    have hd1 : (cexSigma 4).d (1 : Fin 3) = 1 := cexdB_one
    have hw : cw (1 : Fin 3) 2 = 1 := by simp [cw]
    rw [hB, hd1, hw] at hcalc
    exact hcalc
  exact (by norm_num : ¬((5 : ℝ≥0∞) ≤ 1 + 1)) hcontra

end Counterexample

/-! ## Non-vacuity of the sound engine -/

/-- A concrete SOUND run: settle the source at step 0 (always legal from boundary
`⊤` and pending set `∅` — the lookahead box is vacuous there), then echo-sweep at
`s` forever (an idempotent union).  The `⊤` initial boundary again forces the first
settlement to be the source: while `s` sits unsettled with `d s = 0`, the frontier
box `⊤ ≤ ⨅ frontier dInit` fails for every other vertex. -/
def trivialAsyncSigma (w : V → V → ℝ≥0∞) (s : V) : ℕ → AsyncState V
  | 0 => { d := dInit s, U := ∅, B := ⊤, P := ∅ }
  | _t + 1 =>
      { d := dInit s, U := {s}, B := ⊤, P := Finset.image (fun x => (s, x)) Finset.univ }

def trivialAsyncRun (w : V → V → ℝ≥0∞) (s : V) : AsyncRun w s where
  σ := trivialAsyncSigma w s
  init := rfl
  legal := by
    intro t
    rcases t with _ | t
    · -- step 0: settle the source
      refine Or.inr (Or.inr ⟨s, ?_, rfl, rfl, ?_, ?_, ?_⟩)
      · simp [trivialAsyncSigma]
      · have hd0 : dInit s s = 0 := by simp [dInit]
        show dInit s s ≤ (⊤ : ℝ≥0∞)
        rw [hd0]
        exact le_top
      · show (⊤ : ℝ≥0∞) ≤ ⨅ u ∈ Finset.univ \ insert s (∅ : Finset V), dInit s u
        refine le_iInf fun u => le_iInf fun hu => ?_
        have hne : u ≠ s := by
          have hv := (Finset.mem_sdiff.mp hu).2
          intro heq
          exact hv (by rw [heq]; exact Finset.mem_insert.mpr (Or.inl rfl))
        have : dInit s u = ⊤ := by simp [dInit, hne]
        rw [this]
      · simp [trivialAsyncSigma]
    · -- steps t+1: echo-sweep at the source (idempotent union)
      refine Or.inr (Or.inl ⟨s, ?_, rfl, rfl, rfl, ?_⟩)
      · simp [trivialAsyncSigma]
      · apply Finset.ext
        intro q
        simp [trivialAsyncSigma]

/-- The trivial run respects the lookahead box: at step 0 the pending set is empty
(the box is vacuous), and at later steps no settlement happens (`U = {s}` is
constant), so the box premise never fires. -/
theorem trivialAsyncRun_lookahead (w : V → V → ℝ≥0∞) (s : V) :
    LookaheadBoxed w (trivialAsyncRun w s) := by
  intro t hprem p hp
  rcases t with _ | t
  · have hp' : p ∈ (∅ : Finset (V × V)) := hp
    simp at hp'
  · rcases hprem with ⟨v, hv, hU⟩
    have hself : v ∈ insert v ({s} : Finset V) := Finset.mem_insert.mpr (Or.inl rfl)
    have hU' : insert v ({s} : Finset V) = {s} := hU.symm
    have hvs : v = s := Finset.mem_singleton.mp (hU' ▸ hself)
    exact (hv (by rw [hvs]; exact Finset.mem_singleton.mpr rfl)).elim

/-! ## Healing without lookahead: convergence under edge fairness

The uncapped-engine story: settlement may be premature (the counterexample above),
but the VALUE dynamics still converge to `distV` if pushes keep flowing.  Fairness
must cover exactly this: every edge `(u,x)` is relaxed cofinally often
(`RelaxesEdge` below).  In this model that presupposes every vertex settles (or
echo-sweeps) cofinally often, since only settled sources are ever enqueued — the
run in the counterexample section, e.g., stalls forever with `d v = 5` because
after time 5 nothing re-relaxes `(a,v)` into effect... it IS enqueued (echo at `v`
only re-adds `(v,·)`); what never happens again is an echo at `a`, and `a`'s push
`(a,v)` sits pending-but-relevant: the run's tail deliberately echoes at the wrong
vertex.  A run that echo-sweeps every settled vertex cofinally often and applies
every pending push promptly satisfies `hfair` and heals. -/

/-- Step `t` RELAXES edge `e`: the push was pending, and the step lowered `d e.2`
to at most the current potential `d e.1 + w e.1 e.2` (immediate from the `apply`
branch of `BlindStep`). -/
def RelaxesEdge (w : V → V → ℝ≥0∞) (pre post : AsyncState V) (e : V × V) : Prop :=
  e ∈ pre.P ∧ post.d e.2 ≤ pre.d e.1 + w e.1 e.2

namespace AsyncRun

variable {w : V → V → ℝ≥0∞} {s : V} (run : AsyncRun w s)

/-- **HEALING THEOREM.**  No lookahead box, no certification, settled vertices
never revisited: if the value vector stabilizes (`hstable`) and every edge is
relaxed cofinally often (`hfair`), the stable vector IS `distV`.  The settled set
`U` plays no role in the value dynamics — this is the pillar-(ii) characterization
composing with the pending-push dynamics: the stable vector is edge-relaxed
everywhere, hence post-fixed for `T_BF`, hence `≤ distV` (`le_distV_of_le_T_BF`);
invariant 1 (`distV_le_d`) gives `distV ≤` it. -/
theorem healing_of_stable_and_edgeFair
    (hstable : ∃ N, ∀ n ≥ N, (run.σ n).d = (run.σ N).d)
    (hfair : ∀ (e : V × V) (N : ℕ), ∃ n, N ≤ n ∧ RelaxesEdge w (run.σ n) (run.σ (n + 1)) e) :
    ∃ N, ∀ n ≥ N, (run.σ n).d = distV w s := by
  obtain ⟨N, hN⟩ := hstable
  refine ⟨N, fun n hn => ?_⟩
  have hd : (run.σ n).d = (run.σ N).d := hN n hn
  rw [hd]
  refine le_antisymm ?_ (run.distV_le_d N)
  apply le_distV_of_le_T_BF
  intro x
  by_cases hxs : x = s
  · subst x
    have h0 : (run.σ N).d s = 0 := run.d_s N
    have hT : T_BF w s (run.σ N).d s = 0 := by simp [T_BF_apply]
    rw [h0, hT]
  · rw [T_BF_apply_of_ne hxs]
    refine le_iInf fun u => ?_
    obtain ⟨n, hnN, hrel⟩ := hfair (u, x) N
    have h1 : (run.σ n).d = (run.σ N).d := hN n hnN
    have h2 : (run.σ (n + 1)).d = (run.σ N).d := hN (n + 1) (by omega)
    have h3 : (run.σ (n + 1)).d x ≤ (run.σ n).d u + w u x := hrel.2
    rw [h1, h2] at h3
    exact h3

/-- Pillar (i)'s discreteness supplies the stability hypothesis: antitone +
per-component finite range ⇒ eventually constant (`exists_eventuallyConstant_of_antitone`,
promoted uniformly by `Fintype` exactly as in `iterate_eventuallyConstant`).

HONEST SEAM: pillar (ii)'s finite value universe (`iterate_range_finite`) is proved
for full `T_BF` iterates, where the prefix-tightness squeeze applies to the infimal
proposal.  Porting it to edge-level `applyPush` dynamics is not free — a single-edge
proposal `d u + w u x` can be the cost of a NON-simple walk, and the tightness
induction does not transfer verbatim — so range-finiteness is a hypothesis here,
not a consequence. -/
theorem healing_of_finiteRange_edgeFair
    (hrange : ∀ v, (Set.range fun n => (run.σ n).d v).Finite)
    (hfair : ∀ (e : V × V) (N : ℕ), ∃ n, N ≤ n ∧ RelaxesEdge w (run.σ n) (run.σ (n + 1)) e) :
    ∃ N, ∀ n ≥ N, (run.σ n).d = distV w s := by
  classical
  choose Nv hNv using fun v =>
    exists_eventuallyConstant_of_antitone (fun n => (run.σ n).d v)
      (fun a b hab => run.d_antitone hab v) (hrange v)
  refine run.healing_of_stable_and_edgeFair
      ⟨Finset.sup Finset.univ Nv, fun n hn => ?_⟩ hfair
  funext v
  have h1 : (run.σ n).d v = (run.σ (Nv v)).d v :=
    hNv v n ((Finset.le_sup (Finset.mem_univ v)).trans hn)
  have h2 : (run.σ (Finset.sup Finset.univ Nv)).d v = (run.σ (Nv v)).d v :=
    hNv v _ (Finset.le_sup (Finset.mem_univ v))
  rw [h1, h2]

end AsyncRun

end RelaxLFP

/-! ## Status ledger (honest)

Pillar (iv) — proved, ZERO sorries:

* the async engine (`applyPush`, `AsyncState` with pending-push set `P`,
  `BlindStep`, `AsyncRun`) — settle does NOT fire the push atomically; it enqueues;
* **the exact soundness condition** `LookaheadBoxed` — the null-message/lookahead
  box `B ≤ ⨅ (u,x) ∈ P, d u + w u x` checked at settle time over the pre-settle
  pending set (boundedlag NOTE: `certified := below GVT` in event time);
* **POSITIVE**: `AsyncRun.certified_settled_final_async` — under the lookahead box,
  settlement is final; the pillar-(iii) walk induction extends through the async
  edge-accounting invariant `settled_edges_accounted` (settled out-edges are
  relaxed-or-pending; the pending arm is where the box is consumed).  Maintenance
  of the accounting invariant needs certification itself (a push application can
  lower a settled TARGET's value only if the target was uncertified) — hence
  simultaneous induction, hence the theorem genuinely requires soundness;
* **NEGATIVE**: `certification_fails_without_lookahead` — a concrete blind-legal run
  on `s →(1) a →(1) v`, `s →(5) v` settles `v` at `5 ≠ distV v = 2`;
  `cex_lookahead_violated` — the run violates the box at precisely the fatal settle
  (pending `(a,v)`, potential `2 < 5 = B`).  The lookahead clause is the exact gap;
* **FROZEN LOCK / SKIP-RE-EXPANSION**: `frozen_lock_async`, `settled_push_noop`
  (fastsweep NOTE: under sound certification, echo sweeps may skip certified
  vertices — pushes aimed at them are provable no-ops);
* **HEALING**: `healing_of_stable_and_edgeFair` — WITHOUT lookahead, stability +
  cofinal edge-relaxation ⇒ `d` converges to `distV` (composes pillar (ii)'s
  post-fixed-point characterization with invariant 1); `healing_of_finiteRange_edgeFair`
  — pillar (i)'s discreteness lemma supplies stability from finite per-component
  value ranges.  Honest seam: the finite-range HYPOTHESIS is not discharged —
  pillar (ii)'s simple-walk value universe does not port verbatim to single-edge
  proposals (documented at the theorem);
* `trivialAsyncRun` + `trivialAsyncRun_lookahead` — the sound engine class is
  inhabited (non-vacuity), and the `⊤` start boundary forces the first settlement
  to be the source.

Model honesty notes: (1) pushes carry no values — applying `(u,x)` re-reads current
`d u` (echo-sweep semantics); value-carrying messages would need a staleness
side-condition instead. (2) `hfair` quantifies over ALL edges including
self-loops/non-edges; their pending pushes have potential `⊤` and are harmless, but
the enqueue discipline means only settled sources ever enter `P` — so `hfair`
presupposes every vertex eventually settles (stated in the section docstring).
(3) The blind engine's `settled_edges_accounted` analogue is FALSE (settled values
can drop — that is precisely the healing regime), so the edge-accounting invariant
is stated only under `LookaheadBoxed`.
-/
