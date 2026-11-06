import GKK.C0
namespace GKK
variable {A D : Type} [DecidableEq A] [DecidableEq D]

/-- The properties proved, conjoined. -/
def Props (s : St A D) : Prop :=
  (∀ (x0 : A), s.identity x0 ≤ 1) ∧
  (∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0)

/-- Every reachable state satisfies every property. -/
theorem reach_props {s : St A D} (h : Reach s) : Props s := by
  induction h with
  | init => exact ⟨p0_init, p1_init, p2_init⟩
  | step _ hs ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    exact ⟨p0_step _ _ h0 hs, p1_step _ _ h0 h1 h2 hs, p2_step _ _ h0 h1 h2 hs⟩

end GKK
