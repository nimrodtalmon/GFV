import GB.C0
import GB.C1
import GB.C2
import GB.C3
import GB.C4
import GB.C5
namespace GB
variable {A D : Type} [DecidableEq A] [DecidableEq D]

/-- The properties proved, conjoined. -/
def Props (s : St A D) : Prop :=
  (∀ (x0 : A), s.identity x0 ≤ 1) ∧
  (∀ (x0 : A), s.dated x0 ≤ 1) ∧
  (∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) ∧
  (∀ (x0 : A) (x1 : Nat), s.date x0 x1 > 0 → s.identity x0 > 0) ∧
  (∀ (x0 : A) (x1 : Nat), s.date x0 x1 > 0 → s.dated x0 > 0) ∧
  (∀ (x0 : A) (x1 : A) (x2 : Nat), s.bond x0 x1 x2 > 0 → s.identity x0 > 0) ∧
  (∀ (x0 : A) (x1 : A) (x2 : Nat), s.bond x0 x1 x2 > 0 → s.identity x1 > 0) ∧
  (∀ (x0 : A) (x1 : A) (x2 : Nat), s.bond x0 x1 x2 > 0 → s.dated x1 > 0) ∧
  (∀ (x0 : A), s.dated x0 > 0 → s.identity x0 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) ∧
  (∀ (x0 : A) (x1 : A) (x2 : Nat), s.bond x0 x1 x2 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0)

/-- Every reachable state satisfies every property. -/
theorem reach_props {s : St A D} (h : Reach s) : Props s := by
  induction h with
  | init => exact ⟨p0_init, p3_init, p4_init, p5_init, p6_init, p7_init, p8_init, p9_init, p10_init, p11_init, p12_init, p13_init, p14_init, p15_init⟩
  | step _ hs ih =>
    obtain ⟨h0, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := ih
    exact ⟨p0_step _ _ h0 hs, p3_step _ _ h0 h3 h8 h9 h13 hs, p4_step _ _ h0 h4 h5 h6 h7 h8 h10 h11 h14 h15 hs, p5_step _ _ h0 h4 h5 h6 h7 h8 h10 h11 h14 h15 hs, p6_step _ _ h0 h4 h5 h6 h7 h8 h10 h11 h14 h15 hs, p7_step _ _ h0 h4 h5 h6 h7 h8 h10 h11 h14 h15 hs, p8_step _ _ h0 h3 h8 h9 h13 hs, p9_step _ _ h0 h3 h8 h9 h13 hs, p10_step _ _ h0 h4 h5 h6 h7 h8 h10 h11 h14 h15 hs, p11_step _ _ h0 h4 h5 h6 h7 h8 h10 h11 h14 h15 hs, p12_step _ _ h0 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hs, p13_step _ _ h0 h3 h8 h9 h13 hs, p14_step _ _ h0 h4 h5 h6 h7 h8 h10 h11 h14 h15 hs, p15_step _ _ h0 h4 h5 h6 h7 h8 h10 h11 h14 h15 hs⟩

end GB
