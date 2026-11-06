import GDO.C0
import GDO.C1
import GDO.C2
import GDO.C3
import GDO.C4
import GDO.C5
import GDO.C6
namespace GDO
variable {A D : Type} [DecidableEq A] [DecidableEq D]

/-- The properties proved, conjoined. -/
def Props (s : St A D) : Prop :=
  (∀ (x0 : A), s.identity x0 ≤ 1) ∧
  (∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) ∧
  (∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) ∧
  (∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) ∧
  (∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) ∧
  (∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) ∧
  (∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) ∧
  (∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) ∧
  (∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) ∧
  (∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0)

/-- Every reachable state satisfies every property. -/
theorem reach_props {s : St A D} (h : Reach s) : Props s := by
  induction h with
  | init => exact ⟨p0_init, p1_init, p2_init, p3_init, p4_init, p5_init, p6_init, p7_init, p8_init, p9_init, p10_init, p11_init, p12_init, p13_init, p14_init, p15_init, p16_init, p17_init, p18_init, p19_init⟩
  | step _ hs ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := ih
    exact ⟨p0_step _ _ h0 hs, p1_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p2_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p3_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p4_step _ _ h0 h4 h5 hs, p5_step _ _ h0 h4 h5 hs, p6_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p7_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p8_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p9_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p10_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p11_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p12_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p13_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p14_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs, p15_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, p16_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, p17_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, p18_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, p19_step _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs⟩

end GDO
