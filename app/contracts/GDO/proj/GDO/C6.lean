import GDO.Model
namespace GDO
variable {A D : Type} [DecidableEq A] [DecidableEq D]

/-- points_to(X, Y)  ⇒  not friend(X, X) -/
theorem p18_init : ∀ (x0 : A) (x1 : A), (init : St A D).points_to x0 x1 > 0 → (init : St A D).friend x0 x0 = 0 := by
  simp [init]

theorem p18_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.points_to x0 x1 > 0 → s'.friend x0 x0 = 0 := by
  cases h <;> grind

/-- points_to(X, Y)  ⇒  not friend(Y, Y) -/
theorem p19_init : ∀ (x0 : A) (x1 : A), (init : St A D).points_to x0 x1 > 0 → (init : St A D).friend x1 x1 = 0 := by
  simp [init]

theorem p19_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.points_to x0 x1 > 0 → s'.friend x1 x1 = 0 := by
  cases h <;> grind

end GDO
