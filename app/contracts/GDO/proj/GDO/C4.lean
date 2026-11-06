import GDO.Model
namespace GDO
variable {A D : Type} [DecidableEq A] [DecidableEq D]

/-- friend(X, Y)  ⇒  not friend(X, X) -/
theorem p12_init : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 > 0 → (init : St A D).friend x0 x0 = 0 := by
  simp [init]

theorem p12_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 > 0 → s'.friend x0 x0 = 0 := by
  cases h <;> grind

/-- friend(X, Y)  ⇒  friend(Y, X) -/
theorem p13_init : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 > 0 → (init : St A D).friend x1 x0 > 0 := by
  simp [init]

theorem p13_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 > 0 → s'.friend x1 x0 > 0 := by
  cases h <;> grind

/-- friend(X, Y)  ⇒  not friend(Y, Y) -/
theorem p14_init : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 > 0 → (init : St A D).friend x1 x1 = 0 := by
  simp [init]

theorem p14_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 > 0 → s'.friend x1 x1 = 0 := by
  cases h <;> grind

end GDO
