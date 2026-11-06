import GB.Model
namespace GB
variable {A D : Type} [DecidableEq A] [DecidableEq D]

/-- dated(X) is never held twice -/
theorem p3_init : ∀ (x0 : A), (init : St A D).dated x0 ≤ 1 := by
  simp [init]

theorem p3_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H3 : ∀ (x0 : A), s.dated x0 ≤ 1) (H8 : ∀ (x0 : A) (x1 : Nat), s.date x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : Nat), s.date x0 x1 > 0 → s.dated x0 > 0) (H13 : ∀ (x0 : A), s.dated x0 > 0 → s.identity x0 > 0) (h : Step s s') :
    ∀ (x0 : A), s'.dated x0 ≤ 1 := by
  cases h <;> grind

/-- knows(X, Y)  ⇒  identity(X) -/
theorem p4_init : ∀ (x0 : A) (x1 : A), (init : St A D).knows x0 x1 > 0 → (init : St A D).identity x0 > 0 := by
  simp [init]

theorem p4_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) (H7 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) (H8 : ∀ (x0 : A) (x1 : Nat), s.date x0 x1 > 0 → s.identity x0 > 0) (H10 : ∀ (x0 : A) (x1 : A) (x2 : Nat), s.bond x0 x1 x2 > 0 → s.identity x0 > 0) (H11 : ∀ (x0 : A) (x1 : A) (x2 : Nat), s.bond x0 x1 x2 > 0 → s.identity x1 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (H15 : ∀ (x0 : A) (x1 : A) (x2 : Nat), s.bond x0 x1 x2 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.knows x0 x1 > 0 → s'.identity x0 > 0 := by
  cases h <;> grind

/-- knows(X, Y)  ⇒  identity(Y) -/
theorem p5_init : ∀ (x0 : A) (x1 : A), (init : St A D).knows x0 x1 > 0 → (init : St A D).identity x1 > 0 := by
  simp [init]

theorem p5_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) (H7 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) (H8 : ∀ (x0 : A) (x1 : Nat), s.date x0 x1 > 0 → s.identity x0 > 0) (H10 : ∀ (x0 : A) (x1 : A) (x2 : Nat), s.bond x0 x1 x2 > 0 → s.identity x0 > 0) (H11 : ∀ (x0 : A) (x1 : A) (x2 : Nat), s.bond x0 x1 x2 > 0 → s.identity x1 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (H15 : ∀ (x0 : A) (x1 : A) (x2 : Nat), s.bond x0 x1 x2 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.knows x0 x1 > 0 → s'.identity x1 > 0 := by
  cases h <;> grind

end GB
