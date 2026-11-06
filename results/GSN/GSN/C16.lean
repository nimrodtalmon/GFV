import GSN.Model
namespace GSN
variable {A D : Type} [DecidableEq A] [DecidableEq D]

/-- received(X, d, Y)  ⇒  identity(X) -/
theorem p48_init : ∀ (x0 : A) (x1 : D) (x2 : A), (init : St A D).received x0 x1 x2 > 0 → (init : St A D).identity x0 > 0 := by
  simp [init]

theorem p48_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H5 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → x0 ≠ x2) (H12 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H17 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H21 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H22 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H23 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H48 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.identity x0 > 0) (H49 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.identity x2 > 0) (H52 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.friend x0 x0 = 0) (H53 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.friend x2 x2 = 0) (H54 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.received x0 x1 x0 = 0) (H55 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.received x2 x1 x2 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : D) (x2 : A), s'.received x0 x1 x2 > 0 → s'.identity x0 > 0 := by
  cases h <;> grind

/-- received(X, d, Y)  ⇒  identity(Y) -/
theorem p49_init : ∀ (x0 : A) (x1 : D) (x2 : A), (init : St A D).received x0 x1 x2 > 0 → (init : St A D).identity x2 > 0 := by
  simp [init]

theorem p49_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H5 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → x0 ≠ x2) (H12 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H17 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H21 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H22 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H23 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H48 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.identity x0 > 0) (H49 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.identity x2 > 0) (H52 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.friend x0 x0 = 0) (H53 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.friend x2 x2 = 0) (H54 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.received x0 x1 x0 = 0) (H55 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.received x2 x1 x2 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : D) (x2 : A), s'.received x0 x1 x2 > 0 → s'.identity x2 > 0 := by
  cases h <;> grind

/-- received(X, d, Y)  ⇒  knows(X, Y) -/
theorem p50_init : ∀ (x0 : A) (x1 : D) (x2 : A), (init : St A D).received x0 x1 x2 > 0 → (init : St A D).knows x0 x2 > 0 := by
  simp [init]

theorem p50_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H5 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → x0 ≠ x2) (H12 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H15 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H16 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H17 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H19 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H20 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H21 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H22 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H23 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H48 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.identity x0 > 0) (H49 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.identity x2 > 0) (H50 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.knows x0 x2 > 0) (H51 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.knows x2 x0 > 0) (H52 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.friend x0 x0 = 0) (H53 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.friend x2 x2 = 0) (H54 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.received x0 x1 x0 = 0) (H55 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.received x2 x1 x2 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : D) (x2 : A), s'.received x0 x1 x2 > 0 → s'.knows x0 x2 > 0 := by
  cases h <;> grind

end GSN
