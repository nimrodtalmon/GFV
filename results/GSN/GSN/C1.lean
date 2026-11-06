import GSN.Model
namespace GSN
variable {A D : Type} [DecidableEq A] [DecidableEq D]

/-- member(X, n) is never held twice -/
theorem p4_init : ∀ (x0 : A) (x1 : (A × D)), (init : St A D).member x0 x1 ≤ 1 := by
  simp [init]

theorem p4_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H4 : ∀ (x0 : A) (x1 : (A × D)), s.member x0 x1 ≤ 1) (H6 : ∀ (x0 : A) (x1 : D), s.closed x0 x1 ≤ 1) (H12 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H17 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H21 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H22 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H23 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H24 : ∀ (x0 : A) (x1 : A) (x2 : D), s.listed x0 x1 x2 > 0 → s.identity x0 > 0) (H25 : ∀ (x0 : A) (x1 : A) (x2 : D), s.listed x0 x1 x2 > 0 → s.identity x1 > 0) (H26 : ∀ (x0 : A) (x1 : A) (x2 : D), s.listed x0 x1 x2 > 0 → s.friend x0 x0 = 0) (H27 : ∀ (x0 : A) (x1 : A) (x2 : D), s.listed x0 x1 x2 > 0 → s.friend x1 x1 = 0) (H34 : ∀ (x0 : A) (x1 : (A × D)), s.member x0 x1 > 0 → s.identity x0 > 0) (H35 : ∀ (x0 : A) (x1 : (A × D)), s.member x0 x1 > 0 → s.identity x1.1 > 0) (H36 : ∀ (x0 : A) (x1 : (A × D)), s.member x0 x1 > 0 → s.friend x0 x0 = 0) (H37 : ∀ (x0 : A) (x1 : (A × D)), s.member x0 x1 > 0 → s.friend x1.1 x1.1 = 0) (H38 : ∀ (x0 : A) (x1 : (A × D)), s.member x0 x1 > 0 → s.listed x1.1 x0 x1.2 > 0) (H39 : ∀ (x0 : A) (x1 : (A × D)), s.member x0 x1 > 0 → s.listed x1.1 x1.1 x1.2 > 0) (H40 : ∀ (x0 : A) (x1 : (A × D)), s.member x0 x1 > 0 → s.member x1.1 x1 > 0) (H43 : ∀ (x0 : A) (x1 : (A × D)), s.member x0 x1 > 0 → s.closed x1.1 x1.2 = 0) (H60 : ∀ (x0 : A) (x1 : D), s.closed x0 x1 > 0 → s.identity x0 > 0) (H61 : ∀ (x0 : A) (x1 : D), s.closed x0 x1 > 0 → s.friend x0 x0 = 0) (H63 : ∀ (x0 : A) (x1 : D), s.closed x0 x1 > 0 → s.member x0 (x0, x1) = 0) (H137 : ∀ (x0 : A) (x1 : A) (x2 : D), s.listed x0 x1 x2 > 0 → x0 ≠ x1 → s.friend x0 x1 > 0) (H138 : ∀ (x0 : A) (x1 : A) (x2 : D), s.listed x0 x1 x2 > 0 → x0 ≠ x1 → s.friend x1 x0 > 0) (H141 : ∀ (x0 : A) (x1 : (A × D)), s.member x0 x1 > 0 → x0 ≠ x1.1 → s.friend x0 x1.1 > 0) (H142 : ∀ (x0 : A) (x1 : (A × D)), s.member x0 x1 > 0 → x0 ≠ x1.1 → s.friend x1.1 x0 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : (A × D)), s'.member x0 x1 ≤ 1 := by
  cases h <;> grind

/-- received(X, d, Y)  ⇒  X ≠ Y -/
theorem p5_init : ∀ (x0 : A) (x1 : D) (x2 : A), (init : St A D).received x0 x1 x2 > 0 → x0 ≠ x2 := by
  simp [init]

theorem p5_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H5 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → x0 ≠ x2) (H12 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H17 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H21 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H22 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H23 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H48 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.identity x0 > 0) (H49 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.identity x2 > 0) (H52 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.friend x0 x0 = 0) (H53 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.friend x2 x2 = 0) (H54 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.received x0 x1 x0 = 0) (H55 : ∀ (x0 : A) (x1 : D) (x2 : A), s.received x0 x1 x2 > 0 → s.received x2 x1 x2 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : D) (x2 : A), s'.received x0 x1 x2 > 0 → x0 ≠ x2 := by
  cases h <;> grind

end GSN
