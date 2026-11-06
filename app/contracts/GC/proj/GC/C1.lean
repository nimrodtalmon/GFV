import GC.Model
namespace GC
variable {A D : Type} [DecidableEq A] [DecidableEq D]

/-- coin(X, Y)  ⇒  identity(X) -/
theorem p3_init : ∀ (x0 : A) (x1 : A), (init : St A D).coin x0 x1 > 0 → (init : St A D).identity x0 > 0 := by
  simp [init]

theorem p3_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H2 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H3 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) (H4 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.coin x0 x1 > 0 → s'.identity x0 > 0 := by
  cases h <;> grind

/-- coin(X, Y)  ⇒  identity(Y) -/
theorem p4_init : ∀ (x0 : A) (x1 : A), (init : St A D).coin x0 x1 > 0 → (init : St A D).identity x1 > 0 := by
  simp [init]

theorem p4_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H2 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H3 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) (H4 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.coin x0 x1 > 0 → s'.identity x1 > 0 := by
  cases h <;> grind

/-- coin(X, Y) and X ≠ Y  ⇒  knows(X, Y) -/
theorem p5_init : ∀ (x0 : A) (x1 : A), (init : St A D).coin x0 x1 > 0 → x0 ≠ x1 → (init : St A D).knows x0 x1 > 0 := by
  simp [init]

theorem p5_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H2 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H3 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) (H4 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.coin x0 x1 > 0 → x0 ≠ x1 → s'.knows x0 x1 > 0 := by
  cases h <;> grind

end GC
