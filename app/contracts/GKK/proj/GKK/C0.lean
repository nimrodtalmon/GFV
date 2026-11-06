import GKK.Model
namespace GKK
variable {A D : Type} [DecidableEq A] [DecidableEq D]

/-- identity(X) is never held twice -/
theorem p0_init : ∀ (x0 : A), (init : St A D).identity x0 ≤ 1 := by
  simp [init]

theorem p0_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (h : Step s s') :
    ∀ (x0 : A), s'.identity x0 ≤ 1 := by
  cases h <;> grind

/-- knows(X, Y)  ⇒  identity(X) -/
theorem p1_init : ∀ (x0 : A) (x1 : A), (init : St A D).knows x0 x1 > 0 → (init : St A D).identity x0 > 0 := by
  simp [init]

theorem p1_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H2 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.knows x0 x1 > 0 → s'.identity x0 > 0 := by
  cases h <;> grind

/-- knows(X, Y)  ⇒  identity(Y) -/
theorem p2_init : ∀ (x0 : A) (x1 : A), (init : St A D).knows x0 x1 > 0 → (init : St A D).identity x1 > 0 := by
  simp [init]

theorem p2_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H2 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.knows x0 x1 > 0 → s'.identity x1 > 0 := by
  cases h <;> grind

end GKK
