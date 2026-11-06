import GB.Model
namespace GB
variable {A D : Type} [DecidableEq A] [DecidableEq D]

/-- identity(X) is never held twice -/
theorem p0_init : ∀ (x0 : A), (init : St A D).identity x0 ≤ 1 := by
  simp [init]

theorem p0_step (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (h : Step s s') :
    ∀ (x0 : A), s'.identity x0 ≤ 1 := by
  cases h <;> grind

end GB
