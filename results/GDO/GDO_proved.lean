namespace GDO

structure St (A D : Type) where
  identity : A → Nat
  knows : A → A → Nat
  friend : A → A → Nat
  points_to : A → A → Nat

variable {A D : Type} [DecidableEq A] [DecidableEq D]

def init : St A D := ⟨fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

inductive Step : St A D → St A D → Prop
  /-- establish; guarded by Alice -/
  | establish (s : St A D) (r_Alice : A) (h0 : s.identity r_Alice = 0) :
      Step s { s with identity := fun p => s.identity p + ((if (p = r_Alice) then 1 else 0)) }
  /-- acquaint; guarded by Alice, Bob -/
  | acquaint (s : St A D) (r_Alice : A) (r_Bob : A) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.identity r_Bob ≥ 1) :
      Step s { s with knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = r_Bob) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = r_Alice) then 1 else 0)) }
  /-- introduce; guarded by Alice, Bob -/
  | introduce (s : St A D) (r_Alice : A) (r_Bob : A) (v_c : A) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.knows r_Alice r_Bob ≥ 1) (h3 : s.knows r_Alice v_c ≥ 1) (h4 : s.identity r_Bob ≥ 1) (h5 : s.knows r_Bob r_Alice ≥ 1) :
      Step s { s with knows := fun p x1 => s.knows p x1 + ((if (p = r_Bob) ∧ (x1 = v_c) then 1 else 0)) }
  /-- befriend; guarded by Alice, Bob -/
  | befriend (s : St A D) (r_Alice : A) (r_Bob : A) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.knows r_Alice r_Bob ≥ 1) (h3 : s.friend r_Alice r_Bob = 0) (h4 : s.identity r_Bob ≥ 1) (h5 : s.knows r_Bob r_Alice ≥ 1) (h6 : s.friend r_Bob r_Alice = 0) :
      Step s { s with friend := fun p x1 => s.friend p x1 + ((if (p = r_Alice) ∧ (x1 = r_Bob) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = r_Alice) then 1 else 0)) }
  /-- unfriend; guarded by Alice -/
  | unfriend (s : St A D) (r_Alice : A) (r_Bob : A) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.friend r_Alice r_Bob ≥ 1) (h3 : s.identity r_Bob ≥ 1) (h4 : s.friend r_Bob r_Alice ≥ 1) :
      Step s { s with friend := fun p x1 => (s.friend p x1 - ((if (p = r_Alice) ∧ (x1 = r_Bob) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = r_Alice) then 1 else 0))) }
  /-- point_friend; guarded by Alice -/
  | point_friend (s : St A D) (r_Alice : A) (r_Bob : A) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.friend r_Alice r_Bob ≥ 1) (h3 : s.points_to r_Alice r_Bob = 0) (h4 : s.identity r_Bob ≥ 1) :
      Step s { s with points_to := fun p x1 => s.points_to p x1 + ((if (p = r_Alice) ∧ (x1 = r_Bob) then 1 else 0)) }
  /-- point_transitive; guarded by Alice -/
  | point_transitive (s : St A D) (r_Alice : A) (r_Bob : A) (v_c : A) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.knows r_Alice v_c ≥ 1) (h3 : s.points_to r_Alice r_Bob ≥ 1) (h4 : s.identity r_Bob ≥ 1) (h5 : s.points_to r_Bob v_c ≥ 1) :
      Step s { s with points_to := fun p x1 => s.points_to p x1 + ((if (p = r_Alice) ∧ (x1 = v_c) then 1 else 0)) }
  /-- unpoint; guarded by Alice -/
  | unpoint (s : St A D) (r_Alice : A) (r_Bob : A) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.points_to r_Alice r_Bob ≥ 1) (h3 : s.identity r_Bob ≥ 1) :
      Step s { s with points_to := fun p x1 => (s.points_to p x1 - ((if (p = r_Alice) ∧ (x1 = r_Bob) then 1 else 0))) }

inductive Reach : St A D → Prop
  | init : Reach init
  | step {s s' : St A D} : Reach s → Step s s' → Reach s'

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

/-- identity(X) is never held twice -/
theorem init_0 : ∀ (x0 : A), (init : St A D).identity x0 ≤ 1 := by
  simp [init]

theorem step_0 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A), s'.identity x0 ≤ 1 := by
  cases h <;> grind

/-- friend(X, Y) is never held twice -/
theorem init_1 : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 ≤ 1 := by
  simp [init]

theorem step_1 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 ≤ 1 := by
  cases h <;> grind

/-- friend(X, Y)  ⇒  X ≠ Y -/
theorem init_2 : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 > 0 → x0 ≠ x1 := by
  simp [init]

theorem step_2 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 > 0 → x0 ≠ x1 := by
  cases h <;> grind

/-- identity(X)  ⇒  not friend(X, X) -/
theorem init_3 : ∀ (x0 : A), (init : St A D).identity x0 > 0 → (init : St A D).friend x0 x0 = 0 := by
  simp [init]

theorem step_3 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A), s'.identity x0 > 0 → s'.friend x0 x0 = 0 := by
  cases h <;> grind

/-- knows(X, Y)  ⇒  identity(X) -/
theorem init_4 : ∀ (x0 : A) (x1 : A), (init : St A D).knows x0 x1 > 0 → (init : St A D).identity x0 > 0 := by
  simp [init]

theorem step_4 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.knows x0 x1 > 0 → s'.identity x0 > 0 := by
  cases h <;> grind

/-- knows(X, Y)  ⇒  identity(Y) -/
theorem init_5 : ∀ (x0 : A) (x1 : A), (init : St A D).knows x0 x1 > 0 → (init : St A D).identity x1 > 0 := by
  simp [init]

theorem step_5 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.knows x0 x1 > 0 → s'.identity x1 > 0 := by
  cases h <;> grind

/-- knows(X, Y)  ⇒  not friend(X, X) -/
theorem init_6 : ∀ (x0 : A) (x1 : A), (init : St A D).knows x0 x1 > 0 → (init : St A D).friend x0 x0 = 0 := by
  simp [init]

theorem step_6 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.knows x0 x1 > 0 → s'.friend x0 x0 = 0 := by
  cases h <;> grind

/-- knows(X, Y)  ⇒  not friend(Y, Y) -/
theorem init_7 : ∀ (x0 : A) (x1 : A), (init : St A D).knows x0 x1 > 0 → (init : St A D).friend x1 x1 = 0 := by
  simp [init]

theorem step_7 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.knows x0 x1 > 0 → s'.friend x1 x1 = 0 := by
  cases h <;> grind

/-- friend(X, Y)  ⇒  identity(X) -/
theorem init_8 : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 > 0 → (init : St A D).identity x0 > 0 := by
  simp [init]

theorem step_8 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 > 0 → s'.identity x0 > 0 := by
  cases h <;> grind

/-- friend(X, Y)  ⇒  identity(Y) -/
theorem init_9 : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 > 0 → (init : St A D).identity x1 > 0 := by
  simp [init]

theorem step_9 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 > 0 → s'.identity x1 > 0 := by
  cases h <;> grind

/-- friend(X, Y)  ⇒  knows(X, Y) -/
theorem init_10 : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 > 0 → (init : St A D).knows x0 x1 > 0 := by
  simp [init]

theorem step_10 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 > 0 → s'.knows x0 x1 > 0 := by
  cases h <;> grind

/-- friend(X, Y)  ⇒  knows(Y, X) -/
theorem init_11 : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 > 0 → (init : St A D).knows x1 x0 > 0 := by
  simp [init]

theorem step_11 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 > 0 → s'.knows x1 x0 > 0 := by
  cases h <;> grind

/-- friend(X, Y)  ⇒  not friend(X, X) -/
theorem init_12 : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 > 0 → (init : St A D).friend x0 x0 = 0 := by
  simp [init]

theorem step_12 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 > 0 → s'.friend x0 x0 = 0 := by
  cases h <;> grind

/-- friend(X, Y)  ⇒  friend(Y, X) -/
theorem init_13 : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 > 0 → (init : St A D).friend x1 x0 > 0 := by
  simp [init]

theorem step_13 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 > 0 → s'.friend x1 x0 > 0 := by
  cases h <;> grind

/-- friend(X, Y)  ⇒  not friend(Y, Y) -/
theorem init_14 : ∀ (x0 : A) (x1 : A), (init : St A D).friend x0 x1 > 0 → (init : St A D).friend x1 x1 = 0 := by
  simp [init]

theorem step_14 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.friend x0 x1 > 0 → s'.friend x1 x1 = 0 := by
  cases h <;> grind

/-- points_to(X, Y)  ⇒  identity(X) -/
theorem init_15 : ∀ (x0 : A) (x1 : A), (init : St A D).points_to x0 x1 > 0 → (init : St A D).identity x0 > 0 := by
  simp [init]

theorem step_15 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.points_to x0 x1 > 0 → s'.identity x0 > 0 := by
  cases h <;> grind

/-- points_to(X, Y)  ⇒  identity(Y) -/
theorem init_16 : ∀ (x0 : A) (x1 : A), (init : St A D).points_to x0 x1 > 0 → (init : St A D).identity x1 > 0 := by
  simp [init]

theorem step_16 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.points_to x0 x1 > 0 → s'.identity x1 > 0 := by
  cases h <;> grind

/-- points_to(X, Y)  ⇒  knows(X, Y) -/
theorem init_17 : ∀ (x0 : A) (x1 : A), (init : St A D).points_to x0 x1 > 0 → (init : St A D).knows x0 x1 > 0 := by
  simp [init]

theorem step_17 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.points_to x0 x1 > 0 → s'.knows x0 x1 > 0 := by
  cases h <;> grind

/-- points_to(X, Y)  ⇒  not friend(X, X) -/
theorem init_18 : ∀ (x0 : A) (x1 : A), (init : St A D).points_to x0 x1 > 0 → (init : St A D).friend x0 x0 = 0 := by
  simp [init]

theorem step_18 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.points_to x0 x1 > 0 → s'.friend x0 x0 = 0 := by
  cases h <;> grind

/-- points_to(X, Y)  ⇒  not friend(Y, Y) -/
theorem init_19 : ∀ (x0 : A) (x1 : A), (init : St A D).points_to x0 x1 > 0 → (init : St A D).friend x1 x1 = 0 := by
  simp [init]

theorem step_19 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 ≤ 1) (H2 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → x0 ≠ x1) (H3 : ∀ (x0 : A), s.identity x0 > 0 → s.friend x0 x0 = 0) (H4 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H6 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x0 x0 = 0) (H7 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.friend x1 x1 = 0) (H8 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x0 > 0) (H9 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.identity x1 > 0) (H10 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x0 x1 > 0) (H11 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.knows x1 x0 > 0) (H12 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x0 x0 = 0) (H13 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x0 > 0) (H14 : ∀ (x0 : A) (x1 : A), s.friend x0 x1 > 0 → s.friend x1 x1 = 0) (H15 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x0 > 0) (H16 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.identity x1 > 0) (H17 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.knows x0 x1 > 0) (H18 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x0 x0 = 0) (H19 : ∀ (x0 : A) (x1 : A), s.points_to x0 x1 > 0 → s.friend x1 x1 = 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.points_to x0 x1 > 0 → s'.friend x1 x1 = 0 := by
  cases h <;> grind

/-- Every reachable state satisfies every property. -/
theorem reach_props {s : St A D} (h : Reach s) : Props s := by
  induction h with
  | init => exact ⟨init_0, init_1, init_2, init_3, init_4, init_5, init_6, init_7, init_8, init_9, init_10, init_11, init_12, init_13, init_14, init_15, init_16, init_17, init_18, init_19⟩
  | step _ hs ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := ih
    exact ⟨step_0 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_1 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_2 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_3 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_4 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_5 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_6 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_7 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_8 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_9 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_10 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_11 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_12 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_13 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_14 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_15 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_16 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_17 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_18 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs, step_19 _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hs⟩

end GDO
