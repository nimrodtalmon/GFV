namespace GC

structure St (A D : Type) where
  identity : A → Nat
  knows : A → A → Nat
  coin : A → A → Nat

variable {A D : Type} [DecidableEq A] [DecidableEq D]

def init : St A D := ⟨fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩

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
  /-- mint; guarded by Alice -/
  | mint (s : St A D) (r_Alice : A) (v_k : Nat) (h0 : v_k ≥ 1) (h1 : s.identity r_Alice ≥ 1) :
      Step s { s with coin := fun p x1 => s.coin p x1 + ((if (p = r_Alice) ∧ (x1 = r_Alice) then v_k else 0)) }
  /-- swap; guarded by Alice, Bob -/
  | swap (s : St A D) (r_Alice : A) (r_Bob : A) (v_u : A) (v_v : A) (v_k : Nat) (v_k1 : Nat) (h0 : r_Alice ≠ r_Bob) (h1 : v_k ≥ 1) (h2 : v_k1 ≥ 1) (h3 : s.identity r_Alice ≥ 1) (h4 : s.knows r_Alice r_Bob ≥ 1) (h5 : s.coin r_Alice v_u ≥ v_k) (h6 : s.identity r_Bob ≥ 1) (h7 : s.knows r_Bob r_Alice ≥ 1) (h8 : s.coin r_Bob v_v ≥ v_k1) (h9 : ∀ p : A, p = r_Alice → p = r_Alice → ¬ ((v_v = v_u))) (h10 : ∀ p : A, p = r_Bob → p = r_Bob → ¬ ((v_u = v_v))) :
      Step s { s with coin := fun p x1 => (s.coin p x1 - ((if (p = r_Alice) ∧ (x1 = v_u) then v_k else 0) + (if (p = r_Bob) ∧ (x1 = v_v) then v_k1 else 0))) + ((if (p = r_Alice) ∧ (x1 = v_v) then v_k1 else 0) + (if (p = r_Bob) ∧ (x1 = v_u) then v_k else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_v) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = v_u) then 1 else 0)) }
  /-- pay; guarded by Alice -/
  | pay (s : St A D) (r_Alice : A) (r_Bob : A) (v_k : Nat) (h0 : r_Alice ≠ r_Bob) (h1 : v_k ≥ 1) (h2 : s.identity r_Alice ≥ 1) (h3 : s.knows r_Alice r_Bob ≥ 1) (h4 : s.coin r_Alice r_Bob ≥ v_k) (h5 : s.identity r_Bob ≥ 1) :
      Step s { s with coin := fun p x1 => (s.coin p x1 - ((if (p = r_Alice) ∧ (x1 = r_Bob) then v_k else 0))) + ((if (p = r_Bob) ∧ (x1 = r_Bob) then v_k else 0)) }
  /-- redeem; guarded by Alice -/
  | redeem (s : St A D) (r_Alice : A) (r_Bob : A) (v_r : A) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.knows r_Alice r_Bob ≥ 1) (h3 : s.coin r_Alice r_Bob ≥ 1) (h4 : s.identity r_Bob ≥ 1) (h5 : s.coin r_Bob v_r ≥ 1) (h6 : ∀ p : A, p = r_Alice → p = r_Alice → ¬ ((v_r = r_Bob))) (h7 : ∀ p : A, p = r_Bob → p = r_Bob → ¬ ((r_Bob = v_r))) :
      Step s { s with coin := fun p x1 => (s.coin p x1 - ((if (p = r_Alice) ∧ (x1 = r_Bob) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = v_r) then 1 else 0))) + ((if (p = r_Alice) ∧ (x1 = v_r) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = r_Bob) then 1 else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_r) then 1 else 0)) }

inductive Reach : St A D → Prop
  | init : Reach init
  | step {s s' : St A D} : Reach s → Step s s' → Reach s'

/-- The properties proved, conjoined. -/
def Props (s : St A D) : Prop :=
  (∀ (x0 : A), s.identity x0 ≤ 1) ∧
  (∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) ∧
  (∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0)

/-- identity(X) is never held twice -/
theorem init_0 : ∀ (x0 : A), (init : St A D).identity x0 ≤ 1 := by
  simp [init]

theorem step_0 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (h : Step s s') :
    ∀ (x0 : A), s'.identity x0 ≤ 1 := by
  cases h <;> grind

/-- knows(X, Y)  ⇒  identity(X) -/
theorem init_1 : ∀ (x0 : A) (x1 : A), (init : St A D).knows x0 x1 > 0 → (init : St A D).identity x0 > 0 := by
  simp [init]

theorem step_1 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H2 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H3 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) (H4 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.knows x0 x1 > 0 → s'.identity x0 > 0 := by
  cases h <;> grind

/-- knows(X, Y)  ⇒  identity(Y) -/
theorem init_2 : ∀ (x0 : A) (x1 : A), (init : St A D).knows x0 x1 > 0 → (init : St A D).identity x1 > 0 := by
  simp [init]

theorem step_2 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H2 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H3 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) (H4 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.knows x0 x1 > 0 → s'.identity x1 > 0 := by
  cases h <;> grind

/-- coin(X, Y)  ⇒  identity(X) -/
theorem init_3 : ∀ (x0 : A) (x1 : A), (init : St A D).coin x0 x1 > 0 → (init : St A D).identity x0 > 0 := by
  simp [init]

theorem step_3 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H2 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H3 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) (H4 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.coin x0 x1 > 0 → s'.identity x0 > 0 := by
  cases h <;> grind

/-- coin(X, Y)  ⇒  identity(Y) -/
theorem init_4 : ∀ (x0 : A) (x1 : A), (init : St A D).coin x0 x1 > 0 → (init : St A D).identity x1 > 0 := by
  simp [init]

theorem step_4 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H2 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H3 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) (H4 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.coin x0 x1 > 0 → s'.identity x1 > 0 := by
  cases h <;> grind

/-- coin(X, Y) and X ≠ Y  ⇒  knows(X, Y) -/
theorem init_5 : ∀ (x0 : A) (x1 : A), (init : St A D).coin x0 x1 > 0 → x0 ≠ x1 → (init : St A D).knows x0 x1 > 0 := by
  simp [init]

theorem step_5 (s s' : St A D) (H0 : ∀ (x0 : A), s.identity x0 ≤ 1) (H1 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x0 > 0) (H2 : ∀ (x0 : A) (x1 : A), s.knows x0 x1 > 0 → s.identity x1 > 0) (H3 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x0 > 0) (H4 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → s.identity x1 > 0) (H5 : ∀ (x0 : A) (x1 : A), s.coin x0 x1 > 0 → x0 ≠ x1 → s.knows x0 x1 > 0) (h : Step s s') :
    ∀ (x0 : A) (x1 : A), s'.coin x0 x1 > 0 → x0 ≠ x1 → s'.knows x0 x1 > 0 := by
  cases h <;> grind

/-- Every reachable state satisfies every property. -/
theorem reach_props {s : St A D} (h : Reach s) : Props s := by
  induction h with
  | init => exact ⟨init_0, init_1, init_2, init_3, init_4, init_5⟩
  | step _ hs ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := ih
    exact ⟨step_0 _ _ h0 hs, step_1 _ _ h0 h1 h2 h3 h4 h5 hs, step_2 _ _ h0 h1 h2 h3 h4 h5 hs, step_3 _ _ h0 h1 h2 h3 h4 h5 hs, step_4 _ _ h0 h1 h2 h3 h4 h5 hs, step_5 _ _ h0 h1 h2 h3 h4 h5 hs⟩

end GC
