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
/-- A run in which every schema fires: the Step relation is not vacuous. -/
theorem nonvacuous : ∃ s : St (Fin 3) (Fin 2), Reach s :=
  ⟨_, (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step Reach.init (Step.establish _ 0 (by decide))) (Step.establish _ 1 (by decide))) (Step.acquaint _ 0 1 (by decide) (by decide) (by decide))) (Step.befriend _ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.unfriend _ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.acquaint _ 0 1 (by decide) (by decide) (by decide))) (Step.introduce _ 0 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.befriend _ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.point_friend _ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.unpoint _ 0 1 (by decide) (by decide) (by decide) (by decide))) (Step.point_friend _ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.point_friend _ 1 0 (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.point_transitive _ 1 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))⟩
end GDO

