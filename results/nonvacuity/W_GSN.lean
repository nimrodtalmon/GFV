namespace GSN

structure St (A D : Type) where
  identity : A → Nat
  knows : A → A → Nat
  friend : A → A → Nat
  listed : A → A → D → Nat
  member : A → (A × D) → Nat
  received : A → D → A → Nat
  closed : A → D → Nat
  posted : A → D → D → Nat
  delivered : A → D → A → D → Nat
  received_in : A → D → A → D → Nat

variable {A D : Type} [DecidableEq A] [DecidableEq D]

def init : St A D := ⟨fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, fun _ _ _ _ => 0⟩

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
      Step s { s with friend := fun p x1 => (s.friend p x1 - ((if (p = r_Alice) ∧ (x1 = r_Bob) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = r_Alice) then 1 else 0))), listed := fun p x1 x2 => (if ((p = r_Alice) ∧ (x1 = r_Bob)) ∨ ((p = r_Bob) ∧ (x1 = r_Alice)) then 0 else s.listed p x1 x2), member := fun p x1 => (if ((p = r_Alice) ∧ (x1.1 = r_Bob)) ∨ ((p = r_Bob) ∧ (x1.1 = r_Alice)) then 0 else s.member p x1) }
  /-- message; guarded by Alice -/
  | message (s : St A D) (r_Alice : A) (r_Bob : A) (v_x : D) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.friend r_Alice r_Bob ≥ 1) (h3 : s.identity r_Bob ≥ 1) :
      Step s { s with received := fun p x1 x2 => s.received p x1 x2 + ((if (p = r_Bob) ∧ (x1 = v_x) ∧ (x2 = r_Alice) then 1 else 0)) }
  /-- create; guarded by Alice -/
  | create (s : St A D) (r_Alice : A) (v_n : D) (h0 : s.identity r_Alice ≥ 1) (h1 : s.member r_Alice (r_Alice, v_n) = 0) (h2 : s.closed r_Alice v_n = 0) (h3 : ∀ (z0 : A), s.member z0 (r_Alice, v_n) = 0) :
      Step s { s with member := fun p x1 => s.member p x1 + ((if (p = r_Alice) ∧ (x1 = (r_Alice, v_n)) then 1 else 0)), listed := fun p x1 x2 => s.listed p x1 x2 + ((if (p = r_Alice) ∧ (x1 = r_Alice) ∧ (x2 = v_n) then 1 else 0)) }
  /-- join; guarded by Alice, Bob -/
  | join (s : St A D) (r_Alice : A) (r_Bob : A) (v_n : D) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.member r_Alice (r_Alice, v_n) ≥ 1) (h3 : s.friend r_Alice r_Bob ≥ 1) (h4 : s.identity r_Bob ≥ 1) (h5 : s.member r_Bob (r_Alice, v_n) = 0) :
      Step s { s with listed := fun p x1 x2 => s.listed p x1 x2 + ((if (p = r_Alice) ∧ (x1 = r_Bob) ∧ (x2 = v_n) then 1 else 0)), member := fun p x1 => s.member p x1 + ((if (p = r_Bob) ∧ (x1 = (r_Alice, v_n)) then 1 else 0)) }
  /-- leave; guarded by Bob -/
  | leave (s : St A D) (r_Alice : A) (r_Bob : A) (v_n : D) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.listed r_Alice r_Bob v_n ≥ 1) (h3 : s.identity r_Bob ≥ 1) (h4 : s.member r_Bob (r_Alice, v_n) ≥ 1) :
      Step s { s with listed := fun p x1 x2 => (s.listed p x1 x2 - ((if (p = r_Alice) ∧ (x1 = r_Bob) ∧ (x2 = v_n) then 1 else 0))), member := fun p x1 => (s.member p x1 - ((if (p = r_Bob) ∧ (x1 = (r_Alice, v_n)) then 1 else 0))) }
  /-- remove; guarded by Alice -/
  | remove (s : St A D) (r_Alice : A) (r_Bob : A) (v_n : D) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.listed r_Alice r_Bob v_n ≥ 1) (h3 : s.identity r_Bob ≥ 1) (h4 : s.member r_Bob (r_Alice, v_n) ≥ 1) :
      Step s { s with listed := fun p x1 x2 => (s.listed p x1 x2 - ((if (p = r_Alice) ∧ (x1 = r_Bob) ∧ (x2 = v_n) then 1 else 0))), member := fun p x1 => (s.member p x1 - ((if (p = r_Bob) ∧ (x1 = (r_Alice, v_n)) then 1 else 0))) }
  /-- close; guarded by Alice -/
  | close (s : St A D) (r_Alice : A) (v_n : D) (h0 : s.identity r_Alice ≥ 1) (h1 : s.member r_Alice (r_Alice, v_n) ≥ 1) (h2 : s.listed r_Alice r_Alice v_n ≥ 1) (h3 : ∀ q : A, s.listed r_Alice q v_n > 0 → s.identity q ≥ 1) (h4 : ∀ q : A, s.listed r_Alice q v_n > 0 → s.member q (r_Alice, v_n) ≥ 1) :
      Step s { s with closed := fun p x1 => s.closed p x1 + ((if (p = r_Alice) ∧ (x1 = v_n) then 1 else 0)), listed := fun p x1 x2 => (s.listed p x1 x2 - ((if (p = r_Alice) ∧ (x1 = r_Alice) ∧ (x2 = v_n) then 1 else 0))), member := fun p x1 => (s.member p x1 - ((if (s.listed r_Alice p v_n > 0) ∧ (x1 = (r_Alice, v_n)) then 1 else 0))) }
  /-- post_own; guarded by Alice -/
  | post_own (s : St A D) (r_Alice : A) (v_n : D) (v_x : D) (h0 : s.identity r_Alice ≥ 1) (h1 : s.member r_Alice (r_Alice, v_n) ≥ 1) (h2 : s.posted r_Alice v_x v_n = 0) :
      Step s { s with posted := fun p x1 x2 => s.posted p x1 x2 + ((if (p = r_Alice) ∧ (x1 = v_x) ∧ (x2 = v_n) then 1 else 0)) }
  /-- post; guarded by Bob -/
  | post (s : St A D) (r_Bob : A) (r_Alice : A) (v_n : D) (v_x : D) (h0 : r_Bob ≠ r_Alice) (h1 : s.identity r_Bob ≥ 1) (h2 : s.member r_Bob (r_Alice, v_n) ≥ 1) (h3 : s.identity r_Alice ≥ 1) (h4 : s.member r_Alice (r_Alice, v_n) ≥ 1) (h5 : s.listed r_Alice r_Bob v_n ≥ 1) (h6 : s.friend r_Alice r_Bob ≥ 1) (h7 : s.posted r_Alice v_x v_n = 0) :
      Step s { s with posted := fun p x1 x2 => s.posted p x1 x2 + ((if (p = r_Alice) ∧ (x1 = v_x) ∧ (x2 = v_n) then 1 else 0)) }
  /-- deliver; guarded by none (unguarded: taken by liveness) -/
  | deliver (s : St A D) (r_Alice : A) (r_Bob : A) (v_n : D) (v_x : D) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.member r_Alice (r_Alice, v_n) ≥ 1) (h3 : s.posted r_Alice v_x v_n ≥ 1) (h4 : s.listed r_Alice r_Bob v_n ≥ 1) (h5 : s.friend r_Alice r_Bob ≥ 1) (h6 : s.delivered r_Alice v_x r_Bob v_n = 0) (h7 : s.identity r_Bob ≥ 1) (h8 : s.member r_Bob (r_Alice, v_n) ≥ 1) :
      Step s { s with delivered := fun p x1 x2 x3 => s.delivered p x1 x2 x3 + ((if (p = r_Alice) ∧ (x1 = v_x) ∧ (x2 = r_Bob) ∧ (x3 = v_n) then 1 else 0)), received_in := fun p x1 x2 x3 => s.received_in p x1 x2 x3 + ((if (p = r_Bob) ∧ (x1 = v_x) ∧ (x2 = r_Alice) ∧ (x3 = v_n) then 1 else 0)) }

inductive Reach : St A D → Prop
  | init : Reach init
  | step {s s' : St A D} : Reach s → Step s s' → Reach s'
/-- A run in which every schema fires: the Step relation is not vacuous. -/
theorem nonvacuous : ∃ s : St (Fin 3) (Fin 2), Reach s :=
  ⟨_, (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step (Reach.step Reach.init (Step.establish _ 0 (by decide))) (Step.create _ 0 0 (by decide) (by decide) (by decide) (by decide))) (Step.close _ 0 0 (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.establish _ 1 (by decide))) (Step.acquaint _ 0 1 (by decide) (by decide) (by decide))) (Step.befriend _ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.unfriend _ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.acquaint _ 0 1 (by decide) (by decide) (by decide))) (Step.introduce _ 0 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.befriend _ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.message _ 0 1 0 (by decide) (by decide) (by decide) (by decide))) (Step.create _ 0 1 (by decide) (by decide) (by decide) (by decide))) (Step.join _ 0 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.leave _ 0 1 1 (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.post_own _ 0 1 0 (by decide) (by decide) (by decide))) (Step.join _ 0 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.remove _ 0 1 1 (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.join _ 0 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.post _ 1 0 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))) (Step.deliver _ 0 1 1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))⟩
end GSN

