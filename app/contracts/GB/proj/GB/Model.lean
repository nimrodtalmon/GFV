namespace GB

structure St (A D : Type) where
  identity : A → Nat
  knows : A → A → Nat
  coin : A → A → Nat
  date : A → Nat → Nat
  bond : A → A → Nat → Nat
  today : A → Nat → Nat
  dated : A → Nat

variable {A D : Type} [DecidableEq A] [DecidableEq D]

def init : St A D := ⟨fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ => 0⟩

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
  /-- mint_coin; guarded by Alice -/
  | mint_coin (s : St A D) (r_Alice : A) (v_k : Nat) (h0 : v_k ≥ 1) (h1 : s.identity r_Alice ≥ 1) :
      Step s { s with coin := fun p x1 => s.coin p x1 + ((if (p = r_Alice) ∧ (x1 = r_Alice) then v_k else 0)) }
  /-- mint_bond; guarded by Alice -/
  | mint_bond (s : St A D) (r_Alice : A) (v_t : Nat) (v_d : Nat) (v_k : Nat) (h0 : v_k ≥ 1) (h1 : v_d > v_t) (h2 : s.identity r_Alice ≥ 1) (h3 : s.date r_Alice v_t ≥ 1) :
      Step s { s with bond := fun p x1 x2 => s.bond p x1 x2 + ((if (p = r_Alice) ∧ (x1 = r_Alice) ∧ (x2 = v_d) then v_k else 0)) }
  /-- first_date; guarded by none (unguarded: taken by liveness) -/
  | first_date (s : St A D) (r_Alice : A) (v_d : Nat) (h0 : s.identity r_Alice ≥ 1) (h1 : s.today r_Alice v_d ≥ 1) (h2 : s.dated r_Alice = 0) :
      Step s { s with date := fun p x1 => s.date p x1 + ((if (p = r_Alice) ∧ (x1 = v_d) then 1 else 0)), dated := fun p => s.dated p + ((if (p = r_Alice) then 1 else 0)) }
  /-- advance; guarded by none (unguarded: taken by liveness) -/
  | advance (s : St A D) (r_Alice : A) (v_d : Nat) (v_t : Nat) (v_t1 : Nat) (h0 : v_t1 = v_t + 1) (h1 : v_t1 ≤ v_d) (h2 : s.identity r_Alice ≥ 1) (h3 : s.today r_Alice v_d ≥ 1) (h4 : s.date r_Alice v_t ≥ 1) (h5 : ∀ p : A, p = r_Alice → p = r_Alice → ¬ ((v_t1 = v_t))) :
      Step s { s with date := fun p x1 => (s.date p x1 - ((if (p = r_Alice) ∧ (x1 = v_t) then 1 else 0))) + ((if (p = r_Alice) ∧ (x1 = v_t1) then 1 else 0)) }
  /-- swap_cc; guarded by Alice, Bob -/
  | swap_cc (s : St A D) (r_Alice : A) (r_Bob : A) (v_u : A) (v_v : A) (v_k : Nat) (v_k1 : Nat) (h0 : r_Alice ≠ r_Bob) (h1 : v_k ≥ 1) (h2 : v_k1 ≥ 1) (h3 : s.identity r_Alice ≥ 1) (h4 : s.knows r_Alice r_Bob ≥ 1) (h5 : s.coin r_Alice v_u ≥ v_k) (h6 : s.identity r_Bob ≥ 1) (h7 : s.knows r_Bob r_Alice ≥ 1) (h8 : s.coin r_Bob v_v ≥ v_k1) (h9 : ∀ p : A, p = r_Alice → p = r_Alice → ¬ ((v_v = v_u))) (h10 : ∀ p : A, p = r_Bob → p = r_Bob → ¬ ((v_u = v_v))) :
      Step s { s with coin := fun p x1 => (s.coin p x1 - ((if (p = r_Alice) ∧ (x1 = v_u) then v_k else 0) + (if (p = r_Bob) ∧ (x1 = v_v) then v_k1 else 0))) + ((if (p = r_Alice) ∧ (x1 = v_v) then v_k1 else 0) + (if (p = r_Bob) ∧ (x1 = v_u) then v_k else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_v) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = v_u) then 1 else 0)) }
  /-- swap_cb; guarded by Alice, Bob -/
  | swap_cb (s : St A D) (r_Alice : A) (r_Bob : A) (v_u : A) (v_v : A) (v_k : Nat) (v_d1 : Nat) (v_k1 : Nat) (h0 : r_Alice ≠ r_Bob) (h1 : v_k ≥ 1) (h2 : v_k1 ≥ 1) (h3 : s.identity r_Alice ≥ 1) (h4 : s.knows r_Alice r_Bob ≥ 1) (h5 : s.coin r_Alice v_u ≥ v_k) (h6 : s.identity r_Bob ≥ 1) (h7 : s.knows r_Bob r_Alice ≥ 1) (h8 : s.bond r_Bob v_v v_d1 ≥ v_k1) :
      Step s { s with bond := fun p x1 x2 => (s.bond p x1 x2 - ((if (p = r_Bob) ∧ (x1 = v_v) ∧ (x2 = v_d1) then v_k1 else 0))) + ((if (p = r_Alice) ∧ (x1 = v_v) ∧ (x2 = v_d1) then v_k1 else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_v) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = v_u) then 1 else 0)), coin := fun p x1 => (s.coin p x1 - ((if (p = r_Alice) ∧ (x1 = v_u) then v_k else 0))) + ((if (p = r_Bob) ∧ (x1 = v_u) then v_k else 0)) }
  /-- swap_bc; guarded by Alice, Bob -/
  | swap_bc (s : St A D) (r_Alice : A) (r_Bob : A) (v_u : A) (v_v : A) (v_d : Nat) (v_k : Nat) (v_k1 : Nat) (h0 : r_Alice ≠ r_Bob) (h1 : v_k ≥ 1) (h2 : v_k1 ≥ 1) (h3 : s.identity r_Alice ≥ 1) (h4 : s.knows r_Alice r_Bob ≥ 1) (h5 : s.bond r_Alice v_u v_d ≥ v_k) (h6 : s.identity r_Bob ≥ 1) (h7 : s.knows r_Bob r_Alice ≥ 1) (h8 : s.coin r_Bob v_v ≥ v_k1) :
      Step s { s with coin := fun p x1 => (s.coin p x1 - ((if (p = r_Bob) ∧ (x1 = v_v) then v_k1 else 0))) + ((if (p = r_Alice) ∧ (x1 = v_v) then v_k1 else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_v) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = v_u) then 1 else 0)), bond := fun p x1 x2 => (s.bond p x1 x2 - ((if (p = r_Alice) ∧ (x1 = v_u) ∧ (x2 = v_d) then v_k else 0))) + ((if (p = r_Bob) ∧ (x1 = v_u) ∧ (x2 = v_d) then v_k else 0)) }
  /-- swap_bb; guarded by Alice, Bob -/
  | swap_bb (s : St A D) (r_Alice : A) (r_Bob : A) (v_u : A) (v_v : A) (v_d : Nat) (v_k : Nat) (v_d1 : Nat) (v_k1 : Nat) (h0 : r_Alice ≠ r_Bob) (h1 : v_k ≥ 1) (h2 : v_k1 ≥ 1) (h3 : s.identity r_Alice ≥ 1) (h4 : s.knows r_Alice r_Bob ≥ 1) (h5 : s.bond r_Alice v_u v_d ≥ v_k) (h6 : s.identity r_Bob ≥ 1) (h7 : s.knows r_Bob r_Alice ≥ 1) (h8 : s.bond r_Bob v_v v_d1 ≥ v_k1) (h9 : ∀ p : A, p = r_Alice → p = r_Alice → ¬ ((v_v = v_u) ∧ (v_d1 = v_d))) (h10 : ∀ p : A, p = r_Bob → p = r_Bob → ¬ ((v_u = v_v) ∧ (v_d = v_d1))) :
      Step s { s with bond := fun p x1 x2 => (s.bond p x1 x2 - ((if (p = r_Alice) ∧ (x1 = v_u) ∧ (x2 = v_d) then v_k else 0) + (if (p = r_Bob) ∧ (x1 = v_v) ∧ (x2 = v_d1) then v_k1 else 0))) + ((if (p = r_Alice) ∧ (x1 = v_v) ∧ (x2 = v_d1) then v_k1 else 0) + (if (p = r_Bob) ∧ (x1 = v_u) ∧ (x2 = v_d) then v_k else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_v) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = v_u) then 1 else 0)) }
  /-- pay; guarded by Alice -/
  | pay (s : St A D) (r_Alice : A) (r_Bob : A) (v_k : Nat) (h0 : r_Alice ≠ r_Bob) (h1 : v_k ≥ 1) (h2 : s.identity r_Alice ≥ 1) (h3 : s.knows r_Alice r_Bob ≥ 1) (h4 : s.coin r_Alice r_Bob ≥ v_k) (h5 : s.identity r_Bob ≥ 1) :
      Step s { s with coin := fun p x1 => (s.coin p x1 - ((if (p = r_Alice) ∧ (x1 = r_Bob) then v_k else 0))) + ((if (p = r_Bob) ∧ (x1 = r_Bob) then v_k else 0)) }
  /-- redeem_cc; guarded by Alice -/
  | redeem_cc (s : St A D) (r_Alice : A) (r_Bob : A) (v_r : A) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.knows r_Alice r_Bob ≥ 1) (h3 : s.coin r_Alice r_Bob ≥ 1) (h4 : s.identity r_Bob ≥ 1) (h5 : s.coin r_Bob v_r ≥ 1) (h6 : ∀ p : A, p = r_Alice → p = r_Alice → ¬ ((v_r = r_Bob))) (h7 : ∀ p : A, p = r_Bob → p = r_Bob → ¬ ((r_Bob = v_r))) :
      Step s { s with coin := fun p x1 => (s.coin p x1 - ((if (p = r_Alice) ∧ (x1 = r_Bob) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = v_r) then 1 else 0))) + ((if (p = r_Alice) ∧ (x1 = v_r) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = r_Bob) then 1 else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_r) then 1 else 0)) }
  /-- redeem_cb; guarded by Alice -/
  | redeem_cb (s : St A D) (r_Alice : A) (r_Bob : A) (v_r : A) (v_d1 : Nat) (h0 : r_Alice ≠ r_Bob) (h1 : s.identity r_Alice ≥ 1) (h2 : s.knows r_Alice r_Bob ≥ 1) (h3 : s.coin r_Alice r_Bob ≥ 1) (h4 : s.identity r_Bob ≥ 1) (h5 : s.bond r_Bob v_r v_d1 ≥ 1) :
      Step s { s with bond := fun p x1 x2 => (s.bond p x1 x2 - ((if (p = r_Bob) ∧ (x1 = v_r) ∧ (x2 = v_d1) then 1 else 0))) + ((if (p = r_Alice) ∧ (x1 = v_r) ∧ (x2 = v_d1) then 1 else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_r) then 1 else 0)), coin := fun p x1 => (s.coin p x1 - ((if (p = r_Alice) ∧ (x1 = r_Bob) then 1 else 0))) + ((if (p = r_Bob) ∧ (x1 = r_Bob) then 1 else 0)) }
  /-- redeem_bc; guarded by Alice -/
  | redeem_bc (s : St A D) (r_Alice : A) (r_Bob : A) (v_r : A) (v_d : Nat) (v_t : Nat) (h0 : r_Alice ≠ r_Bob) (h1 : v_d ≤ v_t) (h2 : s.identity r_Alice ≥ 1) (h3 : s.knows r_Alice r_Bob ≥ 1) (h4 : s.bond r_Alice r_Bob v_d ≥ 1) (h5 : s.identity r_Bob ≥ 1) (h6 : s.date r_Bob v_t ≥ 1) (h7 : s.coin r_Bob v_r ≥ 1) :
      Step s { s with coin := fun p x1 => (s.coin p x1 - ((if (p = r_Bob) ∧ (x1 = v_r) then 1 else 0))) + ((if (p = r_Alice) ∧ (x1 = v_r) then 1 else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_r) then 1 else 0)), bond := fun p x1 x2 => (s.bond p x1 x2 - ((if (p = r_Alice) ∧ (x1 = r_Bob) ∧ (x2 = v_d) then 1 else 0))) + ((if (p = r_Bob) ∧ (x1 = r_Bob) ∧ (x2 = v_d) then 1 else 0)) }
  /-- redeem_bb; guarded by Alice -/
  | redeem_bb (s : St A D) (r_Alice : A) (r_Bob : A) (v_r : A) (v_d : Nat) (v_d1 : Nat) (v_t : Nat) (h0 : r_Alice ≠ r_Bob) (h1 : v_d ≤ v_t) (h2 : s.identity r_Alice ≥ 1) (h3 : s.knows r_Alice r_Bob ≥ 1) (h4 : s.bond r_Alice r_Bob v_d ≥ 1) (h5 : s.identity r_Bob ≥ 1) (h6 : s.date r_Bob v_t ≥ 1) (h7 : s.bond r_Bob v_r v_d1 ≥ 1) (h8 : ∀ p : A, p = r_Alice → p = r_Alice → ¬ ((v_r = r_Bob) ∧ (v_d1 = v_d))) (h9 : ∀ p : A, p = r_Bob → p = r_Bob → ¬ ((r_Bob = v_r) ∧ (v_d = v_d1))) :
      Step s { s with bond := fun p x1 x2 => (s.bond p x1 x2 - ((if (p = r_Alice) ∧ (x1 = r_Bob) ∧ (x2 = v_d) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = v_r) ∧ (x2 = v_d1) then 1 else 0))) + ((if (p = r_Alice) ∧ (x1 = v_r) ∧ (x2 = v_d1) then 1 else 0) + (if (p = r_Bob) ∧ (x1 = r_Bob) ∧ (x2 = v_d) then 1 else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_r) then 1 else 0)) }
  /-- deposit_c; guarded by Alice, Carol -/
  | deposit_c (s : St A D) (r_Alice : A) (r_Carol : A) (v_u : A) (v_k : Nat) (h0 : r_Alice ≠ r_Carol) (h1 : v_k ≥ 1) (h2 : s.identity r_Alice ≥ 1) (h3 : s.knows r_Alice r_Carol ≥ 1) (h4 : s.coin r_Alice v_u ≥ v_k) (h5 : s.identity r_Carol ≥ 1) (h6 : s.knows r_Carol r_Alice ≥ 1) :
      Step s { s with coin := fun p x1 => (s.coin p x1 - ((if (p = r_Alice) ∧ (x1 = v_u) then v_k else 0))) + ((if (p = r_Carol) ∧ (x1 = v_u) then v_k else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Carol) ∧ (x1 = v_u) then 1 else 0)) }
  /-- deposit_b; guarded by Alice, Carol -/
  | deposit_b (s : St A D) (r_Alice : A) (r_Carol : A) (v_u : A) (v_d : Nat) (v_k : Nat) (h0 : r_Alice ≠ r_Carol) (h1 : v_k ≥ 1) (h2 : s.identity r_Alice ≥ 1) (h3 : s.knows r_Alice r_Carol ≥ 1) (h4 : s.bond r_Alice v_u v_d ≥ v_k) (h5 : s.identity r_Carol ≥ 1) (h6 : s.knows r_Carol r_Alice ≥ 1) :
      Step s { s with bond := fun p x1 x2 => (s.bond p x1 x2 - ((if (p = r_Alice) ∧ (x1 = v_u) ∧ (x2 = v_d) then v_k else 0))) + ((if (p = r_Carol) ∧ (x1 = v_u) ∧ (x2 = v_d) then v_k else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Carol) ∧ (x1 = v_u) then 1 else 0)) }
  /-- release_c; guarded by Carol, Bob -/
  | release_c (s : St A D) (r_Carol : A) (r_Bob : A) (v_u : A) (v_k : Nat) (h0 : r_Carol ≠ r_Bob) (h1 : v_k ≥ 1) (h2 : s.identity r_Carol ≥ 1) (h3 : s.knows r_Carol r_Bob ≥ 1) (h4 : s.coin r_Carol v_u ≥ v_k) (h5 : s.identity r_Bob ≥ 1) (h6 : s.knows r_Bob r_Carol ≥ 1) :
      Step s { s with coin := fun p x1 => (s.coin p x1 - ((if (p = r_Carol) ∧ (x1 = v_u) then v_k else 0))) + ((if (p = r_Bob) ∧ (x1 = v_u) then v_k else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Bob) ∧ (x1 = v_u) then 1 else 0)) }
  /-- release_b; guarded by Carol, Bob -/
  | release_b (s : St A D) (r_Carol : A) (r_Bob : A) (v_u : A) (v_d : Nat) (v_k : Nat) (h0 : r_Carol ≠ r_Bob) (h1 : v_k ≥ 1) (h2 : s.identity r_Carol ≥ 1) (h3 : s.knows r_Carol r_Bob ≥ 1) (h4 : s.bond r_Carol v_u v_d ≥ v_k) (h5 : s.identity r_Bob ≥ 1) (h6 : s.knows r_Bob r_Carol ≥ 1) :
      Step s { s with bond := fun p x1 x2 => (s.bond p x1 x2 - ((if (p = r_Carol) ∧ (x1 = v_u) ∧ (x2 = v_d) then v_k else 0))) + ((if (p = r_Bob) ∧ (x1 = v_u) ∧ (x2 = v_d) then v_k else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Bob) ∧ (x1 = v_u) then 1 else 0)) }
  /-- return_c; guarded by Carol, Alice -/
  | return_c (s : St A D) (r_Carol : A) (r_Alice : A) (v_u : A) (v_k : Nat) (h0 : r_Carol ≠ r_Alice) (h1 : v_k ≥ 1) (h2 : s.identity r_Carol ≥ 1) (h3 : s.knows r_Carol r_Alice ≥ 1) (h4 : s.coin r_Carol v_u ≥ v_k) (h5 : s.identity r_Alice ≥ 1) (h6 : s.knows r_Alice r_Carol ≥ 1) :
      Step s { s with coin := fun p x1 => (s.coin p x1 - ((if (p = r_Carol) ∧ (x1 = v_u) then v_k else 0))) + ((if (p = r_Alice) ∧ (x1 = v_u) then v_k else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_u) then 1 else 0)) }
  /-- return_b; guarded by Carol, Alice -/
  | return_b (s : St A D) (r_Carol : A) (r_Alice : A) (v_u : A) (v_d : Nat) (v_k : Nat) (h0 : r_Carol ≠ r_Alice) (h1 : v_k ≥ 1) (h2 : s.identity r_Carol ≥ 1) (h3 : s.knows r_Carol r_Alice ≥ 1) (h4 : s.bond r_Carol v_u v_d ≥ v_k) (h5 : s.identity r_Alice ≥ 1) (h6 : s.knows r_Alice r_Carol ≥ 1) :
      Step s { s with bond := fun p x1 x2 => (s.bond p x1 x2 - ((if (p = r_Carol) ∧ (x1 = v_u) ∧ (x2 = v_d) then v_k else 0))) + ((if (p = r_Alice) ∧ (x1 = v_u) ∧ (x2 = v_d) then v_k else 0)), knows := fun p x1 => s.knows p x1 + ((if (p = r_Alice) ∧ (x1 = v_u) then 1 else 0)) }
  /-- environment: the platform keeps `today` current (any update) -/
  | env_today (s : St A D) (f : A → Nat → Nat) : Step s { s with today := f }

inductive Reach : St A D → Prop
  | init : Reach init
  | step {s s' : St A D} : Reach s → Step s s' → Reach s'
end GB
