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
end GC
