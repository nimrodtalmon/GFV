namespace GKK

structure St (A D : Type) where
  identity : A → Nat
  knows : A → A → Nat

variable {A D : Type} [DecidableEq A] [DecidableEq D]

def init : St A D := ⟨fun _ => 0, fun _ _ => 0⟩

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

inductive Reach : St A D → Prop
  | init : Reach init
  | step {s s' : St A D} : Reach s → Step s s' → Reach s'
end GKK
