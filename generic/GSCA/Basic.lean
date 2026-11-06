/-
Route A: speech-act schemas as data, a semantics, and a theorem proved once for
every contract meeting a syntactic condition.

Fragment: schemas with agent roles, agent variables and speech-act variables
(no listed roles, name terms or values).  The semantics is deliberately
permissive -- any deletion is allowed, distinctness of roles and forbidden atoms
are not required -- so every theorem below holds a fortiori for the protocol of
GSC's Definition "Denotation".

Theorem `records_within_instances`: if a contract has traceable provenance
(GSC Def. "Traceable provenance", the set of all predicates, agent-role
fragment), then in every reachable configuration, an agent holding an atom that
names another agent is connected to that agent in the interaction graph of the
run: records never cross instances (GSC Lemma "No edge crosses instances").
-/

namespace GSCA

/-! ## Syntax -/

inductive Term where
  | role (i : Nat)
  | avar (j : Nat)
  | svar (j : Nat)
  deriving DecidableEq, Repr

structure Atom where
  pred : String
  args : List Term     -- the holder is the role, not an argument
  deriving DecidableEq, Repr

structure RoleSpec where
  req  : List Atom
  forb : List Atom
  add  : List Atom
  del  : List Atom
  deriving Repr

structure Schema where
  name   : String
  roles  : List RoleSpec
  guards : List Nat
  deriving Repr

abbrev Contract := List Schema

/-! ## Semantics -/

variable {Ag Sa : Type}

inductive Val (Ag Sa : Type) where
  | ag (a : Ag)
  | sa (d : Sa)

structure GAtom (Ag Sa : Type) where
  pred : String
  args : List (Val Ag Sa)

structure Binding (Ag Sa : Type) where
  role : Nat → Ag
  avar : Nat → Ag
  svar : Nat → Sa

def Term.eval (b : Binding Ag Sa) : Term → Val Ag Sa
  | .role i => .ag (b.role i)
  | .avar j => .ag (b.avar j)
  | .svar j => .sa (b.svar j)

def Atom.eval (b : Binding Ag Sa) (a : Atom) : GAtom Ag Sa :=
  ⟨a.pred, a.args.map (Term.eval b)⟩

/-- A configuration: each agent's state, and the interaction graph of the run so far. -/
structure Config (Ag Sa : Type) where
  st : Ag → List (GAtom Ag Sa)
  g  : Ag → Ag → Prop

def Config.init : Config Ag Sa := ⟨fun _ => [], fun _ _ => False⟩

/-- Schema `τ` fires at binding `b`: every role's required atoms are held; every atom
held afterwards was held before or was added by a role at its agent; and the
interaction graph gains an edge between every two participants. -/
structure Fires (τ : Schema) (b : Binding Ag Sa) (c c' : Config Ag Sa) : Prop where
  pre  : ∀ (i : Nat) (r : RoleSpec), τ.roles[i]? = some r → ∀ a ∈ r.req, a.eval b ∈ c.st (b.role i)
  post : ∀ p x, x ∈ c'.st p → x ∈ c.st p ∨
           ∃ (i : Nat) (r : RoleSpec), τ.roles[i]? = some r ∧ p = b.role i ∧ ∃ φ ∈ r.add, x = φ.eval b
  graph : ∀ x y, c'.g x y ↔ c.g x y ∨
           ∃ i j, i < τ.roles.length ∧ j < τ.roles.length ∧ x = b.role i ∧ y = b.role j

inductive Reach (C : Contract) : Config Ag Sa → Prop where
  | init : Reach C Config.init
  | step {c c' : Config Ag Sa} (τ : Schema) (b : Binding Ag Sa) :
      Reach C c → τ ∈ C → Fires τ b c c' → Reach C c'

/-- Connected in the undirected interaction graph: the same instance. -/
inductive Conn (g : Ag → Ag → Prop) : Ag → Ag → Prop where
  | refl (a : Ag) : Conn g a a
  | tail {a b c : Ag} : Conn g a b → (g b c ∨ g c b) → Conn g a c

/-! ## The syntactic condition -/

/-- Traceable provenance of a schema, agent-role fragment, all predicates: every agent
argument of an atom a role adds is that role, another role, or an argument of an
atom some role requires. -/
def TPSchema (τ : Schema) : Prop :=
  ∀ (i : Nat) (r : RoleSpec), τ.roles[i]? = some r → ∀ φ ∈ r.add, ∀ u ∈ φ.args,
    (∃ j, u = .svar j) ∨ (∃ j, j < τ.roles.length ∧ u = .role j) ∨
    (∃ (j : Nat) (rj : RoleSpec), τ.roles[j]? = some rj ∧ ∃ ψ ∈ rj.req, u ∈ ψ.args)

/-- The decision procedure. -/
def tpTerm (τ : Schema) (u : Term) : Bool :=
  match u with
  | .svar _ => true
  | _ => (match u with | .role j => decide (j < τ.roles.length) | _ => false) ||
         τ.roles.any (fun rj => rj.req.any (fun ψ => ψ.args.contains u))

def tpCheck (τ : Schema) : Bool :=
  τ.roles.all (fun r => r.add.all (fun φ => φ.args.all (tpTerm τ)))

/-! ## Lemmas on connectivity -/

theorem Conn.trans {g : Ag → Ag → Prop} {a b c : Ag} (h1 : Conn g a b) (h2 : Conn g b c) :
    Conn g a c := by
  induction h2 with
  | refl => exact h1
  | tail _ e ih => exact Conn.tail ih e

theorem Conn.single {g : Ag → Ag → Prop} {a b : Ag} (e : g a b ∨ g b a) : Conn g a b :=
  Conn.tail (Conn.refl a) e

theorem Conn.symm {g : Ag → Ag → Prop} {a b : Ag} (h : Conn g a b) : Conn g b a := by
  induction h with
  | refl => exact Conn.refl _
  | tail _ e ih => exact Conn.trans (Conn.single (Or.symm e)) ih

theorem Conn.mono {g g' : Ag → Ag → Prop} (hg : ∀ x y, g x y → g' x y) {a b : Ag}
    (h : Conn g a b) : Conn g' a b := by
  induction h with
  | refl => exact Conn.refl _
  | tail _ e ih => exact Conn.tail ih (e.elim (fun h => Or.inl (hg _ _ h)) (fun h => Or.inr (hg _ _ h)))

/-! ## Soundness of the checker -/

theorem tpTerm_sound (τ : Schema) (u : Term) (h : tpTerm τ u = true) :
    (∃ j, u = .svar j) ∨ (∃ j, j < τ.roles.length ∧ u = .role j) ∨
    (∃ (j : Nat) (rj : RoleSpec), τ.roles[j]? = some rj ∧ ∃ ψ ∈ rj.req, u ∈ ψ.args) := by
  cases u with
  | svar j => exact Or.inl ⟨j, rfl⟩
  | role j =>
    simp only [tpTerm, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
      List.contains_iff_mem] at h
    rcases h with h | ⟨rj, hrj, ψ, hψ, hu⟩
    · exact Or.inr (Or.inl ⟨j, h, rfl⟩)
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hrj
      exact Or.inr (Or.inr ⟨k, rj, hk, ψ, hψ, hu⟩)
  | avar j =>
    simp only [tpTerm, Bool.false_or, List.any_eq_true, List.contains_iff_mem] at h
    obtain ⟨rj, hrj, ψ, hψ, hu⟩ := h
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hrj
    exact Or.inr (Or.inr ⟨k, rj, hk, ψ, hψ, hu⟩)

theorem tpCheck_sound (τ : Schema) (h : tpCheck τ = true) : TPSchema τ := by
  intro i r hr φ hφ u hu
  apply tpTerm_sound
  simp only [tpCheck, List.all_eq_true] at h
  exact h r (List.mem_of_getElem? hr) φ hφ u hu

/-! ## The theorem -/

/-- In every reachable configuration of a contract with traceable provenance, a
record held by `p` that names agent `q` lies within `p`'s instance. -/
theorem records_within_instances (C : Contract) (hC : ∀ τ ∈ C, TPSchema τ)
    {c : Config Ag Sa} (hr : Reach C c) :
    ∀ p x q, x ∈ c.st p → Val.ag q ∈ x.args → Conn c.g p q := by
  induction hr with
  | init => intro p x q hx; simp [Config.init] at hx
  | @step c c' τ b _ hτ hf ih =>
    have mono : ∀ x y, c.g x y → c'.g x y := fun x y h => (hf.graph x y).mpr (Or.inl h)
    have edge : ∀ i j, i < τ.roles.length → j < τ.roles.length →
        c'.g (b.role i) (b.role j) := fun i j hi hj =>
      (hf.graph _ _).mpr (Or.inr ⟨i, j, hi, hj, rfl, rfl⟩)
    intro p x q hx hq
    rcases hf.post p x hx with hold | ⟨i, r, hr, rfl, φ, hφ, rfl⟩
    · exact Conn.mono mono (ih p x q hold hq)
    · simp only [Atom.eval, List.mem_map] at hq
      obtain ⟨u, hu, hev⟩ := hq
      have hi : i < τ.roles.length := (List.getElem?_eq_some_iff.mp hr).1
      rcases hC τ hτ i r hr φ hφ u hu with ⟨j, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, rj, hrj, ψ, hψ, hu'⟩
      · simp [Term.eval] at hev
      · simp only [Term.eval, Val.ag.injEq] at hev
        subst hev
        exact Conn.single (Or.inl (edge i j hi hj))
      · have hj : j < τ.roles.length := (List.getElem?_eq_some_iff.mp hrj).1
        have held : ψ.eval b ∈ c.st (b.role j) := hf.pre j rj hrj ψ hψ
        have named : Val.ag q ∈ (ψ.eval b).args := by
          simp only [Atom.eval, List.mem_map]; exact ⟨u, hu', hev⟩
        have h1 : Conn c'.g (b.role j) q := Conn.mono mono (ih _ _ _ held named)
        exact Conn.trans (Conn.single (Or.inl (edge i j hi hj))) h1

/-- The stamp: a contract the checker accepts has records within instances. -/
theorem stamp (C : Contract) (h : C.all tpCheck = true) {c : Config Ag Sa} (hr : Reach C c) :
    ∀ p x q, x ∈ c.st p → Val.ag q ∈ x.args → Conn c.g p q :=
  records_within_instances C (fun τ hτ => tpCheck_sound τ (List.all_eq_true.mp h τ hτ)) hr

end GSCA
