import GSCA.Basic
/-!
Second generic theorem: volition gives closure (GSC Prop. "Closure", agent-role
fragment).  The role graph of a schema has an edge between two roles when one
requires an atom naming the other.  A certificate gives, for each role, a path
in the role graph: to role 0 ("connected") or to a guarding role ("guarded").
Lean checks the certificate by `decide`.  The theorem: for any enabled
transaction in a reachable configuration, either all participants lie in one
instance, or each participant lies in the instance of some guard.
-/
namespace GSCA

variable {Ag Sa : Type}

def reqNames (τ : Schema) (i j : Nat) : Bool :=
  match τ.roles[i]? with
  | some r => r.req.any (fun ψ => ψ.args.contains (.role j))
  | none => false

def rgEdge (τ : Schema) (i j : Nat) : Bool := reqNames τ i j || reqNames τ j i

def pathOK (τ : Schema) : Nat → List Nat → Nat → Bool
  | i, [], j => i == j
  | i, k :: ks, j => rgEdge τ i k && pathOK τ k ks j

inductive VolCert where
  | connected (paths : List (List Nat))           -- paths[i] : 0 ~> i
  | guarded (paths : List (Nat × List Nat))       -- paths[i] = (g, i ~> g), g a guard

def volCheck (τ : Schema) : VolCert → Bool
  | .connected ps => ps.length == τ.roles.length &&
      (List.range τ.roles.length).all (fun i => pathOK τ 0 (ps.getD i []) i)
  | .guarded ps => ps.length == τ.roles.length &&
      (List.range τ.roles.length).all (fun i =>
        let (g, p) := ps.getD i (0, [])
        τ.guards.contains g && pathOK τ i p g)

/-- Schema `τ` is enabled at binding `b` in configuration `c`. -/
def Enabled (τ : Schema) (b : Binding Ag Sa) (c : Config Ag Sa) : Prop :=
  ∀ (i : Nat) (r : RoleSpec), τ.roles[i]? = some r → ∀ a ∈ r.req, a.eval b ∈ c.st (b.role i)

theorem reqNames_conn (C : Contract) (hC : ∀ τ ∈ C, TPSchema τ) {c : Config Ag Sa}
    (hr : Reach C c) (τ : Schema) (b : Binding Ag Sa) (he : Enabled τ b c) (i j : Nat)
    (h : reqNames τ i j = true) : Conn c.g (b.role i) (b.role j) := by
  unfold reqNames at h
  split at h
  · rename_i r hr'
    simp only [List.any_eq_true, List.contains_iff_mem] at h
    obtain ⟨ψ, hψ, hj⟩ := h
    apply records_within_instances C hC hr (b.role i) (ψ.eval b) (b.role j) (he i r hr' ψ hψ)
    simp only [Atom.eval, List.mem_map]
    exact ⟨.role j, hj, rfl⟩
  · simp at h

theorem path_conn (C : Contract) (hC : ∀ τ ∈ C, TPSchema τ) {c : Config Ag Sa}
    (hr : Reach C c) (τ : Schema) (b : Binding Ag Sa) (he : Enabled τ b c) :
    ∀ (p : List Nat) (i j : Nat), pathOK τ i p j = true → Conn c.g (b.role i) (b.role j) := by
  intro p
  induction p with
  | nil => intro i j h; simp [pathOK] at h; subst h; exact Conn.refl _
  | cons k ks ih =>
    intro i j h
    simp only [pathOK, Bool.and_eq_true] at h
    have e : Conn c.g (b.role i) (b.role k) := by
      simp only [rgEdge, Bool.or_eq_true] at h
      rcases h.1 with h1 | h1
      · exact reqNames_conn C hC hr τ b he i k h1
      · exact (reqNames_conn C hC hr τ b he k i h1).symm
    exact e.trans (ih k j h.2)

/-- Closure: an enabled act of a schema with a checked volition certificate either
lies within one instance, or every participant shares an instance with a guard. -/
theorem closure (C : Contract) (hC : ∀ τ ∈ C, TPSchema τ) {c : Config Ag Sa}
    (hr : Reach C c) (τ : Schema) (cert : VolCert) (hv : volCheck τ cert = true)
    (b : Binding Ag Sa) (he : Enabled τ b c) :
    (∀ i j, i < τ.roles.length → j < τ.roles.length → Conn c.g (b.role i) (b.role j)) ∨
    (∀ i, i < τ.roles.length → ∃ g ∈ τ.guards, Conn c.g (b.role i) (b.role g)) := by
  cases cert with
  | connected ps =>
    left
    simp only [volCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hv
    have h0 : ∀ i, i < τ.roles.length → Conn c.g (b.role 0) (b.role i) := fun i hi =>
      path_conn C hC hr τ b he _ 0 i (hv.2 i hi)
    intro i j hi hj
    exact (h0 i hi).symm.trans (h0 j hj)
  | guarded ps =>
    right
    simp only [volCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hv
    intro i hi
    have := hv.2 i hi
    revert this
    generalize ps.getD i (0, []) = q
    obtain ⟨g, p⟩ := q
    intro h
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    exact ⟨g, h.1, path_conn C hC hr τ b he p i g h.2⟩

end GSCA

namespace GSCA
variable {Ag Sa : Type}

/-- The stamp for a contract given with volition certificates: records stay within
instances, and every enabled act is within one instance or guarded in each. -/
theorem closure_stamp (L : List (Schema × VolCert))
    (htp : (L.map Prod.fst).all tpCheck = true)
    (hv : L.all (fun p => volCheck p.1 p.2) = true)
    {c : Config Ag Sa} (hr : Reach (L.map Prod.fst) c)
    (τ : Schema) (hτ : τ ∈ L.map Prod.fst) (b : Binding Ag Sa) (he : Enabled τ b c) :
    (∀ i j, i < τ.roles.length → j < τ.roles.length → Conn c.g (b.role i) (b.role j)) ∨
    (∀ i, i < τ.roles.length → ∃ g ∈ τ.guards, Conn c.g (b.role i) (b.role g)) := by
  have hC : ∀ τ ∈ L.map Prod.fst, TPSchema τ :=
    fun τ h => tpCheck_sound τ (List.all_eq_true.mp htp τ h)
  obtain ⟨⟨τ', k⟩, hp, rfl⟩ := List.mem_map.mp hτ
  exact closure _ hC hr τ' k (List.all_eq_true.mp hv _ hp) b he

end GSCA
