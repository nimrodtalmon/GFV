import GSCA.Volition
namespace GSCA
def gkk_s0 : Schema :=
  { name := "establish", guards := [0],
    roles := [{ req := [], forb := [⟨"identity", []⟩], add := [⟨"identity", []⟩], del := [] }] }
def gkk_s1 : Schema :=
  { name:= "acquaint", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 0]⟩], del := [] }] }
def gkk_s2 : Schema :=
  { name:= "introduce", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"knows", [.avar 0]⟩], forb := [], add := [], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [], add := [⟨"knows", [.avar 0]⟩], del := [] }] }
def gkk_certified : List (Schema × VolCert) := [(gkk_s0, .connected [[]]), (gkk_s1, .guarded [(0, []), (1, [])]), (gkk_s2, .connected [[], [1]])]

theorem gkk_tp : (gkk_certified.map Prod.fst).all tpCheck = true := by decide
theorem gkk_vol : gkk_certified.all (fun p => volCheck p.1 p.2) = true := by decide
/-- GKK: in every reachable configuration, every enabled act lies within one instance,
or each of its participants shares an instance with one of its guards. -/
theorem gkk_closure {Ag Sa : Type} {c : Config Ag Sa} (hr : Reach (gkk_certified.map Prod.fst) c)
    (τ : Schema) (hτ : τ ∈ gkk_certified.map Prod.fst) (b : Binding Ag Sa) (he : Enabled τ b c) :
    (∀ i j, i < τ.roles.length → j < τ.roles.length → Conn c.g (b.role i) (b.role j)) ∨
    (∀ i, i < τ.roles.length → ∃ g ∈ τ.guards, Conn c.g (b.role i) (b.role g)) :=
  closure_stamp gkk_certified gkk_tp gkk_vol hr τ hτ b he

def gsg_s0 : Schema :=
  { name := "establish", guards := [0],
    roles := [{ req := [], forb := [⟨"identity", []⟩], add := [⟨"identity", []⟩], del := [] }] }
def gsg_s1 : Schema :=
  { name:= "acquaint", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 0]⟩], del := [] }] }
def gsg_s2 : Schema :=
  { name:= "introduce", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"knows", [.avar 0]⟩], forb := [], add := [], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [], add := [⟨"knows", [.avar 0]⟩], del := [] }] }
def gsg_s3 : Schema :=
  { name:= "befriend", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩], forb := [⟨"friend", [.role 1]⟩], add := [⟨"friend", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [⟨"friend", [.role 0]⟩], add := [⟨"friend", [.role 0]⟩], del := [] }] }
def gsg_s4 : Schema :=
  { name:= "unfriend", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"friend", [.role 1]⟩, ⟨"friend", [.role 1]⟩], forb := [], add := [], del := [⟨"friend", [.role 1]⟩] }, { req := [⟨"identity", []⟩, ⟨"friend", [.role 0]⟩, ⟨"friend", [.role 0]⟩], forb := [], add := [], del := [⟨"friend", [.role 0]⟩] }] }
def gsg_certified : List (Schema × VolCert) := [(gsg_s0, .connected [[]]), (gsg_s1, .guarded [(0, []), (1, [])]), (gsg_s2, .connected [[], [1]]), (gsg_s3, .connected [[], [1]]), (gsg_s4, .connected [[], [1]])]

theorem gsg_tp : (gsg_certified.map Prod.fst).all tpCheck = true := by decide
theorem gsg_vol : gsg_certified.all (fun p => volCheck p.1 p.2) = true := by decide
/-- GSG: in every reachable configuration, every enabled act lies within one instance,
or each of its participants shares an instance with one of its guards. -/
theorem gsg_closure {Ag Sa : Type} {c : Config Ag Sa} (hr : Reach (gsg_certified.map Prod.fst) c)
    (τ : Schema) (hτ : τ ∈ gsg_certified.map Prod.fst) (b : Binding Ag Sa) (he : Enabled τ b c) :
    (∀ i j, i < τ.roles.length → j < τ.roles.length → Conn c.g (b.role i) (b.role j)) ∨
    (∀ i, i < τ.roles.length → ∃ g ∈ τ.guards, Conn c.g (b.role i) (b.role g)) :=
  closure_stamp gsg_certified gsg_tp gsg_vol hr τ hτ b he

def gc_s0 : Schema :=
  { name := "establish", guards := [0],
    roles := [{ req := [], forb := [⟨"identity", []⟩], add := [⟨"identity", []⟩], del := [] }] }
def gc_s1 : Schema :=
  { name:= "acquaint", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 0]⟩], del := [] }] }
def gc_s2 : Schema :=
  { name:= "introduce", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"knows", [.avar 0]⟩], forb := [], add := [], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [], add := [⟨"knows", [.avar 0]⟩], del := [] }] }
def gc_s3 : Schema :=
  { name:= "mint", guards := [0],
    roles := [{ req := [⟨"identity", []⟩], forb := [], add := [⟨"coin", [.role 0]⟩], del := [] }] }
def gc_s4 : Schema :=
  { name:= "swap", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"coin", [.avar 0]⟩, ⟨"coin", [.avar 0]⟩], forb := [], add := [⟨"coin", [.avar 1]⟩, ⟨"knows", [.avar 1]⟩], del := [⟨"coin", [.avar 0]⟩] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩, ⟨"coin", [.avar 1]⟩, ⟨"coin", [.avar 1]⟩], forb := [], add := [⟨"coin", [.avar 0]⟩, ⟨"knows", [.avar 0]⟩], del := [⟨"coin", [.avar 1]⟩] }] }
def gc_s5 : Schema :=
  { name:= "pay", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"coin", [.role 1]⟩, ⟨"coin", [.role 1]⟩], forb := [], add := [], del := [⟨"coin", [.role 1]⟩] }, { req := [⟨"identity", []⟩], forb := [], add := [⟨"coin", [.role 1]⟩], del := [] }] }
def gc_s6 : Schema :=
  { name:= "redeem", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"coin", [.role 1]⟩, ⟨"coin", [.role 1]⟩], forb := [], add := [⟨"coin", [.avar 0]⟩, ⟨"knows", [.avar 0]⟩], del := [⟨"coin", [.role 1]⟩] }, { req := [⟨"identity", []⟩, ⟨"coin", [.avar 0]⟩, ⟨"coin", [.avar 0]⟩], forb := [], add := [⟨"coin", [.role 1]⟩], del := [⟨"coin", [.avar 0]⟩] }] }
def gc_certified : List (Schema × VolCert) := [(gc_s0, .connected [[]]), (gc_s1, .guarded [(0, []), (1, [])]), (gc_s2, .connected [[], [1]]), (gc_s3, .connected [[]]), (gc_s4, .connected [[], [1]]), (gc_s5, .connected [[], [1]]), (gc_s6, .connected [[], [1]])]

theorem gc_tp : (gc_certified.map Prod.fst).all tpCheck = true := by decide
theorem gc_vol : gc_certified.all (fun p => volCheck p.1 p.2) = true := by decide
/-- GC: in every reachable configuration, every enabled act lies within one instance,
or each of its participants shares an instance with one of its guards. -/
theorem gc_closure {Ag Sa : Type} {c : Config Ag Sa} (hr : Reach (gc_certified.map Prod.fst) c)
    (τ : Schema) (hτ : τ ∈ gc_certified.map Prod.fst) (b : Binding Ag Sa) (he : Enabled τ b c) :
    (∀ i j, i < τ.roles.length → j < τ.roles.length → Conn c.g (b.role i) (b.role j)) ∨
    (∀ i, i < τ.roles.length → ∃ g ∈ τ.guards, Conn c.g (b.role i) (b.role g)) :=
  closure_stamp gc_certified gc_tp gc_vol hr τ hτ b he

def gdo_s0 : Schema :=
  { name := "establish", guards := [0],
    roles := [{ req := [], forb := [⟨"identity", []⟩], add := [⟨"identity", []⟩], del := [] }] }
def gdo_s1 : Schema :=
  { name:= "acquaint", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 0]⟩], del := [] }] }
def gdo_s2 : Schema :=
  { name:= "introduce", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"knows", [.avar 0]⟩], forb := [], add := [], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [], add := [⟨"knows", [.avar 0]⟩], del := [] }] }
def gdo_s3 : Schema :=
  { name:= "befriend", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩], forb := [⟨"friend", [.role 1]⟩], add := [⟨"friend", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [⟨"friend", [.role 0]⟩], add := [⟨"friend", [.role 0]⟩], del := [] }] }
def gdo_s4 : Schema :=
  { name:= "unfriend", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"friend", [.role 1]⟩, ⟨"friend", [.role 1]⟩], forb := [], add := [], del := [⟨"friend", [.role 1]⟩] }, { req := [⟨"identity", []⟩, ⟨"friend", [.role 0]⟩, ⟨"friend", [.role 0]⟩], forb := [], add := [], del := [⟨"friend", [.role 0]⟩] }] }
def gdo_s5 : Schema :=
  { name:= "point_friend", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"friend", [.role 1]⟩], forb := [⟨"points_to", [.role 1]⟩], add := [⟨"points_to", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩], forb := [], add := [], del := [] }] }
def gdo_s6 : Schema :=
  { name:= "point_transitive", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.avar 0]⟩, ⟨"points_to", [.role 1]⟩], forb := [], add := [⟨"points_to", [.avar 0]⟩], del := [] }, { req := [⟨"identity", []⟩, ⟨"points_to", [.avar 0]⟩], forb := [], add := [], del := [] }] }
def gdo_s7 : Schema :=
  { name:= "unpoint", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"points_to", [.role 1]⟩, ⟨"points_to", [.role 1]⟩], forb := [], add := [], del := [⟨"points_to", [.role 1]⟩] }, { req := [⟨"identity", []⟩], forb := [], add := [], del := [] }] }
def gdo_certified : List (Schema × VolCert) := [(gdo_s0, .connected [[]]), (gdo_s1, .guarded [(0, []), (1, [])]), (gdo_s2, .connected [[], [1]]), (gdo_s3, .connected [[], [1]]), (gdo_s4, .connected [[], [1]]), (gdo_s5, .connected [[], [1]]), (gdo_s6, .connected [[], [1]]), (gdo_s7, .connected [[], [1]])]

theorem gdo_tp : (gdo_certified.map Prod.fst).all tpCheck = true := by decide
theorem gdo_vol : gdo_certified.all (fun p => volCheck p.1 p.2) = true := by decide
/-- GDO: in every reachable configuration, every enabled act lies within one instance,
or each of its participants shares an instance with one of its guards. -/
theorem gdo_closure {Ag Sa : Type} {c : Config Ag Sa} (hr : Reach (gdo_certified.map Prod.fst) c)
    (τ : Schema) (hτ : τ ∈ gdo_certified.map Prod.fst) (b : Binding Ag Sa) (he : Enabled τ b c) :
    (∀ i j, i < τ.roles.length → j < τ.roles.length → Conn c.g (b.role i) (b.role j)) ∨
    (∀ i, i < τ.roles.length → ∃ g ∈ τ.guards, Conn c.g (b.role i) (b.role g)) :=
  closure_stamp gdo_certified gdo_tp gdo_vol hr τ hτ b he

end GSCA
