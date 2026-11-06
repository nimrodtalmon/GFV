import GSCA.Basic
namespace GSCA
def gkk : Contract := [
  { name := "establish", guards := [0],
    roles := [{ req := [], forb := [⟨"identity", []⟩], add := [⟨"identity", []⟩], del := [] }] },
  { name := "acquaint", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 0]⟩], del := [] }] },
  { name := "introduce", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"knows", [.avar 0]⟩], forb := [], add := [], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [], add := [⟨"knows", [.avar 0]⟩], del := [] }] }]

theorem gkk_checked : gkk.all tpCheck = true := by decide
theorem gkk_records_within_instances {Ag Sa : Type} {c : Config Ag Sa} (hr : Reach gkk c) :
    ∀ p x q, x ∈ c.st p → Val.ag q ∈ x.args → Conn c.g p q := stamp gkk gkk_checked hr

def gsg : Contract := [
  { name := "establish", guards := [0],
    roles := [{ req := [], forb := [⟨"identity", []⟩], add := [⟨"identity", []⟩], del := [] }] },
  { name := "acquaint", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 0]⟩], del := [] }] },
  { name := "introduce", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"knows", [.avar 0]⟩], forb := [], add := [], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [], add := [⟨"knows", [.avar 0]⟩], del := [] }] },
  { name := "befriend", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩], forb := [⟨"friend", [.role 1]⟩], add := [⟨"friend", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [⟨"friend", [.role 0]⟩], add := [⟨"friend", [.role 0]⟩], del := [] }] },
  { name := "unfriend", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"friend", [.role 1]⟩, ⟨"friend", [.role 1]⟩], forb := [], add := [], del := [⟨"friend", [.role 1]⟩] }, { req := [⟨"identity", []⟩, ⟨"friend", [.role 0]⟩, ⟨"friend", [.role 0]⟩], forb := [], add := [], del := [⟨"friend", [.role 0]⟩] }] }]

theorem gsg_checked : gsg.all tpCheck = true := by decide
theorem gsg_records_within_instances {Ag Sa : Type} {c : Config Ag Sa} (hr : Reach gsg c) :
    ∀ p x q, x ∈ c.st p → Val.ag q ∈ x.args → Conn c.g p q := stamp gsg gsg_checked hr

def gc : Contract := [
  { name := "establish", guards := [0],
    roles := [{ req := [], forb := [⟨"identity", []⟩], add := [⟨"identity", []⟩], del := [] }] },
  { name := "acquaint", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 0]⟩], del := [] }] },
  { name := "introduce", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"knows", [.avar 0]⟩], forb := [], add := [], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [], add := [⟨"knows", [.avar 0]⟩], del := [] }] },
  { name := "mint", guards := [0],
    roles := [{ req := [⟨"identity", []⟩], forb := [], add := [⟨"coin", [.role 0]⟩], del := [] }] },
  { name := "swap", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"coin", [.avar 0]⟩, ⟨"coin", [.avar 0]⟩], forb := [], add := [⟨"coin", [.avar 1]⟩, ⟨"knows", [.avar 1]⟩], del := [⟨"coin", [.avar 0]⟩] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩, ⟨"coin", [.avar 1]⟩, ⟨"coin", [.avar 1]⟩], forb := [], add := [⟨"coin", [.avar 0]⟩, ⟨"knows", [.avar 0]⟩], del := [⟨"coin", [.avar 1]⟩] }] },
  { name := "pay", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"coin", [.role 1]⟩, ⟨"coin", [.role 1]⟩], forb := [], add := [], del := [⟨"coin", [.role 1]⟩] }, { req := [⟨"identity", []⟩], forb := [], add := [⟨"coin", [.role 1]⟩], del := [] }] },
  { name := "redeem", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"coin", [.role 1]⟩, ⟨"coin", [.role 1]⟩], forb := [], add := [⟨"coin", [.avar 0]⟩, ⟨"knows", [.avar 0]⟩], del := [⟨"coin", [.role 1]⟩] }, { req := [⟨"identity", []⟩, ⟨"coin", [.avar 0]⟩, ⟨"coin", [.avar 0]⟩], forb := [], add := [⟨"coin", [.role 1]⟩], del := [⟨"coin", [.avar 0]⟩] }] }]

theorem gc_checked : gc.all tpCheck = true := by decide
theorem gc_records_within_instances {Ag Sa : Type} {c : Config Ag Sa} (hr : Reach gc c) :
    ∀ p x q, x ∈ c.st p → Val.ag q ∈ x.args → Conn c.g p q := stamp gc gc_checked hr

def gdo : Contract := [
  { name := "establish", guards := [0],
    roles := [{ req := [], forb := [⟨"identity", []⟩], add := [⟨"identity", []⟩], del := [] }] },
  { name := "acquaint", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.role 0]⟩], del := [] }] },
  { name := "introduce", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩, ⟨"knows", [.avar 0]⟩], forb := [], add := [], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [], add := [⟨"knows", [.avar 0]⟩], del := [] }] },
  { name := "befriend", guards := [0, 1],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.role 1]⟩], forb := [⟨"friend", [.role 1]⟩], add := [⟨"friend", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩, ⟨"knows", [.role 0]⟩], forb := [⟨"friend", [.role 0]⟩], add := [⟨"friend", [.role 0]⟩], del := [] }] },
  { name := "unfriend", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"friend", [.role 1]⟩, ⟨"friend", [.role 1]⟩], forb := [], add := [], del := [⟨"friend", [.role 1]⟩] }, { req := [⟨"identity", []⟩, ⟨"friend", [.role 0]⟩, ⟨"friend", [.role 0]⟩], forb := [], add := [], del := [⟨"friend", [.role 0]⟩] }] },
  { name := "point_friend", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"friend", [.role 1]⟩], forb := [⟨"points_to", [.role 1]⟩], add := [⟨"points_to", [.role 1]⟩], del := [] }, { req := [⟨"identity", []⟩], forb := [], add := [], del := [] }] },
  { name := "point_transitive", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"knows", [.avar 0]⟩, ⟨"points_to", [.role 1]⟩], forb := [], add := [⟨"points_to", [.avar 0]⟩], del := [] }, { req := [⟨"identity", []⟩, ⟨"points_to", [.avar 0]⟩], forb := [], add := [], del := [] }] },
  { name := "unpoint", guards := [0],
    roles := [{ req := [⟨"identity", []⟩, ⟨"points_to", [.role 1]⟩, ⟨"points_to", [.role 1]⟩], forb := [], add := [], del := [⟨"points_to", [.role 1]⟩] }, { req := [⟨"identity", []⟩], forb := [], add := [], del := [] }] }]

theorem gdo_checked : gdo.all tpCheck = true := by decide
theorem gdo_records_within_instances {Ag Sa : Type} {c : Config Ag Sa} (hr : Reach gdo c) :
    ∀ p x q, x ∈ c.st p → Val.ag q ∈ x.args → Conn c.g p q := stamp gdo gdo_checked hr

/-- A contract with a "registry" act: Bob comes to know any c, with nobody to vouch for c. -/
def registry : Contract := [
  { name := "assign", guards := [0],
    roles := [{ req := [⟨"identity", []⟩], forb := [], add := [⟨"knows", [.avar 0]⟩], del := [] }] }]
theorem registry_rejected : registry.all tpCheck = false := by decide
end GSCA
