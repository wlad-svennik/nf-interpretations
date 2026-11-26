module

public import HostTerm

@[expose] public section

set_option autoImplicit false

/-!
# The arithmetic of the numbers of a host

`HostTerm.lean` evaluates terms in a host through a structure of numbers `N` with a map onto
the numbers of the host and definable graphs of addition, multiplication and `2^x`
(`Host.Arith`). For `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙` the structure was the natural numbers of the model of NFU.

Here the structure is built in the host itself: `Host.Nm H` is the type of the numbers of `H`,
with addition, multiplication and `2^x` defined by iteration in the host (`ItV`: the value of
an iteration is read off a computation, a function on `b + 1`). It is a commutative semiring
with the facts `NFacts`, and **`Host.arithNm : H.Arith H.expN (fun i : H.Nm => i.1)`**.

The numbers of a host may be nonstandard, so every law is proved by induction in the host
(`om_ind`), for a definable predicate.
-/

namespace Host

variable {H : Host}

/-! ### Iteration of a definable step -/

/-- `f` is a computation of length `b` of the iteration of the step `S` from `c`. -/
def ItC (H : Host) (S : H.W → H.W → Prop) (f c b : H.W) : Prop :=
  (∃ sb, H.IsSuc sb b ∧ H.FunOn f sb) ∧ H.App f H.emp c ∧
    ∀ i u v si, i ∈ b → H.App f i u → H.IsSuc si i → H.App f si v → S u v

/-- `z` is the value after `b` steps of the iteration of `S` from `c`. -/
def ItV (H : Host) (S : H.W → H.W → Prop) (c b z : H.W) : Prop :=
  ∃ f, H.ItC S f c b ∧ H.App f b z

section iter

variable {S : H.W → H.W → Prop}

/-- The definition of a computation is written without the successor function, so that it can
be used in the graph of a function. This is what it says. -/
theorem itC_iff {f c b : H.W} : H.ItC S f c b ↔ (H.FunOn f (H.suc b) ∧ H.App f H.emp c ∧
    ∀ i u v, i ∈ b → H.App f i u → H.App f (H.suc i) v → S u v) := by
  constructor
  · rintro ⟨⟨sb, hsb, hf⟩, h0, hstep⟩
    rw [H.isSuc_iff.mp hsb] at hf
    exact ⟨hf, h0, fun i u v hi hu hv => hstep i u v _ hi hu (H.isSuc_iff.mpr rfl) hv⟩
  · rintro ⟨hf, h0, hstep⟩
    exact ⟨⟨_, H.isSuc_iff.mpr rfl, hf⟩, h0, fun i u v si hi hu hsi hv => by
      rw [H.isSuc_iff.mp hsi] at hv
      exact hstep i u v hi hu hv⟩

theorem itV_zero {c z : H.W} : H.ItV S c H.emp z ↔ z = c := by
  constructor
  · rintro ⟨f, hf, hz⟩
    have hf := H.itC_iff.mp hf
    exact hf.1.1.2 _ _ _ hz hf.2.1
  · rintro rfl
    refine ⟨H.ins H.emp H.emp z, H.itC_iff.mpr ⟨H.funOn_ins H.funOn_emp,
      H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩),
      fun i u v hi => (H.not_mem_emp i hi).elim⟩, H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩)⟩

theorem itV_succ {c b u v : H.W} (h : H.ItV S c b u) (hs : S u v) : H.ItV S c (H.suc b) v := by
  obtain ⟨f, hf, hu⟩ := h
  have hf := H.itC_iff.mp hf
  refine ⟨H.ins f (H.suc b) v, H.itC_iff.mpr ⟨H.funOn_ins hf.1, H.app_ins.mpr (Or.inl hf.2.1),
    fun i u' v' hi hu' hv' => ?_⟩, H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩)⟩
  have hu'f : H.App f i u' := by
    rcases H.app_ins.mp hu' with h1 | ⟨e, -⟩
    · exact h1
    · rw [e] at hi
      exact (H.mem_irrefl _ hi).elim
  rcases H.app_ins.mp hv' with h1 | ⟨e1, e2⟩
  · have hd : H.suc i ∈ H.suc b := (hf.1.2 _).mpr ⟨v', h1⟩
    rcases H.mem_suc.mp hi with hib | hib
    · exact hf.2.2 i u' v' hib hu'f h1
    · rw [hib] at hd
      exact (H.mem_irrefl _ hd).elim
  · have e : i = b := H.suc_inj e1
    rw [e] at hu'f
    rw [hf.1.1.2 _ _ _ hu'f hu, e2]
    exact hs

theorem itV_ex (hS : Def2 H S) (htot : ∀ u, ∃ v, S u v) (c : H.W) :
    ∀ b, b ∈ H.om → ∃ z, H.ItV S c b z :=
  H.om_ind (fun b => ∃ z, H.ItV S c b z) (by hdef) ⟨c, H.itV_zero.mpr rfl⟩
    (fun b _ ⟨z, hz⟩ => by
      obtain ⟨v, hv⟩ := htot z
      exact ⟨v, H.itV_succ hz hv⟩)

theorem itV_fun (hfun : ∀ u v v', S u v → S u v' → v = v') {c b : H.W} (hb : b ∈ H.om)
    {z z' : H.W} (h : H.ItV S c b z) (h' : H.ItV S c b z') : z = z' := by
  obtain ⟨f, hf, hz⟩ := h
  obtain ⟨f', hf', hz'⟩ := h'
  have hf := H.itC_iff.mp hf
  have hf' := H.itC_iff.mp hf'
  have key := H.om_ind (fun i => i ∈ H.suc b → ∀ u u', H.App f i u → H.App f' i u' → u = u')
    (by hdef)
    (fun _ u u' hu hu' => by
      rw [hf.1.1.2 _ _ _ hu hf.2.1, hf'.1.1.2 _ _ _ hu' hf'.2.1])
    (fun i _ ih hsi u u' hu hu' => by
      have hib : i ∈ b := by
        rcases H.mem_suc.mp hsi with h1 | h1
        · exact H.om_mem_trans hb h1 (H.mem_suc.mpr (Or.inr rfl))
        · rw [← h1]
          exact H.mem_suc.mpr (Or.inr rfl)
      have his : i ∈ H.suc b := H.mem_suc.mpr (Or.inl hib)
      obtain ⟨w, hw⟩ := (hf.1.2 i).mp his
      obtain ⟨w', hw'⟩ := (hf'.1.2 i).mp his
      have e := ih his w w' hw hw'
      rw [← e] at hw'
      exact hfun w u u' (hf.2.2 i w u hib hw hu) (hf'.2.2 i w u' hib hw' hu'))
  exact key b hb (H.mem_suc.mpr (Or.inr rfl)) z z' hz hz'

/-- The value of the iteration, as a function. -/
noncomputable def itW (H : Host) (S : H.W → H.W → Prop) (c b : H.W) : H.W :=
  open Classical in if h : ∃ z, H.ItV S c b z then Classical.choose h else H.emp

variable (hS : Def2 H S) (htot : ∀ u, ∃ v, S u v) (hfun : ∀ u v v', S u v → S u v' → v = v')
include hS htot hfun

theorem itV_iff {c b z : H.W} (hb : b ∈ H.om) : H.ItV S c b z ↔ z = H.itW S c b := by
  have hex := H.itV_ex hS htot c b hb
  have hsp : H.ItV S c b (H.itW S c b) := by
    unfold itW
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact ⟨fun h => H.itV_fun hfun hb h hsp, fun h => h ▸ hsp⟩

theorem itW_zero (c : H.W) : H.itW S c H.emp = c :=
  (H.itV_zero.mp ((H.itV_iff hS htot hfun H.emp_mem_om).mpr rfl))

theorem itW_succ {c b : H.W} (hb : b ∈ H.om) : S (H.itW S c b) (H.itW S c (H.suc b)) := by
  obtain ⟨v, hv⟩ := htot (H.itW S c b)
  have h1 := H.itV_succ ((H.itV_iff hS htot hfun hb).mpr rfl) hv
  rw [← (H.itV_iff hS htot hfun (H.suc_mem_om hb)).mp h1]
  exact hv

end iter

/-! ### Addition -/

/-- The step of addition. -/
def addS (H : Host) (u v : H.W) : Prop := H.IsSuc v u

theorem def_addS : Def2 H (fun u v => H.addS u v) := by hdef

theorem addS_tot (u : H.W) : ∃ v, H.addS u v := ⟨_, H.isSuc_iff.mpr rfl⟩

theorem addS_fun (u v v' : H.W) (h : H.addS u v) (h' : H.addS u v') : v = v' :=
  (H.isSuc_iff.mp h).trans (H.isSuc_iff.mp h').symm

/-- Addition on the numbers of the host (the empty set if `b` is not a number). -/
noncomputable def addW (H : Host) (a b : H.W) : H.W :=
  open Classical in if b ∈ H.om then H.itW H.addS a b else H.emp

def addW.graph (H : Host) (y a b : H.W) : Prop :=
  (b ∈ H.om ∧ H.ItV (fun u v => H.addS u v) a b y) ∨ (¬ b ∈ H.om ∧ y = H.emp)

theorem addW_graph {y a b : H.W} : Host.addW.graph H y a b ↔ y = H.addW a b := by
  unfold addW.graph addW
  by_cases hb : b ∈ H.om
  · rw [if_pos hb]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact (H.itV_iff H.def_addS H.addS_tot H.addS_fun hb).mp h
      · exact (h hb).elim
    · intro h
      exact Or.inl ⟨hb,
        (H.itV_iff H.def_addS H.addS_tot H.addS_fun hb).mpr h⟩
  · rw [if_neg hb]
    exact ⟨fun h => h.elim (fun h => (hb h.1).elim) (fun h => h.2), fun h => Or.inr ⟨hb, h⟩⟩

theorem addW.flat (H : Host) (a b : H.W) (Q : H.W → Prop) :
    (∃ y, Host.addW.graph H y a b ∧ Q y) ↔ Q (H.addW a b) :=
  ⟨fun ⟨y, hy, hQ⟩ => (H.addW_graph.mp hy) ▸ hQ, fun h => ⟨_, H.addW_graph.mpr rfl, h⟩⟩

theorem addW_zero (a : H.W) : H.addW a H.emp = a := by
  unfold addW
  rw [if_pos H.emp_mem_om]
  exact H.itW_zero H.def_addS H.addS_tot H.addS_fun a

theorem addW_suc (a : H.W) {b : H.W} (hb : b ∈ H.om) :
    H.addW a (H.suc b) = H.suc (H.addW a b) := by
  unfold addW
  rw [if_pos hb, if_pos (H.suc_mem_om hb)]
  exact H.isSuc_iff.mp (H.itW_succ H.def_addS H.addS_tot H.addS_fun hb)

theorem addW_om {a b : H.W} (ha : a ∈ H.om) (hb : b ∈ H.om) : H.addW a b ∈ H.om :=
  H.om_ind (fun b => H.addW a b ∈ H.om) (by hdef) (by rw [H.addW_zero]; exact ha)
    (fun b hb ih => by rw [H.addW_suc a hb]; exact H.suc_mem_om ih) b hb

theorem zero_addW {b : H.W} (hb : b ∈ H.om) : H.addW H.emp b = b :=
  H.om_ind (fun b => H.addW H.emp b = b) (by hdef) (H.addW_zero _)
    (fun b hb ih => by rw [H.addW_suc _ hb, ih]) b hb

theorem suc_addW (a : H.W) {b : H.W} (hb : b ∈ H.om) :
    H.addW (H.suc a) b = H.suc (H.addW a b) :=
  H.om_ind (fun b => H.addW (H.suc a) b = H.suc (H.addW a b)) (by hdef)
    (by rw [H.addW_zero, H.addW_zero])
    (fun b hb ih => by rw [H.addW_suc _ hb, H.addW_suc _ hb, ih]) b hb

theorem addW_comm {a b : H.W} (ha : a ∈ H.om) (hb : b ∈ H.om) : H.addW a b = H.addW b a :=
  H.om_ind (fun b => H.addW a b = H.addW b a) (by hdef)
    (by rw [H.addW_zero, H.zero_addW ha])
    (fun b hb ih => by rw [H.addW_suc _ hb, H.suc_addW _ ha, ih]) b hb

theorem addW_assoc (a : H.W) {b c : H.W} (hb : b ∈ H.om) (hc : c ∈ H.om) :
    H.addW (H.addW a b) c = H.addW a (H.addW b c) :=
  H.om_ind (fun c => H.addW (H.addW a b) c = H.addW a (H.addW b c)) (by hdef)
    (by rw [H.addW_zero, H.addW_zero])
    (fun c hc ih => by
      rw [H.addW_suc _ hc, H.addW_suc _ hc, H.addW_suc _ (H.addW_om hb hc), ih]) c hc

theorem addW_cancel {a b c : H.W} (hc : c ∈ H.om) (h : H.addW a c = H.addW b c) : a = b :=
  H.om_ind (fun c => H.addW a c = H.addW b c → a = b) (by hdef)
    (fun h => by rwa [H.addW_zero, H.addW_zero] at h)
    (fun c hc ih h => by
      rw [H.addW_suc _ hc, H.addW_suc _ hc] at h
      exact ih (H.suc_inj h)) c hc h

/-! ### Multiplication -/

/-- The step of multiplication by `a`. -/
def mulS (H : Host) (a u v : H.W) : Prop := Host.addW.graph H v u a

theorem def_mulS (a : H.W) : Def2 H (fun u v => H.mulS a u v) := by hdef

theorem mulS_tot (a u : H.W) : ∃ v, H.mulS a u v := ⟨_, H.addW_graph.mpr rfl⟩

theorem mulS_fun (a u v v' : H.W) (h : H.mulS a u v) (h' : H.mulS a u v') : v = v' :=
  (H.addW_graph.mp h).trans (H.addW_graph.mp h').symm

/-- Multiplication on the numbers of the host. -/
noncomputable def mulW (H : Host) (a b : H.W) : H.W :=
  open Classical in if b ∈ H.om then H.itW (H.mulS a) H.emp b else H.emp

def mulW.graph (H : Host) (y a b : H.W) : Prop :=
  (b ∈ H.om ∧ H.ItV (fun u v => H.mulS a u v) H.emp b y) ∨ (¬ b ∈ H.om ∧ y = H.emp)

theorem mulW_graph {y a b : H.W} : Host.mulW.graph H y a b ↔ y = H.mulW a b := by
  unfold mulW.graph mulW
  by_cases hb : b ∈ H.om
  · rw [if_pos hb]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact (H.itV_iff (H.def_mulS a) (H.mulS_tot a) (H.mulS_fun a) hb).mp h
      · exact (h hb).elim
    · intro h
      exact Or.inl ⟨hb, (H.itV_iff (H.def_mulS a) (H.mulS_tot a) (H.mulS_fun a) hb).mpr h⟩
  · rw [if_neg hb]
    exact ⟨fun h => h.elim (fun h => (hb h.1).elim) (fun h => h.2), fun h => Or.inr ⟨hb, h⟩⟩

theorem mulW.flat (H : Host) (a b : H.W) (Q : H.W → Prop) :
    (∃ y, Host.mulW.graph H y a b ∧ Q y) ↔ Q (H.mulW a b) :=
  ⟨fun ⟨y, hy, hQ⟩ => (H.mulW_graph.mp hy) ▸ hQ, fun h => ⟨_, H.mulW_graph.mpr rfl, h⟩⟩

theorem mulW_zero (a : H.W) : H.mulW a H.emp = H.emp := by
  unfold mulW
  rw [if_pos H.emp_mem_om]
  exact H.itW_zero (H.def_mulS a) (H.mulS_tot a) (H.mulS_fun a) _

theorem mulW_suc (a : H.W) {b : H.W} (hb : b ∈ H.om) :
    H.mulW a (H.suc b) = H.addW (H.mulW a b) a := by
  unfold mulW
  rw [if_pos hb, if_pos (H.suc_mem_om hb)]
  exact H.addW_graph.mp (H.itW_succ (H.def_mulS a) (H.mulS_tot a) (H.mulS_fun a) hb)

theorem mulW_om {a b : H.W} (ha : a ∈ H.om) (hb : b ∈ H.om) : H.mulW a b ∈ H.om :=
  H.om_ind (fun b => H.mulW a b ∈ H.om) (by hdef) (by rw [H.mulW_zero]; exact H.emp_mem_om)
    (fun b hb ih => by rw [H.mulW_suc a hb]; exact H.addW_om ih ha) b hb

theorem zero_mulW {b : H.W} (hb : b ∈ H.om) : H.mulW H.emp b = H.emp :=
  H.om_ind (fun b => H.mulW H.emp b = H.emp) (by hdef) (H.mulW_zero _)
    (fun b hb ih => by rw [H.mulW_suc _ hb, ih, H.addW_zero]) b hb

theorem suc_mulW {a b : H.W} (ha : a ∈ H.om) (hb : b ∈ H.om) :
    H.mulW (H.suc a) b = H.addW (H.mulW a b) b :=
  H.om_ind (fun b => H.mulW (H.suc a) b = H.addW (H.mulW a b) b) (by hdef)
    (by rw [H.mulW_zero, H.mulW_zero, H.addW_zero])
    (fun b hb ih => by
      have hm := H.mulW_om ha hb
      rw [H.mulW_suc _ hb, H.mulW_suc _ hb, ih, H.addW_suc _ ha, H.addW_suc _ hb,
        H.addW_assoc _ hb ha, H.addW_assoc _ ha hb, H.addW_comm ha hb]) b hb

theorem mulW_comm {a b : H.W} (ha : a ∈ H.om) (hb : b ∈ H.om) : H.mulW a b = H.mulW b a :=
  H.om_ind (fun b => H.mulW a b = H.mulW b a) (by hdef)
    (by rw [H.mulW_zero, H.zero_mulW ha])
    (fun b hb ih => by rw [H.mulW_suc _ hb, H.suc_mulW hb ha, ih]) b hb

theorem mulW_addW {a b c : H.W} (ha : a ∈ H.om) (hb : b ∈ H.om) (hc : c ∈ H.om) :
    H.mulW a (H.addW b c) = H.addW (H.mulW a b) (H.mulW a c) :=
  H.om_ind (fun c => H.mulW a (H.addW b c) = H.addW (H.mulW a b) (H.mulW a c)) (by hdef)
    (by rw [H.addW_zero, H.mulW_zero, H.addW_zero])
    (fun c hc ih => by
      rw [H.addW_suc _ hc, H.mulW_suc _ (H.addW_om hb hc), ih, H.mulW_suc _ hc,
        H.addW_assoc _ (H.mulW_om ha hc) ha]) c hc

theorem mulW_assoc {a b c : H.W} (ha : a ∈ H.om) (hb : b ∈ H.om) (hc : c ∈ H.om) :
    H.mulW (H.mulW a b) c = H.mulW a (H.mulW b c) :=
  H.om_ind (fun c => H.mulW (H.mulW a b) c = H.mulW a (H.mulW b c)) (by hdef)
    (by rw [H.mulW_zero, H.mulW_zero, H.mulW_zero])
    (fun c hc ih => by
      rw [H.mulW_suc _ hc, ih, H.mulW_suc _ hc, H.mulW_addW ha (H.mulW_om hb hc) hb]) c hc

theorem mulW_one {a : H.W} (ha : a ∈ H.om) : H.mulW a (H.suc H.emp) = a := by
  rw [H.mulW_suc _ H.emp_mem_om, H.mulW_zero, H.zero_addW ha]

/-! ### The function `2^x` -/

/-- The step of `2^x`. -/
def expS (H : Host) (u v : H.W) : Prop := Host.addW.graph H v u u

theorem def_expS : Def2 H (fun u v => H.expS u v) := by hdef

theorem expS_tot (u : H.W) : ∃ v, H.expS u v := ⟨_, H.addW_graph.mpr rfl⟩

theorem expS_fun (u v v' : H.W) (h : H.expS u v) (h' : H.expS u v') : v = v' :=
  (H.addW_graph.mp h).trans (H.addW_graph.mp h').symm

/-- `2^b` on the numbers of the host. -/
noncomputable def expW (H : Host) (b : H.W) : H.W :=
  open Classical in if b ∈ H.om then H.itW H.expS (H.suc H.emp) b else H.emp

def expW.graph (H : Host) (y b : H.W) : Prop :=
  (b ∈ H.om ∧ H.ItV (fun u v => H.expS u v) (H.suc H.emp) b y) ∨ (¬ b ∈ H.om ∧ y = H.emp)

theorem expW_graph {y b : H.W} : Host.expW.graph H y b ↔ y = H.expW b := by
  unfold expW.graph expW
  by_cases hb : b ∈ H.om
  · rw [if_pos hb]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact (H.itV_iff H.def_expS H.expS_tot H.expS_fun hb).mp h
      · exact (h hb).elim
    · intro h
      exact Or.inl ⟨hb,
        (H.itV_iff H.def_expS H.expS_tot H.expS_fun hb).mpr h⟩
  · rw [if_neg hb]
    exact ⟨fun h => h.elim (fun h => (hb h.1).elim) (fun h => h.2), fun h => Or.inr ⟨hb, h⟩⟩

theorem expW.flat (H : Host) (b : H.W) (Q : H.W → Prop) :
    (∃ y, Host.expW.graph H y b ∧ Q y) ↔ Q (H.expW b) :=
  ⟨fun ⟨y, hy, hQ⟩ => (H.expW_graph.mp hy) ▸ hQ, fun h => ⟨_, H.expW_graph.mpr rfl, h⟩⟩

theorem expW_zero : H.expW H.emp = H.suc H.emp := by
  unfold expW
  rw [if_pos H.emp_mem_om]
  exact H.itW_zero H.def_expS H.expS_tot H.expS_fun _

theorem expW_suc {b : H.W} (hb : b ∈ H.om) :
    H.expW (H.suc b) = H.addW (H.expW b) (H.expW b) := by
  unfold expW
  rw [if_pos hb, if_pos (H.suc_mem_om hb)]
  exact H.addW_graph.mp (H.itW_succ H.def_expS H.expS_tot H.expS_fun hb)

theorem expW_om {b : H.W} (hb : b ∈ H.om) : H.expW b ∈ H.om :=
  H.om_ind (fun b => H.expW b ∈ H.om) (by hdef)
    (by rw [H.expW_zero]; exact H.suc_mem_om H.emp_mem_om)
    (fun b hb ih => by rw [H.expW_suc hb]; exact H.addW_om ih ih) b hb

theorem expW_addW {a b : H.W} (ha : a ∈ H.om) (hb : b ∈ H.om) :
    H.expW (H.addW a b) = H.mulW (H.expW a) (H.expW b) :=
  H.om_ind (fun b => H.expW (H.addW a b) = H.mulW (H.expW a) (H.expW b)) (by hdef)
    (by rw [H.addW_zero, H.expW_zero, H.mulW_one (H.expW_om ha)])
    (fun b hb ih => by
      rw [H.addW_suc _ hb, H.expW_suc (H.addW_om ha hb), ih, H.expW_suc hb,
        H.mulW_addW (H.expW_om ha) (H.expW_om hb) (H.expW_om hb)]) b hb

/-- `1 ≤ 2^a`, with a witness. -/
theorem one_le_expW {a : H.W} (ha : a ∈ H.om) :
    ∃ c, c ∈ H.om ∧ H.addW (H.suc H.emp) c = H.expW a :=
  H.om_ind (fun a => ∃ c, c ∈ H.om ∧ H.addW (H.suc H.emp) c = H.expW a) (by hdef)
    ⟨H.emp, H.emp_mem_om, by rw [H.addW_zero, H.expW_zero]⟩
    (fun a ha ⟨c, hc, e⟩ => ⟨H.addW c (H.expW a), H.addW_om hc (H.expW_om ha), by
      rw [H.expW_suc ha, ← H.addW_assoc _ hc (H.expW_om ha), e]⟩) a ha

/-! ### The order -/

theorem le_addW {a : H.W} {c : H.W} (hc : c ∈ H.om) : a ∈ H.addW a c ∨ a = H.addW a c :=
  H.om_ind (fun c => a ∈ H.addW a c ∨ a = H.addW a c) (by hdef)
    (Or.inr (H.addW_zero a).symm)
    (fun c hc ih => by
      rw [H.addW_suc _ hc]
      rcases ih with h | h
      · exact Or.inl (H.mem_suc.mpr (Or.inl h))
      · exact Or.inl (H.mem_suc.mpr (Or.inr h))) c hc

theorem exists_addW {b : H.W} (hb : b ∈ H.om) :
    ∀ a, (a ∈ b ∨ a = b) → ∃ c, c ∈ H.om ∧ H.addW a c = b :=
  H.om_ind (fun b => ∀ a, (a ∈ b ∨ a = b) → ∃ c, c ∈ H.om ∧ H.addW a c = b) (by hdef)
    (fun a h => by
      rcases h with h | h
      · exact (H.not_mem_emp a h).elim
      · exact ⟨H.emp, H.emp_mem_om, by rw [H.addW_zero, h]⟩)
    (fun b _ ih a h => by
      rcases h with h | h
      · obtain ⟨c, hc, e⟩ := ih a (H.mem_suc.mp h)
        exact ⟨H.suc c, H.suc_mem_om hc, by rw [H.addW_suc _ hc, e]⟩
      · exact ⟨H.emp, H.emp_mem_om, by rw [H.addW_zero, h]⟩) b hb

/-! ### The structure of the numbers of a host -/

/-- The numbers of a host. -/
structure Nm (H : Host) where
  val : H.W
  prop : val ∈ H.om

namespace Nm

theorem ext {a b : Nm H} (h : a.1 = b.1) : a = b := by
  cases a
  cases b
  cases h
  rfl

noncomputable instance : Zero (Nm H) := ⟨⟨H.emp, H.emp_mem_om⟩⟩
noncomputable instance : One (Nm H) := ⟨⟨H.suc H.emp, H.suc_mem_om H.emp_mem_om⟩⟩
noncomputable instance : Add (Nm H) := ⟨fun a b => ⟨H.addW a.1 b.1, H.addW_om a.2 b.2⟩⟩
noncomputable instance : Mul (Nm H) := ⟨fun a b => ⟨H.mulW a.1 b.1, H.mulW_om a.2 b.2⟩⟩

theorem val_zero : (0 : Nm H).1 = H.emp := rfl

theorem val_one : (1 : Nm H).1 = H.suc H.emp := rfl

theorem val_add (a b : Nm H) : (a + b).1 = H.addW a.1 b.1 := rfl

theorem val_mul (a b : Nm H) : (a * b).1 = H.mulW a.1 b.1 := rfl

noncomputable instance : CommSemiring (Nm H) where
  add := (· + ·)
  zero := 0
  mul := (· * ·)
  one := 1
  add_assoc a b c := ext (H.addW_assoc a.1 b.2 c.2)
  zero_add a := ext (H.zero_addW a.2)
  add_zero a := ext (H.addW_zero a.1)
  add_comm a b := ext (H.addW_comm a.2 b.2)
  left_distrib a b c := ext (H.mulW_addW a.2 b.2 c.2)
  right_distrib a b c := ext (by
    show H.mulW (H.addW a.1 b.1) c.1 = H.addW (H.mulW a.1 c.1) (H.mulW b.1 c.1)
    rw [H.mulW_comm (H.addW_om a.2 b.2) c.2, H.mulW_addW c.2 a.2 b.2, H.mulW_comm c.2 a.2,
      H.mulW_comm c.2 b.2])
  zero_mul a := ext (H.zero_mulW a.2)
  mul_zero a := ext (H.mulW_zero a.1)
  mul_assoc a b c := ext (H.mulW_assoc a.2 b.2 c.2)
  one_mul a := ext (by
    show H.mulW (H.suc H.emp) a.1 = a.1
    rw [H.mulW_comm (H.suc_mem_om H.emp_mem_om) a.2, H.mulW_one a.2])
  mul_one a := ext (H.mulW_one a.2)
  mul_comm a b := ext (H.mulW_comm a.2 b.2)
  nsmul := nsmulRec
  npow := npowRec

instance : PartialOrder (Nm H) where
  le a b := a.1 ∈ b.1 ∨ a.1 = b.1
  le_refl a := Or.inr rfl
  le_trans a b c h h' := by
    rcases h' with h' | h'
    · rcases h with h | h
      · exact Or.inl (H.om_mem_trans c.2 h' h)
      · exact Or.inl (h ▸ h')
    · rcases h with h | h
      · exact Or.inl (h' ▸ h)
      · exact Or.inr (h.trans h')
  le_antisymm a b h h' := by
    rcases h with h | h
    · rcases h' with h' | h'
      · exact (H.mem_asymm h h').elim
      · exact ext h'.symm
    · exact ext h

theorem le_def {a b : Nm H} : a ≤ b ↔ a.1 ∈ b.1 ∨ a.1 = b.1 := Iff.rfl

theorem val_succ (a : Nm H) : (a + 1).1 = H.suc a.1 := by
  rw [val_add, val_one, H.addW_suc _ H.emp_mem_om, H.addW_zero]

theorem le_iff (a b : Nm H) : a ≤ b ↔ ∃ c, a + c = b := by
  constructor
  · intro h
    obtain ⟨c, hc, e⟩ := H.exists_addW b.2 a.1 h
    exact ⟨⟨c, hc⟩, ext e⟩
  · rintro ⟨c, rfl⟩
    exact H.le_addW c.2

theorem zero_le (a : Nm H) : 0 ≤ a := (le_iff 0 a).mpr ⟨a, zero_add a⟩

theorem cancel (a b c : Nm H) (h : a + c = b + c) : a = b :=
  ext (H.addW_cancel c.2 (congrArg Nm.val h))

theorem not_succ_le (a : Nm H) : ¬ a + 1 ≤ a := by
  intro h
  rw [le_def, val_succ] at h
  rcases h with h | h
  · exact H.mem_asymm h (H.mem_suc.mpr (Or.inr rfl))
  · exact H.mem_irrefl a.1 (by
      have : a.1 ∈ H.suc a.1 := H.mem_suc.mpr (Or.inr rfl)
      rwa [h] at this)

theorem succ_ne_zero (a : Nm H) : a + 1 ≠ 0 := fun h => not_succ_le a (h ▸ zero_le a)

theorem eq_or_succ_le (a b : Nm H) (h : a ≤ b) : a = b ∨ a + 1 ≤ b := by
  rcases h with h | h
  · refine Or.inr ?_
    rw [le_def, val_succ]
    exact H.suc_mem_or _ b.2 _ h
  · exact Or.inl (ext h)

theorem total (a b : Nm H) : a ≤ b ∨ b ≤ a := by
  rcases H.om_tri _ a.2 _ b.2 with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem zero_or_succ (a : Nm H) : a = 0 ∨ ∃ b, a = b + 1 := by
  rcases H.om_cases a.2 with h | ⟨m, hm, h⟩
  · exact Or.inl (ext h)
  · exact Or.inr ⟨⟨m, hm⟩, ext (by rw [val_succ]; exact h)⟩

/-- `2^x` on the numbers of the host. -/
noncomputable def expN (a : Nm H) : Nm H := ⟨H.expW a.1, H.expW_om a.2⟩

theorem add_ne_self (a k : Nm H) : a + (k + 1) ≠ a := by
  intro h
  have h1 : (k + 1) + a = 0 + a := by rw [zero_add, add_comm]; exact h
  exact succ_ne_zero k (cancel _ _ _ h1)

theorem cast_inj (a b : ℕ) (h : ((a : ℕ) : Nm H) = ((b : ℕ) : Nm H)) : a = b := by
  have key : ∀ a k : ℕ, ((a : ℕ) : Nm H) ≠ ((a + (k + 1) : ℕ) : Nm H) := by
    intro a k h
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one] at h
    exact add_ne_self _ _ h.symm
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨k, rfl⟩ : ∃ k, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
    exact key a k h
  · obtain ⟨k, rfl⟩ : ∃ k, a = b + (k + 1) := ⟨a - b - 1, by omega⟩
    exact key b k h.symm

theorem sq_lt {s s' : Nm H} (h : s + 1 ≤ s') : ∃ d, s * s + s + 1 + d = s' * s' := by
  obtain ⟨c, rfl⟩ := (le_iff _ _).mp h
  exact ⟨s + c * (s + 1 + c) + (s + 1) * c, by ring⟩

theorem pair_lt {x y x' y' : Nm H} (h : (x + y) + 1 ≤ x' + y') :
    (x + y) * (x + y) + x ≠ (x' + y') * (x' + y') + x' := by
  intro e
  obtain ⟨d, hd⟩ := sq_lt h
  rw [← hd] at e
  have e2 : (y + d + x' + 1) + ((x + y) * (x + y) + x) = 0 + ((x + y) * (x + y) + x) := by
    rw [zero_add]
    calc (y + d + x' + 1) + ((x + y) * (x + y) + x)
        = (x + y) * (x + y) + (x + y) + 1 + d + x' := by ring
      _ = (x + y) * (x + y) + x := e.symm
  exact succ_ne_zero _ (cancel _ _ _ e2)

theorem pair_inj (x y x' y' : Nm H)
    (h : (x + y) * (x + y) + x = (x' + y') * (x' + y') + x') : x = x' ∧ y = y' := by
  have hs : x + y = x' + y' := by
    rcases total (x + y) (x' + y') with h1 | h1
    · rcases eq_or_succ_le _ _ h1 with h2 | h2
      · exact h2
      · exact (pair_lt h2 h).elim
    · rcases eq_or_succ_le _ _ h1 with h2 | h2
      · exact h2.symm
      · exact (pair_lt h2 h.symm).elim
  rw [hs] at h
  have hx : x = x' := cancel x x' ((x' + y') * (x' + y')) (by
    rw [add_comm x _, add_comm x' ((x' + y') * (x' + y'))]; exact h)
  refine ⟨hx, ?_⟩
  rw [hx] at hs
  exact cancel y y' x' (by rw [add_comm y x', add_comm y' x']; exact hs)

theorem nfacts : NFacts (Nm H) expN where
  le_iff := le_iff
  total := total
  cancel := cancel
  not_succ_le := not_succ_le
  eq_or_succ_le := eq_or_succ_le
  zero_or_succ := zero_or_succ
  E_zero := ext H.expW_zero
  E_add := fun a b => ext (H.expW_addW a.2 b.2)
  E_one := by
    rw [← one_add_one_eq_two]
    refine ext ?_
    show H.expW (H.suc H.emp) = H.addW (H.suc H.emp) (H.suc H.emp)
    rw [H.expW_suc H.emp_mem_om, H.expW_zero]
  E_pos := fun a => by
    obtain ⟨c, hc, e⟩ := H.one_le_expW a.2
    exact (le_iff _ _).mpr ⟨⟨c, hc⟩, ext e⟩
  le_mul_self := fun z => by
    rcases zero_or_succ z with rfl | ⟨w, rfl⟩
    · exact zero_le _
    · exact (le_iff _ _).mpr ⟨(w + 1) * w, by ring⟩
  cast_inj := cast_inj
  pair_inj := pair_inj

theorem numIso : NumIso H (fun i : Nm H => i.1) where
  zero := rfl
  succ := val_succ
  inj := fun _ _ h => ext h
  onto := fun z => ⟨fun h => ⟨⟨z, h⟩, rfl⟩, fun ⟨i, h⟩ => h ▸ i.2⟩
  mem := fun i k => by
    rw [le_def, val_succ]
    constructor
    · exact H.suc_mem_or _ k.2 _
    · rintro (h | h)
      · exact H.om_mem_trans k.2 h (H.mem_suc.mpr (Or.inr rfl))
      · rw [← h]
        exact H.mem_suc.mpr (Or.inr rfl)

end Nm

/-- **The numbers of a host, with the arithmetic defined in the host, are a structure of
numbers for the evaluation of terms.** -/
theorem arithNm : H.Arith (N := Nm H) Nm.expN (fun i : Nm H => i.1) where
  iso := Nm.numIso
  nf := Nm.nfacts
  add := ⟨fun a b z => z = H.addW a b, by hdef, fun _ _ _ => Iff.rfl⟩
  mul := ⟨fun a b z => z = H.mulW a b, by hdef, fun _ _ _ => Iff.rfl⟩
  exp := ⟨fun a z => z = H.expW a, by hdef, fun _ _ => Iff.rfl⟩

end Host
