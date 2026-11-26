module

public import MHInternal

@[expose] public section

set_option autoImplicit false

/-!
# The arithmetic of the natural numbers of a model of `𝗠𝗛`, by formulas

The numbers of the hosts at the full heights of a model of `𝗠𝗛` are one ordered semiring
(`MHInternal.lean`). For the interpretation `𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗡𝗙𝗖` its operations have to be given by
formulas of `ℒₛₑₜ` that do not mention a host.

* `NumR x`: `x` is a finite ordinal (`numR_iff`: the members of `ω`).
* `AddR a b c`, `MulR a b c`: some set that contains the base triples, is closed under the
  recursion step and is the graph of a function contains the triple (`addR_iff`, `mulR_iff`:
  for numbers these are `c = a + b`, `c = a · b`).
* `nm_agree_ind`, `nm_least`: the two least number principles that the term model on a cut
  uses (`CutSys.agree_ind`, `CutSys.least`).
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

/-! ### The definitions, in every structure -/

section defs

variable {V : Type} [SetStructure V]

/-- `x` has no member, or is the successor of one of its members. -/
def ZS (x : V) : Prop := (∀ z, z ∈ x → False) ∨ ∃ z, z ∈ x ∧ SuccR x z

/-- `x` is a finite ordinal. -/
def NumR (x : V) : Prop := Ord x ∧ (ZS x ∧ ∀ y, y ∈ x → ZS y)

/-- The triple of `a`, `b`, `c` is in `G`. -/
def Tr3 (G a b c : V) : Prop := ∃ p, IsOp p a b ∧ Pr G p c

/-- `G` contains the graph of addition on the finite ordinals and is the graph of a function. -/
def AddG (G : V) : Prop :=
  (∀ a e : V, NumR a → (∀ z, z ∈ e → False) → Tr3 G a e a) ∧
  ((∀ a b c b' c' : V, Tr3 G a b c → SuccR b' b → SuccR c' c → Tr3 G a b' c') ∧
    ∀ a b c c' : V, Tr3 G a b c → Tr3 G a b c' → c = c')

/-- `G` contains the graph of multiplication on the finite ordinals and is the graph of a
function, where `GA` is a set for addition. -/
def MulG (G GA : V) : Prop :=
  (∀ a e : V, NumR a → (∀ z, z ∈ e → False) → Tr3 G a e e) ∧
  ((∀ a b c b' c' : V, Tr3 G a b c → SuccR b' b → Tr3 GA c a c' → Tr3 G a b' c') ∧
    ∀ a b c c' : V, Tr3 G a b c → Tr3 G a b c' → c = c')

/-- `c` is the sum of `a` and `b`. -/
def AddR (a b c : V) : Prop := ∃ G, AddG G ∧ Tr3 G a b c

/-- `c` is the product of `a` and `b`. -/
def MulR (a b c : V) : Prop := ∃ GA G, AddG GA ∧ (MulG G GA ∧ Tr3 G a b c)

end defs

def zsB : BDef (k := 1) (fun V _ v ↦ ZS (v 0)) :=
  ((BDef.ball 0 BDef.fls).or (BDef.bex 0 (succB.comp ![1, 0]))).congr fun _ _ _ => Iff.rfl

def numB : BDef (k := 1) (fun V _ v ↦ NumR (v 0)) :=
  ((ordB.comp ![0]).and ((zsB.comp ![0]).and (BDef.ball 0 (zsB.comp ![0])))).congr
    fun _ _ _ => Iff.rfl

def tr3F : FDef (k := 4) (fun V _ v ↦ Tr3 (v 0) (v 1) (v 2) (v 3)) :=
  (FDef.ex ((isOpB.toFDef.comp ![0, 2, 3]).and (prB.toFDef.comp ![1, 0, 4]))).congr
    fun _ _ _ => Iff.rfl

def addGF : FDef (k := 1) (fun V _ v ↦ AddG (v 0)) :=
  ((FDef.all (FDef.all ((numB.toFDef.comp ![1]).imp
      (((BDef.ball (k := 1) 0 BDef.fls).toFDef.comp ![0]).imp (tr3F.comp ![2, 1, 0, 1]))))).and
    ((FDef.all (FDef.all (FDef.all (FDef.all (FDef.all ((tr3F.comp ![5, 4, 3, 2]).imp
      ((succB.toFDef.comp ![1, 3]).imp ((succB.toFDef.comp ![0, 2]).imp
        (tr3F.comp ![5, 4, 1, 0]))))))))).and
    (FDef.all (FDef.all (FDef.all (FDef.all ((tr3F.comp ![4, 3, 2, 1]).imp
      ((tr3F.comp ![4, 3, 2, 0]).imp ((BDef.eq (k := 5) 1 0).toFDef))))))))).congr
    fun _ _ _ => Iff.rfl

def mulGF : FDef (k := 2) (fun V _ v ↦ MulG (v 0) (v 1)) :=
  ((FDef.all (FDef.all ((numB.toFDef.comp ![1]).imp
      (((BDef.ball (k := 1) 0 BDef.fls).toFDef.comp ![0]).imp (tr3F.comp ![2, 1, 0, 0]))))).and
    ((FDef.all (FDef.all (FDef.all (FDef.all (FDef.all ((tr3F.comp ![5, 4, 3, 2]).imp
      ((succB.toFDef.comp ![1, 3]).imp ((tr3F.comp ![6, 2, 4, 0]).imp
        (tr3F.comp ![5, 4, 1, 0]))))))))).and
    (FDef.all (FDef.all (FDef.all (FDef.all ((tr3F.comp ![4, 3, 2, 1]).imp
      ((tr3F.comp ![4, 3, 2, 0]).imp ((BDef.eq (k := 6) 1 0).toFDef))))))))).congr
    fun _ _ _ => Iff.rfl

def addRF : FDef (k := 3) (fun V _ v ↦ AddR (v 0) (v 1) (v 2)) :=
  (FDef.ex ((addGF.comp ![0]).and (tr3F.comp ![0, 1, 2, 3]))).congr fun _ _ _ => Iff.rfl

def mulRF : FDef (k := 3) (fun V _ v ↦ MulR (v 0) (v 1) (v 2)) :=
  (FDef.ex (FDef.ex ((addGF.comp ![1]).and ((mulGF.comp ![0, 1]).and
    (tr3F.comp ![0, 2, 3, 4]))))).congr fun _ _ _ => Iff.rfl

/-! ### In a model of `𝗠𝗛` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem zs_om {x : V} (hx : x ∈ (om : V)) : ZS x := by
  rcases om_cases hx with h | ⟨m, -, h⟩
  · exact Or.inl fun z hz => by
      rw [h] at hz
      exact absurd hz (by simp)
  · exact Or.inr ⟨m, by rw [h]; exact self_mem_sc m, succR_iff_sc.mpr h⟩

/-- **The finite ordinals are the members of `ω`.** -/
theorem numR_iff {x : V} : NumR x ↔ x ∈ (om : V) := by
  constructor
  · rintro ⟨hO, hz, hall⟩
    by_contra hx
    let Z : V := sepB (k := 1) (BDef.mem 0 1).not (sc x) ![(om : V)]
    have hZ : ∀ y, y ∈ Z ↔ y ∈ sc x ∧ ¬ y ∈ (om : V) := fun y => mem_sepB _ _ _ y
    obtain ⟨z, hzZ, hmin⟩ := ord_least Z (fun y hy => ord_mem (ord_sc hO) ((hZ y).mp hy).1)
      ⟨x, (hZ x).mpr ⟨self_mem_sc x, hx⟩⟩
    obtain ⟨hzs, hzo⟩ := (hZ z).mp hzZ
    have hzZS : ZS z := by
      rcases mem_sc.mp hzs with e | e
      · rw [e]
        exact hz
      · exact hall z e
    rcases hzZS with h | ⟨w, hw, hs⟩
    · apply hzo
      have : z = ∅ := mem_ext fun u => ⟨fun hu => (h u hu).elim, fun hu => absurd hu (by simp)⟩
      rw [this]
      exact empty_mem_om
    · have e : z = sc w := succR_iff_sc.mp hs
      have hws : w ∈ sc x := (ord_sc hO).1 z hzs w hw
      have hwo : w ∈ (om : V) := by
        by_contra hwn
        rcases hmin w ((hZ w).mpr ⟨hws, hwn⟩) with k | k
        · rw [k] at hw
          exact mem_irrefl _ hw
        · exact mem_asymm hw k
      apply hzo
      rw [e]
      exact sc_mem_om hwo
  · intro hx
    exact ⟨ord_mem ord_om hx, zs_om hx, fun y hy => zs_om (om_tr x hx y hy)⟩

theorem tr3_iff {G a b c : V} : Tr3 G a b c ↔ kp (kp a b) c ∈ G := by
  constructor
  · rintro ⟨p, hp, hpr⟩
    rw [isOp_iff.mp hp] at hpr
    exact pr_iff.mp hpr
  · intro h
    exact ⟨kp a b, isOp_kp a b, pr_iff.mpr h⟩

theorem tr3_pt {G a b c : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) :
    Tr3 G a b c ↔ Pt G (prodS (om : V) om) c a b := by
  constructor
  · rintro ⟨p, hp, hpr⟩
    refine ⟨p, ?_, hp, hpr⟩
    rw [isOp_iff.mp hp]
    exact mem_prodS.mpr ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨p, -, hp, hpr⟩
    exact ⟨p, hp, hpr⟩

variable {κ₀ : V} (h₀ : Full κ₀)

/-- The triples of the graph of an operation of the host. -/
theorem tr3_graph {G : (levHost h₀).W}
    {f : (levHost h₀).W → (levHost h₀).W → (levHost h₀).W}
    (hf : ∀ a b, a ∈ (levHost h₀).om → b ∈ (levHost h₀).om → f a b ∈ (levHost h₀).om)
    (hG : ∀ t, t ∈ G ↔ ∃ a b, a ∈ (levHost h₀).om ∧ b ∈ (levHost h₀).om ∧
      t = (levHost h₀).op ((levHost h₀).op a b) (f a b)) {a b c : V} :
    Tr3 (hval h₀ G) a b c ↔ ∃ a' b' : (levHost h₀).Nm,
      a = hval h₀ a'.val ∧ b = hval h₀ b'.val ∧ c = hval h₀ (f a'.val b'.val) := by
  have hmem : ∀ {x y : (levHost h₀).W}, x ∈ y → hval h₀ x ∈ hval h₀ y := fun h => h
  rw [tr3_iff]
  constructor
  · intro h
    obtain ⟨t, ht, htm⟩ := hlift h₀ h
    obtain ⟨a₀, b₀, ha₀, hb₀, rfl⟩ := (hG t).mp htm
    rw [op_val, op_val] at ht
    obtain ⟨e1, e2⟩ := kp_inj ht
    obtain ⟨e3, e4⟩ := kp_inj e1
    exact ⟨⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩, e3.symm, e4.symm, e2.symm⟩
  · rintro ⟨a', b', rfl, rfl, rfl⟩
    rw [← op_val, ← op_val]
    exact hmem ((hG _).mpr ⟨a'.val, b'.val, a'.prop, b'.prop, rfl⟩)

theorem tr3_add {a b c : V} :
    Tr3 (hval h₀ (levHost h₀).addG) a b c ↔ ∃ a' b' : (levHost h₀).Nm,
      a = hval h₀ a'.val ∧ b = hval h₀ b'.val ∧ c = hval h₀ (a' + b').val :=
  tr3_graph h₀ (fun _ _ ha hb => (levHost h₀).addW_om ha hb)
    (fun t => (levHost h₀).mem_addG (t := t))

theorem tr3_mul {a b c : V} :
    Tr3 (hval h₀ (levHost h₀).mulG) a b c ↔ ∃ a' b' : (levHost h₀).Nm,
      a = hval h₀ a'.val ∧ b = hval h₀ b'.val ∧ c = hval h₀ (a' * b').val :=
  tr3_graph h₀ (fun _ _ ha hb => (levHost h₀).mulW_om ha hb)
    (fun t => (levHost h₀).mem_mulG (t := t))

theorem emp_eq {e : V} (he : ∀ z, z ∈ e → False) : e = hval h₀ (0 : (levHost h₀).Nm).val := by
  rw [nv_zero]
  exact mem_ext fun u => ⟨fun hu => (he u hu).elim, fun hu => absurd hu (by simp)⟩

theorem succ_eq {x : V} {a : (levHost h₀).Nm} (h : SuccR x (hval h₀ a.val)) :
    x = hval h₀ (a + 1).val := by
  rw [nv_succ]
  exact succR_iff_sc.mp h

/-- The graph of addition of a host is a set for addition. -/
theorem addG_true : AddG (hval h₀ (levHost h₀).addG) := by
  refine ⟨fun a e ha he => ?_, fun a b c b' c' h hb hc => ?_, fun a b c c' h h' => ?_⟩
  · obtain ⟨a', rfl⟩ := nv_surj h₀ (numR_iff.mp ha)
    exact (tr3_add h₀).mpr ⟨a', 0, rfl, emp_eq h₀ he, by rw [add_zero]⟩
  · obtain ⟨a', b₁, rfl, rfl, rfl⟩ := (tr3_add h₀).mp h
    exact (tr3_add h₀).mpr ⟨a', b₁ + 1, rfl, succ_eq h₀ hb, by
      rw [succ_eq h₀ hc, add_assoc]⟩
  · obtain ⟨a₁, b₁, rfl, rfl, rfl⟩ := (tr3_add h₀).mp h
    obtain ⟨a₂, b₂, e1, e2, rfl⟩ := (tr3_add h₀).mp h'
    rw [nv_inj h₀ e1, nv_inj h₀ e2]

/-- A set for addition contains the graph of addition. -/
theorem addG_sub {G : V} (hG : AddG G) (a b : (levHost h₀).Nm) :
    Tr3 G (hval h₀ a.val) (hval h₀ b.val) (hval h₀ (a + b).val) := by
  have key := om_ind (k := 4)
    (BDef.ball 1 (BDef.ball 2 ((ptB.comp ![4, 6, 0, 1, 2]).imp (ptB.comp ![5, 6, 0, 1, 2]))))
    ![(om : V), hval h₀ (levHost h₀).addG, G, prodS (om : V) om]
    (fun x hx c hc h => by
      obtain ⟨a', rfl⟩ := nv_surj h₀ hx
      obtain ⟨a₁, b₁, e1, e2, rfl⟩ :=
        (tr3_add h₀).mp ((tr3_pt (nv_om h₀ a') empty_mem_om).mpr h)
      have eb : b₁ = 0 := nv_inj h₀ (e2.symm.trans (nv_zero h₀).symm)
      rw [← nv_inj h₀ e1, eb, add_zero]
      exact (tr3_pt (nv_om h₀ a') empty_mem_om).mp
        (hG.1 _ _ (numR_iff.mpr (nv_om h₀ a')) (fun z hz => absurd hz (by simp))))
    (fun n hn ih x hx c hc h => by
      obtain ⟨a', rfl⟩ := nv_surj h₀ hx
      obtain ⟨n', rfl⟩ := nv_surj h₀ hn
      obtain ⟨a₁, b₁, e1, e2, rfl⟩ :=
        (tr3_add h₀).mp ((tr3_pt (nv_om h₀ a') (sc_mem_om (nv_om h₀ n'))).mpr h)
      have eb : b₁ = n' + 1 := nv_inj h₀ (e2.symm.trans (nv_succ h₀ n').symm)
      rw [← nv_inj h₀ e1, eb]
      have h1 : Tr3 G (hval h₀ a'.val) (hval h₀ n'.val) (hval h₀ (a' + n').val) :=
        (tr3_pt (nv_om h₀ a') (nv_om h₀ n')).mpr (ih _ (nv_om h₀ a') _ (nv_om h₀ (a' + n'))
          ((tr3_pt (nv_om h₀ a') (nv_om h₀ n')).mp
            ((tr3_add h₀).mpr ⟨a', n', rfl, rfl, rfl⟩)))
      have h2 := hG.2.1 _ _ _ (sc (hval h₀ n'.val)) (sc (hval h₀ (a' + n').val)) h1
        (succR_iff_sc.mpr rfl) (succR_iff_sc.mpr rfl)
      rw [← nv_succ h₀ (a' + n'), add_assoc] at h2
      exact (tr3_pt (nv_om h₀ a') (sc_mem_om (nv_om h₀ n'))).mp h2)
    (hval h₀ b.val) (nv_om h₀ b) (hval h₀ a.val) (nv_om h₀ a) (hval h₀ (a + b).val)
    (nv_om h₀ (a + b))
    ((tr3_pt (nv_om h₀ a) (nv_om h₀ b)).mp ((tr3_add h₀).mpr ⟨a, b, rfl, rfl, rfl⟩))
  exact (tr3_pt (nv_om h₀ a) (nv_om h₀ b)).mpr key

theorem addG_iff {G : V} (hG : AddG G) {a b : (levHost h₀).Nm} {c : V} :
    Tr3 G (hval h₀ a.val) (hval h₀ b.val) c ↔ c = hval h₀ (a + b).val :=
  ⟨fun h => hG.2.2 _ _ _ _ h (addG_sub h₀ hG a b), fun h => h ▸ addG_sub h₀ hG a b⟩

/-- **`AddR` is the addition of the numbers.** -/
theorem addR_iff {a b : (levHost h₀).Nm} {c : V} :
    AddR (hval h₀ a.val) (hval h₀ b.val) c ↔ c = hval h₀ (a + b).val :=
  ⟨fun ⟨_, hG, h⟩ => (addG_iff h₀ hG).mp h,
    fun h => ⟨_, addG_true h₀, (addG_iff h₀ (addG_true h₀)).mpr h⟩⟩

/-- The graph of multiplication of a host is a set for multiplication. -/
theorem mulG_true : MulG (hval h₀ (levHost h₀).mulG) (hval h₀ (levHost h₀).addG) := by
  refine ⟨fun a e ha he => ?_, fun a b c b' c' h hb hc => ?_, fun a b c c' h h' => ?_⟩
  · obtain ⟨a', rfl⟩ := nv_surj h₀ (numR_iff.mp ha)
    exact (tr3_mul h₀).mpr ⟨a', 0, rfl, emp_eq h₀ he, by rw [mul_zero]; exact emp_eq h₀ he⟩
  · obtain ⟨a', b₁, rfl, rfl, rfl⟩ := (tr3_mul h₀).mp h
    have hc' := (addG_iff h₀ (addG_true h₀)).mp hc
    exact (tr3_mul h₀).mpr ⟨a', b₁ + 1, rfl, succ_eq h₀ hb, by
      rw [hc', mul_add, mul_one]⟩
  · obtain ⟨a₁, b₁, rfl, rfl, rfl⟩ := (tr3_mul h₀).mp h
    obtain ⟨a₂, b₂, e1, e2, rfl⟩ := (tr3_mul h₀).mp h'
    rw [nv_inj h₀ e1, nv_inj h₀ e2]

/-- A set for multiplication contains the graph of multiplication. -/
theorem mulG_sub {G GA : V} (hGA : AddG GA) (hG : MulG G GA) (a b : (levHost h₀).Nm) :
    Tr3 G (hval h₀ a.val) (hval h₀ b.val) (hval h₀ (a * b).val) := by
  have key := om_ind (k := 4)
    (BDef.ball 1 (BDef.ball 2 ((ptB.comp ![4, 6, 0, 1, 2]).imp (ptB.comp ![5, 6, 0, 1, 2]))))
    ![(om : V), hval h₀ (levHost h₀).mulG, G, prodS (om : V) om]
    (fun x hx c hc h => by
      obtain ⟨a', rfl⟩ := nv_surj h₀ hx
      obtain ⟨a₁, b₁, e1, e2, rfl⟩ :=
        (tr3_mul h₀).mp ((tr3_pt (nv_om h₀ a') empty_mem_om).mpr h)
      have eb : b₁ = 0 := nv_inj h₀ (e2.symm.trans (nv_zero h₀).symm)
      rw [eb, mul_zero, nv_zero]
      exact (tr3_pt (nv_om h₀ a') empty_mem_om).mp
        (hG.1 _ _ (numR_iff.mpr (nv_om h₀ a')) (fun z hz => absurd hz (by simp))))
    (fun n hn ih x hx c hc h => by
      obtain ⟨a', rfl⟩ := nv_surj h₀ hx
      obtain ⟨n', rfl⟩ := nv_surj h₀ hn
      obtain ⟨a₁, b₁, e1, e2, rfl⟩ :=
        (tr3_mul h₀).mp ((tr3_pt (nv_om h₀ a') (sc_mem_om (nv_om h₀ n'))).mpr h)
      have eb : b₁ = n' + 1 := nv_inj h₀ (e2.symm.trans (nv_succ h₀ n').symm)
      rw [← nv_inj h₀ e1, eb]
      have h1 : Tr3 G (hval h₀ a'.val) (hval h₀ n'.val) (hval h₀ (a' * n').val) :=
        (tr3_pt (nv_om h₀ a') (nv_om h₀ n')).mpr (ih _ (nv_om h₀ a') _ (nv_om h₀ (a' * n'))
          ((tr3_pt (nv_om h₀ a') (nv_om h₀ n')).mp
            ((tr3_mul h₀).mpr ⟨a', n', rfl, rfl, rfl⟩)))
      have h2 := hG.2.1 _ _ _ (sc (hval h₀ n'.val)) (hval h₀ (a' * n' + a').val) h1
        (succR_iff_sc.mpr rfl) (addG_sub h₀ hGA (a' * n') a')
      rw [mul_add, mul_one]
      exact (tr3_pt (nv_om h₀ a') (sc_mem_om (nv_om h₀ n'))).mp h2)
    (hval h₀ b.val) (nv_om h₀ b) (hval h₀ a.val) (nv_om h₀ a) (hval h₀ (a * b).val)
    (nv_om h₀ (a * b))
    ((tr3_pt (nv_om h₀ a) (nv_om h₀ b)).mp ((tr3_mul h₀).mpr ⟨a, b, rfl, rfl, rfl⟩))
  exact (tr3_pt (nv_om h₀ a) (nv_om h₀ b)).mpr key

/-- **`MulR` is the multiplication of the numbers.** -/
theorem mulR_iff {a b : (levHost h₀).Nm} {c : V} :
    MulR (hval h₀ a.val) (hval h₀ b.val) c ↔ c = hval h₀ (a * b).val :=
  ⟨fun ⟨_, _, hGA, hG, h⟩ => hG.2.2 _ _ _ _ h (mulG_sub h₀ hGA hG a b),
    fun h => ⟨_, _, addG_true h₀, mulG_true h₀, h ▸ mulG_sub h₀ (addG_true h₀) (mulG_true h₀) a b⟩⟩

/-- The numerals are the values of the standard numbers. -/
theorem isNum_nv_iff (k : ℕ) :
    ∀ w : V, IsNum k w ↔ w = hval h₀ ((k : ℕ) : (levHost h₀).Nm).val := by
  induction k with
  | zero =>
    intro w
    rw [Nat.cast_zero, nv_zero]
    exact ⟨fun h => mem_ext fun u => ⟨fun hu => (h u hu).elim, fun hu => absurd hu (by simp)⟩,
      fun h u hu => by
        rw [h] at hu
        exact absurd hu (by simp)⟩
  | succ k ih =>
    intro w
    rw [Nat.cast_succ, nv_succ]
    constructor
    · rintro ⟨m, -, hm, hs⟩
      rw [(ih m).mp hm] at hs
      exact succR_iff_sc.mp hs
    · intro h
      exact ⟨_, by rw [h]; exact self_mem_sc _, (ih _).mpr rfl, succR_iff_sc.mpr h⟩

/-! ### The least number principles -/

/-- **The least number principle for the disagreement of two sets below a number.** -/
theorem nm_agree_ind (s s' : V) (k : (levHost h₀).Nm)
    (hstep : ∀ i : (levHost h₀).Nm, i + 1 ≤ k →
      (∀ j : (levHost h₀).Nm, j + 1 ≤ i → (hval h₀ j.val ∈ s ↔ hval h₀ j.val ∈ s')) →
      (hval h₀ i.val ∈ s ↔ hval h₀ i.val ∈ s')) :
    ∀ i : (levHost h₀).Nm, i + 1 ≤ k → (hval h₀ i.val ∈ s ↔ hval h₀ i.val ∈ s') := by
  intro i hi
  by_contra hne
  have hkO : Ord (hval h₀ k.val) := ord_mem ord_om (nv_om h₀ k)
  let Z : V := sepB (k := 2) ((BDef.mem 0 1).iff (BDef.mem 0 2)).not (hval h₀ k.val) ![s, s']
  have hZ : ∀ y, y ∈ Z ↔ y ∈ hval h₀ k.val ∧ ¬ (y ∈ s ↔ y ∈ s') := fun y => mem_sepB _ _ _ y
  obtain ⟨z, hzZ, hmin⟩ := ord_least Z (fun y hy => ord_mem hkO ((hZ y).mp hy).1)
    ⟨_, (hZ _).mpr ⟨(nv_mem h₀).mpr hi, hne⟩⟩
  obtain ⟨hzk, hzn⟩ := (hZ z).mp hzZ
  obtain ⟨i₀, rfl⟩ := nv_surj h₀ (om_tr _ (nv_om h₀ k) _ hzk)
  refine hzn (hstep i₀ ((nv_mem h₀).mp hzk) fun j hj => ?_)
  have hjz : hval h₀ j.val ∈ hval h₀ i₀.val := (nv_mem h₀).mpr hj
  by_contra hjn
  rcases hmin _ ((hZ _).mpr ⟨hkO.1 _ hzk _ hjz, hjn⟩) with e | e
  · rw [e] at hjz
    exact mem_irrefl _ hjz
  · exact mem_asymm hjz e

/-- **The least number principle for the equality atoms with a given right side.** -/
theorem nm_least (s : V) (t : (levHost h₀).Nm) (ht : hval h₀ (aEq t t).val ∈ s) :
    ∃ m : (levHost h₀).Nm, m ≤ t ∧ hval h₀ (aEq m t).val ∈ s ∧
      ∀ m' : (levHost h₀).Nm, m' ≤ t → hval h₀ (aEq m' t).val ∈ s → m ≤ m' := by
  have ga : ∀ {a b : (levHost h₀).Nm} {c : V},
      Pt (hval h₀ (levHost h₀).addG) (prodS (om : V) om) c (hval h₀ a.val) (hval h₀ b.val) ↔
        c = hval h₀ (a + b).val := fun {a b c} =>
    (tr3_pt (nv_om h₀ a) (nv_om h₀ b)).symm.trans (addG_iff h₀ (addG_true h₀))
  have gm : ∀ {a b : (levHost h₀).Nm} {c : V},
      Pt (hval h₀ (levHost h₀).mulG) (prodS (om : V) om) c (hval h₀ a.val) (hval h₀ b.val) ↔
        c = hval h₀ (a * b).val := fun {a b c} =>
    (tr3_pt (nv_om h₀ a) (nv_om h₀ b)).symm.trans
      ⟨fun h => (mulG_true h₀).2.2 _ _ _ _ h (mulG_sub h₀ (addG_true h₀) (mulG_true h₀) a b),
        fun h => h ▸ mulG_sub h₀ (addG_true h₀) (mulG_true h₀) a b⟩
  let Z : V := sepB (k := 6)
    (BDef.bex 1 ((ptB.comp ![3, 5, 0, 1, 7]).and (BDef.bex 2 ((ptB.comp ![5, 6, 0, 1, 1]).and
      (BDef.bex 3 ((ptB.comp ![5, 7, 0, 1, 3]).and (BDef.bex 4 ((ptB.comp ![6, 8, 0, 1, 1]).and
        (BDef.bex 9 (succB.comp ![0, 1]))))))))))
    (sc (hval h₀ t.val))
    ![(om : V), hval h₀ (levHost h₀).addG, hval h₀ (levHost h₀).mulG, prodS (om : V) om, s,
      hval h₀ t.val]
  have hZ0 : ∀ x, x ∈ Z ↔ x ∈ sc (hval h₀ t.val) ∧ ∃ u, u ∈ (om : V) ∧
      (Pt (hval h₀ (levHost h₀).addG) (prodS (om : V) om) u x (hval h₀ t.val) ∧
      ∃ v, v ∈ (om : V) ∧ (Pt (hval h₀ (levHost h₀).mulG) (prodS (om : V) om) v u u ∧
      ∃ w, w ∈ (om : V) ∧ (Pt (hval h₀ (levHost h₀).addG) (prodS (om : V) om) w v x ∧
      ∃ y, y ∈ (om : V) ∧ (Pt (hval h₀ (levHost h₀).addG) (prodS (om : V) om) y w w ∧
      ∃ c, c ∈ s ∧ SuccR c y)))) := fun x => mem_sepB _ _ _ x
  have hZ : ∀ m : (levHost h₀).Nm, hval h₀ m.val ∈ Z ↔
      hval h₀ m.val ∈ sc (hval h₀ t.val) ∧ hval h₀ (aEq m t).val ∈ s := by
    intro m
    rw [hZ0]
    refine and_congr Iff.rfl ⟨?_, fun h => ?_⟩
    · rintro ⟨u, -, hu, v, -, hv, w, -, hw, y, -, hy, c, hc, hcy⟩
      rw [ga.mp hu] at hv
      rw [gm.mp hv] at hw
      rw [ga.mp hw] at hy
      rw [ga.mp hy] at hcy
      rw [succ_eq h₀ hcy] at hc
      exact hc
    · exact ⟨_, nv_om h₀ (m + t), ga.mpr rfl, _, nv_om h₀ ((m + t) * (m + t)), gm.mpr rfl, _,
        nv_om h₀ ((m + t) * (m + t) + m), ga.mpr rfl, _,
        nv_om h₀ ((m + t) * (m + t) + m + ((m + t) * (m + t) + m)), ga.mpr rfl, _, h,
        succR_iff_sc.mpr (nv_succ h₀ _)⟩
  have htO : Ord (sc (hval h₀ t.val)) := ord_sc (ord_mem ord_om (nv_om h₀ t))
  obtain ⟨z, hzZ, hmin⟩ := ord_least Z (fun y hy => ord_mem htO ((hZ0 y).mp hy).1)
    ⟨_, (hZ t).mpr ⟨self_mem_sc _, ht⟩⟩
  have hzs : z ∈ sc (hval h₀ t.val) := ((hZ0 z).mp hzZ).1
  have hle : ∀ m : (levHost h₀).Nm, hval h₀ m.val ∈ sc (hval h₀ t.val) ↔ m ≤ t := fun m =>
    mem_sc.trans ⟨fun h => h.elim (fun e => Or.inr (Subtype.ext e)) Or.inl,
      fun h => h.elim Or.inr (fun e => Or.inl (congrArg (hval h₀) e))⟩
  obtain ⟨m, rfl⟩ := nv_surj h₀ (om_tr _ (sc_mem_om (nv_om h₀ t)) _ hzs)
  refine ⟨m, (hle m).mp hzs, ((hZ m).mp hzZ).2, fun m' hm' hs' => ?_⟩
  rcases hmin _ ((hZ m').mpr ⟨(hle m').mpr hm', hs'⟩) with e | e
  · exact Or.inr (Subtype.ext e)
  · exact Or.inl e

end model

end MH

end FFL.FirstOrder.SetTheory
