module

public import MGraphSep

@[expose] public section

set_option autoImplicit false

/-!
# The pointed graphs of a model of `𝗠` form a model of `𝗠𝗛`

Continues `MGraphSep.lean`. `V` is a model of `𝗠`.

* `exists_pairs`, `qg_rel`: for a set `P` of pairs of nodes of a graph, a class whose members
  are the ordered pairs, formed in `QG V`, of the classes of the two nodes of each pair in `P`.
* `colG`: one graph for all the well-founded relations `ρ` on the set `C` of the children of
  a point: the nodes are the pairs `⟨ρ, c⟩`, and `⟨ρ, a⟩` is a child of `⟨ρ, b⟩` when
  `⟨a, b⟩ ∈ ρ`. The class of the node `⟨ρ, c⟩` is the value at `c` of the collapse of `ρ`.
* **`qg_hc`**: the collapse axiom holds in `QG V`.
* **`qgModelsMH : (QG V) ⊧ 𝗠𝗛`**.
-/

namespace FFL.FirstOrder.SetTheory

namespace MG

open MH

section defs

variable {V : Type} [SetStructure V]

/-- `c` is a member of a member of `i`. -/
def UpCh (c i : V) : Prop := ∃ s, s ∈ i ∧ c ∈ s

/-- `c = ⟨N, j⟩` for `j = i`, or for `j = ⟨a, a⟩` where `i = ⟨a, b⟩`. -/
def OpCh (c i N : V) : Prop :=
  ∃ s, s ∈ c ∧ ∃ j, j ∈ s ∧ (IsOp c N j ∧ (j = i ∨
    ∃ t, t ∈ i ∧ ∃ a, a ∈ t ∧ ∃ b, b ∈ t ∧ (IsOp i a b ∧ IsOp j a a)))

/-- Every member of `PC` with a member has a member with no `ρ`-predecessor in it. -/
def WfRel (ρ PC : V) : Prop :=
  ∀ S, S ∈ PC → ((∃ z, z ∈ S ∧ ¬False) → ∃ m, m ∈ S ∧ ∀ c, c ∈ S → ¬Pr ρ c m)

/-- `x = ⟨N, ⟨ρ, a⟩⟩`. -/
def Nd (x N ρ a : V) : Prop := ∃ s, s ∈ x ∧ ∃ i, i ∈ s ∧ (IsOp i ρ a ∧ IsOp x N i)

/-- `⟨N, ⟨ρ, b⟩⟩ ∈ S`. -/
def NdIn (b S N ρ : V) : Prop := ∃ x, x ∈ S ∧ Nd x N ρ b

/-- `x = ⟨N, ⟨ρ, a⟩⟩` and `y = ⟨N, ⟨ρ, b⟩⟩` for a `ρ ∈ R` and a pair `⟨a, b⟩ ∈ ρ`. -/
def ColE (x y N R : V) : Prop :=
  ∃ ρ, ρ ∈ R ∧ ∃ e, e ∈ ρ ∧ ∃ s, s ∈ e ∧ ∃ a, a ∈ s ∧ ∃ b, b ∈ s ∧
    (IsOp e a b ∧ (Nd x N ρ a ∧ Nd y N ρ b))

/-- The class of the node `⟨N₁, z⟩` of `E₂` is a member of the class of `(Er, pr)`. -/
def RhoR (z N₁ M P E₂ Er pr : V) : Prop := ∃ n, n ∈ M ∧ (IsOp n N₁ z ∧ MemCh n P E₂ Er pr)

/-- `n = ⟨N, ⟨ρ, c⟩⟩`. -/
def FRel (c n N ρ : V) : Prop := Nd n N ρ c

end defs

def upChB : BDef (k := 2) (fun V _ v ↦ UpCh (v 0) (v 1)) :=
  (BDef.bex 1 (BDef.mem 1 0)).congr fun _ _ _ => Iff.rfl

def opChB : BDef (k := 3) (fun V _ v ↦ OpCh (v 0) (v 1) (v 2)) :=
  (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 4, 0]).and ((BDef.eq 0 3).or
    (BDef.bex 3 (BDef.bex 0 (BDef.bex 1 ((isOpB.comp ![6, 1, 0]).and
      (isOpB.comp ![3, 1, 1]))))))))).congr fun _ _ _ => Iff.rfl

def wfRelB : BDef (k := 2) (fun V _ v ↦ WfRel (v 0) (v 1)) :=
  (BDef.ball 1 ((BDef.bex 0 BDef.fls.not).imp
    (BDef.bex 0 (BDef.ball 1 (prB.comp ![3, 0, 1]).not)))).congr fun _ _ _ => Iff.rfl

def ndB : BDef (k := 4) (fun V _ v ↦ Nd (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![0, 4, 5]).and (isOpB.comp ![2, 3, 0])))).congr
    fun _ _ _ => Iff.rfl

def ndInB : BDef (k := 4) (fun V _ v ↦ NdIn (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.bex 1 (ndB.comp ![0, 3, 4, 1])).congr fun _ _ _ => Iff.rfl

def colEB : BDef (k := 4) (fun V _ v ↦ ColE (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.bex 3 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 1 ((isOpB.comp ![3, 1, 0]).and
    ((ndB.comp ![5, 7, 4, 1]).and (ndB.comp ![6, 7, 4, 0])))))))).congr fun _ _ _ => Iff.rfl

def rhoRB : BDef (k := 7)
    (fun V _ v ↦ RhoR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  (BDef.bex 2 ((isOpB.comp ![0, 2, 1]).and (memChB.comp ![0, 4, 5, 6, 7]))).congr
    fun _ _ _ => Iff.rfl

def fRelB : BDef (k := 4) (fun V _ v ↦ FRel (v 0) (v 1) (v 2) (v 3)) :=
  (ndB.comp ![1, 2, 3, 0]).congr fun _ _ _ => Iff.rfl

section pairs

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

theorem mem_kp {a b z : V} : z ∈ kp a b ↔ z = {a} ∨ z = {a, b} := by simp [kp]

/-- A set whose members are a singleton and a pair is an ordered pair. -/
theorem eq_kp_of {p s d x y : V} (hs : ∀ z, z ∈ s ↔ z = x) (hd : ∀ z, z ∈ d ↔ z = x ∨ z = y)
    (hp : ∀ z, z ∈ p ↔ z = s ∨ z = d) : p = kp x y := by
  have es : s = {x} := mem_ext fun z => by simp [hs]
  have ed : d = {x, y} := mem_ext fun z => by simp [hd]
  refine mem_ext fun z => ?_
  rw [hp, mem_kp, es, ed]

theorem upCh_kp {c a b : V} : UpCh c (kp a b) ↔ c = a ∨ c = b := by
  constructor
  · rintro ⟨s, hs, hc⟩
    rcases mem_kp.mp hs with e | e
    · rw [e] at hc
      exact Or.inl (by simpa using hc)
    · rw [e] at hc
      simpa using hc
  · intro h
    have h1 : ({a} : V) ∈ kp a b := mem_kp.mpr (Or.inl rfl)
    have h2 : ({a, b} : V) ∈ kp a b := mem_kp.mpr (Or.inr rfl)
    rcases h with e | e
    · exact ⟨{a}, h1, by simp [e]⟩
    · exact ⟨{a, b}, h2, by simp [e]⟩

theorem opCh_kp {c a b N : V} : OpCh c (kp a b) N ↔ c = kp N (kp a b) ∨ c = kp N (kp a a) := by
  constructor
  · rintro ⟨s, -, j, -, hop, h⟩
    have e := isOp_iff.mp hop
    rcases h with h | ⟨t, -, a', -, b', -, h1, h2⟩
    · rw [h] at e
      exact Or.inl e
    · obtain ⟨e1, -⟩ := kp_inj (isOp_iff.mp h1)
      rw [isOp_iff.mp h2, ← e1] at e
      exact Or.inr e
  · have h2 : ({a, b} : V) ∈ kp a b := mem_kp.mpr (Or.inr rfl)
    have ha : a ∈ ({a, b} : V) := by simp
    have hb : b ∈ ({a, b} : V) := by simp
    rintro (rfl | rfl)
    · obtain ⟨s, hs, hj⟩ := pr_snd_mem (isOp_kp N (kp a b))
      exact ⟨s, hs, kp a b, hj, isOp_kp _ _, Or.inl rfl⟩
    · obtain ⟨s, hs, hj⟩ := pr_snd_mem (isOp_kp N (kp a a))
      exact ⟨s, hs, kp a a, hj, isOp_kp _ _, Or.inr ⟨_, h2, a, ha, b, hb, isOp_kp a b,
        isOp_kp a a⟩⟩

theorem nd_iff {x N ρ a : V} : Nd x N ρ a ↔ x = kp N (kp ρ a) := by
  constructor
  · rintro ⟨s, -, i, -, h1, h2⟩
    have e := isOp_iff.mp h2
    rw [isOp_iff.mp h1] at e
    exact e
  · intro e
    obtain ⟨s, hs, hi⟩ := pr_snd_mem (isOp_kp N (kp ρ a))
    rw [e]
    exact ⟨s, hs, kp ρ a, hi, isOp_kp ρ a, isOp_kp N (kp ρ a)⟩

/-! ### Ordered pairs of classes -/

/-- The children relation for the unordered pairs: `c` is a component of `i`. -/
noncomputable def upG (N : V) : V := relB (k := 0) upChB N (prodS N N) ![]

theorem pr_upG {N c i : V} : Pr (upG N) c i ↔ c ∈ N ∧ i ∈ prodS N N ∧ UpCh c i :=
  pr_relB upChB N (prodS N N) ![] c i

/-- The children relation for the ordered pairs. -/
noncomputable def opG (N N₁ P : V) : V := relB (k := 1) opChB N₁ P ![N]

theorem pr_opG {N N₁ P c i : V} : Pr (opG N N₁ P) c i ↔ c ∈ N₁ ∧ i ∈ P ∧ OpCh c i N :=
  pr_relB opChB N₁ P ![N] c i

/-- **A graph with a node for each pair in `P`**, whose class is the ordered pair of the
classes of the two nodes; the members of the class of the graph are these ordered pairs. -/
theorem exists_pairs (g : PG V) (N : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N) (P : V)
    (hP : ∀ z, z ∈ P → z ∈ prodS N N) :
    ∃ (g₂ : PG V) (N₁ : V),
      (∀ a b, kp a b ∈ P → kp N₁ (kp a b) ∈ nodes g₂ ∧
        mkQ (g₂.at (kp N₁ (kp a b))) = kp (mkQ (g.at a)) (mkQ (g.at b))) ∧
      ∀ x : QG V, x ∈ mkQ g₂ ↔ ∃ i, i ∈ P ∧ x = mkQ (g₂.at (kp N₁ i)) := by
  let I : V := prodS N N
  let g₁ : PG V := g.adj (upG N) I N hN
  have h1 : ∀ a b, a ∈ N → b ∈ N → ∀ x : QG V,
      x ∈ mkQ (g₁.at (kp N (kp a b))) ↔ x = mkQ (g.at a) ∨ x = mkQ (g.at b) := by
    intro a b ha hb x
    have hab : kp a b ∈ I := mem_prodS.mpr ⟨a, ha, b, hb, rfl⟩
    refine (mem_adj_new g (upG N) I N hN).trans ⟨?_, ?_⟩
    · rintro ⟨c, -, -, hch, e⟩
      rcases upCh_kp.mp (pr_upG.mp hch).2.2 with e' | e'
      · rw [e'] at e
        exact Or.inl e
      · rw [e'] at e
        exact Or.inr e
    · rintro (e | e)
      · exact ⟨a, ha, hab, pr_upG.mpr ⟨ha, hab, upCh_kp.mpr (Or.inl rfl)⟩, e⟩
      · exact ⟨b, hb, hab, pr_upG.mpr ⟨hb, hab, upCh_kp.mpr (Or.inr rfl)⟩, e⟩
  let N₁ : V := nodes g₁
  have hN₁ : ∀ c x, Pr g₁.E c x → c ∈ N₁ ∧ x ∈ N₁ := nodes_ok g₁
  have hin : ∀ i, i ∈ I → kp N i ∈ N₁ := fun i hi =>
    (hN₁ _ _ ((pr_adj_top hN).mpr ⟨i, hi, rfl⟩)).1
  let g₂ : PG V := g₁.adj (opG N N₁ P) P N₁ hN₁
  have h2 : ∀ a b, a ∈ N → b ∈ N → kp a b ∈ P → ∀ x : QG V,
      x ∈ mkQ (g₂.at (kp N₁ (kp a b))) ↔
        x = mkQ (g₁.at (kp N (kp a a))) ∨ x = mkQ (g₁.at (kp N (kp a b))) := by
    intro a b ha hb hab x
    have haa : kp N (kp a a) ∈ N₁ := hin _ (mem_prodS.mpr ⟨a, ha, a, ha, rfl⟩)
    have hab' : kp N (kp a b) ∈ N₁ := hin _ (mem_prodS.mpr ⟨a, ha, b, hb, rfl⟩)
    refine (mem_adj_new g₁ (opG N N₁ P) P N₁ hN₁).trans ⟨?_, ?_⟩
    · rintro ⟨c, -, -, hch, e⟩
      rcases opCh_kp.mp (pr_opG.mp hch).2.2 with e' | e'
      · rw [e'] at e
        exact Or.inr e
      · rw [e'] at e
        exact Or.inl e
    · rintro (e | e)
      · exact ⟨_, haa, hab, pr_opG.mpr ⟨haa, hab, opCh_kp.mpr (Or.inr rfl)⟩, e⟩
      · exact ⟨_, hab', hab, pr_opG.mpr ⟨hab', hab, opCh_kp.mpr (Or.inl rfl)⟩, e⟩
  refine ⟨g₂, N₁, fun a b hab => ?_, fun x => mem_adj_top g₁ (opG N N₁ P) P N₁ hN₁⟩
  obtain ⟨a', ha, b', hb, e⟩ := mem_prodS.mp (hP _ hab)
  obtain ⟨e1, e2⟩ := kp_inj e
  rw [← e1] at ha
  rw [← e2] at hb
  refine ⟨(nodes_ok g₂ _ _ ((pr_adj_top hN₁).mpr ⟨kp a b, hab, rfl⟩)).1, ?_⟩
  exact eq_kp_of (fun z => (h1 a a ha ha z).trans or_self_iff) (h1 a b ha hb) (h2 a b ha hb hab)

/-- **A class of ordered pairs** of classes of nodes, for any set of pairs of nodes. -/
theorem qg_rel (g : PG V) (N : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N) (P : V)
    (hP : ∀ z, z ∈ P → z ∈ prodS N N) :
    ∃ R : QG V, ∀ x y : QG V,
      Pr R x y ↔ ∃ a b, kp a b ∈ P ∧ (x = mkQ (g.at a) ∧ y = mkQ (g.at b)) := by
  obtain ⟨g₂, N₁, h1, h2⟩ := exists_pairs g N hN P hP
  refine ⟨mkQ g₂, fun x y => ?_⟩
  rw [pr_iff, h2]
  constructor
  · rintro ⟨i, hi, e⟩
    obtain ⟨a, -, b, -, rfl⟩ := mem_prodS.mp (hP i hi)
    rw [(h1 a b hi).2] at e
    obtain ⟨e1, e2⟩ := kp_inj e
    exact ⟨a, b, hi, e1, e2⟩
  · rintro ⟨a, b, hab, e1, e2⟩
    rw [e1, e2]
    exact ⟨kp a b, hab, ((h1 a b hab).2).symm⟩

/-! ### The graph of the well-founded relations on a set -/

/-- The well-founded relations on `C`. -/
noncomputable def wfRels (C : V) : V := sepB (k := 1) wfRelB (℘ (prodS C C)) ![℘ C]

theorem mem_wfRels {C ρ : V} : ρ ∈ wfRels C ↔ (∀ z, z ∈ ρ → z ∈ prodS C C) ∧
    ∀ S : V, (∀ z, z ∈ S → z ∈ C) → (∃ z, z ∈ S) → ∃ m, m ∈ S ∧ ∀ c, c ∈ S → ¬Pr ρ c m := by
  have h0 : ρ ∈ wfRels C ↔ ρ ∈ ℘ (prodS C C) ∧ WfRel ρ (℘ C) := mem_sepB wfRelB _ _ ρ
  rw [h0]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun z hz => mem_power_iff.mp h1 z hz, fun S hS ⟨z, hz⟩ =>
      h2 S (mem_power_iff.mpr hS) ⟨z, hz, not_false⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mem_power_iff.mpr h1, fun S hS ⟨z, hz, _⟩ =>
      h2 S (fun w hw => mem_power_iff.mp hS w hw) ⟨z, hz⟩⟩

theorem wfRels_dom {C ρ a b : V} (hρ : ρ ∈ wfRels C) (h : Pr ρ a b) : a ∈ C ∧ b ∈ C := by
  obtain ⟨a', ha, b', hb, e⟩ := mem_prodS.mp ((mem_wfRels.mp hρ).1 _ (pr_iff.mp h))
  obtain ⟨e1, e2⟩ := kp_inj e
  rw [← e1] at ha
  rw [← e2] at hb
  exact ⟨ha, hb⟩

theorem col_iff {x y N R : V} : ColE x y N R ↔
    ∃ ρ a b, ρ ∈ R ∧ (Pr ρ a b ∧ (x = kp N (kp ρ a) ∧ y = kp N (kp ρ b))) := by
  constructor
  · rintro ⟨ρ, hρ, e, he, s, -, a, -, b, -, hop, hx, hy⟩
    exact ⟨ρ, a, b, hρ, ⟨e, he, hop⟩, nd_iff.mp hx, nd_iff.mp hy⟩
  · rintro ⟨ρ, a, b, hρ, hpr, hx, hy⟩
    have h2 : ({a, b} : V) ∈ kp a b := mem_kp.mpr (Or.inr rfl)
    have ha : a ∈ ({a, b} : V) := by simp
    have hb : b ∈ ({a, b} : V) := by simp
    exact ⟨ρ, hρ, kp a b, pr_iff.mp hpr, _, h2, a, ha, b, hb, isOp_kp a b, nd_iff.mpr hx,
      nd_iff.mpr hy⟩

/-- The edges between the nodes `⟨N, ⟨ρ, c⟩⟩`, for the well-founded relations `ρ` on `C`. -/
noncomputable def colG (N C : V) : V :=
  relB (k := 2) colEB (tg N (prodS (wfRels C) C)) (tg N (prodS (wfRels C) C)) ![N, wfRels C]

theorem pr_colG {N C x y : V} : Pr (colG N C) x y ↔
    ∃ ρ a b, ρ ∈ wfRels C ∧ (Pr ρ a b ∧ (x = kp N (kp ρ a) ∧ y = kp N (kp ρ b))) := by
  have h0 : Pr (colG N C) x y ↔ x ∈ tg N (prodS (wfRels C) C) ∧
      y ∈ tg N (prodS (wfRels C) C) ∧ ColE x y N (wfRels C) :=
    pr_relB colEB _ _ ![N, wfRels C] x y
  rw [h0, col_iff]
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · rintro ⟨ρ, a, b, hρ, hpr, hx, hy⟩
    obtain ⟨ha, hb⟩ := wfRels_dom hρ hpr
    refine ⟨?_, ?_, ρ, a, b, hρ, hpr, hx, hy⟩
    · rw [hx]
      exact mem_tg.mpr ⟨kp ρ a, mem_prodS.mpr ⟨ρ, hρ, a, ha, rfl⟩, rfl⟩
    · rw [hy]
      exact mem_tg.mpr ⟨kp ρ b, mem_prodS.mpr ⟨ρ, hρ, b, hb, rfl⟩, rfl⟩

theorem colG_target {N C c x : V} (h : Pr (colG N C) c x) : x ∉ N := by
  obtain ⟨ρ, a, b, -, -, -, e⟩ := pr_colG.mp h
  rw [e]
  exact kp_fresh N _

theorem colG_wf (N C : V) : WFG (colG N C) := by
  intro S hS
  by_cases h : ∃ ρ b, ρ ∈ wfRels C ∧ (b ∈ C ∧ kp N (kp ρ b) ∈ S)
  · obtain ⟨ρ, b, hρ, hb, hbS⟩ := h
    let Sρ : V := sepB (k := 3) ndInB C ![S, N, ρ]
    have h0 : ∀ b, b ∈ Sρ ↔ b ∈ C ∧ NdIn b S N ρ := fun b => mem_sepB ndInB C ![S, N, ρ] b
    have hSρ : ∀ b, b ∈ Sρ ↔ b ∈ C ∧ kp N (kp ρ b) ∈ S := by
      intro b
      rw [h0]
      refine and_congr_right fun _ => ⟨?_, fun k => ⟨_, k, nd_iff.mpr rfl⟩⟩
      rintro ⟨x, hx, hnd⟩
      rw [← nd_iff.mp hnd]
      exact hx
    obtain ⟨m, hm, hmin⟩ := (mem_wfRels.mp hρ).2 Sρ (fun z hz => ((hSρ z).mp hz).1)
      ⟨b, (hSρ b).mpr ⟨hb, hbS⟩⟩
    refine ⟨kp N (kp ρ m), ((hSρ m).mp hm).2, fun c hc hcm => ?_⟩
    obtain ⟨ρ', a, b', hρ', hpr, ec, e⟩ := pr_colG.mp hcm
    obtain ⟨-, e2⟩ := kp_inj e
    obtain ⟨e3, e4⟩ := kp_inj e2
    rw [← e3] at hpr ec
    rw [← e4] at hpr
    rw [ec] at hc
    exact hmin a ((hSρ a).mpr ⟨(wfRels_dom hρ hpr).1, hc⟩) hpr
  · obtain ⟨m, hm⟩ := hS
    refine ⟨m, hm, fun c hc hcm => h ?_⟩
    obtain ⟨ρ, a, b, hρ, hpr, -, e⟩ := pr_colG.mp hcm
    rw [e] at hm
    exact ⟨ρ, b, hρ, (wfRels_dom hρ hpr).2, hm⟩

/-- The graph of `g` together with the graph of the well-founded relations on `C`. -/
noncomputable def PG.col (g : PG V) (N C : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N) : PG V :=
  ⟨g.E ∪ colG N C, g.p, wfg_union g.wf (colG_wf N C) hN fun _ _ h => colG_target h⟩

theorem col_old (g : PG V) (N C : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N) {a : V}
    (ha : a ∈ N) : mkQ ((g.col N C hN).at a) = mkQ (g.at a) :=
  mkQ_eq.mpr (bis_union_old hN (fun _ _ h => colG_target h) ha)

/-- **The members of the class of the node `⟨ρ, c⟩`** are the classes of the nodes `⟨ρ, a⟩`
for the pairs `⟨a, c⟩ ∈ ρ`. -/
theorem mem_col_new (g : PG V) (N C : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N) {ρ c : V}
    (hρ : ρ ∈ wfRels C) {x : QG V} :
    x ∈ mkQ ((g.col N C hN).at (kp N (kp ρ c))) ↔
      ∃ a, Pr ρ a c ∧ x = mkQ ((g.col N C hN).at (kp N (kp ρ a))) := by
  rw [mem_mkQ]
  constructor
  · rintro ⟨d, hd, e⟩
    rcases pr_union.mp hd with k | k
    · exact absurd (hN _ _ k).2 (kp_fresh N _)
    · obtain ⟨ρ', a, b, -, hpr, ed, e'⟩ := pr_colG.mp k
      obtain ⟨-, e2⟩ := kp_inj e'
      obtain ⟨e3, e4⟩ := kp_inj e2
      rw [← e3] at hpr ed
      rw [← e4] at hpr
      rw [ed] at e
      exact ⟨a, hpr, e⟩
  · rintro ⟨a, ha, e⟩
    exact ⟨kp N (kp ρ a), pr_union.mpr (Or.inr (pr_colG.mpr ⟨ρ, a, c, hρ, ha, rfl, rfl⟩)), e⟩

/-- A set of pairs of children that represents the relation `r` of `QG V`. -/
theorem exists_rho (g : PG V) (N : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N) (C : V)
    (hCN : ∀ c, c ∈ C → c ∈ N) (r : QG V) :
    ∃ ρ : V, (∀ z, z ∈ ρ → z ∈ prodS C C) ∧
      ∀ a b, Pr ρ a b ↔ a ∈ C ∧ (b ∈ C ∧ Pr r (mkQ (g.at a)) (mkQ (g.at b))) := by
  obtain ⟨gr, rfl⟩ := exists_rep r
  have hP : ∀ z, z ∈ prodS C C → z ∈ prodS N N := by
    intro z hz
    obtain ⟨a, ha, b, hb, e⟩ := mem_prodS.mp hz
    exact mem_prodS.mpr ⟨a, hCN a ha, b, hCN b hb, e⟩
  obtain ⟨g₂, N₁, h1, -⟩ := exists_pairs g N hN (prodS C C) hP
  let P' : V := ℘ (prodS (nodes g₂) (nodes gr))
  let ρ : V := sepB (k := 6) rhoRB (prodS C C) ![N₁, nodes g₂, P', g₂.E, gr.E, gr.p]
  have h0 : ∀ z, z ∈ ρ ↔ z ∈ prodS C C ∧ RhoR z N₁ (nodes g₂) P' g₂.E gr.E gr.p :=
    fun z => mem_sepB rhoRB _ _ z
  refine ⟨ρ, fun z hz => ((h0 z).mp hz).1, fun a b => ?_⟩
  rw [pr_iff, h0]
  constructor
  · rintro ⟨hab, n, -, hop, hm⟩
    obtain ⟨a', ha, b', hb, e⟩ := mem_prodS.mp hab
    obtain ⟨e1, e2⟩ := kp_inj e
    rw [← e1] at ha
    rw [← e2] at hb
    rw [isOp_iff.mp hop] at hm
    have h3 := (memCh_iff g₂ gr (h1 a b hab).1).mp hm
    rw [(h1 a b hab).2] at h3
    exact ⟨ha, hb, pr_iff.mpr h3⟩
  · rintro ⟨ha, hb, hr⟩
    have hab : kp a b ∈ prodS C C := mem_prodS.mpr ⟨a, ha, b, hb, rfl⟩
    refine ⟨hab, kp N₁ (kp a b), (h1 a b hab).1, isOp_kp _ _,
      (memCh_iff g₂ gr (h1 a b hab).1).mpr ?_⟩
    rw [(h1 a b hab).2]
    exact pr_iff.mp hr

/-! ### The collapse axiom -/

/-- **The collapse axiom holds in the pointed graphs modulo bisimulation.** -/
theorem qg_hc : HC (QG V) := by
  intro u
  obtain ⟨g, rfl⟩ := exists_rep u
  let N : V := nodes g
  have hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N := nodes_ok g
  let C : V := sepB (k := 2) (prB.comp ![1, 0, 2]) N ![g.E, g.p]
  have hC : ∀ c, c ∈ C ↔ Pr g.E c g.p := fun c =>
    (mem_sepB _ _ _ c).trans ⟨fun k => k.2, fun k => ⟨(hN c _ k).1, k⟩⟩
  have hCN : ∀ c, c ∈ C → c ∈ N := fun c hc => (hN c _ ((hC c).mp hc)).1
  let h : PG V := g.col N C hN
  let NT : V := tg N (prodS (wfRels C) C)
  let N' : V := nodes h ∪ NT
  have hN' : ∀ c x, Pr h.E c x → c ∈ N' ∧ x ∈ N' := fun c x k =>
    ⟨mem_union_iff.mpr (Or.inl (nodes_ok h c x k).1),
      mem_union_iff.mpr (Or.inl (nodes_ok h c x k).2)⟩
  have hNT : ∀ ρ c, ρ ∈ wfRels C → c ∈ C → kp N (kp ρ c) ∈ NT := fun ρ c hρ hc =>
    mem_tg.mpr ⟨kp ρ c, mem_prodS.mpr ⟨ρ, hρ, c, hc, rfl⟩, rfl⟩
  have hNTN' : ∀ a, a ∈ NT → a ∈ N' := fun a ha => mem_union_iff.mpr (Or.inr ha)
  have hold : ∀ a, a ∈ N → mkQ (h.at a) = mkQ (g.at a) := fun a ha => col_old g N C hN ha
  have hnew : ∀ ρ, ρ ∈ wfRels C → ∀ (c : V) (x : QG V),
      x ∈ mkQ (h.at (kp N (kp ρ c))) ↔ ∃ a, Pr ρ a c ∧ x = mkQ (h.at (kp N (kp ρ a))) :=
    fun ρ hρ c x => mem_col_new g N C hN hρ
  let T : QG V := mkS h N' hN' NT
  have hT : ∀ x : QG V, x ∈ T ↔ ∃ n, n ∈ NT ∧ x = mkQ (h.at n) :=
    fun x => mem_mkS h N' hN' hNTN'
  refine ⟨T, fun y hy z hz => ?_, fun r hr => ?_⟩
  · obtain ⟨n, hn, rfl⟩ := (hT y).mp hy
    obtain ⟨i, hi, rfl⟩ := mem_tg.mp hn
    obtain ⟨ρ, hρ, c, hc, rfl⟩ := mem_prodS.mp hi
    obtain ⟨a, ha, rfl⟩ := (hnew ρ hρ c z).mp hz
    exact (hT _).mpr ⟨_, hNT ρ a hρ (wfRels_dom hρ ha).1, rfl⟩
  · obtain ⟨ρ, hρs, hρ⟩ := exists_rho g N hN C hCN r
    have hρw : ρ ∈ wfRels C := by
      refine mem_wfRels.mpr ⟨hρs, fun S hS hne => ?_⟩
      have hSN : ∀ a, a ∈ S → a ∈ N := fun a ha => hCN a (hS a ha)
      have hX : ∀ x : QG V, x ∈ mkS g N hN S ↔ ∃ a, a ∈ S ∧ x = mkQ (g.at a) :=
        fun x => mem_mkS g N hN hSN
      obtain ⟨z, hz⟩ := hne
      obtain ⟨c, hc, hmin⟩ := hr (mkS g N hN S) ⟨mkQ (g.at z), (hX _).mpr ⟨z, hz, rfl⟩, not_false⟩
        (fun c hc => by
          obtain ⟨a, ha, rfl⟩ := (hX c).mp hc
          exact mem_mkQ.mpr ⟨a, (hC a).mp (hS a ha), rfl⟩)
      obtain ⟨m, hm, rfl⟩ := (hX c).mp hc
      exact ⟨m, hm, fun a ha ham =>
        hmin (mkQ (g.at a)) ((hX _).mpr ⟨a, ha, rfl⟩) ((hρ a m).mp ham).2.2⟩
    let PF : V := relB (k := 2) fRelB C NT ![N, ρ]
    have hPF : ∀ c n, Pr PF c n ↔ c ∈ C ∧ n ∈ NT ∧ FRel c n N ρ :=
      fun c n => pr_relB fRelB C NT ![N, ρ] c n
    have hPFs : ∀ z, z ∈ PF → z ∈ prodS N' N' := by
      intro z hz
      obtain ⟨c, hc, n, hn, e⟩ := mem_prodS.mp (relB_sub fRelB C NT ![N, ρ] hz)
      exact mem_prodS.mpr ⟨c, mem_union_iff.mpr (Or.inl
        (nodes_ok h c g.p (pr_union.mpr (Or.inl ((hC c).mp hc)))).1), n, hNTN' n hn, e⟩
    obtain ⟨F, hF⟩ := qg_rel h N' hN' PF hPFs
    have hF' : ∀ x y : QG V, Pr F x y ↔
        ∃ c, c ∈ C ∧ (x = mkQ (g.at c) ∧ y = mkQ (h.at (kp N (kp ρ c)))) := by
      intro x y
      rw [hF]
      constructor
      · rintro ⟨a, b, hab, e1, e2⟩
        obtain ⟨ha, -, hnd⟩ := (hPF a b).mp (pr_iff.mpr hab)
        have eb : b = kp N (kp ρ a) := nd_iff.mp hnd
        rw [eb] at e2
        exact ⟨a, ha, e1.trans (hold a (hCN a ha)), e2⟩
      · rintro ⟨c, hc, e1, e2⟩
        exact ⟨c, kp N (kp ρ c), pr_iff.mp ((hPF _ _).mpr ⟨hc, hNT ρ c hρw hc, nd_iff.mpr rfl⟩),
          e1.trans (hold c (hCN c hc)).symm, e2⟩
    refine ⟨F, fun b hb => ?_⟩
    obtain ⟨c, hc, rfl⟩ := mem_mkQ.mp hb
    have hcC : c ∈ C := (hC c).mpr hc
    refine ⟨mkQ (h.at (kp N (kp ρ c))), (hT _).mpr ⟨_, hNT ρ c hρw hcC, rfl⟩,
      (hF' _ _).mpr ⟨c, hcC, rfl, rfl⟩, fun v' hv' => ?_, fun y => ?_⟩
    · obtain ⟨c', hc', e, rfl⟩ := (hF' _ _).mp hv'
      refine qg_ext _ _ fun z => ?_
      rw [hnew ρ hρw c' z, hnew ρ hρw c z]
      refine exists_congr fun a => and_congr_left fun _ => ?_
      rw [hρ a c', hρ a c, ← e]
      exact ⟨fun k => ⟨k.1, hcC, k.2.2⟩, fun k => ⟨k.1, hc', k.2.2⟩⟩
    · rw [hnew ρ hρw c y]
      constructor
      · rintro ⟨a, ha, rfl⟩
        have k := (hρ a c).mp ha
        exact ⟨mkQ (g.at a), mem_mkQ.mpr ⟨a, (hC a).mp k.1, rfl⟩, k.2.2,
          (hF' _ _).mpr ⟨a, k.1, rfl, rfl⟩⟩
      · rintro ⟨a, -, har, haF⟩
        obtain ⟨c', hc', rfl, rfl⟩ := (hF' _ _).mp haF
        exact ⟨c', (hρ c' c).mpr ⟨hc', hcC, har⟩, rfl⟩

/-- **The pointed graphs of a model of `𝗠`, modulo bisimulation, are a model of `𝗠𝗛`.** -/
instance qgModelsMH : (QG V)↓[ℒₛₑₜ] ⊧* 𝗠𝗛 := MH.models_of_hc qg_hc

end pairs

end MG

end FFL.FirstOrder.SetTheory
