module

public import MHCodes
public import MacModel

@[expose] public section

set_option autoImplicit false

/-!
# Well-founded pointed graphs in a model of `𝗠`, modulo bisimulation

In a model `V` of `𝗠`. A graph is a set `E` of pairs `⟨c, x⟩`, read "`c` is a child of `x`"
(`Pr E c x`). It is well-founded (`WFG`) if every set with a member has a member none of whose
children is in the set. A pointed graph (`PG`) is a well-founded graph with a point.

* `IsBisG B E E'`: `B` is a bisimulation between `E` and `E'`. `Bis E x E' x'`: some
  bisimulation relates `x` and `x'`. It is an equivalence (`bis_refl`, `bis_symm`, `bis_trans`),
  and a bisimulation can be taken inside any two sets of nodes (`bis_trim`), which makes
  `Bis` bounded (`BisIn`, `bisInB`).
* `QG V`: the pointed graphs modulo `Bis`. `x ∈ y` in `QG V`: `x` is the class of the graph of
  `y` pointed at a child of its point (`mem_mkQ`).
* `qg_ext`: extensionality. `qg_found`: foundation.
* `wfg_union`, `bis_union_old`, `bis_union_new`: adding to a graph edges whose targets are new
  nodes.
* `adj`: new nodes `⟨N, i⟩` for `i ∈ I` with given old children, and a top node `N` above them
  (`adj_old`, `mem_adj_new`, `mem_adj_top`). `mkS`: the class with given members.
* `tagE`: a copy of a graph on new nodes (`tag_bis`).
* `EX X`, `jX X a`: the membership graph of a transitive set `X`, pointed at `a` (`mem_jX`).

This is the construction of A. R. D. Mathias (*The strength of Mac Lane set theory*, §3) with
bisimulation in place of isomorphism of extensional relations.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MG

open MH

/-! ### Definitions -/

section defs

variable {V : Type} [SetStructure V]

/-- Every child of `x` in `E` is related by `B` to a child of `x'` in `E'`. -/
def Fwd (B E E' x x' : V) : Prop :=
  ∀ e, e ∈ E → ∀ w, w ∈ e → ∀ c, c ∈ w → (IsOp e c x →
    ∃ e', e' ∈ E' ∧ ∃ w', w' ∈ e' ∧ ∃ c', c' ∈ w' ∧ (IsOp e' c' x' ∧ Pr B c c'))

/-- Every child of `x'` in `E'` is related by `B` to a child of `x` in `E`. -/
def Bwd (B E E' x x' : V) : Prop :=
  ∀ e', e' ∈ E' → ∀ w', w' ∈ e' → ∀ c', c' ∈ w' → (IsOp e' c' x' →
    ∃ e, e ∈ E ∧ ∃ w, w ∈ e ∧ ∃ c, c ∈ w ∧ (IsOp e c x ∧ Pr B c c'))

/-- `B` is a bisimulation between the graphs `E` and `E'`. -/
def IsBisG (B E E' : V) : Prop :=
  ∀ q, q ∈ B → ∀ u, u ∈ q → ∀ x, x ∈ u → ∀ u', u' ∈ q → ∀ x', x' ∈ u' →
    (IsOp q x x' → (Fwd B E E' x x' ∧ Bwd B E E' x x'))

/-- A bisimulation in `P` relates `x` and `x'`. -/
def BisIn (P E x E' x' : V) : Prop := ∃ B, B ∈ P ∧ (IsBisG B E E' ∧ Pr B x x')

/-- Some bisimulation relates `x` and `x'`. -/
def Bis (E x E' x' : V) : Prop := ∃ B, IsBisG B E E' ∧ Pr B x x'

/-- The graph `E` is well-founded. -/
def WFG (E : V) : Prop := ∀ S : V, (∃ z, z ∈ S) → ∃ m, m ∈ S ∧ ∀ c, c ∈ S → ¬ Pr E c m

end defs

def fwdB : BDef (k := 5) (fun V _ v ↦ Fwd (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.ball 1 (BDef.ball 0 (BDef.ball 0 ((isOpB.comp ![2, 0, 6]).imp
    (BDef.bex 5 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 0, 10]).and
      (prB.comp ![6, 3, 0]))))))))).congr fun _ _ _ => Iff.rfl

def bwdB : BDef (k := 5) (fun V _ v ↦ Bwd (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.ball 2 (BDef.ball 0 (BDef.ball 0 ((isOpB.comp ![2, 0, 7]).imp
    (BDef.bex 4 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 0, 9]).and
      (prB.comp ![6, 0, 3]))))))))).congr fun _ _ _ => Iff.rfl

def isBisGB : BDef (k := 3) (fun V _ v ↦ IsBisG (v 0) (v 1) (v 2)) :=
  (BDef.ball 0 (BDef.ball 0 (BDef.ball 0 (BDef.ball 2 (BDef.ball 0
    ((isOpB.comp ![4, 2, 0]).imp ((fwdB.comp ![5, 6, 7, 2, 0]).and
      (bwdB.comp ![5, 6, 7, 2, 0])))))))).congr fun _ _ _ => Iff.rfl

def bisInB : BDef (k := 5) (fun V _ v ↦ BisIn (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 0 ((isBisGB.comp ![0, 2, 4]).and (prB.comp ![0, 3, 5]))).congr
    fun _ _ _ => Iff.rfl

/-- A well-founded graph with a point. -/
structure PG (V : Type) [SetStructure V] where
  /-- The edges: pairs of a child and a parent. -/
  E : V
  /-- The point. -/
  p : V
  /-- The graph is well-founded. -/
  wf : WFG E

/-- The same graph pointed at `c`. -/
def PG.at {V : Type} [SetStructure V] (g : PG V) (c : V) : PG V := ⟨g.E, c, g.wf⟩

section basic

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-! ### New nodes -/

theorem no_cycle3' {a b c : V} (h1 : a ∈ b) (h2 : b ∈ c) : c ∉ a := by
  intro h3
  obtain ⟨z, hz, hmin⟩ := m_found ({a, b, c} : V) ⟨a, by simp⟩
  rcases (by simpa using hz : z = a ∨ z = b ∨ z = c) with e | e | e
  · exact hmin c (by simp) (e ▸ h3)
  · exact hmin a (by simp) (e ▸ h1)
  · exact hmin b (by simp) (e ▸ h2)

/-- The pair of `N` and anything is not a member of `N`. -/
theorem kp_fresh (N i : V) : kp N i ∉ N :=
  no_cycle3' (a := N) (b := {N}) (c := kp N i) (by simp) (by simp [kp])

theorem kp_ne_self (N i : V) : kp N i ≠ N := by
  intro e
  have h1 : ({N} : V) ∈ N := by
    have : ({N} : V) ∈ kp N i := by simp [kp]
    rw [e] at this
    exact this
  exact mem_asymm (show N ∈ ({N} : V) by simp) h1

/-! ### The nodes of a graph -/

/-- A set that has the children and the parents of a graph as members. -/
noncomputable def fld (E : V) : V := ⋃ˢ (⋃ˢ E)

theorem pr_fld {E c x : V} (h : Pr E c x) : c ∈ fld E ∧ x ∈ fld E := by
  have h1 : ({c, x} : V) ∈ ⋃ˢ E := mem_sUnion_iff.mpr ⟨kp c x, pr_iff.mp h, by simp [kp]⟩
  exact ⟨mem_sUnion_iff.mpr ⟨_, h1, by simp⟩, mem_sUnion_iff.mpr ⟨_, h1, by simp⟩⟩

theorem pr_union {E E₁ c x : V} : Pr (E ∪ E₁) c x ↔ Pr E c x ∨ Pr E₁ c x :=
  pr_iff.trans (mem_union_iff.trans (or_congr pr_iff.symm pr_iff.symm))

/-! ### Bisimulations -/

theorem fwd_iff {B E E' x x' : V} :
    Fwd B E E' x x' ↔ ∀ c, Pr E c x → ∃ c', Pr E' c' x' ∧ Pr B c c' := by
  constructor
  · rintro H c ⟨e, he, hop⟩
    obtain ⟨w, hw, hcw⟩ := pr_fst_mem hop
    obtain ⟨e', he', w', -, c', -, hop', hB⟩ := H e he w hw c hcw hop
    exact ⟨c', ⟨e', he', hop'⟩, hB⟩
  · intro H e he w _ c _ hop
    obtain ⟨c', ⟨e', he', hop'⟩, hB⟩ := H c ⟨e, he, hop⟩
    obtain ⟨w', hw', hcw'⟩ := pr_fst_mem hop'
    exact ⟨e', he', w', hw', c', hcw', hop', hB⟩

theorem bwd_iff {B E E' x x' : V} :
    Bwd B E E' x x' ↔ ∀ c', Pr E' c' x' → ∃ c, Pr E c x ∧ Pr B c c' := by
  constructor
  · rintro H c' ⟨e', he', hop'⟩
    obtain ⟨w', hw', hcw'⟩ := pr_fst_mem hop'
    obtain ⟨e, he, w, -, c, -, hop, hB⟩ := H e' he' w' hw' c' hcw' hop'
    exact ⟨c, ⟨e, he, hop⟩, hB⟩
  · intro H e' he' w' _ c' _ hop'
    obtain ⟨c, ⟨e, he, hop⟩, hB⟩ := H c' ⟨e', he', hop'⟩
    obtain ⟨w, hw, hcw⟩ := pr_fst_mem hop
    exact ⟨e, he, w, hw, c, hcw, hop, hB⟩

theorem isBisG_iff {B E E' : V} : IsBisG B E E' ↔ ∀ x x', Pr B x x' →
    ((∀ c, Pr E c x → ∃ c', Pr E' c' x' ∧ Pr B c c') ∧
      ∀ c', Pr E' c' x' → ∃ c, Pr E c x ∧ Pr B c c') := by
  constructor
  · rintro H x x' ⟨q, hq, hop⟩
    obtain ⟨u, hu, hxu⟩ := pr_fst_mem hop
    obtain ⟨u', hu', hxu'⟩ := pr_snd_mem hop
    obtain ⟨h1, h2⟩ := H q hq u hu x hxu u' hu' x' hxu' hop
    exact ⟨fwd_iff.mp h1, bwd_iff.mp h2⟩
  · intro H q hq u _ x _ u' _ x' _ hop
    obtain ⟨h1, h2⟩ := H x x' ⟨q, hq, hop⟩
    exact ⟨fwd_iff.mpr h1, bwd_iff.mpr h2⟩

theorem bis_refl (E x : V) : Bis E x E x := by
  let N : V := fld E ∪ {x}
  let B : V := relB (k := 0) (BDef.eq 0 1) N N ![]
  have hB : ∀ a b, Pr B a b ↔ a ∈ N ∧ b ∈ N ∧ a = b := fun a b => pr_relB _ N N ![] a b
  have inN : ∀ {c y : V}, Pr E c y → c ∈ N := fun h => mem_union_iff.mpr (Or.inl (pr_fld h).1)
  refine ⟨B, isBisG_iff.mpr fun a b hab => ?_, (hB x x).mpr ⟨by simp [N], by simp [N], rfl⟩⟩
  obtain ⟨-, -, rfl⟩ := (hB a b).mp hab
  exact ⟨fun c hc => ⟨c, hc, (hB c c).mpr ⟨inN hc, inN hc, rfl⟩⟩,
    fun c hc => ⟨c, hc, (hB c c).mpr ⟨inN hc, inN hc, rfl⟩⟩⟩

theorem bis_symm {E x E' x' : V} (h : Bis E x E' x') : Bis E' x' E x := by
  obtain ⟨B, hB, hx⟩ := h
  let B' : V := relB (k := 1) (prB.comp ![2, 1, 0]) (fld B) (fld B) ![B]
  have hB' : ∀ b a, Pr B' b a ↔ Pr B a b := fun b a =>
    (pr_relB (prB.comp ![2, 1, 0]) (fld B) (fld B) ![B] b a).trans
      ⟨fun k => k.2.2, fun k => ⟨(pr_fld k).2, (pr_fld k).1, k⟩⟩
  refine ⟨B', isBisG_iff.mpr fun b a hba => ?_, (hB' x' x).mpr hx⟩
  obtain ⟨h1, h2⟩ := isBisG_iff.mp hB a b ((hB' b a).mp hba)
  exact ⟨fun c' hc' => let ⟨c, hc, k⟩ := h2 c' hc'; ⟨c, hc, (hB' c' c).mpr k⟩,
    fun c hc => let ⟨c', hc', k⟩ := h1 c hc; ⟨c', hc', (hB' c' c).mpr k⟩⟩

theorem bis_trans {E x E' x' E'' x'' : V} (h : Bis E x E' x') (h' : Bis E' x' E'' x'') :
    Bis E x E'' x'' := by
  obtain ⟨B, hB, hx⟩ := h
  obtain ⟨B', hB', hx'⟩ := h'
  let B'' : V := relB (k := 3) (BDef.bex 4 ((prB.comp ![3, 1, 0]).and (prB.comp ![4, 0, 2])))
    (fld B) (fld B') ![B, B', fld B]
  have hB'' : ∀ a c, Pr B'' a c ↔ ∃ m, Pr B a m ∧ Pr B' m c := fun a c =>
    (pr_relB _ (fld B) (fld B') ![B, B', fld B] a c).trans
      ⟨fun k => let ⟨m, _, k1, k2⟩ := k.2.2; ⟨m, k1, k2⟩,
        fun ⟨m, k1, k2⟩ => ⟨(pr_fld k1).1, (pr_fld k2).2, m, (pr_fld k1).2, k1, k2⟩⟩
  refine ⟨B'', isBisG_iff.mpr fun a c hac => ?_, (hB'' x x'').mpr ⟨x', hx, hx'⟩⟩
  obtain ⟨m, k1, k2⟩ := (hB'' a c).mp hac
  obtain ⟨f1, b1⟩ := isBisG_iff.mp hB a m k1
  obtain ⟨f2, b2⟩ := isBisG_iff.mp hB' m c k2
  refine ⟨fun d hd => ?_, fun d'' hd'' => ?_⟩
  · obtain ⟨d', hd', j1⟩ := f1 d hd
    obtain ⟨d'', hd'', j2⟩ := f2 d' hd'
    exact ⟨d'', hd'', (hB'' d d'').mpr ⟨d', j1, j2⟩⟩
  · obtain ⟨d', hd', j2⟩ := b2 d'' hd''
    obtain ⟨d, hd, j1⟩ := b1 d' hd'
    exact ⟨d, hd, (hB'' d d'').mpr ⟨d', j1, j2⟩⟩

/-- Bisimilar nodes have bisimilar children. -/
theorem bis_child {E x E' x' c : V} (h : Bis E x E' x') (hc : Pr E c x) :
    ∃ c', Pr E' c' x' ∧ Bis E c E' c' := by
  obtain ⟨B, hB, hx⟩ := h
  obtain ⟨c', hc', k⟩ := (isBisG_iff.mp hB x x' hx).1 c hc
  exact ⟨c', hc', B, hB, k⟩

theorem bis_child' {E x E' x' c' : V} (h : Bis E x E' x') (hc' : Pr E' c' x') :
    ∃ c, Pr E c x ∧ Bis E c E' c' := by
  obtain ⟨B, hB, hx⟩ := h
  obtain ⟨c, hc, k⟩ := (isBisG_iff.mp hB x x' hx).2 c' hc'
  exact ⟨c, hc, B, hB, k⟩

theorem bisIn_bis {P E x E' x' : V} (h : BisIn P E x E' x') : Bis E x E' x' :=
  let ⟨B, _, hB, hx⟩ := h; ⟨B, hB, hx⟩

/-- **A bisimulation can be taken inside any two sets of nodes.** -/
theorem bis_trim {E x E' x' N N' : V} (hN : ∀ z, z ∈ fld E → z ∈ N) (hx : x ∈ N)
    (hN' : ∀ z, z ∈ fld E' → z ∈ N') (hx' : x' ∈ N') (h : Bis E x E' x') :
    BisIn (℘ (prodS N N')) E x E' x' := by
  obtain ⟨B, hB, hxx⟩ := h
  let B' : V := sepB (k := 1) (BDef.mem 0 1) (prodS N N') ![B]
  have hB'z : ∀ z, z ∈ B' ↔ z ∈ prodS N N' ∧ z ∈ B := fun z => mem_sepB _ _ _ z
  have hB' : ∀ a b, Pr B' a b ↔ a ∈ N ∧ b ∈ N' ∧ Pr B a b := by
    intro a b
    rw [pr_iff, hB'z, mem_prodS, pr_iff]
    constructor
    · rintro ⟨⟨a', ha', b', hb', e⟩, k⟩
      obtain ⟨rfl, rfl⟩ := kp_inj e
      exact ⟨ha', hb', k⟩
    · rintro ⟨ha, hb, k⟩
      exact ⟨⟨a, ha, b, hb, rfl⟩, k⟩
  refine ⟨B', mem_power_iff.mpr fun z hz => ((hB'z z).mp hz).1, isBisG_iff.mpr fun a b hab => ?_,
    (hB' x x').mpr ⟨hx, hx', hxx⟩⟩
  obtain ⟨f, b'⟩ := isBisG_iff.mp hB a b ((hB' a b).mp hab).2.2
  exact ⟨fun c hc => let ⟨c', hc', k⟩ := f c hc
      ⟨c', hc', (hB' c c').mpr ⟨hN c (pr_fld hc).1, hN' c' (pr_fld hc').1, k⟩⟩,
    fun c' hc' => let ⟨c, hc, k⟩ := b' c' hc'
      ⟨c, hc, (hB' c c').mpr ⟨hN c (pr_fld hc).1, hN' c' (pr_fld hc').1, k⟩⟩⟩

/-! ### The quotient -/

instance pgSetoid : Setoid (PG V) where
  r g g' := Bis g.E g.p g'.E g'.p
  iseqv := ⟨fun g => bis_refl g.E g.p, fun h => bis_symm h, fun h h' => bis_trans h h'⟩

/-- `g` is the class of the graph of `g'` pointed at a child of its point. -/
def memG (g g' : PG V) : Prop := ∃ c, Pr g'.E c g'.p ∧ Bis g.E g.p g'.E c

theorem memG_congr {a b a' b' : PG V} (h : a ≈ a') (h' : b ≈ b') : memG a b ↔ memG a' b' := by
  have key : ∀ {a b a' b' : PG V}, Bis a.E a.p a'.E a'.p → Bis b.E b.p b'.E b'.p →
      memG a b → memG a' b' := by
    rintro a b a' b' h h' ⟨c, hc, hb⟩
    obtain ⟨c', hc', hb'⟩ := bis_child h' hc
    exact ⟨c', hc', bis_trans (bis_trans (bis_symm h) hb) hb'⟩
  exact ⟨key h h', key (bis_symm h) (bis_symm h')⟩

end basic

/-- **The well-founded pointed graphs of a model of `𝗠`, modulo bisimulation.** -/
abbrev QG (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗠] : Type :=
  Quotient (pgSetoid (V := V))

section quot

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

instance qgSetStructure : SetStructure (QG V) :=
  ⟨fun y x => Quotient.liftOn₂ x y memG fun _ _ _ _ h h' => propext (memG_congr h h')⟩

/-- The class of a pointed graph. -/
def mkQ (g : PG V) : QG V := Quotient.mk _ g

theorem mkQ_mem {g g' : PG V} : mkQ g ∈ mkQ g' ↔ memG g g' := Iff.rfl

theorem mkQ_eq {g g' : PG V} : mkQ g = mkQ g' ↔ Bis g.E g.p g'.E g'.p :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem exists_rep (x : QG V) : ∃ g : PG V, x = mkQ g :=
  let ⟨g, hg⟩ := Quotient.exists_rep x; ⟨g, hg.symm⟩

/-- **The members of a class** are the classes of its graph pointed at the children of its
point. -/
theorem mem_mkQ {x : QG V} {g : PG V} :
    x ∈ mkQ g ↔ ∃ c, Pr g.E c g.p ∧ x = mkQ (g.at c) := by
  obtain ⟨g₀, rfl⟩ := exists_rep x
  exact ⟨fun ⟨c, hc, hb⟩ => ⟨c, hc, mkQ_eq.mpr hb⟩, fun ⟨c, hc, e⟩ => ⟨c, hc, mkQ_eq.mp e⟩⟩

/-- The nodes of a pointed graph. -/
noncomputable def nodes (g : PG V) : V := fld g.E ∪ {g.p}

theorem fld_sub_nodes (g : PG V) : ∀ z, z ∈ fld g.E → z ∈ nodes g :=
  fun _ hz => mem_union_iff.mpr (Or.inl hz)

theorem p_mem_nodes (g : PG V) : g.p ∈ nodes g := by simp [nodes]

/-- **Extensionality.** -/
theorem qg_ext (x y : QG V) (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  obtain ⟨g, rfl⟩ := exists_rep x
  obtain ⟨g', rfl⟩ := exists_rep y
  let N : V := nodes g
  let N' : V := nodes g'
  let B : V := relB (k := 5) ((bisInB.comp ![2, 3, 0, 4, 1]).or
    ((BDef.eq 0 5).and (BDef.eq 1 6))) N N' ![℘ (prodS N N'), g.E, g'.E, g.p, g'.p]
  have hB : ∀ a b, Pr B a b ↔ a ∈ N ∧ b ∈ N' ∧
      (BisIn (℘ (prodS N N')) g.E a g'.E b ∨ (a = g.p ∧ b = g'.p)) :=
    fun a b => pr_relB _ N N' ![℘ (prodS N N'), g.E, g'.E, g.p, g'.p] a b
  have trim : ∀ {a b : V}, a ∈ N → b ∈ N' → Bis g.E a g'.E b →
      BisIn (℘ (prodS N N')) g.E a g'.E b :=
    fun ha hb k => bis_trim (fld_sub_nodes g) ha (fld_sub_nodes g') hb k
  have inN : ∀ {c z : V}, Pr g.E c z → c ∈ N := fun k => fld_sub_nodes g _ (pr_fld k).1
  have inN' : ∀ {c z : V}, Pr g'.E c z → c ∈ N' := fun k => fld_sub_nodes g' _ (pr_fld k).1
  refine mkQ_eq.mpr ⟨B, isBisG_iff.mpr fun a b hab => ?_,
    (hB g.p g'.p).mpr ⟨p_mem_nodes g, p_mem_nodes g', Or.inr ⟨rfl, rfl⟩⟩⟩
  obtain ⟨-, -, k | ⟨rfl, rfl⟩⟩ := (hB a b).mp hab
  · have kb := bisIn_bis k
    refine ⟨fun c hc => ?_, fun c' hc' => ?_⟩
    · obtain ⟨c', hc', j⟩ := bis_child kb hc
      exact ⟨c', hc', (hB c c').mpr ⟨inN hc, inN' hc', Or.inl (trim (inN hc) (inN' hc') j)⟩⟩
    · obtain ⟨c, hc, j⟩ := bis_child' kb hc'
      exact ⟨c, hc, (hB c c').mpr ⟨inN hc, inN' hc', Or.inl (trim (inN hc) (inN' hc') j)⟩⟩
  · refine ⟨fun c hc => ?_, fun c' hc' => ?_⟩
    · have h1 : mkQ (g.at c) ∈ mkQ g' :=
        (h _).mp (mem_mkQ.mpr ⟨c, hc, rfl⟩)
      obtain ⟨c', hc', j⟩ := mkQ_mem.mp h1
      exact ⟨c', hc', (hB c c').mpr ⟨inN hc, inN' hc', Or.inl (trim (inN hc) (inN' hc') j)⟩⟩
    · have h1 : mkQ (g'.at c') ∈ mkQ g :=
        (h _).mpr (mem_mkQ.mpr ⟨c', hc', rfl⟩)
      obtain ⟨c, hc, j⟩ := mkQ_mem.mp h1
      exact ⟨c, hc, (hB c c').mpr
        ⟨inN hc, inN' hc', Or.inl (trim (inN hc) (inN' hc') (bis_symm j))⟩⟩

end quot

/-- `d` is bisimilar, by a bisimulation in `P`, to a child of `p`. -/
def ChildBis {V : Type} [SetStructure V] (d P E p : V) : Prop :=
  ∃ e, e ∈ E ∧ ∃ w, w ∈ e ∧ ∃ c, c ∈ w ∧ (IsOp e c p ∧ BisIn P E d E c)

def childBisB : BDef (k := 4) (fun V _ v ↦ ChildBis (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.bex 2 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 0, 6]).and
    (bisInB.comp ![4, 5, 3, 5, 0]))))).congr fun _ _ _ => Iff.rfl

section found

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-- **Foundation.** -/
theorem qg_found (x : QG V) (hx : ∃ y, y ∈ x) : ∃ y, y ∈ x ∧ ∀ z, z ∈ x → z ∉ y := by
  obtain ⟨g, rfl⟩ := exists_rep x
  obtain ⟨y₀, hy₀⟩ := hx
  obtain ⟨c₀, hc₀, -⟩ := mem_mkQ.mp hy₀
  let N : V := nodes g
  let P : V := ℘ (prodS N N)
  let S : V := sepB (k := 3) childBisB N ![P, g.E, g.p]
  have hS : ∀ d, d ∈ S ↔ d ∈ N ∧ ChildBis d P g.E g.p := fun d => mem_sepB _ _ _ d
  have inN : ∀ {c z : V}, Pr g.E c z → c ∈ N := fun k => fld_sub_nodes g _ (pr_fld k).1
  have hS' : ∀ d, d ∈ S ↔ d ∈ N ∧ ∃ c, Pr g.E c g.p ∧ Bis g.E d g.E c := by
    intro d
    rw [hS]
    refine and_congr_right fun hd => ?_
    constructor
    · rintro ⟨e, he, w, -, c, -, hop, k⟩
      exact ⟨c, ⟨e, he, hop⟩, bisIn_bis k⟩
    · rintro ⟨c, ⟨e, he, hop⟩, k⟩
      obtain ⟨w, hw, hcw⟩ := pr_fst_mem hop
      exact ⟨e, he, w, hw, c, hcw, hop,
        bis_trim (fld_sub_nodes g) hd (fld_sub_nodes g) (inN ⟨e, he, hop⟩) k⟩
  obtain ⟨m, hm, hmin⟩ := g.wf S ⟨c₀, (hS' c₀).mpr ⟨inN hc₀, c₀, hc₀, bis_refl _ _⟩⟩
  obtain ⟨-, c, hc, hmc⟩ := (hS' m).mp hm
  refine ⟨mkQ (g.at m), mkQ_mem.mpr ⟨c, hc, hmc⟩, fun z hz hzm => ?_⟩
  obtain ⟨c', hc', rfl⟩ := mem_mkQ.mp hz
  obtain ⟨d, hd, k⟩ := mkQ_mem.mp hzm
  exact hmin d ((hS' d).mpr ⟨inN hd, c', hc', bis_symm k⟩) hd

end found

end MG

end FFL.FirstOrder.SetTheory
