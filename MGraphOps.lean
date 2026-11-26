module

public import MGraph

@[expose] public section

set_option autoImplicit false

/-!
# Operations on the pointed graphs of a model of `𝗠`

Continues `MGraph.lean`.

* `wfg_union`, `bis_union_old`, `bis_union_new`: adding to a graph `E`, whose nodes are in `N`,
  edges `E₁` whose targets are not in `N`.
* `adj E Ch I N`: new nodes `⟨N, i⟩` for `i ∈ I`, the children of `⟨N, i⟩` being the old nodes
  `a` with `Ch(a, i)`, and a top node `N` whose children are the new nodes. `PG.adj`,
  `adj_old_eq`, `mem_adj_new`, `mem_adj_top`. `mkS`: the class whose members are the classes of
  the nodes in a set (`mem_mkS`).
* `tagE N E`: the copy of `E` on the nodes `⟨N, a⟩` (`tag_wf`, `tag_bis`). `PG.sum`: two graphs
  in one (`sum_left`, `sum_right`).
* `EX X`, `gX`, `jX`: the membership graph of a set (`mem_jX`).
* `qg_pair`, `qg_power`, `qg_tco`, `qg_inf`: four of the conditions of `IsMacBase`.
* `memCh_iff`: "the class of a node of one graph is a member of the class of another pointed
  graph" has a bounded definition.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MG

open MH

section defs

variable {V : Type} [SetStructure V]

/-- `y` is the new node `⟨N, i⟩` for an `i ∈ I` with `Ch(a, i)`. -/
def AdjA (a y I N Ch : V) : Prop := ∃ i, i ∈ I ∧ (IsOp y N i ∧ Pr Ch a i)

/-- `u = ⟨N, c⟩` and `v = ⟨N, x⟩` for an edge `⟨c, x⟩` of `E`. -/
def TagR (u v F N E : V) : Prop :=
  ∃ c, c ∈ F ∧ ∃ x, x ∈ F ∧ (IsOp u N c ∧ (IsOp v N x ∧ Pr E c x))

/-- The class of `(E, c)` is a member of the class of `(Ez, pz)`, by a bisimulation in `P`. -/
def MemCh (c P E Ez pz : V) : Prop :=
  ∃ e, e ∈ Ez ∧ ∃ w, w ∈ e ∧ ∃ d, d ∈ w ∧ (IsOp e d pz ∧ BisIn P E c Ez d)

/-- `u = ⟨N, b⟩`. -/
def TagB (u b N : V) : Prop := IsOp u N b

end defs

def tagBB : BDef (k := 3) (fun V _ v ↦ TagB (v 0) (v 1) (v 2)) :=
  (isOpB.comp ![0, 2, 1]).congr fun _ _ _ => Iff.rfl

def adjAB : BDef (k := 5) (fun V _ v ↦ AdjA (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 2 ((isOpB.comp ![2, 4, 0]).and (prB.comp ![5, 1, 0]))).congr fun _ _ _ => Iff.rfl

def tagRB : BDef (k := 5) (fun V _ v ↦ TagR (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 2 (BDef.bex 3 ((isOpB.comp ![2, 5, 1]).and ((isOpB.comp ![3, 5, 0]).and
    (prB.comp ![6, 1, 0]))))).congr fun _ _ _ => Iff.rfl

def memChB : BDef (k := 5) (fun V _ v ↦ MemCh (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 3 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 0, 7]).and
    (bisInB.comp ![4, 5, 3, 6, 0]))))).congr fun _ _ _ => Iff.rfl

section ops

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-! ### Adding edges to new nodes -/

theorem wfg_union {E E₁ N : V} (hE : WFG E) (hE₁ : WFG E₁)
    (hN : ∀ c x, Pr E c x → c ∈ N ∧ x ∈ N) (h1 : ∀ c x, Pr E₁ c x → x ∉ N) :
    WFG (E ∪ E₁) := by
  intro S hS
  by_cases h : ∃ z, z ∈ S ∧ z ∈ N
  · let S₁ : V := sepB (k := 1) (BDef.mem 0 1) S ![N]
    have hS₁ : ∀ z, z ∈ S₁ ↔ z ∈ S ∧ z ∈ N := fun z => mem_sepB _ _ _ z
    obtain ⟨z, hz⟩ := h
    obtain ⟨m, hm, hmin⟩ := hE S₁ ⟨z, (hS₁ z).mpr hz⟩
    obtain ⟨hmS, hmN⟩ := (hS₁ m).mp hm
    refine ⟨m, hmS, fun c hc hcm => ?_⟩
    rcases pr_union.mp hcm with k | k
    · exact hmin c ((hS₁ c).mpr ⟨hc, (hN c m k).1⟩) k
    · exact h1 c m k hmN
  · obtain ⟨m, hm, hmin⟩ := hE₁ S hS
    refine ⟨m, hm, fun c hc hcm => ?_⟩
    rcases pr_union.mp hcm with k | k
    · exact h ⟨m, hm, (hN c m k).2⟩
    · exact hmin c hc k

/-- An old node has the same class in the larger graph. -/
theorem bis_union_old {E E₁ N a : V} (hN : ∀ c x, Pr E c x → c ∈ N ∧ x ∈ N)
    (h1 : ∀ c x, Pr E₁ c x → x ∉ N) (ha : a ∈ N) : Bis (E ∪ E₁) a E a := by
  let B : V := relB (k := 0) (BDef.eq 0 1) N N ![]
  have hB : ∀ x y, Pr B x y ↔ x ∈ N ∧ y ∈ N ∧ x = y := fun x y => pr_relB _ N N ![] x y
  refine ⟨B, isBisG_iff.mpr fun x y hxy => ?_, (hB a a).mpr ⟨ha, ha, rfl⟩⟩
  obtain ⟨hx, -, rfl⟩ := (hB x y).mp hxy
  refine ⟨fun c hc => ?_, fun c hc => ⟨c, pr_union.mpr (Or.inl hc),
    (hB c c).mpr ⟨(hN c x hc).1, (hN c x hc).1, rfl⟩⟩⟩
  rcases pr_union.mp hc with k | k
  · exact ⟨c, k, (hB c c).mpr ⟨(hN c x k).1, (hN c x k).1, rfl⟩⟩
  · exact absurd hx (h1 c x k)

/-- A new node, in a set `N₁` of new nodes closed under children in `E₁`, has the same class
in the larger graph as in `E₁`. -/
theorem bis_union_new {E E₁ N N₁ a : V} (hN : ∀ c x, Pr E c x → x ∈ N)
    (hdisj : ∀ z, z ∈ N₁ → z ∉ N) (hN₁ : ∀ c x, Pr E₁ c x → x ∈ N₁ → c ∈ N₁) (ha : a ∈ N₁) :
    Bis (E ∪ E₁) a E₁ a := by
  let B : V := relB (k := 0) (BDef.eq 0 1) N₁ N₁ ![]
  have hB : ∀ x y, Pr B x y ↔ x ∈ N₁ ∧ y ∈ N₁ ∧ x = y := fun x y => pr_relB _ N₁ N₁ ![] x y
  refine ⟨B, isBisG_iff.mpr fun x y hxy => ?_, (hB a a).mpr ⟨ha, ha, rfl⟩⟩
  obtain ⟨hx, -, rfl⟩ := (hB x y).mp hxy
  refine ⟨fun c hc => ?_, fun c hc => ⟨c, pr_union.mpr (Or.inr hc),
    (hB c c).mpr ⟨hN₁ c x hc hx, hN₁ c x hc hx, rfl⟩⟩⟩
  rcases pr_union.mp hc with k | k
  · exact absurd (hN c x k) (hdisj x hx)
  · exact ⟨c, k, (hB c c).mpr ⟨hN₁ c x k hx, hN₁ c x k hx, rfl⟩⟩

/-! ### New nodes with given children, and a top node -/

/-- The set of the pairs `⟨N, b⟩` for `b ∈ F`. -/
noncomputable def tg (N F : V) : V := prodS {N} F

theorem mem_tg {N F z : V} : z ∈ tg N F ↔ ∃ b, b ∈ F ∧ z = kp N b := by
  rw [tg, mem_prodS]
  constructor
  · rintro ⟨n, hn, b, hb, rfl⟩
    rw [show n = N by simpa using hn]
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨N, by simp, b, hb, rfl⟩

/-- The edges from old nodes to the new nodes. -/
noncomputable def adjA (Ch I N : V) : V := relB (k := 3) adjAB N (tg N I) ![I, N, Ch]

/-- The edges from the new nodes to the top node. -/
noncomputable def adjT (I N : V) : V := prodS (tg N I) {N}

/-- The graph `E` with the new nodes and the top node. -/
noncomputable def adj (E Ch I N : V) : V := E ∪ (adjA Ch I N ∪ adjT I N)

theorem pr_adjA {Ch I N a y : V} :
    Pr (adjA Ch I N) a y ↔ a ∈ N ∧ ∃ i, i ∈ I ∧ (y = kp N i ∧ Pr Ch a i) := by
  have h0 : Pr (adjA Ch I N) a y ↔ a ∈ N ∧ y ∈ tg N I ∧ AdjA a y I N Ch :=
    pr_relB adjAB N (tg N I) ![I, N, Ch] a y
  refine h0.trans ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨ha, -, i, hi, hop, hch⟩ := k
    exact ⟨ha, i, hi, isOp_iff.mp hop, hch⟩
  · obtain ⟨ha, i, hi, rfl, hch⟩ := k
    exact ⟨ha, mem_tg.mpr ⟨i, hi, rfl⟩, i, hi, isOp_kp N i, hch⟩

theorem pr_adjT {I N y t : V} : Pr (adjT I N) y t ↔ t = N ∧ ∃ i, i ∈ I ∧ y = kp N i := by
  rw [pr_iff, adjT, mem_prodS]
  constructor
  · rintro ⟨y', hy', t', ht', e⟩
    obtain ⟨rfl, rfl⟩ := kp_inj e
    obtain ⟨i, hi, rfl⟩ := mem_tg.mp hy'
    exact ⟨by simpa using ht', i, hi, rfl⟩
  · rintro ⟨rfl, i, hi, rfl⟩
    exact ⟨kp t i, mem_tg.mpr ⟨i, hi, rfl⟩, t, by simp, rfl⟩

theorem adj_new_target {Ch I N c x : V} (h : Pr (adjA Ch I N ∪ adjT I N) c x) : x ∉ N := by
  rcases pr_union.mp h with k | k
  · obtain ⟨-, i, -, rfl, -⟩ := pr_adjA.mp k
    exact kp_fresh N i
  · rw [(pr_adjT.mp k).1]
    exact mem_irrefl N

theorem adj_new_wf (Ch I N : V) : WFG (adjA Ch I N ∪ adjT I N) := by
  intro S hS
  by_cases h1 : ∃ z, z ∈ S ∧ z ∈ N
  · obtain ⟨z, hz, hzN⟩ := h1
    exact ⟨z, hz, fun c _ hcz => adj_new_target hcz hzN⟩
  · by_cases h2 : ∃ z, z ∈ S ∧ ∃ i, z = kp N i
    · obtain ⟨z, hz, i, rfl⟩ := h2
      refine ⟨kp N i, hz, fun c hc hcz => ?_⟩
      rcases pr_union.mp hcz with k | k
      · exact h1 ⟨c, hc, (pr_adjA.mp k).1⟩
      · exact kp_ne_self N i (pr_adjT.mp k).1
    · obtain ⟨z, hz⟩ := hS
      refine ⟨z, hz, fun c hc hcz => ?_⟩
      rcases pr_union.mp hcz with k | k
      · obtain ⟨-, i, -, e, -⟩ := pr_adjA.mp k
        exact h2 ⟨z, hz, i, e⟩
      · obtain ⟨-, i, -, e⟩ := pr_adjT.mp k
        exact h2 ⟨c, hc, i, e⟩

theorem adj_wf {E Ch I N : V} (hE : WFG E) (hN : ∀ c x, Pr E c x → c ∈ N ∧ x ∈ N) :
    WFG (adj E Ch I N) :=
  wfg_union hE (adj_new_wf Ch I N) hN fun _ _ h => adj_new_target h

theorem pr_adj_new {E Ch I N c i : V} (hN : ∀ c x, Pr E c x → c ∈ N ∧ x ∈ N) :
    Pr (adj E Ch I N) c (kp N i) ↔ c ∈ N ∧ (i ∈ I ∧ Pr Ch c i) := by
  constructor
  · intro h
    rcases pr_union.mp h with k | k
    · exact absurd (hN _ _ k).2 (kp_fresh N i)
    · rcases pr_union.mp k with k | k
      · obtain ⟨hc, i', hi', e, hch⟩ := pr_adjA.mp k
        obtain ⟨-, rfl⟩ := kp_inj e
        exact ⟨hc, hi', hch⟩
      · exact absurd (pr_adjT.mp k).1 (kp_ne_self N i)
  · rintro ⟨hc, hi, hch⟩
    exact pr_union.mpr (Or.inr (pr_union.mpr (Or.inl (pr_adjA.mpr ⟨hc, i, hi, rfl, hch⟩))))

theorem pr_adj_top {E Ch I N c : V} (hN : ∀ c x, Pr E c x → c ∈ N ∧ x ∈ N) :
    Pr (adj E Ch I N) c N ↔ ∃ i, i ∈ I ∧ c = kp N i := by
  constructor
  · intro h
    rcases pr_union.mp h with k | k
    · exact absurd (hN _ _ k).2 (mem_irrefl N)
    · rcases pr_union.mp k with k | k
      · obtain ⟨-, i, -, e, -⟩ := pr_adjA.mp k
        exact absurd e.symm (kp_ne_self N i)
      · exact (pr_adjT.mp k).2
  · rintro ⟨i, hi, rfl⟩
    exact pr_union.mpr (Or.inr (pr_union.mpr (Or.inr (pr_adjT.mpr ⟨rfl, i, hi, rfl⟩))))

/-- The pointed graph with the new nodes, pointed at the top node. -/
noncomputable def PG.adj (g : PG V) (Ch I N : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N) :
    PG V := ⟨MG.adj g.E Ch I N, N, adj_wf g.wf hN⟩

theorem adj_old_eq (g : PG V) (Ch I N : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N) {a : V}
    (ha : a ∈ N) : mkQ ((g.adj Ch I N hN).at a) = mkQ (g.at a) :=
  mkQ_eq.mpr (bis_union_old hN (fun _ _ h => adj_new_target h) ha)

/-- **The members of the class of a new node.** -/
theorem mem_adj_new (g : PG V) (Ch I N : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N)
    {i : V} {x : QG V} :
    x ∈ mkQ ((g.adj Ch I N hN).at (kp N i)) ↔
      ∃ a, a ∈ N ∧ (i ∈ I ∧ (Pr Ch a i ∧ x = mkQ (g.at a))) := by
  rw [mem_mkQ]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hcN, hi, hch⟩ := (pr_adj_new hN).mp hc
    exact ⟨c, hcN, hi, hch, adj_old_eq g Ch I N hN hcN⟩
  · rintro ⟨a, ha, hi, hch, rfl⟩
    exact ⟨a, (pr_adj_new hN).mpr ⟨ha, hi, hch⟩, (adj_old_eq g Ch I N hN ha).symm⟩

/-- **The members of the class of the top node.** -/
theorem mem_adj_top (g : PG V) (Ch I N : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N)
    {x : QG V} :
    x ∈ mkQ (g.adj Ch I N hN) ↔ ∃ i, i ∈ I ∧ x = mkQ ((g.adj Ch I N hN).at (kp N i)) := by
  rw [mem_mkQ]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (pr_adj_top hN).mp hc
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨kp N i, (pr_adj_top hN).mpr ⟨i, hi, rfl⟩, rfl⟩

theorem nodes_ok (g : PG V) : ∀ c x, Pr g.E c x → c ∈ nodes g ∧ x ∈ nodes g :=
  fun _ _ h => ⟨fld_sub_nodes g _ (pr_fld h).1, fld_sub_nodes g _ (pr_fld h).2⟩

/-- **The class whose members are the classes of the nodes in `S`.** -/
noncomputable def mkS (g : PG V) (N : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N) (S : V) :
    QG V := mkQ ((g.adj (prodS S {S}) {S} N hN).at (kp N S))

theorem mem_mkS (g : PG V) (N : V) (hN : ∀ c x, Pr g.E c x → c ∈ N ∧ x ∈ N) {S : V}
    (hS : ∀ a, a ∈ S → a ∈ N) {x : QG V} :
    x ∈ mkS g N hN S ↔ ∃ a, a ∈ S ∧ x = mkQ (g.at a) := by
  have hch : ∀ a, Pr (prodS S ({S} : V)) a S ↔ a ∈ S := by
    intro a
    rw [pr_iff, mem_prodS]
    constructor
    · rintro ⟨a', ha', s, -, e⟩
      rw [(kp_inj e).1]
      exact ha'
    · intro ha
      exact ⟨a, ha, S, by simp, rfl⟩
  refine (mem_adj_new g _ _ N hN).trans ⟨fun ⟨a, _, _, k, e⟩ => ⟨a, (hch a).mp k, e⟩,
    fun ⟨a, ha, e⟩ => ⟨a, hS a ha, by simp, (hch a).mpr ha, e⟩⟩

/-! ### A copy of a graph on new nodes -/

/-- The copy of `E` on the nodes `⟨N, a⟩`. -/
noncomputable def tagE (N E : V) : V :=
  relB (k := 3) tagRB (tg N (fld E)) (tg N (fld E)) ![fld E, N, E]

theorem pr_tagE {N E u v : V} :
    Pr (tagE N E) u v ↔ ∃ c x, u = kp N c ∧ (v = kp N x ∧ Pr E c x) := by
  have h0 : Pr (tagE N E) u v ↔ u ∈ tg N (fld E) ∧ v ∈ tg N (fld E) ∧
      TagR u v (fld E) N E := pr_relB tagRB _ _ ![fld E, N, E] u v
  refine h0.trans ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨-, -, c, -, x, -, h1, h2, h3⟩ := k
    exact ⟨c, x, isOp_iff.mp h1, isOp_iff.mp h2, h3⟩
  · obtain ⟨c, x, rfl, rfl, h3⟩ := k
    exact ⟨mem_tg.mpr ⟨c, (pr_fld h3).1, rfl⟩,
      mem_tg.mpr ⟨x, (pr_fld h3).2, rfl⟩, c, (pr_fld h3).1, x, (pr_fld h3).2,
      isOp_kp N c, isOp_kp N x, h3⟩

theorem tag_wf {E : V} (hE : WFG E) (N : V) : WFG (tagE N E) := by
  intro S hS
  let S' : V := sepB (k := 2) (BDef.bex 1 (isOpB.comp ![0, 3, 1])) (⋃ˢ (⋃ˢ S)) ![S, N]
  have h0 : ∀ a, a ∈ S' ↔ a ∈ ⋃ˢ (⋃ˢ S) ∧ ∃ y, y ∈ S ∧ IsOp y N a :=
    fun a => mem_sepB _ _ _ a
  have hS' : ∀ a, a ∈ S' ↔ kp N a ∈ S := by
    intro a
    refine (h0 a).trans ⟨fun k => ?_, fun k => ⟨?_, kp N a, k, isOp_kp N a⟩⟩
    · obtain ⟨-, y, hy, hop⟩ := k
      rw [← isOp_iff.mp hop]
      exact hy
    · have h1 : ({N, a} : V) ∈ ⋃ˢ S := mem_sUnion_iff.mpr ⟨kp N a, k, by simp [kp]⟩
      exact mem_sUnion_iff.mpr ⟨_, h1, by simp⟩
  by_cases h : ∃ a, a ∈ S'
  · obtain ⟨a₀, ha₀, hmin⟩ := hE S' h
    refine ⟨kp N a₀, (hS' a₀).mp ha₀, fun u hu hum => ?_⟩
    obtain ⟨c, x, rfl, e, hcx⟩ := pr_tagE.mp hum
    obtain ⟨-, rfl⟩ := kp_inj e
    exact hmin c ((hS' c).mpr hu) hcx
  · obtain ⟨z, hz⟩ := hS
    refine ⟨z, hz, fun u _ huz => ?_⟩
    obtain ⟨c, x, -, rfl, -⟩ := pr_tagE.mp huz
    exact h ⟨x, (hS' x).mpr hz⟩

/-- The copy of a node has the class of the node. -/
theorem tag_bis (N E a : V) : Bis (tagE N E) (kp N a) E a := by
  let F : V := fld E ∪ {a}
  let B : V := relB (k := 1) tagBB (tg N F) F ![N]
  have h0 : ∀ u b, Pr B u b ↔ u ∈ tg N F ∧ b ∈ F ∧ TagB u b N :=
    fun u b => pr_relB (k := 1) tagBB (tg N F) F ![N] u b
  have hB : ∀ u b, Pr B u b ↔ b ∈ F ∧ u = kp N b := fun u b =>
    (h0 u b).trans
      ⟨fun k => ⟨k.2.1, isOp_iff.mp k.2.2⟩, fun k => ⟨by
        rw [k.2]
        exact mem_tg.mpr ⟨b, k.1, rfl⟩, k.1, by
        rw [k.2]
        exact isOp_kp N b⟩⟩
  have inF : ∀ {c y : V}, Pr E c y → c ∈ F := fun k => mem_union_iff.mpr (Or.inl (pr_fld k).1)
  refine ⟨B, isBisG_iff.mpr fun u b hub => ?_, (hB _ _).mpr ⟨by simp [F], rfl⟩⟩
  obtain ⟨-, rfl⟩ := (hB u b).mp hub
  refine ⟨fun u' hu' => ?_, fun c hc => ?_⟩
  · obtain ⟨c, x, rfl, e, hcx⟩ := pr_tagE.mp hu'
    obtain ⟨-, rfl⟩ := kp_inj e
    exact ⟨c, hcx, (hB _ _).mpr ⟨inF hcx, rfl⟩⟩
  · exact ⟨kp N c, pr_tagE.mpr ⟨c, b, rfl, rfl, hc⟩, (hB _ _).mpr ⟨inF hc, rfl⟩⟩

theorem tag_target {N E c x : V} (h : Pr (tagE N E) c x) : x ∉ N := by
  obtain ⟨c', x', -, rfl, -⟩ := pr_tagE.mp h
  exact kp_fresh N x'

/-- The graph of `g` together with a copy of the graph of `g'`, pointed at the point of `g`. -/
noncomputable def PG.sum (g g' : PG V) : PG V :=
  ⟨g.E ∪ tagE (nodes g) g'.E, g.p,
    wfg_union g.wf (tag_wf g'.wf _) (nodes_ok g) fun _ _ h => tag_target h⟩

theorem sum_left (g g' : PG V) {a : V} (ha : a ∈ nodes g) :
    mkQ ((g.sum g').at a) = mkQ (g.at a) :=
  mkQ_eq.mpr (bis_union_old (nodes_ok g) (fun _ _ h => tag_target h) ha)

theorem sum_right (g g' : PG V) (a : V) :
    mkQ ((g.sum g').at (kp (nodes g) a)) = mkQ (g'.at a) := by
  let N : V := nodes g
  let N₁ : V := tg N (fld g'.E ∪ {a})
  refine mkQ_eq.mpr (bis_trans (bis_union_new (N := N) (N₁ := N₁)
    (fun c x h => (nodes_ok g c x h).2) (fun z hz => ?_) (fun c x h _ => ?_) ?_)
    (tag_bis N g'.E a))
  · obtain ⟨b, -, rfl⟩ := mem_tg.mp hz
    exact kp_fresh N b
  · obtain ⟨c', x', rfl, -, hcx⟩ := pr_tagE.mp h
    exact mem_tg.mpr ⟨c', mem_union_iff.mpr (Or.inl (pr_fld hcx).1), rfl⟩
  · exact mem_tg.mpr ⟨a, by simp, rfl⟩

/-! ### The membership graph of a set -/

/-- The membership relation on the members of `X`, as a graph. -/
noncomputable def EX (X : V) : V := relB (k := 0) (BDef.mem 0 1) X X ![]

theorem pr_EX {X a b : V} : Pr (EX X) a b ↔ a ∈ X ∧ b ∈ X ∧ a ∈ b :=
  pr_relB (BDef.mem 0 1) X X ![] a b

theorem ex_wf (X : V) : WFG (EX X) := by
  intro S hS
  obtain ⟨m, hm, hmin⟩ := m_found S hS
  exact ⟨m, hm, fun c hc hcm => hmin c hc (pr_EX.mp hcm).2.2⟩

/-- The membership graph of `X`, pointed at `a`. -/
noncomputable def gX (X a : V) : PG V := ⟨EX X, a, ex_wf X⟩

/-- The class of the membership graph of `X` pointed at `a`. -/
noncomputable def jX (X a : V) : QG V := mkQ (gX X a)

/-- **The members of `jX X b`**, for a member `b` of a transitive set `X`. -/
theorem mem_jX {X b : V} (hX : Tr X) (hb : b ∈ X) {x : QG V} :
    x ∈ jX X b ↔ ∃ a, a ∈ b ∧ x = jX X a := by
  show x ∈ mkQ (gX X b) ↔ _
  rw [mem_mkQ]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (pr_EX.mp hc).2.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, pr_EX.mpr ⟨hX b hb a ha, hb, ha⟩, rfl⟩

/-! ### Membership of classes, bounded -/

theorem memCh_iff (g gz : PG V) {c : V} (hc : c ∈ nodes g) :
    MemCh c (℘ (prodS (nodes g) (nodes gz))) g.E gz.E gz.p ↔ mkQ (g.at c) ∈ mkQ gz := by
  rw [mkQ_mem]
  constructor
  · rintro ⟨e, he, w, -, d, -, hop, k⟩
    exact ⟨d, ⟨e, he, hop⟩, bisIn_bis k⟩
  · rintro ⟨d, ⟨e, he, hop⟩, k⟩
    obtain ⟨w, hw, hdw⟩ := pr_fst_mem hop
    exact ⟨e, he, w, hw, d, hdw, hop, bis_trim (fld_sub_nodes g) hc (fld_sub_nodes gz)
      (fld_sub_nodes gz _ (pr_fld ⟨e, he, hop⟩).1) k⟩

/-! ### Pairs, power sets, transitive containment, infinity -/

theorem qg_pair (x y : QG V) : ∃ p : QG V, x ∈ p ∧ y ∈ p := by
  obtain ⟨g, rfl⟩ := exists_rep x
  obtain ⟨g', rfl⟩ := exists_rep y
  let s : PG V := g.sum g'
  let q : V := kp (nodes g) g'.p
  let N₂ : V := nodes s ∪ {q}
  have hN₂ : ∀ c x, Pr s.E c x → c ∈ N₂ ∧ x ∈ N₂ := fun c x h =>
    ⟨mem_union_iff.mpr (Or.inl (nodes_ok s c x h).1),
      mem_union_iff.mpr (Or.inl (nodes_ok s c x h).2)⟩
  have hp : g.p ∈ nodes s := p_mem_nodes s
  have hS : ∀ a, a ∈ ({g.p, q} : V) → a ∈ N₂ := by
    intro a ha
    rcases (by simpa using ha : a = g.p ∨ a = q) with rfl | rfl
    · exact mem_union_iff.mpr (Or.inl hp)
    · exact mem_union_iff.mpr (Or.inr (by simp))
  refine ⟨mkS s N₂ hN₂ {g.p, q}, (mem_mkS s N₂ hN₂ hS).mpr ⟨g.p, by simp, ?_⟩,
    (mem_mkS s N₂ hN₂ hS).mpr ⟨q, by simp, ?_⟩⟩
  · exact (sum_left g g' (p_mem_nodes g)).symm
  · exact (sum_right g g' g'.p).symm

theorem qg_power (x : QG V) : ∃ p : QG V, ∀ z : QG V, (∀ w, w ∈ z → w ∈ x) → z ∈ p := by
  obtain ⟨g, rfl⟩ := exists_rep x
  let N : V := nodes g
  have hN := nodes_ok g
  let C : V := sepB (k := 2) (prB.comp ![1, 0, 2]) N ![g.E, g.p]
  have hC : ∀ c, c ∈ C ↔ Pr g.E c g.p := fun c =>
    (mem_sepB _ _ _ c).trans ⟨fun k => k.2, fun k => ⟨(hN c _ k).1, k⟩⟩
  let Ch : V := relB (k := 0) (BDef.mem 0 1) C (℘ C) ![]
  have hCh : ∀ a s, Pr Ch a s ↔ a ∈ C ∧ s ∈ ℘ C ∧ a ∈ s := fun a s => pr_relB _ C (℘ C) ![] a s
  let G : PG V := g.adj Ch (℘ C) N hN
  refine ⟨mkQ G, fun z hz => ?_⟩
  obtain ⟨gz, rfl⟩ := exists_rep z
  let s : V := sepB (k := 4) memChB C ![℘ (prodS N (nodes gz)), g.E, gz.E, gz.p]
  have hs : ∀ c, c ∈ s ↔ c ∈ C ∧ mkQ (g.at c) ∈ mkQ gz := by
    intro c
    refine (mem_sepB _ _ _ c).trans (and_congr_right fun hc => ?_)
    exact memCh_iff g gz (hN c _ ((hC c).mp hc)).1
  have hsI : s ∈ ℘ C := mem_power_iff.mpr fun c hc => ((hs c).mp hc).1
  refine (mem_adj_top g Ch (℘ C) N hN).mpr ⟨s, hsI, qg_ext _ _ fun w => ?_⟩
  rw [mem_adj_new]
  constructor
  · intro hw
    obtain ⟨c, hc, rfl⟩ := mem_mkQ.mp (hz w hw)
    have hcs : c ∈ s := (hs c).mpr ⟨(hC c).mpr hc, hw⟩
    exact ⟨c, (hN c _ hc).1, hsI, (hCh c s).mpr ⟨(hC c).mpr hc, hsI, hcs⟩, rfl⟩
  · rintro ⟨a, -, -, hch, rfl⟩
    exact ((hs a).mp ((hCh a s).mp hch).2.2).2

theorem qg_tco (x : QG V) :
    ∃ t : QG V, (∀ z, z ∈ x → z ∈ t) ∧ ∀ y, y ∈ t → ∀ z, z ∈ y → z ∈ t := by
  obtain ⟨g, rfl⟩ := exists_rep x
  have hN := nodes_ok g
  have hm := fun {x : QG V} => mem_mkS g (nodes g) hN (S := nodes g) (fun _ h => h) (x := x)
  refine ⟨mkS g (nodes g) hN (nodes g), fun z hz => ?_, fun y hy z hz => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := mem_mkQ.mp hz
    exact hm.mpr ⟨c, (hN c _ hc).1, rfl⟩
  · obtain ⟨a, -, rfl⟩ := hm.mp hy
    obtain ⟨c, hc, rfl⟩ := mem_mkQ.mp hz
    exact hm.mpr ⟨c, (hN c _ hc).1, rfl⟩

theorem qg_inf : ∃ I : QG V, (∃ e, e ∈ I ∧ ∀ z, z ∉ e) ∧
    ∀ x, x ∈ I → ∃ x', x' ∈ I ∧ ∀ z, z ∈ x' ↔ z = x ∨ z ∈ x := by
  let X : V := sc (om : V)
  have hX : Tr X := fun y hy z hz => by
    rcases mem_sc.mp hy with e | e
    · rw [e] at hz
      exact mem_sc.mpr (Or.inr hz)
    · exact mem_sc.mpr (Or.inr (om_tr y e z hz))
  have homX : (om : V) ∈ X := self_mem_sc _
  have inX : ∀ {n : V}, n ∈ (om : V) → n ∈ X := fun h => mem_sc.mpr (Or.inr h)
  refine ⟨jX X om, ⟨jX X ∅, (mem_jX hX homX).mpr ⟨∅, empty_mem_om, rfl⟩, fun z hz => ?_⟩,
    fun x hx => ?_⟩
  · obtain ⟨a, ha, -⟩ := (mem_jX hX (inX empty_mem_om)).mp hz
    exact absurd ha (by simp)
  · obtain ⟨n, hn, rfl⟩ := (mem_jX hX homX).mp hx
    have hsn : sc n ∈ (om : V) := sc_mem_om hn
    refine ⟨jX X (sc n), (mem_jX hX homX).mpr ⟨sc n, hsn, rfl⟩, fun z => ?_⟩
    rw [mem_jX hX (inX hsn)]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases mem_sc.mp ha with e | e
      · exact Or.inl (by rw [e])
      · exact Or.inr ((mem_jX hX (inX hn)).mpr ⟨a, e, rfl⟩)
    · rintro (rfl | hz)
      · exact ⟨n, self_mem_sc n, rfl⟩
      · obtain ⟨a, ha, rfl⟩ := (mem_jX hX (inX hn)).mp hz
        exact ⟨a, mem_sc.mpr (Or.inr ha), rfl⟩

end ops

end MG

end FFL.FirstOrder.SetTheory
