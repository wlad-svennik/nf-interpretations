module

public import ConNF.NF.NFUArith

@[expose] public section
set_option autoImplicit false
namespace NFUCut.Model
open NFUCut
variable {V : Type} [Nonempty V] (M : NFUCut.Model V)

def successorGraph : Fml := .ex 1 (.ex 2 (.and (.mem 1 3) (.and (fOp 0 1 2 9 10) (fSuccEq 2 1))))

theorem exists_successor_graph : ∃ g, M.isSet g ∧ ∀ p,
    M.mem p g ↔ ∃ n, M.mem n M.nat ∧ p = M.op n (M.succ n) := by
  obtain ⟨g,isSet,hg⟩ := M.comp (σW [(0,4),(3,3),(9,3)]) successorGraph 0 (by decide) (fun _ => M.nat)
  refine ⟨g,isSet,fun p => (hg p).trans ?_⟩
  simp [successorGraph,M.sat_ex, Sat, M.sat_fSuccEq, M.sat_fOp (p:=0) (a:=1) (b:=2) (u:=9) (c:=10)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), Function.update_apply]

structure DedekindMap (D g t : V) (F : V → V) : Prop where
  seed : M.mem t D
  maps : ∀ x, M.mem x D → M.mem (F x) D
  injective : ∀ x y, M.mem x D → M.mem y D → F x = F y → x = y
  misses : ∀ x, M.mem x D → F x ≠ t
  graph : ∀ x y, M.mem (M.op x y) g ↔ M.mem x D ∧ F x = y

theorem naturals_dedekind [Fact M.Infinity] : ∃ g, M.isSet g ∧ M.DedekindMap M.nat g M.zero M.succ := by
  obtain ⟨g,hg,e⟩ := M.exists_successor_graph
  refine ⟨g,hg,M.zero_mem_nat,fun _ h=> M.succ_mem_nat h,
    fun _ _ hx hy eq => M.succ_inj hx hy eq,fun x _ => Ne.symm (M.zero_ne_succ x),fun x y=> ?_⟩
  rw [e]
  constructor
  · rintro ⟨n,hn,eq⟩
    obtain ⟨rfl,h⟩ := M.op_inj eq
    exact ⟨hn,h.symm⟩
  · rintro ⟨hx,rfl⟩; exact ⟨_,hx,rfl⟩

end NFUCut.Model
#print axioms NFUCut.Model.naturals_dedekind
