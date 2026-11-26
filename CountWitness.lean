module

public import CountSet
public import OrbitCounting
public import FunctionCut

@[expose] public section


set_option autoImplicit false
namespace FFL.FirstOrder.FNF.CountSet
noncomputable section
variable {V : Type} [Tarski.Structure ℒλ V] [Tarski.Structure.Eq ℒλ V] [Nonempty V]
  [V↓[ℒλ] ⊧* 𝗙𝗡𝗙]

structure ProperMap {W : Type} [Nonempty W] (M : NFUCut.Model W) (d f t : W) (F : W → W) : Prop where
  strong : M.SC d
  seed : M.mem t d
  maps : ∀ x, M.mem x d → M.mem (F x) d
  injective : ∀ x y, M.mem x d → M.mem y d → F x = F y → x = y
  misses : ∀ x, M.mem x d → F x ≠ t
  graph : ∀ x y, M.mem x d → (M.mem (M.op x y) f ↔ F x = y)

/-- The characteristic sets in the function model form a Jensen NFU model with full Counting. -/
theorem model_with_strong_dedekind (d : V) (strong : Strong d) (ded : Dedekind d) :
    ∃ M : NFUCut.Model V, ∃ h : Fact M.Infinity, letI := h; (∀ n : M.Num, M.T n = n) ∧ ∃ f t F, ProperMap M d f t F := by
  classical
  let M := FunctionCut.model (M:=V)
  have inf : M.Infinity := FunctionCut.infinity
  letI : Fact M.Infinity := ⟨inf⟩
  have mm (a b : V) : M.mem a b ↔ Mem a b := Iff.rfl
  have isSet {x : V} (hx : IsSet x) : M.isSet x := hx
  have one (a : V) : M.sing a = sing a := M.ext (M.sing_isSet a) (isSet isSet_sing)
    (fun z => M.mem_sing.trans mem_sing.symm)
  have pair (a b : V) : M.up a b = upr a b := M.ext (M.up_isSet a b) (isSet isSet_upr)
    (fun z => M.mem_up.trans mem_upr.symm)
  have op (a b : V) : M.op a b = kp a b := by
    simp only [NFUCut.Model.op,kp,one,pair]
  obtain ⟨g,_,hg⟩ := strong
  have sc : M.SC d := by
    refine ⟨g,fun p => ?_⟩
    simpa only [mm,op,one] using hg p
  obtain ⟨f,t,_,inj,ht,miss⟩ := ded
  let F : V → V := fun x => if h : Mem x d then (inj.tot x h).choose else x
  have spec (x : V) (h : Mem x d) : Ap f x (F x) := by
    simpa only [F,dif_pos h] using (inj.tot x h).choose_spec
  have proper : ProperMap M d f t F := by
    refine ⟨sc,ht,?_,?_,?_,?_⟩
    · exact fun x hx => (inj.dom _ _ (spec x hx)).2
    · intro x y hx hy eq
      exact inj.inj _ _ _ (spec x hx) (eq ▸ spec y hy)
    · intro x hx eq
      exact miss x (eq ▸ spec x hx)
    · intro x y hx
      rw [op]
      change Ap f x y ↔ F x = y
      exact ⟨fun h => inj.func _ _ _ (spec x hx) h, fun h => h ▸ spec x hx⟩
  exact ⟨M,⟨inf⟩,NFUCut.Model.OrbitCounting.counting M d f t F sc ht
    proper.maps proper.injective proper.misses proper.graph,f,t,F,proper⟩

end
end FFL.FirstOrder.FNF.CountSet
#print axioms FFL.FirstOrder.FNF.CountSet.model_with_strong_dedekind
