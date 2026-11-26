module

public import FnSets

@[expose] public section


set_option autoImplicit false
namespace FFL.FirstOrder.FNF.CountSet
open JensenNFU.TFm (scons)

variable {M : Type} [Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] [Nonempty M]
  [M↓[ℒλ] ⊧* 𝗙𝗡𝗙]
local infixl:70 " ⬝ " => App

/-- The exact Kuratowski-pair graph of singletons on an internal set exists internally. -/
def Strong (d : M) : Prop := ∃ g : M, IsSet g ∧ ∀ p, Mem p g ↔ ∃ x, Mem x d ∧ p = kp x (sing x)

/-- An internally represented self-injection omits a member of its own source. -/
def Dedekind (d : M) : Prop := ∃ f t : M, IsSet f ∧ Inj f d d ∧ Mem t d ∧ ∀ x, ¬ Ap f x t

noncomputable section
private theorem exists_range (j : M) : ∃ d : M, IsSet d ∧ ∀ a, Mem a d ↔ ∃ b, j ⬝ b = a := by
  exact (BT.ex (Γ := [0,1]) 0 (BT.app 2 0 1 0 rfl rfl rfl)).set (fun _ => j)

theorem graph (d j : M) : ∃ f : M, IsSet f ∧ ∀ p,
    Mem p f ↔ ∃ x y, p = kp x y ∧ Mem x d ∧ j ⬝ x = y := by
  exact (BT.ex (Γ := [2,1,1]) 0 (BT.ex 0 ((kpB.sub [2,1,0] 0).and
    ((BT.mem 1 3 0 rfl rfl).and (BT.app 4 1 0 0 rfl rfl rfl))))).set (scons d (fun _ => j))

theorem liftGraph (d j q : M) : ∃ g : M, IsSet g ∧ ∀ p,
    Mem p g ↔ ∃ x y w t, p = kp x y ∧ Mem x d ∧ j ⬝ x = w ∧ w ⬝ q = t ∧ y = sing t := by
  exact (BT.ex (Γ := [3,2,2,0]) 1 (BT.ex 1 (BT.ex 1 (BT.ex 0 ((kpB.sub [4,3,2] 1).and
   ((BT.mem 3 5 1 rfl rfl).and ((BT.app 6 3 1 1 rfl rfl rfl).and
    ((BT.app 1 7 0 0 rfl rfl rfl).and (singB.sub [2,0] 0))))))))).set (scons d (scons j (fun _ => q)))

theorem exists_strong_dedekind (j q : M) (fixedFree : ∀ a, q ⬝ a ≠ a)
    (diagonal : ∀ a, (j ⬝ a) ⬝ a = a)
    (scalar : ∀ a, (j ⬝ (j ⬝ a)) ⬝ q = j ⬝ a) :
    ∃ d : M, IsSet d ∧ Strong d ∧ Dedekind d := by
  obtain ⟨d,hd,range⟩ := exists_range j
  have member (x : M) : Mem (j ⬝ x) d := (range _).mpr ⟨x,rfl⟩
  have cancel {x : M} (hx : Mem x d) : (j ⬝ x) ⬝ q = x := by
    obtain ⟨a,rfl⟩ := (range x).mp hx
    exact scalar a
  obtain ⟨g,hg,lift⟩ := liftGraph d j q
  have strong : Strong d := by
    refine ⟨g,hg,fun p => ?_⟩
    rw [lift]
    constructor
    · rintro ⟨x,y,_,_,pair,mem,rfl,rfl,rfl⟩
      exact ⟨x,mem,by simpa only [cancel mem] using pair⟩
    · rintro ⟨x,h,rfl⟩
      exact ⟨x,sing x,j ⬝ x,x,rfl,h,rfl,cancel h,rfl⟩
  obtain ⟨f,hf,graph⟩ := graph d j
  have appgraph (a b : M) : Ap f a b ↔ Mem a d ∧ j ⬝ a = b := by
    change Mem (kp a b) f ↔ _
    rw [graph]
    constructor
    · rintro ⟨x,y,p,mem,val⟩
      obtain ⟨rfl,rfl⟩ := kp_inj p
      exact ⟨mem,val⟩
    · rintro ⟨mem,val⟩
      exact ⟨a,b,rfl,mem,val⟩
  have inj : Inj f d d := by
    constructor
    · intro x y h
      obtain ⟨mem,rfl⟩ := (appgraph _ _).mp h
      exact ⟨mem,member x⟩
    · exact fun x hx => ⟨_,(appgraph _ _).mpr ⟨hx,rfl⟩⟩
    · intro x y z ha hb
      exact ((appgraph _ _).mp ha).2.symm.trans ((appgraph _ _).mp hb).2
    · intro x y z hx hy
      obtain ⟨mx,ex⟩ := (appgraph _ _).mp hx
      obtain ⟨my,ey⟩ := (appgraph _ _).mp hy
      exact (cancel mx).symm.trans ((congrArg (fun a => a ⬝ q) (ex.trans ey.symm)).trans (cancel my))
  refine ⟨d,hd,strong,f,j ⬝ q,hf,inj,member q,?_⟩
  intro x atX
  obtain ⟨hx,he⟩ := (appgraph _ _).mp atX
  have equal : x = q := (cancel hx).symm.trans ((congrArg (fun a => a ⬝ q) he).trans (diagonal q))
  subst x
  obtain ⟨y,ey⟩ := (range q).mp hx
  exact fixedFree y (ey ▸ diagonal y)
end
end FFL.FirstOrder.FNF.CountSet
#print axioms FFL.FirstOrder.FNF.CountSet.exists_strong_dedekind
