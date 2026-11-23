module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle575
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle634
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle067
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

def pmap2 {A A' : Over S} (q : A ⟶ A') (T : Over S) : A ⊗ (A ⊗ T) ⟶ A' ⊗ (A' ⊗ T) :=
  lift (fst A (A ⊗ T) ≫ q) (snd A (A ⊗ T) ≫ pmap q T)

def ptFst (A T : Over S) : A ⊗ (A ⊗ T) ⟶ A ⊗ T := lift (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T)

def ptSnd (A T : Over S) : A ⊗ (A ⊗ T) ⟶ A ⊗ T := lift (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)

def ptMul (A T : Over S) [MonObj A] : A ⊗ (A ⊗ T) ⟶ A ⊗ T :=
  lift (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T)

def addBundle {A T : Over S} [MonObj A] (M : LB (A ⊗ T).left) : LB (A ⊗ (A ⊗ T)).left :=
  LB.div (tens (ev M (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T))
      (ev M (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)))
    (ev M (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T))

theorem preimage_le_of_comp {X Y Z W : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ W} {f' : X ⟶ Z} {g' : Z ⟶ W}
    (h : f ≫ g = f' ≫ g') (U : W.Opens) : f ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ f' ⁻¹ᵁ (g' ⁻¹ᵁ U) := by
  intro x hx
  have e : g.base (f.base x) = g'.base (f'.base x) := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  show g'.base (f'.base x) ∈ U
  rw [← e]
  exact hx

theorem prodMapPairTimesIdentity_fst {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    (pmap2 q T).left ≫ (lift (fst A' (A' ⊗ T)) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptFst A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptFst, pmap]

theorem prodMapPairTimesIdentity_snd {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    (pmap2 q T).left ≫ (lift (snd A' (A' ⊗ T) ≫ fst A' T) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptSnd A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptSnd, pmap]

theorem prodMapPairTimesIdentity_mul {A A' : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (T : Over S) :
    (pmap2 q T).left ≫ (lift (fst A' (A' ⊗ T) * (snd A' (A' ⊗ T) ≫ fst A' T)) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptMul A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptMul, pmap, MonObj.comp_mul, MonObj.mul_comp]

theorem addGen_le₁ {A A' T : Over S} [MonObj A'] (q : A ⟶ A') (M : LB (A' ⊗ T).left) (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptFst A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.1.1 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_fst q T) _)
  intro x hx
  exact LB.wchart_le M _ k.1.1 PUnit.unit hx.1.1

theorem addGen_le₂ {A A' T : Over S} [MonObj A'] (q : A ⟶ A') (M : LB (A' ⊗ T).left) (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptSnd A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.1.2 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_snd q T) _)
  intro x hx
  exact LB.wchart_le M _ k.1.2 PUnit.unit hx.1.2

theorem addGen_le₃ {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left)
    (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptMul A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.2 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_mul q T) _)
  intro x hx
  exact LB.wchart_le M _ k.2 PUnit.unit hx.2

def addGen {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left)
    (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) (k : (addBundle M).ι) :
    Γ((A ⊗ (A ⊗ T)).left, (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)ˣ :=
  res (addGen_le₁ q M k) (pullU (ptFst A T).left _ (e (k.1.1 PUnit.unit))) *
    res (addGen_le₂ q M k) (pullU (ptSnd A T).left _ (e (k.1.2 PUnit.unit))) *
    (res (addGen_le₃ q M k) (pullU (ptMul A T).left _ (e (k.2 PUnit.unit))))⁻¹

end GlobalTheory.CharKer
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistFlat

theorem pull_restrict_eq_zero_iff {X₁ X₂ Z : Scheme.{0}} (f₁ : X₁ ⟶ Z) (f₂ : X₂ ⟶ Z) (h : X₁ ⟶ X₂) (k : X₂ ⟶ X₁)
    (hk : k ≫ h = 𝟙 X₂) (hf : h ≫ f₂ = f₁) (hf' : k ≫ f₁ = f₂) (U : Z.Opens) (c : Pic X₂) :
    CechPic.pull (f₁ ⁻¹ᵁ U).ι (CechPic.pull h c) = 0 ↔ CechPic.pull (f₂ ⁻¹ᵁ U).ι c = 0 := by
  constructor
  · intro e
    have e' := pull_eq_zero_of_mem (f₁ ⁻¹ᵁ U) ((f₂ ⁻¹ᵁ U).ι ≫ k) (fun z ↦ by
      show f₁ (k ((f₂ ⁻¹ᵁ U).ι z)) ∈ U
      rw [← Scheme.Hom.comp_apply, hf']
      exact z.2) (c := CechPic.pull h c) e
    rwa [← pull_comp, Category.assoc, hk, Category.comp_id] at e'
  · intro e
    rw [← pull_comp]
    exact pull_eq_zero_of_mem (f₂ ⁻¹ᵁ U) ((f₁ ⁻¹ᵁ U).ι ≫ h) (fun z ↦ by
      show f₂ (h ((f₁ ⁻¹ᵁ U).ι z)) ∈ U
      rw [← Scheme.Hom.comp_apply, hf]
      exact z.2) e

section Iso
variable {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left)
  (Y : Over (Sp V))

def cmpHom : pullback Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ⟶ pullback (Y.hom ≫ φ ≫ T.hom) A.hom :=
  pullback.lift (pullback.fst Y.hom _) (pullback.snd Y.hom _ ≫ pullback.fst A.hom (φ ≫ T.hom)) (by
    rw [← Category.assoc, pullback.condition, Category.assoc, Category.assoc, pullback.condition])

def cmpInv : pullback (Y.hom ≫ φ ≫ T.hom) A.hom ⟶ pullback Y.hom (pullback.snd A.hom (φ ≫ T.hom)) :=
  pullback.lift (pullback.fst _ A.hom)
    (pullback.lift (pullback.snd _ A.hom) (pullback.fst _ A.hom ≫ Y.hom) (by
      rw [Category.assoc]; exact pullback.condition.symm)) (pullback.lift_snd _ _ _).symm

theorem cmpInv_hom : cmpInv A φ Y ≫ cmpHom A φ Y = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [cmpHom, cmpInv, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.id_comp]

theorem cmpHom_fst : cmpHom A φ Y ≫ pullback.fst _ A.hom = pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) :=
  pullback.lift_fst _ _ _

theorem cmpInv_fst : cmpInv A φ Y ≫ pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) = pullback.fst _ A.hom :=
  pullback.lift_fst _ _ _

theorem cmpHom_snd : cmpHom A φ Y ≫ pullback.snd (Y.hom ≫ φ ≫ T.hom) A.hom =
    pullback.snd Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ pullback.fst A.hom (φ ≫ T.hom) :=
  pullback.lift_snd _ _ _

end Iso

section Main
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V]
  (φ : Sp V ⟶ T.left)

def cmpOver (Y : Over (Sp V)) : Over.mk ((Y ⊗ bc A φ).hom ≫ φ ≫ T.hom) ⟶ up φ Y ⊗ A :=
  Over.homMk (cmpHom A φ Y) (by
    show cmpHom A φ Y ≫ (up φ Y ⊗ A).hom = (Y ⊗ bc A φ).hom ≫ φ ≫ T.hom
    rw [← Over.w (fst (up φ Y) A), ← Over.w (fst Y (bc A φ))]
    show cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ (Y.hom ≫ φ ≫ T.hom) =
      (pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ Y.hom) ≫ φ ≫ T.hom
    rw [← Category.assoc, cmpHom_fst, Category.assoc])

theorem mul_left_fst {Y : Over (Sp V)} (x : Y ⟶ bc A φ) :
    ((fst Y (bc A φ) ≫ x) * snd Y (bc A φ)).left ≫ pullback.fst A.hom (φ ≫ T.hom) =
      cmpHom A φ Y ≫ ((fst (up φ Y) A ≫ upa φ x) * snd (up φ Y) A).left := by
  have hG := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (φ ≫ T.hom)).2 (Y ⊗ bc A φ)
    (fst Y (bc A φ) ≫ x) (snd Y (bc A φ)) (cmpOver A φ Y ≫ fst (up φ Y) A ≫ upa φ x)
    (cmpOver A φ Y ≫ snd (up φ Y) A) (by
      show cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ x.left ≫ pullback.fst A.hom (φ ≫ T.hom) =
        (pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ x.left) ≫ pullback.fst A.hom (φ ≫ T.hom)
      rw [← Category.assoc, cmpHom_fst, Category.assoc]) (cmpHom_snd A φ Y)
  rw [← MonObj.comp_mul] at hG
  exact hG.symm

theorem snd_lift_pa_pt (Y : Over (Sp V)) :
    (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ)).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y)).left := by
  apply pullback.hom_ext
  · show (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ) ≫ fst A T).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y) ≫ fst A T).left
    rw [lift_fst, lift_fst]
    exact (cmpHom_snd A φ Y).symm
  · show (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ) ≫ snd A T).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y) ≫ snd A T).left
    rw [lift_snd, lift_snd]
    show pullback.snd Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ pullback.snd A.hom (φ ≫ T.hom) ≫ φ =
      cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ Y.hom ≫ φ
    rw [← Category.assoc (cmpHom A φ Y), cmpHom_fst, ← Category.assoc, ← pullback.condition, Category.assoc]

theorem triv_pull_iff {X : Scheme.{0}} {D : LB X} (hD : D.IsLB) (W : X.Opens) :
    Triv (D.pull W.ι) ↔ CechPic.pull W.ι (cls D hD) = 0 := by
  unfold Triv
  rw [← cls_eq_zero_iff (pull_isLB hD _), cls_pull hD]

local instance (priority := high) grpObjTwistBC : GrpObj (bc A φ) :=
  let f := φ ≫ T.hom
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

theorem triv_twist_iff (L : LB A.left) (hL : L.IsLB) (N : LB (A ⊗ T).left) (hN : N.IsLB) (Y : Over (Sp V))
    (x : Y ⟶ bc A φ) (U : Y.left.Opens) :
    Triv ((LB.div (translDiff (bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x)
        ((twist A φ N).pull (snd Y (bc A φ)).left)).pull ((fst Y (bc A φ)).left ⁻¹ᵁ U).ι) ↔
      Triv ((LB.div (translDiff A L (upa φ x)) (ev N (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y))).pull
        ((fst (up φ Y) A).left ⁻¹ᵁ U).ι) := by
  have hL' : (L.pull (pullback.fst A.hom (φ ≫ T.hom))).IsLB := pull_isLB hL _
  have h₁ : (translDiff (bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x).IsLB := LB.isLB_linComb hL' _ _
  have hO : (twist A φ N).IsLB := pull_isLB hN _
  have h₂ : ((twist A φ N).pull (snd Y (bc A φ)).left).IsLB := pull_isLB hO _
  have h₃ : (translDiff A L (upa φ x)).IsLB := LB.isLB_linComb hL _ _
  have h₄ : (ev N (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y)).IsLB := pull_isLB hN _
  have hc : cls _ (LB.isLB_div h₁ h₂) = CechPic.pull (cmpHom A φ Y) (cls _ (LB.isLB_div h₃ h₄)) := by
    rw [cls_div h₁ h₂, cls_div h₃ h₄, map_sub]
    have e₁ := pull_translDiff hL' x h₁ (fst Y (bc A φ)) (snd Y (bc A φ))
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have e₂ := pull_translDiff hL (upa φ x) h₃ (fst (up φ Y) A) (snd (up φ Y) A)
    rw [lift_fst_snd, Over.id_left, pull_id] at e₂
    rw [e₁, e₂, map_sub, cls_pull hL, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, mul_left_fst]
    have e₅ : (snd Y (bc A φ)).left ≫ pullback.fst A.hom (φ ≫ T.hom) = cmpHom A φ Y ≫ (snd (up φ Y) A).left :=
      (cmpHom_snd A φ Y).symm
    rw [e₅, cls_pull hO _ h₂,
      show cls (twist A φ N) hO = CechPic.pull (lift (pa A φ) (pt A φ)).left (cls N hN) from cls_pull hN _ hO,
      cls_pull hN, ← pull_comp, ← pull_comp, snd_lift_pa_pt]
  rw [triv_pull_iff (LB.isLB_div h₁ h₂), triv_pull_iff (LB.isLB_div h₃ h₄), hc]
  exact pull_restrict_eq_zero_iff _ _ (cmpHom A φ Y) (cmpInv A φ Y) (cmpInv_hom A φ Y) (cmpHom_fst A φ Y)
    (cmpInv_fst A φ Y) U _

end Main

end GlobalTheory.TwistFlat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixUnit

theorem ratio_unit_eq_one : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), IsAbelianScheme A → L.IsLB → M.IsLB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (α α₂ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) (v : Γ(A'.left, ⊤)ˣ), IsTest A B L M t A' B' φA' φB' Φ' → ψA ≫ (snd (topS Rg) A).left = φA' → ψB ≫ (snd (topS Rg) B).left = φB' → (∀ p, α.s p = res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v * α₂.s p) → RigEq L M k eA eB t Φ' ψA ψB α → RigEq L M k eA eB t Φ' ψA ψB α₂ → v = 1 := by
  intro Rg _ A B _ _ L M k eA eB hA hL hM R _ t A' B' _ _ φA' φB' Φ' ψA ψB α α₂ v hT hψA hψB hv hα hα₂
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hT.1
  refine Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.unit_eq_one_of_eSec GlobalTheory.globalFns_holds A' hA' v ?_
  show (zeroPt A').appTop.hom v.val = 1
  let W : ((Fin 1 → M.ι) × (Fin 1 → L.ι)) → (Sp R).Opens := fun p =>
    (zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
      t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
      t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0)
  have hloc : ∀ p, ((Sp R).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op).hom
      ((zeroPt A').appTop.hom v.val) = 1 := by
    intro p
    have h1 := hα p
    have h2 := hα₂ p
    rw [hv p, Units.val_mul, map_mul] at h1
    have hres : (Scheme.Hom.appLE (zeroPt A') ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (W p)
        (inf_le_left.trans inf_le_left)).hom
          ((res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ) : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)) =
        ((Sp R).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op).hom ((zeroPt A').appTop.hom v.val) := by
      show (A'.left.presheaf.map (homOfLE (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤)).op ≫
        Scheme.Hom.appLE (zeroPt A') ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (W p)
          (inf_le_left.trans inf_le_left)).hom v.val = _
      rw [Scheme.Hom.map_appLE]
      rfl
    rw [hres] at h1
    have key := h1.trans h2.symm
    rw [_root_.mul_assoc] at key
    exact (IsUnit.mul_left_inj (IsUnit.mul ((α₂.s p).isUnit.map _) (((eA.s _).isUnit.map _).pow k))).1
      (key.trans (_root_.one_mul _).symm)
  have hcov : (⊤ : (Sp R).Opens) ≤ iSup W := by
    rintro x -
    have hc : ∀ {X : Scheme.{0}} (N : LB X), N.IsLB → ∀ y : X, ∃ i, y ∈ N.U i := fun N hN y =>
      TopologicalSpace.Opens.mem_iSup.1 (by rw [hN.cover]; trivial)
    obtain ⟨iL, hiL⟩ := hc L hL ((eSec A) (t x))
    obtain ⟨iM, hiM⟩ := hc M hM ((eSec B) (t x))
    haveI := hT.2.2.1
    have eA' : zeroPt A' ≫ ψA ≫ (snd (topS Rg) A).left = t ≫ eSec A := by
      rw [hψA]; exact GlobalTheory.UU.eSec_comp_of_isGrpPullback hT.1
    have eB' : zeroPt A' ≫ (Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left = t ≫ eSec B := by
      have h0 : zeroPt A' ≫ Φ'.left = zeroPt B' := congrArg Over.Hom.left (IsMonHom.one_hom Φ')
      rw [Category.assoc, hψB, ← Category.assoc, h0]
      exact GlobalTheory.UU.eSec_comp_of_isGrpPullback hT.2.1
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => iM, fun _ => iL), ?_⟩
    refine ⟨⟨⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩, Set.mem_iInter.2 fun _ => hiL⟩,
      Set.mem_iInter.2 fun _ => hiM⟩
    · show ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (zeroPt A' x) ∈ M.U iM
      rw [← Scheme.Hom.comp_apply, eB', Scheme.Hom.comp_apply]
      exact hiM
    · show (ψA ≫ (snd (topS Rg) A).left) (zeroPt A' x) ∈ L.U iL
      rw [← Scheme.Hom.comp_apply, eA', Scheme.Hom.comp_apply]
      exact hiL
  exact TopCat.Sheaf.eq_of_locally_eq' (Sp R).sheaf W ⊤ (fun p => homOfLE le_top) hcov _ 1
    (fun p => (hloc p).trans (map_one ((Sp R).presheaf.map (homOfLE le_top : W p ⟶ ⊤).op).hom).symm)

end GlobalTheory.HomFixUnit
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section

namespace GlobalTheory.Mum.EndThick

theorem commGroup_torusCoordinate_mul_identity {U : Type} [CommGroup U] {vxy wXY ux uy vX vY wx wy c₁ c₂ uxy : U}
    (m₁ : wXY * c₁ = vX * vY) (m₂ : vxy * c₂ = wx * wy) (r : uxy * c₁ = c₂ * (ux * uy))
    (ex : vX = wx * ux) (ey : vY = wy * uy) : vxy * uxy = wXY := by
  rw [eq_mul_inv_of_mul_eq m₁, eq_mul_inv_of_mul_eq m₂, eq_mul_inv_of_mul_eq r, ex, ey]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel


open GlobalTheory.TorusCoord GlobalTheory.OLinearCompare in
theorem isMonHom_of_isCoordEnd : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), (∀ χ, D.c (h' χ) = D.c χ ≫ a') → ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → IsMonHom F := by
  intro R _ _ I D e G _ _ g a a' _ _ h' hc u hu h₀ F hF
  obtain ⟨hF₁, hF₂⟩ := hF
  have hG := GlobalTheory.globalFns_holds
  have him : ∀ {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G),
      im g (x ≫ F) = im g x ≫ a := fun x =>
    Over.OverMorphism.ext ((Category.assoc x.left F.left _).trans
      ((congrArg (x.left ≫ ·) hF₁).trans (Category.assoc _ _ _).symm))
  have hU : ∀ {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G) (χ : D.X)
      (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left) x.left z J =
        val₂ u z J (cPt T χ) (im g x) :=
    fun x χ z J hJ => val_pull_lift u χ g.pG ((Over.map (thick R I e)).map x) hJ
  have mul : ∀ (T) (x y : T ⟶ thickObj R I e G), (x * y) ≫ F = (x ≫ F) * (y ≫ F) := by
    intro T x y
    refine Over.OverMorphism.ext (ext_of_val g _ _ ?_ fun χ z J hJ => ?_)
    · have : im g ((x * y) ≫ F) = im g ((x ≫ F) * (y ≫ F)) := by
        rw [him, im_mul, im_mul, him, him, MonObj.mul_comp]
      exact congrArg (·.left) this
    · have e₁ := hF₂ χ _ (x * y).left z J hJ
      have ex := hF₂ χ _ x.left z J hJ
      have ey := hF₂ χ _ y.left z J hJ
      have m₁ := val_t_mul_points g hG χ (x ≫ F) (y ≫ F) z J hJ
      have m₂ := val_t_mul_points g hG (h' χ) x y z J hJ
      have r := (ros_add D.cub hG D.P.isAb a' a u hu h₀ hJ (im g x) (im g y) (cPt T χ)).2
      have c₁ : cubeVal g χ z J (x ≫ F) (y ≫ F) = cubV D.cub z J (cPt T χ) (im g x ≫ a) (im g y ≫ a) := by
        unfold cubeVal
        rw [him, him]
      have c₂ : cubeVal g (h' χ) z J x y = cubV D.cub z J (cPt T χ ≫ a') (im g x) (im g y) := by
        unfold cubeVal
        congr 1
        show toUnit _ ≫ D.c (h' χ) = (toUnit _ ≫ D.c χ) ≫ a'
        rw [hc, Category.assoc]
      rw [c₁] at m₁
      rw [c₂] at m₂
      rw [hU _ χ z J hJ, im_mul] at e₁
      rw [hU _ χ z J hJ] at ex ey
      refine e₁.trans (commGroup_torusCoordinate_mul_identity m₁ m₂ r ex ey)
  refine ⟨?_, ?_⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ _ ⟶ thickObj R I e G) ≫ F = 1 := mul_eq_left.1 h.symm
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h'
  · have h := mul _ (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    refine h.trans ?_
    congr 1

end GlobalTheory.Mum.EndThick
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section
namespace GlobalTheory.Mum.EndThick

open GlobalTheory.TorusCoord GlobalTheory.OLinearCompare

theorem q_comm_of_isCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a : D.P.A ⟶ D.P.A) (F : thickObj R I e G ⟶ thickObj R I e G)
    (hF : F.left ≫ g.pG.left = g.pG.left ≫ a.left) :
    F ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map a := by
  ext1
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
    have := hF
    simp only [GtCoord.pG, Over.comp_left, Over.map_map_left, DegPre.prBe, Over.homMk_left] at this
    simpa [Category.assoc] using this
  · simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_snd]
    have h1 : g.q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) :=
      Over.w g.q
    have h2 : F.left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w F
    rw [h1, h2]

theorem torus_of_isCoordEnd : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X, TorusEndOf D.X h' t ∧ g.i ≫ F = t ≫ g.i := by
  intro R _ _ I D e G _ _ g a a' _ _ h' u hu h₀ F hF
  have hb : IsMonHom ((Over.pullback (thick R I e)).map a) := inferInstance
  have hq := q_comm_of_isCoordEnd g a F hF.1
  have hd : (g.i ≫ F) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, g.isKernel.w, Category.assoc, IsMonHom.one_hom]
  obtain ⟨t, ht⟩ : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X,
      t ≫ g.i = g.i ≫ F :=
    ⟨g.isKernel.lift _ _ hd, g.isKernel.lift_fst _ _ hd⟩
  refine ⟨t, fun χ => unit_ext fun y hy => ?_, ht.symm⟩
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.P.L D.P.isLB y
  have hJ : Good D.P.L y J := hJ
  have := g.q_hom
  have v₁ := val_torus g χ hJ t 1
  have v₂ := val_torus g (h' χ) hJ (𝟙 _) 1
  rw [_root_.mul_one, val_unit g _ hJ, _root_.mul_one] at v₁ v₂
  rw [ht] at v₁
  rw [Category.id_comp] at v₂
  have e1 : TorusCoord.im g g.i = 1 := (im_congr g (x' := 1) (by
    rw [g.isKernel.w, MonObj.one_comp, Hom.one_def])).trans (im_one g)
  have v₃ : val (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left) g.i.left y J = 1 :=
    (val_pull_lift u χ g.pG ((Over.map (thick R I e)).map g.i) hJ).trans
      ((congrArg _ e1).trans (val₂_axis D.P.isAb D.P.isLB a' a u hu h₀ hJ _))
  have v₄ := (hF.2 χ _ g.i.left y J hJ).trans ((congrArg₂ (· * ·) v₂ v₃).trans (_root_.mul_one _))
  refine (gm_res _ y (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).trans
    ((gm_pull (𝟙 _) t.left y ⊤ trivial _).trans ?_)
  rw [Category.id_comp]
  rw [Over.comp_left] at v₁
  exact v₁.symm.trans v₄

end GlobalTheory.Mum.EndThick
end
end
