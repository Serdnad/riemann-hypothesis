module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsLBZb
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle005
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle234
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Group.Abelian
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem lam_zb (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L)) :
    pull (sqToBase (G4 (A ⊗ B)) s) (zc hD.isLB l mu α) =
      lam (cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL)) (fst _ _) (snd _ _) := by
  haveI : IsCommMonObj A := hA.comm
  have hw : sqToBase (G4 (A ⊗ B)) s = Over.Hom.left (lift
      (toBase (G4 (A ⊗ B)) s (fst ((Over.pullback s).obj (G4 (A ⊗ B))) ((Over.pullback s).obj (G4 (A ⊗ B)))))
      (toBase (G4 (A ⊗ B)) s (snd ((Over.pullback s).obj (G4 (A ⊗ B))) ((Over.pullback s).obj (G4 (A ⊗ B)))))) := rfl
  rw [zc, hw, pull_zcPair, lift_fst, lift_snd]
  have hc : cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL) =
      cls (L.LinComb (phiL mu s) fun _ => 1) (LB.isLB_linComb hL _ _) +
        cls (P.LinComb (phiP s) fun ij => α ij.1 ij.2) (LB.isLB_linComb hD.isLB _ _) :=
    cls_tens (LB.isLB_linComb hL _ _) (LB.isLB_linComb hD.isLB _ _) (isLB_zb mu α s hD.isLB hL)
  rw [hc, cls_linComb hL, cls_linComb hD.isLB]

  rw [lam_eq_lamHom, map_add (f := _), map_sum, map_sum]
  simp only [map_zsmul, one_smul, ← lam_eq_lamHom, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, line_bundle_pairing_zeroth hD l mu s L hL e, line_bundle_pairing_first hD hD' l mu s L hL e,
    line_bundle_pairing_second hD l mu s L hL e, line_bundle_pairing_third hD hD' l mu s L hL e, lam_phiP hD hD' s, zcPair, smul_add]
  abel

end PositivityTheory.PrwZar
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

theorem surj_of_finite_dimS {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f] (g : ℕ)
    (hX : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = g)
    (hY : ∀ y : Y, IsClosed ({y} : Set Y) → ringKrullDim (Y.presheaf.stalk y) = g)
    (o : X) (ho : IsClosed ({o} : Set X)) : Surjective f := by
  refine ⟨fun y => ?_⟩
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  suffices hη : genericPoint Y ∈ Set.range f by
    have hsub : closure ({genericPoint Y} : Set Y) ⊆ Set.range f :=
      closure_minimal (Set.singleton_subset_iff.mpr hη) hcl
    have hc : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_spec Y
    rw [hc] at hsub
    exact hsub (Set.mem_univ y)
  by_contra hη
  have hmono : StrictMono f := GlobalTheory.FiniteEndFlat.strictMono_of_locallyQuasiFinite f
  let F : WithTop X → Y := fun a => WithTop.recTopCoe (genericPoint Y) (fun x => f x) a
  have hF : StrictMono F := by
    intro a b hab
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe a =>
      induction b using WithTop.recTopCoe with
      | top =>
        refine lt_of_le_of_ne (genericPoint_specializes (f a)) ?_
        intro h
        have hi : Inseparable (f a) (genericPoint Y) := h.symm
        exact hη ⟨a, hi.eq⟩
      | coe b => exact hmono (WithTop.coe_lt_coe.mp hab)
  have h1 := Order.coheight_le_coheight_apply_of_strictMono F hF (o : WithTop X)
  rw [Order.coheight_coe_withTop] at h1
  have hfo : IsClosed ({f o} : Set Y) := by
    have := f.isClosedMap _ ho
    rwa [Set.image_singleton] at this
  have e1 := hX o ho
  have e2 := hY (f o) hfo
  rw [ringKrullDim_stalk_eq_coheight] at e1 e2
  have e1' : Order.coheight o = g := by exact_mod_cast e1
  have e2' : Order.coheight (f o) = g := by exact_mod_cast e2
  change Order.coheight o + 1 ≤ Order.coheight (f o) at h1
  rw [e1', e2'] at h1
  exact absurd h1 (by norm_cast; omega)

theorem isClosed_originS {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] [IsProper G.hom] :
    IsClosed ({η[G].left (IsLocalRing.closedPoint Ω)} : Set G.left) := by
  have hc : IsClosed ({IsLocalRing.closedPoint Ω} : Set (Sp Ω)) := isClosed_singleton
  have h1 := (η[G].left).isClosedEmbedding.isClosedMap _ hc
  convert h1 using 1
  exact (Set.image_singleton).symm

theorem flat_surj_of_finite {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G']
    (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (g : ℕ) (hgG : SmoothOfRelativeDimension g G.hom)
    (hgG' : SmoothOfRelativeDimension g G'.hom) (f : G ⟶ G') [IsMonHom f] (hf : IsFinite f.left) :
    Flat f.left ∧ Surjective f.left := by
  haveI := hG.smooth
  haveI := hG'.smooth
  haveI := hG.proper
  haveI := hG'.proper
  haveI := hf
  haveI : AlgebraicGeometry.IsIntegral G.left := GlobalTheory.isIntegral_of_isAbelianScheme_field Ω G hG
  haveI : AlgebraicGeometry.IsIntegral G'.left := GlobalTheory.isIntegral_of_isAbelianScheme_field Ω G' hG'
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have hsurj : Surjective f.left :=
    surj_of_finite_dimS f.left g
      (fun x hx => GlobalTheory.CutDegree.ringKrullDim_stalk hgG hx)
      (fun y hy => GlobalTheory.CutDegree.ringKrullDim_stalk hgG' hy)
      _ (isClosed_originS (G := G))
  haveI := hsurj
  exact ⟨GlobalTheory.SS.flat_of_isDominant_grpHom Ω G G' f, hsurj⟩

end PositivityTheory.PrwZar.Z2
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.XB

variable {S : Scheme.{0}}

def fourfoldProductMap {G H : Over S} (h : G ⟶ H) : G4 G ⟶ G4 H := h ⊗ₘ (h ⊗ₘ (h ⊗ₘ h))

theorem isFinite_map_g4map {T : Scheme.{0}} (s : T ⟶ S) {G H : Over S} (h : G ⟶ H)
    (hh : IsFinite ((Over.pullback s).map h).left) : IsFinite ((Over.pullback s).map (fourfoldProductMap h)).left :=
  isFinite_map_tensorHom s _ _ hh (isFinite_map_tensorHom s _ _ hh (isFinite_map_tensorHom s _ _ hh hh))

variable {Ω : Type} [Field Ω]

theorem isIso_inv_left {G : Over (Sp Ω)} [GrpObj G] [IsCommMonObj G] : IsIso ((𝟙 G)⁻¹ : G ⟶ G).left := by
  have e : ((𝟙 G)⁻¹ : G ⟶ G) ≫ (𝟙 G)⁻¹ = 𝟙 G := by
    rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
  haveI : IsIso ((𝟙 G)⁻¹ : G ⟶ G) := ⟨⟨(𝟙 G)⁻¹, e, e⟩⟩
  exact (Over.forget (Sp Ω)).map_isIso ((𝟙 G)⁻¹ : G ⟶ G)

theorem relAmple_sym {G : Over (Sp Ω)} [GrpObj G] [IsCommMonObj G] [IsProper G.hom] {L : LB G.left} (hL : L.IsLB)
    (ha : Out.RelAmple G L) :
    Out.RelAmple G (LB.LinComb L (K := Fin 2) ![𝟙 G.left, ((𝟙 G)⁻¹ : G ⟶ G).left] ![1, 1]) := by
  haveI : IsIso ((𝟙 G)⁻¹ : G ⟶ G).left := isIso_inv_left
  haveI : IsAffineHom ((𝟙 G)⁻¹ : G ⟶ G).left := inferInstance
  have hLi : Out.RelAmple G (L.pull ((𝟙 G)⁻¹ : G ⟶ G).left) :=
    GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom _ hL ha
  have hN := LB.isLB_linComb (K := Fin 2) hL ![𝟙 G.left, ((𝟙 G)⁻¹ : G ⟶ G).left] ![1, 1]
  refine GlobalTheory.relAmple_of_isAmpleLB G hN (fun U hU => ?_)
  have hP := LB.isLB_pull hL ((𝟙 G)⁻¹ : G ⟶ G).left
  have h1 := GlobalTheory.isAmpleLB_of_relAmple G hL ha U hU
  have h2 := GlobalTheory.isAmpleLB_of_relAmple G hP hLi U hU
  have a1 := LB.isLB_pull hN (G.hom ⁻¹ᵁ U).ι
  have a2 := LB.isLB_pull hL (G.hom ⁻¹ᵁ U).ι
  have a3 := LB.isLB_pull hP (G.hom ⁻¹ᵁ U).ι
  have a4 := LB.isLB_div a1 a2
  have a5 := LB.isLB_div a4 a3
  refine GlobalTheory.IsAmpleLB.tensor h1 h2 a1 ?_
  rw [← cls_eq_zero_iff a5, cls_div a4 a3 a5, cls_div a1 a2 a4, cls_pull hN _ a1, cls_pull hL _ a2,
    cls_pull hP _ a3, cls_pull hL _ hP, cls_linComb hL _ _ hN]
  simp [Fin.sum_univ_two, pull_id]

end PositivityTheory.PrwZar.XB
end
end
