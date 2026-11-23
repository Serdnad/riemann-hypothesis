module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleFirstOrderTaylorSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCohomologyIsoPresentedCrystal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle944
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle946
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle947
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Obs.GluePair

open Opposite Limits GlobalTheory.LiftSys.Glue

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {X₀ Z₀ : Scheme.{0}} {t₀ : Z₀ ⟶ Sp R₀}

abbrev fh {f₀ : Z₀ ⟶ X₀} {T₁ T₂ : Pair f₀} (a : T₁ ⟶ T₂) : (op T₂.1.1 : AffOp Z₀) ⟶ op T₁.1.1 :=
  (homOfLE (Pair.le_fst (leOfHom a))).op

abbrev cov {S' : Sys I π t₀} {Z : Scheme.{0}} {t : Z ⟶ Sp R} {k : Z₀ ⟶ Z} (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀)
    (hc : ∀ z : Z, ∃ (T : Pair f₀) (w : Sp (S'.F.obj (op T.1.1))), P'.y (op T.1.1) w = z) : Z.OpenCover where
  I₀ := Pair f₀
  X T := Sp (S'.F.obj (op T.1.1))
  f T := P'.y (op T.1.1)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x ↦ by obtain ⟨T, z, hz⟩ := hc x; exact ⟨T, z, hz⟩, fun T ↦ P'.isOpen _⟩

def dir {S' : Sys I π t₀} {Z : Scheme.{0}} {t : Z ⟶ Sp R} {k : Z₀ ⟶ Z} (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀)
    (hc : ∀ z : Z, ∃ (T : Pair f₀) (w : Sp (S'.F.obj (op T.1.1))), P'.y (op T.1.1) w = z)
    (hd : ∀ (T₁ T₂ : Pair f₀) (a : Sp (S'.F.obj (op T₁.1.1))) (b : Sp (S'.F.obj (op T₂.1.1))),
      P'.y (op T₁.1.1) a = P'.y (op T₂.1.1) b → ∃ (T₃ : Pair f₀) (_ : T₃ ≤ T₁) (_ : T₃ ≤ T₂)
        (c : Sp (S'.F.obj (op T₃.1.1))), P'.y (op T₃.1.1) c = P'.y (op T₁.1.1) a) :
    (cov P' f₀ hc).LocallyDirected where
  trans {T₁ T₂} a := spMap (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1))
  trans_id T := by
    haveI := P'.isOpen (op T.1.1)
    rw [← cancel_mono (P'.y (op T.1.1))]
    exact (P'.nat _).trans (Category.id_comp _).symm
  trans_comp {T₁ T₂ T₃} a b := by
    haveI := P'.isOpen (op T₃.1.1)
    rw [← cancel_mono (P'.y (op T₃.1.1))]
    rw [Category.assoc]
    exact (P'.nat _).trans ((congrArg (_ ≫ ·) (P'.nat _)).trans (P'.nat _)).symm
  w {T₁ T₂} a := P'.nat _
  directed {T₁ T₂} x := by
    haveI := P'.isOpen (op T₁.1.1)
    haveI := P'.isOpen (op T₂.1.1)
    obtain ⟨T₃, h₁, h₂, c, hcT⟩ := hd T₁ T₂ (pullback.fst (P'.y (op T₁.1.1)) (P'.y (op T₂.1.1)) x)
      (pullback.snd (P'.y (op T₁.1.1)) (P'.y (op T₂.1.1)) x)
      (by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply])
    refine ⟨T₃, homOfLE h₁, homOfLE h₂, c, ?_⟩
    apply (pullback.fst (P'.y (op T₁.1.1)) (P'.y (op T₂.1.1)) ≫ P'.y (op T₁.1.1)).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    change (spMap _ ≫ P'.y (op T₁.1.1)) c = _
    rw [P'.nat, hcT, Scheme.Hom.comp_apply]
  property_trans {T₁ T₂} a := by
    haveI := P'.isOpen (op T₂.1.1)
    haveI : IsOpenImmersion (spMap (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1)) ≫
        P'.y (op T₂.1.1)) := by
      rw [P'.nat]; exact P'.isOpen _
    exact IsOpenImmersion.of_comp _ (P'.y (op T₂.1.1))

end GlobalTheory.Obs.GluePair

namespace GlobalTheory.Obs

open Opposite Limits GlobalTheory.LiftSys.Glue GlobalTheory.Obs.GluePair

theorem pairs_glue : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l → (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l → ∃ f : Z ⟶ X, f ≫ s = t ∧ k ≫ f = f₀ ≫ i := by
  intro R R₀ _ _ I hI π hπ hk X₀ Z₀ X Z s₀ t₀ s t i k hi hkk S S' P P' f₀ h l hL hN
  have hsurU : ∀ W, Function.Surjective (spMap (S'.p W)) := fun W ↦
    spMap_surjective _ (S'.surj W) fun b hb ↦ by
      have hb' := (S'.ker W b).1 hb
      have : b * b ∈ (I.map (algebraMap R (S'.F.obj W))) ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul hb' hb'
      rwa [map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hπs : Function.Surjective (spMap π) := spMap_surjective π hπ fun a ha ↦ by
    have ha' : a ∈ I := hk ▸ RingHom.mem_ker.2 ha
    have : a * a ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha' ha'
    rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom π) hπ
  haveI hkc : IsClosedImmersion k := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hkk.flip inferInstance
  have hinj : Function.Injective k := k.isClosedEmbedding.injective
  have hksurj : Function.Surjective k :=
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hkk.flip ⟨hπs⟩).surj

  have hrng : ∀ (W : Z₀.affineOpens) (w : Sp (S'.F.obj (op W))), ∃ z₀ ∈ W.1, P'.y (op W) w = k z₀ := by
    intro W w
    obtain ⟨v, rfl⟩ := hsurU (op W) w
    refine ⟨affPt t₀ W v, W.2.range_fromSpec.le ⟨v, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, P'.red (op W), Scheme.Hom.comp_apply]
  have hcov : ∀ (W : Z₀.affineOpens) (z₀ : Z₀), z₀ ∈ W.1 → ∃ w : Sp (S'.F.obj (op W)), P'.y (op W) w = k z₀ := by
    intro W z₀ hz
    obtain ⟨v, hv⟩ : z₀ ∈ Set.range (affPt t₀ W) := W.2.range_fromSpec.ge hz
    refine ⟨spMap (S'.p (op W)) v, ?_⟩
    change (spMap (S'.p (op W)) ≫ P'.y (op W)) v = k z₀
    rw [P'.red (op W), Scheme.Hom.comp_apply]
    exact congrArg k hv

  have hpair : ∀ (z₀ : Z₀) (U : X₀.affineOpens), f₀ z₀ ∈ U.1 → ∀ V : Z₀.Opens, z₀ ∈ V →
      ∃ T : Pair f₀, z₀ ∈ T.1.1.1 ∧ T.1.2 = U ∧ T.1.1.1 ≤ V := by
    intro z₀ U hU V hV
    obtain ⟨W, hW, hWle⟩ := exists_affine (show z₀ ∈ V ⊓ f₀ ⁻¹ᵁ U.1 from ⟨hV, hU⟩)
    exact ⟨⟨(W, U), hWle.trans inf_le_right⟩, hW, rfl, hWle.trans inf_le_left⟩
  have hpt : ∀ z₀ : Z₀, ∃ T : Pair f₀, z₀ ∈ T.1.1.1 := by
    intro z₀
    obtain ⟨U, hU, -⟩ := exists_affine (show f₀ z₀ ∈ (⊤ : X₀.Opens) from trivial)
    obtain ⟨T, hT, -, -⟩ := hpair z₀ U hU ⊤ trivial
    exact ⟨T, hT⟩
  have hc : ∀ z : Z, ∃ (T : Pair f₀) (w : Sp (S'.F.obj (op T.1.1))), P'.y (op T.1.1) w = z := by
    intro z
    obtain ⟨z₀, rfl⟩ := hksurj z
    obtain ⟨T, hT⟩ := hpt z₀
    obtain ⟨w, hw⟩ := hcov T.1.1 z₀ hT
    exact ⟨T, w, hw⟩
  have hd : ∀ (T₁ T₂ : Pair f₀) (a : Sp (S'.F.obj (op T₁.1.1))) (b : Sp (S'.F.obj (op T₂.1.1))),
      P'.y (op T₁.1.1) a = P'.y (op T₂.1.1) b → ∃ (T₃ : Pair f₀) (_ : T₃ ≤ T₁) (_ : T₃ ≤ T₂)
        (c : Sp (S'.F.obj (op T₃.1.1))), P'.y (op T₃.1.1) c = P'.y (op T₁.1.1) a := by
    intro T₁ T₂ a b hab
    obtain ⟨z₀, h₁, ha⟩ := hrng T₁.1.1 a
    obtain ⟨z₁, h₂, hb⟩ := hrng T₂.1.1 b
    have e : z₀ = z₁ := hinj (ha.symm.trans (hab.trans hb))
    subst e
    have hU₁ : f₀ z₀ ∈ T₁.1.2.1 := T₁.2 h₁
    have hU₂ : f₀ z₀ ∈ T₂.1.2.1 := T₂.2 h₂
    obtain ⟨U₃, hU₃, hU₃le⟩ := exists_affine (show f₀ z₀ ∈ T₁.1.2.1 ⊓ T₂.1.2.1 from ⟨hU₁, hU₂⟩)
    obtain ⟨T₃, hT₃, e₃, hT₃le⟩ := hpair z₀ U₃ hU₃ (T₁.1.1.1 ⊓ T₂.1.1.1) ⟨h₁, h₂⟩
    subst e₃
    obtain ⟨c, hc'⟩ := hcov T₃.1.1 z₀ hT₃
    refine ⟨T₃, ?_, ?_, c, hc'.trans ha.symm⟩
    · exact Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(le_inf_iff.1 hT₃le).1, (le_inf_iff.1 hU₃le).1⟩)
    · exact Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(le_inf_iff.1 hT₃le).2, (le_inf_iff.1 hU₃le).2⟩)
  letI := dir P' f₀ hc hd
  let 𝒰 := cov P' f₀ hc
  let lr : ∀ T : Pair f₀, S.F.obj (op T.1.2) →+* S'.F.obj (op T.1.1) := fun T ↦ (l (op T)).toRingHom
  let g : ∀ T : 𝒰.I₀, 𝒰.X T ⟶ X := fun T ↦ spMap (lr T) ≫ P.y (op T.1.2)
  have hg : ∀ {T₁ T₂ : 𝒰.I₀} (a : T₁ ⟶ T₂), 𝒰.trans a ≫ g T₂ = g T₁ := by
    intro T₁ T₂ a
    change spMap (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1)) ≫
      spMap (lr T₂) ≫ P.y (op T₂.1.2) = _
    rw [← Category.assoc, ← spMap_comp₂]
    have e : (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1)).comp (lr T₂) =
        (lr T₁).comp (mp S.F (homOfLE (Pair.le_snd (leOfHom a))).op : S.F.obj (op T₂.1.2) →+* S.F.obj (op T₁.1.2)) :=
      RingHom.ext fun b ↦ hN a.op b
    rw [e, spMap_comp₂, Category.assoc, P.nat]
  refine ⟨𝒰.glueMorphismsOfLocallyDirected g hg, 𝒰.hom_ext _ _ fun T ↦ ?_, ?_⟩
  · rw [𝒰.map_glueMorphismsOfLocallyDirected_assoc g hg T]
    change (spMap (lr T) ≫ P.y (op T.1.2)) ≫ s = P'.y (op T.1.1) ≫ t
    rw [Category.assoc, P.base, P'.base, ← spMap_comp₂]
    exact congrArg spMap (RingHom.ext fun r ↦ (l (op T)).commutes r)
  · let 𝒱 : Z₀.OpenCover := Scheme.Cover.mkOfCovers (Pair f₀) (fun T ↦ Sp (GlobalTheory.CechDR.Sec t₀ T.1.1.1))
      (fun T ↦ affPt t₀ T.1.1)
      (fun z ↦ by
        obtain ⟨T, hT⟩ := hpt z
        obtain ⟨w, hw⟩ : z ∈ Set.range (affPt t₀ T.1.1) := T.1.1.2.range_fromSpec.ge hT
        exact ⟨T, w, hw⟩)
      (fun T ↦ IsAffineOpen.isOpenImmersion_fromSpec T.1.1.2)
    refine 𝒱.hom_ext _ _ fun T ↦ ?_
    change affPt t₀ T.1.1 ≫ k ≫ _ = affPt t₀ T.1.1 ≫ f₀ ≫ i
    rw [← Category.assoc, show affPt t₀ T.1.1 ≫ k = _ from (P'.red (op T.1.1)).symm, Category.assoc]
    change spMap (S'.p (op T.1.1)) ≫ 𝒰.f T ≫ _ = _
    rw [𝒰.map_glueMorphismsOfLocallyDirected g hg T]
    change spMap (S'.p (op T.1.1)) ≫ spMap (lr T) ≫ P.y (op T.1.2) = _
    rw [← Category.assoc, ← spMap_comp₂]
    have e : (S'.p (op T.1.1)).comp (lr T) = (GlobalTheory.CechDR.secPull s₀ t₀ T).comp (S.p (op T.1.2)) :=
      RingHom.ext fun b ↦ hL (op T) b
    rw [e, spMap_comp₂, Category.assoc, show spMap (S.p (op T.1.2)) ≫ P.y (op T.1.2) = affPt s₀ T.1.2 ≫ i from P.red _,
      ← Category.assoc, GlobalTheory.CechDR.secPull_affPt (φ := f₀) s₀ t₀ T, Category.assoc]

end GlobalTheory.Obs
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Twist

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

def twistHom {B B₀ B' : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B']
    [Algebra R B'] (hI : I ^ 2 = 0) (p : B →+* B₀) (hp : SemiHom π p) (α : B →ₐ[R] B') (θ : Ω[B₀⁄R₀] →+ B')
    (hsm : ∀ b w, θ (p b • w) = α b * θ w) (hmem : ∀ w, θ w ∈ I.map (algebraMap R B')) : B →ₐ[R] B' where
  toFun b := α b + θ (D R₀ B₀ (p b))
  map_one' := by simp
  map_mul' b c := by
    have h := mul_eq_zero_of_mem_map hI (hmem (D R₀ B₀ (p b))) (hmem (D R₀ B₀ (p c)))
    simp only [map_mul, Derivation.leibniz, map_add (f := _), hsm]
    linear_combination -h
  map_zero' := by simp
  map_add' b c := by simp only [map_add (f := _)]; abel
  commutes' r := by
    simp only [SemiHom.map_algebraMap hp, Derivation.map_algebraMap, map_zero, add_zero, AlgHom.commutes]

variable {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) (hI : I ^ 2 = 0)
  (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj V)
  (hsm : ∀ (U V : AffOp X₀) (a : U ⟶ V) b w, θ U V a (S.p U b • w) = mp S.F a b * θ U V a w)
  (hmem : ∀ (U V : AffOp X₀) (a : U ⟶ V) w, θ U V a w ∈ I.map (algebraMap R (S.F.obj V)))
  (hid : ∀ U, θ U U (𝟙 U) = 0)
  (hcomp : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (c : S.F.obj U),
    θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
      mp S.F b (θ U V a (D R₀ _ (S.p U c))) + θ V W b (D R₀ _ (S.p V (mp S.F a c))))

def twistF : AffOp X₀ ⥤ CommAlgCat.{0} R where
  obj := S.F.obj
  map {U V} a := CommAlgCat.ofHom (twistHom hI (S.p U) (S.semi U) (mp S.F a) (θ U V a) (hsm U V a) (hmem U V a))
  map_id U := CommAlgCat.hom_ext (AlgHom.ext fun b ↦ by
    change mp S.F (𝟙 U) b + θ U U (𝟙 U) (D R₀ _ (S.p U b)) = b
    rw [hid, AddMonoidHom.zero_apply, add_zero, mp_id])
  map_comp {U V W} a b := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ by
    change mp S.F (a ≫ b) c + θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
      mp S.F b (mp S.F a c + θ U V a (D R₀ _ (S.p U c))) +
        θ V W b (D R₀ _ (S.p V (mp S.F a c + θ U V a (D R₀ _ (S.p U c)))))
    have h0 : S.p V (θ U V a (D R₀ _ (S.p U c))) = 0 := (S.ker V _).2 (hmem U V a _)
    rw [map_add (S.p V), h0, add_zero, hcomp, mp_comp, map_add (f := _)]
    abel)

def twistSys : Sys I π s₀ where
  F := twistF S hI θ hsm hmem hid hcomp
  p := S.p
  semi := S.semi
  nat {U V} a b := by
    change S.p V (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) = _
    rw [map_add (f := _), (S.ker V _).2 (hmem U V a _), add_zero]
    exact S.nat a b
  surj := S.surj
  ker := S.ker
  smooth := S.smooth

def ev {S' : Sys I π s₀} (v : GlobForm s₀ →+ Z1 S'.F) {U V : AffOp X₀}
    (a : U ⟶ V) : GlobForm s₀ →+ S'.F.obj V where
  toFun w := (v w).1 U V a
  map_zero' := by simp
  map_add' w w' := by simp

end GlobalTheory.LiftSys.Twist

namespace GlobalTheory.LiftSys

open Twist

theorem exists_twist : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S : Sys I π s₀) (v : GlobForm s₀ →+ Z1 S.F), (∀ w, S.IsIdealValuedLiftSystemCocycle (v w)) → (∀ (r : R) w, v (π r • w) = r • v w) → ∃ (S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ ∧ ∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = Φ.φ V ((v w).1 U V a) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar S v hv hs
  have hex : ∀ (U V : AffOp X₀) (a : U ⟶ V), ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj V,
      (∀ b w, θ (S.p U b • w) = mp S.F a b * θ w) ∧ (∀ w, θ w ∈ I.map (algebraMap R (S.F.obj V))) ∧
        ∀ w : GlobForm s₀, θ (w.1 U) = (v w).1 U V a := fun U V a ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U _ _ (S.p U) (S.semi U) (S.surj U) (S.ker U) (mp S.F a)
      (ev v a) (fun r w ↦ by show (v (π r • w)).1 U V a = r • (v w).1 U V a; rw [hs]; rfl) (fun w ↦ hv w U V a)
  choose θ hθ huniq using hex
  have hsm := fun U V a ↦ (hθ U V a).1
  have hmem := fun U V a ↦ (hθ U V a).2.1
  have hglob := fun U V a ↦ (hθ U V a).2.2
  have hid : ∀ U, θ U U (𝟙 U) = 0 := fun U ↦ (huniq U U (𝟙 U) 0
    ⟨fun b w ↦ by simp, fun w ↦ by simp, fun w ↦ by rw [AddMonoidHom.zero_apply, Z1.id]⟩).symm
  have hcomp' : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (x : Ω[Sec s₀ U.unop.1⁄R₀]),
      θ U W (a ≫ b) x = mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x) := by
    intro U V W a b
    let ψ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj W :=
      AddMonoidHom.mk' (fun x ↦ mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x)) (fun x y ↦ by
        simp only [map_add (f := _)]; abel)
    have e : ψ = θ U W (a ≫ b) := by
      refine huniq U W (a ≫ b) ψ ⟨fun c x ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩
      · show mp S.F b (θ U V a (S.p U c • x)) + θ V W b (p1 (OAff s₀) a (S.p U c • x)) =
          mp S.F (a ≫ b) c * (mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x))
        rw [hsm, oneFormsMapOfFunctorMorphism_smul, ← S.nat, hsm, map_mul, mp_comp, mul_add]
      · exact Ideal.add_mem _ (algHom_mem_map I (mp S.F b) (hmem U V a x)) (hmem V W b _)
      · show mp S.F b (θ U V a (w.1 U)) + θ V W b (p1 (OAff s₀) a (w.1 U)) = (v w).1 U W (a ≫ b)
        rw [← w.2 a, hglob, hglob, Z1.comp]
    intro x
    rw [← e]
    rfl
  have hcomp : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (c : S.F.obj U),
      θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
        mp S.F b (θ U V a (D R₀ _ (S.p U c))) + θ V W b (D R₀ _ (S.p V (mp S.F a c))) := by
    intro U V W a b c
    rw [hcomp', p1_D, S.nat]
  let S' := twistSys S hI θ hsm hmem hid hcomp
  let Φ : S.LocIso S' := ⟨fun _ ↦ AlgEquiv.refl, fun _ _ ↦ rfl⟩
  refine ⟨S', Φ, θ, fun U V a ↦ ⟨fun b w ↦ ?_, fun b ↦ ?_, hmem U V a⟩, fun w U V a ↦ hglob U V a w⟩
  · show θ U V a (S.p U b • w) = (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) * θ U V a w
    rw [hsm, add_mul, mul_eq_zero_of_mem_map hI (hmem U V a _) (hmem U V a _), add_zero]
  · show θ U V a (D R₀ _ (S.p U b)) = (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) - mp S.F a b
    rw [add_sub_cancel_left]

end GlobalTheory.LiftSys
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_morphism_liftSystemPresents_of_hom : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (Y : Scheme.{0}) (t : Y ⟶ Sp R) (j : X₀ ⟶ Y), IsPullback i s₀ s (spMap π) → S.Presents t j → S'.Presents s i → (∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b)) → ∃ f : X ⟶ Y, f ≫ t = s ∧ i ≫ f = j := by
  first | exact @GlobalTheory.LiftSys.Glue.presents_hom | exact GlobalTheory.LiftSys.Glue.presents_hom | (intros; apply GlobalTheory.LiftSys.Glue.presents_hom <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsPullback i s₀ s (spMap π) → Smooth s → ∃ S : Sys I π s₀, Nonempty (S.Presents s i) := by
  first | exact @GlobalTheory.LiftSys.exists_sys_presents | exact GlobalTheory.LiftSys.exists_sys_presents | (intros; apply GlobalTheory.LiftSys.exists_sys_presents <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (U V : AffOp X₀), (∃ Q : S.thickObj hI U ⟶ (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop)), ∀ b, Q.φ b = S.p U b) ∧ ∀ (Q : S.thickObj hI U ⟶ (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop))), (∀ b, Q.φ b = S.p U b) → ∀ (α β : S.thickObj hI U ⟶ S'.thickObj hI V) (θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), IsTheta I (S.p U) α.φ β.φ θ → ∀ f : Z1 (O (divided₂ hI) (s₀ ≫ spMap π)), ev f β - ev f α = θ (connForm ((redMor hI hk s₀).coef.pullbackOneCocycle f) (affPt s₀ U.unop) (affPt_w s₀ U.unop) - D R₀ (Sec s₀ U.unop.1) (ev f Q : Sec s₀ U.unop.1)) := by
  first | exact @GlobalTheory.LiftSys.Taylor.ev_sub_ev_eq | exact GlobalTheory.LiftSys.Taylor.ev_sub_ev_eq | (intros; apply GlobalTheory.LiftSys.Taylor.ev_sub_ev_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hodge_cohomology_iso_presented_crystal : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (h : IsPullback i s₀ s (spMap π)), S.Presents s i → ∃ e : HO1 s ≃ₗ[R] GlobalTheory.CatCoh.H1 S.F, (∀ (m : IsMor (dp0 R) s (divided₂ hI) (s₀ ≫ spMap π) (RingHom.id R) i) (c : FirstDeRham s), e (toHO1 s (cmp1 s c)) = S.r hI (m.pull1 c)) ∧ ∀ c : HO1 s, IsPullO h.w c (S.redO.pull1 (e c)) := by
  first | exact @GlobalTheory.LiftSys.cohomology_presents | exact GlobalTheory.LiftSys.cohomology_presents | (intros; apply GlobalTheory.LiftSys.cohomology_presents <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.globalFunctionsAreConstant_abelianScheme_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → Const A.hom := by
  first | exact @GlobalTheory.LiftSys.const_of_isAbelianScheme | exact GlobalTheory.LiftSys.const_of_isAbelianScheme | (intros; apply GlobalTheory.LiftSys.const_of_isAbelianScheme <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.rigidLineBundleIso_descent_along_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [IsCommMonObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left) (φ : A.left ⟶ B.left) (PA : RigLB A) (PB : RigLB B) (L' : LB A'.left), IsAbelianScheme A → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ → IsGrpPullback A B f φ → L'.IsLB → LBIso L' (PA.L.pull φ₁) → LBIso L' (PB.L.pull (φ₁ ≫ φ)) → LBIso PA.L (PB.L.pull φ) := by
  first | exact @GlobalTheory.GaloisLBDescent.lbIso_of_galoisCover | exact GlobalTheory.GaloisLBDescent.lbIso_of_galoisCover | (intros; apply GlobalTheory.GaloisLBDescent.lbIso_of_galoisCover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.descended_polarisation_kernel_killed_same_integer : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (e : ℕ), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ (T : Over X) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over Y) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.DescPolKer.pow_eq_one_of_descent) | (exact GlobalTheory.DescPolKer.pow_eq_one_of_descent) | (intros; apply GlobalTheory.DescPolKer.pow_eq_one_of_descent  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cohomology_subsingleton_of_disjoint_open_cover : ∀ (X : Scheme.{0}) (M : LB X) (κ : Type) (U : κ → X.Opens), M.IsLB → ⨆ c, U c = ⊤ → (Pairwise fun a b => Disjoint (U a) (U b)) → ∀ q : ℕ, (∀ c, Subsingleton (coh (LB.toMod (M.pull (U c).ι)) q)) → Subsingleton (coh (LB.toMod M) q) := by
  first | exact @GlobalTheory.coh_subsingleton_of_disjoint_cover | exact GlobalTheory.coh_subsingleton_of_disjoint_cover | (intros; apply GlobalTheory.coh_subsingleton_of_disjoint_cover <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

namespace GlobalTheory

theorem hdim_twist_pushforward_lbPow_of_isClosedImmersion : ∀ (k : Type) [Field k] (X Z : Scheme.{0}) [Algebra k Γ(X, ⊤)] (g : Z ⟶ X) [IsClosedImmersion g] (L : LB X), L.IsLB → ∀ (G : Z.Modules) (m i : ℕ), letI := algebraΓAlong k g; hdim k (twist ((Scheme.Modules.pushforward g).obj G) (lbPow L m)) i = hdim k (twist G (lbPow (L.pull g) m)) i := by
  intro k _ X Z _ g _ L hL G m i
  letI := algebraΓAlong k g
  have hf : ∀ r : k, g.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Z, ⊤) r := fun _ => rfl
  have hP : hdim k ((Scheme.Modules.pushforward g).obj (twist G ((lbPow L m).pull g))) i =
      hdim k (twist G ((lbPow L m).pull g)) i := by
    rw [hdim_def, hdim_def]
    exact (LinearEquiv.ofBijective _
      (cohPushMap_bijective_of_isClosedImmersion k g hf (twist G ((lbPow L m).pull g)) ⊤ i)).finrank_eq
  obtain ⟨e⟩ := nonempty_iso_of_lbIso (F := G) (isLB_lbPow (pull_isLB hL g) m)
    (pull_isLB (isLB_lbPow hL m) g) (lbIso_lbPow_pull hL g m)
  rw [← hdim_congr k i (projIso (lbPow L m) g G), hP, hdim_congr k i e.symm]

end GlobalTheory
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.TypeTwo

theorem absPow_ofReal_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x y : ℝ), absPow k (x : ℂ) = absPow k (y : ℂ) → x = y := by
  intro k _ _ _ _ x y h
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer k
  have h1 : nabs k ϖ ≠ 1 := fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ.symm.trans ((nabs_eq_one_iff ϖ).1 e))
  have h2 : nabs k ϖ ^ x = nabs k ϖ ^ y := by
    have hx := val_absPow_ofReal k x ϖ
    have hy := val_absPow_ofReal k y ϖ
    rw [h] at hx
    exact_mod_cast hx.symm.trans hy
  have h3 := congrArg Real.log h2
  rw [Real.log_rpow (nabs_pos' k ϖ), Real.log_rpow (nabs_pos' k ϖ)] at h3
  exact mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) h1) h3

end GlobalTheory.TypeTwo
end
