module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle169
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2089
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc



theorem exists_ratModel_normalization : ∀ (A o Ω : Type) [CommRing A] [IsDedekindDomain A] [CommRing o] [Field Ω]
    [Algebra o Ω] [ArithBase o Ω] (κ : A →+* o), κ.Finite → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp A), LocallyOfFiniteType z →
    QuasiCompact z → IsSeparated z → ∀ p : Sp Ω ⟶ Z, p ≫ z = spMap ((algebraMap o Ω).comp κ) →
    (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ (M : RatModel o Ω) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z ∧
    IsFinite π ∧ M.pt ≫ π = p := by
  intro A o Ω _ _ _ _ _ _ κ hκ Z z _ _ _ p hp hfin
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : CharZero (Sp Ω).functionField :=
    charZero_of_injective_ringHom (((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫
      (Sp Ω).germToFunctionField ⊤).hom).injective
  haveI : IsFinite p.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_genericallyFinite (o := CommRingCat.of A) p z hfin
  haveI : GlobalTheory.IsNormalScheme p.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral p
  haveI : IsFinite (spMap κ) := by rw [IsFinite.SpecMap_iff]; exact hκ
  have hl : p ≫ z = spMap (algebraMap o Ω) ≫ spMap κ := by
    rw [hp, ← Spec.map_comp]; rfl
  let l : Sp Ω ⟶ pullback z (spMap κ) := pullback.lift p (spMap (algebraMap o Ω)) hl
  have hl1 : p = l ≫ pullback.fst z (spMap κ) := (pullback.lift_fst _ _ _).symm
  let d := p.normalizationDesc l (pullback.fst z (spMap κ)) hl1
  let s : p.normalization ⟶ Sp o := d ≫ pullback.snd z (spMap κ)
  have hs : s ≫ spMap κ = p.fromNormalization ≫ z := by
    simp only [s, d, Category.assoc, ← pullback.condition]
    rw [Scheme.Hom.normalizationDesc_comp_assoc]
  have hfz : LocallyOfFiniteType (s ≫ spMap κ) ∧ IsSeparated (s ≫ spMap κ) ∧ QuasiCompact (s ≫ spMap κ) := by
    rw [hs]; exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨h1, h2, h3⟩ := hfz
  have hpt_s : p.toNormalization ≫ s = spMap (algebraMap o Ω) := by
    simp only [s, d]
    rw [Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_snd]
  have hgen : Set.range p.toNormalization = {genericPoint p.normalization} := by
    have hr : ∀ w : Sp Ω, w = IsLocalRing.closedPoint Ω := fun w => Subsingleton.elim _ _
    have hrng : Set.range p.toNormalization = {p.toNormalization (IsLocalRing.closedPoint Ω)} :=
      Set.ext fun y => ⟨fun ⟨w, hw⟩ => hw ▸ congrArg p.toNormalization (hr w),
        fun hy => ⟨_, hy.symm⟩⟩
    have : IsGenericPoint (p.toNormalization (IsLocalRing.closedPoint Ω)) (⊤ : Set p.normalization) := by
      rw [isGenericPoint_def, ← hrng]
      exact p.toNormalization.denseRange.closure_range
    rw [hrng, this.eq (genericPoint_spec p.normalization)]
  have honto : ∀ x : Ω, ∃ (U : p.normalization.Opens) (f : Γ(p.normalization, U)), (U : Set p.normalization).Nonempty ∧
      valF p.toNormalization U f = x := by
    intro x
    set ξ : Sp Ω := genericPoint (Sp Ω) with hξ
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (x := p ξ) (U := ⊤) trivial
    have hsub : ∀ w : Sp Ω, w = ξ := fun w => Subsingleton.elim _ _
    have hpV : ⊤ ≤ p ⁻¹ᵁ V := fun w _ => by rw [hsub w]; exact hxV
    have hξB : ξ ∈ p ⁻¹ᵁ V := hxV
    letI := (p.app V).hom.toAlgebra

    let gB := (Sp Ω).presheaf.germ (p ⁻¹ᵁ V) ξ hξB
    let gR := Z.presheaf.germ V (p ξ) hxV
    have hsq : gR ≫ p.stalkMap ξ = p.app V ≫ gB := p.germ_stalkMap V ξ hxV
    letI alO : Algebra Γ(Z, V) (Z.presheaf.stalk (p ξ)) :=
      TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨p ξ, hxV⟩
    letI alS : Algebra (Z.presheaf.stalk (p ξ)) ((Sp Ω).presheaf.stalk ξ) := (p.stalkMap ξ).hom.toAlgebra
    letI alRS : Algebra Γ(Z, V) ((Sp Ω).presheaf.stalk ξ) := (gR ≫ p.stalkMap ξ).hom.toAlgebra
    haveI : IsScalarTower Γ(Z, V) (Z.presheaf.stalk (p ξ)) ((Sp Ω).presheaf.stalk ξ) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI hloc : IsLocalization.AtPrime (Z.presheaf.stalk (p ξ)) (hV.primeIdealOf ⟨p ξ, hxV⟩).asIdeal :=
      hV.isLocalization_stalk ⟨p ξ, hxV⟩

    have h1 : ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ (p ⁻¹ᵁ V) := hpV
    let E : Γ(Sp Ω, p ⁻¹ᵁ V) →+* Ω := (GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1).hom
    have hE : ∀ b, E b = valR (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) b := fun b => (GlobalTheory.Points.valR_eq _ _ h1 b).symm
    have hEinj : Function.Injective E := by
      have e1 : GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1 =
          (Sp Ω).presheaf.map (homOfLE h1).op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
        rw [GlobalTheory.Points.valMap, Scheme.Hom.appLE]
        simp
        rfl
      haveI : Nonempty (⊤ : (Sp Ω).Opens) := ⟨⟨ξ, trivial⟩⟩
      show Function.Injective (GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1).hom
      rw [e1]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).1.comp
        (map_injective_of_isIntegral (Sp Ω) (homOfLE h1))
    obtain ⟨y', hy'⟩ : ∃ y' : Γ(Sp Ω, p ⁻¹ᵁ V), E y' = x := by
      refine ⟨((Sp Ω).presheaf.map (homOfLE le_top).op).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom x), ?_⟩
      rw [hE, GlobalTheory.Points.valR_res (𝟙 (Sp Ω)) le_top h1]
      have := GlobalTheory.Points.valR_specMap (𝟙 (CommRingCat.of Ω)) x
      rw [Spec.map_id] at this
      exact this

    let y := gB.hom y'
    have hy : IsIntegral (Z.presheaf.stalk (p ξ)) y := hfin.to_isIntegral y
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (hV.primeIdealOf ⟨p ξ, hxV⟩).asIdeal.primeCompl y hy
    have hcomm : ∀ r : Γ(Z, V), gB.hom (algebraMap Γ(Z, V) Γ(Sp Ω, p ⁻¹ᵁ V) r) =
        algebraMap Γ(Z, V) ((Sp Ω).presheaf.stalk ξ) r := fun r => by
      show gB.hom ((p.app V).hom r) = (gR ≫ p.stalkMap ξ).hom r
      rw [hsq]; rfl
    let gB' : Γ(Sp Ω, p ⁻¹ᵁ V) →ₐ[Γ(Z, V)] (Sp Ω).presheaf.stalk ξ := { gB.hom with commutes' := hcomm }
    have hgB : Function.Injective gB' := germ_injective_of_isIntegral (Sp Ω) ξ hξB
    let c' : Γ(Sp Ω, p ⁻¹ᵁ V) := algebraMap Γ(Z, V) _ (m : Γ(Z, V))
    let d' : Γ(Sp Ω, p ⁻¹ᵁ V) := c' * y'
    have hc : IsIntegral Γ(Z, V) c' := isIntegral_algebraMap
    have hd : IsIntegral Γ(Z, V) d' := by
      rw [← isIntegral_algHom_iff gB' hgB]
      have : gB' d' = (m : Γ(Z, V)) • y := by
        rw [Algebra.smul_def, map_mul]
        exact congrArg (· * y) (hcomm _)
      rw [this]
      exact hm
    have hc0 : c' ≠ 0 := by
      intro h0
      have h2 : IsUnit (gB.hom c') := by
        rw [hcomm]
        exact ((IsLocalization.map_units (Z.presheaf.stalk (p ξ)) m).map (p.stalkMap ξ).hom)
      rw [h0, map_zero] at h2
      exact not_isUnit_zero h2
    have hEc : E c' ≠ 0 := fun h0 => hc0 (hEinj (h0.trans (map_zero E).symm))

    let iso := p.normalizationObjIso hV
    have key := p.normalizationObjIso_hom_val hV
    let ac : Γ(p.normalization, p.fromNormalization ⁻¹ᵁ V) := iso.inv.hom ⟨c', hc⟩
    let ad : Γ(p.normalization, p.fromNormalization ⁻¹ᵁ V) := iso.inv.hom ⟨d', hd⟩
    have hle : p ⁻¹ᵁ V ≤ p.toNormalization ⁻¹ᵁ (p.fromNormalization ⁻¹ᵁ V) := by
      simp [← Scheme.Hom.comp_preimage]
    have hval : ∀ e : integralClosure Γ(Z, V) Γ(Sp Ω, p ⁻¹ᵁ V),
        valR p.toNormalization (p.fromNormalization ⁻¹ᵁ V) (iso.inv.hom e) = E e.1 := by
      intro e
      have h3 := congrArg (fun φ => φ.hom (iso.inv.hom e)) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] at h3
      rw [hE, ← Category.id_comp p.toNormalization, ← GlobalTheory.Points.valR_appLE (𝟙 (Sp Ω)) p.toNormalization hle h1]
      congr 1
      exact h3.symm
    have hW : ⊤ ≤ p.toNormalization ⁻¹ᵁ (p.fromNormalization ⁻¹ᵁ V) := h1.trans hle
    have hU : ⊤ ≤ p.toNormalization ⁻¹ᵁ p.normalization.basicOpen ac := by
      rw [GlobalTheory.Points.le_preimage_basicOpen_iff _ hW ac]
      exact (show valR p.toNormalization _ ac ≠ 0 from (hval _).trans_ne hEc).isUnit
    have hu : IsUnit ((p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ac) :=
      p.normalization.toRingedSpace.isUnit_res_basicOpen ac
    refine ⟨p.normalization.basicOpen ac,
      (p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ad * ↑(hu.unit⁻¹),
      ⟨_, hU (x := ξ) trivial⟩, ?_⟩
    rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valR_mul _ _ hU, GlobalTheory.Points.valR_res _ _ hU, hval]
    have h4 : valR p.toNormalization _ ((p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ac) *
        valR p.toNormalization (p.normalization.basicOpen ac) ↑(hu.unit⁻¹) = 1 := by
      rw [← GlobalTheory.Points.valR_mul _ _ hU, ← GlobalTheory.Points.valR_one p.toNormalization _ hU]
      congr 1
      exact hu.mul_val_inv
    rw [GlobalTheory.Points.valR_res _ _ hU, hval] at h4
    rw [eq_inv_of_mul_eq_one_right h4]
    show E (c' * y') * (E c')⁻¹ = x
    rw [map_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hEc, one_mul, hy']
  haveI := IsSeparated.of_comp s (spMap κ)
  haveI := locallyOfFiniteType_of_comp s (spMap κ)
  haveI := QuasiCompact.of_comp s (spMap κ)
  let M : RatModel o Ω :=
    { Z := p.normalization
      s := s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := p.toNormalization
      pt_s := hpt_s
      gen := hgen
      onto := honto }
  exact ⟨M, p.fromNormalization, GlobalTheory.IsNormalScheme.pred _, inferInstance, p.toNormalization_fromNormalization⟩

end GlobalTheory.Poinc
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem prime_eq_of_natCast_eq_zero {K : Type*} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : (p : K) = 0) (h2 : (q : K) = 0) : p = q := by
  have a := ringChar.dvd h1
  have b := ringChar.dvd h2
  have hne : ringChar K ≠ 1 := CharP.ringChar_ne_one
  have e1 := (hp.eq_one_or_self_of_dvd _ a).resolve_left hne
  have e2 := (hq.eq_one_or_self_of_dvd _ b).resolve_left hne
  rw [← e1, ← e2]

theorem natCast_residueField_cPt {X : Scheme.{0}} {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ X) :
    ((p : ℕ) : X.residueField (y (cPt p))) = 0 := by
  let φ := (Scheme.stalkClosedPointTo (R := CommRingCat.of (OO p)) y).hom
  have hinj := (IsLocalRing.ResidueField.map φ).injective
  refine hinj ((map_natCast _ p).trans ?_)
  exact (natCast_residueField_OO (p := p)).trans (map_zero _).symm

theorem eq_zero_of_val_cen_eq_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (p : ℕ) [Fact p.Prime] (y₀ : Sp (OO p) ⟶ M.Z) (b : Ω), b ∈ M.O (y₀ (cPt p)) → (∀ y : Sp (OO p) ⟶ M.Z, M.Cen U (y₀ (cPt p)) y → M.val (gPt p ≫ y) b = 0) → b = 0 := by
  intro o Ω _ _ _ hb M hN U hU p _ y₀ b hb0 hv
  by_contra hne
  obtain ⟨V, f, hzV, hf⟩ := hb0
  have hD : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have h0 : f = 0 := (basicOpen_eq_bot_iff f).1 (SetLike.coe_injective h)
    apply hne
    rw [← hf, ← M.res_apply V ⟨_, hzV⟩, h0, map_zero]
  have hW : ((U ⊓ M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := M.nonempty_inf hU hD
  have := hb.ded
  have := hb.ft
  have := hb.char
  have : CharZero o := (RingHom.charZero_iff hb.inj).2 hb.char
  let π : M.Z ⟶ Spec (.of ℤ) := M.s ≫ Spec.map (CommRingCat.ofHom (Int.castRingHom o))
  have : Flat M.s := GlobalTheory.ModelOfOutput.flat_ratModel M
  have : Flat (Spec.map (CommRingCat.ofHom (Int.castRingHom o))) := by
    refine Flat.SpecMap_iff.2 ?_
    have : FaithfulSMul ℤ o := inferInstance
    exact (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Flat π := inferInstance
  have := M.lft
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Int.castRingHom o))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact (RingHom.finiteType_algebraMap (A := ℤ) (B := o)).2 hb.ft
  have : LocallyOfFiniteType π := inferInstance
  have hz : IsClosed ({y₀ (cPt p)} : Set M.Z) := isClosed_singleton_cPt y₀
  obtain ⟨p', hp', y, hy, hyW⟩ := GlobalTheory.padicAlgCl_integral_points.1 M.Z π (y₀ (cPt p)) hz _ hW
  have e : p = p' := prime_eq_of_natCast_eq_zero (Fact.out) hp'.out (natCast_residueField_cPt y₀)
    (hy ▸ natCast_residueField_cPt y)
  subst e
  have h0 := hv y ⟨hy, hyW.trans (fun _ h => h.1)⟩
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hξ : (gPt p ≫ y) w ∈ M.Z.basicOpen f := (hyW ⟨w, rfl⟩).2
  have hξV : (gPt p ≫ y) w ∈ V := M.Z.basicOpen_le f hξ
  subst hf
  exact (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ w) ⟨_, RatModel.valF_mem_O hξV f⟩).2
    ((RatModel.isUnit_valF_iff hξV f).2 hξ) h0

end GlobalTheory.Poinc

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EndoPt

theorem exists_mulEquiv_points {S S' : Scheme.{0}} {g : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G g φ) (T : Over S') :
    ∃ E : (T ⟶ G') ≃* (Over.mk (T.hom ≫ g) ⟶ G), ∀ x, (E x).left = x.left ≫ φ := by
  let F : (T ⟶ G') → (Over.mk (T.hom ≫ g) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ g
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  have hF : ∀ x, (F x).left = x.left ≫ φ := fun x => rfl
  have inj : Function.Injective F := fun x y e => by
    apply Over.OverMorphism.ext
    refine h.1.hom_ext ?_ ?_
    · rw [← hF, ← hF, e]
    · rw [Over.w x, Over.w y]
  have sur : Function.Surjective F := fun z => by
    have w : z.left ≫ G.hom = T.hom ≫ g := Over.w z
    refine ⟨Over.homMk (h.1.lift z.left T.hom w) (h.1.lift_snd _ _ w), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ w
  refine ⟨{ Equiv.ofBijective F ⟨inj, sur⟩ with map_mul' := fun x y => ?_ }, hF⟩
  apply Over.OverMorphism.ext
  exact (h.2 T x y (F x) (F y) rfl rfl).symm

theorem exists_point_of_isMonHom {S S' : Scheme.{0}} {g : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G g φ) (f : G ⟶ G) [IsMonHom f] (m : ℕ) {T : Over S'}
    (x : T ⟶ G') (hx : x ^ m = 1) :
    ∃ x₂ : T ⟶ G', x₂.left ≫ φ = x.left ≫ φ ≫ f.left ∧ x₂ ^ m = 1 := by
  obtain ⟨E, hE⟩ := exists_mulEquiv_points h T
  refine ⟨E.symm (E x ≫ f), ?_, ?_⟩
  · rw [← hE, MulEquiv.apply_symm_apply, Over.comp_left, hE, Category.assoc]
  · rw [← map_pow, ← MonObj.pow_comp, ← map_pow, hx, map_one, MonObj.one_comp, map_one]

theorem exists_endo_point : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (f : ρ.P.A ⟶ ρ.P.A), IsMonHom f → ∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x ^ m = 1 → ∃ x₂ : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x₂.left ≫ u.φ = x.left ≫ u.φ ≫ f.left ∧ x₂ ^ m = 1 := by
  intro o Ω _ _ _ S ρ p _ y₀ u f hf m x hx
  exact exists_point_of_isMonHom u.cart f m x hx

end GlobalTheory.EndoPt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_qkPt_of_utest : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : S.Gam), ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left := by
  intro o Ω _ _ _ S ρ p _ y₀ u a
  haveI : CharZero u.V := ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V _)).charZero
  obtain ⟨x, hx, hadd, -⟩ := utest_torsion_points o Ω S ρ p y₀ u
  obtain ⟨f, f₁, f₂, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) _ (GlobalTheory.RealCompare.one_le_rN S)
  have hx1 : x a ^ (S.r * S.N) = 1 := by
    have := u.A.isAb.comm
    obtain ⟨h0, hsm⟩ := ThetaReal.pt_nsmul x hadd
    rw [← hsm, ThetaReal.nsmul_self, h0]
  obtain ⟨q, hq⟩ := f₂ _ hx1
  exact ⟨q, x a, (f₁ _ _).2 hq.symm, hx a⟩

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LabelTorsion

theorem pt_nsmul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (b : S.Gam)
    (n : ℕ) : ρ.pt (n • b) = ρ.pt b ^ n := by
  have h0 : ρ.pt 0 = 1 := by
    have h := ρ.pt_add 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]

theorem pt_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (b : S.Gam) :
    ρ.pt b ^ (S.r * S.N) = 1 := by
  have h : (S.r * S.N) • b = 0 • b := by
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, zero_smul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [← pt_nsmul, h, pt_nsmul, pow_zero]

theorem pow_eq_one_of_over_label : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (b : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left → x ^ (S.r * S.N) = 1 := by
  intro o Ω _ _ _ S ρ p _ y₀ u b x hx
  exact GlobalTheory.FrameMove.pow_eq_one_of (T := baseOver (Sp S.R)) (x := ρ.pt b) u.cart hx (pt_pow_eq_one ρ b)

end GlobalTheory.LabelTorsion
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QLevelRescale
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem exists_qkPt_rescale : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k k' d : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ k → 1 ≤ d → k' = d * k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → ∃ pk' : QkPt u.D.toPre (PadicAlgCl p) k', pk'.y = d • pk.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) k' pk' x := by
  intro o Ω _ _ _ S ρ p _ y₀ u k k' d pk x hk hd hk' hx
  have hA : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  have e : k' • pk.g = iota hB (PadicAlgCl p) (d • pk.y) := by
    rw [hk', ← smul_smul, qk_nsmul hB, map_nsmul]
  refine ⟨qkMk hB (d • pk.y) pk.g e, rfl, ?_⟩
  have L := GlobalTheory.PeriodsAnyChar.qkToAkU_level GlobalTheory.firstFiveLaws u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p)
    k d k' hk hd (by rw [hk', Nat.mul_comm]) pk (qkMk hB (d • pk.y) pk.g e) x
  exact (L.1 rfl rfl).1 hx

end GlobalTheory.QLevelRescale
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

noncomputable section
namespace GlobalTheory.Poinc

theorem exists_eq_div_of_mem_O_affine : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z ∈ U, ∀ x ∈ M.O z, ∃ a ∈ M.ringOn (U : Set M.Z), ∃ b ∈ M.ringOn (U : Set M.Z), b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x = a / b := by
  intro o Ω _ _ _ M U hU z hz x hx
  obtain ⟨W, f, hzW, rfl⟩ := hx
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  obtain ⟨g, hgW, hzg⟩ := hU.exists_basicOpen_le (V := W) ⟨z, hzW⟩ hz
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzg⟩
  have := hU.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgW f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, U), M.res _ hg (algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen g) t) = M.res U hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, res_resG, res_apply, ← map_pow, res_apply, res_apply] at h1
  have hu := (isUnit_O_iff _).1 ((isUnit_valF_iff hz g).2 hzg)
  have hb : valF M.pt U (g ^ n) = valF M.pt U g ^ n := by
    rw [← M.res_apply U hne, map_pow, res_apply]
  have h0 : valF M.pt U (g ^ n) ≠ 0 := by
    rw [hb]
    exact pow_ne_zero _ hu.1
  refine ⟨_, (mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _, (mem_ringOn_iff_exists hne).2 ⟨g ^ n, rfl⟩, h0, ?_,
    (eq_div_iff h0).2 h1⟩
  rw [hb, ← inv_pow]
  exact pow_mem hu.2 n

end GlobalTheory.Poinc
end
end
