module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2903
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle030
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory GlobalTheory.USep GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.UCovSep.GenModel

theorem exists_genModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x₀ : Xo.XF c) (n : ℕ), n.Prime → Odd n → ∃ g₀ : ℕ, ∀ e : ℕ, ∃ (o₁ Ω : Type) (_ : CommRing o₁) (_ : Field Ω) (_ : Algebra o₁ Ω) (_ : ArithBase o₁ Ω) (ze : o₁ˣ) (uη : Sp Ω ⟶ Xo.XF c) (A₁ : PolAV (Sp Ω)) (_ : Out.Level A₁ (n ^ e) (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze))) (M : RatModel o₁ Ω) (U : C.Z.Opens) (g : M.Z ⟶ U.toScheme), A₁.g = g₀ ∧ IsUnit (n : o₁) ∧ (∀ w, uη w = x₀) ∧ UOver Xo c A₁ (RingHom.id Ω) uη ∧ M.pt ≫ g ≫ U.ι = uη ≫ C.i ∧ GlobalTheory.IsNormalScheme M.Z ∧ IsProjOver M.s ∧ IsFinite g ∧ Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z) := by
  intro E _ _ _ H Dw _ l Xo c C x₀ n hn ho
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
  obtain ⟨A, _, φ, j, P, _, hφ, hjs, hjo, hjx⟩ :=
    GlobalTheory.UPoinc.GSetup.exists_chart (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x₀
  let ev : A →+* P.ResidueField := algebraMap A P.ResidueField
  let y : Sp P.ResidueField ⟶ Xo.XF c := spMap ev ≫ j
  have hy : ∀ w, y w = x₀ := fun w => by
    have hp : spMap ev w = ⟨P, inferInstance⟩ := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ev w.asIdeal = P
      rw [Subsingleton.elim w (⊥ : PrimeSpectrum P.ResidueField)]
      exact Ideal.ker_algebraMap_residueField _
    show j (spMap ev w) = x₀
    rw [hp, hjx]
  haveI : CharZero P.ResidueField := (ev.comp φ).charZero_iff (ev.comp φ).injective |>.1 inferInstance
  obtain ⟨A₀, -, hU₀⟩ := GlobalTheory.UPoinc.GSetup.exists_fibre Xo c y
  refine ⟨A₀.g, fun e => ?_⟩
  have hpos : 1 ≤ n ^ e := Nat.one_le_iff_ne_zero.2 (by have := hn.pos; positivity)
  obtain ⟨Ω, _, f, A₁, ψ, ze, hf, hA₁, hze, ⟨lev⟩⟩ := GlobalTheory.UPoinc.GSetup.exists_level_finite P.ResidueField A₀ _ hpos
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  have hU₁ : UOver Xo c A₁ (RingHom.id Ω) (spMap f ≫ y) := by
    refine (uOver_baseChange_iff hA₁.2.1 (LBIso.symm hA₁.2.2) (RingHom.id Ω)).2 ?_
    rw [RingHom.id_comp]
    simpa only [RingHom.comp_id] using hU₀.comp f
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  have hnF : C.b (n : C.o) ≠ 0 := by rw [map_natCast]; exact Nat.cast_ne_zero.2 hn.ne_zero
  have hno : (n : C.o) ≠ 0 := fun h => hnF (by rw [h, map_zero])
  have hle : Submonoid.powers (n : C.o) ≤ nonZeroDivisors C.o := powers_le_nonZeroDivisors_of_noZeroDivisors hno
  let o' := Localization.Away (n : C.o)
  haveI : IsDomain o' := IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain o' := IsLocalization.isDedekindDomain C.o hle o'
  let b' : o' →+* c.F := IsLocalization.Away.lift (n : C.o) (IsUnit.mk0 _ hnF)
  have hb' : b'.comp (algebraMap C.o o') = C.b := IsLocalization.Away.lift_comp _ _
  letI : Algebra o' c.F := b'.toAlgebra
  haveI : IsScalarTower C.o o' c.F := IsScalarTower.of_algebraMap_eq' hb'.symm
  haveI : IsFractionRing o' c.F := IsFractionRing.isFractionRing_of_isLocalization _ o' c.F hle
  let β : c.F →+* Ω := f.comp (ev.comp φ)
  obtain ⟨o₁, _, _, κ, ze₁, hded, hκ, hinj, hcomp, hze₁⟩ :=
    GlobalTheory.UPoinc.GSetup.exists_base_root o' c.F Ω β ze _ hpos hze
  have hft : Algebra.FiniteType ℤ o₁ := by
    have h₁ : (algebraMap ℤ C.o).FiniteType := RingHom.finiteType_algebraMap.2 C.ft
    have h₂ : (algebraMap C.o o').FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
    have h₃ := hκ.finiteType.comp (h₂.comp h₁)
    rw [RingHom.ext_int (κ.comp _) (algebraMap ℤ o₁)] at h₃
    exact RingHom.finiteType_algebraMap.1 h₃
  haveI : ArithBase o₁ Ω := ⟨hded, hft, inferInstance, hinj⟩
  have hun : IsUnit (n : o₁) := by
    simpa using (IsLocalization.Away.algebraMap_isUnit (S := o') (n : C.o)).map κ
  rw [← hze₁] at lev
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  haveI := C.iF_open
  haveI : SurjectiveOnStalks (spMap ev) :=
    (SurjectiveOnStalks.Spec_iff (φ := CommRingCat.ofHom ev)).2 (Ideal.surjectiveOnStalks_residueField P)
  let a : Sp o' ⟶ Sp C.o := spMap (algebraMap C.o o')
  haveI : IsOpenImmersion a := IsOpenImmersion.of_isLocalization (n : C.o)
  have hba : spMap b' ≫ a = spMap C.b := by rw [← hb']; exact (Spec.map_comp _ _).symm
  let inc : pullback C.z a ⟶ C.Z := pullback.fst _ _
  let gf : pullback C.z (spMap C.b) ⟶ pullback C.z a := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap b')
    (by rw [Category.assoc, hba, pullback.condition])
  have hgf : gf ≫ inc = pullback.fst _ _ := pullback.lift_fst _ _ _
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  haveI : IsPreimmersion (gf ≫ inc) := hgf ▸ inferInstance
  haveI : IsPreimmersion gf := IsPreimmersion.of_comp gf inc
  have hpz : (spMap f ≫ spMap ev ≫ j ≫ C.iF ≫ gf) ≫ pullback.snd _ _ = spMap ((algebraMap o₁ Ω).comp κ) := by
    simp only [Category.assoc, gf, pullback.lift_snd]
    rw [← Category.assoc C.iF, C.iF_over, ← Category.assoc j, hjs, hcomp]
    simp only [← Spec.map_comp]
    rfl
  have hst : ((spMap f ≫ spMap ev ≫ j ≫ C.iF ≫ gf).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (GlobalTheory.UPoinc.GSetup.finite_stalkMap_field f hf _)
      (RingHom.Finite.of_surjective _ (Scheme.Hom.stalkMap_surjective _ _))
  obtain ⟨M, π, hMn, hπ, hMp⟩ := GlobalTheory.Poinc.exists_ratModel_normalization o' o₁ Ω κ hκ _ (pullback.snd C.z a) inferInstance
    inferInstance inferInstance _ hpz hst
  have hMs : M.s ≫ spMap κ = π ≫ pullback.snd C.z a := by
    refine ext_of_isDominant_of_isSeparated (spMap (algebraMap ℤ o')) (specZIsTerminal.hom_ext _ _) M.pt ?_
    rw [← Category.assoc, M.pt_s, ← Category.assoc, hMp, hpz, ← Spec.map_comp]
    rfl
  have hproj : IsProjOver M.s :=
    GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over o' o₁ κ M.Z (pullback C.z a) (pullback.snd C.z a) π M.s
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap C.o o') C.proj) hπ inferInstance hMs
  refine ⟨o₁, Ω, inferInstance, inferInstance, inferInstance, inferInstance, ze₁, spMap f ≫ y, A₁, lev, M,
    inc.opensRange, π ≫ inc.isoOpensRange.hom, hA₁.1, hun, fun w => hy _, hU₁, ?_,
    GlobalTheory.IsNormalScheme.of_pred hMn, hproj, inferInstance, ?_⟩
  · rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← Category.assoc, hMp]
    simp only [y, Category.assoc, hgf]
  · rintro _ ⟨x, rfl⟩
    exact ⟨gf x, by rw [← Scheme.Hom.comp_apply, hgf]⟩

end GlobalTheory.UCovSep.GenModel
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep.Setup

def RootsIn {V V₁ : Type} [CommRing V] [CommRing V₁] (ρ : V →+* V₁) (F : Polynomial V) : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (ψ : V₁ →+* D) (d : D), F.eval₂ (ψ.comp ρ) d = 0 → d ∈ ψ.range

theorem rootsIn_of_splits {V V₁ : Type} [CommRing V] [CommRing V₁] (ρ : V →+* V₁) {F : Polynomial V} (hF : F.Monic)
    (h : (F.map ρ).Splits) : RootsIn ρ F := by
  intro D _ _ ψ d hd
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.1 h
  rw [← Polynomial.eval₂_map, hm, (hF.map ρ).leadingCoeff, map_one, _root_.one_mul, Polynomial.eval₂_multiset_prod,
    Multiset.map_map, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hd
  obtain ⟨a, -, ha⟩ := hd
  exact ⟨a, (sub_eq_zero.1 (by simpa using ha)).symm⟩

theorem exists_ext (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.Mum.Base V) (L : Type) [Field L]
    [Algebra (FractionRing V) L] [FiniteDimensional (FractionRing V) L] (F : Polynomial V) (hF : F.Monic) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (σ : L →+* FractionRing V₁),
      GlobalTheory.Mum.Base V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧
      (σ.comp (algebraMap (FractionRing V) L)).comp (algebraMap V _) = (algebraMap V₁ _).comp ρ ∧ RootsIn ρ F := by
  haveI := hV.2
  let K := FractionRing V
  let F₁ : Polynomial L := F.map ((algebraMap K L).comp (algebraMap V K))
  let L₂ := F₁.SplittingField
  haveI : FiniteDimensional K L₂ := Module.Finite.trans L L₂
  obtain ⟨E, _, _, _, _, j, ζ, hζ⟩ := MumLevel.exists_galois_root K L₂ 1 le_rfl
  obtain ⟨V₁, _, _, _, ρ, e, -, hρ, he, -, -⟩ := MumLevel.exists_ring V hV E ζ 1 le_rfl hζ
  let τ : L₂ →+* FractionRing V₁ := e.toRingHom.comp j.toRingHom
  have hσ : ((τ.comp (algebraMap L L₂)).comp (algebraMap K L)).comp (algebraMap V K) = (algebraMap V₁ _).comp ρ :=
    RingHom.ext fun r => (congrArg e ((congrArg j (IsScalarTower.algebraMap_apply K L L₂ _).symm).trans
      (j.commutes _))).trans (he r)
  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  haveI := hρ.1.2.2.1
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, ρ, τ.comp (algebraMap L L₂),
    ⟨hρ.1, (ρ.charZero_iff hρ.2.1).1 inferInstance⟩, hρ.2.1, hρ.2.2, hσ, rootsIn_of_splits ρ hF ?_⟩
  refine Polynomial.Splits.of_splits_map_of_injective hinj ?_ fun a ha => ?_
  · have := (Polynomial.SplittingField.splits F₁).map τ
    rw [Polynomial.map_map, Polynomial.map_map, ← RingHom.comp_assoc, hσ] at this
    rwa [Polynomial.map_map]
  · exact IsIntegrallyClosed.isIntegral_iff.1 ⟨F.map ρ, hF.map ρ, by
      rw [← Polynomial.eval_map]; exact (Polynomial.mem_roots'.1 ha).2⟩

theorem RootsIn.exists_sq {V V₁ : Type} [CommRing V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {F : Polynomial V}
    (h : RootsIn ρ F) {s : V} (hs : Polynomial.X ^ 2 - Polynomial.C s ∣ F) : ∃ r : V₁, r ^ 2 = ρ s := by
  let D := AlgebraicClosure (FractionRing V₁)
  let ψ : V₁ →+* D := (algebraMap (FractionRing V₁) D).comp (algebraMap V₁ _)
  have hψ : Function.Injective ψ := (algebraMap (FractionRing V₁) D).injective.comp (IsFractionRing.injective V₁ _)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (ψ (ρ s)) two_pos
  obtain ⟨G, rfl⟩ := hs
  obtain ⟨r, rfl⟩ := h D ψ d (by simp [Polynomial.eval₂_mul, Polynomial.eval₂_sub, hd])
  exact ⟨r, hψ (by rw [map_pow, hd])⟩


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


theorem exists_lift_genericFibre (C : UCompact Xo c) {O W : Type} [CommRing O] [CommRing W] (ev : O →+* W) [IsLocalHom ev]
    (t : Sp O ⟶ C.Z) (ξ : Sp W ⟶ pullback C.z (spMap C.b)) (h : spMap ev ≫ t = ξ ≫ pullback.fst _ _) :
    ∃ ζ : Sp O ⟶ pullback C.z (spMap C.b), ζ ≫ pullback.fst _ _ = t := by
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ C.z)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (ξ ≫ pullback.snd _ _)
  have e : φ ≫ CommRingCat.ofHom ev = CommRingCat.ofHom C.b ≫ β := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hφ, hβ, ← Category.assoc, h, Category.assoc, Category.assoc, pullback.condition])
  have hu : ∀ a : nonZeroDivisors C.o, IsUnit (φ.hom a) := fun a => by
    refine (isUnit_map_iff ev _).1 ?_
    rw [show ev (φ.hom a) = β.hom (C.b a) from congrArg (fun χ => χ.hom a.1) e]
    exact (IsLocalization.map_units c.F a).map β.hom
  refine ⟨pullback.lift t (spMap (IsLocalization.lift (S := c.F) hu)) ?_, pullback.lift_fst _ _ _⟩
  rw [← hφ, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (IsLocalization.lift_comp (S := c.F) hu).symm)

theorem fromSpecStalk_bot {X : Scheme.{0}} [IsIntegral X] (z : X) (p : Sp (X.presheaf.stalk z)) (hp : p.asIdeal = ⊥) :
    X.fromSpecStalk z p = genericPoint X := by
  obtain ⟨q, hq⟩ : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes z
  have h : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (show p.asIdeal ≤ q.asIdeal from hp ▸ bot_le)
  exact ((hq ▸ h.map (X.fromSpecStalk z).continuous).antisymm (genericPoint_specializes _)).eq

end GlobalTheory.USep.Setup
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem ringOp_map_of_intertwine {A B : Type} [CommRing A] [CommRing B] (iK : A →+* B) {n : ℕ} (d : A → A) (dd : Fin n → A → A)
    (d' : B → B) (dd' : Fin n → B → B) (hd : ∀ w, d' (iK w) = iK (d w)) (hdd : ∀ a w, dd' a (iK w) = iK (dd a w))
    (Θ : Matrix (Fin n) (Fin n) A) (u : Fin n → A) (p p' : A) (k : ℕ) (f : A) :
    iK (ringOp d dd Θ u p p' k f) = ringOp d' dd' (iK.mapMatrix Θ) (fun a => iK (u a)) (iK p) (iK p') k (iK f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ringOp, map_sub, map_add (f := _), map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd,
    RingHom.mapMatrix_apply, Matrix.map_apply]

theorem ringOp_mul_of_const {K : Type} [CommRing K] {n : ℕ} (d : K → K) (δ : Fin n → K → K)
    (Θ : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (p p' : K) (k : ℕ) (c s : K)
    (hd : d (c * s) = c * d s + s * d c) (h1 : ∀ a y, δ a (c * y) = c * δ a y) :
    ringOp d δ Θ u p p' k (c * s) = c * ringOp d δ Θ u p p' k s + 2 * (k : K) * d c * s := by
  simp only [ringOp, h1, hd, mul_left_comm _ c, ← Finset.mul_sum]
  try ring

theorem exists_derivation_fractionRing_ext (Ω : Type) [CommRing Ω] [IsDomain Ω] (d : Derivation ℤ Ω Ω) :
    ∃ dL : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ w, dL (algebraMap Ω (FractionRing Ω) w) = algebraMap Ω (FractionRing Ω) (d w) := by
  obtain ⟨δ', hder, hδ'⟩ := Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc (nonZeroDivisors Ω) (B := FractionRing Ω)
    (fun w => algebraMap Ω (FractionRing Ω) (d w)) (fun a b => by simp)
    (fun a b => by simp [Derivation.leibniz, smul_eq_mul])
  have hsm : ∀ (z : ℤ) (a : FractionRing Ω), δ' (z • a) = z • δ' a := by
    intro z a
    induction z using Int.induction_on with
    | zero => simp [hder.der_zero]
    | succ i ih => simp only [add_smul, one_smul, hder.add, ih]
    | pred i ih => simp only [sub_smul, one_smul, hder.der_sub, ih]
  have hint : ∀ m : ℤ, δ' (m : FractionRing Ω) = 0 := fun m => by
    have := hsm m 1
    rw [zsmul_eq_mul, _root_.mul_one, hder.der_one] at this
    simpa using this
  have hlb : ∀ a b : FractionRing Ω, δ' (a * b) = a • δ' b + b • δ' a := fun a b => by
    rw [hder.mul, smul_eq_mul, smul_eq_mul]
  let dL : Derivation ℤ (FractionRing Ω) (FractionRing Ω) := { toFun := δ', map_add' := hder.add, map_smul' := fun m y => by rw [RingHom.id_apply, Algebra.smul_def, eq_intCast, zsmul_eq_mul, hder.mul, hint m, MulZeroClass.mul_zero, add_zero], map_one_eq_zero' := hder.der_one, leibniz' := hlb }
  exact ⟨dL, hδ'⟩

theorem heat_acts_on_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) u' p p' k s)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmono htt hab
  intro Y n vH dd hinv v' hpt D h hbasic hdef i0 Ω _ _ _ φ x x' δ hcompl hx hx' hδφ hδ hpx dΩ hW hdΩ g hg δL hδL
  letI := H.starRing
  have hDφ := (GlobalTheory.T.heatOperator_value_at_point_eq_ringOperator R Y.H _ _ P.D.toPre.P.L n dd ⇑D h i0 Ω φ x hx δ hδ dΩ hW hdΩ).1
  obtain ⟨e, p0, p0', hcore⟩ := GlobalTheory.T.heat_operator_values_of_sections_complete_local_ring E H R t P m tt gam hmono htt hab Y n vH dd hinv v' hpt D h hbasic hdef i0 Ω φ x x' δ
    hcompl hx hx' hδφ hδ hpx dΩ hW hdΩ g hg
  obtain ⟨dL, hdL⟩ := exists_derivation_fractionRing_ext Ω dΩ
  set iK := algebraMap Ω (FractionRing Ω) with hiK
  have hiKinj : Function.Injective iK := IsFractionRing.injective Ω (FractionRing Ω)
  have h2R : IsUnit (2 : R) := by
    have := (isUnit_iff_ne_zero.2 (two_ne_zero : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
    rwa [map_ofNat] at this
  have h2K : (2 : FractionRing Ω) ≠ 0 := by
    have := (h2R.map (iK.comp φ)).ne_zero
    rwa [map_ofNat] at this
  have hsymm : ((iK.comp φ).mapMatrix h.Θ)ᵀ = (iK.comp φ).mapMatrix h.Θ := by
    show (h.Θ.map _)ᵀ = h.Θ.map _
    rw [← Matrix.transpose_map, h.symm]
  have hce : iK ((e⁻¹ : Ωˣ) : Ω) ≠ 0 := fun h0 => (e⁻¹).ne_zero (hiKinj (h0.trans (map_zero iK).symm))
  obtain ⟨d', u'', q, q', hd'c, hconj⟩ := GlobalTheory.T.heatOperatorOnRing_conj_pow_fractionField Ω n dL δL ((iK.comp φ).mapMatrix h.Θ) hsymm h2K
    (fun a => iK (φ (h.u a))) (iK p0) (iK p0') _ hce
  refine ⟨d', u'', q, q', fun r => ?_, ?_⟩
  · rw [hd'c _ (fun a => by rw [hδL, hδφ, map_zero]), hdL, hDφ]
  intro k hk s ⟨r₁, σ, ω, hr₁, hv, hs⟩
  obtain ⟨r₂, σ₂, ω₂, hr₂, hv₂, hω₂⟩ := hcore k hk σ ω hv
  have key : iK ω₂ = iK (φ r₂) * ringOp ⇑d' (fun a => ⇑(δL a)) ((iK.comp φ).mapMatrix h.Θ) u'' q q' k (iK ω) := by
    rw [hω₂, map_mul, map_mul, map_pow, ringOp_map_of_intertwine iK _ _ _ _ hdL hδL, map_mul, map_pow]
    have e1 : iK.mapMatrix (φ.mapMatrix h.Θ) = (iK.comp φ).mapMatrix h.Θ := by
      ext a b; simp
    rw [e1, hconj, ← _root_.mul_assoc (iK (e : Ω) ^ k), ← mul_pow, ← map_mul, Units.mul_inv, map_one, one_pow, _root_.one_mul]
  by_cases hc1 : φ r₁ = 0
  · exact ⟨r₁, σ, ω, hr₁, hv, by rw [hs, hc1]; simp⟩
  · have hδc : ∀ a, δL a (iK (φ r₁)) = 0 := fun a => by rw [hδL, hδφ, map_zero]
    have hdc : d' (iK (φ r₁)) = iK (φ (D r₁)) := by rw [hd'c _ hδc, hdL, hDφ]
    have hs' : iK ω = iK (φ r₁) * s := hs
    have hRO := ringOp_mul_of_const ⇑d' (fun a => ⇑(δL a)) ((iK.comp φ).mapMatrix h.Θ) u'' q q' k (iK (φ r₁)) s
      (by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]) (fun a y => by
        rw [Derivation.leibniz, hδc, smul_zero, add_zero, smul_eq_mul])
    rw [← hs', hdc] at hRO
    obtain ⟨σ₃, hv₃⟩ := GlobalTheory.T.sectionValueInFrame_linearCombination R t.G t.PP.L Ω φ x' hx' g k σ₂ σ ω₂ ω r₁ (-(2 * (k : R)) * D r₁ * r₂) hv₂ hv
    refine ⟨r₁ * r₁ * r₂, σ₃, _, mul_ne_zero (mul_ne_zero hr₁ hr₁) hr₂, hv₃, ?_⟩
    simp only [RingHom.comp_apply, map_add (f := _), map_mul, map_neg, map_natCast, map_ofNat]
    rw [key, hRO, hs']
    ring

end GlobalTheory.Heat
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_torusInvariant_lift_derivation_raynaud : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ d : Fld Y.H.left, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V.1) d ∧ ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  first | exact @GlobalTheory.Heat.HxLift.exists_invLift | exact GlobalTheory.Heat.HxLift.exists_invLift | (intros; apply GlobalTheory.Heat.HxLift.exists_invLift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section
namespace GlobalTheory.GSep.FrameUniq

section Gen
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {D : DegPre R}

theorem exists_ratio {b b' : TF (R := R) F ⟶ D.P.A} (h : b' = b) {w : Frm D F 1 b} {w' : Frm D F 1 b'}
    (hw : w.IsGen) (hw' : w'.IsGen) : ∃ c : F, c ≠ 0 ∧ ∀ z J, Good D.P.L z J →
      (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val := by
  subst h
  exact exists_frame_ratio hw hw'

theorem coef_congr' {k : ℕ} {g g₂ : GtPtF D F} {w : Frm D F k g.b} {w₂ : Frm D F k g₂.b} (hw : w.IsGen)
    (hb : g₂.b = g.b) (hs : ∀ χ z J, Good D.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J)
    (hv : ∀ z J, Good D.P.L z J → val w₂ (𝟙 _) z J = val w (𝟙 _) z J) (s : Fam D F k) (χ : D.X) :
    coef s g₂ w₂ χ = coef s g w χ := by
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  have e : lift (𝟙 (TF (R := R) F)) g₂.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
  rw [hs χ z J hJ, hv z J hJ, e]
  exact a
end Gen

theorem frame_val_eq : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x)
  (g g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  w₀.IsGen → fr.IsGen →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g w x fr →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀ g₂ w₂ x fr →
  g₂.b = g.b → (∀ χ z J, Good 𝔪.D.toPre.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J) →
  ∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val w (𝟙 _) z J := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ x fr g g₂ w w₂ hw₀ hfr _ hw hO _ hw₂ hO₂ hb hs
  have hadm : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  obtain ⟨c, hc, hcv⟩ := exists_ratio hb hw hw₂
  have pow_one_of : ∀ k : ℕ, 4 ≤ k → c ^ k = 1 := by
    intro k hk
    have hk1 : 1 ≤ k := by omega
    obtain ⟨wk, hwkg, hwk⟩ := TorsionValue.exists_frm_pow w hw k
    obtain ⟨wk₂, hwk₂g, hwk₂⟩ := TorsionValue.exists_frm_pow w₂ hw₂ k
    obtain ⟨w', hw'g, hw'⟩ := TorsionValue.exists_frm_scale wk hwkg (pow_ne_zero k hc)
    obtain ⟨th, a, ha0, ha⟩ := GlobalTheory.UT.NonVan.exists_sec_ne_zero GlobalTheory.firstFiveLaws V 𝔪.A (FractionRing V) k hk x fr hfr
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF GlobalTheory.globalFns_holds 𝔪.U (FractionRing V) (k := k) hk1 w₀ hw₀
    have hexp : 𝔪.U.ExpandsF (FractionRing V) k w₀ th (e th) := (he th _).2 rfl
    have H1 := hO k hk1 wk hwk hwkg th (e th) a hexp ha
    have H2 := hO₂ k hk1 wk₂ hwk₂ hwk₂g th (e th) a hexp ha
    have hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → val wk₂ (𝟙 _) z J = val w' (𝟙 _) z J := by
      intro z J hJ
      apply Units.ext
      rw [hwk₂ z J hJ, hw' z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hcv z J hJ, mul_pow,
        cst_eq, cst_eq, map_pow]
    have e2 : coef (e th) g₂ wk₂ = fun χ => c ^ k * coef (e th) g wk χ := funext fun χ => by
      rw [coef_congr' hw'g hb hs hv, TorsionValue.coef_scale hwkg hw' (e th) χ]
    rw [e2] at H2
    have hl := ((GlobalTheory.AdicSum.sumF_calculus V (maximalIdeal V) hadm (FractionRing V) _ (coef (e th) g wk)
      (coef (e th) g wk) a a).2.1 H1 H1 (c ^ k - 1))
    have ee : (fun χ => (c ^ k - 1) * coef (e th) g wk χ + coef (e th) g wk χ) = fun χ => c ^ k * coef (e th) g wk χ :=
      funext fun χ => by ring
    rw [ee] at hl
    have := (GlobalTheory.AdicSum.sumF_calculus V (maximalIdeal V) hadm (FractionRing V) _ _ (coef (e th) g wk) a
      ((c ^ k - 1) * a + a)).1 H2 hl
    have h0 : (c ^ k - 1) * a = 0 := by linear_combination -this
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right ha0)
  have h4 := pow_one_of 4 le_rfl
  have h5 := pow_one_of 5 (by norm_num)
  have hc1 : c = 1 := by linear_combination (-c) * h4 + h5
  intro z J hJ
  apply Units.ext
  rw [hcv z J hJ, hc1, cst_eq, map_one, _root_.one_mul]

end GlobalTheory.GSep.FrameUniq
end
end
