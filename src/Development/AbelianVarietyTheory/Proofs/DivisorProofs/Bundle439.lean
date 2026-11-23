module

public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle182
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle389
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle390
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
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory.RegularCompletionPackage

theorem exists_regular_completion :
    ∀ (R₁ Ω : Type) [CommRing R₁] [IsRegularLocalRing R₁] [Field Ω] (u : R₁ →+* Ω),
      RingHom.ker u = maximalIdeal R₁ →
      ∃ (C : Type) (_ : CommRing C) (_ : IsRegularLocalRing C) (c : R₁ →+* C) (uC : C →+* Ω),
        c.Flat ∧ (maximalIdeal R₁).map c = maximalIdeal C ∧ IsAdicComplete (maximalIdeal C) C ∧
        RingHom.ker uC = maximalIdeal C ∧ uC.comp c = u := by
  intro R₁ Ω _ _ _ u hu
  set C := AdicCompletion (maximalIdeal R₁) R₁
  haveI : IsRegularLocalRing C := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R₁
  have hbij := AdicCompletion.residueField_map_bijective_of_fg (R := R₁)
    (maximalIdeal R₁).fg_of_isNoetherianRing
  let e : ResidueField R₁ ≃+* ResidueField C :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap R₁ C)) hbij
  let ub : ResidueField R₁ →+* Ω := Ideal.Quotient.lift (maximalIdeal R₁) u
    (fun a ha => by rw [← RingHom.mem_ker, hu]; exact ha)
  let uC : C →+* Ω := (ub.comp e.symm.toRingHom).comp (residue C)
  have hcomp : uC.comp (algebraMap R₁ C) = u := by
    ext r
    simp only [uC, RingHom.comp_apply]
    have : residue C (algebraMap R₁ C r) = e (residue R₁ r) := by
      simp [e, ResidueField.map_residue]
    rw [this]
    simp [ub]
    rfl
  refine ⟨C, inferInstance, inferInstance, algebraMap R₁ C, uC,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
    (AdicCompletion.maximalIdeal_eq_map).symm, inferInstance, ?_, hcomp⟩
  ext x
  rw [RingHom.mem_ker]
  simp only [uC, RingHom.comp_apply]
  constructor
  · intro h
    have h1 : e.symm (residue C x) = 0 := (injective_iff_map_eq_zero ub).1 ub.injective _ h
    have h2 : residue C x = 0 := by simpa using h1
    simpa [residue_eq_zero_iff] using h2
  · intro h
    rw [(residue_eq_zero_iff x).2 h]
    simp

end GlobalTheory.RegularCompletionPackage
end

section

open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem exists_finite_depth_two_hull_of_etale_off_closed_point : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S → ∀ (A : Type) [CommRing A] [Algebra S A] [Module.Finite S A], ReciprocityTheory.CA.ModDepthGE S A 1 → (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra S A'), Module.Finite S A' ∧ ∃ ι : A →ₐ[S] A', Function.Injective ι ∧ ReciprocityTheory.CA.ModDepthGE S A' 2 ∧ (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A')) ∧ ∃ k : ℕ, ∀ x ∈ maximalIdeal S ^ k, ∀ y : A', x • y ∈ ι.range := by
  intro S _ _ hdim A _ _ _ hdep het
  obtain ⟨hSd, hSic⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing S
  have htf : ∀ s : S, s ≠ 0 → IsSMulRegular A s := GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos_domain' S A hdep het
  let K := FractionRing S
  let j : A →ₐ[S] K ⊗[S] A := Algebra.TensorProduct.includeRight
  have hj : ∀ a, j a = TensorProduct.mk S K A 1 a := fun a => rfl
  haveI : IsLocalizedModule (nonZeroDivisors S) (TensorProduct.mk S K A 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).mpr (TensorProduct.isBaseChange S A K)
  have hjinj : Function.Injective j := by
    intro a b hab
    rw [hj, hj] at hab
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors S) hab
    exact htf c (nonZeroDivisors.coe_ne_zero c) hc

  have hVtf : ∀ s : S, s ≠ 0 → ∀ v w : K ⊗[S] A, s • v = s • w → v = w := by
    intro s hs v w h
    rw [← algebraMap_smul K s v, ← algebraMap_smul K s w] at h
    have hs' : algebraMap S K s ≠ 0 := by
      rw [ne_eq, ← map_zero (algebraMap S K)]
      exact fun e => hs (IsFractionRing.injective S K e)
    exact smul_right_injective _ hs' h
  let B := idealTransform S (maximalIdeal S) A
  have hjB : ∀ a, j a ∈ B := fun a => ⟨0, fun b _ => ⟨b • a, by simp [j]⟩⟩
  let ι : A →ₐ[S] B := j.codRestrict B hjB
  have hιinj : Function.Injective ι := fun a b h => hjinj (congrArg Subtype.val h)
  have hrange : ∀ y : B, y ∈ ι.range ↔ (y : K ⊗[S] A) ∈ j.range := by
    intro y
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, ha⟩; exact ⟨a, Subtype.ext ha⟩

  have hfg : (Subalgebra.toSubmodule B).FG := by
    refine GlobalTheory.T.fg_of_ideal_pow_smul_mem_range_tensor S (maximalIdeal S) (GlobalTheory.T.isInteger_of_maximalIdeal_pow_smul_isInteger' S hdim) A _ fun z hz => ?_
    obtain ⟨k, hk⟩ := hz
    exact ⟨k, fun a ha => by obtain ⟨b, hb⟩ := hk a ha; exact ⟨b, hb⟩⟩
  haveI hfin : Module.Finite S B := Module.Finite.iff_fg.mpr hfg

  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ a ∈ maximalIdeal S ^ k, ∀ y : B, a • y ∈ ι.range.toSubmodule := by
    refine GlobalTheory.T.exists_pow_smul_mem_of_forall_exists' S (maximalIdeal S) B _ fun y => ?_
    obtain ⟨k, hk⟩ := y.2
    exact ⟨k, fun a ha => (hrange _).2 (hk a ha)⟩
  refine ⟨B, inferInstance, inferInstance, hfin, ι, hιinj, ?_, ?_, k, hk⟩
  ·
    obtain ⟨q, -, hq0, hqm⟩ := exists_isPrime_ne_bot_lt_maximalIdeal_of_two_le_ringKrullDim S hdim
    have hm0 : maximalIdeal S ≠ ⊥ := (bot_le.trans_lt hqm).ne'
    obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm0
    haveI : Nontrivial A := by
      obtain ⟨rs, -, -, hreg⟩ := hdep
      by_contra hA
      rw [not_nontrivial_iff_subsingleton] at hA
      exact hreg.2 (Subsingleton.elim _ _)
    haveI : Nontrivial B := nontrivial_of_ne (ι 0) (ι 1) (hιinj.ne zero_ne_one)
    have hxreg : IsSMulRegular B x := fun u v h =>
      Subtype.ext (hVtf x hx0 _ _ (congrArg Subtype.val h))
    refine GlobalTheory.T.modDepthGE_two_of_regular_quotient_no_socle S B x hxm hxreg fun u hu => ?_
    let w : K ⊗[S] A := (algebraMap S K x)⁻¹ • (u : K ⊗[S] A)
    have hxw : x • w = u := by
      simp only [w, ← algebraMap_smul K x, smul_smul]
      rw [mul_inv_cancel₀, one_smul]
      rw [ne_eq, ← map_zero (algebraMap S K)]
      exact fun e => hx0 (IsFractionRing.injective S K e)
    have hwB : w ∈ B := by
      refine mem_idealTransform_of_forall_smul_mem w fun a ha => ?_
      obtain ⟨v, -, hv⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp (hu a ha)
      have : a • w = v := by
        apply hVtf x hx0
        rw [smul_comm, hxw]
        exact (congrArg Subtype.val hv).symm
      rw [this]; exact v.2
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨⟨w, hwB⟩, Submodule.mem_top, Subtype.ext hxw⟩
  · intro p _ hp
    have hnot : ¬ maximalIdeal S ^ k ≤ p := fun h =>
      hp ((maximalIdeal.isMaximal S).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.IsPrime.le_of_pow_le h)).symm
    obtain ⟨s, hs, hsp⟩ := Set.not_subset.mp hnot
    exact GlobalTheory.T.etale_localization_of_injective_cokernel_killed S A B ι hιinj p s hsp (hk s hs) (het p hp)

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory


open Pointwise in
theorem modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R,
      f ≠ 0 → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B]
      [Nontrivial B] (k : ℕ), 1 ≤ k →
      ReciprocityTheory.CA.ModDepthGE R (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) 2 := by
  intro R _ _ hd f hf hf0 B _ _ _ _ _ k hk
  haveI : IsDomain R := GlobalTheory.isDomain_of_isRegularLocalRing R
  have h3 : ReciprocityTheory.CA.ModDepthGE R B 3 :=
    GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing R hd B
  have hfk0 : f ^ k ≠ 0 := pow_ne_zero k hf0
  have hfkm : f ^ k ∈ maximalIdeal R := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_succ]
    exact Ideal.mul_mem_left _ _ hf
  have hreg : IsSMulRegular B (f ^ k) := smul_right_injective B hfk0
  have h2 : ReciprocityTheory.CA.ModDepthGE R (QuotSMulTop (f ^ k) B) 2 :=
    ReciprocityTheory.CA.ModDepthGE.quotSMulTop hfkm hreg h3
  have hpow : (Ideal.span {f}).map (algebraMap R B) ^ k =
      (Ideal.span {f ^ k}).map (algebraMap R B) := by
    rw [← Ideal.map_pow, Ideal.span_singleton_pow]
  have heq : ((f ^ k) • (⊤ : Submodule R B)) =
      ((Ideal.span {f}).map (algebraMap R B) ^ k).restrictScalars R := by
    rw [hpow]
    ext x
    simp [Submodule.mem_smul_pointwise_iff_exists, Ideal.map_span, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  let e : QuotSMulTop (f ^ k) B ≃ₗ[R] (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) :=
    (Submodule.quotEquivOfEq _ _ heq).trans
      (Submodule.Quotient.restrictScalarsEquiv R ((Ideal.span {f}).map (algebraMap R B) ^ k))
  exact (ReciprocityTheory.CA.modDepthGE_congr e 2).mp h2

end GlobalTheory
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.modDepthGE_three_of_free_regularLocal : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M] [Nontrivial M], ReciprocityTheory.CA.ModDepthGE R M 3 := by
  first | exact @GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing | exact GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing | (intros; apply GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenTransl

variable {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R))

abbrev genOver : Over (Sp R) := Over.mk (pullback.snd G.hom (jK R) ≫ jK R)

def genPr : genOver G ⟶ G := Over.homMk (pullback.fst G.hom (jK R)) pullback.condition

def genPt (a : Over.mk (jK R) ⟶ G) : genOver G ⟶ G :=
  Over.homMk (pullback.snd G.hom (jK R) ≫ a.left) (by
    rw [Category.assoc, Over.w a]; rfl)

def IsGenTransl [GrpObj G] (L L₁ : LB G.left) (a : Over.mk (jK R) ⟶ G) : Prop :=
  LBIso (L₁.pull (pullback.fst G.hom (jK R))) (L.pull ((genPr G * genPt G a).left))

end GlobalTheory.GenTransl
end
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out


theorem _root_.GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), LocallyOfFiniteType π → Function.Surjective π → ∀ (K : Type) [Field K] (x : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (y : Sp K' ⟶ Y), σ.Finite ∧ y ≫ π = spMap σ ≫ x := by
  first | exact @GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft | exact GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft | (intros; apply GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.RetractionLiftSection

theorem exists_retraction {R K A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] (φ : R →+* A) (hφ : φ.IsIntegral) (ψ : A →+* K)
    (h : ψ.comp φ = algebraMap R K) :
    ∃ σ : A →+* R, (algebraMap R K).comp σ = ψ ∧ σ.comp φ = RingHom.id R := by
  have inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have key : ∀ a : A, ∃ r : R, algebraMap R K r = ψ a := by
    intro a
    obtain ⟨f, hf, hfa⟩ := hφ a
    have hi : IsIntegral R (ψ a) := by
      refine ⟨f, hf, ?_⟩
      rw [← h, ← Polynomial.hom_eval₂, hfa, map_zero]
    exact IsIntegrallyClosed.algebraMap_eq_of_integral hi
  choose s hs using key
  let σ : A →+* R :=
    { toFun := s
      map_one' := inj (by rw [hs, map_one, map_one])
      map_mul' := fun a b => inj (by rw [map_mul, hs, hs, hs, map_mul])
      map_zero' := inj (by rw [hs, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [map_add (f := _), hs, hs, hs, map_add (f := _)]) }
  refine ⟨σ, RingHom.ext hs, RingHom.ext fun r => inj ?_⟩
  exact (hs (φ r)).trans (RingHom.congr_fun h r)

theorem exists_section {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {W : Scheme.{0}} (q : W ⟶ Spec (CommRingCat.of R)) [IsFinite q]
    (y : Spec (CommRingCat.of K) ⟶ W) (h : y ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ W, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = y ∧ s ≫ q = 𝟙 _ := by
  haveI : IsAffine W := isAffine_of_isAffineHom q
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ q)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ W.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hint : φ.hom.IsIntegral := ((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, h]
  obtain ⟨σ, h₁, h₂⟩ := exists_retraction (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)
  refine ⟨Spec.map (CommRingCat.ofHom σ) ≫ W.isoSpec.inv, ?_, ?_⟩
  · have e : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h₁
    rw [← Category.assoc, ← Spec.map_comp]
    erw [e]
    rw [hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · have e : φ ≫ CommRingCat.ofHom σ = 𝟙 _ := CommRingCat.hom_ext h₂
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    erw [e]
    rw [Spec.map_id]

theorem exists_lift {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Z P : Scheme.{0}} (p : Z ⟶ P) [IsFinite p] (x : Spec (CommRingCat.of R) ⟶ P)
    (y : Spec (CommRingCat.of K) ⟶ Z) (h : y ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ x) :
    ∃ ξ : Spec (CommRingCat.of R) ⟶ Z, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ ξ = y ∧ ξ ≫ p = x := by
  obtain ⟨s, h₁, h₂⟩ := exists_section (K := K) (pullback.snd p x) (pullback.lift y _ h) (pullback.lift_snd _ _ _)
  refine ⟨s ≫ pullback.fst p x, ?_, ?_⟩
  · rw [← Category.assoc, h₁, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.id_comp]

theorem lift_finite : ∀ (R : Type) [inst : CommRing R] [IsDomain R] [IsIntegrallyClosed R] (Z P : AlgebraicGeometry.Scheme) (p : Z ⟶ P) (ξ₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ P) (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing R) ⟶ Z), AlgebraicGeometry.IsFinite p → CategoryTheory.CategoryStruct.comp y p = CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Out.jK R) ξ₀ → ∃ (ξ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Z), CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Out.jK R) ξ = y ∧ CategoryTheory.CategoryStruct.comp ξ p = ξ₀ :=
  fun R _ _ _ _ _ p x y _ h => exists_lift (R := R) (K := FractionRing R) p x y h

end GlobalTheory.RetractionLiftSection
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsSympLevel (D : Datum H) {k : Type} [Field k] {Q : Type} [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) (N : ℕ) (z : kˣ) (ev : D.La → Q) : Prop :=
  (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧
    (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ x : Q, x ^ N = 1 ↔ ∃ a, ev a = x) ∧
    ∀ a b, e N (ev a) (ev b) (z ^ D.EF a b)

def Induces {D : Datum H} (l : Level H) {Q : Type} [Group Q] (etaA eta ev : D.La → Q) : Prop :=
  (∀ a, ev a ^ (l.M' / l.A) = etaA a) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ev a ^ (l.M' / l.M) = eta a

theorem A_dvd_M' (l : Level H) : l.A ∣ l.M' := Nat.dvd_lcm_right _ _

theorem M_dvd_M' (l : Level H) : l.M ∣ l.M' := Nat.dvd_lcm_left _ _

theorem M'_pos (l : Level H) : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

end GlobalTheory.FullLevel
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EqCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsLevGrp {H : Host E} (l : Level H) {r : ℕ} (Y : Data E r) : Prop :=
  ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧
    (∀ x ∈ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • Y.Λ, ∃ y ∈ Y.Λ,
      (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M • y) ∧
    (∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.A • y)

def IsSelfDualTr {r : ℕ} (Y : Data E r) : Prop :=
  ∀ x : Fin r → E, x ∈ Y.Λ ↔ ∀ y ∈ Y.Λ, ∃ n : ℤ, Algebra.trace ℚ E (-Y.ξ0 * herm Y.Gm x y) = n

end GlobalTheory.EqCovol
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem range_jK_fromSpecStalk_subset_of_dense_range {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S]
    [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (s : S) :
    Set.range (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) ⊆
      Set.range j := by
  rintro _ ⟨x, rfl⟩
  have hZ : irreducibleComponent s ∈ irreducibleComponents S :=
    irreducibleComponent_mem_irreducibleComponents s
  have hZo : IsOpen (irreducibleComponent s) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hZ
  obtain ⟨_, hu, ⟨u, rfl⟩⟩ := hj.inter_open_nonempty _ hZo ⟨s, mem_irreducibleComponent⟩
  have hg := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hZ)
  have hgs : hZ.1.genericPoint ⤳ s := hg.specializes mem_irreducibleComponent
  have hgr : hZ.1.genericPoint ∈ Set.range (S.fromSpecStalk s) := by
    rw [Scheme.range_fromSpecStalk]; exact hgs
  obtain ⟨p, hp⟩ := hgr
  have hxp : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s)) x ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes (R := S.presheaf.stalk s) _ _).mp ?_
    show Ideal.comap _ x.asIdeal ≤ p.asIdeal
    have hx0 : x.asIdeal = ⊥ :=
      @Ideal.eq_bot_of_prime (FractionRing (S.presheaf.stalk s)) _ x.asIdeal x.isPrime
    intro a ha
    rw [Ideal.mem_comap, hx0, Ideal.mem_bot] at ha
    have ha0 : a = 0 :=
      IsFractionRing.injective (S.presheaf.stalk s) (FractionRing (S.presheaf.stalk s))
        (by simpa using ha)
    rw [ha0]
    exact Ideal.zero_mem _
  have h1 : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) x ⤳
      hZ.1.genericPoint := by
    rw [Scheme.Hom.comp_apply, ← hp]
    exact hxp.map (S.fromSpecStalk s).continuous
  have h2 : hZ.1.genericPoint ⤳ j u := hg.specializes hu
  exact (h1.trans h2).mem_open j.isOpenEmbedding.isOpen_range ⟨u, rfl⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.trace_product_skew_hermitian_real : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X Y : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace ∈ maximalRealSubfield E := by
  first | exact @GlobalTheory.trace_mul_skew_mem_maximalRealSubfield | exact GlobalTheory.trace_mul_skew_mem_maximalRealSubfield | (intros; apply GlobalTheory.trace_mul_skew_mem_maximalRealSubfield <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.lie_basis_spans_unitary_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ i, (e i).trace = 0 ∧ ∀ u w, herm G (e i *ᵥ u) w + herm G u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → X ∈ Submodule.span (maximalRealSubfield E) (Set.range e) := by
  first | exact @GlobalTheory.SkewSpan.mem_span_of_skew | exact GlobalTheory.SkewSpan.mem_span_of_skew | (intros; apply GlobalTheory.SkewSpan.mem_span_of_skew <;> assumption)
end
