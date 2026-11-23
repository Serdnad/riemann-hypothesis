module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfIsLocalization
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle010
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
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.CStarAlgebra.Matrix
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory.IndEtaleCancel

theorem isIndEtale_of_etale_of_isIndEtale : ∀ (A W O : Type) [CommRing A] [CommRing W]
    [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O]
    [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) →
      GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) := by
  intro A W O _ _ _ _ _ _ _ _ h
  have hT : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W (W ⊗[A] O)) :=
    GlobalTheory.isIndEtale_tensorProduct_left A O W h
  obtain ⟨t, ht1, ht2⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := W)).1 inferInstance
  let g : W →ₐ[A] O := IsScalarTower.toAlgHom A W O
  let μ : W ⊗[A] O →ₐ[W] O := Algebra.TensorProduct.lift (Algebra.ofId W O) (AlgHom.id A O)
    (fun _ _ => Commute.all _ _)
  have hμ : ∀ w o, μ (w ⊗ₜ o) = algebraMap W O w * o := fun w o => by simp [μ]
  let e : W ⊗[A] O := Algebra.TensorProduct.map (AlgHom.id A W) g t
  have he1 : ∀ s : W, ((1 : W) ⊗ₜ[A] (algebraMap W O s) - s ⊗ₜ[A] (1 : O)) * e = 0 := by
    intro s
    have := congrArg (Algebra.TensorProduct.map (AlgHom.id A W) g) (ht1 s)
    simpa [map_mul, map_sub, e, g] using this
  have hμe : μ e = 1 := by
    have H : (μ.restrictScalars A).comp (Algebra.TensorProduct.map (AlgHom.id A W) g) =
        g.comp (Algebra.TensorProduct.lmul' A) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [μ, g, Algebra.TensorProduct.lmul'_apply_tmul, IsScalarTower.algebraMap_apply A W O]
    have := DFunLike.congr_fun H t
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at this
    rw [show μ e = _ from this, ht2, map_one]
  have hkey : ∀ x : W ⊗[A] O, e * x = e * ((1 : W) ⊗ₜ[A] μ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul w o =>
      rw [hμ]
      have h1 : (w ⊗ₜ[A] o : W ⊗[A] O) = (w ⊗ₜ[A] (1 : O)) * ((1 : W) ⊗ₜ[A] o) := by simp
      have h2 : ((1 : W) ⊗ₜ[A] (algebraMap W O w * o) : W ⊗[A] O) =
          ((1 : W) ⊗ₜ[A] algebraMap W O w) * ((1 : W) ⊗ₜ[A] o) := by simp
      linear_combination e * h1 - e * h2 - ((1 : W) ⊗ₜ[A] o) * he1 w
    | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), TensorProduct.tmul_add, mul_add]
  have hidem : IsIdempotentElem e := by
    show e * e = e
    rw [hkey e, hμe, Algebra.TensorProduct.one_def.symm, mul_one]
  letI : Algebra (W ⊗[A] O) O := μ.toRingHom.toAlgebra
  have hmap : ∀ x, algebraMap (W ⊗[A] O) O x = μ x := fun _ => rfl
  haveI : IsScalarTower W (W ⊗[A] O) O :=
    IsScalarTower.of_algebraMap_eq (fun w => by rw [hmap, μ.commutes])
  haveI : IsLocalization.Away e O := by
    refine IsLocalization.away_of_isIdempotentElem_of_mul hidem (fun x y => ?_) ?_
    · rw [hmap, hmap]
      constructor
      · intro hxy; rw [hkey x, hkey y, hxy]
      · intro hxy
        have hx : μ (e * x) = μ x := by rw [map_mul, hμe, one_mul]
        have hy : μ (e * y) = μ y := by rw [map_mul, hμe, one_mul]
        rw [← hx, ← hy, hxy]
    · intro o
      exact ⟨(1 : W) ⊗ₜ o, by rw [hmap, hμ, map_one, one_mul]⟩
  exact GlobalTheory.IndEtaleLoc.isIndEtale_of_isLocalization W (W ⊗[A] O) O (Submonoid.powers e) hT

end GlobalTheory.IndEtaleCancel
end

section

noncomputable section

open GlobalTheory.EtC

namespace GlobalTheory.LocInField

variable {K : Type} [Field K]

def locAt (R : Subring K) (𝔪 : Ideal R) [𝔪.IsPrime] : Subring K where
  carrier := {x | ∃ a s : R, s ∉ 𝔪 ∧ x * s = a}
  zero_mem' := ⟨0, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  one_mem' := ⟨1, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, t, ht, hy⟩
    refine ⟨a * t + b * s, s * t, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs ht, ?_⟩
    push_cast; rw [← hx, ← hy]; ring
  mul_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, t, ht, hy⟩
    refine ⟨a * b, s * t, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs ht, ?_⟩
    push_cast; rw [← hx, ← hy]; ring
  neg_mem' := by
    rintro x ⟨a, s, hs, hx⟩
    refine ⟨-a, s, hs, ?_⟩
    push_cast; rw [← hx]; ring

theorem le_locAt (R : Subring K) (𝔪 : Ideal R) [𝔪.IsPrime] : R ≤ locAt R 𝔪 := fun x hx =>
  ⟨⟨x, hx⟩, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩

theorem exists_local_subring : ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] (φ : k →+* K) (R : Subring K) (𝔪 : Ideal R),
    φ.range ≤ R → 𝔪.IsMaximal → (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) →
    (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) → (∀ x : K, IsIntegral R x → x ∈ R) →
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  intro k K _ _ _ φ R 𝔪 hφ hmax hres hden hic
  haveI : 𝔪.IsPrime := hmax.isPrime
  have hRT := le_locAt R 𝔪
  letI : Algebra R (locAt R 𝔪) := (Subring.inclusion hRT).toAlgebra
  haveI : IsScalarTower R (locAt R 𝔪) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hunit : ∀ s : R, s ∉ 𝔪 → IsUnit (algebraMap R (locAt R 𝔪) s) := by
    intro s hs
    have hs0 : (s : K) ≠ 0 := fun h => hs (by rw [show s = 0 from Subtype.ext h]; exact zero_mem _)
    refine isUnit_iff_exists_inv.2 ⟨⟨(s : K)⁻¹, 1, s, hs, by simp [hs0]⟩, Subtype.ext ?_⟩
    change (s : K) * (s : K)⁻¹ = 1
    exact mul_inv_cancel₀ hs0
  haveI hloc : IsLocalization 𝔪.primeCompl (locAt R 𝔪) :=
    { map_units := fun s => hunit s s.2
      surj := fun t => by
        obtain ⟨a, s, hs, h⟩ := t.2
        exact ⟨(a, ⟨s, hs⟩), Subtype.ext h⟩
      exists_of_eq := fun {x y} h => by
        have h' := congrArg Subtype.val h
        have hxy : x = y := Subtype.ext h'
        exact ⟨1, by rw [hxy]⟩ }
  haveI : IsLocalRing (locAt R 𝔪) := IsLocalization.AtPrime.isLocalRing (locAt R 𝔪) 𝔪
  refine ⟨locAt R 𝔪, fun x hx => hRT (hφ hx), ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · intro p hp hdeg
    have hdeg' : (p.map (algebraMap (locAt R 𝔪) K)).degree ≠ 0 := by
      rw [hp.degree_map, Polynomial.degree_eq_natDegree hp.ne_zero]
      exact_mod_cast hdeg.ne'
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg'
    have hyT : IsIntegral (locAt R 𝔪) y := ⟨p, hp, by rw [← Polynomial.eval_map]; exact hy⟩
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization 𝔪.primeCompl y hyT
    have hmR : m • y ∈ R := hic _ hm
    have hmy : m • y = y * ((m : R) : K) := by
      rw [Submonoid.smul_def, Algebra.smul_def, mul_comm]; rfl
    have hyT' : y ∈ locAt R 𝔪 := ⟨⟨m • y, hmR⟩, m, m.2, hmy.symm⟩
    refine ⟨⟨y, hyT'⟩, Subtype.ext ?_⟩
    change algebraMap (locAt R 𝔪) K (p.eval ⟨y, hyT'⟩) = 0
    rw [← Polynomial.eval₂_at_apply (algebraMap (locAt R 𝔪) K), ← Polynomial.eval_map]
    exact hy
  · intro t
    obtain ⟨a, s, hs, hts⟩ := t.2
    obtain ⟨c, hc, hac⟩ := hres a
    obtain ⟨e, he, hse⟩ := hres s
    have he0 : e ≠ 0 := by
      rintro rfl
      apply hs
      have h0 : s - ⟨φ 0, he⟩ = s := by
        rw [sub_eq_self]; exact Subtype.ext (by simp)
      rwa [h0] at hse
    have hg : φ (c / e) ∈ R := hφ ⟨c / e, rfl⟩
    have hge : φ (c / e) * φ e = φ c := by rw [← map_mul, div_mul_cancel₀ c he0]
    refine ⟨c / e, hRT hg, ?_⟩
    have hb : (a - ⟨φ c, hc⟩) - ⟨φ (c / e), hg⟩ * (s - ⟨φ e, he⟩) ∈ 𝔪 :=
      sub_mem hac (Ideal.mul_mem_left _ _ hse)
    have key : (t - ⟨φ (c / e), hRT hg⟩) * algebraMap R (locAt R 𝔪) s =
        algebraMap R (locAt R 𝔪) ((a - ⟨φ c, hc⟩) - ⟨φ (c / e), hg⟩ * (s - ⟨φ e, he⟩)) := by
      apply Subtype.ext
      change ((t : K) - φ (c / e)) * (s : K) = ((a : K) - φ c) - φ (c / e) * ((s : K) - φ e)
      linear_combination hts - hge
    have hb' := (IsLocalization.AtPrime.to_map_mem_maximal_iff (locAt R 𝔪) 𝔪 _).2 hb
    rw [← key] at hb'
    exact (Ideal.IsPrime.mem_or_mem inferInstance hb').resolve_right
      fun h => (IsLocalRing.mem_maximalIdeal _).1 h (hunit s hs)
  · haveI : FaithfulSMul (locAt R 𝔪) K := inferInstance
    refine IsFractionRing.of_field _ K fun z => ?_
    obtain ⟨d, hd, hdz⟩ := hden z
    have hd0 : (d : K) ≠ 0 := fun h => hd (Subtype.ext h)
    refine ⟨⟨(d : K) * z, hRT hdz⟩, ⟨d, hRT d.2⟩, ?_⟩
    change z = (d : K) * z / d
    field_simp

end GlobalTheory.LocInField
end
end

section

open NumberField GlobalTheory.LKTrip IsDedekindDomain
open scoped TensorProduct Matrix.Norms.L2Operator RestrictedProduct

noncomputable section

open Topology

namespace GlobalTheory.GfTop

theorem td_of_inj {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TotallyDisconnectedSpace Y]
    {f : X → Y} (hf : Continuous f) (hi : Function.Injective f) : TotallyDisconnectedSpace X :=
  ⟨fun s _ hs => Set.subsingleton_of_image hi s
    (isTotallyDisconnected_of_totallyDisconnectedSpace (f '' s) (f '' s) subset_rfl (hs.image f hf.continuousOn))⟩

theorem props_of_closedEmb {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LocallyCompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [SecondCountableTopology Y] {f : X → Y} (hf : IsClosedEmbedding f) :
    LocallyCompactSpace X ∧ T2Space X ∧ TotallyDisconnectedSpace X ∧ SecondCountableTopology X :=
  ⟨hf.locallyCompactSpace, hf.isEmbedding.t2Space, td_of_inj hf.continuous hf.injective,
    hf.isEmbedding.secondCountableTopology⟩

theorem isClosedEmbedding_embedProduct' (A : Type*) [TopologicalSpace A] [Monoid A] [ContinuousMul A] [T2Space A] :
    IsClosedEmbedding (Units.embedProduct A) := by
  refine ⟨Units.isEmbedding_embedProduct, ?_⟩
  have h : Set.range (Units.embedProduct A) =
      {x : A × Aᵐᵒᵖ | x.1 * x.2.unop = 1 ∧ x.2.unop * x.1 = 1} := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨u, hu⟩
      rw [← hu]
      simp
    · rintro ⟨h1, h2⟩
      exact ⟨⟨a, b.unop, h1, h2⟩, rfl⟩
  rw [h]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
    (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

theorem units_props (A : Type*) [TopologicalSpace A] [Monoid A] [ContinuousMul A] [LocallyCompactSpace A]
    [T2Space A] [TotallyDisconnectedSpace A] [SecondCountableTopology A] :
    LocallyCompactSpace Aˣ ∧ T2Space Aˣ ∧ TotallyDisconnectedSpace Aˣ ∧ SecondCountableTopology Aˣ := by
  obtain ⟨o1, o2, o3, o4⟩ := props_of_closedEmb (MulOpposite.opHomeomorph (M := A)).symm.isClosedEmbedding
  exact props_of_closedEmb (isClosedEmbedding_embedProduct' A)

theorem module_props (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [T2Space R] [TotallyDisconnectedSpace R] [SecondCountableTopology R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [TopologicalSpace M]
    [IsModuleTopology R M] :
    LocallyCompactSpace M ∧ T2Space M ∧ TotallyDisconnectedSpace M ∧ SecondCountableTopology M := by
  haveI : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  let b := Module.Free.chooseBasis R M
  let e : M ≃ₜ (Module.Free.ChooseBasisIndex R M → R) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  exact props_of_closedEmb e.isClosedEmbedding

section UPts

open GlobalTheory.LKTrip

variable {C : Type} [Ring C] [Algebra ℚ C] [Module.Finite ℚ C] (star : C →+* Cᵐᵒᵖ)

theorem upts_props (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [SecondCountableTopology R] :
    LocallyCompactSpace (UPts star R) ∧ T2Space (UPts star R) ∧ TotallyDisconnectedSpace (UPts star R) ∧
      SecondCountableTopology (UPts star R) := by
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  haveI : IsModuleTopology R (R ⊗[ℚ] C) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[ℚ] C) := IsModuleTopology.isTopologicalRing R (R ⊗[ℚ] C)
  obtain ⟨m1, m2, m3, m4⟩ := module_props R (R ⊗[ℚ] C)
  obtain ⟨u1, u2, u3, u4⟩ := units_props (R ⊗[ℚ] C)
  obtain ⟨v1, v2, v3, v4⟩ := units_props R
  let f : C →ₗ[ℚ] C := (MulOpposite.opLinearEquiv ℚ).symm.toLinearMap ∘ₗ star.toRatAlgHom.toLinearMap
  have hσeq : (fun y : R ⊗[ℚ] C => (starT star R y).unop) = LinearMap.baseChange R f := by
    funext y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [starT_tmul, LinearMap.baseChange_tmul]
      rfl
    | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add] at hx hy ⊢; rw [hx, hy]
  have hσ : Continuous (fun y : R ⊗[ℚ] C => (starT star R y).unop) := by
    rw [hσeq]
    exact IsModuleTopology.continuous_of_linearMap _
  have hcl : IsClosed ((UPts star R : Subgroup ((R ⊗[ℚ] C)ˣ × Rˣ)) : Set ((R ⊗[ℚ] C)ˣ × Rˣ)) := by
    have hs : ((UPts star R : Subgroup ((R ⊗[ℚ] C)ˣ × Rˣ)) : Set ((R ⊗[ℚ] C)ˣ × Rˣ)) =
        {x | ((x.1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C) * (starT star R ((x.1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C)).unop =
          algebraMap R (R ⊗[ℚ] C) ((x.2 : Rˣ) : R)} := rfl
    rw [hs]
    exact isClosed_eq ((Units.continuous_val.comp continuous_fst).mul (hσ.comp (Units.continuous_val.comp continuous_fst)))
      ((continuous_algebraMap R (R ⊗[ℚ] C)).comp (Units.continuous_val.comp continuous_snd))
  exact props_of_closedEmb hcl.isClosedEmbedding_subtypeVal

end UPts

end GlobalTheory.GfTop

namespace GlobalTheory.GfTop

open GlobalTheory.LKTrip IsDedekindDomain

section AfP

variable (p : ℕ)

theorem t2Space_afP : T2Space (AfP p) :=
  inferInstanceAs (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))

theorem finiteAdeleRingAway_locallyCompactSpace : LocallyCompactSpace (AfP p) :=
  (LevelExists.isCompact_intAfP p).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((LevelExists.isOpen_intAfP p).mem_nhds (LevelExists.intAfP p).zero_mem)

theorem finiteAdeleRingAway_totallyDisconnectedSpace : TotallyDisconnectedSpace (AfP p) :=
  td_of_inj (X := Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ])
    (f := fun x => (x : ∀ v : AwayP p, v.1.adicCompletion ℚ)) RestrictedProduct.continuous_coe
    (fun x y h => RestrictedProduct.ext _ _ fun i => congrFun h i)

theorem countable_awayP : Countable (AwayP p) := by
  have hI : Countable (Ideal ℤ) := by
    have hs : Function.Surjective (fun n : ℤ => Ideal.span {n}) := fun I =>
      ⟨Submodule.IsPrincipal.generator I, Ideal.span_singleton_generator I⟩
    exact hs.countable
  have hi : Function.Injective (fun v : AwayP p => v.1.asIdeal) := fun v w h =>
    Subtype.ext (HeightOneSpectrum.ext h)
  exact hi.countable

theorem compl_sc (v : HeightOneSpectrum ℤ) : SecondCountableTopology (v.adicCompletion ℚ) := by
  haveI : Fact ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isEmbedding.secondCountableTopology

theorem finiteAdeleRingAway_secondCountableTopology : SecondCountableTopology (AfP p) := by
  haveI := countable_awayP p
  haveI : ∀ v : AwayP p, SecondCountableTopology (v.1.adicCompletion ℚ) := fun v => compl_sc v.1
  have hAopen : ∀ v : AwayP p, IsOpen ((v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) :=
    fun v => Valued.isOpen_valuationSubring _
  have hS : ∀ S : Finset (AwayP p), Filter.cofinite ≤ Filter.principal ((S : Set (AwayP p))ᶜ) := fun S =>
    Filter.le_principal_iff.2 S.finite_toSet.compl_mem_cofinite
  let U : Finset (AwayP p) → Set (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]) :=
    fun S => Set.range (RestrictedProduct.inclusion (fun v : AwayP p => v.1.adicCompletion ℚ)
      (fun v : AwayP p => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) (hS S))
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hAopen (hS S)).isOpen_range
  have hsc : ∀ S, SecondCountableTopology (U S) := fun S => by
    haveI : SecondCountableTopology (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]_[
        Filter.principal ((S : Set (AwayP p))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (RestrictedProduct.isOpenEmbedding_inclusion_principal hAopen
      (hS S)).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hcov : ⋃ S, U S = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨(Filter.eventually_cofinite.1 x.2).toFinset, ?_⟩
    show x ∈ Set.range _
    rw [RestrictedProduct.range_inclusion]
    refine Filter.eventually_principal.2 fun i hi => ?_
    by_contra h
    exact hi (by rw [Finset.mem_coe, Set.Finite.mem_toFinset]; exact h)
  exact @TopologicalSpace.secondCountableTopology_of_countable_cover _ _ _ _ U hsc hUo hcov

end AfP

end GlobalTheory.GfTop
end
end

section

open GlobalTheory.Cong

noncomputable section

namespace GlobalTheory.Cong.OpPoly

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

def opHom (v : V) : (G →₀ ℂ) →+ V :=
  Finsupp.liftAddHom fun g => (smulAddHom ℂ V).flip (ρ g v)

theorem opHom_apply (v : V) (F : G →₀ ℂ) : opHom ρ v F = opOf ρ F v := by
  rw [opHom, Finsupp.liftAddHom_apply, opOf]
  exact Finsupp.sum_congr fun g _ => rfl

theorem opOf_single (g : G) (c : ℂ) (v : V) : opOf ρ (Finsupp.single g c) v = c • ρ g v := by
  simp [opOf, Finsupp.sum_single_index]

theorem opOf_add (F F' : G →₀ ℂ) (v : V) : opOf ρ (F + F') v = opOf ρ F v + opOf ρ F' v := by
  simp only [← opHom_apply, map_add (f := _)]

theorem opOf_smul (F : G →₀ ℂ) (c : ℂ) (v : V) : opOf ρ F (c • v) = c • opOf ρ F v := by
  simp [opOf, Finsupp.smul_sum, smul_comm c]

def conv (F f : G →₀ ℂ) : G →₀ ℂ :=
  F.sum fun g a => f.sum fun h b => Finsupp.single (g * h) (a * b)

theorem opOf_conv (F f : G →₀ ℂ) (v : V) : opOf ρ (conv F f) v = opOf ρ F (opOf ρ f v) := by
  rw [← opHom_apply]

  simp only [conv, Finsupp.sum, map_sum, opHom_apply, opOf_single]

  simp only [opOf, Finsupp.sum, map_sum, map_smul, Finset.smul_sum, mul_smul, map_mul, Module.End.mul_apply]

end GlobalTheory.Cong.OpPoly
end
end

section

open GlobalTheory.LatHecke

theorem _root_.GlobalTheory.T.generalLinear_transitive_on_lattices_over_DVR : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ), (∀ L : Lat O K r, ∃ g : GL (Fin r) K, glMap g (std O K r).1 = L.1) ∧ ∀ (g : GL (Fin r) K) (L : Lat O K r), (glMap g L.1).IsLattice K := by
  first | exact @GlobalTheory.LatHecke.gl_transitive_lattices | exact GlobalTheory.LatHecke.gl_transitive_lattices | (intros; apply GlobalTheory.LatHecke.gl_transitive_lattices <;> assumption)
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet Matrix

namespace GlobalTheory.GodementJacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLocallyConstant_char_det {n : Type} [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) :
    IsLocallyConstant fun g : GL n k => ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  set χ : GL n k →* ℂˣ := μ.comp GeneralLinearGroup.det with hχd
  have hχ : IsOpen (χ.ker : Set (GL n k)) := hμ.preimage GeneralLinearGroup.continuous_det
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set (GL n k)) ∈ nhds g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  have e : χ g = χ g0 := by
    have := congrArg (χ g0 * ·) hg'
    simp only [← map_mul, mul_inv_cancel_left, mul_one] at this
    exact this
  exact congrArg (fun u : ℂˣ => (u : ℂ)) e

end GlobalTheory.GodementJacquet
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.isEmpty_of_fibreFieldPointsCardLE_zero : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X), GlobalTheory.EtC.Tr.FibrePointsLE f 0 → IsEmpty Z := by
  first | (exact @GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero) | (exact GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero) | (intros; apply GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero  <;> assumption)
end
