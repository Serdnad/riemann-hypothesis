module

public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle181
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle023
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

namespace GlobalTheory.IdxAll

theorem eq_or_eq_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e τ : E →+* ℂ) (heτ : e.comp (algebraMap F E) = τ.comp (algebraMap F E)) :
    τ = e ∨ ∀ x, τ x = star (e x) := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨g, hg⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) e τ heτ
  have hσσ : ∀ x, σ (σ x) = x := fun x => e.injective (by rw [hσ, hσ, star_star])
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσσ) (AlgHom.ext hσσ)
  have hs : s ≠ 1 := by
    intro h1
    refine IsTotallyComplex.complexEmbedding_not_isReal e ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have : σ x = x := congrArg (fun t : E ≃ₐ[F] E => t x) h1
    have h3 := hσ e x
    rw [this] at h3
    exact h3.symm
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases hg1 : g.symm = 1
  · left
    rw [← hg, hg1]
    rfl
  · right
    intro x
    rw [← hg, (hy _ hg1).trans (hy _ hs).symm]
    exact hσ e x

end GlobalTheory.IdxAll
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_second_coordinate_of_orthogonal_selfDual : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    (∀ z, z ∈ Λ ↔ ∀ l ∈ Λ, ψ₀ (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1) →
    (∀ a ∈ v.adicCompletionIntegers F, ∀ l ∈ Λ, a • l ∈ Λ) →
    (∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F) →
    ∀ u : κ → Fv F v, (∀ y, ((0 : κ → Fv F v), y) ∈ Λ → ψ₀ (u ⬝ᵥ y) = 1) → ∃ y', (u, y') ∈ Λ := by
  first | exact @GlobalTheory.selfDual_exists_snd_of_orth | exact GlobalTheory.selfDual_exists_snd_of_orth | (intros; apply GlobalTheory.selfDual_exists_snd_of_orth <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.isHermitianNondegenerate_neg_traceZero_smul_inv_skewHermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E), (∀ i j, σ (J j i) = -J i j) → IsUnit J.det → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
    IsHermND σ (-ξ₀ • J⁻¹) := by
  first | exact @GlobalTheory.skew_dual_isHermND | exact GlobalTheory.skew_dual_isHermND | (intros; apply GlobalTheory.skew_dual_isHermND <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.exists_rational_projection_section_isotropicSpan : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ P Q : Matrix κ κ F,
      (∀ s ∈ S, (P.map (algebraMap F (AF F))) *ᵥ s.1 = 0) ∧
      (∀ s ∈ S, (s.1, (Q.map (algebraMap F (AF F))) *ᵥ s.1) ∈ S) ∧
      (∀ ξ : κ → F, P *ᵥ ξ = 0 →
        ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((Q *ᵥ ξ) i))) ∈ S) := by
  first | exact @GlobalTheory.rational_proj_section_of_span | exact GlobalTheory.rational_proj_section_of_span | (intros; apply GlobalTheory.rational_proj_section_of_span <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

open IsDedekindDomain HeightOneSpectrum WithZero

theorem locGen_val_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) :
    Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = v.intValuation d := by
  have h := valuedAdicCompletion_eq_valuation' (K := F) v (d : F)
  rw [← valuation_of_algebraMap (K := F) v d]
  exact h

theorem ideal_localGenerator : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), I ≠ ⊥ → ∃ z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v, z ≠ 0 ∧ (¬ I ≤ v.asIdeal → z = 1) ∧ (∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z) ∧ ∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z := by
  intro F _ _ I v hI
  by_cases hv : I ≤ v.asIdeal
  · classical
    have hex : ∃ n : ℕ, ∃ d ∈ I, v.intValuation d = exp (-(n : ℤ)) := by
      obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      exact ⟨_, d, hdI, v.intValuation_if_neg hd0⟩
    obtain ⟨d0, hd0I, hd0v⟩ := Nat.find_spec hex
    refine ⟨algebraMap F _ (d0 : F), ?_, fun h => absurd hv h, ?_, d0, hd0I, rfl⟩
    · intro h
      have h2 := locGen_val_eq F v d0
      rw [h, map_zero, hd0v] at h2
      exact exp_ne_zero h2.symm
    · intro d hd
      rw [locGen_val_eq, locGen_val_eq, hd0v]
      by_cases hd0 : d = 0
      · simp [hd0]
      · have hk := v.intValuation_if_neg hd0
        rw [hk, exp_le_exp, neg_le_neg_iff, Int.ofNat_le]
        exact Nat.find_min' hex ⟨d, hd, hk⟩
  · obtain ⟨d, hdI, hdv⟩ := Set.not_subset.mp hv
    refine ⟨1, one_ne_zero, fun _ => rfl, ?_, d, hdI, ?_⟩
    · intro e _
      rw [locGen_val_eq, map_one]
      exact v.intValuation_le_one e
    · rw [locGen_val_eq, map_one]
      exact intValuation_eq_one_iff.mpr hdv

end GlobalTheory
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory.CMConjInvol

theorem cm_conj_invol_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧ ∀ x, σ x = x → ∃ f : F, algebraMap F E f = x :=
  fun _ _ _ _ _ _ _ _ h => ⟨GlobalTheory.HermLineZeros.conj_invol h, GlobalTheory.HermLineZeros.exists_of_fixed h⟩

end GlobalTheory.CMConjInvol
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.IdeleCongr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intAE_mul {s t : FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hs : s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) (ht : t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : s * t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  first
  | exact @_root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem
  | exact _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem
  | (apply _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem ..)

theorem intAE_one : (1 : FiniteAdeleRing (𝓞 F) F ⊗[F] E) ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  refine AddSubgroup.subset_closure ⟨1, fun v => ?_, 1, ?_⟩
  · rw [map_one]; exact one_mem _
  · rw [Algebra.TensorProduct.one_def]; simp

theorem intAE_nat (m : ℕ) : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  rw [← nsmul_one]; exact nsmul_mem intAE_one m

theorem sigR_intAE (σ : E →ₐ[F] E) {z : FiniteAdeleRing (𝓞 F) F ⊗[F] E} (h : z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, RingOfIntegers.mapRingHom (σ : E →+* E) x, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_cA (σ : E →ₐ[F] E) (y : AdeleRing (𝓞 F) F ⊗[F] E) : HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.cA σ y) = HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ (HeckeCharacterZeroLocus.ThmBIn.finPart F E y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

end GlobalTheory.IdeleCongr

namespace GlobalTheory.IdeleCongr

theorem exists_open_congruence_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (m : ℕ), 0 < m → ∃ U : Subgroup (AdeleRing (𝓞 F) F ⊗[F] E)ˣ, IsOpen (U : Set (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) ∧
      (∀ x ∈ U, Units.map (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ).toRingHom.toMonoidHom x ∈ U) ∧
      ∀ x ∈ U, ∃ s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E,
        HeckeCharacterZeroLocus.ThmBIn.finPart F E (x : AdeleRing (𝓞 F) F ⊗[F] E) = 1 + (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * s := by
  intro F E _ _ _ _ _ σ m hm
  haveI : IsModuleTopology (HeckeCharacterZeroLocus.ThmBIn.AF F) (HeckeCharacterZeroLocus.ThmBIn.AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (HeckeCharacterZeroLocus.ThmBIn.AE F E) := IsModuleTopology.isTopologicalRing (HeckeCharacterZeroLocus.ThmBIn.AF F) _
  obtain ⟨Φ, hΦc, -, hint⟩ := GlobalTheory.HeckeInhabitant.exists_fin (F := F) (E := E)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  let c : FiniteAdeleRing (𝓞 F) F ⊗[F] E := HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹)
  have hmc : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * c = 1 := by
    have : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) = HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)) := by
      rw [map_natCast, map_natCast]
    rw [this, ← map_mul, ← map_mul, mul_inv_cancel₀ hm0, map_one, map_one]
  let C : AdeleRing (𝓞 F) F ⊗[F] E → Prop := fun y =>
    (HeckeCharacterZeroLocus.ThmBIn.finPart F E y - 1) * c ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E
  have hdec : ∀ z : FiniteAdeleRing (𝓞 F) F ⊗[F] E, z = 1 + m * ((z - 1) * c) := fun z => by
    linear_combination (1 - z) * hmc
  have hint' : ∀ y, C y → HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := fun y hy => by
    rw [hdec (HeckeCharacterZeroLocus.ThmBIn.finPart F E y)]
    exact add_mem intAE_one (intAE_mul (intAE_nat m) hy)
  have hCmul : ∀ y z, C y → C z → C (y * z) := fun y z hy hz => by
    have e : (HeckeCharacterZeroLocus.ThmBIn.finPart F E (y * z) - 1) * c = HeckeCharacterZeroLocus.ThmBIn.finPart F E y * ((HeckeCharacterZeroLocus.ThmBIn.finPart F E z - 1) * c)
        + (HeckeCharacterZeroLocus.ThmBIn.finPart F E y - 1) * c := by
      rw [map_mul]; ring
    show _ ∈ _
    rw [e]
    exact add_mem (intAE_mul (hint' y hy) hz) hy
  have hC1 : C 1 := by
    show _ ∈ _
    rw [map_one, sub_self, zero_mul]
    exact zero_mem _
  let U : Subgroup (AdeleRing (𝓞 F) F ⊗[F] E)ˣ :=
    { carrier := {x | C x ∧ C ((x⁻¹ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) : AdeleRing (𝓞 F) F ⊗[F] E)}
      one_mem' := ⟨by rw [Units.val_one]; exact hC1, by rw [inv_one, Units.val_one]; exact hC1⟩
      mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul]; exact hCmul _ _ hx.1 hy.1,
        by rw [mul_inv_rev, Units.val_mul]; exact hCmul _ _ hy.2 hx.2⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩ }
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hcont : Continuous fun y : AdeleRing (𝓞 F) F ⊗[F] E => (y - 1) * HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹ :=
    (continuous_id.sub continuous_const).mul continuous_const
  have hCo : IsOpen {y | C y} := by
    have h1 : IsOpen {y : AdeleRing (𝓞 F) F ⊗[F] E |
        ∀ P, Valued.v (Φ ((y - 1) * HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹) P) ≤ 1} := (hO.preimage hΦc).preimage hcont
    convert h1 using 1
    ext y
    simp only [Set.mem_setOf_eq]
    rw [← hint, map_mul, map_sub, map_one]
  have hσ : ∀ y, (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) y
      = HeckeCharacterZeroLocus.ThmBIn.cA σ y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a x => rfl
  have hsc : HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ c = c := by
    change HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ (HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹)) = _
    rw [← finPart_cA, GlobalTheory.HeckeInhabitant.cA_inc, map_inv₀, map_natCast]
  have hCσ : ∀ y, C y → C (HeckeCharacterZeroLocus.ThmBIn.cA σ y) := fun y hy => by
    show _ ∈ _
    rw [finPart_cA, ← hsc, ← map_one (HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ), ← map_sub, ← map_mul]
    exact sigR_intAE σ hy
  refine ⟨U, ?_, fun x hx => ⟨?_, ?_⟩, fun x hx => ⟨_, hx.1, hdec _⟩⟩
  · exact (hCo.preimage Units.continuous_val).inter (hCo.preimage Units.continuous_coe_inv)
  · change C ((Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) (x : AdeleRing (𝓞 F) F ⊗[F] E))
    rw [hσ]; exact hCσ _ hx.1
  · rw [← map_inv]
    change C ((Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) ((x⁻¹ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) : AdeleRing (𝓞 F) F ⊗[F] E))
    rw [hσ]; exact hCσ _ hx.2

end GlobalTheory.IdeleCongr
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped nonZeroDivisors

namespace GlobalTheory.UnrTraceDual

theorem traceDual_ringOfIntegers_iff_of_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔ ∀ d ∈ differentIdeal ℤ (𝓞 F), IsIntegral ℤ (algebraMap F E (d : F) * e) := by
  intro F E _ _ _ _ _ hU e
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := inferInstance
  have hEq : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
      (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu, Ideal.top_mul]
  have hint : ∀ x : E, IsIntegral ℤ x ↔ x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    intro x
    rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]
  have h1 : (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔
      e ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
    constructor
    · intro h a ha
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 ha
      rw [Algebra.traceForm_apply, mul_comm]
      exact RingHom.mem_range.2 (IsIntegrallyClosed.isIntegral_iff.1 (h o))
    · intro h o
      have := h (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff (𝓞 E)⁰).2 ⟨o, rfl⟩)
      rw [Algebra.traceForm_apply, mul_comm] at this
      exact IsIntegrallyClosed.isIntegral_iff.2 (RingHom.mem_range.1 this)
  have h2 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  have hne : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  rw [h1, h2, FractionalIdeal.mem_inv_iff hne, hEq]
  let J : Ideal (𝓞 E) :=
    { carrier := {x | IsIntegral ℤ (algebraMap (𝓞 E) E x * e)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add (f := _), add_mul] at *
        exact ha.add hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero, zero_mul]
        exact isIntegral_zero
      smul_mem' := by
        intro c x hx
        have hx' : IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := hx
        have hc : IsIntegral ℤ (algebraMap (𝓞 E) E c) := RingOfIntegers.isIntegral_coe c
        show IsIntegral ℤ (algebraMap (𝓞 E) E (c * x) * e)
        rw [map_mul, mul_assoc]
        exact IsIntegral.mul hc hx' }
  have hJ : ∀ x : 𝓞 E, x ∈ J ↔ IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := fun _ => Iff.rfl
  have hL : (∀ y ∈ (((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) : Ideal (𝓞 E)) :
      FractionalIdeal (𝓞 E)⁰ E), e * y ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔
      (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) ≤ J := by
    constructor
    · intro h x hx
      rw [hJ, hint, mul_comm]
      exact h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hx)
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
      rw [mul_comm, ← hint]
      exact (hJ x).1 (h hx)
  rw [hL, Ideal.map_le_iff_le_comap]
  constructor
  · intro h d hd
    have := (hJ _).1 (h hd)
    rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
  · intro h d hd
    show algebraMap (𝓞 F) (𝓞 E) d ∈ J
    rw [hJ, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    exact h d hd

end GlobalTheory.UnrTraceDual
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Pointwise

namespace GlobalTheory

theorem ideal_map_smul_isLattice (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)) :
    I ≠ ⊥ → Submodule.IsLattice E L →
      Submodule.IsLattice E (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) := by
  intro hI hL
  have hle : I.map (algebraMap (𝓞 F) (𝓞 E)) • L ≤ L := Submodule.smul_le_right
  obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hdE : ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) ≠ 0 := by
    intro h
    apply hd0
    have h1 : algebraMap (𝓞 F) (𝓞 E) d = 0 := by exact_mod_cast h
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)) (by simpa using h1)
  set u : Eˣ := Units.mk0 _ hdE
  have hsub : (u • L : Submodule (𝓞 E) (Fin n → E)) ≤ I.map (algebraMap (𝓞 F) (𝓞 E)) • L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have : (u • y : Fin n → E) = (algebraMap (𝓞 F) (𝓞 E) d) • y := by
      rw [Units.smul_def, Units.val_mk0, ← algebraMap_smul E (algebraMap (𝓞 F) (𝓞 E) d) y]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hdI) hy
  exact Submodule.IsLattice.of_fg E (Submodule.FG.of_le hL.fg hle)

end GlobalTheory
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.injective_of_map_pderiv_eq_and_map_one_ne_zero : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (Φ₀ : MvPolynomial ι ℂ →ₗ[ℂ] V)
    (d : ι → Module.End ℂ V), (∀ (i : ι) (p : MvPolynomial ι ℂ), Φ₀ (MvPolynomial.pderiv i p) = d i (Φ₀ p)) →
    Φ₀ 1 ≠ 0 → Function.Injective Φ₀ := by
  first | exact @GlobalTheory.FockAlg.injective_of_pderiv | exact GlobalTheory.FockAlg.injective_of_pderiv | (intros; apply GlobalTheory.FockAlg.injective_of_pderiv <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.finite_coheight_one_notMem_of_genericPoint_mem : ∀ (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (U : X.Opens), genericPoint X ∈ U → {z : X | Order.coheight z = 1 ∧ z ∉ U}.Finite := by
  first | exact @GlobalTheory.Mix.finite_coheight_one_notMem_open | exact GlobalTheory.Mix.finite_coheight_one_notMem_open | (intros; apply GlobalTheory.Mix.finite_coheight_one_notMem_open <;> assumption)
end
