module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle055
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle606
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterAdelicGLEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothVecHeadOfDerivativeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.RayPrincipalIdeals
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle607
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem matrices_bounded_denominator_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsTotallyReal F → ∀ {ι : Type} [Finite ι] (d : ℕ) (B : ℝ), 0 < d → {N : Matrix ι ι E | (∀ u v, IsIntegral ℤ ((d : E) * N u v)) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : ι), ‖τ.1 (N u v)‖ ≤ B}.Finite := by
  intro F E _ _ _ _ _ hF ι _ d B hd
  haveI := hF
  have hS : {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ) * B}.Finite :=
    Embeddings.finite_of_norm_le E ℂ _
  have hd0 : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hT := hS.preimage (f := fun e : E => (d : E) * e)
    (fun a _ b _ h => mul_left_cancel₀ hd0 h)
  have hM := Set.Finite.pi' (fun _ : ι => Set.Finite.pi' (fun _ : ι => hT))
  refine hM.subset ?_
  rintro N ⟨h1, h2⟩ u v
  refine ⟨h1 u v, fun φ => ?_⟩
  have hr : ComplexEmbedding.IsReal (φ.comp (algebraMap F E)) :=
    IsTotallyReal.complexEmbedding_isReal _
  have hb := h2 (InfinitePlace.mk (φ.comp (algebraMap F E)))
    ⟨φ, (InfinitePlace.embedding_mk_eq_of_isReal hr).symm⟩ u v
  rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg d)

end GlobalTheory.CompanionTheory.CFin
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_ratEmb_eq_of_mem_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J), g ∈ ratPts σ J → ∃ η : GRat σ J, g = ratEmb σ J η := by
  intro F E _ _ _ _ _ σ n J g hg
  rw [← range_ratEmb σ J] at hg
  obtain ⟨η, rfl⟩ := hg
  exact ⟨η, rfl⟩

end GlobalTheory.CompanionTheory.CFin
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * x) :=
  _root_.UpperTheory.Reformulated.B.DYha3.main x

theorem exists_nat_mul_isIntegral_of_isCompact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {𝒦 : Set (Af F ⊗[F] E)} (h𝒦 : IsCompact 𝒦) :
    ∃ d : ℕ, 0 < d ∧ ∀ e : E, inclR (F := F) (Af F) e ∈ 𝒦 → IsIntegral ℤ ((d : E) * e) := by
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let bb := Algebra.TensorProduct.basis (Af F) b
  have hc : ∀ i, Continuous (fun x : Af F ⊗[F] E => bb.coord i x) := fun i =>
    IsModuleTopology.continuous_of_linearMap (bb.coord i)
  have hcoord : ∀ (e : E) i, bb.coord i (inclR (F := F) (Af F) e) = algebraMap F (Af F) (b.repr e i) := by
    intro e i
    change bb.repr ((1 : Af F) ⊗ₜ[F] e) i = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp [Algebra.algebraMap_eq_smul_one]
  choose m hm hmi using fun i =>
    GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_integral_of_isCompact F (h𝒦.image (hc i))
  choose D hD hDi using fun i => exists_nat_mul_isIntegral (b i)
  refine ⟨(∏ i, m i) * ∏ i, D i, Nat.mul_pos (Finset.prod_pos fun i _ => hm i)
    (Finset.prod_pos fun i _ => hD i), fun e he => ?_⟩
  have hsum : ((((∏ i, m i) * ∏ i, D i : ℕ)) : E) * e =
      ∑ i, algebraMap F E (((∏ i, m i : ℕ) : F) * b.repr e i) * (((∏ i, D i : ℕ)) : E) * b i := by
    conv_lhs => rw [← b.sum_repr e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [hsum]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  obtain ⟨z, hz⟩ := hmi i (b.repr e i) ⟨_, he, hcoord e i⟩
  have h1 : IsIntegral ℤ (algebraMap F E (((∏ i, m i : ℕ) : F) * b.repr e i)) := by
    have : ((∏ i, m i : ℕ) : F) * b.repr e i = (q : F) * (z : F) := by
      rw [hq, hz, Nat.cast_mul]
      ring
    rw [this]
    exact IsIntegral.algebraMap ((isIntegral_natCast q).mul z.2)
  have h2 : (((∏ i, D i : ℕ)) : E) * b i = (r : E) * ((D i : E) * b i) := by
    rw [hr, Nat.cast_mul]
    ring
  rw [mul_assoc, h2]
  exact h1.mul ((isIntegral_natCast r).mul (hDi i))

end GlobalTheory.CompanionTheory.CFin

namespace GlobalTheory.CompanionTheory.CFin

theorem bounded_denominators : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (𝒞 : Set (GFin σ J)), IsCompact 𝒞 → ∀ {ι : Type} [Fintype ι] (A : Matrix ι (Fin n) E) (B : Matrix (Fin n) ι E), ∃ d : ℕ, 0 < d ∧ ∀ δ : GRat σ J, projFin σ J (ratEmb σ J δ) ∈ 𝒞 → ∀ u v, IsIntegral ℤ ((d : E) * (A * δ.1.1 * B) u v) := by
  intro F E _ _ _ _ _ σ n J 𝒞 h𝒞 ι _ A B
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  let f : ι → ι → GFin σ J → Af F ⊗[F] E := fun u v y =>
    (A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J y).1 * B.map (inclR (F := F) (Af F))) u v
  have hmat : Continuous fun y : GFin σ J => ((matHom (Af F) σ J y).1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    Units.continuous_val.comp (GlobalTheory.AdelicU.isEmbedding_matHom (Af F) σ J).continuous
  have hf : ∀ u v, Continuous (f u v) := fun u v => by
    have : Continuous fun y : GFin σ J =>
        A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J y).1 * B.map (inclR (F := F) (Af F)) :=
      (continuous_const.matrix_mul hmat).matrix_mul continuous_const
    exact this.matrix_elem u v
  obtain ⟨d, hd, h⟩ := exists_nat_mul_isIntegral_of_isCompact F E
    (𝒦 := ⋃ u, ⋃ v, f u v '' 𝒞)
    (isCompact_iUnion fun u => isCompact_iUnion fun v => h𝒞.image (hf u v))
  refine ⟨d, hd, fun δ hδ u v => h _ ?_⟩
  refine Set.mem_iUnion.2 ⟨u, Set.mem_iUnion.2 ⟨v, _, hδ, ?_⟩⟩
  have hval : ((matHom (Af F) σ J (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J δ))).1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) =
      δ.1.1.map (inclR (F := F) (Af F)) := by
    refine Matrix.ext fun r s => ?_
    change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (δ.1.1 r s)) =
      (1 : Af F) ⊗ₜ[F] (δ.1.1 r s)
    simp
  change (A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J δ))).1 *
    B.map (inclR (F := F) (Af F))) u v = _
  rw [hval, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

end GlobalTheory.CompanionTheory.CFin

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.DegOneRay

variable {F : Type} [Field F] [NumberField F]

theorem finite_realEmb : Finite (F →+* ℝ) :=
  Finite.of_injective (fun σ : F →+* ℝ => (Complex.ofRealHom.comp σ : F →+* ℂ)) fun σ τ h => by
    ext x
    exact Complex.ofReal_injective (congrArg (fun f : F →+* ℂ => f x) h)

theorem exists_totPos_inv {𝔣 : Ideal (𝓞 F)} (hf : 𝔣 ≠ ⊥) {u : 𝓞 F} (hu : IsCoprime (Ideal.span {u}) 𝔣) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ d * u - 1 ∈ 𝔣 ∧ ∀ σ : F →+* ℝ, 0 < σ (d : F) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hu
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  have hc : c * u - 1 ∈ 𝔣 := by
    have : c * u - 1 = -j := by rw [← hij]; ring
    rw [this]; exact 𝔣.neg_mem hj
  set N : ℕ := Ideal.absNorm 𝔣 with hN
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by simpa [hN, Ideal.absNorm_eq_zero_iff] using hf)
  have hNm : ((N : ℕ) : 𝓞 F) ∈ 𝔣 := Ideal.absNorm_mem 𝔣
  have : Finite (F →+* ℝ) := finite_realEmb
  obtain ⟨b, hb⟩ := (Set.finite_range fun σ : F →+* ℝ => -σ (c : F)).bddAbove
  obtain ⟨M, hM⟩ := exists_nat_gt b
  have key : ∀ m : ℕ, M ≤ m → ((c + (m : 𝓞 F) * (N : 𝓞 F)) * u - 1 ∈ 𝔣 ∧
      ∀ σ : F →+* ℝ, 0 < σ ((c + (m : 𝓞 F) * (N : 𝓞 F) : 𝓞 F) : F)) := by
    intro m hm
    refine ⟨?_, fun σ => ?_⟩
    · have : (c + (m : 𝓞 F) * (N : 𝓞 F)) * u - 1 = (c * u - 1) + (N : 𝓞 F) * ((m : 𝓞 F) * u) := by ring
      rw [this]
      exact 𝔣.add_mem hc (𝔣.mul_mem_right _ hNm)
    · have h1 : -σ (c : F) ≤ b := hb ⟨σ, rfl⟩
      have h2 : (M : ℝ) ≤ m := by exact_mod_cast hm
      have h3 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have e : σ ((c + (m : 𝓞 F) * (N : 𝓞 F) : 𝓞 F) : F) = σ (c : F) + (m : ℝ) * (N : ℝ) := by
        push_cast
        simp
      rw [e]
      nlinarith
  by_cases h0 : c + (M : 𝓞 F) * (N : 𝓞 F) = 0
  · refine ⟨c + ((M + 1 : ℕ) : 𝓞 F) * (N : 𝓞 F), ?_, (key _ (Nat.le_succ M)).1, (key _ (Nat.le_succ M)).2⟩
    have : c + ((M + 1 : ℕ) : 𝓞 F) * (N : 𝓞 F) = (N : 𝓞 F) := by
      push_cast
      linear_combination h0
    rw [this]
    exact_mod_cast hN0.ne'
  · exact ⟨_, h0, (key M le_rfl).1, (key M le_rfl).2⟩

theorem rayRel_of_rayPair {𝔣 𝔠 𝔞 : Ideal (𝓞 F)} (hf : 𝔣 ≠ ⊥) {α β : 𝓞 F} (hr : GlobalTheory.NT.RayPair 𝔣 α β)
    (h : Ideal.span {β} * 𝔠 = Ideal.span {α} * 𝔞) : RayRel F 𝔣 𝔠 𝔞 := by
  obtain ⟨ha, hb, ha', hb', hab, hpos⟩ := hr
  have hb2 : IsCoprime (Ideal.span {β * β}) 𝔣 := by
    rw [← Ideal.span_singleton_mul_span_singleton]; exact hb'.mul_left hb'
  obtain ⟨d, hd0, hd, hdp⟩ := exists_totPos_inv hf hb2
  refine ⟨d * (β * β), d * (α * β), mul_ne_zero hd0 (mul_ne_zero hb hb),
    mul_ne_zero hd0 (mul_ne_zero ha hb), hd, ?_, fun σ => ?_, ?_⟩
  · have : d * (α * β) - 1 = (d * β) * (α - β) + (d * (β * β) - 1) := by ring
    rw [this]
    exact 𝔣.add_mem (𝔣.mul_mem_left _ hab) hd
  · have hbK : (β : F) ≠ 0 := by exact_mod_cast hb
    have hσb : σ (β : F) ≠ 0 := (map_ne_zero σ).2 hbK
    have e1 : σ ((d * (β * β) : 𝓞 F) : F) = σ (d : F) * (σ (β : F) * σ (β : F)) := by
      push_cast; simp
    have e2 : σ ((d * (α * β) : 𝓞 F) : F) = σ (d : F) * (σ (α : F) * σ (β : F)) := by
      push_cast; simp
    rw [e1, e2]
    exact ⟨mul_pos (hdp σ) (mul_self_pos.2 hσb), mul_pos (hdp σ) (hpos σ)⟩
  · calc Ideal.span {d * (β * β)} * 𝔠 = Ideal.span {d * β} * (Ideal.span {β} * 𝔠) := by
          rw [← mul_assoc (Ideal.span {d * β}), Ideal.span_singleton_mul_span_singleton, mul_assoc d]
      _ = Ideal.span {d * β} * (Ideal.span {α} * 𝔞) := by rw [h]
      _ = Ideal.span {d * (α * β)} * 𝔞 := by
          rw [← mul_assoc (Ideal.span {d * β}), Ideal.span_singleton_mul_span_singleton,
            show d * β * α = d * (α * β) by ring]

theorem finite_excluded (𝔣 : Ideal (𝓞 F)) (hf : 𝔣 ≠ ⊥) (W : Finset (𝓞 F)) (B : ℕ) (hW : ∀ x ∈ W, x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ 𝔣 ∨ Ideal.absNorm v.asIdeal ≤ B ∨ ∃ x ∈ W, x ∈ v.asIdeal}.Finite := by
  have h1 : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ 𝔣}.Finite := Ideal.finite_factors hf
  have h2 : {v : HeightOneSpectrum (𝓞 F) | Ideal.absNorm v.asIdeal ≤ B}.Finite := by
    have h : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ B}.Finite := by
      have : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ B} =
          ⋃ n ∈ Finset.range (B + 1), {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
        ext I; simp [Nat.lt_succ_iff]
      rw [this]
      exact Set.Finite.biUnion (Finset.finite_toSet _) fun n _ => Ideal.finite_setOfPred_absNorm_eq n
    exact (h.preimage (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
      (fun v _ w _ e => HeightOneSpectrum.ext e))
  have h3 : {v : HeightOneSpectrum (𝓞 F) | ∃ x ∈ W, x ∈ v.asIdeal}.Finite := by
    have : {v : HeightOneSpectrum (𝓞 F) | ∃ x ∈ W, x ∈ v.asIdeal} =
        ⋃ x ∈ W, {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {x}} := by
      ext v
      simp [Ideal.dvd_span_singleton]
    rw [this]
    refine Set.Finite.biUnion W.finite_toSet fun x hx => Ideal.finite_factors ?_
    simpa using hW x hx
  exact (h1.union (h2.union h3)).subset fun v hv => by
    rcases hv with h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]

theorem exists_degree_one_frobenius_prime {Ω : Type} [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω)
    [FiniteDimensional F L] [IsGalois F L] (g : L ≃ₐ[F] L) (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g := by
  obtain ⟨v, hv, hd, A, hA, -, σ, hσ, hg⟩ := GlobalTheory.Published.chebotarevDegreeOne' F Ω L g S hS
  refine ⟨v, hv, hd, ?_⟩
  have h := GlobalTheory.RayFromArtin.isFrob_restrict (K := F) (Ω := Ω) L hA hσ
  rwa [hg] at h

theorem exists_degOne_isFrob_of_closure (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {L : Type} [Field L]
    [NumberField L] [Algebra F L] [IsGalois F L] (g : L ≃ₐ[F] L) (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : FiniteDimensional F L := Module.Finite.of_restrictScalars_finite ℚ F L
  let i : L →ₐ[F] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : L ≃ₐ[F] i.fieldRange := AlgEquiv.ofInjectiveField i
  have : IsGalois F i.fieldRange := IsGalois.of_algEquiv e
  have : FiniteDimensional F i.fieldRange := e.toLinearEquiv.finiteDimensional
  obtain ⟨v, hv, hd, h⟩ := exists_degree_one_frobenius_prime i.fieldRange (e.autCongr g) S hS
  exact ⟨v, hv, hd, (GlobalTheory.Mem.Fld.isFrob_congr e v g).1 h⟩

theorem exists_degOne_isFrob {L : Type} [Field L] [NumberField L] [Algebra F L] [IsGalois F L] (g : L ≃ₐ[F] L)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g :=
  exists_degOne_isFrob_of_closure (AlgebraicClosure F) g S hS

theorem exists_degOne_prime_in_rayClass : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    CoprimeTo F 𝔣 𝔞 → ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) →
    ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ CoprimeTo F 𝔣 𝔠 ∧
      RayRel F 𝔣 𝔠 𝔞 ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  intro F _ _ 𝔣 𝔞 hf ha W B hW
  obtain ⟨ha0, hac⟩ := ha
  obtain ⟨L, _, _, _, hab, Art, hArt⟩ := (GlobalTheory.Published.rayClassFieldSt_iff_artinIso.1
    (GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt GlobalTheory.CompanionTheory.Hypotheses₂.globalArtinReciprocity)) F 𝔣 hf
  have hc : IsCoprime 𝔞 𝔣 := Ideal.isCoprime_iff_sup_eq.2 hac
  obtain ⟨J, hJ⟩ := GlobalTheory.RayFieldCompare.exists_integral 𝔣 𝔞 ha0 hc
  obtain ⟨v, hv, hd, hfr⟩ := exists_degOne_isFrob (Art (QuotientGroup.mk J)) _ (finite_excluded 𝔣 hf W B hW)
  simp only [Set.mem_setOf_eq, not_or, not_exists, not_and] at hv
  obtain ⟨hv1, hv2, hv3⟩ := hv
  have heq : (QuotientGroup.mk J : GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.RayClassGroup 𝔣) = GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeClass 𝔣 v hv1 :=
    Art.injective (GlobalTheory.RayFieldCompare.isFrob_unique L (hArt v hv1).1 hfr (hArt v hv1).2)
  obtain ⟨x, ⟨α, β, hr, hx⟩, hxJ⟩ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 heq)
  have e1 : J.1 * toPrincipalIdeal (𝓞 F) F x = (GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeElt 𝔣 v hv1).1 := by
    rw [hxJ, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have e2 : (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) =
      (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) := by
    have h := congrArg Units.val e1
    rw [Units.val_mul, hJ, coe_toPrincipalIdeal] at h
    exact h
  have hα : FractionalIdeal.spanSingleton (𝓞 F)⁰ ((α : 𝓞 F) : F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) * FractionalIdeal.spanSingleton (𝓞 F)⁰ ((β : 𝓞 F) : F) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hx]
  have e3 : Ideal.span {β} * v.asIdeal = Ideal.span {α} * 𝔞 := by
    refine FractionalIdeal.coeIdeal_injective (K := F) ?_
    change ((Ideal.span {β} * v.asIdeal : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      ((Ideal.span {α} * 𝔞 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, ← e2]
    change FractionalIdeal.spanSingleton (𝓞 F)⁰ ((β : 𝓞 F) : F) * _ =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ((α : 𝓞 F) : F) * _
    rw [hα]
    ring
  refine ⟨v.asIdeal, v.isPrime, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd,
    not_le.1 hv2, ⟨v.ne_bot, ?_⟩, rayRel_of_rayPair hf hr e3, fun y hy hy' => hv3 y hy hy'⟩
  by_contra hne
  exact hv1 (Ideal.dvd_iff_le.2 ((v.isMaximal.eq_of_le hne le_sup_left).symm ▸ le_sup_right))

end GlobalTheory.CompanionTheory.DegOneRay
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.finite_nonsplit_sign_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E) (H₀ : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ P₁ : E[X], {w : Pl E | ¬ IsSplitAt w ∧ sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E))) ≠ 1}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.FinSign.main | exact GlobalTheory.CompanionTheory.FinSign.main | (intros; apply GlobalTheory.CompanionTheory.FinSign.main <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.modularCharacter_adelic_GL_eq_one : ∀ (D : D7) (r : ℕ) [LocallyCompactSpace (GL (Fin r) (AE D))] (a : GL (Fin r) (AE D)), Measure.modularCharacterFun a = 1 := by
  first | exact @GlobalTheory.CompanionTheory.GLUnimod.modularCharacterFun_GL_adele | exact GlobalTheory.CompanionTheory.GLUnimod.modularCharacterFun_GL_adele | (intros; apply GlobalTheory.CompanionTheory.GLUnimod.modularCharacterFun_GL_adele <;> assumption)
end

section

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix MeasureTheory GlobalTheory.SmoothGlob Filter
open GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped Topology

namespace GlobalTheory.CompanionTheory.SobComplete

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Dw_sub_of_sm {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H} (hx : Sm ε σ x) (hy : Sm ε σ y) :
    Dw σ l (x - y) = Dw σ l x - Dw σ l y := by
  have hxy : Sm ε σ (x - y) := sm_iff.2 (Submodule.sub_mem _ (sm_iff.1 hx) (sm_iff.1 hy))
  have h := Dw_add hσ hl hxy hy
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem tendsto_sobNorm_zero {σ : Mx n → (H →L[ℂ] H)} {u : ℕ → H} (S : List (List (Mx n)))
    (h : ∀ l ∈ S, Tendsto (fun k => ‖l.foldr (dRep σ) (u k)‖) atTop (𝓝 0)) :
    Tendsto (fun k => sobNorm σ S (u k)) atTop (𝓝 0) := by
  induction S with
  | nil => simpa [sobNorm] using tendsto_const_nhds
  | cons l S ih =>
    have h1 := h l List.mem_cons_self
    have h2 := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr fun k => ?_
    simp [sobNorm]

theorem smoothVec_complete_of_unitary (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : IsURepOn (UJset ε) σ) (w : ℕ → H) (hw : ∀ k, SmoothVec (lieSet ε) σ (w k))
    (hC : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∀ δ > 0,
      ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ) :
    ∃ w₀, SmoothVec (lieSet ε) σ w₀ ∧ ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)),
      (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → Tendsto (fun k => sobNorm σ S (w k - w₀)) atTop (𝓝 0) := by
  have hρ : ModRep ε σ := GlobalTheory.FamSmooth.modRep_of_isURepOn hσ
  have hmem : ∀ l : List (lie (Jm ε)), ∀ X ∈ l.map Subtype.val, X ∈ lieSet ε := fun l X hX => by
    obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
    exact Y.2
  let U : ℕ → List (lie (Jm ε)) → H := fun k l => Dw σ (l.map Subtype.val) (w k)
  have hU : ∀ k, U k ∈ Fam ε σ := fun k => GlobalTheory.SobUnif.smooth_fam hσ (hw k)
  have hcau : ∀ l, CauchySeq fun k => U k l := fun l => by
    refine Metric.cauchySeq_iff.2 fun δ hδ => ?_
    obtain ⟨K, hK⟩ := hC [l.map Subtype.val] (by simpa using hmem l) δ hδ
    refine ⟨K, fun k hk m hm => ?_⟩
    rw [dist_eq_norm]
    show ‖Dw σ (l.map Subtype.val) (w k) - Dw σ (l.map Subtype.val) (w m)‖ < δ
    rw [← Dw_sub_of_sm hσ (hmem l) (hw k) (hw m)]
    exact (norm_Dw_le_sobNorm σ List.mem_cons_self _).trans_lt (hK k hk m hm)
  choose v hv using fun l => cauchySeq_tendsto_of_complete (hcau l)
  have hvF : v ∈ Fam ε σ :=
    (GlobalTheory.T.isClosed_derivativeFamilies_moderateGrowth n ε H σ hρ).mem_of_tendsto (tendsto_pi_nhds.2 hv) (Eventually.of_forall hU)
  obtain ⟨hs, hd⟩ := GlobalTheory.SobUnif.fam_smooth hσ hvF
  refine ⟨v [], hs, fun S hS => tendsto_sobNorm_zero S fun l hl => ?_⟩
  obtain ⟨l', rfl⟩ := GlobalTheory.SobUnif.exists_lift l (hS l hl)
  have h1 : Tendsto (fun k => U k l' - v l') atTop (𝓝 0) := by
    simpa using (hv l').sub_const (v l')
  have h2 := h1.norm
  rw [norm_zero] at h2
  refine h2.congr fun k => ?_
  show ‖Dw σ (l'.map Subtype.val) (w k) - v l'‖ = ‖Dw σ (l'.map Subtype.val) (w k - v [])‖
  rw [Dw_sub_of_sm hσ (hmem l') (hw k) hs, hd l']

theorem smoothVec_complete : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ w : ℕ → H, (∀ k, SmoothVec (lieSet ε) σ (w k)) → (∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∀ δ > 0, ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ) → ∃ w₀, SmoothVec (lieSet ε) σ w₀ ∧ ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → Filter.Tendsto (fun k => sobNorm σ S (w k - w₀)) Filter.atTop (nhds 0) :=
  fun n ε H _ _ _ σ hσ _ w hw hC => smoothVec_complete_of_unitary n ε H σ hσ w hw hC

end GlobalTheory.CompanionTheory.SobComplete

end
end
