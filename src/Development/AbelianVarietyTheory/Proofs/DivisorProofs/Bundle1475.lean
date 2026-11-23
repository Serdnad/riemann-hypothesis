module

public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle295
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NormDichotomy

theorem unit_or_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) ∨ (∀ k : K, k ≠ 0 → ∃ t : K ⊗[F] E, t * sigR K σ t = algebraMap K (K ⊗[F] E) k) := by
  intro F E _ _ _ _ _ σ h K _ _

  obtain ⟨e, he⟩ := GlobalTheory.HermLineZeros.exists_conj_ne h
  set d : E := e - σ e with hd
  have hσd : σ d = -d := by
    rw [hd, map_sub, GlobalTheory.HermLineZeros.conj_invol h]; ring
  have hd0 : d ≠ 0 := by
    intro h0; apply he; rw [hd, sub_eq_zero] at h0; exact h0.symm
  have hfix : σ (d * d) = d * d := by rw [map_mul, hσd]; ring
  obtain ⟨c0, hc0⟩ := GlobalTheory.HermLineZeros.exists_of_fixed h _ hfix
  haveI : CharZero F := inferInstance
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  set L := K ⊗[F] E
  set ι := algebraMap K L with hι
  set D : L := inclR K d with hD
  set c : K := algebraMap F K c0 with hc
  have hc0ne : c0 ≠ 0 := by
    rintro rfl; apply hd0; rw [map_zero] at hc0; exact mul_self_eq_zero.1 hc0.symm
  have hcne : c ≠ 0 := by rw [hc]; exact (map_ne_zero _).2 hc0ne
  have hDD : D * D = ι c := by
    rw [hD, ← map_mul, ← hc0, hc, hι, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).commutes c0
  have hsD : sigR K σ D = -D := by
    show inclR K (σ d) = _
    rw [hσd, map_neg]
  have hst : ∀ t : K, sigR K σ (ι t) = ι t := by
    intro t
    show t ⊗ₜ[F] σ 1 = _
    rw [map_one]
    rfl

  have hli : LinearIndependent F ![(1 : E), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst0
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst0
    have e2 := congrArg σ hst0
    rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσd, map_zero] at e2
    have ht : algebraMap F E t * d = 0 := by linear_combination (hst0 - e2) / 2
    have ht0 : t = 0 := by
      rcases mul_eq_zero.1 ht with h1 | h1
      · exact (map_eq_zero _).1 h1
      · exact absurd h1 hd0
    refine ⟨?_, ht0⟩
    rw [ht0, map_zero, zero_mul, add_zero] at hst0
    exact (map_eq_zero _).1 hst0
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  let bK := Algebra.TensorProduct.basis K b
  have hdec : ∀ a : L, ∃ u v : K, a = ι u + ι v * D := by
    intro a
    refine ⟨bK.repr a 0, bK.repr a 1, ?_⟩
    conv_lhs => rw [← bK.sum_repr a]
    rw [Fin.sum_univ_two]
    have hb : ⇑b = ![(1 : E), d] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    have h0 : bK 0 = 1 := by
      simp only [bK, Algebra.TensorProduct.basis_apply, hb, Matrix.cons_val_zero]; rfl
    have h1 : bK 1 = D := by
      simp only [bK, Algebra.TensorProduct.basis_apply, hb, Matrix.cons_val_one, Matrix.head_cons]; rfl
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]
  by_cases hsq : ∃ r : K, r * r = c
  · right
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by rintro rfl; exact hcne (by rw [← hr, mul_zero])
    have h2 : ι (1 / 2) * 2 = 1 := by
      rw [show (2 : L) = ι 2 from (map_ofNat ι 2).symm, ← map_mul]; norm_num
    have hs : ι r * ι r⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hr0, map_one]
    have hD2 : D * D = ι r * ι r := by rw [hDD, ← hr, map_mul]
    set ε : L := ι (1 / 2) * (1 + ι r⁻¹ * D) with hε
    have he0 : ε * (1 - ε) = 0 := by
      rw [hε]
      linear_combination (-(1 + ι r⁻¹ * D) * ι (1 / 2)) * h2 + (-ι (1 / 2) ^ 2 * ι r⁻¹ ^ 2) * hD2 + (-ι (1 / 2) ^ 2 * (ι r⁻¹ * ι r + 1)) * hs
    have hσε : sigR K σ ε = 1 - ε := by
      rw [hε, map_mul, map_add (f := _), map_mul, map_one, hst, hst, hsD]
      linear_combination h2
    intro k _
    refine ⟨ι k * ε + (1 - ε), ?_⟩
    rw [map_add (f := _), map_mul, map_sub, map_one, hst, hσε]
    linear_combination (ι k ^ 2 + 1 - 2 * ι k) * he0
  · left
    push_neg at hsq
    intro a ha
    obtain ⟨u, v, rfl⟩ := hdec a
    have hn : u * u - c * (v * v) ≠ 0 := by
      intro h0
      by_cases hv : v = 0
      · apply ha
        have : u * u = 0 := by rw [hv] at h0; simpa using h0
        rw [mul_self_eq_zero.1 this, hv, map_zero, zero_mul, add_zero]
      · apply hsq (u / v)
        field_simp
        linear_combination h0
    have hN : (ι u + ι v * D) * sigR K σ (ι u + ι v * D) = ι (u * u - c * (v * v)) := by
      rw [map_add (f := _), map_mul, hst, hst, hsD, map_sub, map_mul, map_mul, map_mul]
      linear_combination (-(ι v * ι v)) * hDD
    refine IsUnit.of_mul_eq_one (sigR K σ (ι u + ι v * D) * ι (u * u - c * (v * v))⁻¹) ?_
    rw [← mul_assoc, hN, ← map_mul, mul_inv_cancel₀ hn, map_one]

end GlobalTheory.NormDichotomy
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.PartialFourierSum

open GroundTheory.Global NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem adelicFourierPi_mul (f : (κ → mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (y : κ → AdeleRing (𝓞 F) F) :
    adelicFourierPi F (fun x => f (infPartPi x) * g (finPartPi x)) y =
      mixedFourierPi F f (infPartPi y) * finiteFourierPi F g (finPartPi y) := by
  have h := integral_prod_mul (μ := mixedMeasurePi F) (ν := finiteMeasurePi F)
    (fun u ↦ 𝐞 (-mixedPairingPi F u (infPartPi y)) • f u)
    (fun v ↦ g v * (finiteAdelicChar F (∑ i, v i * finPartPi y i) : ℂ))
  have e := measurePreserving_splitEquivPi.integral_comp' (μ := adeleMeasurePi F)
    (f := splitEquivPi F κ) (fun p : (κ → mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) ↦
      (𝐞 (-mixedPairingPi F p.1 (infPartPi y)) • f p.1) *
        (g p.2 * (finiteAdelicChar F (∑ i, p.2 i * finPartPi y i) : ℂ)))
  rw [mixedFourierPi, finiteFourierPi, ← h, ← e, adelicFourierPi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [splitEquivPi_apply, adelicChar_sum_mul_eq_pi, Circle.smul_def, smul_eq_mul]
  ring

theorem exists_summable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : (κ → mixedSpace F) ≃L[ℝ] E)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → Summable fun ξ : κ → F => ((1 + ‖L (embPi F ξ)‖) ^ k)⁻¹ *
      ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ := by
  obtain ⟨k₀, M, hM, hb⟩ := GlobalTheory.SchwartzMajorant.exists_majorant_pureA F (g := g) hg 0
  refine ⟨k₀, fun k hk => ?_⟩
  set c : ℝ := ‖(L.symm : E →L[ℝ] (κ → mixedSpace F))‖ with hc
  have hn : ∀ v, ‖((((1 + ‖L v‖) ^ k)⁻¹ : ℝ) : ℂ)‖ = ((1 + ‖L v‖) ^ k)⁻¹ := fun v => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hb' := hb 1 (c ^ k₀) (fun v => ((((1 + ‖L v‖) ^ k)⁻¹ : ℝ) : ℂ))
    (fun v => by
      rw [hn]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (L v)])))
    (fun v => by
      rw [hn, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have h1 : ‖v‖ ≤ c * ‖L v‖ := by
        simpa using (L.symm : E →L[ℝ] (κ → mixedSpace F)).le_opNorm (L v)
      have hc0 : 0 ≤ c := norm_nonneg _
      calc ‖v‖ ^ k₀ ≤ (c * (1 + ‖L v‖)) ^ k₀ :=
            pow_le_pow_left₀ (norm_nonneg _) (h1.trans (by nlinarith [norm_nonneg (L v)])) _
        _ = c ^ k₀ * (1 + ‖L v‖) ^ k₀ := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith [norm_nonneg (L v)]) hk) (by positivity))
  refine Summable.of_nonneg_of_le (fun ξ => by positivity) (fun ξ => ?_) (hM.mul_left (1 + c ^ k₀))
  have h := hb' ξ
  rw [GlobalTheory.SchwartzMajorant.pureA_add_algebraMap, norm_mul, hn] at h
  have e1 : ((fun j => mixedEmbedding F (ξ j)) + fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((0 : κ → AdeleRing (𝓞 F) F) j).1) = embPi F ξ := by
    funext j
    simp only [Pi.add_apply, Pi.zero_apply, embPi]
    rw [show (0 : AdeleRing (𝓞 F) F).1 = 0 from rfl, map_zero, add_zero]
  have e2 : ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + fun j =>
      ((0 : κ → AdeleRing (𝓞 F) F) j).2) = fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j) := by
    funext j
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [show (0 : AdeleRing (𝓞 F) F).2 = 0 from rfl, add_zero]
  rw [e1, e2] at h
  exact h

def shear : ((κ → mixedSpace F) × EuclidPi F κ) ≃L[ℝ] (κ ⊕ κ → mixedSpace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => Sum.elim ((toEuclidPi F).symm p.2 + p.1) ((toEuclidPi F).symm p.2)
      map_add' := fun p q => by
        funext i
        rcases i with i | i
        · simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), Sum.elim_inl, Pi.add_apply]; abel
        · simp only [Prod.snd_add, map_add (f := _), Sum.elim_inr, Pi.add_apply]
      map_smul' := fun a p => by
        funext i
        rcases i with i | i
        · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Sum.elim_inl, Pi.add_apply, Pi.smul_apply,
            RingHom.id_apply, smul_add]
        · simp only [Prod.smul_snd, map_smul, Sum.elim_inr, Pi.smul_apply, RingHom.id_apply]
      invFun := fun x => (fun i => x (Sum.inl i) - x (Sum.inr i), toEuclidPi F fun i => x (Sum.inr i))
      left_inv := fun p => by
        refine Prod.ext (funext fun i => ?_) ?_
        · simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply]; abel
        · simp only [Sum.elim_inr]
          exact (toEuclidPi F).apply_symm_apply p.2
      right_inv := fun x => by
        funext i
        rcases i with i | i
        · simp only [ContinuousLinearEquiv.symm_apply_apply, Sum.elim_inl, Pi.add_apply]; abel
        · simp only [ContinuousLinearEquiv.symm_apply_apply, Sum.elim_inr] }

theorem arch_bound (f : SchwartzMap (κ ⊕ κ → mixedSpace F) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ u v : κ → mixedSpace F, ‖mixedFourierPi F (fun t => f (Sum.elim (t + u) t)) v‖ ≤
      C * (((1 + ‖u‖) ^ k)⁻¹ * ((1 + ‖toEuclidPiConj F v‖) ^ k)⁻¹) := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.schwartz_fourier_secondVariable_rapid_decay (κ → mixedSpace F) (EuclidPi F κ)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (shear (F := F) (κ := κ)) f) k
  refine ⟨C, fun u v => ?_⟩
  have h := hC u (toEuclidPiConj F v)
  rw [mixedFourierPi_eq, ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact h

theorem finiteTensor_shift (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (b : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)
    (u t : κ → FiniteAdeleRing (𝓞 F) F) :
    finiteTensor (fun i => cosetIndicator J (b i)) (Sum.elim (t + u) t) =
      finiteTensor (fun i => cosetIndicator J (b (Sum.inl i) - b (Sum.inr i))) u *
        finiteTensor (fun i => cosetIndicator J (b (Sum.inr i))) t := by
  simp only [finiteTensor, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [cosetIndicator_apply]
  by_cases h : t i - b (Sum.inr i) ∈ idealFiniteAdeles J
  · have : t i + u i - b (Sum.inl i) ∈ idealFiniteAdeles J ↔
        u i - (b (Sum.inl i) - b (Sum.inr i)) ∈ idealFiniteAdeles J := by
      rw [show t i + u i - b (Sum.inl i) = (t i - b (Sum.inr i)) + (u i - (b (Sum.inl i) - b (Sum.inr i))) by ring]
      exact AddSubgroup.add_mem_cancel_left _ h
    simp only [this]
  · simp only [if_neg h, mul_zero]

theorem summable_gen (f : SchwartzMap (κ ⊕ κ → mixedSpace F) ℂ) (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (b : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :
    Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F =>
      schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i))
        (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  set g₁ := finiteTensor (fun i => cosetIndicator J (b (Sum.inl i) - b (Sum.inr i))) with hg₁
  set g₂ := finiteTensor (fun i => cosetIndicator J (b (Sum.inr i))) with hg₂
  have m₁ : g₁ ∈ finiteSchwartzBruhatPi F :=
    finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J _
  have m₂ : finiteFourierPi F g₂ ∈ finiteSchwartzBruhatPi F :=
    finiteFourierPi_mem (finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J _)
  obtain ⟨k₁, h₁⟩ := exists_summable (ContinuousLinearEquiv.refl ℝ (κ → mixedSpace F)) m₁
  obtain ⟨k₂, h₂⟩ := exists_summable (toEuclidPiConj F) m₂
  obtain ⟨C, hC⟩ := arch_bound f (max k₁ k₂)
  have hs := ((h₁ _ (le_max_left k₁ k₂)).mul_of_nonneg (h₂ _ (le_max_right k₁ k₂))
    (fun _ => by positivity) (fun _ => by positivity)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun uv => ?_) hs
  have key : (fun t : κ → AF F => schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i))
        (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) =
      fun t => (fun s => f (Sum.elim (s + embPi F uv.1) s)) (infPartPi t) *
        (g₁ (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (uv.1 i)) • g₂) (finPartPi t) := by
    funext t
    have e1 : infPartPi (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t) =
        Sum.elim (infPartPi t + embPi F uv.1) (infPartPi t) := by
      rw [← infPartPi_algebraMap]
      funext i
      rcases i with i | i
      · simp only [infPartPi, Sum.elim_inl, Pi.add_apply, homeomorphMixedSpace_apply]
        exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
      · rfl
    have e2 : finPartPi (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t) =
        Sum.elim (finPartPi t + fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (uv.1 i)) (finPartPi t) := by
      rw [← finPartPi_algebraMap]
      funext i
      rcases i with i | i <;> rfl
    rw [schwartzBruhatTensorPi, e1, e2, finiteTensor_shift]
    rfl
  rw [key, adelicFourierPi_mul (fun s => f (Sum.elim (s + embPi F uv.1) s)), finiteFourierPi_smul, infPartPi_algebraMap, finPartPi_algebraMap, norm_mul,
    Pi.smul_apply, smul_eq_mul, norm_mul]
  refine (mul_le_mul_of_nonneg_right (hC _ _) (by positivity)).trans (le_of_eq ?_)
  simp only [ContinuousLinearEquiv.refl_apply]
  ring

theorem summable_partial_fourier : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ), φ ∈ schA F (κ ⊕ κ) → Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F => φ (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  intro F _ _ κ _ φ hφ
  have hS : schA F (κ ⊕ κ) = cosetSpanPi F (κ ⊕ κ) := by
    rw [← schwartzBruhatPi_eq_cosetSpanPi]
    refine congrArg (Submodule.span ℂ) (Set.ext fun Φ => ?_)
    exact ⟨fun ⟨f, g, hg, h⟩ => ⟨f, g, hg, h⟩, fun ⟨f, g, hg, h⟩ => ⟨f, g, hg, h⟩⟩
  have hI : ∀ ψ ∈ cosetSpanPi F (κ ⊕ κ), ∀ u : κ → AF F,
      Integrable (fun t : κ → AF F => ψ (Sum.elim (t + u) t)) (adeleMeasurePi F) := fun ψ hψ u =>
    integrable_of_mem_schwartzBruhatPi (GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi F κ ψ (hS ▸ hψ) u)
  rw [hS] at hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, J, b, rfl⟩ := hG
    exact summable_gen f J b
  | zero =>
    simp only [Pi.zero_apply, adelicFourierPi, zero_mul, integral_zero, norm_zero]
    exact summable_zero
  | add G H hG hH ihG ihH =>
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun uv => ?_) (ihG.add ihH)
    have h := congrFun (adelicFourierPi_add (hI G hG fun i => algebraMap F (AF F) (uv.1 i))
      (hI H hH fun i => algebraMap F (AF F) (uv.1 i))) (fun i => algebraMap F (AF F) (uv.2 i))
    exact (congrArg norm h).le.trans (norm_add_le _ _)
  | smul c G _ ih =>
    refine (ih.mul_left ‖c‖).congr fun uv => ?_
    have h := congrFun (adelicFourierPi_smul c (fun t : κ → AF F =>
      G (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t))) (fun i => algebraMap F (AF F) (uv.2 i))
    rw [← _root_.norm_smul]
    exact (congrArg norm h).symm

end GlobalTheory.PartialFourierSum
end
end

section

open Filter Topology MvPolynomial GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.Count

theorem abs_intCast_le_iff (c : ℤ) {R : ℝ} (hR : 0 ≤ R) :
    |(c : ℝ)| ≤ R ↔ c ∈ Finset.Icc (-(⌊R⌋₊ : ℤ)) (⌊R⌋₊ : ℤ) := by
  rw [Finset.mem_Icc, ← abs_le, ← Int.cast_abs, ← Int.le_floor, Int.natCast_floor_eq_floor hR]

theorem coeff_sum_monomial {D q : ℕ} [Fintype {α : Fin (D + 1) →₀ ℕ // α.degree = q}]
    (g : {α : Fin (D + 1) →₀ ℕ // α.degree = q} → ℤ) (β : Fin (D + 1) →₀ ℕ) :
    AddMonoidAlgebra.coeff (∑ a, monomial a.1 (g a)) β = if h : β.degree = q then g ⟨β, h⟩ else 0 := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨β, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Subtype.ext e)
    · simp
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg]
    rintro rfl
    exact h a.2

theorem coeff_eq_zero_of_isHomogeneous {D q : ℕ} {P : MvPolynomial (Fin (D + 1)) ℤ}
    (hP : P.IsHomogeneous q) {β : Fin (D + 1) →₀ ℕ} (hβ : β.degree ≠ q) : AddMonoidAlgebra.coeff P β = 0 := by
  by_contra hc
  exact hβ (by rw [Finsupp.degree_eq_weight_one]; exact hP hc)

end GlobalTheory.HSAmp.Count

open GlobalTheory.HSAmp.Count in
theorem GlobalTheory.HSAmp.card_bounded_forms : ∀ (D q δ : ℕ) (R : ℝ), 0 ≤ R → {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R}.Finite ∧ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R}.ncard = (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ∧ Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D ∧ Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) = (q + D).choose D ∧ Module.Finite ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) := by
  intro D q δ R hR
  classical
  have hAcard : Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D := by
    rw [GlobalTheory.natCard_degree_eq, Fintype.card_fin, show q + (D + 1) - 1 = q + D by omega,
      Nat.choose_symm_add]
  haveI : Finite {α : Fin (D + 1) →₀ ℕ // α.degree = q} := (Finsupp.finite_of_degree_eq q).to_subtype
  letI : Fintype {α : Fin (D + 1) →₀ ℕ // α.degree = q} := Fintype.ofFinite _
  set S := {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧
    ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R} with hS
  let F : S → (Fin δ → {α : Fin (D + 1) →₀ ℕ // α.degree = q} →
      Finset.Icc (-(⌊R⌋₊ : ℤ)) (⌊R⌋₊ : ℤ)) :=
    fun T i a => ⟨AddMonoidAlgebra.coeff (T.1 i) a.1, (abs_intCast_le_iff _ hR).1 (T.2.2 i a.1)⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨T, hT⟩ ⟨T', hT'⟩ h
      apply Subtype.ext
      funext i
      ext β
      by_cases hβ : β.degree = q
      · have := congrArg Subtype.val (congrFun (congrFun h i) ⟨β, hβ⟩)
        simpa [F] using this
      · rw [coeff_eq_zero_of_isHomogeneous (hT.1 i) hβ, coeff_eq_zero_of_isHomogeneous (hT'.1 i) hβ]
    · intro f
      refine ⟨⟨fun i => ∑ a, monomial a.1 ((f i a : ℤ)), fun i => ?_, fun i β => ?_⟩, ?_⟩
      · exact IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_monomial _ a.2
      · rw [coeff_sum_monomial]
        split_ifs with h
        · exact (abs_intCast_le_iff _ hR).2 (f i ⟨β, h⟩).2
        · simpa using hR
      · funext i a
        apply Subtype.ext
        change AddMonoidAlgebra.coeff (∑ b, monomial b.1 (f i b : ℤ)) a.1 = (f i a : ℤ)
        rw [coeff_sum_monomial, dif_pos a.2]
  let e := Equiv.ofBijective F hF
  have hfin : S.Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)
  refine ⟨hfin, ?_, hAcard, ?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_fun, hAcard,
      Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc, Nat.card_eq_fintype_card,
      Fintype.card_fin, ← pow_mul, mul_comm]
    congr 1
    omega
  · rw [homogeneousSubmodule_eq_finsupp_supported]
    exact (Module.finrank_eq_nat_card_basis
      (basisRestrictSupport ℤ {d : Fin (D + 1) →₀ ℕ | d.degree = q})).trans hAcard
  · rw [homogeneousSubmodule_eq_finsupp_supported]
    haveI : Finite {d : Fin (D + 1) →₀ ℕ | d.degree = q} := (Finsupp.finite_of_degree_eq q).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport ℤ {d : Fin (D + 1) →₀ ℕ | d.degree = q})
end

section

open MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.gaussian_iteratedFDeriv_weighted_exp_bounded : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c α : ℝ), 0 < c → α < 1 → ∀ (k m : ℕ),
    ∃ K : ℝ, ∀ y : E, ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
      Real.exp (c * α * ‖y‖ ^ 2) ≤ K := by
  first | exact @GlobalTheory.GaussDerivBound.weighted_bound | exact GlobalTheory.GaussDerivBound.weighted_bound | (intros; apply GlobalTheory.GaussDerivBound.weighted_bound <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.lintegral_fubiniStudy_density_eq_one' : ∀ n : ℕ, ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n, ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) = 1 := by
  first | exact @GlobalTheory.lintegral_fubiniStudy_density_eq_one | exact GlobalTheory.lintegral_fubiniStudy_density_eq_one | (intros; apply GlobalTheory.lintegral_fubiniStudy_density_eq_one <;> assumption)
end
