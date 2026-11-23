module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle149
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinConstantTermPartialZeta
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle152
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

theorem mem_of_components : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S]
    [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ)
    (F : Submodule w.valuationSubring (S → Fin N → C)), Function.Injective a →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N,
    (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F := by
  intro C _ w S _ _ a N F ha hF x hx hc
  have hle : ∀ s, filSpace F s ≤ clearDen F s := fun s => by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨diffGen a s, diffGen_ne_zero a ha s, single_mem_of_mem a F hF.stable s y hy⟩
  choose b hb hbx using fun s => hle s (hc s)
  have hB : (∏ s, b s) ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => hb s
  refine hF.saturated x hx (∏ s, b s) hB ?_
  have key : (∏ s, b s) • x = ∑ s, (∏ t ∈ Finset.univ.erase s, b t) •
      (Pi.single s (b s • x s) : S → Fin N → C) := by
    funext s' i
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single s']
    · simp only [smul_pi_apply, Pi.single_eq_same, smul_vec_apply]
      rw [← mul_assoc, ← Subring.coe_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ s')]
    · intro s _ e
      simp [smul_pi_apply, Pi.single_apply, Ne.symm e]
    · simp
  rw [key]
  exact sum_mem fun s _ => F.smul_mem _ (hbx s)

end GlobalTheory.Div.KerFil
end

section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem iSupIndep_eig : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type)
    [CommRing Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), Function.Injective (algebraMap O C) →
    iSupIndep (fun σ : Λ →+* O => eig C (⇑ρ) σ) := by
  intro C _ O _ _ Λ _ h ρ hinj
  let T : Λ → Module.End C (Fin h → C) := fun a => Matrix.toLin' ((ρ a).map (algebraMap O C))
  have hT : ∀ a b, T a * T b = T (a * b) := by
    intro a b
    simp only [T, map_mul, Matrix.map_mul]
    rw [Matrix.toLin'_mul]
    rfl
  have hc : ∀ a b, Commute (T a) (T b) := by
    intro a b
    show T a * T b = T b * T a
    rw [hT, hT, mul_comm]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  let g : (Λ →+* O) → (Λ → C) := fun σ a => algebraMap O C (σ a)
  have hg : Function.Injective g := by
    intro σ τ hστ
    ext a
    exact hinj (congrFun hστ a)
  refine (hind.comp hg).mono ?_
  intro σ
  exact iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace

end GlobalTheory
end

section

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound

theorem normSq_lower (w : ℂ) (a b : ℝ) :
    (w.im) ^ 2 / (1 + ‖w‖ ^ 2) * (a ^ 2 + b ^ 2) ≤ ‖(a : ℂ) + b * w‖ ^ 2 := by
  have h1 : (0 : ℝ) < 1 + ‖w‖ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ h1]
  have hw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hn : ‖(a : ℂ) + b * w‖ ^ 2 = (a + b * w.re) ^ 2 + (b * w.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [hw, hn]
  nlinarith [sq_nonneg (a + b * w.re), sq_nonneg ((a + b * w.re) * w.re + b * w.im * w.im)]

theorem bound : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∃ C : ℝ, ∀ p : F × F, p ≠ 0 → ‖GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm 2 σ z p‖ ≤ C * (∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2)) ^ (-(1 + σ.re)) := by
  intro F _ _ σ hσ z hz
  set s := σ.re with hs
  let c : (F →+* ℝ) → ℝ := fun τ => 4 * Real.pi ^ 2 * ((z τ).im ^ 2 / (1 + ‖z τ‖ ^ 2))
  have hc : ∀ τ, 0 < c τ := fun τ => by have := hz τ; positivity
  refine ⟨(∏ τ, c τ) ^ (-(1 + s)), fun p hp => ?_⟩
  set P := ∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2) with hPdef
  have hP : 0 < P := Finset.prod_pos fun τ _ => by
    by_contra h
    push_neg at h
    have h1 : τ p.1 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    have h2 : τ p.2 = 0 := by nlinarith [sq_nonneg (τ p.1), sq_nonneg (τ p.2)]
    exact hp (Prod.ext ((map_eq_zero τ).1 h1) ((map_eq_zero τ).1 h2))
  set N := ∏ τ, ‖latPt z p τ‖ with hN
  have hNpos : 0 < N := Finset.prod_pos fun τ _ => norm_pos_iff.2 (latPt_ne_zero hz hp τ)
  have hterm : ‖eisTerm 2 σ z p‖ = (N ^ 2) ^ (-(1 + s)) := by
    unfold eisTerm
    simp only [norm_mul, norm_pow, norm_inv, norm_prod]
    rw [← hN, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    rw [show (N ^ 2 : ℝ) = N ^ (2 : ℝ) from (Real.rpow_two N).symm, ← Real.rpow_mul hNpos.le]
    have : (2 : ℝ) * (-(1 + s)) = -(2 : ℝ) + (-2 * σ).re := by simp [hs]; ring
    rw [this, Real.rpow_add hNpos, Real.rpow_neg hNpos.le, Real.rpow_two, inv_pow]
  have hlow : (∏ τ, c τ) * P ≤ N ^ 2 := by
    rw [hPdef, hN, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_le_prod₀ (fun τ _ => mul_nonneg (hc τ).le (by positivity)) fun τ _ => ?_
    have hl : ‖latPt z p τ‖ ^ 2 = 4 * Real.pi ^ 2 * ‖((τ p.1 : ℝ) : ℂ) + (τ p.2 : ℝ) * z τ‖ ^ 2 := by
      simp only [latPt, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      ring
    rw [hl, mul_assoc (4 * Real.pi ^ 2)]
    exact mul_le_mul_of_nonneg_left (normSq_lower (z τ) _ _) (by positivity)
  rw [hterm, ← Real.mul_rpow (Finset.prod_nonneg fun τ _ => (hc τ).le) hP.le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos (Finset.prod_pos fun τ _ => hc τ) hP) hlow (by linarith)

end GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory

theorem upperHalf_prodImPow_contDiffOn : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), ContDiffOn ℝ ∞ (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  intro F _ _ σ
  apply contDiffOn_prod
  intro τ _
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  have hpos : 0 < (z τ).im := hz τ
  have hL : ContDiff ℝ ∞ (fun w : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => (((w τ).im : ℝ) : ℂ)) := by
    have : (fun w : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => (((w τ).im : ℝ) : ℂ)) =
        (Complex.ofRealCLM.comp (Complex.imCLM.comp (ContinuousLinearMap.proj τ))) := by
      ext w; simp
    rw [this]; exact ContinuousLinearMap.contDiff _
  have hslit : (((z τ).im : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hpos
  have hg : ContDiffAt ℂ ∞ (fun s : ℂ => s ^ (-1 - 2 * σ)) (((z τ).im : ℝ) : ℂ) :=
    (analyticAt_id.cpow analyticAt_const hslit).contDiffAt
  exact (hg.restrict_scalars ℝ).comp z hL.contDiffAt

end GlobalTheory
end

section

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem _root_.GlobalTheory.T.norm_sq_mul_exp_neg_trace_le' : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : ℝ), 0 < δ → ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) → |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤ C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) := by
  first | exact @GlobalTheory.norm_sq_mul_exp_neg_trace_le | exact GlobalTheory.norm_sq_mul_exp_neg_trace_le | (intros; apply GlobalTheory.norm_sq_mul_exp_neg_trace_le <;> assumption)
end

section

open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertEisensteinSeriesLattice_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ),
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  DifferentiableOn ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 k 0) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  first | exact @GlobalTheory.eisSum_zero_differentiableOn | exact GlobalTheory.eisSum_zero_differentiableOn | (intros; apply GlobalTheory.eisSum_zero_differentiableOn <;> assumption)
end

section

open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.hasSum_hilbertEisenstein_constantTerm_partialZeta : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (s : ℕ), 1 ≤ s →
  ∀ (D : (Ideal (NumberField.RingOfIntegers F))⁰), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) →
  ∀ Z : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) Z →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 = 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 (2 * s) 0 z c)
      (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F * GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) * Z ((2 * s : ℕ) : ℂ)) := by
  first | exact @GlobalTheory.EisConstTerm.hasSum_constTerm | exact GlobalTheory.EisConstTerm.hasSum_constTerm | (intros; apply GlobalTheory.EisConstTerm.hasSum_constTerm <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.BalancedUnits

open NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
open NumberField.Units.dirichletUnitTheorem

theorem sum_mult_log_sub {K : Type} [Field K] [NumberField K] (x : mixedSpace K)
    (hx : mixedEmbedding.norm x ≠ 0) :
    ∑ w : InfinitePlace K, (mult w : ℝ) * (Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹) = 0 := by
  have h1 : ∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (normAtPlace w x) =
      Real.log (mixedEmbedding.norm x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [Real.log_pow]
    · intro w _
      exact pow_ne_zero _ (mixedEmbedding.norm_ne_zero_iff.mp hx w)
  have h2 : ∑ w : InfinitePlace K, (mult w : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast sum_mult_eq
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp_rw [mul_sub, Finset.sum_sub_distrib, h1, ← Finset.sum_mul, h2]
  field_simp
  ring

theorem exists_unit_log_bound (K : Type) [Field K] [NumberField K] : ∃ M : ℝ, 0 ≤ M ∧
    ∀ b : K, b ≠ 0 → ∃ ε : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      |Real.log (w (((ε : 𝓞 K) : K) * b)) -
        Real.log (mixedEmbedding.norm (mixedEmbedding K (((ε : 𝓞 K) : K) * b))) *
          (Module.finrank ℚ K : ℝ)⁻¹| ≤ M := by
  classical
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded
    ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))).subset_closedBall 0
  refine ⟨(Fintype.card (InfinitePlace K) : ℝ) * |R|, by positivity, ?_⟩
  intro b hb
  have hx : mixedEmbedding.norm (mixedEmbedding K b) ≠ 0 := by
    rw [norm_eq_norm]; simpa using hb
  obtain ⟨ε, hε⟩ := fundamentalCone.exists_unit_smul_mem hx
  refine ⟨ε, ?_⟩
  have hxy : ε • mixedEmbedding K b = mixedEmbedding K (((ε : 𝓞 K) : K) * b) := by
    rw [unitSMul_smul, map_mul]
  rw [hxy] at hε
  set y : K := ((ε : 𝓞 K) : K) * b with hy_def
  set X := mixedEmbedding K y
  set L := Real.log (mixedEmbedding.norm X) * (Module.finrank ℚ K : ℝ)⁻¹
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_pos
  have hlog : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      |(mult w.val : ℝ) * (Real.log (normAtPlace w.val X) - L)| ≤ |R| := by
    intro w
    have h0 := hR hε.1
    rw [mem_closedBall_zero_iff] at h0
    have h2 := (norm_le_pi_norm (logMap X) w).trans h0
    rw [logMap_apply, Real.norm_eq_abs] at h2
    exact h2.trans (le_abs_self R)
  have hmul : ∀ w : InfinitePlace K,
      |(mult w : ℝ) * (Real.log (normAtPlace w X) - L)| ≤ (Fintype.card (InfinitePlace K) : ℝ) * |R| := by
    intro w
    by_cases hw : w = w₀
    · subst hw
      have hs := sum_mult_log_sub X hε.2
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)] at hs
      rw [eq_neg_of_add_eq_zero_left hs, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ w ∈ Finset.univ.erase w₀, |(mult w : ℝ) * (Real.log (normAtPlace w X) - L)|
          ≤ ∑ _w ∈ Finset.univ.erase w₀, |R| := Finset.sum_le_sum fun w hw =>
            hlog ⟨w, Finset.ne_of_mem_erase hw⟩
        _ ≤ (Fintype.card (InfinitePlace K) : ℝ) * |R| := by
            rw [Finset.sum_const, nsmul_eq_mul]
            gcongr
            exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
    · exact (hlog ⟨w, hw⟩).trans (le_mul_of_one_le_left (abs_nonneg R) hcard)
  intro w
  have h := hmul w
  rw [abs_mul, normAtPlace_apply] at h
  refine le_trans ?_ h
  rw [abs_of_pos (by exact_mod_cast mult_pos : (0:ℝ) < mult w)]
  exact le_mul_of_one_le_left (abs_nonneg _) one_le_mult

theorem balanced_unit_multiple (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ b : F, b ≠ 0 → ∃ ε : (𝓞 F)ˣ, ∀ τ τ' : Emb F,
      |τ (((ε : 𝓞 F) : F) * b)| ≤ C * |τ' (((ε : 𝓞 F) : F) * b)| := by
  obtain ⟨M, hM0, hM⟩ := exists_unit_log_bound F
  refine ⟨Real.exp (2 * M), Real.one_le_exp (by positivity), ?_⟩
  intro b hb
  obtain ⟨ε, hε⟩ := hM b hb
  refine ⟨ε, ?_⟩
  set y : F := ((ε : 𝓞 F) : F) * b with hy_def
  have hy : y ≠ 0 := mul_ne_zero (by simp) hb
  have hw : ∀ τ : Emb F, InfinitePlace.mk (Complex.ofRealHom.comp τ) y = |τ y| := by
    intro τ
    rw [InfinitePlace.apply]
    simp
  have hpos : ∀ τ : Emb F, 0 < |τ y| := fun τ => abs_pos.mpr ((map_ne_zero τ).mpr hy)
  intro τ τ'
  have h1 := hε (InfinitePlace.mk (Complex.ofRealHom.comp τ))
  have h2 := hε (InfinitePlace.mk (Complex.ofRealHom.comp τ'))
  rw [hw] at h1 h2
  have key : Real.log |τ y| ≤ 2 * M + Real.log |τ' y| := by
    have := (abs_le.mp h1).2
    have := (abs_le.mp h2).1
    linarith
  calc |τ y| = Real.exp (Real.log |τ y|) := (Real.exp_log (hpos τ)).symm
    _ ≤ Real.exp (2 * M + Real.log |τ' y|) := Real.exp_le_exp.mpr key
    _ = Real.exp (2 * M) * |τ' y| := by rw [Real.exp_add, Real.exp_log (hpos τ')]

end GlobalTheory.BalancedUnits
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.FreeHc

variable {F : Type} [Field F]

def fixSet {m : ℕ} (f : Fin m → F) : Set (GL (Fin m) F) :=
  {x | ∀ w : Fin m → F, f ⬝ᵥ w = 0 → (x : Matrix (Fin m) (Fin m) F) *ᵥ w = w}

def fixSub {m : ℕ} (f : Fin m → F) : Subgroup (GL (Fin m) F) where
  carrier := fixSet f
  one_mem' := by intro w _; simp
  mul_mem' := by
    intro x y hx hy w hw
    rw [Units.val_mul, ← mulVec_mulVec, hy w hw, hx w hw]
  inv_mem' := by
    intro x hx w hw
    calc ((x⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w
        = ((x⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ ((x : Matrix (Fin m) (Fin m) F) *ᵥ w) := by rw [hx w hw]
      _ = w := by rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem isChar_conj {G : Type} [Group G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) (x y : G) :
    χ (y⁻¹ * x * y) = χ x := by
  obtain ⟨n, ρ, hρ⟩ := h
  rw [hρ, hρ]
  congr 1
  simpa using ρ.char_conj x y⁻¹

theorem finsum_mem_eq {α : Type} [Fintype α] (s : Set α) (g : α → ℂ) :
    ∑ᶠ x ∈ s, g x = ∑ x, if x ∈ s then g x else 0 := by
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  simp [Set.indicator_apply]

def eLast (m : ℕ) (hm : 0 < m) : Fin m → F := Pi.single (⟨m - 1, by omega⟩ : Fin m) 1

theorem vmv_mulVec {m : ℕ} (u v w : Fin m → F) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem key {m : ℕ} (f w₀ : Fin m → F) (hw : f ⬝ᵥ w₀ = 1) (x : GL (Fin m) F) (hx : x ∈ fixSet f) :
    (x : Matrix (Fin m) (Fin m) F) = 1 + vecMulVec ((x : Matrix (Fin m) (Fin m) F) *ᵥ w₀ - w₀) f := by
  have h : ∀ w, (x : Matrix (Fin m) (Fin m) F) *ᵥ w =
      (1 + vecMulVec ((x : Matrix (Fin m) (Fin m) F) *ᵥ w₀ - w₀) f) *ᵥ w := by
    intro w
    have hw' : f ⬝ᵥ (w - (f ⬝ᵥ w) • w₀) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, hw, smul_eq_mul, mul_one, sub_self]
    have h1 := hx _ hw'
    rw [add_mulVec, one_mulVec, vmv_mulVec, smul_sub]
    have : w = (w - (f ⬝ᵥ w) • w₀) + (f ⬝ᵥ w) • w₀ := by abel
    conv_lhs => rw [this]
    rw [mulVec_add, h1, mulVec_smul]
    abel
  ext i j
  have := congr_fun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

theorem conj_mem {m : ℕ} (f : Fin m → F) (z x : GL (Fin m) F) :
    z⁻¹ * x * z ∈ fixSet (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) ↔ x ∈ fixSet f := by
  have hzz : (z : Matrix (Fin m) (Fin m) F) * ((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hzz' : ((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * (z : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  constructor
  · intro h w hw
    have hw' : (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) ⬝ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w) = 0 := by
      rw [← dotProduct_mulVec, mulVec_mulVec, hzz, one_mulVec, hw]
    have := h _ hw'
    have hzw : (z : Matrix (Fin m) (Fin m) F) *ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w) = w := by
      rw [mulVec_mulVec, hzz, one_mulVec]
    simp only [Units.val_mul] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, hzw] at this
    have hzv : ∀ v, (z : Matrix (Fin m) (Fin m) F) *ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ v) = v := by
      intro v; rw [mulVec_mulVec, hzz, one_mulVec]
    have := congrArg (fun v => (z : Matrix (Fin m) (Fin m) F) *ᵥ v) this
    simpa only [hzv] using this
  · intro h w hw
    rw [← dotProduct_mulVec] at hw
    simp only [Units.val_mul]
    rw [← mulVec_mulVec, ← mulVec_mulVec, h _ hw, mulVec_mulVec, hzz', one_mulVec]

theorem sum_conj {m : ℕ} [Fintype (GL (Fin m) F)] (f : Fin m → F) (z : GL (Fin m) F) (φ : GL (Fin m) F → ℂ) :
    (∑ x, if x ∈ fixSet f then φ (z⁻¹ * x * z) else 0) =
      ∑ g, if g ∈ fixSet (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) then φ g else 0 := by
  refine Fintype.sum_equiv (MulAut.conj z⁻¹).toEquiv _ _ fun x => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  rw [conj_mem]

end GlobalTheory.Shin.FreeHc
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ), IsFam act w f ↔ ∀ (i : ι) (γ : SL(2, ℤ)) (τ : ℍ), f i (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * f (act i γ) τ := by
  first | exact @GlobalTheory.QFam.isFam_iff_values | exact GlobalTheory.QFam.isFam_iff_values | (intros; apply GlobalTheory.QFam.isFam_iff_values <;> assumption)
end

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

theorem _root_.GlobalTheory.T.conjugationDerivCutoffPolynomial_mem_unitarySpan : ∀ {n : ℕ} (ε : Fin n → Bool) (Z : GlobalTheory.PsCo.Pc1.Mat n) (H : ℝ → ℝ) (P : GlobalTheory.PsCo.Pc1.Poly n), GlobalTheory.PsCo.Pc1.IsCutFn H → GlobalTheory.PsCo.Pc1.adBas ε Z H P ∈ GlobalTheory.PsCo.Pc1.AdSpanM ε := by
  first | exact @GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM | exact GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM | (intros; apply GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM <;> assumption)
end
