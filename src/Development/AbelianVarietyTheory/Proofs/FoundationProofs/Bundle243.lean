module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle232
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle009
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle218
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011

@[expose] public section

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem tqF_semisimple : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
  ∀ (f : CuspForm (Lev N l) (k : ℤ)) (c : ℂ) (n : ℕ), (fun F => TqF (k : ℤ) q σ F - c • F)^[n] ⇑f = 0 → TqF (k : ℤ) q σ ⇑f = c • ⇑f := by
  intro N l k hN hl hlN hk q σ hq hqNl hσ f c n hf
  obtain ⟨_, _, hT, hD, _⟩ := GlobalTheory.T.heckeOperatorsOnHalfPlaneFunctions_agree_explicit
  have hq0 : 0 < q := hq.pos
  have hfun : (fun F => TqF (k : ℤ) q σ F - c • F) = (fun h => GlobalTheory.Hk.heckeT (k:ℤ) q σ h - c • h) := by
    funext F; rw [hT _ _ _ _ hq0]
  have hσ' : GlobalTheory.Hk.IsDia N l ((q:ℕ):ℤ) σ := (hD N l q σ).1 (by simpa using hσ)
  rw [hfun] at hf
  rw [hT _ _ _ _ hq0]
  exact GlobalTheory.T.heckeTOperatorExplicit_semisimple_cuspForms N l q k σ c n (by omega) hl.pos hq hqNl hσ' f hf

end GlobalTheory.HeckeFamilyMatrices
end

section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

theorem _root_.GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ), admitted c x → T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by
  first | exact @GlobalTheory.KZ.SiegelMem.an_siegel_eq | exact GlobalTheory.KZ.SiegelMem.an_siegel_eq | (intros; apply GlobalTheory.KZ.SiegelMem.an_siegel_eq <;> assumption)
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem extNorm_eq_nat_log_le_bound : ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∃ s : ℕ, 0 < s ∧ extNorm K lam = (s : K) ∧ Real.log s ≤ bound (Fintype.card ι) n R := by
  intro K _ _ _ ι _ n lam R hR hS
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hw : ∀ τ i, (lam τ).natW i ≤ ⌊R⌋₊ := by
    intro τ i
    have hn : 0 < n := Fin.pos i
    have h := hS τ i ⟨n - 1, by omega⟩
    have h2 : (lam τ).w i - (lam τ).w ⟨n - 1, by omega⟩ ≤ (⌊R⌋₊ : ℤ) := by
      rw [Int.natCast_floor_eq_floor hR0]
      exact Int.le_floor.mpr h
    unfold DomWeight.natW DomWeight.detShift
    rw [dite_eq_left hn]
    omega
  choose s hs0 hs1 hs2 using fun τ => GlobalTheory.T.fockNorm_extremal_vector_eq_bounded_nat n (lam τ) ⌊R⌋₊ (hw τ)
  refine ⟨∏ τ, s τ, Finset.prod_pos fun τ _ => hs0 τ, ?_, ?_⟩
  · unfold extNorm
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl fun τ _ => hs2 τ K
  · rw [Nat.cast_prod, Real.log_prod (fun τ _ => by exact_mod_cast (hs0 τ).ne')]
    have hb := GlobalTheory.T.log_factorial_pow_mul_factorial_pow_le' n ⌊R⌋₊ R hR (Nat.floor_le hR0)
    have h1 : ∀ τ, Real.log (s τ) ≤ 4 * (n : ℝ) * R * Real.log (n * R) := fun τ =>
      le_trans (Real.log_le_log (by exact_mod_cast hs0 τ) (by exact_mod_cast hs1 τ)) hb
    calc ∑ τ, Real.log (s τ) ≤ ∑ _τ : ι, 4 * (n : ℝ) * R * Real.log (n * R) :=
          Finset.sum_le_sum fun τ _ => h1 τ
      _ = bound (Fintype.card ι) n R := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          unfold bound
          ring

end GlobalTheory
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.MinorBound

theorem card_strictMono_le (a d : ℕ) [Fintype {s : Fin a → Fin d // StrictMono s}] :
    Fintype.card {s : Fin a → Fin d // StrictMono s} ≤ 2 ^ d := by
  have h : Function.Injective
      (fun s : {s : Fin a → Fin d // StrictMono s} => (Set.range s.1 : Set (Fin d))) := by
    intro s t hst
    exact Subtype.ext ((s.2.range_inj t.2).1 hst)
  have := Fintype.card_le_of_injective _ h
  simpa using this

theorem sum_coeff_monomial {σ : Type} (w : (σ →₀ ℕ) → ℂ) :
    ∃ L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ, (∀ α c, L (MvPolynomial.monomial α c) = c * w α) ∧
      ∀ P, L P = ∑ α ∈ P.support, AddMonoidAlgebra.coeff P α * w α := by
  let L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ := (MvPolynomial.basisMonomials σ ℂ).constr ℂ w
  have h1 : ∀ α c, L (MvPolynomial.monomial α c) = c * w α := by
    intro α c
    have : MvPolynomial.monomial α c = c • (MvPolynomial.basisMonomials σ ℂ) α := by
      simp [MvPolynomial.smul_monomial]
    rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  refine ⟨L, h1, fun P => ?_⟩

  conv_lhs => rw [P.as_sum, map_sum]
  simp only [h1]

theorem prod_monomial {σ ι : Type} (s : Finset ι) (α : ι → σ →₀ ℕ) (c : ι → ℂ) :
    ∏ i ∈ s, MvPolynomial.monomial (α i) (c i) =
      MvPolynomial.monomial (∑ i ∈ s, α i) (∏ i ∈ s, c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih,
      MvPolynomial.monomial_mul]

noncomputable def expo (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) : Mono D a d :=
  ∑ τ, ∑ j, ∑ i, Finsupp.single (τ, (T τ j).1 (p τ j i), i) 1

theorem minorPol_eq (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    minorPol D T = ∑ p : (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)),
      MvPolynomial.monomial (expo D T p) (∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ)) := by
  unfold minorPol
  have hdet : ∀ τ (j : Fin (n τ)), (Matrix.of fun i i' : Fin a =>
      (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ)).det =
      ∑ σ : Equiv.Perm (Fin a), MvPolynomial.monomial
        (∑ i, Finsupp.single ((τ, (T τ j).1 (σ i), i) : GL3Theta.Idx D a d) 1)
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) := by
    intro τ j
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply, MvPolynomial.X]
    rw [prod_monomial, ← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (GL3Theta.Idx D a d) ℂ),
      MvPolynomial.C_mul_monomial]
    simp
  simp only [hdet]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr (by convert rfl) fun p _ => ?_
  simp only [prod_monomial, expo]

theorem expo_le (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) (k : D.what₂.Tau × Fin d × Fin a) :
    expo D T p k ≤ n k.1 := by
  obtain ⟨τ0, r, c⟩ := k
  simp only [expo, Finset.sum_apply']
  rw [Finset.sum_eq_single τ0]
  · calc _ ≤ ∑ _j : Fin (n τ0), 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.sum_eq_single c]
          · rw [Finsupp.single_apply]; split_ifs <;> simp
          · intro i _ hi
            rw [Finsupp.single_apply, if_neg]
            simp [hi]
          · simp
      _ = n τ0 := by simp
  · intro τ _ hτ
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    simp [hτ]
  · simp

theorem expo_sum (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) :
    ((expo D T p).sum fun _ m => m) = a * ∑ τ, n τ := by
  have : ((expo D T p).sum fun _ m => m) = Finsupp.degree (expo D T p) := rfl
  rw [this]

  simp only [expo, map_sum, Finsupp.degree_single]
  simp [Finset.mul_sum, mul_comm]

theorem minor_bound : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → (∀ τ, (n τ : ℝ) ≤ 2 * B) → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → (Fintype.card (Tup D a d n) ≤ 2 ^ (d * ∑ τ, n τ)) ∧ ∀ T : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D T) G‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (S * (2 * Real.exp 1 * Real.pi * B / A) ^ (a * ∑ τ, n τ)) := by
  intro D a d n G S A B hA hB hS hn hG hbd
  constructor
  · simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [pow_mul, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' fun τ _ => Nat.pow_le_pow_left (card_strictMono_le a d) _
  · intro T
    obtain ⟨L, hL1, hL2⟩ := sum_coeff_monomial
      (fun α : Mono D a d => (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α)
    have h0 : GL3Theta.applyAt0 D (minorPol D T) G = L (minorPol D T) := by
      rw [hL2]; simp only [GL3Theta.applyAt0, mul_assoc]
    set M := S * (2 * Real.exp 1 * Real.pi * B / A) ^ (a * ∑ τ, n τ) with hM
    have hM0 : 0 ≤ M := by
      have : (0:ℝ) < B := by linarith
      have := Real.pi_pos
      positivity
    have hterm : ∀ p : (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)),
        ‖L (MvPolynomial.monomial (expo D T p)
          (∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ)))‖ ≤ Real.sqrt M := by
      intro p
      rw [hL1, norm_mul]
      have hs : ‖(∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ))‖ = 1 := by
        rw [norm_prod]
        refine Finset.prod_eq_one fun τ _ => ?_
        rw [norm_prod]
        refine Finset.prod_eq_one fun j _ => ?_
        rcases Int.units_eq_one_or (Equiv.Perm.sign (p τ j)) with h | h <;> simp [h]
      rw [hs, one_mul]
      apply Real.le_sqrt_of_sq_le
      have := GlobalTheory.T.monomialDeriv_cauchy_bound_gaussianGrowth D a d G S A B hA hB hS hG hbd (expo D T p) (fun k =>
        le_trans (by exact_mod_cast expo_le D T p k) (hn k.1))
      rwa [expo_sum] at this
    have hcard : (Fintype.card (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) : ℝ) =
        (a.factorial : ℝ) ^ (∑ τ, n τ) := by
      simp [Fintype.card_pi, Fintype.card_perm, Finset.prod_pow_eq_pow_sum]
    have hle : ‖L (minorPol D T)‖ ≤ (a.factorial : ℝ) ^ (∑ τ, n τ) * Real.sqrt M := by

      rw [minorPol_eq, map_sum]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    rw [h0]
    calc _ ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ) * Real.sqrt M) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, Real.sq_sqrt hM0]

end GlobalTheory.MinorBound
end

section

namespace GlobalTheory.EntireTaylor

theorem summable_of_entire {σ : Type*} [Fintype σ] [DecidableEq σ] {f : (σ → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (c : (σ →₀ ℕ) → ℂ)
    (hc : ∀ α, (∏ j, ((α j).factorial : ℂ)) * c α = pderivIter α f 0) (w : σ → ℂ) :
    Summable fun α : σ →₀ ℕ => c α * ∏ j, w j ^ α j := by
  obtain ⟨R, hRdef⟩ : ∃ R : σ → ℝ, R = fun j => 2 * ‖w j‖ + 1 := ⟨_, rfl⟩
  have hR : ∀ j, 0 < R j := fun j => by rw [hRdef]; positivity
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ Set.univ.pi (fun j => Metric.closedBall (0 : ℂ) (R j)), ‖f z‖ ≤ M :=
    (isCompact_univ_pi fun j => isCompact_closedBall (0 : ℂ) (R j)).exists_bound_of_continuousOn
      hf.continuous.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
    (hM 0 (Set.mem_univ_pi.mpr fun j => Metric.mem_closedBall.mpr (by simpa using (hR j).le)))
  have hw : ∀ j, ‖w j‖ / R j ≤ 1 / 2 := fun j => by
    rw [div_le_iff₀ (hR j), hRdef]
    linarith [norm_nonneg (w j)]
  have key : ∀ α : σ →₀ ℕ, ‖c α * ∏ j, w j ^ α j‖ ≤ M * ∏ j, (1 / 2 : ℝ) ^ α j := by
    intro α
    have hP : (∏ j, ((α j).factorial : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast Nat.factorial_ne_zero _
    have hcα : c α = pderivIter α f 0 / ∏ j, ((α j).factorial : ℂ) := by
      rw [← hc α, mul_div_cancel_left₀ _ hP]
    have hnormP : ‖∏ j, ((α j).factorial : ℂ)‖ = ∏ j, ((α j).factorial : ℝ) := by
      rw [norm_prod]
      simp
    have hPpos : 0 < ∏ j, ((α j).factorial : ℝ) :=
      Finset.prod_pos fun j _ => by exact_mod_cast Nat.factorial_pos _
    have hC : ‖pderivIter α f 0‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, R k ^ α k :=
      GlobalTheory.norm_pderivIter_le_of_differentiable α (fun k => (hR k).le) (fun k _ => hR k) hf
        fun z hz => hM z (Set.mem_univ_pi.mpr fun j => Metric.mem_closedBall.mpr (by
          have h := hz j
          simp only [Pi.zero_apply, sub_zero] at h
          rw [dist_zero_right]
          exact h.le))
    have h1 : ‖c α‖ ≤ M / ∏ j, R j ^ α j := by
      rw [hcα, norm_div, hnormP, div_le_iff₀ hPpos]
      calc ‖pderivIter α f 0‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, R k ^ α k := hC
        _ = (M / ∏ j, R j ^ α j) * ∏ j, ((α j).factorial : ℝ) := by ring
    calc ‖c α * ∏ j, w j ^ α j‖ = ‖c α‖ * ∏ j, ‖w j‖ ^ α j := by
          rw [norm_mul, norm_prod]
          simp [norm_pow]
      _ ≤ (M / ∏ j, R j ^ α j) * ∏ j, ‖w j‖ ^ α j :=
          mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun j _ => by positivity)
      _ = M * ∏ j, (‖w j‖ / R j) ^ α j := by
          simp only [div_pow, Finset.prod_div_distrib]
          ring
      _ ≤ M * ∏ j, (1 / 2 : ℝ) ^ α j :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod₀ (fun j _ => by have := (hR j).le; positivity)
              fun j _ => pow_le_pow_left₀ (by have := (hR j).le; positivity) (hw j) _) hM0
  exact Summable.of_norm_bounded
    ((GlobalTheory.ProdThetaConj.summable_prod_half_pow (σ := σ)).mul_left M) key

end GlobalTheory.EntireTaylor

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem GlobalTheory.EntireTaylor.hasSum_taylor_mono : ∀ (D : D7) (N N' : ℕ) (F : VC D N N' → ℂ), Differentiable ℂ F → ∀ z : VC D N N', HasSum (fun α : Mono D N N' => Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z) (F z) := by
  intro D N N' F hF z
  have hcd : Differentiable ℂ (fun w => F (GlobalTheory.GaussCauchy.curry D N N' w)) := fun w =>
    (hF _).comp w (LinearMap.toContinuousLinearMap (GlobalTheory.GaussCauchy.curry D N N')).differentiableAt
  have hS := GlobalTheory.EntireTaylor.summable_of_entire hcd (fun α => Formalism.MainNotions.TaylorLogMetric.taylor D F α)
    (fun α => by
      rw [← GlobalTheory.GaussCauchy.factorial_mul_taylor D N N' F hF α, Finsupp.prod_fintype]
      intro i
      simp)
    (fun k => z k.1 k.2.1 k.2.2)
  have hmono : ∀ α : Mono D N N', mono D α z = ∏ k, z k.1 k.2.1 k.2.2 ^ α k := fun α => by
    show (α.prod fun k n => z k.1 k.2.1 k.2.2 ^ n) = _
    rw [Finsupp.prod_fintype]
    intro i
    simp
  have hS' : Summable fun α : Mono D N N' => Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z := by
    simpa only [hmono] using hS
  rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D hF z]
  exact hS'.hasSum
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.KerSum

theorem exists_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, ‖H u v‖ ≤ M * ‖u‖ * ‖v‖ := by
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun u v => H u v)
    (fun a b c => by simp)
    (fun c a b => by
      rw [← Complex.coe_smul, map_smul, LinearMap.smul_apply, Complex.coe_smul])
    (fun a b c => by simp)
    (fun c a b => by
      rw [← Complex.coe_smul, LinearMap.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul])
  let B' : V →L[ℝ] V →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ B)
  exact ⟨‖B'‖, norm_nonneg _, fun u v => B'.le_opNorm₂ u v⟩

theorem norm_kerTerm_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : Sesq V) {M R : ℝ} (hM : 0 ≤ M) (hB : ∀ u v, ‖H u v‖ ≤ M * ‖u‖ * ‖v‖) (x w z : V)
    (hw : ‖w‖ ≤ R) :
    ‖kerTerm H x w z‖ ≤ Real.exp (π * (M * R * ‖z‖)) *
      Real.exp (-(π / 2) * (H x x).re + (π * (M * ‖z‖ + M * R)) * ‖x‖) := by
  rw [kerTerm, Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
  have h1 : (H w z).re ≤ M * R * ‖z‖ :=
    ((Complex.re_le_norm _).trans (hB w z)).trans (by gcongr)
  have h2 : (H x z).re ≤ M * ‖x‖ * ‖z‖ := (Complex.re_le_norm _).trans (hB x z)
  have h3 : -(H w x).re ≤ M * R * ‖x‖ :=
    (((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (hB w x)).trans (by gcongr)
  have e : ((π : ℂ) * H (w + x) z - (π : ℂ) * H w x - (π : ℂ) * H x x / 2).re
      = π * ((H w z).re + (H x z).re + -(H w x).re) - π / 2 * (H x x).re := by
    simp; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) Real.pi_pos.le
  linarith

theorem differentiable_kerTerm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (H : Sesq V) (x z : V) :
    Differentiable ℂ (fun w => kerTerm H x w z) := by
  have h : ∀ v, Differentiable ℂ (fun w => H w v) := fun v =>
    (LinearMap.toContinuousLinearMap (H.flip v)).differentiable
  have e : (fun w => kerTerm H x w z) = fun w =>
      cexp ((π : ℂ) * (H w z + H x z) - (π : ℂ) * H w x - (π : ℂ) * H x x / 2) := by
    funext w; simp [kerTerm]
  rw [e]
  exact (((((h z).add_const _).const_mul _).sub ((h x).const_mul _)).sub_const _).cexp

theorem kerTerm_shift {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
    (hH : ∀ z w, H z w = conj (H w z)) (x y w z : V) :
    kerTerm H x (w + y) z * cexp (-(π : ℂ) * H w y - (π : ℂ) * H y y / 2)
      = cexp (-((π : ℂ) * I) * ((H y x).im : ℂ)) * kerTerm H (y + x) w z := by
  have h : I * ((H y x).im : ℂ) = (H y x - H x y) / 2 := by
    rw [hH x y, Complex.sub_conj]; push_cast; ring
  rw [kerTerm, kerTerm, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_add (f := _), LinearMap.add_apply]
  linear_combination (π : ℂ) * h

theorem kerSum_spec : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (α : V → ℂ), IsSemichar H Λ α → (∀ w z, Summable (fun x : Λ => α x * kerTerm H x w z)) ∧ (∀ z, Differentiable ℂ (kerSum H Λ α z)) ∧ ∀ z, ∀ y ∈ Λ, ∀ w, α y * Heisenberg₂ H y (kerSum H Λ α z) w = kerSum H Λ α z w := by
  intro V _ _ _ H hH Λ _ α hα
  obtain ⟨M, hM, hB⟩ := exists_bound H
  have hn : ∀ x : Λ, ‖α x‖ = 1 := fun x => by
    rcases hα.1 x x.2 with h | h <;> simp [h]
  have key : ∀ (z : V) (R : ℝ), ∃ u : Λ → ℝ, Summable u ∧
      ∀ (x : Λ) (w : V), ‖w‖ ≤ R → ‖α x * kerTerm H x w z‖ ≤ u x := fun z R =>
    ⟨_, (GlobalTheory.T.summable_exp_neg_herm_add_norm V H hH Λ (π * (M * ‖z‖ + M * R))).mul_left (Real.exp (π * (M * R * ‖z‖))),
      fun x w hw => by
        rw [norm_mul, hn, one_mul]
        exact norm_kerTerm_le H hM hB x w z hw⟩
  refine ⟨fun w z => ?_, fun z => ?_, fun z y hy w => ?_⟩
  · obtain ⟨u, hu, h⟩ := key z ‖w‖
    exact Summable.of_norm_bounded hu fun x => h x w le_rfl
  · refine differentiableOn_univ.1 (GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal isOpen_univ
      (F := fun (x : Λ) w => α x * kerTerm H x w z)
      (fun x => ((differentiable_kerTerm H x z).const_mul _).differentiableOn) fun w _ => ?_)
    obtain ⟨u, hu, h⟩ := key z (‖w‖ + 1)
    refine ⟨Metric.ball w 1, Metric.ball_mem_nhds w one_pos, u, hu, fun x v hv => h x v ?_⟩
    have := norm_le_norm_add_norm_sub' v w
    rw [mem_ball_iff_norm] at hv
    linarith
  · simp only [Heisenberg₂, kerSum]
    rw [← tsum_mul_right, ← tsum_mul_left,
      ← (Equiv.addLeft (⟨y, hy⟩ : Λ)).tsum_eq (fun x : Λ => α x * kerTerm H x w z)]
    refine tsum_congr fun x => ?_
    simp only [Equiv.coe_addLeft, AddSubgroup.coe_add]
    rw [hα.2.2 y hy x x.2, mul_assoc (α x), kerTerm_shift H hH.1]
    ring

end GlobalTheory.UnitaryTheta.KerSum
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.nabIndep_and_delIndep_local_conditions : NabIndep ∧ DelIndep := by
  first | exact @GlobalTheory.TestLat.nabIndep_and_delIndep | exact GlobalTheory.TestLat.nabIndep_and_delIndep | (intros; apply GlobalTheory.TestLat.nabIndep_and_delIndep <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isHCModule_of_graded_dense_gK : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IsHCMod σ M j := by
  first | exact @GlobalTheory.GradedKFin.isHCMod_of_graded | exact GlobalTheory.GradedKFin.isHCMod_of_graded | (intros; apply GlobalTheory.GradedKFin.isHCMod_of_graded <;> assumption)
end
