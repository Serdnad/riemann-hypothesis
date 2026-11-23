module

import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle010
public import Mathlib.Algebra.DualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle027
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle028
public import Formalism.RealPlaceAnalysis.Bundle003
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle029
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle010
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorSumCounterexample
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries
open scoped MvPowerSeries.WithPiTopology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.Jets

theorem hasSubst_add_sqZero {σ τ S : Type} [Fintype σ] [CommRing S]
    (a b : σ → MvPowerSeries τ S) (e : MvPowerSeries τ S) (he : e * e = 0)
    (ha : ∀ s, IsNilpotent (constantCoeff (a s))) : HasSubst (fun s => a s + e * b s) := by
  apply hasSubst_of_constantCoeff_nilpotent
  intro s
  rw [map_add (f := _), map_mul]
  have h1 : IsNilpotent (constantCoeff e) := ⟨2, by rw [pow_two, ← map_mul, he, map_zero]⟩
  exact (Commute.all _ _).isNilpotent_add (ha s) ((Commute.all _ _).isNilpotent_mul_right h1)


open scoped MvPowerSeries.WithPiTopology in
theorem subst_add_sqZero {σ τ S : Type} [Fintype σ] [CommRing S]
    (a b : σ → MvPowerSeries τ S) (e : MvPowerSeries τ S) (he : e * e = 0)
    (ha0 : ∀ s, IsNilpotent (constantCoeff (a s))) (g : MvPowerSeries σ S) :
    subst (fun s => a s + e * b s) g = subst a g + e * ∑ s, b s * subst a (pderiv s g) := by
  classical
  letI : TopologicalSpace S := ⊥
  letI : UniformSpace S := ⊥
  haveI : DiscreteUniformity S := ⟨rfl⟩
  have ha : HasSubst a := hasSubst_of_constantCoeff_nilpotent ha0
  have hb : HasSubst (fun s => a s + e * b s) := hasSubst_add_sqZero a b e he ha0
  have continuousPderiv (i : σ) : Continuous (fun f : MvPowerSeries σ S => pderiv i f) := by
    refine continuous_pi fun n => ?_
    have h : (fun f : MvPowerSeries σ S => (pderiv i f) n) =
        (fun a : S => a * ((n i : S) + 1)) ∘ ⇑(MvPowerSeries.coeff (n + Finsupp.single i 1)) := by
      funext f
      exact coeff_pderiv f n
    rw [h]
    exact continuous_of_discreteTopology.comp (MvPowerSeries.WithPiTopology.continuous_coeff S _)
  have hca : Continuous (subst a : MvPowerSeries σ S → MvPowerSeries τ S) := continuous_subst ha
  have hcb : Continuous (subst (fun s => a s + e * b s) :
      MvPowerSeries σ S → MvPowerSeries τ S) := continuous_subst hb
  have hs0 : subst a (0 : MvPowerSeries σ S) = 0 := by rw [← coe_substAlgHom ha, map_zero]
  have hs1 : subst a (1 : MvPowerSeries σ S) = 1 := by rw [← coe_substAlgHom ha, map_one]
  let D2 : MvPowerSeries σ S → MvPowerSeries τ S := fun g =>
    subst a g + e * ∑ s, b s * subst a (pderiv s g)
  have c2 : Continuous D2 :=
    hca.add (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (hca.comp (continuousPderiv _))))
  have hpoly : ∀ p : MvPolynomial σ S,
      subst (fun s => a s + e * b s) (MvPolynomial.toMvPowerSeries p) = D2 (MvPolynomial.toMvPowerSeries p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => simp [D2, subst_C, hs0]
    | add p q hp hq =>
      simp only [D2, MvPolynomial.coe_add, subst_add ha, subst_add hb, map_add (f := _)] at hp hq ⊢
      rw [hp, hq]
      simp only [mul_add, Finset.sum_add_distrib]
      ring
    | mul_X p s hp =>
      simp only [D2, MvPolynomial.coe_mul, MvPolynomial.coe_X] at hp ⊢
      rw [subst_mul ha, subst_X ha, subst_mul hb, subst_X hb, hp]
      have hX : ∀ i : σ, pderiv i (X s : MvPowerSeries σ S) = if i = s then 1 else 0 := by
        intro i
        by_cases h : i = s
        · subst h; simp
        · rw [if_neg h, pderiv_X_of_ne]
          intro h'
          exact h h'.symm
      have hterm : ∀ i : σ, b i * subst a (pderiv i ((MvPolynomial.toMvPowerSeries p) * X s)) =
          (if i = s then b i * subst a (MvPolynomial.toMvPowerSeries p) else 0) +
            a s * (b i * subst a (pderiv i (MvPolynomial.toMvPowerSeries p))) := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hX i, subst_add ha, subst_mul ha,
          subst_mul ha, subst_X ha]
        split_ifs with h
        · rw [hs1]; ring
        · rw [hs0]; ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), ← Finset.mul_sum]
      linear_combination (b s * ∑ i, b i * subst a (pderiv i (MvPolynomial.toMvPowerSeries p))) * he
  have := (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries).equalizer hcb c2 (funext fun p => hpoly p)
  exact congrFun this g

theorem map_pderiv' {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (i : σ)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv i f) = pderiv i (MvPowerSeries.map φ f) := by
  classical
  ext n
  simp [coeff_pderiv]

theorem hasSubst_pt_zero (R : Type) [CommRing R] (d : ℕ) :
    ∀ p : Fin 2 × Fin d,
      constantCoeff ((![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) = 0 := by
  rintro ⟨j, i⟩
  fin_cases j <;> simp [pt]

theorem law_right_unit {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (i : Fin d) :
    ev (n := 1) ![pt R d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS R 1 d) := by
  apply GlobalTheory.HomChain.law_right_unit <;> assumption

theorem map_ev_pt_zero {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (φ : R →+* S)
    (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := 1) ![pt R d 0, 0] g) =
      ev (n := 1) ![pt S d 0, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  rw [MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero (hasSubst_pt_zero R d))]
  congr 1
  funext p
  obtain ⟨j, l⟩ := p
  fin_cases j <;> simp [pt]

theorem C_eps_mul_self (R : Type) [CommRing R] (τ : Type) :
    (C (DualNumber.eps : DualNumber R) : MvPowerSeries τ (DualNumber R)) * C DualNumber.eps = 0 := by
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

theorem addOf_eps {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (v : Fin d → R) (j : Fin d) :
    addOf (n := 1) (G.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
        (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R)) j =
      X ((0 : Fin 1), j) + C (DualNumber.eps : DualNumber R) *
        MvPowerSeries.map (algebraMap R (DualNumber R))
          (∑ i : Fin d, C (v i) *
            ev (n := 1) ![pt R d 0, 0] (pderiv ((1 : Fin 2), i) (G.F j))) := by
  have h := subst_add_sqZero
    (fun p : Fin 2 × Fin d => (![pt (DualNumber R) d 0, 0] : Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2)
    (fun p : Fin 2 × Fin d => (![0, fun i => C (algebraMap R (DualNumber R) (v i))] :
      Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2)
    (C DualNumber.eps) (C_eps_mul_self R _)
    (fun p => by rw [hasSubst_pt_zero]; exact IsNilpotent.zero)
    (MvPowerSeries.map (algebraMap R (DualNumber R)) (G.F j))
  have h1 := map_ev_pt_zero (algebraMap R (DualNumber R)) (G.F j)
  rw [law_right_unit, map_X] at h1

  rw [h1, map_sum]
  simp only [map_mul, map_C, map_ev_pt_zero, map_pderiv']
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add] at h
  refine Eq.trans ?_ h
  unfold addOf ev FGLaw.mapF
  congr 1
  funext p
  obtain ⟨l, i⟩ := p
  fin_cases l
  · simp
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
      zero_add]
    rw [← map_mul]
    congr 1
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem ev_addOf_eps :
    ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (v : Fin d → R) (f : PS R 1 d),
      ev (n := 1) ![addOf (G.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
          (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R))]
        (MvPowerSeries.map (algebraMap R (DualNumber R)) f) =
      MvPowerSeries.map (algebraMap R (DualNumber R)) f +
        C (DualNumber.eps : DualNumber R) *
          MvPowerSeries.map (algebraMap R (DualNumber R)) (Dof G.F v f) := by
  intro R _ d G v f
  have h := subst_add_sqZero
    (X : Fin 1 × Fin d → PS (DualNumber R) 1 d)
    (fun p : Fin 1 × Fin d => MvPowerSeries.map (algebraMap R (DualNumber R))
          (∑ i : Fin d, C (v i) *
            ev (n := 1) ![pt R d 0, 0] (pderiv ((1 : Fin 2), i) (G.F p.2))))
    (C DualNumber.eps) (C_eps_mul_self R _)
    (fun p => by rw [constantCoeff_X]; exact IsNilpotent.zero)
    (MvPowerSeries.map (algebraMap R (DualNumber R)) f)
  rw [subst_self, Fintype.sum_prod_type, Fin.sum_univ_one] at h
  unfold Dof

  rw [map_sum]
  simp only [map_mul (MvPowerSeries.map (algebraMap R (DualNumber R)))
    (∑ i : Fin d, _) (pderiv (R := R) _ f), map_pderiv' (algebraMap R (DualNumber R)) _ f]
  refine Eq.trans ?_ h
  unfold ev
  congr 1
  funext p
  obtain ⟨l, j⟩ := p
  obtain rfl : l = 0 := Subsingleton.elim _ _
  exact addOf_eps G v j

end GlobalTheory.Jets
end
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_assoc : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ρ σ τ : Type) [Fintype ρ] [Fintype σ] (s : ρ → MvPowerSeries σ K) (t : σ → MvPowerSeries τ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) → (∀ i, Small (t i)) → Bdd S → (∀ j, Small (csub t (s j))) ∧ csub t (csub s S) = csub (fun j => csub t (s j)) S := by
  first | exact @GlobalTheory.ConvSer.csub_assoc | exact GlobalTheory.ConvSer.csub_assoc | (intros; apply GlobalTheory.ConvSer.csub_assoc <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.exists_goodReduction_algebraic_weierstrass_model : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (L : PeriodPair), d.Prime → d % 16 = 7 → IsOK d L → ∃ M : Mdl q, M.ι = ι ∧ M.L = L ∧ M.Ok ∧ IsAlgebraic ℚ M.W.a₁ ∧ IsAlgebraic ℚ M.W.a₂ ∧ IsAlgebraic ℚ M.W.a₃ ∧ IsAlgebraic ℚ M.W.a₄ ∧ IsAlgebraic ℚ M.W.a₆ := by
  first | exact @GlobalTheory.MomOne.exists_model | exact GlobalTheory.MomOne.exists_model | (intros; apply GlobalTheory.MomOne.exists_model <;> assumption)
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.lowK_sub_single_sqrt_ckv_le : ∀ (n kk : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ) (s : Fin n), Shape ε kk μ bv → lowK ε (μ - Pi.single s 1) = lowK ε μ - Pi.single s 1 ∧ Real.sqrt (ckv ε (lowK ε μ)) + Real.sqrt n ≤ Real.sqrt (ckv ε (lowK ε (μ - Pi.single s 1))) + 8 * n := by
  first | exact @GlobalTheory.lowK_sub_single_and_sqrt_ckv_le | exact GlobalTheory.lowK_sub_single_and_sqrt_ckv_le | (intros; apply GlobalTheory.lowK_sub_single_and_sqrt_ckv_le <;> assumption)
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.wtNear_pr_and_io_of_algTens : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (Λ : Fin n → ℝ) (t : ℝ), AlgTens ε E N F io pr → (∀ w, w ∈ WtNear E Λ t → ∀ s c, pr s (Pi.single c w) ∈ WtNear (F s) Λ (t + 1)) ∧ ∀ s (y : N s), y ∈ WtNear (F s) Λ t → ∀ d, io s y d ∈ WtNear E Λ (t + 1) := by
  first | exact @GlobalTheory.algTens_wtNear | exact GlobalTheory.algTens_wtNear | (intros; apply GlobalTheory.algTens_wtNear <;> assumption)
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.sum_norm_hhJ_self_le_of_orthogonal : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (y : Fin n → Fin n → M) (In : Finset (Fin n)) (Cc Cs Nn : ℝ), (∀ s t, s ≠ t → hhJ ε (y s) (y t) = 0) → (∀ s ∈ In, 0 ≤ (hhJ ε (y s) (y s)).re) → ∑ c, ‖(∑ s ∈ In, y s) c‖ ^ 2 ≤ Cc ^ 2 * Nn → (∀ s, s ∉ In → ∑ c, ‖y s c‖ ^ 2 ≤ Cs ^ 2 * Nn) → ∑ s, ‖hhJ ε (y s) (y s)‖ ≤ (Cc ^ 2 + (Inᶜ.card : ℝ) * Cs ^ 2) * Nn := by
  first | exact @GlobalTheory.sum_norm_hhJ_self_le | exact GlobalTheory.sum_norm_hhJ_self_le | (intros; apply GlobalTheory.sum_norm_hhJ_self_le <;> assumption)
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_orthogonal_weight_decomp_of_mem_wtNear : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t ∧ IsWeight E ω (x ω)) ∧ w = ∑ ω ∈ T, x ω ∧ ∀ ω ∈ T, ∀ ω' ∈ T, ω ≠ ω' → ⟪x ω, x ω'⟫_ℂ = 0 := by
  first | exact @GlobalTheory.WtOrth.wtNear_orth_decomp | exact GlobalTheory.WtOrth.wtNear_orth_decomp | (intros; apply GlobalTheory.WtOrth.wtNear_orth_decomp <;> assumption)
end

section

open Formalism.REAL Finset

theorem _root_.GlobalTheory.T.capelli_left_comatrix_qminor_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (j l : Fin (m + 1)), ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) • (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) = if l = j then qdet E u else 0 := by
  first | exact @GlobalTheory.capelli_left_comatrix | exact GlobalTheory.capelli_left_comatrix | (intros; apply GlobalTheory.capelli_left_comatrix <;> assumption)
end

section

open Formalism.REAL

namespace GlobalTheory

theorem splitCasimir_eigenvalue_dual : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + (n : ℂ) := by
  intro V _ _ _ n E Et Om m hrel hunit hdet hEt hOm lam x hx hxe
  obtain ⟨-, -, -, hcomm⟩ := tensor_dual_standard_rel V n E Et Om hrel hunit hEt hOm
  obtain ⟨K, hK, -⟩ := lastComatrixRow_inverts_dual V n E Om m hrel hdet hOm
  have key : ∀ z : PiLp 2 (fun _ : Fin (n + 1) => V), Om z = lam • z →
      z (Fin.last n) ≠ 0 → ∃ j, lam = m j + (n : ℂ) := by
    intro z hz hzl
    have h0 := hK ((n : ℂ) - lam) z
    have hzero : ((n : ℂ) - lam - (n : ℂ)) • z + Om z = 0 := by
      rw [hz, ← add_smul]
      simp
    rw [hzero, map_zero] at h0
    have hprod : (∏ j, ((n : ℂ) - lam + m j)) = 0 := by
      rcases (smul_eq_zero.mp h0.symm) with h | h
      · exact h
      · exact absurd h hzl
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hprod
    exact ⟨j, by linear_combination -hj⟩
  by_cases hl : x (Fin.last n) = 0
  · have hc : ∃ c, x c ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      apply hx
      ext c
      simp [hne c]
    obtain ⟨c, hc⟩ := hc
    apply key (Et c (Fin.last n) x)
    · have h1 := congrArg (fun f => f x) (hcomm c (Fin.last n))
      simp only [Module.End.mul_apply] at h1
      rw [h1, hxe, map_smul]
    · rw [hEt, hl, map_zero]
      simpa using hc
  · exact key x hxe hl

end GlobalTheory
end

section

open MeasureTheory Finset
open scoped ENNReal

namespace GlobalTheory.MomentHolder

theorem lintegral_density {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (Ph : Ω → ℝ)
    (hPh : AEMeasurable Ph ν) (h0 : ∀ x, 0 ≤ Ph x) (f : Ω → ℝ) (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂(ν.withDensity fun x => ENNReal.ofReal (Ph x))
      = ∫⁻ x, ENNReal.ofReal (f x * Ph x) ∂ν := by
  rw [lintegral_withDensity_eq_lintegral_mul₀ hPh.ennreal_ofReal
    hf.ennreal_ofReal.aemeasurable]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm (f x), ENNReal.ofReal_mul (h0 x)]

theorem exists_pos_version {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (f : Ω → ℝ)
    (hf : AEMeasurable f ν) (hpos : ∀ᵐ x ∂ν, 0 < f x) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ x, 0 < g x) ∧ f =ᵐ[ν] g := by
  classical
  refine ⟨fun x => if 0 < hf.mk f x then hf.mk f x else 1, ?_, ?_, ?_⟩
  · exact Measurable.ite (measurableSet_lt measurable_const hf.measurable_mk)
      hf.measurable_mk measurable_const
  · intro x
    by_cases h : 0 < hf.mk f x <;> simp [h]
  · filter_upwards [hf.ae_eq_mk, hpos] with x hx hp
    rw [← hx, if_pos hp]

theorem product_moment_le :
    ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : ℕ) (len : Fin (r + 1) → Ω → ℝ)
      (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 < len a x) →
      AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr →
      (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q)) →
      (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2,
        ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν
          ≤ ENNReal.ofReal (Rr ^ (2 * q))) →
      ∫⁻ x, ENNReal.ofReal ((∏ a, len a x ^ 2) * Ph x) ∂ν
        ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ (r + 1)) := by
  intro Ω _ ν r len Ph A Rr hm hpos hPh h0 hmass hA hR h1 h2
  choose l hlm hlp hle using fun a => exists_pos_version ν (len a) (hm a) (hpos a)
  have hall : ∀ᵐ x ∂ν, ∀ a, len a x = l a x := ae_all_iff.2 hle
  set μ : Measure Ω := ν.withDensity fun x => ENNReal.ofReal (Ph x) with hμ
  haveI : IsProbabilityMeasure μ := ⟨by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmass]⟩
  have hR0 : 0 ≤ Rr := zero_le_one.trans hR
  have hsq : ∀ q : ℕ, Real.sqrt A ^ (2 * q) = A ^ q := fun q => by
    rw [pow_mul, Real.sq_sqrt hA]
  have hup := Formalism.HermitianLatticeCounting.P.corollary_upper_estimate_holds Ω μ r (r + 1) l (Real.sqrt A) Rr hlm hlp
    (Real.sqrt_nonneg A) hR0
    (fun q hq => by
      rw [hμ, lintegral_density ν Ph hPh h0 _ ((hlm 0).pow_const _), hsq]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h1 q (by rw [sq]; exact hq))
      filter_upwards [hall] with x hx
      rw [hx])
    (fun c q hq => by
      rw [hμ, lintegral_density ν Ph hPh h0
        (fun ω => (l c.succ ω / l c.castSucc ω) ^ (2 * q)) (((hlm _).div (hlm _)).pow_const _)]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h2 c q (by rw [sq]; exact hq))
      filter_upwards [hall] with x hx
      rw [hx, hx])
  have hprod := Formalism.HermitianLatticeCounting.P.corollary_product_estimate_holds Ω μ r 1 (r + 1) l (Real.sqrt A * Rr ^ r) hlm hlp
    (by positivity) le_rfl
    (fun a _ => by
      rw [mul_one]
      refine (hup a).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, ← pow_mul Rr r]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR ?_) (by positivity)
      rw [mul_comm r]
      exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.1 a.isLt))
  have hfilt : univ.filter (fun a : Fin (r + 1) => a.val < r + 1) = univ :=
    filter_true_of_mem fun a _ => a.isLt
  rw [hfilt, hμ, lintegral_density ν Ph hPh h0 _
    ((Finset.measurable_prod _ fun a _ => hlm a).pow_const _)] at hprod
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hprod.trans_eq ?_)
  · filter_upwards [hall] with x hx
    simp only [hx, mul_one, Finset.prod_pow]
  · congr 1
    rw [mul_one, mul_pow, hsq, mul_pow, ← pow_mul, ← pow_mul]
    congr 2
    ring

end GlobalTheory.MomentHolder
end
