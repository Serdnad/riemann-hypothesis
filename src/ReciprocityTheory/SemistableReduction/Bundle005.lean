module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.SemistableReduction.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.Bundle003
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.Lagrange
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwp_ext_poly {σ : Type*} [Fintype σ] [DecidableEq σ] (k : ℕ) (g D : (σ → ℂ) → ℂ)
    (w : σ → ℂ) (hw : ∀ z, {s : ℂ | D (z + s • w) = 0}.Finite)
    (hD : ∀ z v, D z ≠ 0 → {t : ℂ | D (z + t • v) = 0}.Finite)
    (hL : ∀ z v, {t : ℂ | D (z + t • v) = 0}.Finite → ∃ Q : ℂ[X], Q.natDegree ≤ k ∧
      ∀ t, D (z + t • v) ≠ 0 → g (z + t • v) = Q.eval t) :
    ∃ F : MvPolynomial σ ℂ, ∀ z, D z ≠ 0 → g z = MvPolynomial.eval z F := by

  have hw' := fun y => hL y w (hw y)
  choose Qw hQd hQ using hw'

  have hv' := fun (y v : σ → ℂ) (h : D y ≠ 0) => hL y v (hD y v h)
  choose P hPd hP using hv'
  let G : (σ → ℂ) → ℂ := fun y => (Qw y).eval 0
  have hsep : ∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t := by
    intro y m
    set z : σ → ℂ := Function.update y m 0
    set e : σ → ℂ := Pi.single m 1
    have hupd : ∀ t, Function.update y m t = z + t • e := by
      intro t; ext i
      by_cases hi : i = m
      · subst hi; simp [z, e]
      · simp [z, e, Function.update_apply, hi, Pi.single_apply]
    let Pc : ℂ → ℂ[X] := fun c => if h : D (z + c • w) = 0 then 0 else P (z + c • w) e h
    let R : Finset ℂ → ℂ[X] := fun S =>
      ∑ c ∈ S, Polynomial.C ((Lagrange.basis S id c).eval 0) * Pc c
    have hRdeg : ∀ S, (R S).natDegree ≤ k := by
      intro S
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun c _ => ?_)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      simp only [Pc]
      split_ifs with h
      · simp
      · exact hPd _ _ h

    have key : ∀ S : Finset ℂ, S.card = k + 1 → (∀ c ∈ S, D (z + c • w) ≠ 0) →
        ∀ t, (∀ c ∈ S, D ((z + t • e) + c • w) ≠ 0) → G (z + t • e) = (R S).eval t := by
      intro S hS hSz t ht
      simp only [G, R]
      rw [bwp_eval_eq_lagrange S (Qw (z + t • e)) k hS (hQd _) 0, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl (fun c hc => ?_)
      rw [Polynomial.eval_mul, Polynomial.eval_C, ← hQ _ c (ht c hc)]
      congr 1
      simp only [Pc, dif_neg (hSz c hc)]
      rw [← hP _ _ (hSz c hc) t (by rw [add_right_comm]; exact ht c hc), add_right_comm]
    have hbad : ∀ S : Finset ℂ, (∀ c ∈ S, D (z + c • w) ≠ 0) →
        {t : ℂ | ∃ c ∈ S, D ((z + t • e) + c • w) = 0}.Finite := by
      intro S hSz
      have : {t : ℂ | ∃ c ∈ S, D ((z + t • e) + c • w) = 0} =
          ⋃ c ∈ S, {t : ℂ | D ((z + c • w) + t • e) = 0} := by
        ext t; simp [add_right_comm]
      rw [this]
      exact Set.Finite.biUnion S.finite_toSet (fun c hc => hD _ e (hSz c hc))
    obtain ⟨S0, hS0, hS0z⟩ := bwp_exists_nodes {s | D (z + s • w) = 0} (hw z) k
    refine ⟨R S0, hRdeg S0, fun t0 => ?_⟩
    rw [hupd]
    obtain ⟨S1, hS1, hS1z⟩ := bwp_exists_nodes
      ({s | D (z + s • w) = 0} ∪ {s | D ((z + t0 • e) + s • w) = 0})
      ((hw z).union (hw (z + t0 • e))) k
    have hS1a : ∀ c ∈ S1, D (z + c • w) ≠ 0 := fun c hc h => hS1z c hc (Or.inl h)
    have hS1b : ∀ c ∈ S1, D ((z + t0 • e) + c • w) ≠ 0 := fun c hc h => hS1z c hc (Or.inr h)
    have hS0a : ∀ c ∈ S0, D (z + c • w) ≠ 0 := fun c hc h => hS0z c hc h
    have hRR : R S0 = R S1 := by
      refine bwp_poly_eq_of_eval_eq_off _ _ _ ((hbad S0 hS0a).union (hbad S1 hS1a)) (fun t ht => ?_)
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at ht
      rw [← key S0 hS0 hS0a t ht.1, ← key S1 hS1 hS1a t ht.2]
    rw [hRR, key S1 hS1 hS1a t0 hS1b]
  obtain ⟨F, hF⟩ := bwp_sepPoly k G hsep
  refine ⟨F, fun z hz => ?_⟩
  rw [← hF]
  have := hQ z 0 (by simpa using hz)
  simpa [G] using this

end ReciprocityTheory.MultiplicativeHeights
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

theorem continuous_spherePoint (n : ℕ) : Continuous (spherePoint : UnitSphereC n → Fin n → ℂ) := by
  unfold spherePoint
  fun_prop

theorem sphere_zero_null (hSJ : SJStatement) {n a : ℕ} (g : MvPolynomial (Fin n) ℂ)
    (hg : g.IsHomogeneous a) (u : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ = 1)
    (hgu : MvPolynomial.eval (WithLp.ofLp u) g ≠ 0) :
    sphereProb n {z | MvPolynomial.eval (spherePoint z) g = 0} = 0 := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [EuclideanSpace.norm_eq] at hu
    · exact h
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by simp [hn])
  have h0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    refine mul_ne_zero ?_ (measure_ball_pos _ _ one_pos).ne'
    exact_mod_cast Module.finrank_pos.ne'
  have htop : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  haveI : IsProbabilityMeasure (sphereProb n) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite h0 htop
  set μ := sphereProb n with hμ
  set Z := {z : UnitSphereC n | MvPolynomial.eval (spherePoint z) g = 0} with hZdef
  have hZ : MeasurableSet Z :=
    (isClosed_eq ((MvPolynomial.continuous_eval g).comp (continuous_spherePoint n))
      continuous_const).measurableSet
  obtain ⟨hint, -⟩ := hSJ n a g u hg hu hgu
  have key : ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤
      (∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ) -
        Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖ + (a : ℝ) / 2 * (harmonic (n - 1) : ℝ) := by
    intro c hc
    have hgc : (MvPolynomial.C c * g).IsHomogeneous a := by
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) c).mul hg
    obtain ⟨-, hle⟩ := hSJ n a (MvPolynomial.C c * g) u hgc hu (by simp [hc, hgu])
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C] at hle
    have hpt : ∀ z : UnitSphereC n, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ =
        Zᶜ.indicator (fun _ ↦ Real.log ‖c‖) z + Real.log ‖MvPolynomial.eval (spherePoint z) g‖ := by
      intro z
      by_cases hz : MvPolynomial.eval (spherePoint z) g = 0
      · have hzZ : z ∈ Z := hz
        simp [Set.indicator_apply, hzZ, hz]
      · have hzZ : z ∈ Zᶜ := hz
        rw [Set.indicator_of_mem hzZ, norm_mul,
          Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hz)]
    have hI : ∫ z, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ ∂μ =
        (μ Zᶜ).toReal * Real.log ‖c‖ + ∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ := by
      simp_rw [hpt]
      rw [integral_add ((integrable_const _).indicator hZ.compl) hint,
        integral_indicator_const _ hZ.compl, smul_eq_mul]
      try rfl
    have hcomp : (μ Zᶜ).toReal = 1 - (μ Z).toReal := by
      rw [prob_compl_eq_one_sub hZ, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.toReal_one]
    have hL : Real.log ‖c * MvPolynomial.eval (WithLp.ofLp u) g‖ =
        Real.log ‖c‖ + Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖ := by
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hgu)]
    rw [hI, hcomp, hL] at hle
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤ K := ⟨_, key⟩
  by_contra hne
  have hp : 0 < (μ Z).toReal := ENNReal.toReal_pos hne (measure_ne_top _ _)
  have h1 := hK ((Real.exp ((|K| + 1) / (μ Z).toReal) : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.log_exp] at h1
  have h2 : (μ Z).toReal * ((|K| + 1) / (μ Z).toReal) = |K| + 1 := by
    field_simp
  linarith [le_abs_self K]

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

def blockIndexWeight {B n : ℕ} (b : Fin B) : Fin B × Fin n → ℕ := fun p => if p.1 = b then 1 else 0

theorem weight_lh0BlockWt_apply {B n : ℕ} (b : Fin B) (s : Fin B × Fin n →₀ ℕ) :
    Finsupp.weight (blockIndexWeight (n := n) b) s = ∑ j : Fin n, s (b, j) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [blockIndexWeight, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
  simp

theorem isMultiHomogeneous_iff_forall_weighted_lh0BlockWt {R : Type*} [CommSemiring R] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) R) :
    IsMultiHomogeneous a f ↔ ∀ b, IsWeightedHomogeneous (blockIndexWeight b) f (a b) := by
  simp only [IsMultiHomogeneous, IsWeightedHomogeneous, weight_lh0BlockWt_apply, mem_support_iff]
  constructor
  · intro h b d hd
    exact h d hd b
  · intro h s hs b
    exact h b hs

theorem eval_mul_of_isMultiHomogeneous {B n : ℕ} {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (c : ℂ) (z : Fin B × Fin n → ℂ) :
    eval (fun p => c * z p) g = c ^ (∑ b, a b) * eval z g := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdeg : ∑ p, s p = ∑ b, a b := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b _ => hg s hs b
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

private lemma sum_primitiveRoot_pow_mul_inv_pow_eq_ite {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {a b : ℕ}
    (ha : a < N) (hb : b < N) :
    ∑ j : Fin N, (ζ ^ a * ζ⁻¹ ^ b) ^ (j : ℕ) = if a = b then (N : ℂ) else 0 := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le a) ha
  have hz : ζ ≠ 0 := hζ.ne_zero hN.ne'
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ a * ζ⁻¹ ^ b) ^ j) N]
  split_ifs with hab
  · subst hab
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
    simp
  · have hω1 : ζ ^ a * ζ⁻¹ ^ b ≠ 1 := by
      intro h
      apply hab
      apply hζ.pow_inj ha hb
      rwa [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hz)] at h
    have hωN : (ζ ^ a * ζ⁻¹ ^ b) ^ N = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a, Nat.mul_comm b, pow_mul, pow_mul, inv_pow,
        hζ.pow_eq_one]
      simp
    rw [geom_sum_eq hω1, hωN]
    simp

theorem exists_torus_coeff_le {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    ∃ z : ι → ℂ, (∀ i, ‖z i‖ = 1) ∧ ‖AddMonoidAlgebra.coeff g s‖ ≤ ‖eval z g‖ := by
  classical
  by_cases hs : s ∈ g.support
  swap
  · refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    rw [show AddMonoidAlgebra.coeff g s = 0 by simpa using hs, norm_zero]
    exact norm_nonneg _
  obtain ⟨N, hN⟩ : ∃ N, N = g.totalDegree + 1 := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by omega
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hN0⟩
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hN0
  have hlt : ∀ d ∈ g.support, ∀ i, d i < N := by
    intro d hd i
    have h1 : d i ≤ d.sum fun _ e => e := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    have h2 := le_totalDegree hd
    omega
  let z : (ι → Fin N) → ι → ℂ := fun k i => ζ ^ (k i : ℕ)
  let c : (ι → Fin N) → ℂ := fun k => ∏ i, ζ⁻¹ ^ ((k i : ℕ) * s i)
  have key : ∑ k, eval (z k) g * c k = (N : ℂ) ^ Fintype.card ι * AddMonoidAlgebra.coeff g s := by
    calc ∑ k, eval (z k) g * c k
        = ∑ d ∈ g.support, AddMonoidAlgebra.coeff g d * ∏ i, ∑ j : Fin N, (ζ ^ d i * ζ⁻¹ ^ s i) ^ (j : ℕ) := by
          simp only [eval_eq', Finset.sum_mul, z, c]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_assoc, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm (d i), Nat.mul_comm (s i)]
      _ = ∑ d ∈ g.support, AddMonoidAlgebra.coeff g d * (if d = s then (N : ℂ) ^ Fintype.card ι else 0) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          congr 1
          simp_rw [sum_primitiveRoot_pow_mul_inv_pow_eq_ite hζ (hlt d hd _) (hlt s hs _)]
          split_ifs with hds
          · subst hds
            simp
          · obtain ⟨i, hi⟩ : ∃ i, d i ≠ s i := by
              by_contra h
              push_neg at h
              exact hds (Finsupp.ext h)
            exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
      _ = (N : ℂ) ^ Fintype.card ι * AddMonoidAlgebra.coeff g s := by
          rw [Finset.sum_eq_single s (fun d _ hd => by simp [hd]) (fun h => absurd hs h)]
          simp [mul_comm]
  by_contra hcon
  push_neg at hcon
  have hlt2 : ∀ k, ‖eval (z k) g * c k‖ < ‖AddMonoidAlgebra.coeff g s‖ := by
    intro k
    have hc : ‖c k‖ = 1 := by simp [c, norm_prod, norm_pow, norm_inv, hζn]
    rw [norm_mul, hc, mul_one]
    exact hcon (z k) (fun i => by simp [z, norm_pow, hζn])
  have hsum := norm_sum_le (Finset.univ : Finset (ι → Fin N)) (fun k => eval (z k) g * c k)
  have hsum2 : ∑ k, ‖eval (z k) g * c k‖ < ∑ _k : ι → Fin N, ‖AddMonoidAlgebra.coeff g s‖ :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => hlt2 k)
  rw [key, norm_mul, norm_pow, Complex.norm_natCast] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul] at hsum2
  push_cast at hsum2
  linarith

end ReciprocityTheory.MultiplicativeHeights
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open Finset

theorem exp_torus_mean_le_l2_of_lex {ι : Type} [Fintype ι] [LinearOrder ι]
    (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) (F : MvPolynomial ι ℂ) (hF : F ≠ 0) (s : ι →₀ ℕ)
    (Q : MvPolynomial ι ℂ) (hQ : ∀ t ∈ Q.support, toLex s < toLex t) :
    Real.exp (torusMean F) ≤ polyL2 (F * (MvPolynomial.monomial s 1 - Q)) := by
  classical
  set P := MvPolynomial.monomial s (1 : ℂ) - Q with hPdef
  have hsQ : s ∉ Q.support := fun h => lt_irrefl _ (hQ s h)
  have hQs : Q.coeff s = 0 := MvPolynomial.notMem_support_iff.mp hsQ
  have hPs : P.coeff s = 1 := by
    rw [hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl, hQs, sub_zero]
  have hP0 : P ≠ 0 := fun h => by rw [h, MvPolynomial.coeff_zero] at hPs; exact zero_ne_one hPs
  have hsupp : s ∈ P.support := by rw [MvPolynomial.mem_support_iff, hPs]; exact one_ne_zero
  have hlex : Real.log ‖P.coeff s‖ ≤ torusMean P := by
    apply hLex ι P s hsupp
    intro t ht hts
    have htQ : t ∈ Q.support := by
      by_contra h
      have h0 : P.coeff t = 0 := by
        rw [hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_neg (Ne.symm hts),
          MvPolynomial.notMem_support_iff.mp h, sub_zero]
      exact (MvPolynomial.mem_support_iff.mp ht) h0
    obtain ⟨i, h1, h2⟩ := hQ t htQ
    exact ⟨i, h1, h2⟩
  rw [hPs, norm_one, Real.log_one] at hlex
  have hFP : F * P ≠ 0 := mul_ne_zero hF hP0
  have hmul := (hBasic ι).2.1 F P hF hP0
  have hL := (hL2 ι (F * P)).1 hFP
  have hpos : 0 < polyL2 (F * P) := by
    unfold polyL2
    apply Real.sqrt_pos.mpr
    obtain ⟨t, hne⟩ := MvPolynomial.ne_zero_iff.mp hFP
    have ht : t ∈ (F * P).support := MvPolynomial.mem_support_iff.mpr hne
    calc (0 : ℝ) < ‖(F * P).coeff t‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
      _ ≤ _ := Finset.single_le_sum (f := fun s => ‖(F * P).coeff s‖ ^ 2)
          (fun _ _ => by positivity) ht
  calc Real.exp (torusMean F) ≤ Real.exp (torusMean (F * P)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ polyL2 (F * P) := by
      rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hL

def coeffVec {ι : Type*} (T : Finset (ι →₀ ℕ)) : MvPolynomial ι ℂ →ₗ[ℂ] EuclideanSpace ℂ T where
  toFun P := WithLp.toLp 2 fun t : T => P.coeff t
  map_add' P Q := by ext t; simp
  map_smul' c P := by ext t; simp

theorem coeffVec_apply {ι : Type*} (T : Finset (ι →₀ ℕ)) (P : MvPolynomial ι ℂ) (t : T) :
    coeffVec T P t = P.coeff t := rfl

theorem norm_coeffVec {ι : Type*} (T : Finset (ι →₀ ℕ)) (P : MvPolynomial ι ℂ)
    (hP : P.support ⊆ T) : ‖coeffVec T P‖ = polyL2 P := by
  classical
  rw [EuclideanSpace.norm_eq, polyL2]
  congr 1
  simp only [coeffVec_apply]
  rw [Finset.sum_coe_sort T (fun t => ‖P.coeff t‖ ^ 2)]
  exact (Finset.sum_subset hP (fun t _ ht => by
    rw [MvPolynomial.notMem_support_iff.mp ht, norm_zero]; ring)).symm

theorem polyInner_eq_inner {ι : Type*} (T : Finset (ι →₀ ℕ)) (P Q : MvPolynomial ι ℂ)
    (hP : P.support ⊆ T) : polyInner P Q = inner ℂ (coeffVec T Q) (coeffVec T P) := by
  classical
  rw [PiLp.inner_apply]
  simp only [coeffVec_apply, RCLike.inner_apply, polyInner]
  rw [Finset.sum_coe_sort T (fun t => P.coeff t * (starRingEnd ℂ) (Q.coeff t))]
  exact Finset.sum_subset hP (fun t _ ht => by rw [MvPolynomial.notMem_support_iff.mp ht, zero_mul])

theorem exists_lex_enum {ι : Type*} [LinearOrder ι] (S : Finset (ι →₀ ℕ)) :
    ∃ m : Fin S.card → (ι →₀ ℕ), (∀ k, m k ∈ S) ∧ Function.Injective m ∧
      ∀ j k, j < k → toLex (m k) < toLex (m j) := by
  classical
  let S' : Finset (Lex (ι →₀ ℕ)) := S.map toLex.toEmbedding
  have hc : S'.card = S.card := Finset.card_map _
  let f := S'.orderEmbOfFin hc
  refine ⟨fun k => ofLex (f (Fin.rev k)), ?_, ?_, ?_⟩
  · intro k
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp (S'.orderEmbOfFin_mem hc (Fin.rev k))
    have : ofLex (f (Fin.rev k)) = a := by rw [← he]; rfl
    show ofLex (f (Fin.rev k)) ∈ S
    rw [this]; exact ha
  · intro a b h
    exact Fin.rev_injective (f.injective h)
  · intro j k hjk
    show f (Fin.rev k) < f (Fin.rev j)
    exact f.strictMono (Fin.rev_lt_rev.mpr hjk)

end ReciprocityTheory.MultiplicativeHeights
end
