module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Lemmata.FirstBlockLemmaJ.Imports
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD

open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G

attribute [local instance] Over.cartesianMonoidalCategory

section Alg

variable {V : Type} [CommRing V]

theorem aeval_tan {ι : Type} [DecidableEq ι] (ℓ : ι) (P : MvPolynomial ι V) :
    aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber V) else 0) P =
      algebraMap V (DualNumber V) (constantCoeff P) + AddMonoidAlgebra.coeff P (Finsupp.single ℓ 1) • DualNumber.eps := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.constantCoeff_C, MvPolynomial.coeff_C,
      if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, zero_smul, add_zero]
  | add p q hp hq => rw [map_add (f := _), hp, hq, map_add (f := _), map_add (f := _), MvPolynomial.coeff_add, add_smul]; abel
  | mul_X p n hp =>
    rw [map_mul, hp, MvPolynomial.aeval_X, map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, zero_add,
      MvPolynomial.coeff_mul_X']
    by_cases h : n = ℓ
    · subst h
      have hs : n ∈ (Finsupp.single n (1 : ℕ)).support := by simp
      rw [if_pos rfl, if_pos hs, tsub_self, ← MvPolynomial.constantCoeff_eq, add_mul, smul_mul_assoc,
        DualNumber.eps_mul_eps, smul_zero, add_zero, Algebra.smul_def]
    · have : n ∉ (Finsupp.single ℓ 1).support := by simp [Finsupp.support_single_ne_zero, Ne.symm h, h]
      simp [h, this]

theorem coeff_psTrunc {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι V) (e : ι →₀ ℕ)
    (he : e ∈ degLE m) : AddMonoidAlgebra.coeff (psTrunc m f) e = MvPowerSeries.coeff e f := by
  simp [psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he]

theorem single_mem_degLE {ι : Type} [Fintype ι] [DecidableEq ι] (ℓ : ι) : Finsupp.single ℓ 1 ∈ degLE (ι := ι) 1 := by
  simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨⟨fun i => if i = ℓ then 1 else 0, ?_⟩, ?_⟩
  · ext i
    by_cases h : i = ℓ
    · subst h; simp
    · simp [h, Finsupp.single_apply, Ne.symm h]
  · simp [Finsupp.sum_single_index]

theorem ker_jetAug_sq {κ : Type} : (RingHom.ker (jetAug (R := V) (ι := κ) (m := 1))) ^ (1 + 1) = ⊥ := by
  exact ReciprocityTheory.ChartRestriction.G.Chart.ker_jetAug_pow κ 1

end Alg

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
end
end

section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open Metric Set Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem eq_zero_on_ball {g : V → ℂ} {x : V} {ε : ℝ} (hg : DifferentiableOn ℂ g (ball x ε)) {z : V}
    (hz : z ∈ ball x ε) (hgz : g =ᶠ[𝓝 z] 0) : ∀ y ∈ ball x ε, g y = 0 := by
  first | exact Bl.FirstBlockLemmaJ.goal1 .. | (apply Bl.FirstBlockLemmaJ.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaJ.goal1 <;> assumption)

theorem eq_zero_of_eventually {U : Set V} (hU : IsOpen U) (hc : IsPreconnected U) {g : V → ℂ}
    (hg : DifferentiableOn ℂ g U) {x0 : V} (hx0 : x0 ∈ U) (h0 : g =ᶠ[𝓝 x0] 0) : ∀ y ∈ U, g y = 0 := by
  have hZo : IsOpen {x : V | g =ᶠ[𝓝 x] 0} := isOpen_setOfPred_eventually_nhds
  have hsub : U ⊆ {x : V | g =ᶠ[𝓝 x] 0} := by
    refine hc.subset_of_closure_inter_subset hZo ⟨x0, hx0, h0⟩ ?_
    rintro x ⟨hxc, hxU⟩
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU x hxU
    obtain ⟨z, hzZ, hzd⟩ := Metric.mem_closure_iff.mp hxc ε hε
    have hzb : z ∈ ball x ε := by rw [mem_ball, dist_comm]; exact hzd
    have hall := eq_zero_on_ball (hg.mono hb) hzb hzZ
    exact Filter.eventually_of_mem (ball_mem_nhds x hε) hall
  intro y hy
  exact (hsub hy).self_of_nhds

theorem eq_zero_of_mul_eq_zero {U : Set V} (hU : IsOpen U) (hc : IsPreconnected U) {f g : V → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hfg : ∀ y ∈ U, f y * g y = 0)
    {x0 : V} (hx0 : x0 ∈ U) (h0 : f x0 ≠ 0) : ∀ y ∈ U, g y = 0 := by
  refine eq_zero_of_eventually hU hc hg hx0 ?_
  have h1 : ∀ᶠ y in 𝓝 x0, f y ≠ 0 := (hf.continuousOn.continuousAt (hU.mem_nhds hx0)).eventually_ne h0
  filter_upwards [h1, hU.mem_nhds hx0] with y hy hyU
  exact (mul_eq_zero.mp (hfg y hyU)).resolve_left hy

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end

section

set_option autoImplicit false

noncomputable section

open NumberField

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA

variable {E : Type} [Field E] [NumberField E]

private theorem repr_trDual_lemma {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E)
    (x : E) (j : ι) : (TB.trDual b).repr x j = Algebra.trace ℚ E (x * b j) := by
  have h := LinearMap.BilinForm.dualBasis_repr_apply
    (traceForm_nondegenerate ℚ E) b x j
  rw [Algebra.traceForm_apply] at h
  exact h

theorem sum_dual_mul {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) :
    ∑ i, TB.trDual b i * b i = 1 := by
  have key : ∀ y : E, Algebra.trace ℚ E ((∑ i, TB.trDual b i * b i - 1) * y) = 0 := by
    intro y

    rw [sub_mul, one_mul, map_sub, Algebra.trace_eq_matrix_trace (TB.trDual b) y, Matrix.trace,
    Finset.sum_mul, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, repr_trDual_lemma]
    congr 1
    ring
  have h0 : ∑ i, TB.trDual b i * b i - 1 = 0 := by
    apply (TB.trDual b).ext_elem
    intro j
    rw [repr_trDual_lemma, key, map_zero, Finsupp.zero_apply]
  exact sub_eq_zero.1 h0

theorem dual_expand {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (x : E) :
    x = ∑ j, Algebra.trace ℚ E (x * b j) • TB.trDual b j := by
  conv_lhs => rw [← (TB.trDual b).sum_repr x]
  simp only [repr_trDual_lemma]

theorem trace_dual_mul {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (i k : ι) :
    Algebra.trace ℚ E (TB.trDual b i * b k) = if k = i then 1 else 0 := by
  rw [← repr_trDual_lemma, Module.Basis.repr_self]
  by_cases hki : k = i
  · subst hki; simp
  · rw [if_neg hki, Finsupp.single_apply, if_neg (Ne.symm hki)]

theorem idem_data_basis {k V : Type} [Field k] [CommRing V] [Algebra V k] (ψ : E →+* k)
    (hint : ∀ x : 𝓞 E, ∃ v : V, algebraMap V k v = ψ (algebraMap (𝓞 E) E x)) (w : V)
    (hw : algebraMap V k w * (((discr E).natAbs : ℕ) : k) = 1) :
    ∃ (b : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E) (c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → V),
      (∑ i, algebraMap V k (c i) * ψ (algebraMap (𝓞 E) E (b i)) = 1) ∧
      ∀ a : 𝓞 E, ∃ m : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ,
        (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap V k (c i) = ψ (algebraMap (𝓞 E) E a) * algebraMap V k (c j) := by
  classical
  set bZ := NumberField.RingOfIntegers.basis E with hbZdef
  set bQ := NumberField.integralBasis E with hbQdef
  have hbQ_apply : ∀ i, bQ i = algebraMap (𝓞 E) E (bZ i) := fun i => NumberField.integralBasis_apply E i
  have hint_tr : ∀ x : 𝓞 E, ∃ g : ℤ, (g : ℚ) = Algebra.trace ℚ E (algebraMap (𝓞 E) E x) := by
    intro x
    have hx : IsIntegral ℤ (algebraMap (𝓞 E) E x) := (Algebra.IsIntegral.isIntegral x).algebraMap
    have ht : IsIntegral ℤ (Algebra.trace ℚ E (algebraMap (𝓞 E) E x)) := Algebra.isIntegral_trace hx
    obtain ⟨g, hg⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 ht
    exact ⟨g, by rw [← hg, eq_intCast]⟩
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℤ,
      ∀ i j, (G i j : ℚ) = Algebra.trace ℚ E (algebraMap (𝓞 E) E (bZ i) * algebraMap (𝓞 E) E (bZ j)) :=
    ⟨fun i j => (hint_tr (bZ i * bZ j)).choose, fun i j => by
      rw [← map_mul]; exact (hint_tr (bZ i * bZ j)).choose_spec⟩
  have hD : G.det = NumberField.discr E := by
    have hm : (Int.castRingHom ℚ).mapMatrix G = Algebra.traceMatrix ℚ bQ := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        hbQ_apply, hbQ_apply, ← hG]
      simp
    have h1 : ((G.det : ℤ) : ℚ) = (NumberField.discr E : ℚ) := by
      rw [NumberField.coe_discr, ← hbQdef, Algebra.discr_def, ← hm, ← RingHom.map_det]
      simp
    exact_mod_cast h1
  obtain ⟨z, hzdef⟩ : ∃ z : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E,
      ∀ i, z i = ∑ j, G.adjugate i j • bZ j := ⟨_, fun i => rfl⟩
  have key : ∀ i k, Algebra.trace ℚ E (algebraMap (𝓞 E) E (z i) * bQ k) = if i = k then (G.det : ℚ) else 0 := by
    intro i k
    have h1 : (G.adjugate * G) i k = if i = k then G.det else 0 := by
      rw [Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h2 : Algebra.trace ℚ E (algebraMap (𝓞 E) E (z i) * bQ k) = (((G.adjugate * G) i k : ℤ) : ℚ) := by

      rw [hzdef, hbQ_apply, Matrix.mul_apply, map_sum, Finset.sum_mul, map_sum, Int.cast_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_zsmul, smul_mul_assoc, map_zsmul, ← hG, zsmul_eq_mul, Int.cast_mul]
    rw [h2, h1]
    split_ifs <;> simp
  have hz : ∀ i, algebraMap (𝓞 E) E (z i) = (G.det : E) * TB.trDual bQ i := by
    intro i
    apply (TB.trDual bQ).ext_elem
    intro j
    rw [repr_trDual_lemma, repr_trDual_lemma, key i j, mul_assoc, ← zsmul_eq_mul, map_zsmul, trace_dual_mul bQ i j]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij), smul_zero]
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε * G.det = (((NumberField.discr E).natAbs : ℕ) : ℤ) := by
    rw [hD]
    rcases Int.natAbs_eq (NumberField.discr E) with h | h
    · exact ⟨1, by linarith⟩
    · exact ⟨-1, by linarith⟩
  choose v hv using fun i => hint ((ε : 𝓞 E) * z i)
  have hc : ∀ i, algebraMap V k (w * v i) = ψ (TB.trDual bQ i) := by
    intro i
    have e1 : algebraMap (𝓞 E) E ((ε : 𝓞 E) * z i) =
        (((NumberField.discr E).natAbs : ℕ) : E) * TB.trDual bQ i := by
      rw [map_mul, map_intCast, hz i, ← mul_assoc, ← Int.cast_mul, hε, Int.cast_natCast]
    rw [map_mul, hv i, e1, map_mul, map_natCast, ← mul_assoc, hw, one_mul]
  refine ⟨bZ, fun i => w * v i, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one ψ, ← sum_dual_mul bQ, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hc i, map_mul, hbQ_apply]
  · intro a
    refine ⟨fun i j => bZ.repr (a * bZ i) j, fun i => (bZ.sum_repr (a * bZ i)).symm, fun j => ?_⟩
    have hm : ∀ i, Algebra.trace ℚ E (algebraMap (𝓞 E) E a * TB.trDual bQ j * bQ i) =
        ((bZ.repr (a * bZ i) j : ℤ) : ℚ) := by
      intro i
      have hs := bZ.sum_repr (a * bZ i)
      rw [mul_comm (algebraMap (𝓞 E) E a), mul_assoc, hbQ_apply i, ← map_mul (algebraMap (𝓞 E) E)]
      conv_lhs => rw [← hs]

      rw [map_sum, Finset.mul_sum, map_sum]
      simp only [map_zsmul, mul_smul_comm, ← hbQ_apply, trace_dual_mul]
      simp
    simp only [hc]

    rw [← map_mul ψ, dual_expand bQ (algebraMap (𝓞 E) E a * TB.trDual bQ j), map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hm i, Int.cast_smul_eq_zsmul, map_zsmul, zsmul_eq_mul]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem map_gl_mul (τ : E →+* ℂ) (γ₁ γ₂ : GL (Fin r) E) :
    ((γ₁ * γ₂ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ =
      (γ₁ : Matrix (Fin r) (Fin r) E).map τ * (γ₂ : Matrix (Fin r) (Fin r) E).map τ := by
  rw [Units.val_mul, Matrix.map_mul]

theorem map_gl_inv_mul (τ : E →+* ℂ) (γ : GL (Fin r) E) :
    ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * (γ : Matrix (Fin r) (Fin r) E).map τ = 1 := by
  rw [← map_gl_mul, inv_mul_cancel, Units.val_one, Matrix.map_one]
  all_goals first | exact τ.map_zero | exact τ.map_one

def TSet (Ψ : Finset (E →+* ℂ)) (g : Matrix (Fin r) (Fin r) E) : Set (Frame Ψ r) :=
  {x | ∀ τ : Ψ, ∀ a c : Fin r, c < a → (adjugate (mat x τ) * g.map τ.1 * mat x τ) a c = 0}

theorem isClosed_TSet (Ψ : Finset (E →+* ℂ)) (g : Matrix (Fin r) (Fin r) E) : IsClosed (TSet Ψ g) := by
  simp only [TSet, Set.setOf_forall]
  refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
    isClosed_iInter fun _ => ?_
  have hm : Continuous fun x : Frame Ψ r => mat x τ :=
    continuous_pi fun i => continuous_pi fun j => by
      simp only [mat, Matrix.of_apply]
      fun_prop
  exact isClosed_eq
    (((hm.matrix_adjugate.matrix_mul continuous_const).matrix_mul hm).matrix_elem a c)
    continuous_const

theorem mem_TSet (Ψ : Finset (E →+* ℂ)) (γ γ' : GL (Fin r) E) {x b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (h : lact γ x = rmul (lact γ' x) b) : x ∈ TSet Ψ ((γ'⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
  change ∀ τ : Ψ, ∀ a c : Fin r, c < a →
    (adjugate (mat x τ) * ((γ'⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) a c = 0
  intro τ a c hca
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) := by
    have h0 := congrArg (fun y => mat y τ) h
    rw [← Matrix.mul_assoc]
    exact h0
  have h2 : adjugate (mat x τ) * ((γ'⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat x τ = (mat x τ).det • mat b τ := by
    rw [map_gl_mul]
    simp only [Matrix.mul_assoc]
    rw [h1, ← Matrix.mul_assoc _ ((γ' : Matrix (Fin r) (Fin r) E).map τ.1), map_gl_inv_mul,
      Matrix.one_mul, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [h2, Matrix.smul_apply, smul_eq_mul]
  have hB : b τ a c = 0 := (hb τ).2 a c hca
  simp [mat, hB]

theorem scalar_step {Ψ : Finset (E →+* ℂ)} (τ₀ : Ψ) (g : Matrix (Fin r) (Fin r) E) {W : Set (Frame Ψ r)}
    (hWo : IsOpen W) (hWT : W ⊆ TSet Ψ g) {y : Frame Ψ r} (hyW : y ∈ W) (hy : (mat y τ₀).det ≠ 0) :
    ∃ κ : ℂ, g.map τ₀.1 = κ • 1 := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨0, by ext a; exact Fin.elim0 a⟩
  set M : Matrix (Fin r) (Fin r) ℂ := g.map τ₀.1 with hM
  let i0 : Fin r := ⟨0, hr⟩
  let fr : (Fin r → ℂ) → Frame Ψ r := fun v τ a c => if τ = τ₀ ∧ c = i0 then v a else y τ a c
  let v₀ : Fin r → ℂ := fun a => y τ₀ a i0
  have hfr : Continuous fr := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    by_cases h : τ = τ₀ ∧ c = i0
    · simp only [fr, if_pos h]
      exact continuous_apply a
    · simp only [fr, if_neg h]
      exact continuous_const
  have hfr0 : fr v₀ = y := by
    funext τ a c
    by_cases h : τ = τ₀ ∧ c = i0
    · obtain ⟨rfl, rfl⟩ := h
      simp [fr, v₀]
    · simp [fr, h]
  have hdet : Continuous fun v => (mat (fr v) τ₀).det := by
    refine Continuous.matrix_det ?_
    exact continuous_pi fun a => continuous_pi fun c => by
      simp only [mat, Matrix.of_apply]
      exact (continuous_apply c).comp ((continuous_apply a).comp ((continuous_apply τ₀).comp hfr))
  have hW1 : ∀ᶠ v in nhds v₀, fr v ∈ W := (hfr.tendsto' v₀ y hfr0) (hWo.mem_nhds hyW)
  have hP : ∀ᶠ v in nhds v₀, fr v ∈ W ∧ (mat (fr v) τ₀).det ≠ 0 :=
    hW1.and (hdet.continuousAt.eventually_ne (by
      show (mat (fr v₀) τ₀).det ≠ 0
      rw [hfr0]
      exact hy))
  have hB : ∀ v, fr v ∈ W → (mat (fr v) τ₀).det ≠ 0 → ∃ l : ℂ, M *ᵥ v = l • v := by
    intro v hvW hd
    have hT : ∀ τ : Ψ, ∀ a c : Fin r, c < a →
        (adjugate (mat (fr v) τ) * g.map τ.1 * mat (fr v) τ) a c = 0 := hWT hvW
    set X := mat (fr v) τ₀ with hX
    have hcol : ∀ a, X a i0 = v a := fun a => by simp [hX, mat, fr]
    set z := X.adjugate *ᵥ (M *ᵥ v) with hz
    have hz0 : ∀ a, a ≠ i0 → z a = 0 := by
      intro a ha
      have h1 := hT τ₀ a i0 (by
        rw [Fin.lt_iff_val_lt_val]
        exact Nat.pos_of_ne_zero fun h => ha (Fin.ext h))
      have h2 : z a = (X.adjugate * M * X) a i0 := by
        rw [hz, Matrix.mulVec_mulVec]
        simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hcol]
      rw [h2]
      exact h1
    have hXz : X *ᵥ z = X.det • (M *ᵥ v) := by
      calc X *ᵥ z = (X * X.adjugate) *ᵥ (M *ᵥ v) := by
            rw [hz]
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = X.det • (M *ᵥ v) := by
            rw [Matrix.mul_adjugate]
            first
              | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
              | (ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])
    have hXz' : X *ᵥ z = z i0 • v := by
      funext a
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i0 (fun b _ hb => by rw [hz0 b hb, mul_zero])
        (fun h => absurd (Finset.mem_univ i0) h), hcol, mul_comm]
    refine ⟨z i0 / X.det, ?_⟩
    funext a
    have ha := congrFun (hXz.symm.trans hXz') a
    simp only [Pi.smul_apply, smul_eq_mul] at ha ⊢
    rw [div_mul_eq_mul_div, eq_div_iff hd]
    linear_combination ha
  have hQ : ∀ v, fr v ∈ W → (mat (fr v) τ₀).det ≠ 0 →
      ∀ a b, (M *ᵥ v) a * v b = (M *ᵥ v) b * v a := by
    intro v h1 h2 a b
    obtain ⟨l, hl⟩ := hB v h1 h2
    rw [hl]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hall : ∀ u : Fin r → ℂ, ∀ a b, (M *ᵥ u) a * u b = (M *ᵥ u) b * u a := by
    intro u a b
    have t1 : Filter.Tendsto (fun s : ℂ => v₀ + s • u) (nhds 0) (nhds v₀) :=
      Continuous.tendsto' (by fun_prop) 0 v₀ (by simp)
    have t2 : Filter.Tendsto (fun s : ℂ => v₀ + (2 * s) • u) (nhds 0) (nhds v₀) :=
      Continuous.tendsto' (by fun_prop) 0 v₀ (by simp)
    have e1 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, fr (v₀ + s • u) ∈ W ∧ (mat (fr (v₀ + s • u)) τ₀).det ≠ 0 :=
      nhdsWithin_le_nhds (t1.eventually hP)
    have e2 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ,
        fr (v₀ + (2 * s) • u) ∈ W ∧ (mat (fr (v₀ + (2 * s) • u)) τ₀).det ≠ 0 :=
      nhdsWithin_le_nhds (t2.eventually hP)
    have e3 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, s ≠ 0 := self_mem_nhdsWithin
    obtain ⟨s, hs1, hs2, hs0⟩ := (e1.and (e2.and e3)).exists
    have q0 := hQ v₀ (by rw [hfr0]; exact hyW) (by rw [hfr0]; exact hy) a b
    have q1 := hQ _ hs1.1 hs1.2 a b
    have q2 := hQ _ hs2.1 hs2.2 a b
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at q1 q2
    have key : (2 * s ^ 2) * ((M *ᵥ u) a * u b - (M *ᵥ u) b * u a) = 0 := by
      linear_combination q2 - 2 * q1 + q0
    have hs2' : (2 * s ^ 2 : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hs0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hs2')
  have hcolv : ∀ j i, (M *ᵥ Pi.single j 1) i = M i j := by
    intro j i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hoff : ∀ a b, a ≠ b → M a b = 0 := by
    intro a b hab
    have h := hall (Pi.single b 1) a b
    rw [hcolv, hcolv] at h
    simpa [Pi.single_apply, hab] using h
  have hdiag : ∀ a b, M a a = M b b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    have h := hall (Pi.single a 1 + Pi.single b 1) a b
    rw [Matrix.mulVec_add] at h
    simp only [Pi.add_apply, hcolv] at h
    simp [Pi.single_apply, hab, Ne.symm hab, hoff a b hab, hoff b a (Ne.symm hab)] at h
    linear_combination h
  refine ⟨M i0 i0, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [hdiag a i0]
  · simp [hoff a b hab, hab]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
