module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle012
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle002
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XFibMdisc
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
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.UniformSpace.Uniformizable
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul

@[expose] public section

section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem pker_eq {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) (t : ℝ) :
    pker ρ w t = (ρ ^ 2 - ‖w‖ ^ 2) / ‖circleMap 0 ρ t - w‖ ^ 2 := by
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  simp only [pker, poissonKernel_def, sub_zero, h]

theorem sub_le_norm_circleMap_sub {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) (t : ℝ) :
    ρ - ‖w‖ ≤ ‖circleMap 0 ρ t - w‖ := by
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  have h2 := norm_sub_norm_le (circleMap (0 : ℂ) ρ t) w
  rwa [h] at h2

theorem continuous_pker {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : ‖w‖ < ρ) :
    Continuous (pker ρ w) := by
  have h : pker ρ w = fun t => (ρ ^ 2 - ‖w‖ ^ 2) / ‖circleMap 0 ρ t - w‖ ^ 2 :=
    funext (pker_eq hρ w)
  rw [h]
  refine continuous_const.div
    (((continuous_circleMap 0 ρ).sub continuous_const).norm.pow 2) ?_
  intro t
  have h1 := sub_le_norm_circleMap_sub hρ w t
  have h2 : 0 < ‖circleMap (0 : ℂ) ρ t - w‖ := by linarith
  positivity

theorem exists_abs_pker_le {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : ‖w‖ < ρ) :
    ∃ K : ℝ, ∀ t, |pker ρ w t| ≤ K := by
  refine ⟨(ρ ^ 2 - ‖w‖ ^ 2) / (ρ - ‖w‖) ^ 2, fun t => ?_⟩
  have h1 := sub_le_norm_circleMap_sub hρ w t
  have h0 : 0 < ρ - ‖w‖ := by linarith
  have hn : 0 ≤ ρ ^ 2 - ‖w‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg w) hw.le 2
    linarith
  rw [pker_eq hρ, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left hn (by positivity) (pow_le_pow_left₀ h0.le h1 2)

theorem continuous_torusPt {n : ℕ} (ρ : ℝ) : Continuous (torusPt (n := n) ρ) :=
  continuous_pi fun i => (continuous_circleMap 0 ρ).comp (continuous_apply i)

theorem circleMap_mem {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (t : ℝ) :
    circleMap (0 : ℂ) ρ t ≠ 0 ∧ ‖circleMap (0 : ℂ) ρ t‖ < R := by
  refine ⟨circleMap_ne_center hρ.ne', ?_⟩
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  rwa [h]

theorem torusPt_mem_punct {n : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (θ : Fin n → ℝ) :
    torusPt ρ θ ∈ punct R := fun i => circleMap_mem hρ hρR (θ i)

theorem cons_mem_punct {n : ℕ} {R : ℝ} {c : ℂ} {y : Fin n → ℂ} (hc : c ≠ 0 ∧ ‖c‖ < R)
    (hy : y ∈ punct R) : (Fin.cons c y : Fin (n + 1) → ℂ) ∈ punct R := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hc
  · simpa using hy j

theorem continuous_cons_pair {n : ℕ} {α : Type*} [TopologicalSpace α] :
    Continuous (fun p : α × (Fin n → α) => (Fin.cons p.1 p.2 : Fin (n + 1) → α)) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply j).comp continuous_snd

theorem integral_pi_cons {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ)
    (hF : Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
      (angMeas.prod (Measure.pi fun _ : Fin n => angMeas))) :
    ∫ θ, F θ ∂(Measure.pi fun _ : Fin (n + 1) => angMeas) =
      ∫ t, ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) ∂angMeas := by
  have mp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
      (angMeas.prod (Measure.pi fun _ : Fin n => angMeas))
      (Measure.pi fun _ : Fin (n + 1) => angMeas) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => angMeas) 0).symm _
  have he : ∀ p : ℝ × (Fin n → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p =
        Fin.cons p.1 p.2 := by
    rintro ⟨a, b⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove]
  rw [← mp.integral_comp']
  simp only [he]
  exact integral_prod _ hF

theorem polyPoisson_eq_self : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℝ) (ρ R M : ℝ), 0 < ρ → ρ < R →
    ContinuousOn f (punct R) → SepHarm R f → (∀ z ∈ punct R, |f z| ≤ M) →
    ∀ z ∈ punct ρ, polyPoisson ρ f z = f z := by
  intro n
  induction n with
  | zero =>
    intro f ρ R M _ _ _ _ _ z _
    have h : ∀ θ : Fin 0 → ℝ, (∏ i, pker ρ (z i) (θ i)) * f (torusPt ρ θ) = f z := by
      intro θ
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
      rw [Subsingleton.elim (torusPt ρ θ) z]
    simp only [polyPoisson, h]
    simp
  | succ n ih =>
    intro f ρ R M hρ hρR hc hs hb z hz
    have hz0 := hz 0
    have hzt : Fin.tail z ∈ punct ρ := fun i => hz i.succ
    have hztR : Fin.tail z ∈ punct R := fun i => ⟨(hzt i).1, (hzt i).2.trans hρR⟩
    have hslice : ∀ t, polyPoisson ρ (fun y => f (Fin.cons (circleMap 0 ρ t) y)) (Fin.tail z) =
        f (Fin.cons (circleMap 0 ρ t) (Fin.tail z)) := by
      intro t
      have hcm := circleMap_mem (t := t) hρ hρR
      refine ih _ ρ R M hρ hρR ?_ ?_ ?_ _ hzt
      · have hcont : Continuous (fun y : Fin n → ℂ =>
            (Fin.cons (circleMap 0 ρ t) y : Fin (n + 1) → ℂ)) :=
          continuous_cons_pair.comp (continuous_const.prodMk continuous_id)
        exact hc.comp hcont.continuousOn (fun y hy => cons_mem_punct hcm hy)
      · intro y hy i
        have h := hs _ (cons_mem_punct hcm hy) i.succ
        simp only [Fin.cons_succ] at h
        simpa only [Fin.cons_update] using h
      · exact fun y hy => hb _ (cons_mem_punct hcm hy)
    have hone := GlobalTheory.CompanionTheory.Ar.PuncturedDisc.poisson_formula_punctured (fun w => f (Fin.cons w (Fin.tail z))) ρ R M hρ hρR
      (fun w hw0 hwR => by
        have h := hs _ (cons_mem_punct ⟨hw0, hwR⟩ hztR) 0
        simpa only [Fin.update_cons_zero, Fin.cons_zero] using h)
      (fun w hw0 hwR => hb _ (cons_mem_punct ⟨hw0, hwR⟩ hztR))
      (z 0) hz0.1 hz0.2
    simp only [Fin.cons_self_tail] at hone
    set F : (Fin (n + 1) → ℝ) → ℝ :=
      fun θ => (∏ i, pker ρ (z i) (θ i)) * f (torusPt ρ θ) with hFdef
    have hFc : Continuous F :=
      (continuous_finsetProd _ fun i _ =>
        (continuous_pker hρ (hz i).2).comp (continuous_apply i)).mul
      (hc.comp_continuous (continuous_torusPt ρ) (torusPt_mem_punct hρ hρR))
    have hFb : ∃ K, ∀ θ, |F θ| ≤ K := by
      choose K hK using fun i => exists_abs_pker_le hρ (hz i).2
      refine ⟨(∏ i, K i) * M, fun θ => ?_⟩
      rw [hFdef]
      simp only [abs_mul, Finset.abs_prod]
      have hM : 0 ≤ M := (abs_nonneg _).trans (hb _ (torusPt_mem_punct hρ hρR θ))
      have hK0 : 0 ≤ ∏ i, K i :=
        Finset.prod_nonneg fun i _ => (abs_nonneg _).trans (hK i 0)
      exact mul_le_mul
        (Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hK i _))
        (hb _ (torusPt_mem_punct hρ hρR θ)) (abs_nonneg _) hK0
    obtain ⟨K, hK⟩ := hFb
    have hint : Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
        (angMeas.prod (Measure.pi fun _ : Fin n => angMeas)) :=
      Integrable.of_bound (hFc.comp continuous_cons_pair).aestronglyMeasurable K
        (ae_of_all _ fun p => hK _)
    have hFcons : ∀ t θ', F (Fin.cons t θ') = pker ρ (z 0) t *
        ((∏ i, pker ρ (Fin.tail z i) (θ' i)) *
          f (Fin.cons (circleMap 0 ρ t) (torusPt ρ θ'))) := by
      intro t θ'
      have ht : torusPt ρ (Fin.cons t θ' : Fin (n + 1) → ℝ) =
          Fin.cons (circleMap 0 ρ t) (torusPt ρ θ') := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusPt]
      simp only [hFdef, ht, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, mul_assoc]
    calc polyPoisson ρ f z
        = ∫ t, ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) ∂angMeas :=
          integral_pi_cons F hint
      _ = ∫ t, pker ρ (z 0) t * f (Fin.cons (circleMap 0 ρ t) (Fin.tail z)) ∂angMeas := by
          refine integral_congr_ae (ae_of_all _ fun t => ?_)
          have h : ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) =
              pker ρ (z 0) t *
                polyPoisson ρ (fun y => f (Fin.cons (circleMap 0 ρ t) y)) (Fin.tail z) := by
            simp only [hFcons]
            rw [integral_const_mul]
            rfl
          simp only [h, hslice t]
      _ = f z := hone

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly

noncomputable section

lemma exists_perm_of_sum_single {d : ℕ} {τ τ' : Fin d → Option (Fin 3)}
    (h : ∑ t, Finsupp.single (τ t) (1 : ℕ) = ∑ t, Finsupp.single (τ' t) (1 : ℕ)) :
    ∃ π : Equiv.Perm (Fin d), ∀ t, τ' (π t) = τ t := by
  classical
  have hc : ∀ o : Option (Fin 3), Fintype.card {t // τ t = o} = Fintype.card {t // τ' t = o} := by
    intro o
    have h1 := congrArg (fun f => f o) h
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_boole, Nat.cast_id] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h1
  exact ⟨Equiv.ofFiberEquiv (fun o => Fintype.equivOfCardEq (hc o)), fun t => Equiv.ofFiberEquiv_map _ t⟩

lemma prod_X_eq_monomial {d : ℕ} (τ : Fin d → Option (Fin 3)) :
    (∏ t, (X (τ t) : MvPolynomial (Option (Fin 3)) ℝ)) =
      monomial (∑ t, Finsupp.single (τ t) (1 : ℕ)) 1 := by
  exact (monomial_sum_one (R := ℝ) Finset.univ fun t => Finsupp.single (τ t) 1).symm

lemma linear_form_add_eq_sum (n : Fin 3 → ℝ) (v : ℝ) :
    lin4 n + C v * X none =
      ∑ j : Option (Fin 3), C (Option.elim j v n) * (X j : MvPolynomial (Option (Fin 3)) ℝ) := by

  simp only [lin4, lin3, map_sum, map_mul, rename_X, rename_C, Fintype.sum_option, Option.elim_none,
  Option.elim_some]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_functional : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
    ∃ L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ, ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)) := by
  classical
  intro d T H
  obtain ⟨Λ, hΛ, hsym⟩ := (PositivityTheory.Xgp.t_fib_mdisc d).2
  obtain ⟨M, hM⟩ : ∃ M : Option (Fin 3) → Matrix (Fin d) (Fin d) ℂ, M none = H ∧ ∀ i, M (some i) = T i :=
    ⟨fun j => Option.elim j H T, rfl, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (Option (Fin 3) →₀ ℕ) → ℂ, ∀ τ : Fin d → Option (Fin 3),
      g (∑ t, Finsupp.single (τ t) (1 : ℕ)) = (d.factorial : ℂ) * Λ (fun t => M (τ t)) := by
    refine ⟨fun m => if h : ∃ τ : Fin d → Option (Fin 3), ∑ t, Finsupp.single (τ t) (1 : ℕ) = m then
      (d.factorial : ℂ) * Λ (fun t => M (h.choose t)) else 0, fun τ => ?_⟩
    have h : ∃ τ' : Fin d → Option (Fin 3),
        ∑ t, Finsupp.single (τ' t) (1 : ℕ) = ∑ t, Finsupp.single (τ t) (1 : ℕ) := ⟨τ, rfl⟩
    simp only [dif_pos h]
    obtain ⟨π, hπ⟩ := exists_perm_of_sum_single h.choose_spec
    have e : (fun t => M (h.choose t)) = (fun t => M (τ t)) ∘ π :=
      funext fun t => by simp only [Function.comp_apply, hπ]
    rw [e, hsym]
  refine ⟨(basisMonomials (Option (Fin 3)) ℝ).constr ℝ g, fun c v => ?_⟩
  have hL : ∀ (m : Option (Fin 3) →₀ ℕ) (x : ℝ),
      (basisMonomials (Option (Fin 3)) ℝ).constr ℝ g (monomial m x) = (x : ℂ) * g m := by
    intro m x
    have hx : (monomial m x : MvPolynomial (Option (Fin 3)) ℝ) = x • basisMonomials (Option (Fin 3)) ℝ m := by
      simp only [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    rw [hx, map_smul, Module.Basis.constr_basis, Complex.real_smul]
  have hrow : ∀ t, (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H =
      ∑ j : Option (Fin 3), ((Option.elim j (v t) (c t) : ℝ) : ℂ) • M j := by
    intro t
    rw [Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some, hM.1, hM.2]
    exact add_comm _ _
  have hprod : (∏ t, (lin4 (c t) + C (v t) * X none) : MvPolynomial (Option (Fin 3)) ℝ) =
      ∑ r : Fin d → Option (Fin 3),
        monomial (∑ t, Finsupp.single (r t) (1 : ℕ)) (∏ t, Option.elim (r t) (v t) (c t)) := by
    simp only [linear_form_add_eq_sum]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod (C : ℝ →+* MvPolynomial (Option (Fin 3)) ℝ), prod_X_eq_monomial,
      C_mul_monomial, mul_one]
  simp only [hrow]

  rw [← hΛ, MultilinearMap.map_sum, hprod, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, hL, hg, smul_eq_mul, Complex.ofReal_prod]
  simp only [RingHom.id_apply]
  ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly
end

section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem subsingleton_affine_zero {p q : ℂ} (h : p ≠ 0 ∨ q ≠ 0) :
    {a : ℂ | p + q * a = 0}.Subsingleton := by
  intro a ha b hb
  have ha' : p + q * a = 0 := ha
  have hb' : p + q * b = 0 := hb
  have hq : q ≠ 0 := by
    rcases h with hp | hq
    · intro hq0
      rw [hq0, zero_mul, add_zero] at ha'
      exact hp ha'
    · exact hq
  exact mul_left_cancel₀ hq (by linear_combination ha' - hb')

theorem det_smulRight_restrictScalars (w : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w).restrictScalars ℝ).det = Complex.normSq w := by
  have e : ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w = w • ContinuousLinearMap.id ℂ ℂ := by
    ext
    simp
  rw [e, ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    ReciprocityTheory.AnForm.A.det_restrictScalars_real]
  simp

theorem hasDerivAt_mob (g : Matrix (Fin 2) (Fin 2) ℂ) {a : ℂ} (ha : den g a ≠ 0) :
    HasDerivAt (mob g) (mobD g a) a := by
  unfold mob mobD
  unfold den at *
  have h1 : HasDerivAt (fun a => g 1 0 + g 1 1 * a) (g 1 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 1 1)).const_add (g 1 0)
  have h2 : HasDerivAt (fun a => g 0 0 + g 0 1 * a) (g 0 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 0 1)).const_add (g 0 0)
  refine (h1.div h2 ha).congr_deriv ?_
  rw [det_fin_two]
  congr 1
  ring

theorem injOn_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0) :
    Set.InjOn (mob g) {a | den g a ≠ 0} := by
  intro a ha b hb hab
  have ha' : den g a ≠ 0 := ha
  have hb' : den g b ≠ 0 := hb
  unfold mob at hab
  rw [div_eq_div_iff ha' hb'] at hab
  unfold den at hab
  rw [det_fin_two] at hg
  have h : (a - b) * (g 0 0 * g 1 1 - g 0 1 * g 1 0) = 0 := by linear_combination hab
  rcases mul_eq_zero.1 h with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hg

theorem mem_image_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0) {b : ℂ}
    (hb : g 1 1 + (-g 0 1) * b ≠ 0) : b ∈ mob g '' {a | den g a ≠ 0} := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by rwa [det_fin_two] at hg
  have hci : (g 1 1 + -g 0 1 * b) * (g 1 1 + -g 0 1 * b)⁻¹ = 1 := mul_inv_cancel₀ hb
  have hden : den g ((g 0 0 * b - g 1 0) / (g 1 1 + (-g 0 1) * b)) =
      (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (g 1 1 + (-g 0 1) * b)⁻¹ := by
    unfold den
    rw [div_eq_mul_inv]
    linear_combination (-g 0 0) * hci
  refine ⟨(g 0 0 * b - g 1 0) / (g 1 1 + (-g 0 1) * b), ?_, ?_⟩
  · show den g _ ≠ 0
    rw [hden]
    exact mul_ne_zero hd (inv_ne_zero hb)
  · unfold mob
    rw [hden, div_eq_iff (mul_ne_zero hd (inv_ne_zero hb)), div_eq_mul_inv (g 0 0 * b - g 1 0)]
    linear_combination (-g 1 0) * hci

theorem integral_normSq_mobD_mul_comp_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hu : IsUnit g.det)
    (f : ℂ → ℝ) :
    ∫ a : ℂ, Complex.normSq (mobD g a) * f (mob g a) = ∫ b : ℂ, f b := by
  have hdet : g.det ≠ 0 := hu.ne_zero
  have hcont : Continuous (den g) := by
    unfold den
    fun_prop
  have hs : MeasurableSet {a : ℂ | den g a ≠ 0} := (isOpen_ne_fun hcont continuous_const).measurableSet
  have hderiv : ∀ a ∈ {a : ℂ | den g a ≠ 0}, HasFDerivWithinAt (mob g)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (mobD g a)).restrictScalars ℝ)
      {a : ℂ | den g a ≠ 0} a :=
    fun a ha => ((hasDerivAt_mob g ha).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hs hderiv (injOn_mob g hdet) f
  simp only [det_smulRight_restrictScalars, abs_of_nonneg (Complex.normSq_nonneg _), smul_eq_mul] at hcv
  rw [det_fin_two] at hdet
  have hnull1 : ∀ᵐ a ∂(volume : Measure ℂ), a ∈ {a : ℂ | den g a ≠ 0} := by
    have h01 : g 0 0 ≠ 0 ∨ g 0 1 ≠ 0 := by
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      apply hdet
      rw [hc.1, hc.2]
      ring
    refine mem_ae_iff.2 (measure_mono_null ?_ ((subsingleton_affine_zero h01).countable.measure_zero _))
    intro a ha
    have ha' : ¬ den g a ≠ 0 := ha
    rw [not_not] at ha'
    exact ha'
  have hnull2 : ∀ᵐ b ∂(volume : Measure ℂ), b ∈ mob g '' {a : ℂ | den g a ≠ 0} := by
    have h11 : g 1 1 ≠ 0 ∨ -g 0 1 ≠ 0 := by
      by_contra hc
      rw [not_or, not_not, not_not, neg_eq_zero] at hc
      apply hdet
      rw [hc.1, hc.2]
      ring
    refine mem_ae_iff.2 (measure_mono_null ?_ ((subsingleton_affine_zero h11).countable.measure_zero _))
    intro b hb
    by_contra hne
    exact hb (mem_image_mob g hu.ne_zero hne)
  rw [Measure.restrict_eq_self_of_ae_mem hnull1, Measure.restrict_eq_self_of_ae_mem hnull2] at hcv
  exact hcv.symm

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → ∃ T : Fin 3 → Matrix (Fin d) (Fin d) ℂ, ∀ a : ℂ, ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) ∧ hessC (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) = Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (-(((1 + ‖a‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => ∑ i, (((fun (a : ℂ) (i : Fin 3) => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)) a i : ℝ) : ℂ) * T i p' q') q) p := by
  intro d G y _ hC h1 h0
  let A : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ := fun p q => fderiv ℝ (fderiv ℝ fun y' => (G y' p q).re) y
  let B : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ := fun p q => fderiv ℝ (fderiv ℝ fun y' => (G y' p q).im) y
  refine ⟨![PositivityTheory.Xgp.fib_hess.hm ((-(1/2:ℝ)) • (A 0 1 + A 1 0)), PositivityTheory.Xgp.fib_hess.hm ((-(1/2:ℝ)) • (B 1 0 - B 0 1)), PositivityTheory.Xgp.fib_hess.hm ((1/2:ℝ) • (A 1 1 - A 0 0))], fun a => ?_⟩
  obtain ⟨hc, hH⟩ := PositivityTheory.Xgp.fib_hess.jet d G y hC h1 h0 a A B (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨hc, ?_⟩
  ext p q
  refine Fin.cases ?_ (fun p' => ?_) p <;> refine Fin.cases ?_ (fun q' => ?_) q
  all_goals simp only [hessC, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, hH, PositivityTheory.Xgp.fib_hess.tl_zero, PositivityTheory.Xgp.fib_hess.tl_zero', PositivityTheory.Xgp.fib_hess.tl_succ, PositivityTheory.Xgp.fib_hess.tl_succ', map_zero, ContinuousLinearMap.zero_apply]
  all_goals simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, ne_eq, Fin.succ_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, mul_one, Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  all_goals clear hH hc h0 h1 hC
  all_goals have hr : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  all_goals have hpos : (0:ℝ) < 1 + (a.re ^ 2 + a.im ^ 2) := by positivity
  all_goals have hne : (1 + ((a.re:ℂ) ^ 2 + (a.im:ℂ) ^ 2)) ≠ 0 := by exact_mod_cast hpos.ne'
  case refine_1.refine_1 =>
    rw [hr]
    push_cast
    field_simp
    ring
  all_goals have hz : ∀ j : Fin d, (Pi.single j.succ (1:ℂ) : Fin (d+1) → ℂ) 0 = 0 := fun j => by simp [Pi.single_apply, (Fin.succ_ne_zero j).symm]
  all_goals simp only [hz, mul_zero, Complex.zero_re, Complex.zero_im, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PositivityTheory.Xgp.fib_hess.hm, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.neg_apply]
  all_goals try rw [hr]
  case refine_2.refine_2 =>
    apply Complex.ext
    · simp only [Complex.add_re, Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.div_im, Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.normSq_ofNat]
      field_simp
      ring
    · simp only [Complex.add_re, Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.div_im, Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.normSq_ofNat]
      field_simp
      ring
  all_goals push_cast
  all_goals field_simp
  all_goals ring
end
