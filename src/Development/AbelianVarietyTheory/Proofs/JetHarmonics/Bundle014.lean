module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Formalism.RealPlaceAnalysis.Bundle002
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, Small (s i)) → Bdd S → (∀ μ, HasSum (fun ν : σ →₀ ℕ => MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i)) (MvPowerSeries.coeff μ (csub s S))) ∧ Bdd (csub s S) ∧ (Intg S → Intg (csub s S)) ∧ (Intg S → MvPowerSeries.constantCoeff S = 0 → Small (csub s S)) := by
  first | exact @GlobalTheory.ConvSer.csub_hasSum_and_bounds | exact GlobalTheory.ConvSer.csub_hasSum_and_bounds | (intros; apply GlobalTheory.ConvSer.csub_hasSum_and_bounds <;> assumption)
end

section

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TaylorRead

theorem tay_add {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    tay (fun z => F z + G z) = tay F + tay G := by
  ext n
  have := iteratedDeriv_add (n := n) (x := (0 : ℂ)) hF.contDiffAt hG.contDiffAt
  simp only [tay, coeff_mk, map_add (f := _)]
  rw [← add_div, ← this]
  rfl

theorem tay_mul {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    tay (fun z => F z * G z) = tay F * tay G := by
  ext n
  have := iteratedDeriv_mul (n := n) (x := (0 : ℂ)) hF.contDiffAt hG.contDiffAt
  simp only [tay, coeff_mk, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => iteratedDeriv i F 0 / (i.factorial : ℂ) * (iteratedDeriv j G 0 / (j.factorial : ℂ)))]
  change iteratedDeriv n (F * G) 0 / _ = _
  rw [this, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h := Nat.choose_mul_factorial_mul_factorial hi'
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have h3 : (n.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  rw [← h]
  push_cast
  field_simp

theorem tay_congr {F G : ℂ → ℂ} (h : F =ᶠ[𝓝 0] G) : tay F = tay G := by
  ext n
  simp only [tay, coeff_mk]
  rw [h.iteratedDeriv_eq n]

theorem eventuallyEq_of_tay_eq {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (h : tay F = tay G) : F =ᶠ[𝓝 0] G := by
  have hd : ∀ n, iteratedDeriv n F 0 = iteratedDeriv n G 0 := by
    intro n
    have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have := congrArg (coeff n) h
    simp only [tay, coeff_mk] at this
    exact (div_left_inj₀ h1).mp this
  have hs : AnalyticAt ℂ (F - G) 0 := hF.sub hG
  have htop : analyticOrderAt (F - G) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hs]
    intro i _
    rw [iteratedDeriv_sub hF.contDiffAt hG.contDiffAt, hd, sub_self]
  filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
  exact sub_eq_zero.mp hz

theorem tay_const (c : ℂ) : tay (fun _ => c) = C c := by
  ext n
  simp only [tay, coeff_mk, iteratedDeriv_const, coeff_C]
  split_ifs with h
  · simp [h]
  · simp

theorem derivative_tay (F : ℂ → ℂ) : PowerSeries.derivative (tay F) = tay (deriv F) := by
  ext n
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  simp only [coeff_derivative, tay, coeff_mk, iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

theorem tay_id : tay (fun z => z) = X := by
  ext n
  rcases n with _ | n
  · simp [tay]
  · have : deriv (fun z : ℂ => z) = fun _ => 1 := by ext; simp
    simp only [tay, coeff_mk, iteratedDeriv_succ', this, iteratedDeriv_const, coeff_X]
    rcases n with _ | n <;> simp

theorem iteratedDeriv_comp_mul (F : ℂ → ℂ) (α : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => F (α * z)) = fun x => α ^ n * iteratedDeriv n F (α * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    ext x
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left, iteratedDeriv_succ,
      smul_eq_mul]
    ring

theorem tay_comp_mul (F : ℂ → ℂ) (α : ℂ) : tay (fun z => F (α * z)) = rescale α (tay F) := by
  ext n
  simp only [tay, coeff_mk, coeff_rescale, iteratedDeriv_comp_mul, mul_zero]
  ring

theorem constantCoeff_subst_of {R : Type*} [CommRing R] {ℓ : R⟦X⟧} (hℓ : constantCoeff ℓ = 0)
    (f : R⟦X⟧) : constantCoeff (f.subst ℓ : R⟦X⟧) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' (HasSubst.of_constantCoeff_zero' hℓ),
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [hℓ, hd]

theorem subst_injective_of {R : Type*} [Field R] {ℓ : R⟦X⟧} (hℓ : constantCoeff ℓ = 0)
    (h1 : coeff 1 ℓ ≠ 0) {f g : R⟦X⟧} (h : (f.subst ℓ : R⟦X⟧) = g.subst ℓ) : f = g := by
  have hu : IsUnit (coeff 1 ℓ) := h1.isUnit
  have key : ∀ f : R⟦X⟧, PowerSeries.subst (R := R) (S := R) (substInvOfIsUnit ℓ hu) (PowerSeries.subst (R := R) (S := R) ℓ f) = f := by
    intro f
    rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hℓ) (HasSubst.substInvOfIsUnit ℓ hu),
      subst_substInvOfIsUnit_right ℓ hℓ hu, X_subst]
  rw [← key f, h, key g]

theorem hat_laws : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧), constantCoeff ℓ = 0 → (∀ F G : ℂ → ℂ, AnalyticAt ℂ F 0 → AnalyticAt ℂ G 0 → hat ι ℓ (fun z => F z + G z) = hat ι ℓ F + hat ι ℓ G ∧ hat ι ℓ (fun z => F z * G z) = hat ι ℓ F * hat ι ℓ G ∧ ((∀ᶠ z in 𝓝[≠] (0 : ℂ), F z = G z) → hat ι ℓ F = hat ι ℓ G) ∧ (coeff 1 ℓ ≠ 0 → hat ι ℓ F = hat ι ℓ G → F =ᶠ[𝓝 0] G)) ∧ (∀ c : ℂ, hat ι ℓ (fun _ => c) = C (ι c)) ∧ hat ι ℓ (fun z => z) = ℓ ∧ (∀ F : ℂ → ℂ, constantCoeff (hat ι ℓ F) = ι (F 0)) ∧ (∀ F : ℂ → ℂ, AnalyticAt ℂ F 0 → PowerSeries.derivative (hat ι ℓ F) = PowerSeries.derivative ℓ * hat ι ℓ (deriv F)) ∧ (∀ (F : ℂ → ℂ) (α : ℂ), AnalyticAt ℂ F 0 → hat ι ℓ (fun z => F (α * z)) = hat ι (C (ι α) * ℓ) F) ∧ ∀ (F : ℂ → ℂ) (h : ℂ_[q]⟦X⟧), constantCoeff h = 0 → (hat ι ℓ F).subst h = hat ι (ℓ.subst h) F := by
  intro q _ ι ℓ hℓ
  have hs : HasSubst ℓ := HasSubst.of_constantCoeff_zero' hℓ
  refine ⟨fun F G hF hG => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hat]
    rw [tay_add hF hG, map_add (f := _), subst_add hs]
  · simp only [hat]
    rw [tay_mul hF hG, map_mul, subst_mul hs]
  · intro h
    have : F =ᶠ[𝓝 0] G := (hF.frequently_eq_iff_eventually_eq hG).mp h.frequently
    simp only [hat]
    rw [tay_congr this]
  · intro h1 h
    apply eventuallyEq_of_tay_eq hF hG
    exact PowerSeries.map_injective (ι : ℂ →+* ℂ_[q]) ι.injective (subst_injective_of hℓ h1 h)
  · intro c
    simp only [hat]
    rw [tay_const, map_C, subst_C]
    rfl
  · simp only [hat]
    rw [tay_id, map_X, subst_X hs]
  · intro F
    simp only [hat]
    rw [constantCoeff_subst_of hℓ, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
    simp [tay]
  · intro F _
    simp only [hat]
    rw [derivative_subst hs, mul_comm, ← derivative_tay]
    congr 2
    ext n
    simp [coeff_derivative]
  · intro F α _
    simp only [hat]
    have e : PowerSeries.map (ι : ℂ →+* ℂ_[q]) (rescale α (tay F))
        = rescale (ι α) (PowerSeries.map (ι : ℂ →+* ℂ_[q]) (tay F)) := by
      ext n
      simp [coeff_rescale]
    rw [tay_comp_mul, e, rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' _) hs,
      subst_smul hs, subst_X hs, smul_eq_C_mul]
  · intro F h hh
    simp only [hat]
    rw [subst_comp_subst_apply hs (HasSubst.of_constantCoeff_zero' hh)]

end GlobalTheory.MomOne.TaylorRead
end
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem cmLatticeHermitianForm_add_left (d : ℕ) (x y z : ℂ) : h1 d (x + y) z = h1 d x z + h1 d y z := by
  simp only [h1]; ring

theorem cmLatticeHermitianForm_add_right (d : ℕ) (x y z : ℂ) : h1 d x (y + z) = h1 d x y + h1 d x z := by
  simp only [h1, map_add (f := _)]; ring

theorem cmLatticeHermitianForm_swap (d : ℕ) (x y : ℂ) :
    h1 d y x = h1 d x y - 2 * Complex.I * (((h1 d x y).im : ℝ) : ℂ) := by
  have h : h1 d y x = conj (h1 d x y) := by
    simp only [h1, map_mul, Complex.conj_ofReal, Complex.conj_conj]; ring
  rw [h]
  apply Complex.ext
  · simp
  · simp; ring

theorem cmLatticeTranslationOperator_comp (d : ℕ) (x y : ℂ) (F : ℂ → ℂ) :
    U1 d x (U1 d y F) = fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d x y).im : ℝ) : ℂ)) *
      U1 d (x + y) F z := by
  funext z
  simp only [U1]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z x y]
  congr 2
  simp only [cmLatticeHermitianForm_add_left, cmLatticeHermitianForm_add_right]
  rw [cmLatticeHermitianForm_swap d x y]
  ring

theorem differentiable_cmLatticeTranslationOperator (d : ℕ) (x : ℂ) (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Differentiable ℂ (U1 d x F) := by
  unfold U1 h1
  fun_prop

theorem cmLatticeWeylOperator_comp (d : ℕ) (hd : 0 < d) (x y : ℂ) (F : ℂ → ℂ) (h : InOK d (x * conj y)) :
    W1 d x (W1 d y F) = W1 d (x + y) F := by
  obtain ⟨u, v, h⟩ := h
  have hs : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact (Real.sqrt_pos.2 this).ne'
  have him : (h1 d x y).im = v := by
    rw [h1, h, wK, Complex.im_ofReal_mul]
    simp
    field_simp
  have hre : Complex.normSq (x + y) = Complex.normSq x + Complex.normSq y + (2 * u + v) := by
    rw [Complex.normSq_add, h, wK]
    simp
    ring
  funext z
  have h2 : U1 d x (W1 d y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq y : ℝ) : ℂ)) *
      U1 d x (U1 d y F) z := by
    simp only [U1, W1]; ring
  have h3 : W1 d x (W1 d y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) *
      U1 d x (W1 d y F) z := rfl
  rw [h3, h2, cmLatticeTranslationOperator_comp]
  simp only [W1]
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, him, hre]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(u + v), ?_⟩
  push_cast
  ring

theorem cmLatticeTranslationOperator_theta_quasiPeriodicity (d : ℕ) (θ : ℂ → ℂ) (t l z : ℂ) (h : W1 d l θ = θ) :
    U1 d t θ (z + l) * θ z = kap1 d l t * (U1 d t θ z * θ (z + l)) := by
  have a := congrFun h z
  have b := congrFun h (z + t)
  simp only [W1, U1] at a b
  simp only [U1, kap1]
  have e : z + l + t = z + t + l := by ring
  rw [e]
  set A := θ (z + t + l)
  set B := θ (z + l)
  rw [← a, ← b]
  have key : Complex.exp (-(Real.pi : ℂ) * h1 d (z + l) t - (Real.pi : ℂ) / 2 * h1 d t t) *
      Complex.exp (-(Real.pi : ℂ) * h1 d z l - (Real.pi : ℂ) / 2 * h1 d l l) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (((h1 d l t).im : ℝ) : ℂ)) *
      (Complex.exp (-(Real.pi : ℂ) * h1 d (z + t) l - (Real.pi : ℂ) / 2 * h1 d l l) *
      Complex.exp (-(Real.pi : ℂ) * h1 d z t - (Real.pi : ℂ) / 2 * h1 d t t)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [cmLatticeHermitianForm_add_left]
    rw [cmLatticeHermitianForm_swap d l t]
    ring
  linear_combination (A * B * Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq l : ℝ) : ℂ))) * key

theorem heisenbergOne : ∀ d : ℕ, 0 < d → (∀ (x y : ℂ) (F : ℂ → ℂ), U1 d x (U1 d y F) = fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d x y).im : ℝ) : ℂ)) * U1 d (x + y) F z) ∧ (∀ F, U1 d 0 F = F) ∧ (∀ (x : ℂ) (F : ℂ → ℂ), Differentiable ℂ F → Differentiable ℂ (U1 d x F) ∧ Differentiable ℂ (W1 d x F)) ∧ (∀ (x : ℂ) (F : ℂ → ℂ) (z : ℂ), U1 d x (fun z => F (-z)) z = U1 d (-x) F (-z)) ∧ (∀ (x y : ℂ) (F : ℂ → ℂ), d % 4 = 3 → InOK d (x * conj y) → W1 d x (W1 d y F) = W1 d (x + y) F) ∧ (∀ (θ : ℂ → ℂ) (t l z : ℂ), W1 d l θ = θ → U1 d t θ (z + l) * θ z = kap1 d l t * (U1 d t θ z * θ (z + l))) ∧ (∀ (x : ℂ) (f F : ℂ → ℂ) (z : ℂ), W1 d x (fun z => f z * F z) z = f (z + x) * W1 d x F z ∧ U1 d x (fun z => f z * F z) z = f (z + x) * U1 d x F z) ∧ ∀ (x y z : ℂ), kap1 d x (y + z) = kap1 d x y * kap1 d x z ∧ kap1 d (x + y) z = kap1 d x z * kap1 d y z := by
  intro d hd
  refine ⟨cmLatticeTranslationOperator_comp d, ?_, ?_, ?_, fun x y F _ h => cmLatticeWeylOperator_comp d hd x y F h,
    fun θ t l z h => cmLatticeTranslationOperator_theta_quasiPeriodicity d θ t l z h, ?_, ?_⟩
  · intro F
    funext z
    simp [U1, h1]
  · intro x F hF
    refine ⟨differentiable_cmLatticeTranslationOperator d x F hF, ?_⟩
    exact (differentiable_cmLatticeTranslationOperator d x F hF).const_mul _
  · intro x F z
    simp only [U1, h1, map_neg]
    congr 1
    · congr 1; ring
    · congr 1; ring
  · intro x f F z
    simp only [W1, U1]
    constructor <;> ring
  · intro x y z
    simp only [kap1, cmLatticeHermitianForm_add_left, cmLatticeHermitianForm_add_right, Complex.add_im, ← Complex.exp_add]
    constructor <;> (congr 1; push_cast; ring)

end GlobalTheory.MomOne
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem norm_sum_prod_le_of_coord {K : Type*} [NormedCommRing K] {g m : ℕ} (F G : Fin m → Fin g → ℕ → K)
    (c : Fin m → K) (B : ℝ)
    (step : ∀ (i : Fin g) (c' : Fin m → K), (∀ n, ‖∑ j, c' j * F j i n‖ ≤ B) → ∀ n, ‖∑ j, c' j * G j i n‖ ≤ B)
    (h : ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, F j i (ν i)‖ ≤ B) (ν : Fin g → ℕ) :
    ‖∑ j, c j * ∏ i, G j i (ν i)‖ ≤ B := by
  classical
  have key : ∀ I : Finset (Fin g), ∀ ν : Fin g → ℕ,
      ‖∑ j, c j * ∏ i, (if i ∈ I then G j i (ν i) else F j i (ν i))‖ ≤ B := by
    intro I
    induction I using Finset.induction_on with
    | empty => simpa using h
    | insert i₀ I hi ih =>
      intro ν
      have hs := step i₀
        (fun j => c j * ∏ i ∈ Finset.univ.erase i₀, (if i ∈ I then G j i (ν i) else F j i (ν i))) ?_ (ν i₀)
      · convert hs using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi']
        · simp
      · intro n
        convert ih (Function.update ν i₀ n) using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Function.update_of_ne (Finset.ne_of_mem_erase hi')]
        · simp [hi]
  simpa using key Finset.univ ν

theorem translate_norm_prod_le : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (θ : ℂ → ℂ), ThetaLaws ι d ω θ → ∀ (g m : ℕ) (a : Fin g → ℕ) (c : Fin m → ℂ_[q]) (t : Fin m → Fin g → ℂ) (τ : Fin g → ℂ) (B : ℝ), (∀ j i, PrimeTo d q (t j i)) → (∀ i, PrimeTo d q (τ i)) → (∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i)‖ ≤ B) → ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)‖ ≤ B := by
  intro d q _ ι ω θ hθ g m a c t τ B ht hτ h
  refine norm_sum_prod_le_of_coord
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i))
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)) c B ?_ h
  intro i c' hc n
  have := hθ.2.2 (a i) m c' (fun j => t j i) (τ i) B (fun j => ht j i) (hτ i) (fun k => by

    simpa only [map_sum, coeff_C_mul] using hc k) n

  simpa only [map_sum, coeff_C_mul] using this

end GlobalTheory.MomOne
end

section

open Formalism.REAL
namespace GlobalTheory

theorem hw_component_tensor_dual_standard (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (θ : Fin (n + 1) → ℂ) (lam : ℂ) (y : (PiLp 2 (fun _ : Fin (n + 1) => V))) (hEt : ∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) (hOm : ∀ y a, Om y a = ∑ c, E a c (y c)) (hy : y ≠ 0) (hw : IsHW Et θ y) (hl : Om y = lam • y) : ∃ c, y c ≠ 0 ∧ IsHW E (fun a => θ a + if a = c then 1 else 0) (y c) ∧ lam = θ c + 1 - ((c : ℕ) : ℂ) + (n : ℂ) := by
  classical
  have hex : ∃ c, y c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (by ext c; simpa using h c)
  obtain ⟨c, hc, hmin⟩ := (wellFounded_lt (α := Fin (n + 1))).has_min {c | y c ≠ 0} hex
  have hlt : ∀ d, d < c → y d = 0 := fun d hd => by
    by_contra h
    exact hmin d h hd
  unfold IsHW at hw ⊢
  obtain ⟨hd, hu⟩ := hw
  have hc' : y c ≠ 0 := hc
  have hdiag : ∀ a, E a a (y c) = (θ a + if a = c then 1 else 0) • y c := by
    intro a
    have h := hEt a a y c
    rw [hd a, PiLp.smul_apply] at h
    by_cases hac : a = c
    · subst hac
      simp only [if_true] at h ⊢
      rw [add_smul, one_smul, h, sub_add_cancel]
    · have hca : ¬ c = a := fun e => hac e.symm
      simp only [hac, hca, if_false, sub_zero, add_zero] at h ⊢
      exact h.symm
  refine ⟨c, hc', ⟨hdiag, ?_⟩, ?_⟩
  · intro a b hab
    have h := hEt a b y c
    rw [hu a b hab, PiLp.zero_apply] at h
    by_cases hcb : c = b
    · subst hcb
      simp only [if_true, hlt a hab, sub_zero] at h
      exact h.symm
    · simp only [hcb, if_false, sub_zero] at h
      exact h.symm
  · have h := hOm y c
    rw [hl, PiLp.smul_apply] at h
    have hterm : ∀ d, E c d (y d) =
        ((if d = c then θ c + 1 else 0) + (if c < d then (1 : ℂ) else 0)) • y c := by
      intro d
      rcases lt_trichotomy d c with hdc | hdc | hdc
      · simp [hlt d hdc, hdc.ne, hdc.not_gt]
      · subst hdc
        simp [hdiag d]
      · have h2 := hEt c d y d
        rw [hu c d hdc, PiLp.zero_apply] at h2
        simp only [if_true] at h2
        have h3 := (sub_eq_zero.mp h2.symm)
        simp [h3, hdc, hdc.ne']
    simp_rw [hterm] at h
    rw [← Finset.sum_smul] at h
    have h4 := smul_left_injective ℂ hc' h
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_boole] at h4
    have h5 : (Finset.univ.filter (fun d : Fin (n + 1) => c < d)).card = n - c := by
      have : Finset.univ.filter (fun d : Fin (n + 1) => c < d) = Finset.Ioi c := by
        ext d; simp
      rw [this, Fin.card_Ioi]; omega
    rw [h5, Nat.cast_sub (Nat.lt_succ_iff.mp c.2)] at h4
    rw [h4]; ring
end GlobalTheory
end
