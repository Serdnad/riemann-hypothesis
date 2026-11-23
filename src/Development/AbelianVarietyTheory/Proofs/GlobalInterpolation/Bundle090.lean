module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle093
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle034
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle083
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle046
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

namespace GlobalTheory.MomOneAmice

theorem momInt_of_bd_hat (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) (hB : Bd 1 (hat ι (C ω * logS) G)) :
    MomInt ι (fun _ : Unit => ι.symm ω) G := by
  set H := hat ι (C ω * logS) G with hH
  obtain ⟨μ₁, hμ₁, hsum⟩ := GlobalTheory.MultiMahler.exists_measure_of_bounded_moments q 1
    (fun n => coeff (n 0) H) ⟨1, fun n => hB (n 0)⟩
  have hn1 : ‖μ₁‖ ≤ 1 := (hμ₁ 1 zero_le_one).2 fun n => hB (n 0)

  let e : C(Fin 1 → ℤ_[q], Unit → ℤ_[q]) := ⟨fun a _ => a 0, by fun_prop⟩
  let R₀ : C(Unit → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] C(Fin 1 → ℤ_[q], ℂ_[q]) :=
    { toFun := fun F => F.comp e
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : ∀ F, ‖R₀ F‖ ≤ 1 * ‖F‖ := fun F => by
    rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg _)]
    intro a
    exact F.norm_coe_le_norm _
  let R := R₀.mkContinuous 1 hR
  have hRn : ‖R‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  refine ⟨μ₁.comp R, ?_, fun k j f hf => ?_⟩
  · calc ‖μ₁.comp R‖ ≤ ‖μ₁‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hn1 hRn (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · obtain ⟨f₁, hf₁, hs₁⟩ := GlobalTheory.MomOne.TwistMom.twisted_moments q H 1 0 k ⟨1, hB⟩ (by simp)
    have hF : ∀ a : Fin 1 → ℤ_[q], (R f) a = ∏ i, (fun _ : Fin 1 => f₁) i (a i) := fun a => by
      change f (e a) = _
      rw [hf, Fin.prod_univ_one, hf₁]
      simp [e]
    have h2 := hsum (fun _ => f₁) (R f) hF
    have h3 : HasSum (fun m : ℕ => coeff m H * (fwdDiff (1 : ℤ_[q]))^[m] f₁ 0) (μ₁ (R f)) := by
      have := (Equiv.hasSum_iff (Equiv.funUnique (Fin 1) ℕ).symm).2 h2
      simpa [Function.comp_def] using this
    have h4 := h3.unique hs₁
    rw [GlobalTheory.MomOne.Basic.shiftS_one, (GlobalTheory.MomOne.hat_multiplicative_chart q ι ω G (hG.analyticAt 0)).2.1 k] at h4
    rw [ContinuousLinearMap.comp_apply, h4, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
      map_mul, map_prod]
    simp

end GlobalTheory.MomOneAmice
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

def polyOfMv (k : Type) [CommRing k] (σ : Type) :
    MvPolynomial σ (Polynomial k) →+* Polynomial (MvPolynomial σ k) :=
  MvPolynomial.eval₂Hom (Polynomial.mapRingHom (C : k →+* MvPolynomial σ k)) (fun v => Polynomial.C (X v))

theorem polyOfMv_map_C (k : Type) [CommRing k] (σ : Type) (f : MvPolynomial σ k) :
    polyOfMv k σ (map (algebraMap k (Polynomial k)) f) = Polynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [polyOfMv]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, map_X]; simp [polyOfMv]

theorem coeff_polyOfMv_mem (k : Type) [CommRing k] (σ : Type) (M : Submodule k (MvPolynomial σ k))
    (P : MvPolynomial σ (Polynomial k))
    (hP : P ∈ Submodule.span (Polynomial k) (map (algebraMap k (Polynomial k)) '' (M : Set (MvPolynomial σ k)))) :
    ∀ j, (polyOfMv k σ P).coeff j ∈ M := by
  induction hP using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    intro j
    rw [polyOfMv_map_C, Polynomial.coeff_C]
    split_ifs
    · exact hf
    · exact zero_mem _
  | zero => intro j; simp
  | add y z _ _ hy hz => intro j; rw [map_add (f := _), Polynomial.coeff_add]; exact add_mem (hy j) (hz j)
  | smul c y _ hy =>
    intro j
    rw [MvPolynomial.smul_eq_C_mul, map_mul, Polynomial.coeff_mul]
    refine Submodule.sum_mem _ fun x _ => ?_
    have : polyOfMv k σ (C c) = Polynomial.map (C : k →+* MvPolynomial σ k) c := by simp [polyOfMv]
    rw [this, Polynomial.coeff_map, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hy x.2)

end GlobalTheory.Alc

noncomputable section
namespace GlobalTheory.Alc

def transvGL (k : Type) [CommRing k] {N : ℕ} (a b : Fin N) (h : a ≠ b) : GL (Fin N) (Polynomial k) :=
  Matrix.nonsingInvUnit (Matrix.transvection a b (Polynomial.X : Polynomial k))
    (by rw [Matrix.det_transvection_of_ne a b h]; exact isUnit_one)

theorem polyOfMv_sqAct_transv (k : Type) [CommRing k] (N : ℕ) (lam : DomWeight N) (a b : Fin N) (h : a ≠ b)
    (f : MvPolynomial (Fin N × Fin N) k) :
    polyOfMv k _ (sqAct (Polynomial k) N lam (transvGL k a b h) (map (algebraMap k (Polynomial k)) f)) =
      rowGen k a b f := by
  have hdet : detPow (Polynomial k) N (transvGL k a b h) lam.detShift = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det (transvGL k a b h) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact Matrix.det_transvection_of_ne a b h (Polynomial.X : Polynomial k)
    rw [detPow, h1, one_zpow, Units.val_one]
  rw [sqAct, hdet, one_smul]
  induction f using MvPolynomial.induction_on with
  | C r => simp [polyOfMv, rowGen, rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1

    simp only [rowGen, rowAct, aeval_X, map_sum, map_mul]
    have hg : ∀ x, (transvGL k a b h : Matrix (Fin N) (Fin N) (Polynomial k)).transpose v.1 x =
        (if v.1 = x then 1 else 0) + (if a = x ∧ b = v.1 then Polynomial.X else 0) := by
      intro x
      show (Matrix.transvection a b (Polynomial.X : Polynomial k)).transpose v.1 x = _
      simp only [Matrix.transpose_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      congr 1
      simp only [eq_comm]
    simp only [hg, polyOfMv, eval₂Hom_C, eval₂Hom_X', Polynomial.coe_mapRingHom, Polynomial.map_add (f := _), add_mul,
      Finset.sum_add_distrib, apply_ite (Polynomial.map (C : k →+* MvPolynomial (Fin N × Fin N) k)), ite_mul,
      Polynomial.map_one, Polynomial.map_zero, Polynomial.map_X, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ite_and, Finset.sum_ite_eq']
    obtain ⟨v1, v2⟩ := v
    by_cases hb : v1 = b
    · subst hb; simp
    · simp [hb, Ne.symm hb]

end GlobalTheory.Alc

noncomputable section
namespace GlobalTheory.Alc

theorem rowE_mem_of_isGLSubmodule : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)), GlobalTheory.Published.IsGLSubmodule k N lam M →
    ∀ a b : Fin N, a ≠ b → ∀ f ∈ M, rowE k N N a b f ∈ M := by
  intro k _ N lam M hM a b hab f hf
  have h1 := coeff_polyOfMv_mem k _ M _ (hM (Polynomial k) (transvGL k a b hab) f hf) 1
  rw [polyOfMv_sqAct_transv] at h1
  rw [((GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).2.1 a b f)]
  exact h1

end GlobalTheory.Alc
end
end
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bandWidth_le_inv_sq_of_rank_bounds (x e n k d La B c : ℝ) (hx : 1 < x) (hd0 : 0 ≤ d) (hd : d ≤ 1) (hn0 : 0 ≤ n)
    (hn : n ≤ 2 * x ^ (2 + 8 * e)) (hk : x ^ (9 / 2 + 10 * e) ≤ k) (hLa0 : 0 ≤ La)
    (hLa : La ≤ B * Real.log x ^ 2 * (2 * x ^ e))
    (h1 : 64 * B * x ^ (2 + 10 * e) * Real.log x ^ 2 ≤ x ^ (5 / 2 + 10 * e))
    (h2 : 4 * |c| * B * x ^ e * Real.log x ^ 3 ≤ x ^ (5 / 2 + 10 * e)) :
    4 * (2 * n * d) * x ^ e * La / k + c * Real.log x * La / k ≤ x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < k := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hk
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have e1 : x ^ (2 + 10 * e) = x ^ (2 + 8 * e) * x ^ e * x ^ e := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  have e2 : x ^ (5 / 2 + 10 * e) = x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hnd : n * d ≤ 2 * x ^ (2 + 8 * e) := le_trans (mul_le_of_le_one_right hn0 hd) hn
  have t1 : 4 * (2 * n * d) * x ^ e * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc 4 * (2 * n * d) * x ^ e * La = 8 * (n * d) * x ^ e * La := by ring
      _ ≤ 8 * (2 * x ^ (2 + 8 * e)) * x ^ e * (B * Real.log x ^ 2 * (2 * x ^ e)) := by gcongr
      _ = 64 * B * x ^ (2 + 10 * e) * Real.log x ^ 2 / 2 := by rw [e1]; ring
      _ ≤ _ := by linarith
  have t2 : c * Real.log x * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc c * Real.log x * La ≤ |c| * Real.log x * (B * Real.log x ^ 2 * (2 * x ^ e)) := by
          gcongr
          exact le_abs_self c
      _ = 4 * |c| * B * x ^ e * Real.log x ^ 3 / 2 := by ring
      _ ≤ _ := by linarith
  rw [← add_div, div_le_iff₀ hk0]
  have t3 : x ^ (5 / 2 + 10 * e) ≤ x ^ (-2 : ℝ) * k := by
    rw [e2]; gcongr
  linarith

theorem szRow_band_lambda_primes :
    SzRow (fun C D L => G.rhoB D C.GK L.sc ≤ L.sc.x ^ (-2 : ℝ) ∧ L.sc.x ^ L.sc.eps ≤ L.LaG ∧
      (∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L)) ∧ (D.host.pde : ℝ) < L.sc.X' ∧
      (D.host.pde' : ℝ) < L.sc.X' ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) := by
  intro eps he0 he1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hpde, -, hmid, -⟩ := hC
  have hKLa : 1 ≤ C.GK.La := hmid _ (by simp [FC.cMid])
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he0 he1
  obtain ⟨x2, h2⟩ := GlobalTheory.EX.hostBounds eps C.P.Cpde he0 he1 hpde
  obtain ⟨x3, h3⟩ := GlobalTheory.scale_poly_comparison eps 41 1 he0 one_pos
  obtain ⟨x4, h4⟩ := GlobalTheory.scale_poly_comparison eps (2 * C.P.Cpde) 1 he0 one_pos
  obtain ⟨x5, h5⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (2 + 10 * eps) (5 / 2 + 10 * eps)
    (64 * (C.GK.La * CN ^ 2)) 2 (by linarith)
  obtain ⟨x6, h6⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (5 / 2 + 10 * eps)
    (4 * |C.GK.rho * C.GK.CN| * (C.GK.La * CN ^ 2)) 3 (by linarith)
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max (max x5 x6) 512), fun D L he hx hV => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, ⟨hx5, hx6⟩, hx7⟩ := hx
  have hx1' := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  obtain ⟨-, -, hLa⟩ := h1 L.sc he hx1
  obtain ⟨hLa1, hLa2⟩ := hLa C.GK hKLa
  obtain ⟨-, -, -, -, -, -, -, -, hp1, hp2⟩ := h2 L.sc D.R D.host he hx2 hV.ranks hV.host
  obtain ⟨-, -, hb, -⟩ := h3 L.sc he hx3
  obtain ⟨-, -, -, -, -, -, hX⟩ := h4 L.sc he hx4
  have hy0 : 0 < L.sc.x ^ (L.sc.eps / 100) := Real.rpow_pos_of_pos hx0 _
  have hn : (D.R.n : ℝ) / L.sc.x ^ (L.sc.eps / 100) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) := by
    rw [div_le_iff₀ hy0, mul_assoc, ← Real.rpow_add hx0]
    exact hV.ranks.n_le
  have hd : L.sc.delta1 * L.sc.x ^ (L.sc.eps / 100) ≤ 1 := by
    unfold Scale.delta1
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1'.le (by have := L.sc.eps_pos; linarith)
  have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0.le _
  have hnd : 2 * (D.R.n : ℝ) * L.sc.delta1 =
      2 * ((D.R.n : ℝ) / L.sc.x ^ (L.sc.eps / 100)) * (L.sc.delta1 * L.sc.x ^ (L.sc.eps / 100)) := by
    field_simp
  obtain ⟨-, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  obtain ⟨-, hTT, -, -, hg, -⟩ := hV.host
  rw [Real.rpow_one] at hb hX
  have hp : ∀ y : ℝ, Real.log y ≤ 2 * C.P.Cpde * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 → y < L.sc.X' := by
    intro y hy
    have a1 : y ≤ Real.exp (2 * C.P.Cpde * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) :=
      (Real.le_exp_log y).trans (Real.exp_le_exp.2 hy)
    have a2 : 1 < L.sc.x ^ (2 * C.P.Cpde) := Real.one_lt_rpow hx1' (by linarith)
    exact lt_of_le_of_lt a1 (lt_of_lt_of_le (lt_mul_of_one_lt_right (Real.exp_pos _) a2) hX)
  refine ⟨?_, hV.La_eq ▸ hLa1, fun j => ?_, hp _ hp1, hp _ hp2, hTT, ?_⟩
  · unfold G.rhoB G.Nstar
    rw [hnd]
    refine bandWidth_le_inv_sq_of_rank_bounds L.sc.x L.sc.eps _ _ _ _ (C.GK.La * CN ^ 2) _ hx1'
      (mul_nonneg hd0 hy0.le) hd (div_nonneg (Nat.cast_nonneg _) hy0.le) hn hk1
      ((Real.rpow_nonneg hx0.le _).trans hLa1) hLa2 ?_ ?_
    · rw [he]; exact h5 _ hx5
    · rw [he]; exact h6 _ hx6
  · have hk5 : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℝ) := by
      refine hk2.trans ?_
      have : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [he]; linarith)
      linarith
    have hX1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
    have hb0 : 0 < L.sc.b := Real.exp_pos _
    have h41 : L.sc.x ^ (41 : ℕ) ≤ L.sc.b := by
      have : L.sc.x ^ (41 : ℝ) ≤ L.sc.b :=
        (le_mul_of_one_le_right (Real.rpow_nonneg hx0.le _) hX1).trans hb
      exact_mod_cast this
    have hk5' : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℕ) := by exact_mod_cast hk5
    have e9 : Real.exp (9 * L.sc.L) = L.sc.b ^ 9 := by
      unfold Scale.b; rw [← Real.exp_nat_mul]; norm_num
    calc ((D.host.g j : ℕ) : ℝ) ≤ 2 * ((D.R.k : ℝ) * L.sc.b) ^ 8 := (hg j).2
      _ ≤ 2 * ((2 * L.sc.x ^ (5 : ℕ)) * L.sc.b) ^ 8 := by gcongr
      _ = 512 * L.sc.x ^ 40 * L.sc.b ^ 8 := by ring
      _ ≤ L.sc.x * L.sc.x ^ 40 * L.sc.b ^ 8 := by gcongr
      _ = L.sc.x ^ 41 * L.sc.b ^ 8 := by ring
      _ ≤ L.sc.b * L.sc.b ^ 8 := by gcongr
      _ = _ := by rw [e9]; ring
  · unfold ChCode_at
    rw [hV.words]
    exact Nat.le_ceil _

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_cond_qd_pde : SzRow (fun _ _ L => SizeCond L ∧ SizeQD L ∧ SizePde L) := by
  intro eps he he' C hC
  have hC8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x1, h1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  obtain ⟨x2, h2⟩ := hostBounds eps C.P.Cpde he he' hC8
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) eps 60150 72 (1 / 2) 2
    (by positivity) (by linarith) (by norm_num)
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 0 (eps / C.P.Cpde / 100) 2 0 (by positivity)
  obtain ⟨x6, h6⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) (eps / 5 + eps / 100) 1 2 (by linarith)
  obtain ⟨x7, h7⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) eps (2 * C.P.Cpde) 2 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ =>
    ⟨max (max (max x1 x2) (max x3 x4)) (max (max (Real.exp C.P.Cpde) x6) (max x7 (Real.exp 1))), ?_⟩⟩⟩
  intro D L hse hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, ⟨hx5, hx6⟩, hx7, hx8⟩ := hx
  have hr := h1 L.sc D.R hse hx1 hV.ranks
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ (401 : ℝ) := hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨q1, q2, d1, d2, hN, r1, r2, -, p1, p2⟩ := h2 L.sc D.R D.host hse hx2 hV.ranks hV.host
  have k3 := h3 _ hx3
  have k4 := h4 _ hx4
  have k6 := h6 _ hx6
  have k7 := h7 _ hx7
  subst hse
  have hxpos : 0 < L.sc.x := (Real.exp_pos 1).trans_le hx8
  have hlog : 1 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hxpos).mpr hx8
  have hlog2 : 1 ≤ Real.log L.sc.x ^ 2 := one_le_pow₀ hlog
  have hmul : L.sc.x ^ (L.sc.eps / 5) ≤ L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_nonneg hxpos.le _) hlog2
  simp only [pow_zero, mul_one, one_mul] at k6
  have hx1' : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hez : L.sc.eps / C.P.Cpde ≤ L.sc.ez := hostBounds_ez hV.host
  have hez0 : 0 ≤ L.sc.ez := le_trans (by positivity) hez
  have k40 : 2 ≤ L.sc.x ^ (L.sc.ez / 100) := by
    simp only [pow_zero, mul_one, Real.rpow_zero] at k4
    exact k4.trans (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith))
  have k5 : 2 * L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) ≤ L.sc.x ^ (L.sc.ez / 5) := by
    have e : L.sc.x ^ (L.sc.ez / 5) = L.sc.x ^ (L.sc.ez / 100) * L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right k40 (Real.rpow_nonneg hxpos.le _)
  have k41 : L.sc.x ^ (L.sc.ez / 6) ≤ L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hmz : L.sc.x ^ (L.sc.ez / 5) ≤ L.sc.x ^ (L.sc.ez / 5) * (Real.log L.sc.x / L.sc.J) ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_nonneg hxpos.le _)
      (one_le_pow₀ (hostBounds_one_le_log_div hV.host hx5))
  refine ⟨?_, ?_, ?_⟩
  · unfold SizeCond szCond Scale.b Scale.L
    have hA : ((D.host.QS : ℝ) * D.host.q * D.host.d) ≤
        Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) :=
      (Real.le_exp_log _).trans (Real.exp_le_exp.mpr hN)
    have hB : (D.R.t : ℝ) ≤ Real.exp (Real.log L.sc.x * 401) := by
      rwa [Real.rpow_def_of_pos hxpos] at ht
    rw [← Real.exp_half]
    calc ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 * (D.R.t : ℝ) ^ 150
        ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) ^ 36 *
            Real.exp (Real.log L.sc.x * 401) ^ 150 := by gcongr
      _ = Real.exp (((36 : ℕ) : ℝ) * (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) +
            ((150 : ℕ) : ℝ) * (Real.log L.sc.x * 401)) := by
          rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
      _ ≤ Real.exp (L.sc.x ^ L.sc.eps / 2) := by
          apply Real.exp_le_exp.mpr
          push_cast
          linarith
  · unfold SizeQD szTh
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, hV.dlog, r1, r2⟩
  · unfold SizePde Scale.L
    exact ⟨by linarith, by linarith⟩

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_typePrimes : SzRow (fun C D L => (∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧ (D.R.N D.R.m : ℝ) ^ 4 * (condE D : ℝ) ^ C.P.CY ≤ Y ^ ((1 : ℝ) / 4) ∧ Real.log Y ≤ C.P.CYL * L.sc.L ∧ ∀ i, Y ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * Y)) := by
  intro eps he he' C hC
  obtain ⟨-, -, -, -, -, hYL, -, -, -, -, -, -, hpde, -⟩ := hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.EX.hostBounds eps C.P.Cpde he he' hpde
  obtain ⟨x2, h2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  obtain ⟨x3, h3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 0 eps 1608 1 he
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) eps (2 * |C.P.CY|) 2 (by linarith)
  refine ⟨max (max x1 x2) (max x3 x4), fun D L hL hx V => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨-, -, -, -, hc, -⟩ := h1 L.sc D.R D.host hL hx1 V.ranks V.host
  obtain ⟨-, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, hN, -⟩ := h2 L.sc D.R hL hx2 V.ranks
  have h3' := h3 _ hx3
  have h4' := h4 _ hx4
  rw [Real.rpow_zero, mul_one, pow_one] at h3'
  rw [← hL] at h3' h4'
  have hLdef : L.sc.L = L.sc.x ^ L.sc.eps := rfl
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  rw [← hLdef] at h3' h4'
  have hx1' : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog : 0 < Real.log L.sc.x := Real.log_pos hx1'
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have h := V.ranks.2.2.1.1
    have : 1 ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps) := Real.one_le_rpow hx1'.le (by rw [hL]; linarith)
    linarith
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hbpos : 0 < L.sc.b := by rw [hb]; exact Real.exp_pos _
  have hkb : 0 < (D.R.k : ℝ) * L.sc.b := by positivity
  refine ⟨((D.R.k : ℝ) * L.sc.b) ^ 8, le_rfl, ?_, ?_, V.host.2.2.2.2.1⟩
  · have hY : (((D.R.k : ℝ) * L.sc.b) ^ 8) ^ ((1 : ℝ) / 4) = ((D.R.k : ℝ) * L.sc.b) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hkb.le, ← Real.rpow_natCast]
      norm_num
    rw [hY]
    have hcE : ((condE D : ℕ) : ℝ) = (D.host.QS : ℝ) * D.host.q * D.host.d := by
      unfold condE; push_cast; ring
    have hc1 : (1 : ℝ) ≤ (condE D : ℝ) := by
      have : condE D ≠ 0 := by
        have hQS := D.host.QS_pos
        have hq0 := D.host.hyp.1.pos
        have hd0 := D.host.hyp.2.1.pos
        unfold condE; positivity
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    rw [← hcE] at hc
    have hlc : 0 ≤ Real.log (condE D : ℝ) := Real.log_nonneg hc1
    have hA : (condE D : ℝ) ^ C.P.CY ≤ L.sc.b := by
      rw [Real.rpow_def_of_pos (by linarith), hb]
      apply Real.exp_le_exp.mpr
      calc Real.log (condE D : ℝ) * C.P.CY ≤ Real.log (condE D : ℝ) * |C.P.CY| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hlc
        _ ≤ (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) * |C.P.CY| :=
            mul_le_mul_of_nonneg_right hc (abs_nonneg _)
        _ = 2 * |C.P.CY| * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 := by ring
        _ ≤ _ := h4'
    have hB : (D.R.N D.R.m : ℝ) ^ 4 ≤ L.sc.b := by
      calc (D.R.N D.R.m : ℝ) ^ 4 ≤ (L.sc.x ^ (402 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 4
        _ = Real.exp (1608 * Real.log L.sc.x) := by
            rw [Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]; congr 1; push_cast; ring
        _ ≤ L.sc.b := by rw [hb]; exact Real.exp_le_exp.mpr h3'
    calc (D.R.N D.R.m : ℝ) ^ 4 * (condE D : ℝ) ^ C.P.CY ≤ L.sc.b * L.sc.b :=
          mul_le_mul hB hA (Real.rpow_nonneg (by linarith) _) hbpos.le
      _ = L.sc.b ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ hbpos.le (le_mul_of_one_le_left hbpos.le hk1) 2
  · rw [hYL, Real.log_pow, Real.log_mul (by positivity) hbpos.ne', hb, Real.log_exp]
    have : Real.log (D.R.k : ℝ) ≤ 5 * Real.log L.sc.x := by
      rw [← Real.log_rpow hx0]; exact Real.log_le_log (by linarith) hk5
    push_cast
    linarith

end GlobalTheory.EX
end
