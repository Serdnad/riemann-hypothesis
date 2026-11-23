module

public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section act

variable {dim : (E →+* ℂ) → ℕ}

def actE (β : E) (v : Vsp dim) : Vsp dim := WithLp.toLp 2 fun i => i.1 β * v i

theorem act_eq_actE (α : 𝓞 E) (v : Vsp dim) : act α v = actE (α : E) v := rfl

@[simp] theorem actE_apply (β : E) (v : Vsp dim) (i : Idx dim) : actE β v i = i.1 β * v i := rfl

theorem actE_add_right (β : E) (v w : Vsp dim) : actE β (v + w) = actE β v + actE β w := by
  ext i
  simp [mul_add]

theorem actE_smul_right (β : E) (c : ℂ) (v : Vsp dim) : actE β (c • v) = c • actE β v := by
  ext i
  simp only [actE_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem actE_rsmul_right (β : E) (r : ℝ) (v : Vsp dim) : actE β (r • v) = r • actE β v := by
  ext i
  simp only [actE_apply, PiLp.smul_apply, Complex.real_smul]
  ring

theorem actE_zero_right (β : E) : actE β (0 : Vsp dim) = 0 := by
  ext i
  simp

theorem actE_add_left (β γ : E) (v : Vsp dim) : actE (β + γ) v = actE β v + actE γ v := by
  ext i
  simp [add_mul]

theorem actE_zero_left (v : Vsp dim) : actE (0 : E) v = 0 := by
  ext i
  simp

theorem actE_one (v : Vsp dim) : actE (1 : E) v = v := by
  ext i
  simp

theorem actE_mul (β γ : E) (v : Vsp dim) : actE (β * γ) v = actE β (actE γ v) := by
  ext i
  simp [mul_assoc]

theorem actE_qsmul (q : ℚ) (β : E) (v : Vsp dim) : actE (q • β) v = (q : ℝ) • actE β v := by
  ext i
  simp only [actE_apply, PiLp.smul_apply, Complex.real_smul, Rat.smul_def, map_mul, map_ratCast,
    Complex.ofReal_ratCast]
  ring

theorem act_one' (v : Vsp dim) : act (1 : 𝓞 E) v = v := by
  rw [act_eq_actE]
  simpa using actE_one v

theorem act_mul' (α β : 𝓞 E) (v : Vsp dim) : act (α * β) v = act α (act β v) := by
  rw [act_eq_actE, act_eq_actE, act_eq_actE]
  push_cast
  exact actE_mul _ _ v

theorem norm_actE_le (β : E) (Ω : ℝ) (hΩ : 0 ≤ Ω) (h : ∀ σ : E →+* ℂ, ‖σ β‖ ≤ Ω) (v : Vsp dim) :
    ‖actE β v‖ ≤ Ω * ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hΩ, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [actE_apply, norm_mul, mul_pow]
  gcongr
  exact h i.1

theorem actE_mem_of_span (β : E) (S : Set (Vsp dim)) (T : Submodule ℝ (Vsp dim))
    (h : ∀ v ∈ S, actE β v ∈ T) : ∀ v ∈ Submodule.span ℝ S, actE β v ∈ T := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [actE_zero_right]; exact T.zero_mem
  | add x y _ _ hx hy => rw [actE_add_right]; exact T.add_mem hx hy
  | smul r x _ hx => rw [actE_rsmul_right]; exact T.smul_mem r hx

theorem actE_mem_span_omega {n : ℕ} (ω : Fin n → E) {β : E}
    (hβ : β ∈ Submodule.span ℚ (Set.range ω)) (x : Vsp dim) :
    actE β x ∈ Submodule.span ℝ (Set.range fun j => actE (ω j) x) := by
  induction hβ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [actE_zero_left]; exact zero_mem _
  | add y z _ _ hy hz => rw [actE_add_left]; exact add_mem hy hz
  | smul q y _ hy => rw [actE_qsmul]; exact Submodule.smul_mem _ _ hy

variable [IsCMField E]

theorem Hf_actE (β : E) (v w : Vsp dim) :
    Hf (actE β v) w = Hf v (actE (IsCMField.complexConj E β) w) := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [actE_apply, map_mul, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
  ring

theorem Hf_actE' (β : E) (v w : Vsp dim) :
    Hf v (actE β w) = Hf (actE (IsCMField.complexConj E β) v) w := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [actE_apply, map_mul, IsCMField.complexEmbedding_complexConj]
  ring

end act

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem short_vector_bound_le_kappa [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hph : 0 < P.ph) :
    PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E) ≤ P.ka0 * P.ph := by
  unfold Par.ka0 Par.ph RR
  have hph' : 0 < X.ph (th P.q P.R0) := hph
  have hf1 : 1 ≤ PT.f E := le_trans (Nat.one_le_pow 4 P.m P.hm1) P.hmf
  have hm2 : P.m ^ 2 ≤ PT.f E := le_trans (Nat.pow_le_pow_right P.hm1 (by norm_num)) P.hmf
  have hF : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1
  have hM2 : (P.m : ℝ) ^ 2 ≤ PT.f E := by exact_mod_cast hm2
  have hFR : (PT.f E : ℝ) ≤ PT.rd E := P.hfrd
  have hR : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hM0 : (0 : ℝ) ≤ P.m := Nat.cast_nonneg _
  have hd : (dstar (E := E) P.m : ℝ) = 2 * (PT.f E : ℝ) * P.m := by unfold dstar; push_cast; ring
  rw [hd, div_le_iff₀ (by linarith)]
  have key1 : (PT.f E : ℝ) * (P.m : ℝ) ^ 2 ≤ PT.rd E ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hM2 (by linarith : (0 : ℝ) ≤ PT.f E),
      mul_le_mul hFR hFR (by linarith) (by linarith)]
  have h3 : PT.rd E ^ 4 * (PT.f E : ℝ) ≤ PT.rd E ^ 7 * PT.f E :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by norm_num)) (by linarith)
  have h4 := mul_le_mul_of_nonneg_left key1 (by positivity : (0 : ℝ) ≤ 4 * PT.rd E ^ 2 * PT.f E)
  have key2 : PT.rd E ^ 2 * (2 * (PT.f E : ℝ) * P.m) ^ 2 ≤ 8 * PT.rd E ^ 7 * PT.f E := by
    nlinarith [h3, h4, (by positivity : (0 : ℝ) ≤ PT.rd E ^ 7 * PT.f E)]
  have hd2 := mul_nonneg (sq_nonneg (2 * (PT.f E : ℝ) * P.m)) hph'.le
  nlinarith [mul_le_mul_of_nonneg_right key2 hd2]

theorem tof_inv_sqrt_le [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hph : 0 < P.ph) (n : ℕ)
    (hn : n ≤ dstar (E := E) P.m) (c : ℝ) (hc : 0 < c)
    (h1 : 1 ≤ c * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ n) :
    1 / Real.sqrt (c * (2 : ℝ) ^ (-(n : ℝ) / 2)) ≤
      Real.exp (dstar (E := E) P.m) * (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) := by
  have hU := short_vector_bound_le_kappa P hph
  have hf1 : 1 ≤ PT.f E := le_trans (Nat.one_le_pow 4 P.m P.hm1) P.hmf
  have hF : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1
  have hR : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hR0 : (0 : ℝ) < PT.rd E := by linarith
  have hdR : ((dstar (E := E) P.m : ℕ) : ℝ) = 2 * (PT.f E : ℝ) * P.m := by
    unfold dstar; push_cast; ring
  have hm1 : (1 : ℝ) ≤ P.m := by exact_mod_cast P.hm1
  have hd1 : (1 : ℝ) ≤ ((dstar (E := E) P.m : ℕ) : ℝ) := by rw [hdR]; nlinarith
  have hph2 := hph
  unfold Par.ph PT.ph at hph2
  split_ifs at hph2 with hlt
  swap
  · exact absurd hph2 (lt_irrefl 0)
  have hL0 : 0 ≤ X.la1 := by
    unfold PT.la1
    exact Real.sInf_nonneg (by rintro t ⟨x, -, -, rfl⟩; exact norm_nonneg x)
  have hla : 0 < X.la1 ^ 2 := by
    rcases (sq_nonneg X.la1).lt_or_eq with h | h
    · exact h
    · rw [← h] at hph2; simp at hph2
  have hC1 := P.C1
  have hom : (1 : ℝ) ≤ omStar (E := E) := by
    unfold omStar
    first
      | nlinarith [Real.one_le_rpow hF (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      | nlinarith [one_le_pow₀ (n := 3 / 2) hF]
      | (norm_num; nlinarith)
  have hZ : (1 : ℝ) ≤ ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 * omStar (E := E) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd1) hom
  have h2 := mul_self_lt_mul_self hL0 hlt
  have hth : X.la1 ^ 2 < 1 := by
    nlinarith [hC1, hZ, h2, mul_nonneg (sub_nonneg.mpr hZ) (lt_of_le_of_lt (mul_self_nonneg X.la1) h2).le]
  have hK1 : 1 ≤ P.ka0 * P.ph := by
    unfold Par.ka0 Par.ph PT.ph RR
    rw [if_pos hlt]
    have hden : PT.rd E ^ 2 * X.la1 ^ 2 ≠ 0 := (mul_pos (pow_pos hR0 2) hla).ne'
    have hY := div_mul_cancel₀ (2 * (PT.f E : ℝ)) hden
    set Y : ℝ := 2 * (PT.f E : ℝ) / (PT.rd E ^ 2 * X.la1 ^ 2) with hYd
    have hY0 : 0 < Y := hph2
    have h5 : 2 * (PT.f E : ℝ) ≤ Y * PT.rd E ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hth.le) (mul_pos hY0 (pow_pos hR0 2)).le]
    have h6 : (1 : ℝ) ≤ PT.rd E ^ 5 * ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hd1)
    nlinarith [mul_le_mul h6 h5 (by positivity) (by linarith)]
  set K : ℝ := P.ka0 * P.ph with hKd
  have hK0 : 0 ≤ K := by linarith
  have hsK : 1 ≤ √K := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hK1
  have e1 := by
    first
      | exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hU) n
      | exact pow_le_pow_left (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hU) n
  have e2 : √K ^ n ≤ √K ^ (dstar (E := E) P.m) := by
    first
      | exact pow_le_pow_right₀ hsK hn
      | exact pow_le_pow_right hsK hn
  have hcK : 1 ≤ c * √K ^ (dstar (E := E) P.m) :=
    h1.trans (mul_le_mul_of_nonneg_left (e1.trans e2) hc.le)
  have hpow : (K ^ (((dstar (E := E) P.m : ℕ) : ℝ) / 4)) ^ 2 = √K ^ (dstar (E := E) P.m) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast (K ^ (1 / 2 : ℝ)),
      ← Real.rpow_mul hK0, ← Real.rpow_mul hK0]
    congr 1
    push_cast
    ring
  have hE : (1 : ℝ) ≤ Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-(n : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul, ← Real.exp_add]
    refine le_trans ?_ (Real.add_one_le_exp _)
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hnd : (n : ℝ) ≤ ((dstar (E := E) P.m : ℕ) : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hl2 hn0]
  have hc2 : 0 < c * (2 : ℝ) ^ (-(n : ℝ) / 2) := mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)
  have hA : 0 < √(c * (2 : ℝ) ^ (-(n : ℝ) / 2)) := Real.sqrt_pos.mpr hc2
  rw [div_le_iff₀ hA]
  have hx0 : 0 ≤ Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) * K ^ (((dstar (E := E) P.m : ℕ) : ℝ) / 4) *
      √(c * (2 : ℝ) ^ (-(n : ℝ) / 2)) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hK0 _)) (Real.sqrt_nonneg _)
  have hsq : (Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) * K ^ (((dstar (E := E) P.m : ℕ) : ℝ) / 4) *
      √(c * (2 : ℝ) ^ (-(n : ℝ) / 2))) ^ 2 =
      (c * √K ^ (dstar (E := E) P.m)) *
        (Real.exp ((dstar (E := E) P.m : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-(n : ℝ) / 2)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hc2.le, hpow]
    ring
  have hge := one_le_mul_of_one_le_of_one_le hcK hE
  rw [← hsq] at hge
  nlinarith [hge, hx0]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

section ItD

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

def itD (f : W → ℂ) (l : List W) (z : W) : ℂ :=
  iteratedFDeriv ℂ l.length f z (fun j => l.get j)

theorem itD_nil (f : W → ℂ) (z : W) : itD f [] z = f z := by
  simp only [itD]
  first
    | exact iteratedFDeriv_zero_apply _
    | simp

theorem itD_differentiable {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (l : List W) :
    Differentiable ℂ (fun y => itD f l y) := by
  have hD : Differentiable ℂ (iteratedFDeriv ℂ l.length f) := by
    refine hf.differentiable_iteratedFDeriv ?_
    first
      | exact_mod_cast ENat.coe_lt_top _
      | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top _)
      | simp
  unfold itD
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin l.length => W) ℂ _).differentiable.comp hD

theorem itD_cons {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (e : W) (l : List W) (z : W) :
    itD f (e :: l) z = fderiv ℂ (fun y => itD f l y) z e := by
  have hD : Differentiable ℂ (iteratedFDeriv ℂ l.length f) := by
    refine hf.differentiable_iteratedFDeriv ?_
    first
      | exact_mod_cast ENat.coe_lt_top _
      | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top _)
      | simp
  show iteratedFDeriv ℂ (l.length + 1) f z (fun j => (e :: l).get j) = _
  rw [iteratedFDeriv_succ_apply_left]
  have hc : (fun y => itD f l y) =
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin l.length => W) ℂ (fun j => l.get j)) ∘
        iteratedFDeriv ℂ l.length f := rfl
  rw [hc, fderiv_comp z (ContinuousLinearMap.differentiableAt _) (hD z), ContinuousLinearMap.fderiv]
  rfl

theorem fderiv_prod_single {n : ℕ} {h : Fin n → W → ℂ} (hh : ∀ k, Differentiable ℂ (h k))
    (x : Fin n → W) (k0 : Fin n) (e : W) :
    fderiv ℂ (fun y : Fin n → W => ∏ k, h k (y k)) x (Pi.single k0 e) =
      (∏ k ∈ Finset.univ.erase k0, h k (x k)) * fderiv ℂ (h k0) (x k0) e := by
  classical
  have hd : ∀ k, HasFDerivAt (fun y : Fin n → W => h k (y k))
      ((fderiv ℂ (h k) (x k)).comp (ContinuousLinearMap.proj k)) x :=
    fun k => ((hh k) (x k)).hasFDerivAt.comp x (hasFDerivAt_apply k x)
  have hP : HasFDerivAt (fun y : Fin n → W => ∏ k, h k (y k))
      (∑ k, (∏ j ∈ Finset.univ.erase k, h j (x j)) •
        ((fderiv ℂ (h k) (x k)).comp (ContinuousLinearMap.proj k))) x :=
    HasFDerivAt.finsetProd (fun k _ => hd k)
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single k0]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

def colL {n : ℕ} (L : List (Fin n × W)) (k : Fin n) : List W :=
  (L.filter (fun p => p.1 = k)).map Prod.snd

theorem colL_cons {n : ℕ} (a : Fin n × W) (L : List (Fin n × W)) (k : Fin n) :
    colL (a :: L) k = if a.1 = k then a.2 :: colL L k else colL L k := by
  unfold colL
  by_cases h : a.1 = k <;> simp [List.filter_cons, h]

theorem itD_prod {n : ℕ} {g : Fin n → W → ℂ} (hg : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (g k))
    (L : List (Fin n × W)) (x : Fin n → W) :
    itD (fun v : Fin n → W => ∏ k, g k (v k)) (L.map fun p => Pi.single p.1 p.2) x =
      ∏ k, itD (g k) (colL L k) (x k) := by
  have hP : ContDiff ℂ (⊤ : ℕ∞) (fun v : Fin n → W => ∏ k, g k (v k)) := by
    first
      | exact contDiff_prod fun k _ => (hg k).comp (contDiff_apply ℂ W k)
      | fun_prop
  induction L generalizing x with
  | nil => simp [itD_nil, colL]
  | cons a L ih =>
    simp only [List.map_cons]
    rw [itD_cons hP]
    have hfun : (fun y => itD (fun v : Fin n → W => ∏ k, g k (v k))
        (L.map fun p => Pi.single p.1 p.2) y) = fun y => ∏ k, itD (g k) (colL L k) (y k) :=
      funext fun y => ih y
    rw [hfun, fderiv_prod_single (h := fun k y => itD (g k) (colL L k) y)
      (fun k => itD_differentiable (hg k) _)]
    rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ a.1)]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      rw [colL_cons, if_neg (Ne.symm (Finset.ne_of_mem_erase hk))]
    · rw [colL_cons, if_pos rfl, itD_cons (hg _)]

theorem itD_col {s : (Fin 1 → W) → ℂ} (hs : ContDiff ℂ (⊤ : ℕ∞) s) (l : List W) :
    itD (fun z : W => s (fun _ => z)) l 0 = iteratedFDeriv ℂ l.length s 0 (fun j _ => l.get j) := by
  unfold itD
  have hi : ((l.length : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    first
      | exact_mod_cast le_top
      | exact WithTop.coe_le_coe.2 le_top
  have h := (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℂ W).iteratedFDeriv_comp_right
    hs (0 : W) hi
  exact congrArg (fun T => T (fun j => l.get j)) h

end ItD

section PD

variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

def pdTerm (u : σ → W) (F : W → ℂ) (x : W) (m : σ →₀ ℕ) : ℂ :=
  iteratedFDeriv ℂ (Multiset.card (Finsupp.toMultiset m)) F x
    (fun k => u ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm)))

theorem polyDeriv_eq_of_subset (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W)
    {S : Finset (σ →₀ ℕ)} (hS : P.support ⊆ S) :
    polyDeriv P u F x = ∑ m ∈ S, P.coeff m * pdTerm u F x m := by
  unfold polyDeriv
  refine Finset.sum_subset hS fun m _ hm => ?_
  first
    | rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]
    | rw [MvPolynomial.not_mem_support_iff.1 hm, zero_mul]

theorem polyDeriv_add (P Q : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (P + Q) u F x = polyDeriv P u F x + polyDeriv Q u F x := by
  classical
  rw [polyDeriv_eq_of_subset (P + Q) u F x (S := P.support ∪ Q.support) MvPolynomial.support_add,
    polyDeriv_eq_of_subset P u F x (S := P.support ∪ Q.support) (fun _ h => Finset.mem_union_left _ h),
    polyDeriv_eq_of_subset Q u F x (S := P.support ∪ Q.support) (fun _ h => Finset.mem_union_right _ h),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem jof_polyDeriv_sum {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ)
    (x : W) : polyDeriv (∑ i ∈ s, P i) u F x = ∑ i ∈ s, polyDeriv (P i) u F x := by
  exact map_sum (AddMonoidHom.mk' (fun Q : MvPolynomial σ ℂ => polyDeriv Q u F x)
    (fun Q R => polyDeriv_add Q R u F x)) P s

theorem polyDeriv_smul (c : ℂ) (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (c • P) u F x = c * polyDeriv P u F x := by
  classical
  rw [polyDeriv_eq_of_subset (c • P) u F x (S := P.support) MvPolynomial.support_smul,
    polyDeriv_eq_of_subset P u F x (S := P.support) subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]

theorem polyDeriv_monomial_one (m : σ →₀ ℕ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (MvPolynomial.monomial m (1 : ℂ)) u F x = pdTerm u F x m := by
  classical
  rw [polyDeriv_eq_of_subset _ u F x (S := {m}) MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl, one_mul]

theorem pdTerm_eq_itD (u : σ → W) (F : W → ℂ) (x : W) (m : σ →₀ ℕ) :
    pdTerm u F x m = itD F ((Finsupp.toMultiset m).toList.map u) x := by
  have gen : ∀ (n₁ n₂ : ℕ) (h : n₁ = n₂) (v₁ : Fin n₁ → W) (v₂ : Fin n₂ → W),
      (∀ i, v₁ i = v₂ (i.cast h)) → iteratedFDeriv ℂ n₁ F x v₁ = iteratedFDeriv ℂ n₂ F x v₂ := by
    intro n₁ n₂ h v₁ v₂ hv
    subst h
    exact congrArg _ (funext fun i => hv i)
  unfold pdTerm itD
  refine gen _ _ (by simp) _ _ fun i => ?_
  simp

end PD

end

end ReciprocityTheory.ChartRestriction.G.I2
end
