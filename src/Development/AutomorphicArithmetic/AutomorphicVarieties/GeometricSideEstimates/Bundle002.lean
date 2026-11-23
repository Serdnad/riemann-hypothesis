module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private lemma re_mul_conj (z : ℂ) : (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

private lemma sum_mul_le {ι : Type} [Fintype ι] (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, f i * g i ≤ (∑ i, f i) * ∑ i, g i := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => hg j) (Finset.mem_univ i)) (hf i)

private lemma cs_norm {ι : Type} [Fintype ι] (f g : ι → ℂ) :
    ‖∑ i, f i * g i‖ ^ 2 ≤ (∑ i, ‖f i‖ ^ 2) * ∑ i, ‖g i‖ ^ 2 := by
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖f i‖) (fun i => ‖g i‖))
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private lemma qf_eq (w : Fin a → Cinf E) : qf w = ∑ v : InfinitePlace E, ∑ i, ‖w i v‖ ^ 2 := by
  unfold qf; exact Finset.sum_comm

private lemma trF_eq (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF X Y = (∑ p : InfinitePlace E × Fin a × Fin a, X p.2.1 p.2.2 p.1 * Y p.2.2 p.2.1 p.1).re := by
  simp [trF, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_apply]

private lemma quad_eq (w x : Fin a → Cinf E) :
    quad (vecMulVec w (star w)) x = ∑ v : InfinitePlace E, ‖(x ⬝ᵥ w) v‖ ^ 2 := by
  unfold quad
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.vecMul_vecMulVec, smul_dotProduct, ← re_mul_conj]
  congr 1
  simp [dotProduct, Finset.sum_apply, mul_comm]

end

theorem UpperTheory.traceForm_cauchy_schwarz_cmDatum :
    RankOne := by
  intro E _ _ a w
  refine ⟨?_, fun M => ?_, fun x => ⟨?_, ?_, fun h => ?_⟩⟩
  · rw [qf_eq]
    unfold trF
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Matrix.one_mul, Matrix.trace, Matrix.diag, vecMulVec_apply, Finset.sum_apply, Complex.re_sum,
      Pi.mul_apply, Pi.star_apply, Complex.star_def, re_mul_conj]
  · have hM : ∀ i j v, M.1 j i v = (starRingEnd ℂ) (M.1 i j v) := by
      intro i j v
      have h : star M.1 = M.1 := M.2
      conv_lhs => rw [← h]
      rfl
    have h1 : trF M.1 M.1 = ∑ p : InfinitePlace E × Fin a × Fin a, ‖M.1 p.2.1 p.2.2 p.1‖ ^ 2 := by
      rw [trF_eq, Complex.re_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hM p.2.1 p.2.2, re_mul_conj]
    have h2 : ∑ p : InfinitePlace E × Fin a × Fin a, ‖(vecMulVec w (star w)) p.2.2 p.2.1 p.1‖ ^ 2 ≤ qf w ^ 2 := by
      rw [qf_eq, sq (∑ v : InfinitePlace E, ∑ i, ‖w i v‖ ^ 2)]
      refine le_trans (le_of_eq ?_) (sum_mul_le _ _ (fun v => by positivity) (fun v => by positivity))
      simp only [Fintype.sum_prod_type, Finset.sum_mul_sum, vecMulVec_apply, Pi.mul_apply, Pi.star_apply,
        norm_mul, norm_star, mul_pow, mul_comm]
    rw [h1, trF_eq]
    refine le_trans ?_ ((cs_norm _ _).trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
    exact sq_le_sq' (abs_le.1 (Complex.abs_re_le_norm _)).1 (abs_le.1 (Complex.abs_re_le_norm _)).2
  · rw [quad_eq]
    have hs : 0 ≤ ∑ v : InfinitePlace E, ‖(x ⬝ᵥ w) v‖ ^ 2 := by positivity
    rw [← Real.le_sqrt (norm_nonneg _) hs]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_
    rw [Real.le_sqrt (norm_nonneg _) hs]
    exact Finset.single_le_sum (f := fun v => ‖(x ⬝ᵥ w) v‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ v)
  · rw [quad_eq, qf_eq, qf_eq, mul_comm]
    refine le_trans ?_ (sum_mul_le _ _ (fun v => by positivity) (fun v => by positivity))
    refine Finset.sum_le_sum fun v _ => ?_
    have := cs_norm (fun i => x i v) (fun i => w i v)
    simpa [dotProduct, Finset.sum_apply] using this
  · rw [quad_eq, h]; simp
end

section

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chart_prod (f f' : GA E a → ℂ) (g : GA E a) :
    chart (f * f') g = chart f g * chart f' g := by
  funext x
  simp only [Pi.mul_apply, chart]
  split_ifs <;> simp

private theorem sm_prod_mem {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) : f * f' ∈ Sm E a := by
  intro g
  rw [chart_prod]
  exact (h g).mul (h' g)

private theorem leibniz (X : Lie E a) {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) :
    lieD X (f * f') = f * lieD X f' + lieD X f * f' := by
  funext g
  have v : ∀ u : GA E a → ℂ, chart u g (oneL E a) = u g := fun u => by
    simpa using chart_val u g 1
  simp only [lieD, Pi.add_apply, Pi.mul_apply]
  rw [chart_prod, fderiv_mul (differentiableAt_chart h g) (differentiableAt_chart h' g), v, v]
  simp [mul_comm]

private theorem const_ev (c : ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (algebraMap ℂ (GA E a → ℂ) c) g x = c := by
  unfold chart
  rw [dite_eq_left (show IsUnit (Matrix.of x) from hx)]
  rfl

private theorem const_mem (c : ℂ) : algebraMap ℂ (GA E a → ℂ) c ∈ Sm E a := fun g =>
  contDiffOn_const.congr fun _ hx => const_ev c g hx

private theorem lie_const (X : Lie E a) (c : ℂ) : lieD X (algebraMap ℂ (GA E a → ℂ) c) = 0 := by
  funext g
  have e : chart (algebraMap ℂ (GA E a → ℂ) c) g =ᶠ[nhds (oneL E a)] fun _ => c := by
    have h1 : oneL E a ∈ invSet E a := isUnit_one
    filter_upwards [isOpen_invSet.mem_nhds h1] with x hx using const_ev c g hx
  rw [lieD, e.fderiv_eq]
  simp

end

theorem UpperTheory.lieDerivative_isDerivation_smoothFunctions :
    BddAlg := by
  intro E _ _ _ a S hS
  have key : ∀ f ∈ Algebra.adjoin ℂ S, (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ f ∈ Sm E a ∧
      ∀ X : Lie E a, lieD X f ∈ Algebra.adjoin ℂ S := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      obtain ⟨hb, φ, rfl, hX⟩ := hS f hf
      exact ⟨hb, φ.2, hX⟩
    | algebraMap c =>
      exact ⟨⟨‖c‖, fun g => by simp⟩, const_mem c, fun X => by rw [lie_const]; exact zero_mem _⟩
    | add f f' _ _ h h' =>
      obtain ⟨⟨C, hC⟩, hs, hX⟩ := h
      obtain ⟨⟨C', hC'⟩, hs', hX'⟩ := h'
      refine ⟨⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩, add_mem hs hs', fun X => ?_⟩
      have e : lieD X (f + f') = lieD X f + lieD X f' :=
        congrArg Subtype.val ((lie E a X).map_add (⟨f, hs⟩ : Sm E a) (⟨f', hs'⟩ : Sm E a))
      rw [e]
      exact add_mem (hX X) (hX' X)
    | mul f f' hf hf' h h' =>
      obtain ⟨⟨C, hC⟩, hs, hX⟩ := h
      obtain ⟨⟨C', hC'⟩, hs', hX'⟩ := h'
      refine ⟨⟨C * C', fun g => (norm_mul_le _ _).trans
        (mul_le_mul (hC g) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC g)))⟩, sm_prod_mem hs hs', fun X => ?_⟩
      rw [leibniz X hs hs']
      exact add_mem (mul_mem hf (hX' X)) (mul_mem (hX X) hf')
  have main : ∀ ψ : Sm E a, (∀ X, (lie E a X ψ).1 ∈ Algebra.adjoin ℂ S) → BddDer ψ := by
    intro ψ hψ
    have h : ∀ (l : List (Lie E a)) (X : Lie E a),
        (((X :: l).map (lie E a)).prod ψ).1 ∈ Algebra.adjoin ℂ S := by
      intro l
      induction l with
      | nil => intro X; simpa using hψ X
      | cons Y l ih =>
        intro X
        rw [List.map_cons, List.prod_cons]
        exact (key _ (ih Y)).2.2 X
    exact fun X l => (key _ (h l X)).1
  exact ⟨fun f hf => ⟨⟨f, (key f hf).2.1⟩, rfl, main _ (key f hf).2.2⟩, main⟩
end

section

open UpperTheory.V.Lit.Geo

private theorem exp_quad (x : ℝ) : Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  rcases le_or_gt |x| 1 with h | h
  · have h1 := Real.abs_exp_sub_one_sub_id_le h
    have h2 : x ^ 2 ≤ x ^ 2 * Real.exp |x| :=
      le_mul_of_one_le_right (sq_nonneg x) (Real.one_le_exp (abs_nonneg x))
    have h3 := (abs_le.mp h1).2
    linarith
  · rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx] at h ⊢
      have : Real.exp x ≤ x ^ 2 * Real.exp x :=
        le_mul_of_one_le_left (Real.exp_pos x).le (by nlinarith)
      linarith
    · rw [abs_of_neg hx] at h ⊢
      have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx.le
      have h2 : x ^ 2 ≤ x ^ 2 * Real.exp (-x) :=
        le_mul_of_one_le_right (sq_nonneg x) (Real.one_le_exp (by linarith))
      nlinarith

private theorem up_pt (q u ε : ℝ) (hq : 0 ≤ q) (h0 : 0 ≤ ε) (h4 : ε ≤ 1 / 4) (hu : |u| ≤ ε * q) :
    Real.exp (-Real.pi * (q + u)) ≤ Real.exp (-Real.pi * q) + -Real.pi * (u * Real.exp (-Real.pi * q)) +
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by
  have hpi := Real.pi_pos
  have hE : Real.exp (-Real.pi * (q + u)) = Real.exp (-Real.pi * q) * Real.exp (-Real.pi * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hx := exp_quad (-Real.pi * u)
  have habs : |-Real.pi * u| = Real.pi * |u| := by
    rw [abs_mul, abs_neg, abs_of_pos hpi]
  rw [habs] at hx
  have hu4 : |u| ≤ q / 4 := by nlinarith [abs_nonneg u, mul_nonneg (sub_nonneg.mpr h4) hq]
  have hu2 : u ^ 2 ≤ ε ^ 2 * q ^ 2 := by
    have := mul_self_le_mul_self (abs_nonneg u) hu
    nlinarith [sq_abs u]
  have hpu : Real.pi * |u| ≤ Real.pi * (q / 4) := mul_le_mul_of_nonneg_left hu4 hpi.le
  have hy0 : 0 ≤ Real.pi * q / 4 := by positivity
  have hexp1 : Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q) ≤
      Real.exp (-Real.pi * (1 / 2 * q)) * Real.exp (-(Real.pi * q / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hquad : (Real.pi * q / 4) ^ 2 ≤ 2 * Real.exp (Real.pi * q / 4) := by
    have := Real.quadratic_le_exp_of_nonneg hy0
    nlinarith
  have hey : (Real.pi * q / 4) ^ 2 * Real.exp (-(Real.pi * q / 4)) ≤ 2 := by
    have h1 : Real.exp (Real.pi * q / 4) * Real.exp (-(Real.pi * q / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    have h2 := Real.exp_pos (-(Real.pi * q / 4))
    nlinarith
  have A : (-Real.pi * u) ^ 2 ≤ ε ^ 2 * (Real.pi ^ 2 * q ^ 2) := by
    have : (-Real.pi * u) ^ 2 = Real.pi ^ 2 * u ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg Real.pi]
  have hterm : (-Real.pi * u) ^ 2 * Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q) ≤
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by
    calc (-Real.pi * u) ^ 2 * Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q)
        = (-Real.pi * u) ^ 2 * (Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q)) := by ring
      _ ≤ (ε ^ 2 * (Real.pi ^ 2 * q ^ 2)) *
            (Real.exp (-Real.pi * (1 / 2 * q)) * Real.exp (-(Real.pi * q / 4))) :=
          mul_le_mul A hexp1 (by positivity) (by positivity)
      _ = 16 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) *
            ((Real.pi * q / 4) ^ 2 * Real.exp (-(Real.pi * q / 4))) := by ring
      _ ≤ 16 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) * 2 := by gcongr
      _ = 32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by ring
  rw [hE]
  have hE0 := Real.exp_pos (-Real.pi * q)
  have hm := mul_le_mul_of_nonneg_left hx hE0.le
  nlinarith

private theorem low_pt (q u m : ℝ) :
    Real.exp m * ((1 - m) * Real.exp (-Real.pi * q) + -Real.pi * (u * Real.exp (-Real.pi * q))) ≤
      Real.exp (-Real.pi * (q + u)) := by
  have h := Real.add_one_le_exp (-Real.pi * u - m)
  have hE : Real.exp (-Real.pi * (q + u)) =
      Real.exp m * Real.exp (-Real.pi * q) * Real.exp (-Real.pi * u - m) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hE]
  have hp : 0 ≤ Real.exp m * Real.exp (-Real.pi * q) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hp]

private theorem sum_pt (q u ε : ℝ) (hq : 0 ≤ q) (h4 : ε ≤ 1 / 4) (hu : |u| ≤ ε * q) :
    ‖u * Real.exp (-Real.pi * q)‖ ≤ Real.exp (-Real.pi * (1 / 2 * q)) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hu4 : |u| ≤ q / 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr h4) hq]
  have hpi := Real.pi_pos
  have h1 := Real.add_one_le_exp (Real.pi * q / 2)
  have hsplit : Real.exp (-Real.pi * (1 / 2 * q)) =
      Real.exp (-Real.pi * q) * Real.exp (Real.pi * q / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have hE := Real.exp_pos (-Real.pi * q)
  have h2 : q / 4 ≤ Real.exp (Real.pi * q / 2) := by nlinarith [Real.pi_gt_three]
  calc |u| * Real.exp (-Real.pi * q) ≤ q / 4 * Real.exp (-Real.pi * q) :=
        mul_le_mul_of_nonneg_right hu4 hE.le
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 hE.le

theorem UpperTheory.two_sided_bound_of_pointwise_bounds :
    LogTaylor := by
  intro N
  refine ⟨32 * 2 ^ N, by positivity, ?_⟩
  intro ι _ q u ε hS h0 h4 hu
  obtain ⟨hq, hsc⟩ := hS
  have hsum1 := (hsc 1 1 one_pos le_rfl).1
  simp only [one_mul] at hsum1
  have hhalf := hsc (1 / 2) 1 (by norm_num) (by norm_num)
  have hsumh : Summable fun i => Real.exp (-Real.pi * (1 / 2 * q i)) := hhalf.1
  have hSle : ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) ≤
      2 ^ N * ∑' i, Real.exp (-Real.pi * q i) := by
    have h := hhalf.2
    have h2 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
    rw [h2] at h
    simp only [one_mul] at h
    exact h
  set Z := ∑' i, Real.exp (-Real.pi * q i) with hZ
  set Z' := ∑' i, Real.exp (-Real.pi * (q i + u i)) with hZ'
  set M := ∑' i, u i * Real.exp (-Real.pi * q i) with hM
  set S := ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) with hS'
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hZpos : 0 < Z := hsum1.tsum_pos (fun i => (Real.exp_pos _).le) i0 (Real.exp_pos _)
  have hsumM : Summable fun i => u i * Real.exp (-Real.pi * q i) :=
    Summable.of_norm_bounded hsumh (fun i => sum_pt (q i) (u i) ε (hq i) h4 (hu i))
  have hR : HasSum (fun i => Real.exp (-Real.pi * q i) + -Real.pi * (u i * Real.exp (-Real.pi * q i)) +
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q i))) (Z + -Real.pi * M + 32 * ε ^ 2 * S) :=
    (hsum1.hasSum.add (hsumM.hasSum.mul_left _)).add (hsumh.hasSum.mul_left _)
  have hsum' : Summable fun i => Real.exp (-Real.pi * (q i + u i)) :=
    Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le)
      (fun i => up_pt (q i) (u i) ε (hq i) h0 h4 (hu i)) hR.summable
  have hup : Z' ≤ Z + -Real.pi * M + 32 * ε ^ 2 * S := by
    rw [← hR.tsum_eq]
    exact Summable.tsum_le_tsum (fun i => up_pt (q i) (u i) ε (hq i) h0 h4 (hu i)) hsum' hR.summable
  set m := -Real.pi * M / Z with hm
  have hmZ : m * Z = -Real.pi * M := by rw [hm]; exact div_mul_cancel₀ _ hZpos.ne'
  have hlow : Real.exp m * Z ≤ Z' := by
    have hL : HasSum (fun i => Real.exp m * ((1 - m) * Real.exp (-Real.pi * q i) +
        -Real.pi * (u i * Real.exp (-Real.pi * q i)))) (Real.exp m * ((1 - m) * Z + -Real.pi * M)) :=
      ((hsum1.hasSum.mul_left (1 - m)).add (hsumM.hasSum.mul_left (-Real.pi))).mul_left (Real.exp m)
    have e : (1 - m) * Z + -Real.pi * M = Z := by linear_combination (-1 : ℝ) * hmZ
    rw [← e, ← hL.tsum_eq]
    exact Summable.tsum_le_tsum (fun i => low_pt (q i) (u i) m) hL.summable hsum'
  have hZ'pos : 0 < Z' := lt_of_lt_of_le (by positivity) hlow
  have hLo : m ≤ Real.log Z' - Real.log Z := by
    have := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul (Real.exp_pos m).ne' hZpos.ne', Real.log_exp] at this
    linarith
  have hUp : Real.log Z' - Real.log Z ≤ m + 32 * 2 ^ N * ε ^ 2 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hZ'pos hZpos)
    rw [Real.log_div hZ'pos.ne' hZpos.ne'] at h1
    have h2 : Z' / Z - 1 ≤ m + 32 * 2 ^ N * ε ^ 2 := by
      rw [div_sub_one hZpos.ne', div_le_iff₀ hZpos]
      have h3 := mul_le_mul_of_nonneg_left hSle (by positivity : (0 : ℝ) ≤ 32 * ε ^ 2)
      nlinarith
    linarith
  have hexpr : Real.pi * (M / Z) = -m := by rw [hm]; ring
  rw [hexpr, abs_le]
  have hK : (0 : ℝ) ≤ 32 * 2 ^ N * ε ^ 2 := by positivity
  constructor <;> linarith
end

section

open UpperTheory.V.Lit.Geo


theorem UpperTheory.geometric_side_comparison :
    MeanLow := by
  unfold MeanLow
  refine ⟨Real.exp (-Real.pi) / 16, by positivity, ?_⟩
  intro A V _ _ _ φ hinj hS hT h2
  classical
  haveI : IsAddTorsionFree V := by
    constructor
    intro n hn x y _ hxy
    have h : ((n : ℝ)) • x = ((n : ℝ)) • y := by simpa [Nat.cast_smul_eq_nsmul] using hxy
    exact smul_right_injective V (Nat.cast_ne_zero.mpr hn) h
  have hfin : {x : A | ‖φ x‖ < 1}.Finite := by
    have h := hS.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos (-Real.pi)))
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    intro x (hx : ‖φ x‖ < 1)
    simp only [Set.mem_setOf_eq, not_lt]
    apply Real.exp_le_exp.mpr
    have ha2 : ‖φ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (φ x)]
    nlinarith [Real.pi_pos]
  have hfin2 : {x : A | ‖φ x‖ < 1 / 2}.Finite :=
    hfin.subset (fun x (hx : ‖φ x‖ < 1 / 2) => show ‖φ x‖ < 1 by linarith)
  set H := hfin.toFinset with hH
  set F := hfin2.toFinset with hF
  have hFH : F ⊆ H := by
    intro x hx
    simp only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    linarith
  have hcd : 2 * F.card - 1 ≤ H.card := by
    have h0 : (0 : A) ∈ F := by
      simp only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_zero, norm_zero]
      norm_num
    have hne : (F.image φ).Nonempty := ⟨φ 0, Finset.mem_image_of_mem _ h0⟩
    have hcdv := cauchy_davenport_of_isAddTorsionFree hne hne
    have hcard : (F.image φ).card = F.card := Finset.card_image_of_injective _ hinj
    open scoped Pointwise in
    have hsub : F.image φ + F.image φ ⊆ H.image φ := by
      intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      refine Finset.mem_image.mpr ⟨x + y, ?_, map_add φ x y⟩
      simp only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add (f := _)]
      calc ‖φ x + φ y‖ ≤ ‖φ x‖ + ‖φ y‖ := norm_add_le _ _
        _ < 1 := by linarith
    have hle := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hle
    rw [hcard] at hcdv
    omega
  have hsd := Finset.card_sdiff_add_card_eq_card hFH
  have hreal : (F.card : ℝ) ≤ ((H \ F).card : ℝ) + 1 := by
    have : F.card ≤ (H \ F).card + 1 := by omega
    exact_mod_cast this
  have hT2 : ((H \ F).card : ℝ) * (Real.exp (-Real.pi) / 4) ≤
      ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
    refine le_trans ?_ (hT.sum_le_tsum (H \ F) (fun x _ => by positivity))
    have hpt : ∀ x ∈ H \ F, Real.exp (-Real.pi) / 4 ≤ ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
      intro x hx
      simp only [Finset.mem_sdiff, hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx
      obtain ⟨h1, h3⟩ := hx
      have ha2 : ‖φ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (φ x)]
      have e1 : Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have e2 : (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2 := by nlinarith
      have := Real.exp_pos (-Real.pi)
      nlinarith
    calc ((H \ F).card : ℝ) * (Real.exp (-Real.pi) / 4) = ∑ x ∈ H \ F, Real.exp (-Real.pi) / 4 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hpt
  have hS1 : ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
      4 * ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) + F.card := by
    have hg : Summable (fun x => if x ∈ F then (1 : ℝ) else 0) :=
      summable_of_ne_finset_zero (s := F) (fun x hx => if_neg hx)
    have hsum : ∑' x, (if x ∈ F then (1 : ℝ) else 0) = F.card := by
      rw [tsum_eq_sum (s := F) (fun x hx => if_neg hx)]
      simp
    have hle : ∀ x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
        4 * (‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) + (if x ∈ F then (1 : ℝ) else 0) := by
      intro x
      have hp := Real.exp_pos (-Real.pi * ‖φ x‖ ^ 2)
      by_cases hx : x ∈ F
      · rw [if_pos hx]
        have : Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg ‖φ x‖])
        nlinarith [sq_nonneg ‖φ x‖]
      · rw [if_neg hx]
        simp only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx
        have : (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2 := by nlinarith
        nlinarith
    calc _ ≤ ∑' x, (4 * (‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) + (if x ∈ F then (1 : ℝ) else 0)) :=
          Summable.tsum_le_tsum hle hS ((hT.mul_left 4).add hg)
      _ = _ := by rw [Summable.tsum_add (hT.mul_left 4) hg, tsum_mul_left, hsum]
  have hE := Real.exp_pos (-Real.pi)
  have hE1 : Real.exp (-Real.pi) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
  have hT0 : 0 ≤ ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
    tsum_nonneg (fun x => by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hS1 hE.le, mul_le_mul_of_nonneg_left hreal hE.le,
    mul_le_mul_of_nonneg_left h2 hE.le, mul_le_mul_of_nonneg_right hE1 hT0]
end
