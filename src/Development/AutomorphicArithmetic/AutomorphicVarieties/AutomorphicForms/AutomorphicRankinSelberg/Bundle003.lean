module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.NumberTheory.ZetaValues
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open UpperHalfPlane hiding I
open UpperTheory.V.Af UpperTheory.V.Sd

private lemma pet_re (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    (petersson (k : ℤ) f f z).re = Complex.normSq (f z) * z.im ^ k := by
  simp only [petersson]
  rw [zpow_natCast, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.sq_norm]

theorem UpperTheory.V.Af.Rs.core :
    UpperTheory.V.Af.Rs.TBdd → UpperTheory.V.Af.Rs.TTop → UpperTheory.V.Af.Rs.ClsEx → UpperTheory.V.Af.Rs.ClsProp → UpperTheory.V.Af.Rs.TEq → UpperTheory.V.Af.Rs.LBd → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.PetChar → UpperTheory.V.Af.Rs.Cmp → UpperTheory.V.Af.Rs.Core := by
  intro hTB hTT hCE hCP hTE hLB hNP hPC hCmp k L _ hk χ ψ g h hap hχ
  by_contra hne
  have hne' : χ * ψ⁻¹ ≠ 1 := fun e => hne (mul_inv_eq_one.mp e)
  obtain ⟨G, hG⟩ := hCE L (χ * ψ⁻¹) (petersson (k : ℤ) h.f g.f) (hPC k L χ ψ g.f h.f g.char h.char)
  have hNF := hNP k L g.f h.f
  obtain ⟨hP1, hP2, -⟩ := hCP L _ _ G hG
  obtain ⟨C, hC⟩ := hTB L G (hP1 hNF) (hP2 hne')
  have hchar0 := hPC k L χ χ g.f g.f g.char g.char
  simp only [mul_inv_cancel] at hchar0
  obtain ⟨G0, hG0⟩ := hCE L 1 (petersson (k : ℤ) g.f g.f) hchar0
  have hNF0 := hNP k L g.f g.f
  obtain ⟨hQ1, -, hQ3⟩ := hCP L _ _ G0 hG0
  have hfz : ∃ z, g.f z ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h0 : (⇑g.f : ℍ → ℂ) = 0 := funext hall
    have := g.one
    rw [h0] at this
    simp [UpperTheory.V.Af.coef, UpperHalfPlane.qExpansion_zero] at this
  obtain ⟨z0, hz0⟩ := hfz
  have hpos : ∃ z, 0 < (petersson (k : ℤ) g.f g.f z).re := by
    refine ⟨z0, ?_⟩
    rw [pet_re]
    exact mul_pos (Complex.normSq_pos.mpr hz0) (pow_pos z0.im_pos k)
  have hnn : ∀ z, 0 ≤ (petersson (k : ℤ) g.f g.f z).re := by
    intro z
    rw [pet_re]
    exact mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg z.im_pos.le k)
  obtain ⟨hR1, hR2⟩ := hQ3 rfl hnn hpos
  obtain ⟨s, hs, hM⟩ := hTT L G0 (hQ1 hNF0) hR1 hR2 (56 * C + 1)
  have hs1 : (1 : ℝ) ≤ s := hs.1.le
  have e1 := hTE L _ _ G hG hNF (hP1 hNF) s hs
  have e0 := hTE L _ _ G0 hG0 hNF0 (hQ1 hNF0) s hs
  obtain ⟨-, hL1, -⟩ := hLB L (χ * ψ⁻¹) s hs1
  obtain ⟨-, -, hL0⟩ := hLB L 1 s hs1
  have hCs := hC s hs
  have hcmp := hCmp k L hk χ ψ g h hap hχ s hs
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e1, norm_mul, norm_mul, h2] at hCs
  have hre := Complex.re_le_norm (Rs.TT L G0 s)
  have hnorm : ‖Rs.TT L G0 s‖ = ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ *
      (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖) := by
    rw [e0, norm_mul, norm_mul, h2]
  have hA := norm_nonneg (Rs.stripI (petersson (k : ℤ) h.f g.f) s)
  have hB := norm_nonneg (Rs.stripI (petersson (k : ℤ) g.f g.f) s)
  have hX : ‖Rs.stripI (petersson (k : ℤ) h.f g.f) s‖ ≤ 2 * C := by nlinarith
  have hY : ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ * (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖)
      ≤ 2 * (2 * (7 * (2 * C))) := by
    apply mul_le_mul hL0 _ (by positivity) (by norm_num)
    linarith
  linarith
end

section

open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped MatrixGroups

private lemma UpperTheory.V.Af.Rs.stripInt_maj (A B s : ℝ) (hs : 1 < s) :
    IntegrableOn (fun y : ℝ => (if y ≤ 1 then A * y ^ s else B) / y ^ 2) (Ioi 0) := by
  have hsplit : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun y : ℝ => y ^ (s - 2)) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1.mono_set
        (le_of_eq (uIoc_of_le zero_le_one).symm)
    have h1' : IntegrableOn (fun y : ℝ => A * y ^ (s - 2)) (Ioc 0 1) := h1.const_mul A
    refine h1'.congr_fun ?_ measurableSet_Ioc
    intro y hy
    have hy0 : 0 < y := hy.1
    simp only [if_pos hy.2]
    rw [Real.rpow_sub hy0, Real.rpow_two, mul_div_assoc]
  · have h2 : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    have h2' : IntegrableOn (fun y : ℝ => B * y ^ (-2 : ℝ)) (Ioi 1) := h2.const_mul B
    refine h2'.congr_fun ?_ measurableSet_Ioi
    intro y hy
    have hy1 : (1:ℝ) < y := hy
    have hy0 : 0 < y := by linarith
    simp only [if_neg (not_le.mpr hy1)]
    rw [Real.rpow_neg hy0.le, Real.rpow_two, div_eq_mul_inv]

theorem UpperTheory.V.Af.Rs.stripInt :
    UpperTheory.V.Af.Rs.StripIm → UpperTheory.V.Af.Rs.StripInt := by
  intro hIm F hF s hs
  obtain ⟨hcont, C, hC⟩ := hF
  have hbound : ∀ z : ℍ, ‖F z‖ ≤ 8 * C := by
    intro z
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    have h4 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    have hpos := (g • z).im_pos
    have hw : 1 / 2 ≤ (g • z).im := by nlinarith
    have hC' := hC g⁻¹ (g • z) hw
    rw [inv_smul_smul] at hC'
    have h3 : (1 / 2 : ℝ) ^ 3 ≤ (g • z).im ^ 3 := pow_le_pow_left₀ (by norm_num) hw 3
    nlinarith [norm_nonneg (F z)]
  have hhigh : ∀ z : ℍ, 1 < z.im → ‖F z‖ * z.im ^ s ≤ C := by
    intro z hz
    have hC' := hC 1 z (by linarith)
    rw [one_smul] at hC'
    have hle : z.im ^ s ≤ z.im ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hz.le (by push_cast; linarith [hs.2])
    calc ‖F z‖ * z.im ^ s ≤ ‖F z‖ * z.im ^ 3 :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ ≤ C := hC'
  have hmeas : Measurable (fun y : ℝ => if y ≤ 1 then 8 * C * y ^ s else C) :=
    Measurable.ite measurableSet_Iic ((measurable_id.pow_const s).const_mul _) measurable_const
  have hφ := hIm _ hmeas (UpperTheory.V.Af.Rs.stripInt_maj (8 * C) C s hs.1)
  refine Integrable.mono' hφ ?_ ?_
  · have hc : Continuous fun z : ℍ => F z * ((z.im ^ s : ℝ) : ℂ) :=
      hcont.mul (Complex.continuous_ofReal.comp
        (UpperHalfPlane.continuous_im.rpow_const fun _ => Or.inr (by linarith [hs.1])))
    exact hc.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    have hy := z.im_pos
    rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hy.le s)]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right (hbound z) (Real.rpow_nonneg hy.le s)
    · exact hhigh z (not_le.mp h)
end

section

noncomputable section

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

theorem kerLow : KerLow := by
  intro s hs x z hz
  obtain ⟨hs1, hs2⟩ := hs
  unfold ker
  have hy : 0 < z.im := z.im_pos
  have hy2 : 3 ≤ 4 * z.im ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  set r : ℝ := ‖(z : ℂ)‖ with hr
  set n : ℝ := ‖x‖ with hn
  have hr0 : 0 ≤ r := norm_nonneg _
  have hn0 : 0 ≤ n := norm_nonneg _
  have hyr : z.im ≤ r := by
    have := Complex.abs_im_le_norm (z : ℂ)
    simp only [UpperHalfPlane.coe_im] at this
    exact le_trans (le_abs_self _) this
  by_cases hx0 : x = 0
  · subst hx0
    have hn' : n = 0 := by simp [hn]
    have hs0 : -(2 * s) ≠ 0 := by linarith
    rw [hn', Real.zero_rpow hs0, mul_zero]
    exact Real.rpow_nonneg (div_nonneg hy.le (Complex.normSq_nonneg _)) _
  have hxi : ∀ i, |((x i : ℤ) : ℝ)| ≤ n := by
    intro i
    have := norm_le_pi_norm x i
    rwa [Int.norm_eq_abs] at this
  set w : ℂ := (x 0 : ℂ) * (z : ℂ) + (x 1 : ℂ) with hw
  have hwle : ‖w‖ ≤ n * (r + 1) := by
    calc ‖w‖ ≤ ‖(x 0 : ℂ)‖ * r + ‖(x 1 : ℂ)‖ := by
          rw [hw]
          exact (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ n * r + n := by
          rw [Complex.norm_intCast, Complex.norm_intCast]
          have := hxi 0
          have := hxi 1
          nlinarith
      _ = n * (r + 1) := by ring
  have hwne : w ≠ 0 := by
    intro h0
    have him : (w).im = 0 := by rw [h0]; simp
    have hre : (w).re = 0 := by rw [h0]; simp
    simp [hw] at him hre
    rcases him with h | h
    · have h1 : x 1 = 0 := by simpa [h] using hre
      exact hx0 (by ext i; fin_cases i <;> simp [h, h1])
    · exact absurd h hy.ne'
  have hwpos : 0 < Complex.normSq w := Complex.normSq_pos.mpr hwne
  have hnsq : Complex.normSq w ≤ n ^ 2 * (r + 1) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have := norm_nonneg w
    nlinarith
  set q : ℝ := z.im / (r + 1) ^ 2 with hq
  have hr1 : 0 < (r + 1) ^ 2 := by positivity
  have hq0 : 0 < q := div_pos hy hr1
  have hq1 : q ≤ 1 := by
    rw [div_le_one hr1]
    nlinarith
  have hbase : q / n ^ 2 ≤ z.im / Complex.normSq w := by
    rw [hq, div_div]
    apply div_le_div_of_nonneg_left hy.le hwpos
    nlinarith
  have hqn0 : 0 ≤ q / n ^ 2 := by positivity
  have hstep : (q / n ^ 2) ^ s ≤ (z.im / Complex.normSq w) ^ s :=
    Real.rpow_le_rpow hqn0 hbase (by linarith)
  have hsplit : (q / n ^ 2) ^ s = q ^ s * n ^ (-(2 * s)) := by
    rw [Real.div_rpow hq0.le (by positivity), div_eq_mul_inv, Real.rpow_neg hn0,
      Real.rpow_mul hn0]
    norm_num
  have hq2 : q ^ (2 : ℝ) ≤ q ^ s := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hs2
  have hq2' : 1 / 2 / (r + 1) ^ 4 ≤ q ^ (2 : ℝ) := by
    rw [Real.rpow_two, hq, div_pow, ← pow_mul]
    norm_num
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hnpos : 0 ≤ n ^ (-(2 * s)) := Real.rpow_nonneg hn0 _
  calc 1 / 2 / (r + 1) ^ 4 * n ^ (-(2 * s)) ≤ q ^ s * n ^ (-(2 * s)) :=
        mul_le_mul_of_nonneg_right (hq2'.trans hq2) hnpos
    _ = (q / n ^ 2) ^ s := hsplit.symm
    _ ≤ _ := hstep

end UpperTheory.V.Af.Rs
end
end

section

open MeasureTheory Set UpperHalfPlane

theorem UpperTheory.V.Af.Rs.zInt :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZInt := by
  intro hF hB hW L _ G hG s hs v v'
  obtain ⟨hGc, C0, hC0⟩ := hG
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨h1, h2, -, -, -, h6⟩ := hB s hs'
  have hW2 : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hW.1 (2 * s) (by linarith [hs.1])
  set W := ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * s)) with hWdef
  set g : (Fin 2 → ℤ) → ℍ → ℝ := fun x z =>
    if UpperTheory.V.Af.Rs.cls L x = v' then UpperTheory.V.Af.Rs.ker s x z else 0 with hg
  have hg0 : ∀ x z, 0 ≤ g x z := fun x z => by
    simp only [hg]
    split_ifs
    exacts [h2 x z, le_rfl]
  have hgle : ∀ x z, g x z ≤ UpperTheory.V.Af.Rs.ker s x z := fun x z => by
    simp only [hg]
    split_ifs
    exacts [le_rfl, h2 x z]
  have hgm : ∀ x, Measurable (g x) := by
    intro x
    by_cases h : UpperTheory.V.Af.Rs.cls L x = v'
    · have e : g x = UpperTheory.V.Af.Rs.ker s x := by
        funext z
        simp [hg, h]
      rw [e]
      exact (h1 x).measurable
    · have e : g x = fun _ => 0 := by
        funext z
        simp [hg, h]
      rw [e]
      exact measurable_const
  have hgs : ∀ z ∈ ModularGroup.fd, Summable fun x => g x z := fun z hz =>
    Summable.of_nonneg_of_le (fun x => hg0 x z) (fun x => (hgle x z).trans (h6 x z hz))
      (hW2.mul_left _)
  have hEq : EqOn (fun z => G v z * (((∑' x, ENNReal.ofReal (g x z)).toReal : ℝ) : ℂ))
      (fun z => G v z * ((UpperTheory.V.Af.Rs.Zc L v' s z : ℝ) : ℂ)) ModularGroup.fd := by
    intro z hz
    have e : (∑' x, ENNReal.ofReal (g x z)).toReal = UpperTheory.V.Af.Rs.Zc L v' s z := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => hg0 x z) (hgs z hz),
        ENNReal.toReal_ofReal (tsum_nonneg fun x => hg0 x z)]
      rfl
    simp only [e]
  refine IntegrableOn.congr_fun ?_ hEq hF.1
  refine Measure.integrableOn_of_bounded (M := 8 * C0 * W) hF.2.ne ?_ ?_
  · exact ((hGc v).measurable.mul (Complex.measurable_ofReal.comp
      (Measurable.ennreal_toReal (Measurable.tsum fun x => (hgm x).ennreal_ofReal)))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem hF.1 fun z hz => ?_
    have him0 : 0 < z.im := z.im_pos
    have him : 1 / 2 ≤ z.im := by
      have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      nlinarith
    have e := hEq hz
    simp only at e
    rw [e]
    have hZ0 : 0 ≤ UpperTheory.V.Af.Rs.Zc L v' s z := tsum_nonneg fun x => hg0 x z
    have hZ : UpperTheory.V.Af.Rs.Zc L v' s z ≤ 4 * z.im ^ 2 * W := by
      calc UpperTheory.V.Af.Rs.Zc L v' s z = ∑' x, g x z := rfl
        _ ≤ ∑' x : Fin 2 → ℤ, 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)) :=
          Summable.tsum_le_tsum (fun x => (hgle x z).trans (h6 x z hz)) (hgs z hz) (hW2.mul_left _)
        _ = 4 * z.im ^ 2 * W := tsum_mul_left
    have hGb := hC0 v z him
    have hW0 : 0 ≤ W := tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hZ0]
    have hG2 : ‖G v z‖ * z.im ^ 2 ≤ 2 * C0 := by
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (G v z)) (sq_nonneg z.im)) (sub_nonneg.mpr him)]
    calc ‖G v z‖ * UpperTheory.V.Af.Rs.Zc L v' s z ≤ ‖G v z‖ * (4 * z.im ^ 2 * W) :=
          mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
      _ ≤ 8 * C0 * W := by nlinarith [mul_le_mul_of_nonneg_left hG2 hW0]
end

section

theorem UpperTheory.V.Af.Rs.lBd :
    UpperTheory.V.Af.Rs.LBd := by
  intro L _ ψ s hs
  set f : ℕ → ℂ := fun n => ψ n / ((n : ℝ) ^ (2 * s) : ℝ) with hf
  set g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hg
  have hs2 : (2 * s) ≠ 0 := by linarith
  have hbd : ∀ n, ‖f n‖ ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf, hg, Real.zero_rpow hs2]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpos : (0 : ℝ) < (n : ℝ) ^ (2 * s) := Real.rpow_pos_of_pos (by linarith) _
      have hle : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ (2 * s) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      rw [Real.rpow_two] at hle
      simp only [hf, hg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      calc ‖ψ n‖ / (n : ℝ) ^ (2 * s) ≤ 1 / (n : ℝ) ^ (2 * s) :=
            div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one ψ _) hpos.le
        _ ≤ 1 / (n : ℝ) ^ 2 := one_div_le_one_div_of_le (by positivity) hle
  have hgs : HasSum g (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hsum : Summable f := Summable.of_norm_bounded hgs.summable hbd
  refine ⟨hsum, ?_⟩
  have hg2 : HasSum (fun n => g (n + 2)) (Real.pi ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' (f := g) 2).mpr hgs
    simpa [Finset.sum_range_succ, hg] using this
  have htail : ‖∑' n, f (n + 2)‖ ≤ Real.pi ^ 2 / 6 - 1 :=
    tsum_of_norm_bounded hg2 (fun n => hbd (n + 2))
  have hsplit : UpperTheory.V.Af.Rs.Lps ψ s = 1 + ∑' n, f (n + 2) := by
    rw [UpperTheory.V.Af.Rs.Lps, ← hsum.sum_add_tsum_nat_add 2]
    simp [Finset.sum_range_succ, hf, Real.zero_rpow hs2]
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 3 / 4 := by
    have h1 := Real.pi_lt_d2
    have h0 := Real.pi_pos
    nlinarith
  rw [hsplit]
  constructor
  · have := norm_sub_norm_le (1 : ℂ) (-(∑' n, f (n + 2)))
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  · have := norm_add_le (1 : ℂ) (∑' n, f (n + 2))
    rw [norm_one] at this
    linarith
end

section

open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

namespace UpperTheory.V.Af.Rs

private theorem unf_meas_strip : MeasurableSet strip := by
  unfold strip
  exact (measurableSet_le measurable_const UpperHalfPlane.continuous_re.measurable).inter
    (measurableSet_lt UpperHalfPlane.continuous_re.measurable measurable_const)

private theorem unf_meas_smul (γ : SL(2, ℤ)) : Measurable (fun z : ℍ => γ • z) := by
  refine Continuous.measurable ?_
  rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff]
  have h : (UpperHalfPlane.coe ∘ fun z : ℍ => γ • z) = fun z : ℍ =>
      (((algebraMap ℤ ℝ (γ 0 0) : ℂ) * z + (algebraMap ℤ ℝ (γ 0 1) : ℂ)) /
      ((algebraMap ℤ ℝ (γ 1 0) : ℂ) * z + (algebraMap ℤ ℝ (γ 1 1) : ℂ))) :=
    funext fun z => UpperHalfPlane.coe_specialLinearGroup_apply γ z
  rw [h]
  refine Continuous.div₀ (by fun_prop) (by fun_prop) fun z => ?_
  have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
  simpa [UpperHalfPlane.denom] using this

private theorem unf_countable : Countable SL(2, ℤ) := @Subtype.countable (Matrix (Fin 2) (Fin 2) ℤ) (show Countable (Fin 2 → Fin 2 → ℤ) from inferInstance) _

end UpperTheory.V.Af.Rs

private theorem hasSum_integral_fd_smul_eq_two_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hU : UpperTheory.V.Af.Rs.UnfM) (f : ℍ → E) (hfm : StronglyMeasurable f)
    (hfi : Integrable f volume) :
    HasSum (fun γ : SL(2, ℤ) => ∫ z in ModularGroup.fd, f (γ • z)) ((2 : ℝ) • ∫ z, f z) := by
  have hsum : Integrable f (Measure.sum fun γ : SL(2, ℤ) =>
      Measure.map (fun z => γ • z) (volume.restrict ModularGroup.fd)) := by
    rw [hU, two_smul]
    exact hfi.add_measure hfi
  have h1 := hasSum_integral_measure hsum
  rw [hU, two_smul, integral_add_measure hfi hfi, ← two_smul ℝ] at h1
  convert h1 using 1
  funext γ
  rw [integral_map (UpperTheory.V.Af.Rs.unf_meas_smul γ).aemeasurable hfm.aestronglyMeasurable]

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.unfold :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.UnfM → UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.Unfold := by
  classical
  intro _ hU hR H Φ hH hHi hHΦ hΦ
  haveI := unf_countable
  have hstrip := unf_meas_strip
  set f : ℍ → ℂ := strip.indicator H with hf
  have hfm : StronglyMeasurable f := hH.stronglyMeasurable.indicator hstrip
  have hfi : Integrable f volume := (integrable_indicator_iff hstrip).mpr hHi
  have hA := hasSum_integral_fd_smul_eq_two_integral hU f hfm hfi
  have hB := hasSum_integral_fd_smul_eq_two_integral hU (fun z => ‖f z‖) hfm.norm hfi.norm
  have hval : (2 : ℝ) • ∫ z, f z = 2 * ∫ z in strip, H z := by
    rw [hf, integral_indicator hstrip]
    norm_num
  rw [hval] at hA
  have hfγ : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = if γ • z ∈ strip then Φ (row γ) z else 0 := by
    intro γ z
    rw [hf]
    split_ifs with h
    · rw [indicator_of_mem h, hHΦ]
    · rw [indicator_of_notMem h]
  let g : SL(2, ℤ) → Cop := fun γ => ⟨row γ, hR.1 γ⟩
  have hA' := (Equiv.sigmaFiberEquiv g).hasSum_iff.mpr hA
  refine HasSum.sigma hA' fun x => ?_
  have hint : ∀ c : {γ // g γ = x},
      Integrable (fun z => f (c.1 • z)) (volume.restrict ModularGroup.fd) := by
    intro c
    refine Integrable.mono (hΦ x)
      ((hfm.comp_measurable (unf_meas_smul c.1)).aestronglyMeasurable) (ae_of_all _ fun z => ?_)
    have hrow : row c.1 = x := congrArg Subtype.val c.2
    rw [hfγ]
    split_ifs
    · rw [hrow]
    · simp
  have hsumm : Summable fun c : {γ // g γ = x} => ∫ z in ModularGroup.fd, ‖f (c.1 • z)‖ :=
    hB.summable.comp_injective Subtype.val_injective
  have h := hasSum_integral_of_summable_integral_norm hint hsumm
  have heq : ∀ z, ∑' c : {γ // g γ = x}, f (c.1 • z) = Φ x z := by
    intro z
    obtain ⟨γ0, ⟨h0row, h0s⟩, huniq⟩ := hR.2 z x
    have hg0 : g γ0 = x := Subtype.ext h0row
    rw [tsum_eq_single ⟨γ0, hg0⟩]
    · rw [hfγ, if_pos h0s, h0row]
    · intro c hc
      rw [hfγ, if_neg]
      intro hs
      apply hc
      exact Subtype.ext (huniq c.1 ⟨congrArg Subtype.val c.2, hs⟩)
  simp only [heq] at h
  exact h
end
