module

public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.QuotientTorusMinimumBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DifferentiableZeroModeLiftOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ThetaSectionPointwiseNormSqEq

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField MeasureTheory
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace Col

theorem lint_fd_shift {ι : Type} [Fintype ι] {κ : Type} [Finite κ]
    (b : Module.Basis κ ℝ (EuclideanSpace ℂ ι)) (F : EuclideanSpace ℂ ι → ℝ≥0∞)
    (hF : ∀ γ ∈ Submodule.span ℤ (Set.range b), ∀ x, F (x + γ) = F x) (a : EuclideanSpace ℂ ι) :
    ∫⁻ x in ZSpan.fundamentalDomain b, F (x + a) = ∫⁻ x in ZSpan.fundamentalDomain b, F x := by
  haveI : VAddInvariantMeasure (↥(Submodule.span ℤ (Set.range b))) (EuclideanSpace ℂ ι) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : EuclideanSpace ℂ ι) s⟩
  have hfd := ZSpan.isAddFundamentalDomain b (volume : Measure (EuclideanSpace ℂ ι))
  have ht := hfd.preimage_of_equiv (measurePreserving_sub_right volume a).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun g x => add_sub_assoc (g : EuclideanSpace ℂ ι) x a)
  have hpre : (fun x => x + a) ⁻¹' ((fun y => y - a) ⁻¹' ZSpan.fundamentalDomain b) =
      ZSpan.fundamentalDomain b := by
    ext x; simp
  have h1 := (measurePreserving_add_right (volume : Measure (EuclideanSpace ℂ ι)) a).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding F ((fun y => y - a) ⁻¹' ZSpan.fundamentalDomain b)
  rw [hpre] at h1
  refine Eq.trans h1 (ht.setLIntegral_eq hfd F fun g x => ?_)
  show F ((g : EuclideanSpace ℂ ι) + x) = F x
  rw [add_comm]
  exact hF _ g.2 x

variable {E : Type} [Field E] [NumberField E]

theorem three_le_exp : (3 : ℝ) ≤ Real.exp (3 / 2) := by
  have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  norm_num at h
  linarith

theorem num1 (n : ℕ) (x : ℝ) (hx : 2 * (n : ℝ) + 3 ≤ x) :
    2 * 3 ^ n * Real.exp (-(Real.pi / 4 * x)) ≤ 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx0 : 0 ≤ x := by linarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have h1 : 3 / 2 * (n : ℝ) + 9 / 4 ≤ Real.pi / 4 * x := by
    nlinarith [mul_nonneg (sub_nonneg.2 hpi.le) hx0]
  have h2 : (3 : ℝ) ^ n ≤ Real.exp (3 / 2 * n) := by
    rw [show (3 / 2 * (n : ℝ)) = n * (3 / 2) by ring, Real.exp_nat_mul]
    have h3e := three_le_exp
    gcongr
  have h3 : (2 : ℝ) ≤ Real.exp (9 / 4) := by linarith [Real.add_one_le_exp (9 / 4 : ℝ)]
  have h4 : Real.exp (3 / 2 * n) * Real.exp (9 / 4) ≤ Real.exp (Real.pi / 4 * x) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 h1
  have h5 : Real.exp (Real.pi / 4 * x) * Real.exp (-(Real.pi / 4 * x)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-(Real.pi / 4 * x))
  have h6 : 2 * 3 ^ n ≤ Real.exp (Real.pi / 4 * x) := by
    have := mul_le_mul h2 h3 (by norm_num) (Real.exp_pos _).le
    linarith
  calc 2 * 3 ^ n * Real.exp (-(Real.pi / 4 * x)) ≤ Real.exp (Real.pi / 4 * x) * Real.exp (-(Real.pi / 4 * x)) :=
        mul_le_mul_of_nonneg_right h6 hpos.le
    _ = 1 := h5

section Wsec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

theorem threshold_ge_dimension : 2 * (dK (IR I) : ℝ) + 3 ≤ P.q * b0 (E := E) P.q P.R0 := by
  obtain ⟨ρ, hρ, hr⟩ := hI.rank
  have h6 : (X.gA : ℝ) * Real.log 2 + 2 * dstar (E := E) P.m + 3 +
      (DF + 1) * (X.r * Real.log X.r + 3 * X.r + 3) ≤ P.q * b0 (E := E) P.q P.R0 := P.C6
  have hdK : (dK (IR I) : ℝ) ≤ dstar (E := E) P.m := by
    have h : Module.finrank ℝ (IR I) ≤ 2 * PT.f E * P.m := by
      rw [hr]; exact Nat.mul_le_mul_left _ hρ
    exact_mod_cast h
  have hlog : 0 ≤ (X.r : ℝ) * Real.log X.r := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hg : (0 : ℝ) ≤ X.gA * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)
  have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
  have hDF : 0 ≤ ((DF : ℝ) + 1) * (X.r * Real.log X.r + 3 * X.r + 3) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

theorem finite_uQ (hP : Ext.PackingCount) (R : ℝ) : {c : Qc X I | ‖uQ X I c‖ ≤ R}.Finite := by
  classical
  by_contra hinf
  have hb := cutoff_pos P
  set δ := Real.sqrt (b0 (E := E) P.q P.R0)
  have hδ : 0 < δ := Real.sqrt_pos.2 hb
  set R' := max R δ
  obtain ⟨N, hN⟩ := exists_nat_gt ((3 * R' / δ) ^ (dK (IR I)))
  obtain ⟨T, hT, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have hinj : Set.InjOn (uQ X I) T := by
    intro c _ c' _ h
    by_contra hne
    have := uQ_dist hI hne
    rw [h, dist_self] at this
    exact absurd this (not_le.2 hδ)
  have := pack_K hP (IR I) (T.image (uQ X I))
    (fun u hu => by obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu; exact uQ_mem c) δ R' hδ
    (le_max_right _ _)
    (fun u hu => by
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hu
      exact (hT hc).trans (le_max_left _ _))
    (fun u hu u' hu' hne => by
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hu'
      exact uQ_dist hI (fun h => hne (by rw [h])))
  rw [Finset.card_image_of_injOn hinj, hTc] at this
  linarith

end Wsec

theorem cs_tsum {κ : Type} (w N : κ → ℝ) (hw : ∀ c, 0 ≤ w c) (hN : ∀ c, 0 ≤ N c) (h1 : Summable w)
    (h2 : Summable (fun c => w c * N c ^ 2)) (h3 : Summable (fun c => w c * N c)) :
    (∑' c, w c * N c) ^ 2 ≤ (∑' c, w c) * ∑' c, w c * N c ^ 2 := by
  have key : ∀ t : ℝ, 0 ≤ (∑' c, w c) * t * t + (-2 * ∑' c, w c * N c) * t + ∑' c, w c * N c ^ 2 := by
    intro t
    have e : ∑' c, (w c * N c ^ 2 - 2 * t * (w c * N c) + t ^ 2 * w c) =
        (∑' c, w c * N c ^ 2) - 2 * t * (∑' c, w c * N c) + t ^ 2 * ∑' c, w c := by
      rw [(h2.sub (h3.mul_left _)).tsum_add (h1.mul_left _), h2.tsum_sub (h3.mul_left _), tsum_mul_left,
        tsum_mul_left]
    have hnn : 0 ≤ ∑' c, (w c * N c ^ 2 - 2 * t * (w c * N c) + t ^ 2 * w c) :=
      tsum_nonneg fun c => by nlinarith [mul_nonneg (hw c) (sq_nonneg (N c - t))]
    nlinarith [e, hnn]
  have hd := discrim_le_zero (a := ∑' c, w c) (b := -2 * ∑' c, w c * N c) (c := ∑' c, w c * N c ^ 2)
    (fun t => by nlinarith [key t])
  unfold discrim at hd
  nlinarith [hd]

section Wsec2

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound)
include hI hP hA

theorem sum_w_le (u : Vsp X.dim) :
    Summable (fun c : Qc X I => Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2)) ∧
      ∑' c : Qc X I, Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2) ≤ 2 := by
  have hpi := Real.pi_gt_three
  set g : Qc X I → ℝ := fun c => Real.exp (-(Real.pi / 4 * P.q) * ‖uQ X I c‖ ^ 2) with hg
  have hgs : Summable g := summable_gauss hI hP hA (Real.pi / 4) (by linarith)
  have htail := tailQ hI hP hA (Real.pi / 4) (by positivity) (cond_tail hI (Real.pi / 4) (by linarith))
  have hsplit : ∑' c, g c = g 0 + ∑' c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, g c := by
    rw [← hgs.sum_add_tsum_compl (s := {0}), Finset.sum_singleton]
    rfl
  have hg0 : g 0 = 1 := by simp [hg]
  have hnum := num1 (dK (IR I)) (P.q * b0 (E := E) P.q P.R0) (threshold_ge_dimension hI)
  have hgle : ∑' c, g c ≤ 2 := by
    rw [hsplit, hg0]
    have h2 := htail.2
    rw [show Real.pi / 4 * P.q * b0 (E := E) P.q P.R0 = Real.pi / 4 * (P.q * b0 (E := E) P.q P.R0) by ring] at h2
    linarith
  obtain ⟨c0, -, hmin⟩ := Set.exists_min_image {c : Qc X I | ‖uQ X I c‖ ≤ 2 * ‖u‖}
    (fun c => ‖u - uQ X I c‖) (finite_uQ hI hP _) ⟨0, by simp⟩
  have hglob : ∀ c, ‖u - uQ X I c0‖ ≤ ‖u - uQ X I c‖ := by
    intro c
    by_cases hc : ‖uQ X I c‖ ≤ 2 * ‖u‖
    · exact hmin c hc
    · have h0 := hmin 0 (by simp)
      simp only [map_zero, sub_zero] at h0
      push Not at hc
      have : ‖uQ X I c‖ - ‖u‖ ≤ ‖u - uQ X I c‖ := by
        have := norm_sub_norm_le (uQ X I c) u
        rw [norm_sub_rev] at this; exact this
      linarith
  have hpt : ∀ c, Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2) ≤ g (c - c0) := by
    intro c
    simp only [hg, map_sub]
    apply Real.exp_le_exp.2
    have h1 : ‖uQ X I c - uQ X I c0‖ ≤ 2 * ‖u - uQ X I c‖ := by
      calc ‖uQ X I c - uQ X I c0‖ = ‖(u - uQ X I c0) - (u - uQ X I c)‖ := by congr 1; abel
        _ ≤ ‖u - uQ X I c0‖ + ‖u - uQ X I c‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [hglob c]
    have h2 : ‖uQ X I c - uQ X I c0‖ ^ 2 ≤ 4 * ‖u - uQ X I c‖ ^ 2 := by
      nlinarith [norm_nonneg (uQ X I c - uQ X I c0), norm_nonneg (u - uQ X I c)]
    have hq : (0 : ℝ) ≤ P.q := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Real.pi / 4 * P.q)]
  have hgs' : Summable (fun c => g (c - c0)) := (Equiv.subRight c0).summable_iff.2 hgs
  have hs : Summable (fun c : Qc X I => Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2)) :=
    Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hpt hgs'
  refine ⟨hs, (hs.tsum_le_tsum hpt hgs').trans ?_⟩
  have := (Equiv.subRight c0).tsum_eq g
  simp only [Equiv.subRight_apply] at this
  rw [this]
  exact hgle

end Wsec2

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem finrank_span1 (hI : IsSplit P I) : Module.finrank ℂ (span1 (IR I)) = dK (IR I) := by
  have hK := hK_of hI
  have ho : Orthonormal ℂ (e (IR I)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← Hf_eq_inner, Hf_e hK]
    by_cases h : i = j <;> simp [h, eq_comm]
  rw [span1, finrank_span_eq_card ho.linearIndependent, Fintype.card_fin]

theorem dim_count (hI : IsSplit P I) :
    2 * Fintype.card (Idx X.dim) = dK (IR I) + (dK (IR I) + 2 * Fintype.card (Fin (gB (IR I)))) := by
  have h1 := Submodule.finrank_add_finrank_orthogonal (span1 (IR I))
  rw [finrank_euclideanSpace, finrank_span1 hI] at h1
  rw [Fintype.card_fin, gB, V2, ← h1]
  ring

def cp (hI : IsSplit P I) (j : Fin (Module.finrank ℝ (IR I))) : Vsp X.dim :=
  (dual_lift hI (Pi.single j 1)).choose

theorem cp_mem (hI : IsSplit P I) (j) : cp hI j ∈ X.L := (dual_lift hI (Pi.single j 1)).choose_spec.1

theorem cp_pair (hI : IsSplit P I) (j i) :
    (Hf (cp hI j) ((Ib hI i : IR I) : Vsp X.dim)).im = ((Pi.single j 1 : _ → ℤ) i : ℝ) := (dual_lift hI (Pi.single j 1)).choose_spec.2 i

theorem bB_mem_GB (hI : IsSplit P I) (hP : Ext.PackingCount) (l) : bB hI hP l ∈ GB X I := by
  rw [← lat_bB hI hP]; exact Submodule.subset_span ⟨l, rfl⟩

def cpp (hI : IsSplit P I) (hP : Ext.PackingCount) (l : Fin (2 * Fintype.card (Fin (gB (IR I))))) :
    Vsp X.dim :=
  (mem_GB.1 (bB_mem_GB hI hP l)).choose

theorem cpp_mem (hI : IsSplit P I) (hP : Ext.PackingCount) (l) : cpp hI hP l ∈ Ip X I := (mem_GB.1 (bB_mem_GB hI hP l)).choose_spec.1

theorem cpp_wmap (hI : IsSplit P I) (hP : Ext.PackingCount) (l) :
    wmap (IR I) (cpp hI hP l) = bB hI hP l := (mem_GB.1 (bB_mem_GB hI hP l)).choose_spec.2

def Bf (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Fin (Module.finrank ℝ (IR I)) ⊕ (Fin (Module.finrank ℝ (IR I)) ⊕ Fin (2 * Fintype.card (Fin (gB (IR I))))) →
      Vsp X.dim :=
  Sum.elim (fun i => ((Ib hI i : IR I) : Vsp X.dim)) (Sum.elim (cp hI) (cpp hI hP))

theorem mem_I_span (hI : IsSplit P I) {a : Vsp X.dim} (ha : a ∈ I) :
    ∃ c : Fin (Module.finrank ℝ (IR I)) → ℤ, ∑ i, c i • ((Ib hI i : IR I) : Vsp X.dim) = a := by
  have h : (⟨a, mem_IR ha⟩ : IR I) ∈ Submodule.span ℤ (Set.range (Ib hI)) := by
    rw [Ib_span hI]; exact ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa [Submodule.coe_sum] using this

theorem span_Bf (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Submodule.span ℤ (Set.range (Bf hI hP)) = X.L := by
  have hK := hK_of hI
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rcases k with i | j | l
    · exact hI.le (Ib_mem hI i)
    · exact cp_mem hI j
    · exact (cpp_mem hI hP l).1
  · intro x hx
    have hmem : ∀ v, v ∈ Set.range (Bf hI hP) → v ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun v hv => Submodule.subset_span hv
    have hb : ∀ i, ((Ib hI i : IR I) : Vsp X.dim) ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun i => hmem _ ⟨Sum.inl i, rfl⟩
    have hc : ∀ j, cp hI j ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun j => hmem _ ⟨Sum.inr (Sum.inl j), rfl⟩
    have hcc : ∀ l, cpp hI hP l ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun l => hmem _ ⟨Sum.inr (Sum.inr l), rfl⟩
    choose m hm using fun i => X.integral x _ hx (hI.le (Ib_mem hI i))
    set y := x - ∑ j, m j • cp hI j with hy
    have hyL : y ∈ X.L := X.L.sub_mem hx (X.L.sum_mem fun j _ => X.L.smul_mem _ (cp_mem hI j))
    have hyb : ∀ i, (Hf y ((Ib hI i : IR I) : Vsp X.dim)).im = 0 := fun i => by
      rw [hy, Hf_sub_l, Complex.sub_im, Hf_sum_l, Complex.im_sum, hm i]
      simp only [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_l, Complex.mul_im, Complex.intCast_re,
        Complex.intCast_im, zero_mul, add_zero, cp_pair]
      simp [Pi.single_apply]
    have hyIp : y ∈ Ip X I := by
      refine ⟨hyL, fun a ha => ?_⟩
      obtain ⟨c, rfl⟩ := mem_I_span hI ha
      rw [Hf_sum_r, Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_r]
      simp [Complex.mul_im, hyb i]
    have hwy : wmap (IR I) y ∈ Submodule.span ℤ (Set.range (bB hI hP)) := by
      rw [← lat, lat_bB hI hP]; exact wmap_mem_GB hyIp
    obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hwy
    set z := y - ∑ l, k l • cpp hI hP l with hz
    have hzIp : z ∈ Ip X I := (Ip X I).sub_mem hyIp ((Ip X I).sum_mem fun l _ =>
      (Ip X I).smul_mem _ (cpp_mem hI hP l))
    have hwz : wmap (IR I) z = 0 := by

      rw [hz, map_sub, map_sum, ← hk]
      simp only [map_zsmul, cpp_wmap, sub_self]
    have hp2 : p2 (IR I) z = 0 := by
      rw [← norm_eq_zero, ← norm_wmap hK, hwz, norm_zero]
    obtain ⟨c, hc'⟩ := mem_I_span hI (mem_of_proj_two_eq_zero hI hzIp hp2)
    have hxe : x = z + ∑ l, k l • cpp hI hP l + ∑ j, m j • cp hI j := by rw [hz, hy]; abel
    rw [hxe, ← hc']
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb i)
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hcc l)
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hc j)

theorem top_le_span_Bf (hI : IsSplit P I) (hP : Ext.PackingCount) :
    ⊤ ≤ Submodule.span ℝ (Set.range (Bf hI hP)) := by
  rw [← X.b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h : X.b i ∈ Submodule.span ℤ (Set.range (Bf hI hP)) := by
    rw [span_Bf hI hP]; exact Submodule.subset_span ⟨i, rfl⟩
  exact Submodule.span_le_restrictScalars ℤ ℝ _ h

theorem Bf_li (hI : IsSplit P I) (hP : Ext.PackingCount) : LinearIndependent ℝ (Bf hI hP) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank (top_le_span_Bf hI hP)
  have h := dim_count hI
  rw [Fintype.card_fin] at h
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
    Module.finrank_eq_card_basis X.b, Fintype.card_fin]
  exact h.symm

def BB (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Module.Basis (Fin (Module.finrank ℝ (IR I)) ⊕ (Fin (Module.finrank ℝ (IR I)) ⊕
      Fin (2 * Fintype.card (Fin (gB (IR I)))))) ℝ (Vsp X.dim) :=
  Module.Basis.mk (Bf_li hI hP) (top_le_span_Bf hI hP)

theorem BB_apply (hI : IsSplit P I) (hP : Ext.PackingCount) (k) : BB hI hP k = Bf hI hP k := Module.Basis.mk_apply _ _ _

theorem lat_BB (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Submodule.span ℤ (Set.range (BB hI hP)) = X.L := by
  have h : ⇑(BB hI hP) = Bf hI hP := funext (BB_apply hI hP)
  rw [h]
  exact span_Bf hI hP

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end
