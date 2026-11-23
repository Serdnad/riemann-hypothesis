module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology Classical

namespace GlobalTheory.KSp

theorem setIntegral_addSubgroup_add {X : Type} [AddCommGroup X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddRightInvariant] (H : AddSubgroup X)
    (hH : MeasurableSet (H : Set X)) {h : X} (hh : h ∈ H) (g : X → ℂ) :
    ∫ x in (H : Set X), g (x + h) ∂μ = ∫ x in (H : Set X), g x ∂μ := by
  rw [← integral_indicator hH, ← integral_indicator hH]
  have key : (Set.indicator (H : Set X) fun x => g (x + h)) =
      fun x => Set.indicator (H : Set X) g (x + h) := by
    funext x
    by_cases hx : x ∈ H
    · have hx' : x + h ∈ H := H.add_mem hx hh
      simp [Set.indicator_apply, hx, hx']
    · have hx' : x + h ∉ H := fun h' => hx (by simpa using H.sub_mem h' hh)
      simp [Set.indicator_apply, hx, hx']
  rw [key, integral_add_right_eq_self (Set.indicator (H : Set X) g) h]

theorem setIntegral_pair_char {X : Type} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddRightInvariant] {e : X → X → ℂ} (he : IsPair e)
    (M : AddSubgroup X) (hM : MeasurableSet (M : Set X)) (x : X) :
    ∫ m in (M : Set X), e x m ∂μ =
      if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0 := by
  split_ifs with hx
  · rw [setIntegral_congr_fun hM (g := fun _ => (1 : ℂ)) (fun m hm => by
      simp only; rw [he.symm]; exact hx m hm)]
    rw [setIntegral_const]
    simp
  · push_neg at hx
    obtain ⟨m₀, hm₀, hne⟩ := hx
    have h := setIntegral_addSubgroup_add μ M hM hm₀ (fun m => e x m)
    have hsplit : ∀ m, e x (m + m₀) = e x m * e x m₀ := fun m => by
      rw [he.symm x, he.add, he.symm m, he.symm m₀]
    simp only [hsplit] at h
    rw [integral_mul_const] at h
    have hne' : e x m₀ ≠ 1 := by rwa [he.symm]
    have h2 : (∫ m in (M : Set X), e x m ∂μ) * (e x m₀ - 1) = 0 := by
      rw [mul_sub, h]; ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3) hne'

theorem gauss_integral_eventually_const : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e →
    ∀ f : X → ℂ, IsLocallyConstant f → f 0 = 1 → (∀ x y, f (x + y) = f x * f y * e x y) →
    ∃ (γ : ℂ) (K : Set X), IsCompact K ∧ ∀ L : AddSubgroup X, IsCompact (L : Set X) → IsOpen (L : Set X) →
      K ⊆ L → ∫ x in (L : Set X), f x ∂μ = γ := by
  intro X _ _ _ _ hG μ _ e he f hf hf0 hfe
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  obtain ⟨M, hMc, hMo, hMf⟩ := hG.small {x | f x = 1} ((hf.isOpen_fiber 1).mem_nhds hf0)
  have hMn : (M : Set X) ∈ 𝓝 (0 : X) := hMo.mem_nhds M.zero_mem
  obtain ⟨K₀, hK₀c, hK₀⟩ := he.big _ hMn
  have hecont : ∀ m, Continuous (fun y => e m y) := fun m =>
    (he.lc.comp_continuous (continuous_const.prodMk continuous_id)).continuous
  set M' : Set X := {y | ∀ m ∈ (M : Set X), e m y = 1} with hM'
  have hM'cl : IsClosed M' := by
    have : M' = ⋂ m ∈ (M : Set X), {y | e m y = 1} := by ext; simp [M']
    rw [this]
    exact isClosed_biInter fun m _ => isClosed_eq (hecont m) continuous_const
  refine ⟨∫ x in M', f x ∂μ, (M : Set X) ∪ K₀, hMc.union hK₀c, ?_⟩
  intro L hLc hLo hKL
  have hML : (M : Set X) ⊆ L := Set.subset_union_left.trans hKL
  have hM'L : M' ⊆ L := fun y hy => hKL (Or.inr (hK₀ y hy))
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have hMm : MeasurableSet (M : Set X) := hMo.measurableSet
  have hM'm : MeasurableSet M' := hM'cl.measurableSet
  haveI : IsFiniteMeasure (μ.restrict (L : Set X)) := isFiniteMeasure_restrict.mpr hLc.measure_lt_top.ne
  haveI : IsFiniteMeasure (μ.restrict (M : Set X)) := isFiniteMeasure_restrict.mpr hMc.measure_lt_top.ne
  set A := ∫ x in (L : Set X), f x ∂μ with hA
  have h1 : ∀ m ∈ (M : Set X), ∫ x in (L : Set X), f x * e x m ∂μ = A := by
    intro m hm
    rw [hA, ← setIntegral_addSubgroup_add μ L hLm (hML hm) f]
    congr 1; funext x
    rw [hfe, show f m = 1 from hMf hm]; ring
  obtain ⟨C, hC⟩ := hLc.exists_bound_of_continuousOn hf.continuous.continuousOn
  have hint : Integrable (Function.uncurry fun m x => f x * e x m)
      ((μ.restrict (M : Set X)).prod (μ.restrict (L : Set X))) := by
    refine Integrable.mono' (integrable_const C) ?_ ?_
    · exact (Continuous.mul (hf.continuous.comp continuous_snd)
        (he.lc.continuous.comp (continuous_snd.prodMk continuous_fst))).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (hMm.prod hLm) fun p hp => ?_
      show ‖f p.2 * e p.2 p.1‖ ≤ C
      rw [norm_mul, he.norm, mul_one]
      exact hC p.2 hp.2
  have h3 := integral_integral_swap hint
  rw [setIntegral_congr_fun hMm h1, setIntegral_const] at h3
  simp_rw [integral_const_mul, setIntegral_pair_char μ he M hMm] at h3
  have h4 : ∫ x in (L : Set X), f x * (if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0) ∂μ
      = ((μ.real (M : Set X) : ℝ) : ℂ) * ∫ x in M', f x ∂μ := by
    have : (fun x => f x * (if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0)) =
        Set.indicator M' (fun x => ((μ.real (M : Set X) : ℝ) : ℂ) * f x) := by
      funext x
      by_cases hx : x ∈ M'
      · rw [Set.indicator_of_mem hx, if_pos (show ∀ m ∈ (M : Set X), e m x = 1 from hx)]; ring
      · rw [Set.indicator_of_notMem hx, if_neg (show ¬ ∀ m ∈ (M : Set X), e m x = 1 from hx)]; ring
    rw [this, integral_indicator hM'm, Measure.restrict_restrict hM'm, Set.inter_eq_left.mpr hM'L,
      integral_const_mul]
  rw [h4, Complex.real_smul] at h3
  have hpos : ((μ.real (M : Set X) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨(hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne', hMc.measure_lt_top.ne⟩
  exact mul_left_cancel₀ hpos h3

end GlobalTheory.KSp
end
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem pr_eq_half_trace_mat (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (x y : Matrix α ν E) :
  pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  simp only [pr, form, GlobalTheory.WeilM.hTens, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, stdJ, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Pi.zero_apply, Matrix.zero_apply, map_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, one_apply, Matrix.trace, Matrix.mul_apply, transpose_apply, map_apply, diag_apply]
  congr 2
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.one_apply, mul_ite, ite_mul, mul_comm, mul_left_comm, mul_assoc]

theorem pr_diag_norm : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (u : Matrix α α E) (D' : α → F) (a : Matrix ν ν E) (D : ν → F), Q = u * diagonal (fun i => algebraMap F E (D' i)) * (u.map c)ᵀ → ∀ x : Matrix α ν E, 2⁻¹ * pr c Q x (x * (a * diagonal (fun j => algebraMap F E (D j)) * (a.map c)ᵀ)) = ∑ i, ∑ j, (2⁻¹ * D' i * D j) * Algebra.norm F ((uᵀ * x * a) i j) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q _ u D' a D hQu x
  have hc : ∀ z, c (c z) = z := hE.invol
  have hmm : ∀ {m n : Type} (M : Matrix m n E), (M.map c).map c = M := fun M => by ext i j; simp [hc]
  have hd : ∀ {m : Type} [Fintype m] [DecidableEq m] (d : m → F),
      (diagonal (fun i => algebraMap F E (d i))).map c = diagonal (fun i => algebraMap F E (d i)) := by
    intro m _ _ d; ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
  set dD' := diagonal (fun i => algebraMap F E (D' i))
  set dD := diagonal (fun j => algebraMap F E (D j))
  set Y := uᵀ * x * a with hY
  have hQT : Qᵀ = u.map c * dD' * uᵀ := by
    rw [hQu, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  have hbs : ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ = a * dD * (a.map c)ᵀ * (x.map c)ᵀ := by
    rw [Matrix.map_mul (f := c), Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul, transpose_mul,
      transpose_mul, hd, diagonal_transpose, transpose_map, hmm, ← transpose_map, transpose_transpose]
    simp only [Matrix.mul_assoc]
    rfl
  have hYs : (Y.map c)ᵀ = (a.map c)ᵀ * (x.map c)ᵀ * u.map c := by
    rw [hY, Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul, transpose_mul, transpose_map,
      transpose_transpose]
    simp only [Matrix.mul_assoc]
  have htr : Matrix.trace (Qᵀ * (x * ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ)) = Matrix.trace (dD' * Y * dD * (Y.map c)ᵀ) := by
    rw [hQT, hbs, hYs, hY]
    rw [show u.map c * dD' * uᵀ * (x * (a * dD * (a.map c)ᵀ * (x.map c)ᵀ)) =
      u.map c * (dD' * uᵀ * x * a * dD * (a.map c)ᵀ * (x.map c)ᵀ) by simp only [Matrix.mul_assoc], trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hsum : Matrix.trace (dD' * Y * dD * (Y.map c)ᵀ) =
      algebraMap F E (∑ i, ∑ j, D' i * D j * Algebra.norm F (Y i j)) := by

    simp only [Matrix.trace, diag_apply, Matrix.mul_apply, dD', dD, diagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, transpose_apply, map_apply,
    map_sum, map_mul, hE.algebraMap_norm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨b, -, -⟩ := hE.basis
  haveI : Module.Free F E := Module.Free.of_basis b
  haveI : Module.Finite F E := Module.Finite.of_basis b
  have hfin : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [pr_eq_half_trace_mat, htr, hsum, Algebra.trace_algebraMap, hfin, nsmul_eq_mul, Nat.cast_ofNat,
    inv_mul_cancel_left₀ (two_ne_zero : (2 : F) ≠ 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.KSp
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem inCell_iff_det_ne_zero : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)),
    InCell c g ↔ ((mat c g).toBlocks₂₁).det ≠ 0 := by
  intro F _ _ E _ _ c δ hE ν _ _ g
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    have hdet : ∀ x : UG c (stdJ ν E), (mat c x).det ≠ 0 := fun x =>
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (x : GL (ν ⊕ ν) E))).ne_zero
    have hp0 : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0 (mat c p).toBlocks₂₂ := by
      rw [← (mem_sieg c).1 hp, fromBlocks_toBlocks]
    have hq0 : mat c q = fromBlocks (mat c q).toBlocks₁₁ (mat c q).toBlocks₁₂ 0 (mat c q).toBlocks₂₂ := by
      rw [← (mem_sieg c).1 hq, fromBlocks_toBlocks]
    have hpd := hdet p
    have hqd := hdet q
    rw [hp0, det_fromBlocks_zero₂₁] at hpd
    rw [hq0, det_fromBlocks_zero₂₁] at hqd
    change (mat c p * stdJ ν E * mat c q).toBlocks₂₁.det ≠ 0
    rw [hp0, hq0]
    simp only [stdJ, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
    rw [det_neg, det_mul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      (mul_ne_zero (right_ne_zero_of_mul hpd) (left_ne_zero_of_mul hqd))
  · intro hC
    set A := (mat c g).toBlocks₁₁ with hA
    set B := (mat c g).toBlocks₁₂ with hB
    set C := (mat c g).toBlocks₂₁ with hCdef
    set D := (mat c g).toBlocks₂₂ with hD
    have hg0 : mat c g = fromBlocks A B C D := (fromBlocks_toBlocks _).symm
    have hrel : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c _).mp g.2
    have hkey : C * (D.map c)ᵀ = D * (C.map c)ᵀ := by
      have h := congrArg Matrix.toBlocks₂₂ hrel
      rw [hg0] at h
      simp only [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
      simp at h
      exact (neg_add_eq_zero.1 h).symm
    have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 (isUnit_iff_ne_zero.2 hC)
    have hCs : IsUnit (C.map c)ᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det, det_transpose]
      exact (hCu.map (RingHom.mapMatrix (c : E →+* E))).map detMonoidHom
    have hCC : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.2 hC)
    set v := C⁻¹ * D with hv
    have hvh : (v.map c)ᵀ = v := by
      apply hCu.mul_left_cancel
      apply hCs.mul_right_cancel
      have e1 : ((v.map c)ᵀ) * (C.map c)ᵀ = (D.map c)ᵀ := by
        rw [hv, Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← transpose_mul, ← Matrix.map_mul, hCC,
          Matrix.map_one _ (map_zero c) (map_one c), transpose_one, Matrix.mul_one]
      rw [Matrix.mul_assoc, e1, hkey, hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
    let q := unip c v hvh
    have hq : q ∈ sieg c ν := by
      change (fromBlocks (1 : Matrix ν ν E) v 0 1).toBlocks₂₁ = 0
      rw [toBlocks_fromBlocks₂₁]
    refine ⟨g * q⁻¹ * (weyl c ν)⁻¹, ?_, q, hq, by group⟩
    rw [mem_sieg]
    change (mat c g * fromBlocks 1 (-v) 0 1 * -stdJ ν E).toBlocks₂₁ = 0
    rw [hg0]
    simp only [stdJ, fromBlocks_neg, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
    rw [hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul, neg_add_cancel]

end GlobalTheory.KSp
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp


open MeasureTheory Matrix in
theorem _root_.GlobalTheory.KSp.sieg_blocks : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E)
    (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (p : _root_.GlobalTheory.WeilM.UG c (_root_.GlobalTheory.SplitUnitary.stdJ ν E)), p ∈ _root_.GlobalTheory.KSp.sieg c ν →
    (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₂₂).map c)ᵀ = 1 ∧
    (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₁₂).map c)ᵀ = (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₂ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁).map c)ᵀ ∧
    ∃ (a : GL ν E) (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b), p = _root_.GlobalTheory.SplitUnitary.levi c hE.invol a * _root_.GlobalTheory.KSp.unip c b hb := by
  intro F _ _ E _ _ c δ hE ν _ _ p hp
  rw [_root_.GlobalTheory.KSp.mem_sieg] at hp
  have hc := hE.invol
  have hu := (_root_.GlobalTheory.SplitUnitary.mem_UG_iff c (p : GL (ν ⊕ ν) E)).mp p.2
  have hM : ((p : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = _root_.GlobalTheory.KSp.mat c p := rfl
  set M := _root_.GlobalTheory.KSp.mat c p
  rw [hM, ← fromBlocks_toBlocks M, hp] at hu
  unfold _root_.GlobalTheory.SplitUnitary.stdJ at hu
  simp only [fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj] at hu
  simp at hu
  obtain ⟨h1, h2, h3⟩ := hu
  have h2' := mul_eq_one_comm.mp h2
  have h3' := mul_eq_one_comm.mp h3
  have hcc : ∀ X : Matrix ν ν E, (X.map c).map c = X := fun X => by ext i j; simp [hc]
  have hAB : M.toBlocks₁₁ * (M.toBlocks₁₂.map c)ᵀ = M.toBlocks₁₂ * (M.toBlocks₁₁.map c)ᵀ :=
    sub_eq_zero.mp (by rw [← neg_add_eq_sub]; exact h1)
  refine ⟨h2, hAB, ?_⟩
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set D := M.toBlocks₂₂
  let a : GL ν E := ⟨A, (D.map c)ᵀ, h2, h2'⟩
  have hb : (((D.map c)ᵀ * B).map c)ᵀ = (D.map c)ᵀ * B := by
    rw [Matrix.map_mul, transpose_mul, transpose_map, hcc, transpose_transpose]
    have hB : B * (A.map c)ᵀ = A * (B.map c)ᵀ := hAB.symm
    calc (B.map c)ᵀ * D = (D.map c)ᵀ * A * (B.map c)ᵀ * D := by rw [h2', Matrix.one_mul]
      _ = (D.map c)ᵀ * (B * (A.map c)ᵀ) * D := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = (D.map c)ᵀ * B * ((A.map c)ᵀ * D) := by simp only [Matrix.mul_assoc]
      _ = (D.map c)ᵀ * B := by rw [h3', Matrix.mul_one]
  refine ⟨a, (D.map c)ᵀ * B, hb, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, _root_.GlobalTheory.SplitUnitary.levi_val, hM]
  unfold _root_.GlobalTheory.KSp.unip
  simp only [fromBlocks_multiply]
  have ha : ((a⁻¹ : GL ν E) : Matrix ν ν E) = (D.map c)ᵀ := rfl
  rw [ha, transpose_map, hcc, transpose_transpose, ← Matrix.mul_assoc, h2]
  conv_lhs => rw [← fromBlocks_toBlocks M, hp]
  simp [A, B, D]
  rfl

end GlobalTheory.KSp
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology

namespace GlobalTheory.KSp.FourMem

theorem eventually_invariant {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {f : X → ℂ} (hf : f ∈ SB X) : ∀ᶠ t in 𝓝 (0 : X), ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : X × X => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h2 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + -t) = f x := by
    have h3 : Filter.Tendsto (fun t : X => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact h3.eventually h1
  filter_upwards [h1, h2] with t ht ht' x
  by_cases hx : x ∈ tsupport f
  · exact ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · rw [← ht' _ hx', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem four_mem_SB : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ φ ∈ SB X, four μ e φ ∈ SB X := by
  intro X _ _ _ _ h μ _ e he φ hφ
  haveI := h.grp
  haveI := h.t2
  haveI := h.lc
  haveI := h.sc
  obtain ⟨K, hK, hKm⟩ := he.big _ (eventually_invariant hφ)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_, HasCompactSupport.intro hK fun y hy => ?_⟩
  · have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport φ, e z x = e y x := by
      refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun x _ => ?_
      have h2 : IsLocallyConstant fun q : X × X => (e q.1 q.2, e y q.2) :=
        he.lc.prodMk (he.lc.comp_continuous (continuous_const.prodMk continuous_snd))
      filter_upwards [h2.eventually_eq (y, x)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1] with z hz
    unfold four
    congr 1
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hz x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · obtain ⟨t, ht, hne⟩ : ∃ t, (∀ x, φ (x + t) = φ x) ∧ e t y ≠ 1 := by
      by_contra hne
      exact hy (hKm y fun t ht => by
        by_contra h4
        exact hne ⟨t, ht, h4⟩)
    have h1 := integral_add_right_eq_self (μ := μ) (fun x => e y x * φ x) t
    have h2 : ∀ x, e y (x + t) * φ (x + t) = e t y * (e y x * φ x) := by
      intro x
      rw [ht, he.symm y (x + t), he.add, he.symm x y]; ring
    simp only [h2, integral_const_mul] at h1
    refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
    unfold four
    rw [sub_mul, h1, one_mul, sub_self]

end GlobalTheory.KSp.FourMem
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem hasGauss_pi : ∀ (Y : Type) [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (_ : Good Y) (μ : Measure Y) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (f : ι → Y → ℂ) (γ : ι → ℂ), (∀ i, HasGauss μ (f i) (γ i)) → HasGauss (Measure.pi fun _ : ι => μ) (fun x => ∏ i, f i (x i)) (∏ i, γ i) := by
  intro Y _ _ _ _ hY μ _ ι _ f γ hf K hK
  haveI := hY.sc
  haveI := hY.lc
  haveI := hY.t2
  haveI : SigmaFinite μ := sigmaFinite_of_locallyFinite
  have hL : ∀ i, ∃ L : AddSubgroup Y, IsCompact (L : Set Y) ∧ IsOpen (L : Set Y) ∧
      (Function.eval i '' K) ⊆ L ∧ ∫ x in (L : Set Y), f i x ∂μ = γ i :=
    fun i => hf i _ (hK.image (continuous_apply i))
  choose L hLc hLo hLK hLi using hL
  refine ⟨AddSubgroup.pi Set.univ L, ?_, ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_pi]; exact isCompact_univ_pi hLc
  · rw [AddSubgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => hLo i
  · intro x hx
    rw [SetLike.mem_coe, AddSubgroup.mem_pi]
    intro i _
    exact hLK i ⟨x, hx, rfl⟩
  · rw [AddSubgroup.coe_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
    exact Finset.prod_congr rfl fun i _ => hLi i

end GlobalTheory.KSp
end

section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.appLE_opensInclusion_appLE_eq_secMap_isoSpec : ∀ (X T : Scheme.{0}) (p : T ⟶ X) (U : X.affineOpens) (O : T.Opens) (hO : O ≤ p ⁻¹ᵁ U.1) (V : (p ⁻¹ᵁ U.1).toScheme.Opens) (e : V ≤ (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) (r : Γ(X, U.1)), ((p ⁻¹ᵁ U.1).ι.appLE O V e).hom ((p.appLE U.1 O hO).hom r) = (GlobalTheory.CechDR.secMap ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) V).hom r := by
  first | exact @GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap | exact GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap | (intros; apply GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap <;> assumption)
end

section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.inverseUnipotentVolume_conj_diagonalUnitsGL_mul : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (d e : n ⊕ Fin c → kˣ), invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom) = invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) * invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom) := by
  first | exact @GlobalTheory.FunObj.invVol_conj_diagGL_mul | exact GlobalTheory.FunObj.invVol_conj_diagGL_mul | (intros; apply GlobalTheory.FunObj.invVol_conj_diagGL_mul <;> assumption)
end
