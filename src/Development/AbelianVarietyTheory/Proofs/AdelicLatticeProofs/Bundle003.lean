module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

section

open Matrix

namespace GlobalTheory


open Matrix in
theorem _root_.GlobalTheory.differentiable_exp_mul_of_annihilated :
    ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℝ f → (∀ w z : Fin g → ℂ, (fderiv ℝ f w z + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star z)).im : ℂ) * f w) + Complex.I * (fderiv ℝ f w (Complex.I • z) + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star (Complex.I • z))).im : ℂ) * f w) = 0) → Differentiable ℂ fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w := by
  intro g Hm _ f hfd hann
  let B0 : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℂ :=
    LinearMap.mk₂ ℝ (fun u v => u ⬝ᵥ Hm.mulVec (star v))
      (fun u₁ u₂ v => by simp [add_dotProduct])
      (fun r u v => by simp [smul_dotProduct])
      (fun u v₁ v₂ => by simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (fun r u v => by simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  let B : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B0)
  have hB : ∀ u v, B u v = u ⬝ᵥ Hm.mulVec (star v) := fun u v => rfl
  have hQ : ∀ w : Fin g → ℂ, HasFDerivAt (fun w : Fin g → ℂ => w ⬝ᵥ Hm.mulVec (star w))
      (B.precompR _ w (ContinuousLinearMap.id ℝ _) + B.precompL _ (ContinuousLinearMap.id ℝ _) w) w :=
    fun w => B.hasFDerivAt_of_bilinear (hasFDerivAt_id w) (hasFDerivAt_id w)
  intro w
  have hF : HasFDerivAt (fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w) _ w :=
    (((hQ w).const_mul ((Real.pi : ℂ) / 2)).cexp).mul (hfd w).hasFDerivAt
  refine (differentiableAt_iff_restrictScalars ℝ hF.differentiableAt).2 ?_
  rw [hF.fderiv]
  set e := Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) with he
  set T := e • fderiv ℝ f w + f w • (e • (((Real.pi : ℂ) / 2) •
    (B.precompR _ w (ContinuousLinearMap.id ℝ _) + B.precompL _ (ContinuousLinearMap.id ℝ _) w)))
    with hTdef
  have hT : ∀ z, T z = e * fderiv ℝ f w z + f w * (e * ((Real.pi : ℂ) / 2 *
      (w ⬝ᵥ Hm.mulVec (star z) + z ⬝ᵥ Hm.mulVec (star w)))) := by
    intro z
    clear hann hQ hF hTdef
    simp only [T, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, hB, smul_eq_mul]
  have key : ∀ z, T (Complex.I • z) = Complex.I • T z := by
    intro z
    have h1 := hann w z
    have hs1 : w ⬝ᵥ Hm.mulVec (star (Complex.I • z)) = -Complex.I * (w ⬝ᵥ Hm.mulVec (star z)) := by
      simp [Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul]
    have hs2 : (Complex.I • z) ⬝ᵥ Hm.mulVec (star w) = Complex.I * (z ⬝ᵥ Hm.mulVec (star w)) := by
      simp [smul_dotProduct]
    rw [hs1] at h1
    rw [hT, hT, hs1, hs2, smul_eq_mul]
    set b := w ⬝ᵥ Hm.mulVec (star z)
    have him : (-Complex.I * b).im = -b.re := by simp
    rw [him] at h1
    have hb : b = b.re + b.im * Complex.I := (Complex.re_add_im b).symm
    push_cast at h1
    linear_combination (-Complex.I * e) * h1 + (-Complex.I * e * Real.pi * f w) * hb +
      (e * fderiv ℝ f w (Complex.I • z) - Real.pi * Complex.I * e * b.re * f w) * Complex.I_sq
  let L : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun c z => by
        have hc : c • z = c.re • z + c.im • (Complex.I • z) := by
          ext i
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im c]
          ring
        rw [hc, T.map_add, T.map_smul, T.map_smul, key, RingHom.id_apply]
        simp only [Complex.real_smul, smul_eq_mul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring }
  exact ⟨LinearMap.toContinuousLinearMap L, ContinuousLinearMap.ext fun z => rfl⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem exists_near_one_mod_ideal (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (hm : m ≠ ⊥) : ∃ C : ℝ, ∀ z : mixedSpace K, ∃ β : 𝓞 K, β - 1 ∈ m ∧
      ‖z - mixedEmbedding K β‖ ≤ C := by
  set N : ℕ := Ideal.absNorm m with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; exact fun h => hm (Ideal.absNorm_eq_zero_iff.mp h)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  refine ⟨(N : ℝ) * ∑ i, ‖latticeBasis K i‖, fun z => ?_⟩
  set w : mixedSpace K := (N : ℝ)⁻¹ • (z - 1) with hw
  have hmem := (ZSpan.floor (latticeBasis K) w).2
  obtain ⟨a, ha⟩ := (mem_span_latticeBasis K).mp hmem
  refine ⟨1 + (N : 𝓞 K) * a, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact m.mul_mem_right _ (Ideal.absNorm_mem m)
  · have ha' : mixedEmbedding K (a : K) = (ZSpan.floor (latticeBasis K) w : mixedSpace K) := ha
    have h1 : z - mixedEmbedding K ((1 + (N : 𝓞 K) * a : 𝓞 K) : K)
        = (N : ℝ) • ZSpan.fract (latticeBasis K) w := by
      rw [ZSpan.fract_apply, ← ha', smul_sub, hw, smul_inv_smul₀ hNR]
      simp only [map_add (f := _), map_one, map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      ring
    rw [h1, _root_.norm_smul, Real.norm_natCast]
    exact mul_le_mul_of_nonneg_left (ZSpan.norm_fract_le _ _) (Nat.cast_nonneg _)

theorem eq_one_of_homogeneous_of_eq_one_on_class :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (φ : mixedSpace K → ℂ), m ≠ ⊥ → ContinuousOn φ {x | mixedEmbedding.norm x ≠ 0} → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → φ (mixedEmbedding K β) = 1) → ∀ x, mixedEmbedding.norm x ≠ 0 → φ x = 1 := by
  intro K _ _ m φ hm hc hh h1 x hx
  obtain ⟨C, hC⟩ := exists_near_one_mod_ideal K m hm
  choose β hβm hβ using hC
  set y : ℕ → mixedSpace K := fun n =>
    ((n : ℝ) + 1)⁻¹ • mixedEmbedding K (β (((n : ℝ) + 1) • x)) with hy
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hlim : Filter.Tendsto y Filter.atTop (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * C) Filter.atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have : x - y n = ((n : ℝ) + 1)⁻¹ •
        (((n : ℝ) + 1) • x - mixedEmbedding K (β (((n : ℝ) + 1) • x))) := by
      rw [smul_sub, inv_smul_smul₀ (hpos n).ne']
    rw [norm_sub_rev, this, _root_.norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hpos n)).le, one_div]
    exact mul_le_mul_of_nonneg_left (hβ _) (inv_pos.mpr (hpos n)).le
  have hopen : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
  have hca : ContinuousAt φ x := hc.continuousAt (hopen.mem_nhds hx)
  have hev : ∀ᶠ n in Filter.atTop, φ (y n) = 1 := by
    filter_upwards [hlim.eventually (hopen.mem_nhds hx)] with n hn
    have hne : β (((n : ℝ) + 1) • x) ≠ 0 := by
      intro h0
      apply hn
      simp [hy, h0]
    simp only [hy]
    rw [hh _ _ (inv_pos.mpr (hpos n))]
    exact h1 _ hne (hβm _)
  have h2 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds (φ x)) := hca.tendsto.comp hlim
  have h3 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  exact tendsto_nhds_unique h2 h3

end GlobalTheory
end

section

open scoped ContDiff

namespace GlobalTheory.GaussCoset

theorem exp_le_inv_pow {c : ℝ} (hc : 0 < c) (R : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-c * t ^ 2 + R * t) ≤
      ((n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c))) * t⁻¹ ^ n := by
  have hsq : 0 ≤ (2 * c * t - (R + 1)) ^ 2 / (4 * c) := by positivity
  have hid : (2 * c * t - (R + 1)) ^ 2 / (4 * c) =
      (R + 1) ^ 2 / (4 * c) - t - (-c * t ^ 2 + R * t) := by
    field_simp
    ring
  have h1 : Real.exp (-c * t ^ 2 + R * t) ≤
      Real.exp ((R + 1) ^ 2 / (4 * c)) * Real.exp (-t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-t) ≤ (n.factorial : ℝ) * t⁻¹ ^ n := by
    have hpos : 0 < t ^ n / (n.factorial : ℝ) := by positivity
    have hle : t ^ n / (n.factorial : ℝ) ≤ Real.exp t := Real.pow_div_factorial_le_exp t ht.le n
    rw [Real.exp_neg, inv_pow, ← div_eq_mul_inv, ← inv_div]
    exact inv_anti₀ hpos hle
  calc Real.exp (-c * t ^ 2 + R * t)
      ≤ Real.exp ((R + 1) ^ 2 / (4 * c)) * Real.exp (-t) := h1
    _ ≤ Real.exp ((R + 1) ^ 2 / (4 * c)) * ((n.factorial : ℝ) * t⁻¹ ^ n) := by gcongr
    _ = ((n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c))) * t⁻¹ ^ n := by ring

theorem summable_lattice {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] {c : ℝ} (hc : 0 < c)
    (R : ℝ) (x : V) :
    Summable fun z : L => Real.exp (-c * ‖(z : V) - x‖ ^ 2 + R * ‖(z : V) - x‖) := by
  have hmaj := (ZLattice.summable_norm_sub_inv_pow L (Module.finrank ℤ L + 1)
    (Nat.lt_succ_self _) x).mul_left
      (((Module.finrank ℤ L + 1).factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c)))
  refine Summable.of_norm_bounded_eventually hmaj ?_
  have hfin : {z : L | (z : V) = x}.Finite := by
    apply Set.Subsingleton.finite
    intro a ha b hb
    exact Subtype.ext (ha.trans hb.symm)
  filter_upwards [hfin.compl_mem_cofinite] with z hz
  have hne : (z : V) ≠ x := hz
  have hpos : 0 < ‖(z : V) - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_le_inv_pow hc R (Module.finrank ℤ L + 1) hpos

theorem discrete_of_finite {V : Type} [NormedAddCommGroup V] (L : AddSubgroup V)
    (h : {v : V | v ∈ L ∧ ‖v‖ ≤ 1}.Finite) : DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hU : IsOpen (Metric.ball (0 : V) 1 ∩ ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ) :=
    Metric.isOpen_ball.inter (h.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hset : ({0} : Set L) = Subtype.val ⁻¹' (Metric.ball (0 : V) 1 ∩
      ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ) := by
    ext z
    constructor
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simp
    · rintro ⟨h1, h2⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      have h1' : ‖(z : V)‖ < 1 := by simpa using h1
      apply h2
      refine ⟨⟨z.2, h1'.le⟩, ?_⟩
      intro hz0
      apply hne
      simpa using hz0
  rw [hset]
  exact hU.preimage continuous_subtype_val

theorem summable_gaussian_coset : ∀ (G V : Type) [AddCommGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (Γ U : AddSubgroup G), (∀ g ∈ Γ, p g = 0 → g = 0) → (∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U ∧ ‖p g‖ ≤ R}.Finite) → ∀ (c : ℝ), 0 < c → ∀ (R : ℝ) (w : G) (y : V), Summable fun g : Γ => Set.indicator (U : Set G) (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w) := by
  intro G V _ _ _ _ p Γ U hinj hfin c hc R w y
  by_cases hS : ∃ g₀ : Γ, (g₀ : G) + w ∈ U
  swap
  · simp only [not_exists] at hS
    have hzero : (fun g : Γ => Set.indicator (U : Set G)
        (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w)) = 0 := by
      funext g
      exact Set.indicator_of_notMem (hS g) _
    rw [hzero]
    exact summable_zero
  obtain ⟨g₀, hg₀⟩ := hS
  obtain ⟨L, hL⟩ : ∃ L : Submodule ℤ V, ∀ v, v ∈ L ↔ v ∈ (Γ ⊓ U).map p :=
    ⟨((Γ ⊓ U).map p).toIntSubmodule, fun _ => Iff.rfl⟩
  have hfin1 : {v : V | v ∈ L.toAddSubgroup ∧ ‖v‖ ≤ 1}.Finite := by
    refine ((hfin 1).image p).subset ?_
    rintro v ⟨hv, hv1⟩
    rw [Submodule.mem_toAddSubgroup, hL] at hv
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.mp hv
    obtain ⟨hgΓ, hgU⟩ := AddSubgroup.mem_inf.mp hg
    exact ⟨g, ⟨hgΓ, hgU, hv1⟩, rfl⟩
  have : DiscreteTopology L := discrete_of_finite L.toAddSubgroup hfin1
  let S := {g : Γ // (g : G) + w ∈ U}
  have hmem : ∀ s : S, p ((s.1 : G) - g₀) ∈ L := by
    intro s
    rw [hL]
    refine AddSubgroup.mem_map_of_mem p (AddSubgroup.mem_inf.mpr ⟨Γ.sub_mem s.1.2 g₀.2, ?_⟩)
    have hd := U.sub_mem s.2 hg₀
    rwa [add_sub_add_right_eq_sub] at hd
  let φ : S → L := fun s => ⟨p ((s.1 : G) - g₀), hmem s⟩
  have hφ : Function.Injective φ := by
    intro s t hst
    have h1 : p ((s.1 : G) - g₀) = p ((t.1 : G) - g₀) := congrArg Subtype.val hst
    have h2 : p ((s.1 : G) - t.1) = p ((s.1 : G) - g₀) - p ((t.1 : G) - g₀) := by
      rw [← map_sub]
      congr 1
      abel
    rw [h1, sub_self] at h2
    have h3 := hinj _ (Γ.sub_mem s.1.2 t.1.2) h2
    exact Subtype.ext (Subtype.ext (sub_eq_zero.mp h3))
  let F : Γ → ℝ := fun g => Set.indicator (U : Set G)
    (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w)
  show Summable F
  have hL' : Summable fun z : L =>
      Real.exp (-c * ‖(z : V) - -(p g₀ + y)‖ ^ 2 + R * ‖(z : V) - -(p g₀ + y)‖) :=
    summable_lattice L hc R _
  have hcomp : Summable (F ∘ (Subtype.val : S → Γ)) := by
    have heq : F ∘ (Subtype.val : S → Γ) = (fun z : L =>
        Real.exp (-c * ‖(z : V) - -(p g₀ + y)‖ ^ 2 + R * ‖(z : V) - -(p g₀ + y)‖)) ∘ φ := by
      funext s
      have hshift : ((φ s : L) : V) - -(p g₀ + y) = p (s.1 : G) + y := by
        show p ((s.1 : G) - g₀) - -(p g₀ + y) = p (s.1 : G) + y
        rw [map_sub]
        abel
      simp only [Function.comp_apply, F]
      rw [Set.indicator_of_mem (show (s.1 : G) + w ∈ (U : Set G) from s.2), hshift]
    rw [heq]
    exact hL'.comp_injective hφ
  refine (Function.Injective.summable_iff Subtype.val_injective ?_).mp hcomp
  intro g hg
  have hnot : (g : G) + w ∉ (U : Set G) := fun h => hg ⟨⟨g, h⟩, rfl⟩
  exact Set.indicator_of_notMem hnot _

end GlobalTheory.GaussCoset
end

section

open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

namespace SquareTheorem


open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
theorem _root_.GlobalTheory.LocalQuad.SquareTheorem.isSquare_of_norm_sub_one_lt {K : Type*} [NormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (x : K) (h : ‖x - 1‖ < ‖(4 : K)‖) : IsSquare x := by
  have h4 : (4 : K) ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt (norm_nonneg _) h)
  set c : K := (x - 1) / 4 with hc
  have hx : x = 1 + 4 * c := by rw [hc]; field_simp; ring
  have hc1 : ‖c‖ < 1 := by
    rw [hc, norm_div, div_lt_one (norm_pos_iff.2 h4)]; exact h
  set r : ℝ := ‖c‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsq : ∀ z : K, ‖z‖ ≤ r → ‖z ^ 2‖ ≤ r := by
    intro z hz
    rw [norm_pow]
    calc ‖z‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ ≤ r := by nlinarith
  let s := Metric.closedBall (0 : K) r
  haveI : CompleteSpace s := Metric.isClosed_closedBall.completeSpace_coe
  have hmem : ∀ z : s, c - (z : K) ^ 2 ∈ s := by
    intro z
    have hz : ‖(z : K)‖ ≤ r := mem_closedBall_zero_iff.1 z.2
    have hu := IsUltrametricDist.norm_add_le_max c (-((z : K) ^ 2))
    rw [norm_neg, ← sub_eq_add_neg] at hu
    exact mem_closedBall_zero_iff.2 (hu.trans (max_le le_rfl (hsq _ hz)))
  let f : s → s := fun z => ⟨c - (z : K) ^ 2, hmem z⟩
  have hf : ContractingWith ‖c‖₊ f := by
    refine ⟨hc1, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    have ha : ‖(a : K)‖ ≤ r := mem_closedBall_zero_iff.1 a.2
    have hb : ‖(b : K)‖ ≤ r := mem_closedBall_zero_iff.1 b.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have : (c - (a : K) ^ 2) - (c - (b : K) ^ 2) = ((b : K) + a) * ((b : K) - a) := by ring
    simp only [f, this, norm_mul, coe_nnnorm]
    rw [norm_sub_rev (b : K)]
    exact mul_le_mul_of_nonneg_right
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb ha)) (norm_nonneg _)
  haveI : Nonempty s := ⟨⟨0, by simp [s, hr0]⟩⟩
  set z : s := ContractingWith.fixedPoint f hf
  have hz : (z : K) = c - (z : K) ^ 2 := by
    have := ContractingWith.fixedPoint_isFixedPt (f := f) hf
    exact (congrArg Subtype.val this).symm
  exact ⟨1 + 2 * (z : K), by linear_combination hx - 4 * hz⟩

end SquareTheorem


open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
theorem _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : Valued.v (x - 1) < Valued.v (4 : v.adicCompletion F)) : IsSquare x :=
  _root_.GlobalTheory.LocalQuad.SquareTheorem.isSquare_of_norm_sub_one_lt x (Valued.toNormedField.norm_lt_iff.2 h)

end GlobalTheory.LocalQuad
end

section

namespace GlobalTheory.IntegralPointNormSquareBound

theorem exists_pos_mul_norm_sq_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (h : ∀ v : V, v ≠ 0 → 0 < om v (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * ‖v‖ ^ 2 ≤ om v (J v) := by
  have hcont : Continuous fun v : V => om v (J v) := by
    let B : V →ₗ[ℝ] V →L[ℝ] ℝ :=
      (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] V →L[ℝ] ℝ).toLinearMap ∘ₗ om
    have h1 : Continuous B := B.continuous_of_finiteDimensional
    have h2 : Continuous J := J.continuous_of_finiteDimensional
    exact h1.clm_apply h2
  have hcomp : IsCompact (Metric.sphere (0 : V) 1) := by
    haveI : ProperSpace V := FiniteDimensional.proper_real V
    exact isCompact_sphere 0 1
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Metric.sphere (0 : V) 1, c ≤ om u (J u) := by
    rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun u hu => by rw [he] at hu; exact hu.elim⟩
    · obtain ⟨x, hx, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
      refine ⟨om x (J x), h x ?_, fun u hu => hmin hu⟩
      rintro rfl
      simp at hx
  refine ⟨c, hc, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv
    simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
      simp [norm_smul, hn.ne']
    have h3 := hle _ hu
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h3
    have h4 : ‖v‖⁻¹ * (‖v‖⁻¹ * om v (J v)) * ‖v‖ ^ 2 = om v (J v) := by
      field_simp
    calc c * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * om v (J v)) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = om v (J v) := h4

end GlobalTheory.IntegralPointNormSquareBound
end

section

namespace GlobalTheory.CoefficientContraction

theorem coeff_eq_contraction {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] {κ : Type} [DecidableEq κ] (b : Module.Basis κ ℚ W) (i : κ)
    (t : TensorProduct ℚ V W) :
    TensorProduct.equivFinsuppOfBasisRight b t i
      = TensorProduct.rid ℚ V (LinearMap.lTensor V (b.coord i) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem eq_zero_of_contractions {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (t : TensorProduct ℚ V W)
    (h : ∀ m : W →ₗ[ℚ] ℚ, TensorProduct.rid ℚ V (LinearMap.lTensor V m t) = 0) : t = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℚ W
  apply (TensorProduct.equivFinsuppOfBasisRight (M := V) b).injective
  ext i
  rw [coeff_eq_contraction, h, map_zero, Finsupp.zero_apply]

end GlobalTheory.CoefficientContraction
end
