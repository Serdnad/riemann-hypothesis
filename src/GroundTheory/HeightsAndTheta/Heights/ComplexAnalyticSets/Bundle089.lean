module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Regular.RegularSequence
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.Regular.LinearMap
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem abs_finsum_le_finsum_abs {α : Type*} (f : α → ℝ) : |∑ᶠ i, f i| ≤ ∑ᶠ i, |f i| := by
  by_cases h : (Function.support f).Finite
  · have hs : Function.support (fun i => |f i|) ⊆ ↑h.toFinset := by
      intro i hi
      simpa using hi
    rw [finsum_eq_sum_of_support_subset (s := h.toFinset) f (by rw [Set.Finite.coe_toFinset]),
      finsum_eq_sum_of_support_subset _ hs]
    exact Finset.abs_sum_le_sum_abs _ _
  · rw [finsum_of_infinite_support h, abs_zero]
    exact finsum_nonneg fun i => abs_nonneg _

variable {n d : ℕ}

theorem abs_chartDens_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    |chartDens J A f φ y| ≤ chartAbsDens J A f φ y := by
  classical
  refine (abs_finsum_le_finsum_abs _).trans (le_of_eq (finsum_congr fun x => ?_))
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp

theorem chartAbsDens_nonneg (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    0 ≤ chartAbsDens J A f φ y :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity

theorem CutOff.proof (hS : CutOffShape.Statement) (hT : CutOffTube.Statement)
    (hG : CutOffGradient.Statement) : CutOff.Statement := by
  obtain ⟨K, hK⟩ := hG
  intro n d J A P hJ hdim hA hP
  have hA' : ContDiff ℝ ∞ fun x : Fin n → ℂ => A *ᵥ x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff.restrict_scalars ℝ
  have hc : Continuous fun x : Fin n → ℂ => ‖eval (A *ᵥ x) P‖ ^ 2 :=
    ((MvPolynomial.continuous_eval P).comp hA'.continuous).norm.pow 2
  have key : ∀ T : (Fin (d + 1) → ℂ) → ℝ, Integrable T → ∀ (k : ℕ) (F : (Fin (d + 1) → ℂ) → ℝ),
      (∀ y, ‖F y‖ ≤ K / ((k : ℝ) + 1) * T y) → ‖∫ y, F y‖ ≤ K / ((k : ℝ) + 1) * ∫ y, T y :=
    fun T hTi k F hF => (norm_integral_le_of_norm_le (hTi.const_mul _)
      (Eventually.of_forall hF)).trans_eq (integral_const_mul _ _)
  have lim : ∀ c : ℝ, Tendsto (fun k : ℕ => K / ((k : ℝ) + 1) * c) atTop (𝓝 0) := fun c => by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul K).mul_const c
    rw [mul_zero, zero_mul] at h
    exact h.congr fun k => by ring
  refine ⟨logLogCutAlong A P, fun k => ((hS _ P).1 k).1.comp hA', fun k x => ((hS _ P).1 k).2.1 _,
    fun k => ⟨{x | ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k}, isOpen_lt hc continuous_const, fun x hx => ?_,
      fun x hx => ((hS _ P).1 k).2.2 _ hx.1⟩, fun x _ hx => (hS _ P).2 _ hx, fun R => ?_,
    fun R φ hφ => ?_⟩
  · have hx0 : eval (A *ᵥ x) P = 0 := hx
    show ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k
    rw [hx0, norm_zero, zero_pow two_ne_zero]
    exact (cutLevel_mem k).1
  · have hTi := hT n d J A P R (fun _ => euclPot) hJ hdim hA hP
      fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
    have hl := (lim (∫ y, tubeDens J A P R (fun _ => euclPot) y)).const_mul 2
    rw [mul_zero] at hl
    refine squeeze_zero_norm (fun k => ?_) hl
    have h := hK n d J A P R (fun _ => euclPot) k
    refine (norm_sub_le _ _).trans ?_
    rw [two_mul]
    exact add_le_add (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.1)
      (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.2)
  · refine squeeze_zero_norm (fun k => key _ (hT n d J A P R φ hJ hdim hA hP hφ) k _ fun y => ?_)
      (lim _)
    rw [Real.norm_of_nonneg (chartAbsDens_nonneg _ _ _ _ y)]
    exact (hK n d J A P R φ k y hJ hdim hA).1

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

variable {n d : ℕ}

theorem logLogCut_mem_Icc {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ) :
    logLogCut Q k y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold logLogCut cutStep
  split_ifs
  · simp
  · simp
  · exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem comp_sheet_eventuallyEq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (g : (Fin d → ℂ) → ℝ) :
    (fun w => g (A *ᵥ s w)) =ᶠ[𝓝 (A *ᵥ x)] g := by
  obtain ⟨U, hU, hxU, -, -, hsec, -⟩ := hs
  filter_upwards [hU.mem_nhds hxU] with w hw
  rw [(hsec w hw).1]

theorem maDens_cons_of_hessC_eq_smul {D : ℕ} (f g : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) (c : ℝ)
    (h : hessC f y = (c : ℂ) • hessC g y) :
    maDens (Fin.cons f ψ) y = c * maDens (Fin.cons g ψ) y := by
  have e : ∀ u : (Fin (D + 1) → ℂ) → ℝ,
      (fun k => hessC ((Fin.cons u ψ : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ) k) y) =
        Fin.cons (hessC u y) (fun k => hessC (ψ k) y) := fun u => by
    funext k; exact Fin.cases rfl (fun i => rfl) k
  have hm := mdisc_update_smul
    (Fin.cons (hessC g y) (fun k => hessC (ψ k) y) : Fin (D + 1) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    0 (c : ℂ) (hessC g y)
  rw [Fin.update_cons_zero, Fin.update_cons_zero] at hm
  unfold maDens
  rw [e, e, h, hm, Complex.re_ofReal_mul]
  ring

theorem vecCons_comp {D : ℕ} (f : (Fin n → ℂ) → ℝ) (φ : Fin D → (Fin n → ℂ) → ℝ)
    (s : (Fin (D + 1) → ℂ) → Fin n → ℂ) :
    (fun k => (vecCons f φ : Fin (D + 1) → (Fin n → ℂ) → ℝ) k ∘ s) = Fin.cons (f ∘ s) (fun k => φ k ∘ s) := by
  funext k; exact Fin.cases rfl (fun i => rfl) k

theorem sheetSum_le_mul {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) (c : ℝ)
    (F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (h : ∀ x ∈ fibre J A y, ∀ s, IsSheetAt J A x s → F x s ≤ c * G x s) :
    sheetSum J A F y ≤ c * sheetSum J A G y := by
  classical
  unfold sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · exact h x hx _ hs.choose_spec
  · simp

theorem term_le_of_hessC {D : ℕ} {X : Type*} (B : Set X) (w t : X → ℝ) (x : X)
    (hw : |w x| ≤ 1) (hwB : x ∉ B → w x = 0) (ht : 0 ≤ t x) (f g : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) {c e : ℝ}
    (h : hessC f y = (e : ℂ) • hessC g y) (he : |e| ≤ c * t x) :
    |w x * maDens (Fin.cons f ψ) y| ≤ c * |B.indicator t x * maDens (Fin.cons g ψ) y| := by
  rw [maDens_cons_of_hessC_eq_smul f g ψ y e h]
  by_cases hx : x ∈ B
  · rw [Set.indicator_of_mem hx, abs_mul, abs_mul, abs_mul, abs_of_nonneg ht]
    have hM := abs_nonneg (maDens (Fin.cons g ψ) y)
    calc |w x| * (|e| * |maDens (Fin.cons g ψ) y|) ≤ 1 * (c * t x * |maDens (Fin.cons g ψ) y|) :=
          mul_le_mul hw (mul_le_mul_of_nonneg_right he hM) (by positivity) zero_le_one
      _ = c * (t x * |maDens (Fin.cons g ψ) y|) := by ring
  · rw [hwB hx, zero_mul, abs_zero, Set.indicator_of_notMem hx, zero_mul, abs_zero, mul_zero]

theorem CutOffGradient.proof (hH : LogLogCutHess.Statement) : CutOffGradient.Statement := by
  obtain ⟨K, hK0, hK⟩ := hH
  refine ⟨K, fun n d J A P R φ k y hJ hdim hA => ?_⟩
  have hfin := (FibreBound.proof n (d + 1) J A hJ hdim hA y).2.1
  obtain ⟨a, b, ha, hb, hHa, hHb⟩ := hK (d + 1) P k y
  have hc : 0 ≤ K / ((k : ℝ) + 1) := by positivity
  set B := Metric.closedBall (0 : Fin n → ℂ) R
  have ht : ∀ x, 0 ≤ tubeWeight P (A *ᵥ x) := fun x => by
    unfold tubeWeight; split_ifs <;> positivity

  have key : ∀ (w : (Fin n → ℂ) → ℝ) (g : (Fin (d + 1) → ℂ) → ℝ) (e : ℝ),
      (∀ x, |w x| ≤ 1) → (∀ x, x ∉ B → w x = 0) →
      hessC g y = (e : ℂ) • hessC (fun z => logAbsSq P z ^ 2 / 2) y →
      |e| ≤ K / ((k : ℝ) + 1) * tubeWeight P y →
      chartAbsDens J A w (vecCons (fun x => g (A *ᵥ x)) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y := by
    intro w g e hw hwB hg he
    unfold chartAbsDens tubeDens
    refine sheetSum_le_mul hfin _ _ _ fun x hx s hs => ?_
    have hy : A *ᵥ x = y := hx.2
    rw [vecCons_comp, vecCons_comp]
    refine term_le_of_hessC B w (fun x => tubeWeight P (A *ᵥ x)) x (hw x) (hwB x) (ht x) _ _ _ y ?_
      (by rw [hy]; exact he)
    rw [← hy, Function.comp_def, Function.comp_def, hessC_congr' (comp_sheet_eventuallyEq hs g),
      hessC_congr' (comp_sheet_eventuallyEq hs fun z => logAbsSq P z ^ 2 / 2), hy, hg]
  have h1 : ∀ x, |B.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := fun x => by
    unfold Set.indicator; split_ifs <;> simp
  have h0 : ∀ x, x ∉ B → B.indicator (fun _ => (1 : ℝ)) x = 0 := fun x hx => Set.indicator_of_notMem hx _
  refine ⟨key _ (logLogCut P k) a h1 h0 hHa ha, key _ (fun z => logLogCut P k z ^ 2 / 2) b h1 h0 hHb hb,
    key _ (logLogCut P k) a (fun x => ?_) (fun x hx => Set.indicator_of_notMem hx _) hHa ha⟩
  unfold Set.indicator
  split_ifs
  · have hm := logLogCut_mem_Icc P k (A *ᵥ x)
    show |logLogCut P k (A *ᵥ x)| ≤ 1
    rw [abs_of_nonneg hm.1]; exact hm.2
  · simp

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

theorem TubeEuclMass.proof (hC : TubeCollarMass.Statement) (hD : TubeDeepMass.Statement) :
    TubeEuclMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  have hS : {y : Fin (d + 1) → ℂ | logAbsSq P y < -Real.exp 1} =
      {y | -Real.exp 1 ≤ logAbsSq P y}ᶜ := by
    ext y
    simp [not_le]
  have h := (hC n d J A P R hJ hdim hA hP).add (hD n d J A P R hJ hdim hA hP)
  rw [hS, Set.indicator_self_add_compl] at h
  exact h

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R]

theorem exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) :
    ∃ s : R, s ≠ 0 ∧ ∀ a ∈ maximalIdeal R, a * s = 0 := by
  have hmk : ∀ y : R, y • (1 : R ⧸ maximalIdeal R) = Ideal.Quotient.mk (maximalIdeal R) y := fun y ↦ by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  have hns : ¬ Subsingleton ((R ⧸ maximalIdeal R) →ₗ[R] R) := by
    rw [IsSMulRegular.subsingleton_linearMap_iff]
    rintro ⟨r, hr, hreg⟩
    refine h r ?_ hreg
    have h1 := Module.mem_annihilator.mp hr (1 : R ⧸ maximalIdeal R)
    rwa [hmk, Ideal.Quotient.eq_zero_iff_mem] at h1
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨f, hf⟩ := exists_ne (0 : (R ⧸ maximalIdeal R) →ₗ[R] R)
  refine ⟨f 1, fun h0 ↦ hf (LinearMap.ext fun y ↦ ?_), fun a ha ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← hmk, map_smul, h0, smul_zero, LinearMap.zero_apply]
  · rw [← smul_eq_mul, ← map_smul, hmk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

theorem hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (k : ℕ) (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R M) 0 := by
  obtain ⟨s, hs, hms⟩ := exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular h
  have : Module.Free R M := GroundTheory.Arith.SchemeCoh.free_of_hasProjectiveDimensionLT_of_mul_eq_zero hs hms k M hM
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mp (by
    rw [← IsProjective.iff_projective]; infer_instance)

theorem hasProjectiveDimensionLT_of_quotSMulTop [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) (k : ℕ) (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hxM : IsSMulRegular M x)
    (hM : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x M)) (k + 1)) :
    HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) := by
  have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
  have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
  induction k generalizing M with
  | zero =>
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]
      at hM ⊢
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x M) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hfree : Module.Free (R ⧸ span {x}) (QuotSMulTop x M) := Module.free_of_flat_of_isLocalRing
    have := Module.finitePresentation_of_finite R M
    have : Module.Free R M :=
      (Module.free_quotSMulTop_iff_free R M (IsLocalRing.ringJacobson_eq_maximalIdeal R ▸ hx) hxM).mp hfree
    infer_instance
  | succ k ih =>
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    let f₁ : QuotSMulTop x K →ₗ[R] QuotSMulTop x (Fin n → R) := QuotSMulTop.map x K.subtype
    let f₂ : QuotSMulTop x (Fin n → R) →ₗ[R] QuotSMulTop x M := QuotSMulTop.map x π
    have hex0 : Function.Exact K.subtype π := fun y ↦
      ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.2⟩
    have ex : Function.Exact f₁ f₂ := QuotSMulTop.map_exact x hex0 hπ
    have surj : Function.Surjective f₂ := QuotSMulTop.map_surjective x hπ
    have inj : Function.Injective f₁ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [LinearMap.mem_ker] at hy
      simp only [f₁, Submodule.mkQ_apply, QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨b, -, hb⟩ := hy
      have hπb : π b = 0 := by
        apply hxM
        show x • π b = x • 0
        rw [← map_smul, hb, smul_zero]
        exact y.2
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨⟨b, hπb⟩, Submodule.mem_top, Subtype.ext hb⟩
    let g₁ := f₁.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let g₂ := f₂.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let T := ModuleCat.shortComplexOfCompEqZero g₁ g₂
      (LinearMap.ext fun y ↦ ex.apply_apply_eq_zero y)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T ex inj surj
    have hproj2 : Projective T.X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK' : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x K)) (k + 1) :=
      (hT.hasProjectiveDimensionLT_X₃_iff k hproj2).mp hM
    exact (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mpr (ih K hxK hK')

theorem length_le_of_isWeaklyRegular_quotient_span_singleton [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) [IsLocalRing (R ⧸ span {x})] (d : ℕ)
    (hd : ∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d + 1)
    (rs : List (R ⧸ span {x})) (hrs : ∀ r ∈ rs, r ∈ maximalIdeal (R ⧸ span {x}))
    (hreg : IsWeaklyRegular (R ⧸ span {x}) rs) : rs.length ≤ d := by
  let lift : R ⧸ span {x} → R := Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b :=
    Function.surjInv_eq Ideal.Quotient.mk_surjective
  have hrs' : (rs.map lift).map (algebraMap R (R ⧸ span {x})) = rs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id rs]
    exact List.map_congr_left fun b _ ↦ by simp [Ideal.Quotient.algebraMap_eq, hlift]
  have hloc : IsLocalHom (Ideal.Quotient.mk (span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcomap : (maximalIdeal (R ⧸ span {x})).comap (Ideal.Quotient.mk (span {x})) =
      maximalIdeal R := IsLocalRing.maximalIdeal_comap _
  have hmem : ∀ r ∈ x :: rs.map lift, r ∈ maximalIdeal R := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hx
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
      rw [← hcomap, Ideal.mem_comap, hlift]
      exact hrs b hb
  have e : (R ⧸ span {x}) ≃ₗ[R] QuotSMulTop x R :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
  have hreg' : IsWeaklyRegular R (x :: rs.map lift) := by
    rw [isWeaklyRegular_cons_iff]
    refine ⟨hxR, (e.isWeaklyRegular_congr _).mp ?_⟩
    rw [← isWeaklyRegular_map_algebraMap_iff (R ⧸ span {x}), hrs']
    exact hreg
  have := hd _ hmem hreg'
  simp only [List.length_cons, List.length_map] at this
  omega

theorem hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d) →
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ),
        HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) →
          HasProjectiveDimensionLE (ModuleCat.of R M) d := by
  induction d with
  | zero =>
    intro R _ _ _ hd M _ _ _ k hM
    refine hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular (fun y hy hy' ↦ ?_) M k hM
    have := hd [y] (by simpa using hy) ((isWeaklyRegular_singleton_iff R y).mpr hy')
    simp at this
  | succ d ih =>
    intro R _ _ _ hd M _ _ _ k hM
    by_cases hex : ∃ y ∈ maximalIdeal R, IsSMulRegular R y
    swap
    · push Not at hex
      have := hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular hex M k hM
      exact hasProjectiveDimensionLT_of_ge _ (0 + 1) (d + 1 + 1) (by omega)
    obtain ⟨x, hx, hxR⟩ := hex
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (R ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have hd' := length_le_of_isWeaklyRegular_quotient_span_singleton hx hxR d hd
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK : HasProjectiveDimensionLT (ModuleCat.of R K) (k + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mp
        (hasProjectiveDimensionLT_of_ge _ (k + 1) (k + 1 + 1) (by omega))
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    have hKx := GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_quotSMulTop hxR k K hxK hK
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x K) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hKx' := ih (R ⧸ span {x}) hd' (QuotSMulTop x K) k hKx
    have hK2 := hasProjectiveDimensionLT_of_quotSMulTop hx hxR d K hxK hKx'
    exact (hS.hasProjectiveDimensionLT_X₃_iff d hproj).mpr hK2

end GroundTheory.Heights₂.Heights
end
