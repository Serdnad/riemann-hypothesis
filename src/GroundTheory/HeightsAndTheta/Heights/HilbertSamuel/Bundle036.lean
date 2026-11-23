module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle003

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ProjLine
open scoped Topology

noncomputable section

namespace BlockImageMetrics

theorem leviForm_comp_clm {E F : Type} [Fintype E] [Fintype F] (L : (E → ℂ) →L[ℂ] (F → ℂ))
    {φ : (F → ℂ) → ℝ} {z : E → ℂ} (hφ : ContDiffAt ℝ 2 φ (L z)) (w : E → ℂ) :
    leviForm (fun y => φ (L y)) z w = leviForm φ (L z) (L w) := by
  set Lr : (E → ℂ) →L[ℝ] (F → ℂ) := L.restrictScalars ℝ with hLr
  have hev : fderiv ℝ (fun y => φ (L y)) =ᶠ[𝓝 z] fun y => (fderiv ℝ φ (Lr y)).comp Lr := by
    have h1 : ∀ᶠ x in 𝓝 (L z), ContDiffAt ℝ 2 φ x := hφ.eventually (by simp)
    have h2 : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 φ (L y) := (L.continuous.tendsto z).eventually h1
    filter_upwards [h2] with y hy
    have hd : DifferentiableAt ℝ φ (Lr y) := hy.differentiableAt (by norm_num)
    exact (hd.hasFDerivAt.comp y Lr.hasFDerivAt).fderiv
  have hd2 : DifferentiableAt ℝ (fderiv ℝ φ) (Lr z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD : HasFDerivAt (fun y => (fderiv ℝ φ (Lr y)).comp Lr)
      ((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ (fderiv ℝ φ (Lr z))).comp 0 +
        ((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr).comp
          ((fderiv ℝ (fderiv ℝ φ) (Lr z)).comp Lr)) z :=
    (hd2.hasFDerivAt.comp z Lr.hasFDerivAt).clm_comp (hasFDerivAt_const Lr z)
  have hIw : L (Complex.I • w) = Complex.I • L w := L.map_smul _ _
  unfold leviForm
  rw [hev.fderiv_eq, hD.fderiv]
  simp [hLr, hIw]

theorem isSemipositiveRel_of_linear {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {F : Type}
    [Fintype F] (A : HermLine ι) (L : ((Σ k, ι k) → ℂ) →L[ℂ] (F → ℂ))
    (hA : A.h = fun z => (fsMetric (ι := F)).ρ (L z)) (hL : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → L z ≠ 0)
    (P0 P : Ideal (MRing ι)) : IsSemipositiveRel P0 P A := by
  have hsm : ∀ z, L z ≠ 0 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fsMetric (ι := F)).ρ (L z) := fun z hz =>
    (isSmoothMetric_fs (J := F) (L z) hz).contDiffAt (isOpen_ne.mem_nhds hz)
  refine ⟨?_, fun z hz w _ => ?_⟩
  · unfold IsSmoothHerm
    rw [hA]
    intro z hz
    exact ((hsm z (hL z hz)).comp z (L.restrictScalars ℝ).contDiff.contDiffAt).contDiffWithinAt
  · have hz0 := hL z hz.1
    have hlog : ContDiffAt ℝ 2 (fun x => Real.log ((fsMetric (ι := F)).ρ x)) (L z) :=
      ((hsm z hz0).of_le (WithTop.coe_le_coe.2 le_top)).log ((fsMetric (ι := F)).pos _ hz0).ne'
    rw [show (fun z => Real.log (A.h z)) =
      fun y => (fun x => Real.log ((fsMetric (ι := F)).ρ x)) (L y) by rw [hA]]
    rw [leviForm_comp_clm L hlog w]
    exact leviForm_log_fs_nonneg hz0 _

def matCLM {κ J : Type} [Fintype κ] [Fintype J] (N : Matrix κ J ℤ) : (J → ℂ) →L[ℂ] (κ → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin (N.map (Int.cast : ℤ → ℂ)))

theorem matCLM_apply {κ J : Type} [Fintype κ] [Fintype J] (N : Matrix κ J ℤ) (u : J → ℂ) :
    matCLM N u = fun i => ∑ j, (N i j : ℂ) * u j := by
  funext i
  simp [matCLM, Matrix.mulVec, dotProduct]

def blockCLM {K : Type} {ι : K → Type} (k₀ : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k₀ → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (⟨k₀, i⟩ : Σ k, ι k)

theorem blockCLM_apply {K : Type} {ι : K → Type} (k₀ : K) (z : (Σ k, ι k) → ℂ) :
    blockCLM k₀ z = fun i => z ⟨k₀, i⟩ := rfl

theorem proof : BlockImageMetrics.Statement := by
  constructor
  · intro κ J _ _ N hN P
    refine isSemipositiveRel_of_linear _ (matCLM N) ?_ ?_ ⊥ P
    · funext u
      rw [matCLM_apply]
      rfl
    · intro z hz h0
      rw [matCLM_apply] at h0
      obtain ⟨i, hi⟩ := hz ()
      exact hi (congrFun (hN z h0) _)
  · intro K _ _ ι _ k₀ P
    refine isSemipositiveRel_of_linear _ (blockCLM k₀) ?_ ?_ ⊥ P
    · funext z
      rw [blockCLM_apply]
      simp only [HermLine.ofMetrics]
      rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [unitDeg, hk]) (by simp)]
      simp [unitDeg]
    · intro z hz h0
      obtain ⟨i, hi⟩ := hz k₀
      exact hi (congrFun h0 i)

end BlockImageMetrics

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PointHeightFSAux

abbrev fsOne : HermLine (GlobalTheory (Fin 1)) := HermLine.ofCone (fsMetric (ι := Ix (Fin 1)))

abbrev x0 : MRing (GlobalTheory (Fin 1)) := X ⟨(), 0⟩

theorem isSmoothHerm_fsOne : IsSmoothHerm fsOne := by
  refine (ProjLine.isSmoothMetric_fs (J := Ix (Fin 1))).mono fun z hz h0 => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact hi (congrFun h0 _)

theorem divisorSupport_coordinate_point : divSupp (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) x0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun W hW => ?_
  obtain ⟨i, hi⟩ := hW.2 ()
  have hle := hW.1.1.2
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst hi0
  exact hi (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))

theorem logNorm_coordinate_point : logNorm fsOne x0 = fun _ => 0 := by
  funext z
  have hρ : fsOne.h z = ‖z ⟨(), 0⟩‖ := by
    let _ : Unique (Ix (Fin 1)) :=
      ⟨⟨⟨(), 0⟩⟩, fun p => by rcases p with ⟨⟨⟩, i⟩; rw [Subsingleton.elim i 0]; rfl⟩
    show ‖WithLp.toLp 2 z‖ = _
    rw [EuclideanSpace.norm_eq, Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]
    rfl
  simp only [logNorm, hρ, map_X, eval_X]
  rcases eq_or_ne (z ⟨(), 0⟩) 0 with h | h
  · simp [h]
  · rw [div_self (norm_ne_zero_iff.mpr h), Real.log_one]

theorem ptsIntegral_zero {e : ℕ} (P : Ideal (MRing (GlobalTheory (Fin 1))))
    (φ : Fin e → (Ix (Fin 1) → ℂ) → ℝ) : ptsIntegral P φ (fun _ => 0) = 0 := by
  classical
  unfold ptsIntegral
  split_ifs
  · simp [ptsIntegralAt, sheetDensity]
  · rfl

end PointHeightFSAux


open PointHeightFSAux in
theorem PointHeightFS.proof : PointHeightFS.Statement := by
  intro I hI
  classical
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) (0 + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot 0
  have hs : IsMultiHomog x0 fun _ => 1 := IndefiniteRowSideFullHecke.Inter.isMultiHomog_Xb 1 0
  have hx0 : x0 ∉ (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) := by
    rw [Ideal.mem_bot]
    exact X_ne_zero _
  have hR := (hI Unit (GlobalTheory (Fin 1))).2.2 ⊥ 0 Fin.elim0 fsOne x0 (fun _ => 1) hP (fun j => j.elim0)
    isSmoothHerm_fsOne (fun _ => rfl) hs hx0
  have hL : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (GlobalTheory (Fin 1))) fsOne : Fin 1 → _) =
      fun _ => fsOne := by
    funext j
    fin_cases j
    rfl
  rw [hL] at hR
  unfold hhOf
  rw [hR, recR, divisorSupport_coordinate_point, finsum_mem_empty, zero_sub, arInt, logNorm_coordinate_point, ptsIntegral_zero, neg_zero]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocalRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] in
theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]


omit [Fintype K] in
theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k


omit [Fintype K] in
theorem isMultiHomog_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    exact (mem_support_iff.mp hm) (by rw [coeff_C, if_neg (Ne.symm h)])
  subst this
  simp


omit [Fintype K] in
theorem isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [h]

theorem isMultiHomog_chartMono (c : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k) e := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ e k)
      (∑ k ∈ s, e k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isMultiHomog_C (ι := ι) 1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      refine isMultiHomog_mul ?_ ih
      induction e k with
      | zero => simpa using isMultiHomog_C (ι := ι) 1
      | succ m ihm =>
        rw [pow_succ, succ_nsmul]
        exact isMultiHomog_mul ihm (isMultiHomog_X k (c k))
  have h : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = e := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [h] at this

theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (N : K → ℕ) (H : MRing ι), IsMultiHomog H N ∧ aeval y H = x * ∏ k, y ⟨k, c k⟩ ^ N k := by
  classical
  induction hx using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hu
    refine ⟨Pi.single k 1, X ⟨k, i⟩, isMultiHomog_X k i, ?_⟩
    rw [aeval_X, Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp only [Pi.single_eq_same, pow_one]
    exact (div_mul_cancel₀ _ (hc k)).symm
  | algebraMap r =>
    exact ⟨0, C r, isMultiHomog_C r, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₂ k + H₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₁ k,
      isMultiHomog_add (isMultiHomog_mul h₁ (isMultiHomog_chartMono c N₂))
        (add_comm N₂ N₁ ▸ isMultiHomog_mul h₂ (isMultiHomog_chartMono c N₁)), ?_⟩
    simp only [map_add (f := _), map_mul, map_prod, map_pow, aeval_X, e₁, e₂, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib]
    ring
  | mul u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * H₂, isMultiHomog_mul h₁ h₂, ?_⟩
    simp only [map_mul, e₁, e₂, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring

theorem proof : LocalRep.Statement := by
  intro K _ ι _ Ω _ y a n s z hs hz
  classical
  choose c hzc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hzc k
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y (X ⟨k, c k⟩) = 0
      simp [mConeMap, h0]
    simpa using hz.2 _ hmem
  obtain ⟨N, H, hH, he⟩ := exists_form_of_mem_chartRingZ y c hyc (hs c hyc)
  refine ⟨N + fun k => ((n : ℤ) * a k).toNat, N + fun k => (-((n : ℤ) * a k)).toNat,
    H * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ ((n : ℤ) * a k).toNat,
    ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N + fun k => (-((n : ℤ) * a k)).toNat) k,
    isMultiHomog_mul hH (isMultiHomog_chartMono c _), isMultiHomog_chartMono c _, fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X]
    rw [he, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← zpow_add₀ (hyc k)]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_prod, map_pow, map_X, eval_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k)

end LocalRep

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResolutionFormsIndependent.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ) (n r : ℕ)
    (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b → ∀ a : Fin r → ℂ,
    (∀ y : d.R.X, ∑ k, a k * eval (resPt d y) (map (algebraMap ℚ ℂ) (b k)) = 0) → a = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def matSubst {J : Type} [Fintype J] (B : Matrix J J ℚ) (b : MvPolynomial J ℚ) : MvPolynomial J ℚ :=
  aeval (fun i => ∑ j, C (B i j) * X j) b

theorem matAct_one {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] [DecidableEq J] (x : J → Ω) :
    matAct (1 : Matrix J J ℚ) x = x := by
  funext i
  simp only [matAct, Matrix.one_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

def HSMTransport.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (B : Matrix (Ix κ) (Ix κ) ℚ), IsInvMat B →
    ∃ d' : HSMDatum D Ω κ, d'.x = matAct B d.x ∧ (∀ z, d'.m.ρ (matActC B z) = d.m.ρ z) ∧
      ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ),
        resGram d' n b = resGram d n fun k => matSubst B (b k)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullRatiosAlgebraic.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ p q : Σ k, ι k, p.1 = q.1 → IsAlgebraic (pullField y L) (y p / y q)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory
open scoped ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def resCGram (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun k l => ∫ y, pairVal d.m n (b k) (b l) (resPt d y) ∂d.dV


open Classical in
def resCChi (d : HSMDatum D Ω κ) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 then
    -(1 / 2) * Real.log (resCGram d n h.choose.2).det.re
  else 0

def resPot (d : HSMDatum D Ω κ) (m : ConeMetric ℂ (Ix κ)) : LocPot d.R.X where
  U := d.R.U
  isOpen_U := d.R.isOpen_U
  mem_U := d.R.mem_U
  φ x y := Real.log (m.ρ (d.R.lift x y))

def resMetricInt (d : HSMDatum D Ω κ) (m₁ : ConeMetric ℂ (Ix κ)) : ℝ :=
  ∫ t in (0 : ℝ)..1, mInt d.R.A (fun _ => resPot d (interp d.m m₁ t)) fun y => logRatio d.m m₁ (resPt d y)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
