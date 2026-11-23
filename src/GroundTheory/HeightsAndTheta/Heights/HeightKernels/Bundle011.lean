module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle004
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import GroundTheory.GlobalFields.TateThesis.LatticePoisson
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real MeasureTheory

noncomputable section

namespace KThetaCharIntegral

theorem integral_Icc_exp (n : ℤ) :
    ∫ t in Set.Icc (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * ((n : ℂ) * (t : ℂ))) =
      if n = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hn
  · subst hn; simp
  · have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have h1 : ∀ t : ℝ, 2 * π * Complex.I * ((n : ℂ) * (t : ℂ)) = 2 * π * Complex.I * n * t := by
      intro t; ring
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = n * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h2]
    simp

theorem torusChar_eq_prod {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = ∏ i, Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (u i : ℂ))) := by
  unfold torusChar
  rw [Finset.mul_sum, Complex.exp_sum]

end KThetaCharIntegral

theorem ThetaCharIntegral.proof : ThetaCharIntegral.Statement := by
  intro g m
  have hset : Set.Icc (0 : Fin g → ℝ) 1 = Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1 := by
    rw [← Set.pi_univ_Icc]; rfl
  rw [hset, volume_pi, Measure.restrict_pi_pi]
  simp_rw [KThetaCharIntegral.torusChar_eq_prod]
  rw [integral_fintype_prod_eq_prod
    (f := fun i (t : ℝ) => Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (t : ℂ))))]
  simp_rw [KThetaCharIntegral.integral_Icc_exp]
  by_cases hm : m = 0
  · subst hm; simp
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      exact hm (funext h)
    rw [if_neg hm]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real MeasureTheory
open scoped FourierTransform

namespace PGaussFourierSelf

lemma ofReal_gauss {V : Type*} [NormedAddCommGroup V] (x : V) :
    ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) = Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

end PGaussFourierSelf

theorem GaussFourierSelf.proof : GaussFourierSelf.Statement := by
  intro g w
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hfun : (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) =
      fun x => Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    funext x
    exact PGaussFourierSelf.ofReal_gauss x
  rw [hfun, fourier_gaussian_innerProductSpace hb w, PGaussFourierSelf.ofReal_gauss w]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [div_self hpi, Complex.one_cpow, one_mul]
  congr 1
  field_simp

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace PGaussPoissonBound

theorem norm_toLp_sq {g : ℕ} (v : Fin g → ℝ) : ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

end PGaussPoissonBound


open PGaussPoissonBound in
theorem GaussPoissonBound.proof (hL : GaussLatticeIsLattice.Statement)
    (hV : GaussLatticeCovolume.Statement) (hK : GaussLatticeCoords.Statement)
    (hF : GaussFourierSelf.Statement) : GaussPoissonBound.Statement := by
  intro g B hB a
  obtain ⟨hdisc, hlat⟩ := hL g B hB
  have : DiscreteTopology (gaussLattice B) := hdisc
  have : IsZLattice ℝ (gaussLattice B) := hlat
  obtain ⟨hmem, hsurj, hinj⟩ := hK g B hB
  let E := EuclideanSpace ℝ (Fin g)
  let L := gaussLattice B
  let φ : (Fin g → ℤ) ≃ L := Equiv.ofBijective
    (fun k => ⟨WithLp.toLp 2 (B *ᵥ intVec k), hmem k⟩)
    ⟨fun k k' h => hinj (by
        have := congrArg (fun x : L => WithLp.ofLp (x : E)) h
        simpa using this),
      fun x => by
        obtain ⟨k, hk⟩ := hsurj x x.2
        exact ⟨k, Subtype.ext hk.symm⟩⟩
  let G := GroundTheory.Global.gaussianSchwartz E
  let a' : E := WithLp.toLp 2 (B *ᵥ a)
  let f : (Fin g → ℤ) → ℝ := fun k =>
    Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a))))
  have hG : ∀ k, G ((φ k : E) + a') = ((f k : ℝ) : ℂ) := fun k => by
    have h1 : ((φ k : E) + a') = WithLp.toLp 2 (B *ᵥ (intVec k + a)) := by
      rw [Matrix.mulVec_add]; rfl
    rw [h1, GroundTheory.Global.gaussianSchwartz_apply, norm_toLp_sq]
  have hnG : ∀ k, ‖G ((φ k : E) + a')‖ = f k := fun k => by
    rw [hG, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hGfun : (G : E → ℂ) = fun x => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) :=
    funext fun x => GroundTheory.Global.gaussianSchwartz_apply x
  have hFG : ∀ μ : E, 𝓕 (G : E → ℂ) μ = ((Real.exp (-π * ‖μ‖ ^ 2) : ℝ) : ℂ) := fun μ => by
    rw [hGfun]; exact hF g μ
  have hnD : ∀ μ : GroundTheory.Global.dualLattice L,
      ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ = Real.exp (-π * ‖(μ : E)‖ ^ 2) := fun μ => by
    rw [norm_mul, Circle.norm_coe, mul_one, hFG, Complex.norm_of_nonneg (Real.exp_pos _).le]

  have hsumf : Summable f := by
    have h := (φ.summable_iff (f := fun ℓ : L => ‖G (ℓ + a')‖)).2
      (GroundTheory.Global.lattice_summable_norm L G a')
    exact h.congr fun k => hnG k

  have hsumD := GroundTheory.Global.dualLattice_summable_norm L G a'
  have hsumE : Summable fun μ : GroundTheory.Global.dualLattice L => Real.exp (-π * ‖(μ : E)‖ ^ 2) :=
    hsumD.congr hnD
  refine ⟨hsumf, hsumE, ?_⟩

  have hP := GroundTheory.Global.lattice_poisson_summation L G a'
  have hlhs : ∑' ℓ : L, G (ℓ + a') = ((∑' k, f k : ℝ) : ℂ) := by
    rw [← φ.tsum_eq (fun ℓ : L => G (ℓ + a')), Complex.ofReal_tsum]
    exact tsum_congr fun k => hG k
  rw [hlhs] at hP
  have hcov : ZLattice.covolume L = |B.det| := hV g B hB
  have hcpos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  calc ∑' k, f k = ‖((∑' k, f k : ℝ) : ℂ)‖ :=
        (Complex.norm_of_nonneg (tsum_nonneg fun k => (Real.exp_pos _).le)).symm
    _ = (ZLattice.covolume L)⁻¹ *
          ‖∑' μ : GroundTheory.Global.dualLattice L, 𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ := by
        rw [hP, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
    _ ≤ (ZLattice.covolume L)⁻¹ *
          ∑' μ : GroundTheory.Global.dualLattice L, ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsumD) (inv_pos.2 hcpos).le
    _ = |B.det|⁻¹ * ∑' μ : GroundTheory.Global.dualLattice (gaussLattice B),
          Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2) := by
        rw [hcov]; exact congrArg _ (tsum_congr hnD)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussSqrt

theorem eq_eigenvectors_mul_diagonal {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hH : Y.IsHermitian) :
    Y = (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) * diagonal hH.eigenvalues *
      (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ)ᵀ := by
  conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rfl

end PGaussSqrt

theorem GaussSqrt.proof : GaussSqrt.Statement := by
  intro g Y hY
  classical
  set hH := hY.isHermitian
  set U : Matrix (Fin g) (Fin g) ℝ := (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) with hUdef
  refine ⟨diagonal (fun i => √(hH.eigenvalues i)) * Uᵀ, ?_⟩
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => (hY.eigenvalues_pos i).le
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
  calc U * diagonal (fun i => √(hH.eigenvalues i)) * (diagonal (fun i => √(hH.eigenvalues i)) * Uᵀ)
      = U * (diagonal (fun i => √(hH.eigenvalues i)) * diagonal (fun i => √(hH.eigenvalues i)))
          * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = U * diagonal hH.eigenvalues * Uᵀ := by
      have hsq : (fun i => √(hH.eigenvalues i) * √(hH.eigenvalues i)) = hH.eigenvalues :=
        funext fun i => Real.mul_self_sqrt (hnn i)
      rw [diagonal_mul_diagonal, hsq]
    _ = Y := (PGaussSqrt.eq_eigenvectors_mul_diagonal hH).symm

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric

namespace PGaussPacking

theorem pairwiseDisjoint_balls {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) {δ : ℝ}
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) :
    (s : Set (EuclideanSpace ℝ (Fin n))).PairwiseDisjoint (fun x => ball x (δ / 2)) := by
  intro x hx y hy hxy
  apply ball_disjoint_ball
  rw [dist_eq_norm]
  linarith [hsep x hx y hy hxy]

theorem biUnion_balls_subset {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) {δ r : ℝ}
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) :
    (⋃ x ∈ s, ball x (δ / 2)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) (r + δ / 2) := by
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨x, hx, hz⟩ := hz
  rw [mem_ball, dist_eq_norm] at hz ⊢
  rw [sub_zero]
  calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
    _ < δ / 2 + r := by linarith [hs x hx]
    _ = r + δ / 2 := by ring

end PGaussPacking


open PGaussPacking in
theorem GaussPacking.proof : GaussPacking.Statement := by
  intro n s δ r hδ hr hsep hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : s.card ≤ 1 := Finset.card_le_one.2 (fun a _ b _ => Subsingleton.elim a b)
    have h1' : (s.card : ℝ) ≤ 1 := by exact_mod_cast h1
    simpa using h1'
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  have hδ2 : 0 < δ / 2 := by positivity
  have hR : 0 ≤ r + δ / 2 := by positivity
  have hmeas : ∑ x ∈ s, (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x (δ / 2)) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) (r + δ / 2)) := by
    rw [← measure_biUnion_finset (pairwiseDisjoint_balls s hsep) (fun x _ => measurableSet_ball)]
    exact measure_mono (biUnion_balls_subset s hs)
  simp only [Measure.addHaar_ball _ _ hδ2.le, Measure.addHaar_ball _ _ hR,
    finrank_euclideanSpace_fin, Finset.sum_const, nsmul_eq_mul] at hmeas
  have hc0 : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ 0 :=
    (measure_ball_pos _ _ one_pos).ne'
  have hct : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  rw [← mul_assoc] at hmeas
  have h2 := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hmeas
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have hp : 0 < (δ / 2) ^ n := pow_pos hδ2 n
  have key : (1 + 2 * r / δ) ^ n = (r + δ / 2) ^ n / (δ / 2) ^ n := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  rw [key, le_div_iff₀ hp]
  exact h2

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexDet

theorem span_basis_isLattice {V : Type} [AddCommGroup V] [Module ℚ V] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℚ V) : Submodule.IsFullLattice ℚ (Submodule.span ℤ (Set.range b)) := by
  have : Submodule.IsLattice ℚ (Submodule.span ℤ (Set.range b)) :=
    Submodule.IsLattice.of_fg ℚ (Submodule.fg_span (Set.finite_range b))
  refine { span_eq_top := ?_ }
  rw [Submodule.span_span_of_tower ℤ, b.span_eq]

end KLinesGenIndexDet


open KLinesGenIndexDet in
theorem LinesGenIndexDet.proof (h1 : LinesLatticeBasis.Statement) : LinesGenIndexDet.Statement := by
  intro V _ _ _ ι _ _ bA bB A B hA hB
  set MA := Submodule.span ℤ (Set.range bA)
  set MB := Submodule.span ℤ (Set.range bB)
  have : Submodule.IsFullLattice ℚ MA := span_basis_isLattice bA
  have : Submodule.IsFullLattice ℚ MB := span_basis_isLattice bB
  obtain ⟨bE, hE⟩ := h1 V ι (Module.finrank_eq_card_basis bA).symm (MA ⊓ MB)
    (Submodule.IsFullLattice.inf ℚ MA MB)
  have hAB : A ⊓ B = AddSubgroup.closure (Set.range bE) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, ← hE, hA, hB,
      ← Submodule.span_int_eq_addSubgroupClosure, ← Submodule.span_int_eq_addSubgroupClosure]
    rfl
  have hBA : B ⊓ A = AddSubgroup.closure (Set.range bE) := by rw [inf_comm, hAB]
  have e1 : ((B.relIndex A : ℕ) : ℚ) = |bA.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bA hBA hA
  have e2 : ((A.relIndex B : ℕ) : ℚ) = |bB.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bB hAB hB
  have hne : bB.det bE ≠ 0 := (bB.isUnit_det bE).ne_zero
  have key : (B.relIndex A : ℚ) / (A.relIndex B : ℚ) = |bA.det bB| := by
    rw [e1, e2, ← bA.det_mul_det bB bE, abs_mul, mul_div_assoc, div_self (abs_ne_zero.mpr hne),
      mul_one]
  unfold genIndex
  have := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at this
  exact this

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesIsLattice

theorem smul_mem_span_of_mem {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K} (hv : v ∈ M) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  rw [← (integralBasis K).sum_repr t, Finset.sum_smul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_assoc, integralBasis_apply, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (M.smul_mem _ hv))

theorem smul_mem_span {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K}
    (hv : v ∈ Submodule.span ℚ (M : Set (ι → K))) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact smul_mem_span_of_mem M t hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ q hx

def qSpan {K : Type} [Field K] [NumberField K] {ι : Type} (M : Submodule (𝓞 K) (ι → K)) :
    Submodule K (ι → K) where
  carrier := Submodule.span ℚ (M : Set (ι → K))
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  smul_mem' t _ hv := smul_mem_span M t hv

end KLinesIsLattice

theorem LinesIsLattice.proof : LinesIsLattice.Statement := by
  intro K _ _ ι _ M hfg hspan
  letI : Submodule.IsLattice ℚ (M.restrictScalars ℤ) := Submodule.IsLattice.of_fg ℚ hfg
  have htop : Submodule.span ℚ (M : Set (ι → K)) = ⊤ := by
    have hMN : Submodule.span K (M : Set (ι → K)) ≤ KLinesIsLattice.qSpan M :=
      Submodule.span_le.mpr fun v hv => Submodule.subset_span hv
    rw [hspan, top_le_iff] at hMN
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ KLinesIsLattice.qSpan M := hMN ▸ Submodule.mem_top
    exact hv
  letI : Submodule.IsFullLattice ℚ (M.restrictScalars ℤ) := ⟨htop⟩
  exact inferInstance
end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexTrans

theorem toAddSubgroup_span {V : Type} [AddCommGroup V] (s : Set V) :
    (Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s :=
  Submodule.span_int_eq_addSubgroupClosure s

end KLinesGenIndexTrans


open KLinesGenIndexTrans in
theorem LinesGenIndexTrans.proof (h1 : LinesLatticeBasis.Statement)
    (h2 : LinesGenIndexDet.Statement) : LinesGenIndexTrans.Statement := by
  intro V _ _ _ A B C hA hB hC
  classical
  obtain ⟨bA, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) A hA
  obtain ⟨bB, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) B hB
  obtain ⟨bC, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) C hC
  have hAB := h2 V _ bA bB _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  have hBC := h2 V _ bB bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  have hAC := h2 V _ bA bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  refine ⟨?_, ?_⟩
  · rw [hAB]
    have h0 : (bA.det bB : ℚ) ≠ 0 := (bA.isUnit_det bB).ne_zero
    positivity
  · rw [hAB, hBC, hAC, ← abs_mul, ← Rat.cast_mul, Module.Basis.det_mul_det]

end GroundTheory.Heights₂.Heights
end
