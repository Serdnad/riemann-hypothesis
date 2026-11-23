module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.AssemblyPartial
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Vertical

noncomputable section

namespace SecFiniteUnit

theorem prod_natDegree_coeff {R ι : Type*} [CommSemiring R] (s : Finset ι) (f : ι → Polynomial R)
    (D : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ D i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, D i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, D i) = ∏ i ∈ s, (f i).coeff (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha' := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨Polynomial.natDegree_mul_le_of_le ha' h1,
      by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le ha' h1, h2]⟩

variable {k R : Type} [Field k] [CommRing R] [Algebra k R] {n e : ℕ}

def lineSub (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) : Polynomial R :=
  Fin.cases (motive := fun _ => Polynomial R)
    (Polynomial.C (y (.inr ij.2)) * Polynomial.X - if ij.2 = m then 1 else 0)
    (fun i => Polynomial.C (y (.inl (i, ij.2)))) ij.1

def lineTop (y : Par e n → R) (ij : Fin (e + 1) × Fin n) : R :=
  Fin.cases (motive := fun _ => R) (y (.inr ij.2)) (fun i => y (.inl (i, ij.2))) ij.1

theorem lineSub_natDegree_le (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineSub y m ij).natDegree ≤ groupWeight (e + 1) n ij 0 := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    simp only [lineSub, Fin.cases_zero, groupWeight, Pi.single_eq_same]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
    · split_ifs <;> simp
  | succ i => simp [lineSub]

theorem lineSub_coeff (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineSub y m ij).coeff (groupWeight (e + 1) n ij 0) = lineTop y ij := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    simp only [lineSub, lineTop, Fin.cases_zero, groupWeight, Pi.single_eq_same]
    split_ifs <;> simp [Polynomial.coeff_one]
  | succ i => simp [lineSub, lineTop, groupWeight, Fin.succ_ne_zero]

theorem weight_sum {δ : ℕ} {g : MvPolynomial (Fin (e + 1) × Fin n) k} (hg : IsMultiHomog δ g)
    {d : Fin (e + 1) × Fin n →₀ ℕ} (hd : AddMonoidAlgebra.coeff g d ≠ 0) :
    ∑ ij, d ij * groupWeight (e + 1) n ij 0 = δ := by
  have h := congrFun (hg hd) 0
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simpa [Finset.sum_apply, smul_eq_mul] using h

theorem lineSub_aeval {δ : ℕ} {g : MvPolynomial (Fin (e + 1) × Fin n) k} (hg : IsMultiHomog δ g)
    (y : Par e n → R) (m : Fin n) :
    (aeval (lineSub y m) g).natDegree ≤ δ ∧
      (aeval (lineSub y m) g).coeff δ =
        eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y) := by
  have hprod : ∀ d ∈ g.support, (∏ ij, lineSub y m ij ^ d ij).natDegree ≤ δ ∧
      (∏ ij, lineSub y m ij ^ d ij).coeff δ = ∏ ij, lineTop y ij ^ d ij := by
    intro d hd
    have h := prod_natDegree_coeff Finset.univ (fun ij => lineSub y m ij ^ d ij)
      (fun ij => d ij * groupWeight (e + 1) n ij 0)
      (fun ij _ => Polynomial.natDegree_pow_le_of_le _ (lineSub_natDegree_le y m ij))
    rw [weight_sum hg (mem_support_iff.mp hd)] at h
    refine ⟨h.1, h.2.trans (Finset.prod_congr rfl fun ij _ => ?_)⟩
    rw [Polynomial.coeff_pow_of_natDegree_le (lineSub_natDegree_le y m ij), lineSub_coeff]
  rw [aeval_def, eval₂_eq']
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd =>
    (Polynomial.natDegree_C_mul_le _ _).trans (hprod d hd).1, ?_⟩
  have hspec : eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y) = aeval (lineTop y) g := by
    rw [specRest, eval₂_comp_left, aeval_def]
    congr 1
    · ext a; simp
    · funext ⟨i, j⟩
      induction i using Fin.cases with
      | zero => simp [lineTop]
      | succ i => simp [lineTop]
  rw [hspec, aeval_def, eval₂_eq', Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C_mul, (hprod d hd).2]

theorem coord_integral {δ : ℕ} (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → R)
    (hg : IsChowForm Q (e + 1) g) (hδ : IsMultiHomog δ g)
    (hu : IsUnit (eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y))) (m : Fin n) :
    IsIntegral R (secCoord (Q.map (MvPolynomial.map (algebraMap k R))) y m) := by
  set Q' := Q.map (MvPolynomial.map (algebraMap k R))
  set x := secCoord Q' y with hx
  have hC : ∀ a : R, Ideal.Quotient.mk (secIdeal Q' y) (C a) = algebraMap R (SecAlg Q' y) a :=
    fun a => rfl

  have hmk : ∀ q : MvPolynomial (Fin n) k,
      aeval x q = Ideal.Quotient.mk (secIdeal Q' y) (MvPolynomial.map (algebraMap k R) q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => rw [aeval_C, map_C, hC, ← IsScalarTower.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, map_X]; rfl
  have hQ : ∀ q ∈ Q, aeval x q = 0 := fun q hq => by
    rw [hmk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))
  have ht : ∑ j, algebraMap R (SecAlg Q' y) (y (.inr j)) * x j = 1 := by
    have h : chartForm y - 1 ∈ secIdeal Q' y :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← Ideal.Quotient.eq] at h

    simpa [chartForm, linForm, map_sum, hC, hx, secCoord] using h
  have hl : ∀ i, ∑ j, algebraMap R (SecAlg Q' y) (y (.inl (i, j))) * x j = 0 := fun i => by
    have h : secForm y i ∈ secIdeal Q' y :=
      Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h

    simpa [secForm, linForm, map_sum, hC, hx, secCoord] using h

  set φ : MvPolynomial (Fin n ⊕ (Fin (e + 1) × Fin n)) k →ₐ[k] SecAlg Q' y :=
    aeval (Sum.elim x fun ij => Polynomial.aeval (x m) (lineSub y m ij)) with hφ
  have hker : ∀ p ∈ Vertical.incIdeal Q (e + 1), φ p = 0 := by
    intro p hp
    suffices Vertical.incIdeal Q (e + 1) ≤ RingHom.ker φ.toRingHom from this hp
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      simp [hφ, aeval_rename, hQ q hq]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      induction i using Fin.cases with
      | zero =>
        have h0 : ∀ j, Polynomial.aeval (x m) (lineSub y m (0, j)) =
            algebraMap R (SecAlg Q' y) (y (.inr j)) * x m - if j = m then 1 else 0 := by
          intro j
          split_ifs with hj <;> simp [lineSub, hj]

        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, hφ, aeval_X,
        Sum.elim_inr, Sum.elim_inl, h0, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [sub_eq_zero]
        conv_rhs => rw [← mul_one (x m), ← ht, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      | succ i =>
        simpa [hφ, lineSub] using hl i
  obtain ⟨M, hM⟩ := IncidenceNull.full k n (e + 1) Q g hg
  set P : Polynomial R := aeval (lineSub y m) g with hP
  have hG : φ (rename Sum.inr g) = Polynomial.aeval (x m) P := by
    rw [hφ, aeval_rename, Sum.elim_comp_inr, hP]
    have := DFunLike.congr_fun
      (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (x m)).restrictScalars k)) g
    simpa using this.symm
  have hnil : IsNilpotent (Polynomial.aeval (x m) P) := by
    rw [← hG, ← mul_one (φ _), ← ht, Finset.mul_sum]
    refine isNilpotent_sum fun j _ => ?_
    have hj : IsNilpotent (φ (rename Sum.inr g) * x j) := by
      refine ⟨M, ?_⟩
      have h0 := hker _ (hM j)
      rwa [map_pow, map_mul, show φ (X (Sum.inl j)) = x j by simp [hφ]] at h0
    rw [mul_left_comm]
    exact (Commute.all _ _).isNilpotent_mul_left hj

  obtain ⟨N, hN⟩ := hnil
  obtain ⟨hdeg, hcoeff⟩ := lineSub_aeval hδ y m
  obtain ⟨u, hu'⟩ := hu
  have hmonic : (Polynomial.C ((u⁻¹ : Rˣ) : R) * P).Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one δ
      ((Polynomial.natDegree_C_mul_le _ _).trans hdeg)
      (by rw [Polynomial.coeff_C_mul, hcoeff, ← hu', Units.inv_mul])
  refine ⟨(Polynomial.C ((u⁻¹ : Rˣ) : R) * P) ^ N, hmonic.pow N, ?_⟩
  rw [← Polynomial.aeval_def, map_pow, map_mul, mul_pow, hN, mul_zero]

end SecFiniteUnit

theorem SecFiniteUnit.proof : SecFiniteUnit.Statement := by
  intro k R _ _ _ n e δ Q g y hg hδ hu
  set Q' := Q.map (MvPolynomial.map (algebraMap k R))
  have htop : Algebra.adjoin R (Set.range (secCoord Q' y)) = ⊤ := by
    have h : Set.range (secCoord Q' y) = Ideal.Quotient.mkₐ R (secIdeal Q' y) '' Set.range X := by
      rw [← Set.range_comp]; rfl
    rw [h, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective R _)
  have hfg := fg_adjoin_of_finite (Set.finite_range (secCoord Q' y))
    (by rintro _ ⟨m, rfl⟩; exact SecFiniteUnit.coord_integral Q g y hg hδ hu m)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

theorem det_starProjection_compress {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →L[ℂ] F) (T : Submodule ℂ E) :
    (T.starProjection ∘L A.adjoint ∘L A ∘L T.starProjection + (1 - T.starProjection)).det =
      (LinearMap.adjoint ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) ∘ₗ ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype)).det := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : E →L[ℂ] E,
      Q = T.starProjection ∘L A.adjoint ∘L A ∘L T.starProjection + (1 - T.starProjection) := ⟨_, rfl⟩
  rw [← hQdef]
  have hQx : ∀ x : E, Q x =
      T.starProjection (A.adjoint (A (T.starProjection x))) + (x - T.starProjection x) := by
    intro x; subst hQdef; simp
  have hQT : T ≤ T.comap (Q : E →ₗ[ℂ] E) := by
    intro x hx
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hQx,
      Submodule.starProjection_eq_self_iff.mpr hx, sub_self, add_zero]
    exact T.starProjection_apply_mem _
  have hres : (Q : E →ₗ[ℂ] E).restrict hQT =
      LinearMap.adjoint ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) ∘ₗ ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) := by
    ext1 x
    apply ext_inner_right ℂ
    intro z
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, Submodule.coe_inner,
      LinearMap.coe_restrict_apply, ContinuousLinearMap.coe_coe, hQx,
      Submodule.starProjection_eq_self_iff.mpr x.2, sub_self, add_zero,
      Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr z.2,
      ContinuousLinearMap.adjoint_inner_left]
    rfl
  have hquot : T.mapQ T (Q : E →ₗ[ℂ] E) hQT = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_comp, ContinuousLinearMap.coe_coe]
    rw [Submodule.Quotient.eq, hQx]
    have h : T.starProjection (A.adjoint (A (T.starProjection x))) + (x - T.starProjection x) - x =
        T.starProjection (A.adjoint (A (T.starProjection x))) - T.starProjection x := by abel
    rw [h]
    exact T.sub_mem (T.starProjection_apply_mem _) (T.starProjection_apply_mem _)
  rw [ContinuousLinearMap.det, LinearMap.det_eq_det_mul_det T _ hQT, hres, hquot, LinearMap.det_id,
    mul_one]

theorem TangentJacCompress.proof : TangentJacCompress.Statement := by
  intro n m π T
  unfold tangentJac
  have h := LinearMap.normDet_sq (𝕜 := ℂ) (U := T) (V := EuclideanSpace ℂ (Fin m)) ((linProjₗ π).comp T.subtype)
  exact h.trans (det_starProjection_compress (LinearMap.toContinuousLinearMap (linProjₗ π)) T).symm

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

theorem linProj_smul_left {m n : ℕ} (π : Fin m → Fin n → ℂ) (c : ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    linProj π (c • y) = c • linProj π y :=
  (linProjₗ π).map_smul c y

theorem tangentGauss_indicator_eq {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) :
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) =
      if |r| * ‖linProj π (firstCoordVec n)‖ < 1 then (1 : ℝ≥0∞) else 0 := by
  simp only [Set.indicator, Metric.mem_ball, dist_zero_right, linProj_smul_left, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, Pi.one_apply]

theorem tangentGaussProfile_abs (n m : ℕ) (r : ℝ) :
    tangentGaussProfile n m |r| = tangentGaussProfile n m r := by
  unfold tangentGaussProfile
  simp only [tangentGauss_indicator_eq, abs_abs]

theorem tangentGaussProfile_antitoneOn (n m : ℕ) :
    AntitoneOn (tangentGaussProfile n m) (Set.Ici 0) := by
  intro r hr s hs hrs
  unfold tangentGaussProfile
  refine lintegral_mono fun π => ?_
  simp only [tangentGauss_indicator_eq, abs_of_nonneg (Set.mem_Ici.1 hr),
    abs_of_nonneg (Set.mem_Ici.1 hs)]
  have key : s * ‖linProj π (firstCoordVec n)‖ < 1 → r * ‖linProj π (firstCoordVec n)‖ < 1 :=
    fun h => lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrs (norm_nonneg _)) h
  gcongr
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (key h1) h2
  · exact zero_le_one
  · exact le_rfl

theorem measurable_tangentGaussProfile (n m : ℕ) : Measurable (tangentGaussProfile n m) := by
  have hψ : Antitone fun t : ℝ => tangentGaussProfile n m (max t 0) := fun a b hab =>
    tangentGaussProfile_antitoneOn n m (Set.mem_Ici.2 (le_max_right a 0))
      (Set.mem_Ici.2 (le_max_right b 0)) (max_le_max hab le_rfl)
  have h : tangentGaussProfile n m = fun r => tangentGaussProfile n m (max |r| 0) := by
    funext r
    rw [max_eq_left (abs_nonneg r), tangentGaussProfile_abs]
  rw [h]
  exact hψ.measurable.comp measurable_abs

theorem pow_two_mul_sub_one_le {r : ℝ} (hr : 0 ≤ r) (m : ℕ) : r ^ (2 * m - 1) ≤ (1 + r ^ 2) ^ m := by
  rcases le_total r 1 with h | h
  · exact (pow_le_one₀ hr h).trans (one_le_pow₀ (by nlinarith))
  · calc r ^ (2 * m - 1) ≤ r ^ (2 * m) := pow_le_pow_right₀ h (Nat.sub_le _ _)
      _ = (r ^ 2) ^ m := by rw [pow_mul]
      _ ≤ (1 + r ^ 2) ^ m := pow_le_pow_left₀ (sq_nonneg r) (by linarith) m

theorem TangentGaussMoment.proof (hA : LeadPlaneJac.Statement) (hB : LeadBlockGaussTail.Statement) :
    TangentGaussMoment.Statement := by
  intro n m hm hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hk : ∀ r : ℝ, tangentGaussProfile (m + k) m r = ∫⁻ π : Fin m → Fin (m + k) → ℂ, matGauss π *
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
      ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) := by
    intro r
    unfold tangentGaussProfile
    simp only [hA m k]
  have hpos : ∀ r : ℝ, 0 < tangentGaussProfile (m + k) m r := by
    intro r
    rw [hk r]
    have hcont : Continuous fun π : Fin m → Fin (m + k) → ℂ =>
        linProj π ((r : ℂ) • firstCoordVec (m + k)) := by
      unfold linProj
      exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)
    have hdet : Continuous fun π : Fin m → Fin (m + k) → ℂ => (coordPlaneBlock π).det :=
      Continuous.matrix_det (by unfold coordPlaneBlock; fun_prop)
    have hmeas : Measurable fun π : Fin m → Fin (m + k) → ℂ => matGauss π *
        (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
          (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
        ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) ?_
      · unfold matGauss
        exact ENNReal.measurable_ofReal.comp (by fun_prop)
      · exact (measurable_one.indicator Metric.isOpen_ball.measurableSet).comp hcont.measurable
      · exact ENNReal.measurable_ofReal.comp ((continuous_norm.comp hdet).pow 2).measurable
    rw [lintegral_pos_iff_support hmeas]
    set U := {π : Fin m → Fin (m + k) → ℂ |
      linProj π ((r : ℂ) • firstCoordVec (m + k)) ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1}
    have hU : IsOpen U := Metric.isOpen_ball.preimage hcont
    have hU0 : (0 : Fin m → Fin (m + k) → ℂ) ∈ U := by
      have h0 : linProj (0 : Fin m → Fin (m + k) → ℂ) ((r : ℂ) • firstCoordVec (m + k)) = 0 := by
        ext i
        simp [linProj]
      simp only [U, Set.mem_ofPred_eq, h0, Metric.mem_ball, dist_self, zero_lt_one]
    have : (volume : Measure (Fin m → Fin (m + k) → ℂ)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    refine (hU.measure_pos volume ⟨0, hU0⟩).trans_le (measure_mono_ae ?_)
    filter_upwards [ae_coordPlaneBlock_det_ne_zero m k] with π hπdet hπU
    show matGauss π * _ * _ ≠ 0
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    · change linProj π ((r : ℂ) • firstCoordVec (m + k)) ∈ Metric.ball 0 1 at hπU
      rw [Set.indicator_of_mem hπU]
      exact one_ne_zero
    · exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨C, hC⟩ := hB m k hm
  have hmeasM : Measurable fun r : ℝ =>
      tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) :=
    (measurable_tangentGaussProfile _ _).mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  refine ⟨measurable_tangentGaussProfile _ _, tangentGaussProfile_antitoneOn _ _, hpos, ?_, ?_⟩
  · rw [setLIntegral_pos_iff hmeasM]
    have hsub : Set.Ioi (0 : ℝ) ⊆
        Function.support (fun r : ℝ =>
          tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))) ∩
          Set.Ioi 0 := by
      intro r hr
      refine ⟨?_, hr⟩
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      exact mul_ne_zero (hpos r).ne' (ENNReal.ofReal_pos.2 (by
        have := Set.mem_Ioi.1 hr
        positivity)).ne'
    exact lt_of_lt_of_le (by simp) (measure_mono hsub)
  · have hle : ∀ r ∈ Set.Ioi (0 : ℝ),
        tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) ≤
          ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := by
      intro r hr
      have hr0 : 0 ≤ r := le_of_lt hr
      have h1 := pow_two_mul_sub_one_le hr0 m
      have hx : 0 < 1 + r ^ 2 := by positivity
      have hC0 : 0 ≤ max C 0 := le_max_right _ _
      calc tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))
          ≤ ENNReal.ofReal (C / (1 + r ^ 2) ^ (m + 1)) * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) := by
            rw [hk r]
            gcongr
            exact hC r
        _ = ENNReal.ofReal (C / (1 + r ^ 2) ^ (m + 1) * (2 * m * r ^ (2 * m - 1))) :=
            (ENNReal.ofReal_mul' (by positivity)).symm
        _ ≤ ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc C / (1 + r ^ 2) ^ (m + 1) * (2 * m * r ^ (2 * m - 1))
                ≤ max C 0 / (1 + r ^ 2) ^ (m + 1) * (2 * m * (1 + r ^ 2) ^ m) := by
                  gcongr
                  exact le_max_left _ _
              _ = 2 * m * max C 0 * (1 + r ^ 2)⁻¹ := by
                  field_simp
                  ring
    calc ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))
        ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) :=
          setLIntegral_mono' measurableSet_Ioi hle
      _ ≤ ∫⁻ r, ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := setLIntegral_le_lintegral _ _
      _ < ⊤ := (integrable_inv_one_add_sq.const_mul _).lintegral_lt_top

end

end GroundTheory.Heights₂.Heights
end
