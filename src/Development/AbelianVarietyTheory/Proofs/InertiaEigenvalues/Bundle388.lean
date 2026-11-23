module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle366
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle368
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGamGamKTorsion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle377
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle012
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
open MeasureTheory Topology Matrix

namespace GlobalTheory.InvFormBdd

theorem exists_form_of_bounded {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (Matrix.GeneralLinearGroup ι ℂ)) (C : ℝ)
    (hC : ∀ h ∈ H, ∀ i j, ‖(h : Matrix ι ι ℂ) i j‖ ≤ C) :
    ∃ β : (ι → ℂ) →ₗ⋆[ℂ] (ι → ℂ) →ₗ[ℂ] ℂ, (∀ x y, β x y = starRingEnd ℂ (β y x)) ∧
      (∀ x, x ≠ 0 → 0 < (β x x).re) ∧
      ∀ h ∈ H, ∀ x y, β ((h : Matrix ι ι ℂ) *ᵥ x) ((h : Matrix ι ι ℂ) *ᵥ y) = β x y := by
  classical
  let A : Set (Matrix ι ι ℂ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0:ℂ) C
  have hA : IsCompact A := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let S : Set (Matrix.GeneralLinearGroup ι ℂ) :=
    Units.embedProduct (Matrix ι ι ℂ) ⁻¹' (A ×ˢ (MulOpposite.op '' A))
  have hS : IsCompact S := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hA.prod (hA.image MulOpposite.continuous_op))
  have hHS : (H : Set (Matrix.GeneralLinearGroup ι ℂ)) ⊆ S := by
    intro h hh
    refine ⟨fun i _ j _ => ?_, ⟨(h⁻¹ : Matrix.GeneralLinearGroup ι ℂ).val, fun i _ j _ => ?_, rfl⟩⟩
    · simpa using hC h hh i j
    · simpa using hC _ (H.inv_mem hh) i j
  let K := H.topologicalClosure
  have hK : IsCompact (K : Set (Matrix.GeneralLinearGroup ι ℂ)) :=
    hS.of_isClosed_subset H.isClosed_topologicalClosure (closure_minimal hHS hS.isClosed)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haar
  let N : K → Matrix ι ι ℂ := fun k => ((k⁻¹ : K) : Matrix.GeneralLinearGroup ι ℂ).val
  have hN : Continuous N := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  let φ : K → (ι → ℂ) → (ι → ℂ) → ℂ := fun k x y => star (N k *ᵥ x) ⬝ᵥ (N k *ᵥ y)
  have hφc : ∀ x y, Continuous fun k => φ k x y := by
    intro x y
    have h1 : Continuous fun k => N k *ᵥ x := hN.matrix_mulVec continuous_const
    have h2 : Continuous fun k => N k *ᵥ y := hN.matrix_mulVec continuous_const
    exact (continuous_star.comp h1).dotProduct h2
  have hφi : ∀ x y, Integrable (fun k => φ k x y) μ := fun x y =>
    (hφc x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let β : (ι → ℂ) →ₗ⋆[ℂ] (ι → ℂ) →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y => ∫ k, φ k x y ∂μ)
    (fun x x' y => by
      rw [← integral_add (hφi x y) (hφi x' y)]
      congr 1; funext k; simp [φ, Matrix.mulVec_add, add_dotProduct])
    (fun c x y => by
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1; funext k; simp [φ, Matrix.mulVec_smul, smul_dotProduct])
    (fun x y y' => by
      rw [← integral_add (hφi x y) (hφi x y')]
      congr 1; funext k; simp [φ, Matrix.mulVec_add, dotProduct_add])
    (fun c x y => by
      rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
      congr 1; funext k; simp [φ, Matrix.mulVec_smul, dotProduct_smul])
  refine ⟨β, fun x y => ?_, fun x hx => ?_, fun h hh x y => ?_⟩
  · show ∫ k, φ k x y ∂μ = starRingEnd ℂ (∫ k, φ k y x ∂μ)
    rw [← integral_conj]
    congr 1; funext k

    simp [φ, dotProduct, map_sum, mul_comm]
  · show 0 < (∫ k, φ k x x ∂μ).re
    have e := integral_re (hφi x x)
    simp only [RCLike.re_to_complex] at e
    rw [← e]
    have hre : ∀ k, (φ k x x).re = ∑ i, ‖(N k *ᵥ x) i‖ ^ 2 := by
      intro k
      simp only [φ, dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
      norm_cast
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp (hφc x x)) (HasCompactSupport.of_compactSpace _) ?_ ?_
    · intro k
      simp only [Pi.zero_apply, Function.comp_apply, hre]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    · simp only [Function.comp_apply, hre]
      have hN1 : N 1 = 1 := by simp [N]
      rw [hN1, Matrix.one_mulVec]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      refine ne_of_gt (Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩)
      have : x i ≠ 0 := hi
      positivity
  · show ∫ k, φ k ((h : Matrix ι ι ℂ) *ᵥ x) ((h : Matrix ι ι ℂ) *ᵥ y) ∂μ = ∫ k, φ k x y ∂μ
    have hhK : h ∈ K := H.le_topologicalClosure hh
    rw [← integral_mul_left_eq_self (μ := μ) (fun k => φ k x y) (⟨h, hhK⟩⁻¹ : K)]
    congr 1; funext k
    simp only [φ, N, _root_.mul_inv_rev, inv_inv, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]

end GlobalTheory.InvFormBdd

noncomputable section
open MeasureTheory Topology Matrix

namespace GlobalTheory.InvFormBdd

theorem norm_eval_le {σ : Type} (P : MvPolynomial σ ℂ) (v : σ → ℂ) (hv : ∀ s, ‖v s‖ ≤ 1) :
    ‖MvPolynomial.eval v P‖ ≤ ∑ d ∈ P.support, ‖AddMonoidAlgebra.coeff P d‖ := by
  first
  | exact @_root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff
  | exact _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff
  | (apply _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff ..)

theorem norm_emb_le_one {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) L) (hg : g ∈ GQ0 L n) (τ : L →+* ℂ) (i j : Fin n) :
    ‖τ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ≤ 1 := by
  have h1 : (g : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) (g : Matrix (Fin n) (Fin n) L) = 1 := hg
  have h2 := congrFun (congrFun h1 i) i
  simp only [Matrix.mul_apply, conjT, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] at h2
  have h3 := congrArg τ h2

  simp only [map_sum, map_mul, map_one] at h3
  have h4 : ∑ k, (‖τ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 : ℝ) = 1 := by
    have : ∑ k, ((‖τ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h3]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [RingHom.coe_coe, IsCMField.complexEmbedding_complexConj, Complex.mul_conj']
      push_cast; rfl
    exact_mod_cast this
  have h5 : ‖τ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ^ 2 ≤ 1 :=
    h4 ▸ Finset.single_le_sum (f := fun k => ‖τ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [norm_nonneg (τ ((g : Matrix (Fin n) (Fin n) L) i j))]

end GlobalTheory.InvFormBdd


open GlobalTheory.InvFormBdd in
theorem GlobalTheory.InvFormBdd.exists_isInvForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n),
    ∃ β, IsInvForm a β := by
  intro L _ _ _ n a
  classical
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  let f : GQ L n →* Matrix.GeneralLinearGroup ι ℂ :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp a.ρ.asGroupHom
  have hf : ∀ γ, ((f γ : Matrix.GeneralLinearGroup ι ℂ) : Matrix ι ι ℂ) = LinearMap.toMatrix b b (a.ρ γ) := by
    intro γ; ext i j; simp [f, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply, Representation.asGroupHom_apply]
  let C : ℝ := ∑ i, ∑ j, ∑ d ∈ (P i j).support, ‖AddMonoidAlgebra.coeff (P i j) d‖
  have hC : ∀ h ∈ f.range, ∀ i j, ‖(h : Matrix ι ι ℂ) i j‖ ≤ C := by
    rintro _ ⟨γ, rfl⟩ i j
    have hγ := γ.2
    unfold GQ at hγ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
    obtain ⟨g, hg, e⟩ := hγ
    have e' : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (g : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      rw [← e]; rfl
    rw [hf, hP γ g e']
    refine (norm_eval_le _ _ fun p => norm_emb_le_one g hg _ _ _).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ d ∈ (P i j).support, ‖AddMonoidAlgebra.coeff (P i j) d‖)
      (fun i _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ∑ d ∈ (P i j).support, ‖AddMonoidAlgebra.coeff (P i j) d‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨β₀, h1, h2, h3⟩ := exists_form_of_bounded f.range C hC
  let e : a.W →ₗ[ℂ] (ι → ℂ) := b.equivFun.toLinearMap
  refine ⟨(β₀.comp e).compl₂ e, fun x y => ?_, fun x hx => ?_, fun γ x y => ?_⟩
  · exact h1 _ _
  · refine h2 _ ?_
    simpa [e] using hx
  · show β₀ (e (a.ρ γ x)) (e (a.ρ γ y)) = β₀ (e x) (e y)
    have hv : ∀ z, e (a.ρ γ z) = ((f γ : Matrix.GeneralLinearGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ e z := by
      intro z
      rw [hf]
      exact (LinearMap.toMatrix_mulVec_repr b b (a.ρ γ) z).symm
    rw [hv, hv]
    exact h3 _ ⟨γ, rfl⟩ _ _
end
end
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilKisin_lpow_eisensteinPow_twisted_decomp : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (c : ℕ), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ y' ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ c • D.zeta (D.phi m) ∈ D.MM → ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man ∧ (l : K) ^ c • (E K l e ^ (2 * H) • (E K l e • D.zeta (y' + D.phi m) - D.EN (y' + D.phi m))) = p + ((l : K) ^ (3 * H))⁻¹ • f := by
  first | exact @GlobalTheory.BK.lpow_Epow_twistedMon_decomp | exact GlobalTheory.BK.lpow_Epow_twistedMon_decomp | (intros; apply GlobalTheory.BK.lpow_Epow_twistedMon_decomp <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.exists_mem_tameDescent_class_eq_of_pow_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → η < H → H + η < l → 10 * H + 2 ≤ l → ∀ c : ℕ, ∀ w ∈ D.Zl, (l : K) ^ c • D.Lc w ∈ D.Z → ∃ y ∈ D.Y', D.Lc (D.cls y) = (l : K) ^ (c + η + (N + 1) * η) • D.Lc w := by
  first | exact @GlobalTheory.LcImage.exists_mem_Y'_Lc_cls_eq | exact GlobalTheory.LcImage.exists_mem_Y'_Lc_cls_eq | (intros; apply GlobalTheory.LcImage.exists_mem_Y'_Lc_cls_eq <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilKisinDescent_pow_smul_monodromy_add_phi_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ r : ℕ, 1 ≤ r → (∀ τ, ∀ c ∈ D.desc.chars τ, frobPeriod l c ≤ r) → (r + 2) * η < l + 1 → l ≠ 2 → ∀ y ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ (η * (r + 1)) • D.Mon (y + D.phi m) ∈ D.Z := by
  first | exact @GlobalTheory.BK.pow_smul_Mon_add_phi_mem_Z | exact GlobalTheory.BK.pow_smul_Mon_add_phi_mem_Z | (intros; apply GlobalTheory.BK.pow_smul_Mon_add_phi_mem_Z <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.GroupLayer

variable {l : ℕ} [Fact l.Prime]

theorem v_le_iff (P : LocPrime l) (LL : FinExt l) (x y : ↥LL.1) :
    P.v LL y ≤ P.v LL x ↔ ‖(x : Om l)‖ ≤ ‖(y : Om l)‖ := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HWL.NormVal.locPrime_v_normalised l P LL
  by_cases hy : y = 0
  · subst hy
    simp only [AddValuation.map_zero, top_le_iff, AddValuation.top_iff, ZeroMemClass.coe_zero,
      norm_zero, norm_le_zero_iff, ZeroMemClass.coe_eq_zero]
  · have hne : P.v LL y ≠ ⊤ := fun h => hy ((AddValuation.top_iff _).1 h)
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hq, h2, (h1 y q).1 hq.symm]

theorem norm_coe_algebraMap (LL : FinExt l) (a : ℤ_[l]) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) a) : ↥LL.1) : Om l)‖ = ‖a‖ := by
  change ‖algebraMap ℚ_[l] (Om l) (a : ℚ_[l])‖ = ‖(a : ℚ_[l])‖
  simp

theorem norm_pow_sub_one (LL : FinExt l) (a : ℤ_[l]) (k : ℕ) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 ((algebraMap ℤ_[l] ↥(OL LL) a) ^ k) - 1 : ↥LL.1) : Om l)‖
      = ‖a ^ k - 1‖ := by
  rw [← norm_coe_algebraMap LL (a ^ k - 1)]
  simp only [RingHom.map_sub, RingHom.map_one, map_pow (algebraMap ℤ_[l] ↥(OL LL))]

theorem norm_sub_one (LL : FinExt l) (a : ℤ_[l]) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) a) - 1 : ↥LL.1) : Om l)‖
      = ‖a - 1‖ := by
  simpa only [pow_one] using norm_pow_sub_one LL a 1

noncomputable def congSub (l : ℕ) [Fact l.Prime] (s : ℕ) : Subgroup ℤ_[l]ˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {(l : ℤ_[l]) ^ s})).toMonoidHom).ker

theorem mem_congSub (s : ℕ) (u : ℤ_[l]ˣ) :
    u ∈ congSub l s ↔ ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← Ideal.Quotient.eq, congSub, MonoidHom.mem_ker,
    Units.ext_iff]
  simp

theorem nonempty_gamS : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l),
    Good K s LL → Nonempty (GamS P K s LL) := by
  intro l _ P K s LL hG
  obtain ⟨emb, hbij, hσ⟩ := GlobalTheory.HWL.exists_letters l P K s LL hG
  obtain ⟨hs1, hs2, hKs, -⟩ := hG
  obtain ⟨χ, hχ, -, honto⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  obtain ⟨one, hone1, hone2⟩ := GlobalTheory.HWL.exists_unitLat l K LL
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HWL.NormVal.locPrime_v_normalised l P LL
  let χK : ↥(GK K) →* ℤ_[l]ˣ := χ.comp (GK K).subtype
  obtain ⟨gam, gamK, D, hgam, hD, hK, hKeq, hK1⟩ := GlobalTheory.PadicUnitSub.exists_gam_gamK_torsion l s χK.range hs1 hs2 (fun u hu => by
    obtain ⟨g, hg, hgu⟩ := honto K s hKs u hu
    exact ⟨⟨g, hg⟩, hgu⟩)
  let χΓ : ↥χK.range →* (↥(OL LL))ˣ :=
    (Units.map (algebraMap ℤ_[l] ↥(OL LL)).toMonoidHom).comp χK.range.subtype
  have hχΓ : ∀ g : ↥χK.range, (χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) ((g : ℤ_[l]ˣ) : ℤ_[l]) :=
    fun _ => rfl
  have hres : ∀ g : ↥(GK K), algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l]) =
      algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) ((χK g : ℤ_[l]ˣ) : ℤ_[l])) := fun g => by
    rw [P.PD_χ, ← hχ]; rfl
  have hs : ((s : ℚ) : WithTop ℚ) = (s : WithTop ℚ) := by norm_cast
  have hz : (l : ℝ) ^ (-((s : ℚ) : ℝ)) = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [← Real.rpow_intCast]; push_cast; rfl
  refine ⟨{ emb := emb, emb_bij := hbij, emb_σ := hσ, n_eq := rfl, v_l := ?_, s_pos := hs1,
            s_two := fun h => hs2 (by rwa [P.PD_p] at h), Gam := ↥χK.range,
            resΓ := χK.rangeRestrict, resΓ_onto := χK.rangeRestrict_surjective, χΓ := χΓ,
            χΓ_res := fun g => (hres g).symm, χΓ_inj := ?_, gam := gam, gam_gen := ?_, DelF := D,
            DelF_def := hD, gamK := gamK, gamK_gen := ?_, gamK_eq := ?_,
            gamK_eq_one := fun h h' => hK1 h (by rwa [P.PD_p] at h'),
            GKs := (congSub l s).comap χK, GKs_def := ?_, one := one, one_triv := hone1,
            one_line := hone2 }⟩
  · rw [P.PD_p]
    have := (h1 (l : ↥LL.1) 1).2 (by
      have h := norm_coe_algebraMap LL (l : ℤ_[l])
      rw [map_natCast, map_natCast] at h
      rw [h, PadicInt.norm_p]; simp [Real.rpow_neg_one])
    simpa using this
  · intro a b hab
    have h := congrArg (fun u : (↥(OL LL))ˣ => (u : ↥(OL LL))) hab
    simp only [hχΓ] at h
    have h0 := norm_coe_algebraMap LL (((a : ℤ_[l]ˣ) : ℤ_[l]) - ((b : ℤ_[l]ˣ) : ℤ_[l]))
    rw [map_sub, h, sub_self, map_zero, ZeroMemClass.coe_zero, norm_zero, eq_comm, norm_eq_zero,
      sub_eq_zero] at h0
    exact Subtype.ext (Units.ext h0)
  · rw [← hs, h1, hχΓ, norm_sub_one, hgam, hz]
  · intro g
    rw [v_le_iff, hχΓ, hχΓ, norm_pow_sub_one, norm_pow_sub_one]
    exact hK g
  · intro h
    refine hKeq fun g => ?_
    have := h g
    rwa [v_le_iff, hχΓ, hχΓ, norm_pow_sub_one, norm_pow_sub_one] at this
  · intro g
    rw [Subgroup.mem_comap, mem_congSub, ← hs, h2, hres, norm_sub_one, hz]

end GlobalTheory.HWL.GroupLayer
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

open NumberField IsDedekindDomain Module in
private lemma natLog_mul_log_two_le_log_of_le {l m : ℕ} {C : ℝ} (hl : 2 ≤ l) (hC : 1 ≤ C)
    (hm : (m : ℝ) ≤ C) : (Nat.log l m : ℝ) * Real.log 2 ≤ Real.log C := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simpa using Real.log_nonneg hC
  have h1 : Nat.log l m ≤ Nat.log 2 m := Nat.log_anti_left (by norm_num) hl
  have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
  have h3 : (2 : ℝ) ^ Nat.log l m ≤ C :=
    calc (2 : ℝ) ^ Nat.log l m ≤ 2 ^ Nat.log 2 m := pow_le_pow_right₀ (by norm_num) h1
      _ ≤ m := by exact_mod_cast h2
      _ ≤ C := hm
  have h4 := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at h4

open NumberField IsDedekindDomain Module in
private lemma natLog_le_add_two_mul_of_le_two_pow_mul_exp {l m k : ℕ} {L : ℝ} (hl : 2 ≤ l) (hL : 0 ≤ L)
    (hm : (m : ℝ) ≤ 2 ^ k * Real.exp L) : (Nat.log l m : ℝ) ≤ k + 2 * L := by
  have hC : (1 : ℝ) ≤ 2 ^ k * Real.exp L :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp hL)
  have h := natLog_mul_log_two_le_log_of_le hl hC hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  by_contra hcon
  push_neg at hcon
  have : ((Nat.log l m : ℝ) - k) * Real.log 2 ≤ L := by linarith
  nlinarith


open NumberField IsDedekindDomain Module in
theorem _root_.GlobalTheory.HubLoc.cBnum_le_thirty : ∀ (l t N : ℕ) (L : ℝ), 2 ≤ l → 1 ≤ t → 1 ≤ N →
    1 ≤ L → (_root_.GlobalTheory.HubLoc.cBnum l ⌊2 * Real.exp L⌋₊ t N : ℝ) ≤ 30 * t * N * L := by
  intro l t N L hl ht hN hL
  have hfl : ((⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 * Real.exp L :=
    Nat.floor_le (by positivity)
  have hm : ((2 * ⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 ^ 2 * Real.exp L := by
    push_cast
    nlinarith
  have hK := natLog_le_add_two_mul_of_le_two_pow_mul_exp hl (by linarith) hm
  unfold _root_.GlobalTheory.HubLoc.cBnum
  push_cast at hK ⊢
  set K : ℝ := (Nat.log l (2 * ⌊2 * Real.exp L⌋₊) : ℝ)
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have htN : (1 : ℝ) ≤ t * N := one_le_mul_of_one_le_of_one_le ht' hN'
  have htNL : (1 : ℝ) ≤ t * N * L := one_le_mul_of_one_le_of_one_le htN hL
  have hL1 : L ≤ t * N * L := by nlinarith
  have ht1 : (t : ℝ) ≤ t * N * L := by nlinarith
  have hA : (t : ℝ) * N * K ≤ t * N * (2 + 2 * L) := by
    apply mul_le_mul_of_nonneg_left hK; positivity
  nlinarith

end GlobalTheory.HubLoc
end

section

noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem stepJumpDirect_holds : StepJumpDirect := by
  intro D i r eta s S sg U hs hJ Xs w hw hsg
  obtain ⟨hc, hj, hU⟩ := hJ w hw
  refine ⟨insert 0 (U w), ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · constructor <;> push_cast <;> omega
    · obtain ⟨h, -, -⟩ := hU u hu
      have hs' : ((eta : ℚ) + D.R.t + 1) < s := by exact_mod_cast hs
      have hS : (0 : ℚ) ≤ S := by positivity
      have ht : (0 : ℚ) ≤ D.R.t := by positivity
      have he : (0 : ℚ) ≤ eta := by positivity
      have key : -((eta : ℚ) + D.R.t + 1) - 1 < u ∧ (u : ℚ) ≤ s + S := by
        rcases h with ⟨h1, h2⟩ | h | h
        · have h1' : (0 : ℚ) ≤ u := by exact_mod_cast h1
          have h2' : (u : ℚ) < D.R.t := by exact_mod_cast h2
          constructor <;> linarith
        · rw [abs_le] at h; unfold cen at h
          constructor <;> linarith [h.1, h.2]
        · unfold cloud cen at h; rw [hsg] at h; simp only [if_true] at h; push_cast at h
          constructor <;> linarith [h.1, h.2]
      have k1 : -((eta : ℤ) + D.R.t + 1) - 1 < u := by exact_mod_cast key.1
      have k2 : u ≤ (s : ℤ) + S := by exact_mod_cast key.2
      constructor <;> push_cast <;> omega
  · exact (Finset.card_insert_le _ _).trans (by omega)
  · intro x τ a ha
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (hj x τ a ha))

end GlobalTheory.Pass

end
end

section

noncomputable section

namespace GlobalTheory.LenModAgree

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem lenMod_eq {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S H : Submodule O M) :
    BlochKatoDuality.lenMod S H = lenModN S H := by
  unfold BlochKatoDuality.lenMod lenModN
  have h := (LinearMap.quotientInfEquivSupQuotient S H).length_eq
  rw [← h]
  have e : Submodule.comap S.subtype S ⊓ Submodule.comap S.subtype H = Submodule.comap S.subtype H := by simp
  exact (Submodule.quotEquivOfEq _ _ e).length_eq

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem main : (∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (A H : Submodule O M), lenModN A H = BlochKatoDuality.lenMod A H) ∧ ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ), LocBoundP i w hw r Xs M e ↔ LocBound i w hw r Xs M e := by
  refine ⟨fun O M _ _ _ A H => (lenMod_eq A H).symm, ?_⟩
  intro D i w hw r Xs k M e
  unfold LocBoundP LocBound
  rw [lenMod_eq]

end GlobalTheory.LenModAgree
end
end
