module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle035
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLeadBlockGaussTail
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentGaussInvariant
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMassOfFibre
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle043
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.LineFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.eigenspace_frobenius_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist | exact GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.dual_eigen_sub_degree_transpose : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.EigDual.eig_dual_deg | exact GlobalTheory.CompanionTheory.Ar.Crv.EigDual.eig_dual_deg | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.EigDual.eig_dual_deg <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.line_isomorphism_groupoid_laws : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)), IsMultiProjPrime P → (∀ a, IsLineIso P a a 1 1) ∧ (∀ a b f g, IsLineIso P a b f g → IsLineIso P b a g f) ∧ (∀ a b c f g f' g', IsLineIso P a b f g → IsLineIso P b c f' g' → IsLineIso P a c (f * f') (g * g')) ∧ (∀ a b a' b' f g f' g', IsLineIso P a b f g → IsLineIso P a' b' f' g' → IsLineIso P (a + a') (b + b') (f * f') (g * g')) ∧ ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (P' : Ideal (MRing ι')), IsBlockMap κ v → imageZ v P' = P → ∀ a b f g, IsLineIso P a b f g → IsLineIso P' (pullDeg κ a) (pullDeg κ b) (rename v f) (rename v g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.lineIso_algebra | exact GlobalTheory.CompanionTheory.Ar.Cmp.lineIso_algebra | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.lineIso_algebra <;> assumption)
end

section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

noncomputable section

def entryGauss (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-‖z‖ ^ 2))

theorem measurable_entryGauss : Measurable entryGauss := by
  unfold entryGauss
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp ((continuous_norm.pow 2).neg)).measurable

theorem lintegral_entryGauss_lt_top : ∫⁻ z, entryGauss z < ⊤ := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp ((continuous_pow 2).neg)).measurable
  have h1 : ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2)) < ⊤ := by
    simpa using (integrable_exp_neg_mul_sq one_pos).lintegral_lt_top
  have he : ∀ z : ℂ, entryGauss z =
      (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)))
        (Complex.measurableEquivRealProd z) := by
    intro z
    show ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) =
      ENNReal.ofReal (Real.exp (-z.re ^ 2)) * ENNReal.ofReal (Real.exp (-z.im ^ 2))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    congr 2
    ring
  calc ∫⁻ z, entryGauss z
      = ∫⁻ z, (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)))
          (Complex.measurableEquivRealProd z) := lintegral_congr he
    _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)) :=
        Complex.volume_preserving_equiv_real_prod.lintegral_comp
          ((hm.comp measurable_fst).mul (hm.comp measurable_snd))
    _ = (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2))) * ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2)) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul hm.aemeasurable hm.aemeasurable
    _ < ⊤ := ENNReal.mul_lt_top h1 h1

theorem lintegral_entryGauss_pos : 0 < ∫⁻ z, entryGauss z := by
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff measurable_entryGauss]
  intro h
  obtain ⟨z, hz⟩ := h.exists
  have : entryGauss z ≠ 0 := by
    simp [entryGauss, Real.exp_pos]
  exact this hz

theorem gaussM_univ_eq (m n : ℕ) :
    gaussM m n Set.univ = ∏ _i : Fin m, ∏ _j : Fin n, ∫⁻ z, entryGauss z := by
  have hx : ∀ x : Fin m → Fin n → ℂ, matGauss x = ∏ i, ∏ j, entryGauss (x i j) := by
    intro x
    simp only [matGauss, entryGauss, ← Finset.sum_neg_distrib, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
  rw [gaussM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [hx]
  have hmeas : ∀ _i : Fin m, Measurable (fun y : Fin n → ℂ => ∏ j, entryGauss (y j)) := fun _ =>
    Finset.measurable_prod _ fun j _ => measurable_entryGauss.comp (measurable_pi_apply j)
  have hin : ∫⁻ y : Fin n → ℂ, ∏ j, entryGauss (y j) = ∏ _j : Fin n, ∫⁻ z, entryGauss z := by
    rw [volume_pi]
    exact LeadBlockGaussTail.lintegral_pi_prod (volume : Measure ℂ) n (fun _ => entryGauss)
      fun _ => measurable_entryGauss
  have hout := LeadBlockGaussTail.lintegral_pi_prod (volume : Measure (Fin n → ℂ)) m
    (fun _ y => ∏ j, entryGauss (y j)) hmeas
  rw [volume_pi]
  rw [hout]
  exact Finset.prod_congr rfl fun _ _ => hin

theorem gaussM_univ_pos_lt_top : ∀ m n : ℕ, 0 < gaussM m n Set.univ ∧ gaussM m n Set.univ < ⊤ := by
  intro m n
  rw [gaussM_univ_eq]
  constructor
  · exact CanonicallyOrderedAdd.prod_pos.2 fun i _ =>
      CanonicallyOrderedAdd.prod_pos.2 fun j _ => lintegral_entryGauss_pos
  · exact ENNReal.prod_lt_top fun i _ => ENNReal.prod_lt_top fun j _ => lintegral_entryGauss_lt_top

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section

set_option maxSynthPendingDepth 1

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv

noncomputable section

theorem measurePreserving_swapMat (m n : ℕ) :
    MeasurePreserving (fun (π : Fin m → Fin n → ℂ) (j : Fin n) (i : Fin m) => π i j)
      volume volume := by
  have h1 := (measurePreserving_curry_matrix m n).symm (MeasurableEquiv.curry (Fin m) (Fin n) ℂ)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : Fin n × Fin m => ℂ)
    (Equiv.prodComm (Fin m) (Fin n))
  have h3 := measurePreserving_curry_matrix n m
  have h4 := h3.comp (h2.comp h1)
  have h5 : (fun (π : Fin m → Fin n → ℂ) (j : Fin n) (i : Fin m) => π i j) =
      (MeasurableEquiv.curry (Fin n) (Fin m) ℂ) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin m => ℂ)
          (Equiv.prodComm (Fin m) (Fin n))) ∘
          (MeasurableEquiv.curry (Fin m) (Fin n) ℂ).symm := by
    funext π j i
    simp only [MeasurableEquiv.coe_curry_symm, MeasurableEquiv.curry, Function.comp]
    simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Function.curry_apply,
      MeasurableEquiv.coe_piCongrLeft]
    exact (Equiv.piCongrLeft_apply_apply (fun _ : Fin n × Fin m => ℂ)
      (Equiv.prodComm (Fin m) (Fin n)) (Function.uncurry π) (i, j)).symm
  rw [h5]
  exact h4

theorem transpose_mem_unitaryGroup' {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin m) ℂ) : Aᵀ ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.1 hA
  have h2 : (star A * A)ᵀ = 1 := by rw [h, Matrix.transpose_one]
  rw [Matrix.transpose_mul] at h2
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose, Matrix.transpose_map] using h2

def colAct {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (π : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ :=
  fun i j => ∑ k, unitMat V i k * π k j

theorem colAct_eq_mul {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (π : Fin m → Fin n → ℂ) :
    colAct V π = (unitMat V * (Matrix.of π : Matrix (Fin m) (Fin n) ℂ)) := by
  funext i j
  simp [colAct, Matrix.mul_apply]

theorem colAct_symm_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    colAct V.symm (colAct V π) = π := by
  have h : unitMat V.symm * unitMat V = 1 := by simpa using unitMat_mul_symm V.symm
  rw [colAct_eq_mul, colAct_eq_mul]
  show unitMat V.symm * (unitMat V * Matrix.of π) = π
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  rfl

theorem colAct_eq_swap {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    colAct V π = fun i j => ((fun k => π k j) ᵥ* (unitMat V)ᵀ) i := by
  funext i j
  simp [colAct, Matrix.vecMul, dotProduct, mul_comm]

theorem measurePreserving_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    MeasurePreserving (colAct (n := n) V) volume volume := by
  have h1 : MeasurePreserving (fun (ρ : Fin n → Fin m → ℂ) (j : Fin n) => ρ j ᵥ* (unitMat V)ᵀ)
      volume volume :=
    volume_preserving_pi fun _ =>
      measurePreserving_vecMul (transpose_mem_unitaryGroup' (unitMat_mem V))
  have h2 := (measurePreserving_swapMat n m).comp (h1.comp (measurePreserving_swapMat m n))
  convert h2 using 1
  funext π
  rw [colAct_eq_swap]
  rfl

def colActEquiv {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    (Fin m → Fin n → ℂ) ≃ᵐ (Fin m → Fin n → ℂ) where
  toFun := colAct V
  invFun := colAct V.symm
  left_inv := colAct_symm_colAct V
  right_inv π := by simpa using colAct_symm_colAct V.symm π
  measurable_toFun := (measurePreserving_colAct V).measurable
  measurable_invFun := (measurePreserving_colAct V.symm).measurable

theorem matGauss_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    matGauss (colAct V π) = matGauss π := by
  simp only [matGauss]
  congr 3
  rw [colAct_eq_swap, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact sum_norm_sq_vecMul (transpose_mem_unitaryGroup' (unitMat_mem V)) (fun k => π k j)

theorem linProj_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : linProj (colAct V π) y = V (linProj π y) := by
  ext i
  rw [unitary_apply_eq_sum]
  simp only [linProj, colAct]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem linProj_smul {m n : ℕ} (π : Fin m → Fin n → ℂ) (c : ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : linProj π (c • y) = c • linProj π y := by
  ext i
  simp only [linProj, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cntOver_colAct {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsScaleStable S)
    {w : EuclideanSpace ℂ (Fin (e + 1))} (hw : w ≠ 0)
    (V : EuclideanSpace ℂ (Fin (e + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (e + 1)))
    (hV : V w = ((‖w‖ : ℝ) : ℂ) • firstCoordVec (e + 1)) (π : Fin (e + 1) → Fin n → ℂ) :
    cntOver S (colAct V π) (firstCoordVec (e + 1)) = cntOver S π w := by
  set c : ℂ := ((‖w‖ : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact_mod_cast norm_ne_zero_iff.2 hw
  have himg : ptsOver S (colAct V π) (firstCoordVec (e + 1)) =
      (fun y => c⁻¹ • y) '' ptsOver S π w := by
    ext z
    constructor
    · rintro ⟨hzS, hz⟩
      refine ⟨c • z, ⟨hS z hzS c hc0, ?_⟩, by simp [smul_smul, hc0]⟩
      apply V.injective
      rw [linProj_smul, map_smul, ← linProj_colAct, hz, hV]
    · rintro ⟨y, ⟨hyS, hy⟩, rfl⟩
      refine ⟨hS y hyS _ (inv_ne_zero hc0), ?_⟩
      rw [linProj_smul, linProj_colAct, hy, hV, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hinj : Set.InjOn (fun y : EuclideanSpace ℂ (Fin n) => c⁻¹ • y) (ptsOver S π w) :=
    (MulAction.injective₀ (inv_ne_zero hc0)).injOn
  simp only [cntOver]
  rw [himg, hinj.encard_image]

theorem lintegral_matGauss_cntOver :
    ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S →
      ∀ (w : EuclideanSpace ℂ (Fin (e + 1))), w ≠ 0 → ∀ T : ℝ≥0∞ → ℝ≥0∞,
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π w) =
          ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  intro n e S hS w hw T
  obtain ⟨U, -, -, hU⟩ := exists_unitary_leadCoordPlane (n := e + 1) (m := e + 1) (by omega) le_rfl
    ⊤ (by simp) w trivial
  have hV : U.symm w = ((‖w‖ : ℝ) : ℂ) • firstCoordVec (e + 1) := by
    rw [U.symm_apply_eq, hU]
  have hemb : MeasurableEmbedding (colAct (n := n) U.symm) :=
    (colActEquiv U.symm).measurableEmbedding
  have key := (measurePreserving_colAct (n := n) U.symm).lintegral_comp_emb hemb
    (fun π => matGauss π * T (cntOver S π (firstCoordVec (e + 1))))
  refine Eq.trans ?_ key
  refine lintegral_congr fun π => ?_
  simp only [matGauss_colAct, cntOver_colAct hS hw U.symm hV]

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem isPrimitiveRoot_map_of_charZero {A C : Type} [CommRing A] [IsDomain A] [Field C] [CharZero C]
    (ψ : A →+* C) (p : ℕ) [hp : Fact p.Prime] {ζ : A} (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (ψ ζ) p := by
  have hp1 := hp.out
  have h1 : ψ ζ ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h2 : ψ ζ ≠ 1 := by
    intro h
    have hs := congrArg ψ (hζ.geom_sum_eq_zero hp1.one_lt)

    rw [map_sum, map_zero] at hs
    simp only [map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at hs
    exact hp1.ne_zero (by exact_mod_cast hs)
  exact IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime h1 h2)

theorem isHTConst_sub_one_of_primitive {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) [CharZero C] (p : ℕ) [hp : Fact p.Prime] {A : Type} [CommRing A] [IsDomain A]
    (φ : A →+* O) {ζ : A} (hζ : IsPrimitiveRoot ζ p) :
    IsHTConst v p (φ (ζ - 1)) ∧ (ζ - 1) ∣ (p : A) ^ 2 := by
  have h1 : IsPrimitiveRoot ((algebraMap O C) (φ ζ)) p :=
    GlobalTheory.CompanionTheory.Ar.HT.isPrimitiveRoot_map_of_charZero ((algebraMap O C).comp φ) p hζ
  have hne : p - 1 ≠ 0 := by
    have := hp.out.two_le
    omega
  refine ⟨?_, ?_⟩
  · rw [map_sub, map_one]
    exact GlobalTheory.CompanionTheory.Ar.HT.PointTest.isHTConst_sub_one h1
  · exact (dvd_pow_self (ζ - 1) hne).trans
      ((GlobalTheory.CompanionTheory.Ar.HT.primRoot_sub_one_pow_associated hp.out hζ).dvd.trans
        (dvd_pow_self _ two_ne_zero))

theorem isHTConst_of_isCp : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [CharZero C] (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (φ : A →+* O) (κ : A), v (p : C) < 1 → (if p = 2 then κ = 4 else ∃ ζ : A, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → IsHTConst v p (φ κ) ∧ κ ∣ (p : A) ^ 2 := by
  intro C _ v O _ _ hv _ p _ A _ _ _ φ κ hvp hκ
  split_ifs at hκ with h2
  · subst h2
    subst hκ
    have hv2 : v (2 : C) < 1 := by exact_mod_cast hvp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [map_ofNat, map_ofNat]
      norm_num
    · rw [map_ofNat, map_ofNat]
      have h4 : (4 : C) = 2 * 2 := by norm_num
      rw [h4, map_mul]
      norm_num
      exact mul_le_of_le_one_left' hv2.le
    · exact ⟨1, by norm_num⟩
  · obtain ⟨ζ, hζ, rfl⟩ := hκ
    exact GlobalTheory.CompanionTheory.Ar.HT.isHTConst_sub_one_of_primitive v hv p φ hζ

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.monomial_ratio_integral_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (b b' : K → ℤ) (u : Ω), u ≠ 0 → (∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b) → ∃ f g : MRing ι O, IsVerticalDivisor (pointIdeal O x) ϖ (b - b') f g ∧ aeval x f = u * aeval x g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.VertDiv.commensurable_vertical | exact GlobalTheory.CompanionTheory.Ar.Num.VertDiv.commensurable_vertical | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.VertDiv.commensurable_vertical <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.same_generic_flag_comparison : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ), IsFlagFrame x E w b → IsFlagFrame x E' w' b' → (∀ i j : Fin N, i < j → w.repr (w' i) j = 0) → SameGenericFibre ϖ E E' ∧ ∃ f g : Fin N → MRing ι O, IsFlagPair ϖ x E E' w w' b b' f g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagPairOfFrames.main | exact GlobalTheory.CompanionTheory.Ar.FlagPairOfFrames.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagPairOfFrames.main <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem pullConeNullModP : GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.proof

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.integral_point_complete_valued_field : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (p : ℕ) [Fact p.Prime] (𝔮 : Ideal A), 𝔮.IsPrime → 𝔮.height = 1 → (p : A) ∈ 𝔮 → ∃ (C O : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : CommRing O) (_ : IsDomain O) (_ : Algebra O C) (v : Valuation C NNReal) (φ : A →+* O), v.Integers O ∧ v (p : C) < 1 ∧ IsAdicComplete (Ideal.span {(p : O)}) O ∧ Function.Injective φ ∧ ∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (φ a)) < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.exists_complete_algClosed_center_of_height_one | exact GlobalTheory.CompanionTheory.Ar.HT.exists_complete_algClosed_center_of_height_one | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.exists_complete_algClosed_center_of_height_one <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem lineFibre_holds : ReciprocityTheory.ChartRestriction.G.AI.I4.LineFibreStatement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.LineFibre.full

end GlobalTheory.CompanionTheory.Ar.Giv
end
