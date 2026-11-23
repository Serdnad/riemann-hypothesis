module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.wittFrameLevi_normalizes_radical_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → (∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, ∀ u ∈ unipRad σ J X, m * u * m⁻¹ ∈ unipRad σ J X) ∧ (∀ g ∈ unipRad σ J X, g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} → g = 1) ∧ (∀ u ∈ unipRad σ J X, ScalesBy σ J X u 1) ∧ (∀ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ β, ScalesBy σ J X m β ∧ absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ (∀ γ ∈ ratPts σ J, ∀ β, ScalesBy σ J X γ β → absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} ∧ IsClosed ((GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  first | exact @GlobalTheory.ResidueEisenstein.frame_levi_facts | exact GlobalTheory.ResidueEisenstein.frame_levi_facts | (intros; apply GlobalTheory.ResidueEisenstein.frame_levi_facts <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.exists_leviCentreFlow_wittFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ b : ℝ → GAd σ J, IsFlowJ σ J X Y b := by
  first | exact @GlobalTheory.ResidueEisenstein.exists_isFlowJ | exact GlobalTheory.ResidueEisenstein.exists_isFlowJ | (intros; apply GlobalTheory.ResidueEisenstein.exists_isFlowJ <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.leviDecomposition_wittFrameStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ p β, ScalesBy σ J X p β → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, p = u * m ∧ ScalesBy σ J X m β ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) ∧ (absE F E (Matrix.GeneralLinearGroup.det β) = 1 → m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) := by
  first | exact @GlobalTheory.LeviDecompositionFrame.levi_dec_frame | exact GlobalTheory.LeviDecompositionFrame.levi_dec_frame | (intros; apply GlobalTheory.LeviDecompositionFrame.levi_dec_frame <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.ThetaModGrowthPair

theorem theta_modGrowth : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  have hlat := GlobalTheory.T.adelicThetaSum_norm_le_polynomial_scale
  have hfin := GlobalTheory.T.weilRep_rational_support_common_denominator
  have harch := GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨N₀, k₂, C₂, hL⟩ := hlat F (Fin n × Fin d)
  obtain ⟨C₁, k₁, hA⟩ := harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ N₀
  obtain ⟨C₃, k₃, hF⟩ := hfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨|C₂| * |C₁| * |C₃| ^ k₂, k₁ + k₃ * k₂, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hsupp⟩ := hF g h
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hb := hL (C₁ * H ^ k₁) m (om (g, h) Φ) hm1 (fun ξ => hA g h _) hsupp
  have hA0 : 0 ≤ C₁ * H ^ k₁ :=
    le_trans (by positivity) (hA g h (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k₂ := by positivity
  have hmk : (m : ℝ) ^ k₂ ≤ (|C₃| * H ^ k₃) ^ k₂ :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _))) _
  have hC1 : C₁ * H ^ k₁ ≤ |C₁| * H ^ k₁ := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
  show ‖thetaSum F (om (g, h) Φ)‖ ≤ _
  calc ‖thetaSum F (om (g, h) Φ)‖ ≤ C₂ * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ := hb
    _ ≤ |C₂| * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) hm0
    _ ≤ |C₂| * (|C₁| * H ^ k₁) * (|C₃| * H ^ k₃) ^ k₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC1 (abs_nonneg _)) hmk hm0 (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hH0 _)))
    _ = |C₂| * |C₁| * |C₃| ^ k₂ * H ^ (k₁ + k₃ * k₂) := by rw [pow_add, pow_mul]; ring

end GlobalTheory.ThetaModGrowthPair
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.ModelTrUnit

theorem exists_const : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE _hbij μ hμ
  obtain ⟨ei, ev, hei, hev, hpure⟩ := hE.loc
  have hSB : ∀ v : Pl (F := F), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v φ ∈ SB (Fin n × Fin d → Fv F v) := by
    intro v φ hφ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hφ
  have hfin : ∀ v : Pl (F := F), ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ' ∈ SB (Fin n × Fin d → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => ev v φ x * starRingEnd ℂ (ev v φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x)) := by
    intro v
    have h2 : (2 : Fv F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := F)
      apply (algebraMap F (Fv F v)).injective
      rw [map_ofNat, h, map_zero]
    letI : Invertible (2 : Fv F v) := invertibleOfNonzero h2
    obtain ⟨ψv, hc, hne, A, hA⟩ := GlobalTheory.T.exists_addChar_normalizing_schrodinger_action F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure v
    exact GlobalTheory.T.local_intertwiner_unique_scalar F v (Fin n × Fin d) ψv hc hne (ev v) A (hSB v) hA
  have hinf : ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F (Fin n × Fin d),
        @integral _ ℂ _ _ (borel _) μ (fun x => ei f x * starRingEnd ℂ (ei f' x)) =
          (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
    letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    letI : Invertible (2 : mixedEmbedding.mixedSpace F) :=
      (Invertible.map (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2).copy 2 (map_ofNat _ 2).symm
    obtain ⟨ψ, hψ, A, hA⟩ := GlobalTheory.T.weil_eigen_continuous_inverse F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure
    exact GlobalTheory.T.archimedean_intertwiner_unique hP F (Fin n × Fin d) ψ hψ ei A hA
  exact GlobalTheory.T.restricted_tensor_schwartz F (Fin n × Fin d) e M.vac M₁.vac ei ev (fun v => (hPair.good.vac v).1) hPair.good.std hM₁.std
    (fun v => (hev v).1) hSB hpure hinf hfin μ hμ

end GlobalTheory.ModelTrUnit
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section
namespace GlobalTheory.ThetaChange

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c₀ * thetaSum F Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij
  have hstd : IsStd B.ψ := hP.base.std
  have hrk : Module.finrank F E = 2 := hP.base.cm.2.2.1
  obtain ⟨Φr, hΦr⟩ := GlobalTheory.RatCoord.ratEquiv F E σ n d X W M B.ψ hP.good hrk
  obtain ⟨lθ, hlθ, hlθ'⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  have hcomp := GlobalTheory.EvAdm.comp_mem_adm F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE lθ hlθ
  have hinc1 : ∀ k : ℕ, incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := by
    intro k; unfold incM; exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨c, hc⟩ := GlobalTheory.T.schwartz_functional_archimedean_factor F B.ψ hstd (Fin n × Fin d) (fun Φ => thetaSum F (e Φ))
    (fun Φ hΦ Ψ hΨ => by
      simp only [map_add (f := _)]
      exact GlobalTheory.WeilM.thetaSum_add F (hE.maps Φ hΦ) (hE.maps Ψ hΨ))
    (fun c Φ _ => by simp only [map_smul]; exact GlobalTheory.WeilM.thetaSum_smul F c (e Φ))
    (fun g hg => by
      obtain ⟨T, hT⟩ := hcomp g hg
      refine ⟨T, fun f => ?_⟩
      have hm : pureA F f g ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
      rw [← hlθ' _ (hE.maps _ hm)]
      exact hT f)
    (fun a b Φ hΦ => by
      set x := Φr.symm (a, b) with hx
      have hxe : M.co.e (incM F x) = ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) := by
        rw [hΦr x, hx, LinearEquiv.apply_symm_apply]
      have h1 : schr B.ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ =
          M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * incM F x * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ := by
        rw [hinc1, hinc1, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
        show _ = schr B.ψ (M.co.e (incM F x)) Φ
        rw [hxe]
      rw [h1, hE.Heisenberg₂ _ Φ hΦ]
      obtain ⟨y, z, hyz⟩ := hM₁.rat x
      show thetaSum F (schr B.ψ (M₁.co.e (incM F x)) (e Φ)) = _
      rw [hyz]
      exact GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ (fun a => hstd.2.1 a) y z (e Φ))
  refine ⟨c, ?_, hc⟩
  rintro rfl
  obtain ⟨φ₀, hφ₀, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
  obtain ⟨Φ, hΦ, rfl⟩ := hbij.surjOn hφ₀
  exact hne (by rw [hc Φ hΦ, zero_mul])

end GlobalTheory.ThetaChange
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FamHom

theorem main : ∀ (K : Type) [Field K] (A A' T : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P)
    (β : Pic (A.X ⊗ T.X).left), (∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ T.X),
      CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β) →
    CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ T.X)).left β = 0 →
    ∃! ψ : T ⟶ A', β = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ ψ.hom) := by
  intro K _ A A' T P hP β hadd h0
  obtain ⟨M, hM, rfl⟩ := cls_surj β
  have hMa : AbDual.IsAdditive M := (AbDual.isAdditive_iff hM).2 fun Y a a' t => hadd Y a a' t
  obtain ⟨x, hx, hu⟩ := hP.univ T.X M hM hMa
  have hE : (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ x)).IsLB := pull_isLB hP.isLB _
  have c : cls M hM = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ x) := (cls_eq_iff hM hE).2 hx
  have Kx : ∀ (Y : Over (Sp K)) (a : Y ⟶ A.X) (t : Y ⟶ T.X),
      AbDual.evc hP.isLB a (t ≫ x) = AbDual.evc hM a t := by
    intro Y a t
    have k := AbDual.evc_ev hP.isLB (fst A.X T.X) (snd A.X T.X ≫ x) hE a t
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k]
    unfold AbDual.evc
    rw [c]
    rfl
  have h1 := (AbDual.triv_ev_iff hM (𝟙 A.X) (1 : A.X ⟶ T.X)).2 h0
  have u : snd A.X (𝟙_ (Over (Sp K))) ≫ (η[T.X] : 𝟙_ (Over (Sp K)) ⟶ T.X) = 1 := by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A.X (𝟙_ (Over (Sp K)))) (toUnit _)]
  have e1 : η[T.X] ≫ x = 1 := by
    apply hP.eq_one
    rw [AbDual.triv_ev_iff hP.isLB, ← Category.assoc, Kx, u, AbDual.evc_one_right hM h1]
  have hpt : η[T.X] ≫ x = η[A'.X] := by
    rw [e1]
    show toUnit _ ≫ η = η
    rw [toUnit_unique (toUnit (𝟙_ (Over (Sp K)))) (𝟙 _), Category.id_comp]
  have hmon : IsMonHom x := rigidity_holds (Sp K) T.X A'.X T.ab A'.ab x hpt
  refine ⟨Hom.mk x, c, fun ψ hψ => ?_⟩
  have hE' : (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ ψ.hom)).IsLB := pull_isLB hP.isLB _
  have hψ' : LBIso M (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ ψ.hom)) := (cls_eq_iff hM hE').1 hψ
  exact Subtype.ext (hu ψ.hom hψ')

end GlobalTheory.AV.FamHom
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RelAmpleSep

theorem mem_iff_of_gen {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {κ : Type} (r : κ → R) (c : κ → A)
    (I : Ideal R) (hI : ∀ j, r j - φ (c j) ∈ I) (p : MvPolynomial κ A) :
    MvPolynomial.eval₂Hom φ r p ∈ I ↔ φ (MvPolynomial.eval c p) ∈ I := by
  have hr : (Ideal.Quotient.mk I) ∘ r = ((Ideal.Quotient.mk I).comp φ) ∘ c := by
    funext j; exact Ideal.Quotient.eq.2 (hI j)
  have e : Ideal.Quotient.mk I (MvPolynomial.eval₂Hom φ r p) = Ideal.Quotient.mk I (φ (MvPolynomial.eval c p)) := by
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, hr, MvPolynomial.eval,
      MvPolynomial.coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.eval₂_comp_left]
    rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem (I := I), e]

theorem ideal_eq_of_gen {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {κ : Type} (r : κ → R) (c : κ → A)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom φ r)) (P Q : Ideal R)
    (hP : ∀ j, r j - φ (c j) ∈ P) (hQ : ∀ j, r j - φ (c j) ∈ Q) (hPQ : ∀ x, φ x ∈ P ↔ φ x ∈ Q) : P = Q := by
  ext a
  obtain ⟨p, rfl⟩ := hs a
  rw [mem_iff_of_gen φ r c P hP, mem_iff_of_gen φ r c Q hQ]
  exact hPQ _

theorem mem_basicOpen_iff_prime {Y : Scheme.{0}} {D : Y.Opens} (hD : IsAffineOpen D) {y : Y} (hy : y ∈ D)
    (a : Γ(Y, D)) : y ∈ Y.basicOpen a ↔ a ∉ (hD.primeIdealOf ⟨y, hy⟩).asIdeal := by
  have h := hD.fromSpec_primeIdealOf ⟨y, hy⟩
  have h2 : hD.primeIdealOf ⟨y, hy⟩ ∈ hD.fromSpec ⁻¹ᵁ Y.basicOpen a ↔ y ∈ Y.basicOpen a := by
    show hD.fromSpec (hD.primeIdealOf ⟨y, hy⟩) ∈ Y.basicOpen a ↔ y ∈ Y.basicOpen a
    rw [h]
  rw [← h2, hD.fromSpec_preimage_basicOpen]
  rfl

variable {K : Type} [Field K]

theorem one_left_comp_hom (B : AbVar K) : (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left ≫ B.X.hom = 𝟙 _ := Over.w _

theorem sp_pt_eq (a b : Sp K) : a = b := by
  have h : ∀ p : PrimeSpectrum K, p.asIdeal = ⊥ := fun p => Ideal.eq_bot_of_prime _
  exact PrimeSpectrum.ext ((h a).trans (h b).symm)

theorem top_le_preimage_unit (B : AbVar K) : (⊤ : (Over.mk (𝟙 (Sp K))).left.Opens) ≤
    (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left ⁻¹ᵁ (B.X.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial

def unitU (B : AbVar K) : (⊤ : (Sp K).Opens).toScheme ⟶ (B.X.hom ⁻¹ᵁ ⊤).toScheme :=
  (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left.resLE (B.X.hom ⁻¹ᵁ ⊤) (⊤ : (Over.mk (𝟙 (Sp K))).left.Opens)
    (top_le_preimage_unit B)

theorem unitU_comp (B : AbVar K) : unitU B ≫ (B.X.hom ∣_ ⊤) = 𝟙 _ := by
  rw [← cancel_mono (⊤ : (Sp K).Opens).ι, Category.assoc, morphismRestrict_ι, unitU,
    Scheme.Hom.resLE_comp_ι_assoc, one_left_comp_hom, Category.comp_id, Category.id_comp]

theorem unitU_ι (B : AbVar K) (t : (⊤ : (Sp K).Opens).toScheme) :
    (B.X.hom ⁻¹ᵁ ⊤).ι (unitU B t) = B.origin := by
  rw [← Scheme.Hom.comp_apply, unitU, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, AbVar.origin]
  exact congrArg _ (sp_pt_eq _ _)

theorem topU_pt_eq (a b : (⊤ : (Sp K).Opens).toScheme) : a = b := Subtype.ext (sp_pt_eq _ _)

theorem isUnit_sub_mul_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {a b : R} (c : R) (ha : IsUnit a)
    (hb : ¬ IsUnit b) : IsUnit (a - c * b) := by
  by_contra h
  have hb' : b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hb
  have h' : a - c * b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
  have h'' := Ideal.add_mem _ h' (Ideal.mul_mem_left _ c hb')
  rw [sub_add_cancel] at h''
  exact (IsLocalRing.mem_maximalIdeal _).1 h'' ha

theorem gs_secSubScale {Y : Scheme.{0}} {P : LB Y} (a b : P.Sec) (c : Γ(Y, ⊤)) (y : Y) (k : P.ι) (hk : y ∈ P.U k) :
    gs (𝟙 Y) y _ ((DVR.SecOps.secAdd a (DVR.SecOps.secNeg (DVR.SecOps.secScale c b))).f k) =
      gs (𝟙 Y) y _ (a.f k) - gs (𝟙 Y) y ⊤ c * gs (𝟙 Y) y _ (b.f k) := by
  have e : (DVR.SecOps.secAdd a (DVR.SecOps.secNeg (DVR.SecOps.secScale c b))).f k =
      a.f k - Out.resTop _ c * b.f k := by
    simp only [DVR.SecOps.secAdd, DVR.SecOps.secNeg, DVR.SecOps.secScale, sub_eq_add_neg]
  rw [e, LBGerm.gs_sub _ y _ hk, gs_mul _ y _ hk, Out.resTop, gs_res _ y _ hk]

theorem exists_sep_of_chart {Y T : Scheme.{0}} (π : Y ⟶ T) (u : T ⟶ Y) (hu : u ≫ π = 𝟙 T) (hT : ∀ a b : T, a = b)
    {P : LB Y} (hP : P.IsLB) {n : ℕ} (s : Fin n → P.Sec) (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (i : Fin n) (hD : IsAffineOpen (Out.nonzeroLocus (s i)))
    (r : Fin n → Γ(Y, Out.nonzeroLocus (s i)))
    (hr : ∀ j k, (Y.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s j).f k) =
            (Y.presheaf.map (homOfLE (inf_le_left :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ Out.nonzeroLocus (s i))).op).hom (r j) *
            (Y.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s i).f k))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (π.appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom r))
    (t₀ : T) (hi : u t₀ ∈ Out.nonzeroLocus (s i)) :
    ∃ t : Fin n → P.Sec, (∀ j, u t₀ ∉ Out.nonzeroLocus (t j)) ∧
      ∀ y, y ≠ u t₀ → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  classical
  have hTle : ⊤ ≤ u ⁻¹ᵁ Out.nonzeroLocus (s i) := fun t _ => by rw [hT t t₀]; exact hi
  let c : Fin n → Γ(T, ⊤) := fun j => (u.appLE (Out.nonzeroLocus (s i)) ⊤ hTle).hom (r j)
  let φ := (π.appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom
  have hc : ∀ (y : Y) (x : Γ(T, ⊤)), gs (𝟙 Y) y ⊤ (π.appTop.hom x) = gs π y ⊤ x := fun y x =>
    (gs_pull (𝟙 Y) π y ⊤ trivial x).trans (by rw [Category.id_comp])
  have hφ : ∀ y ∈ Out.nonzeroLocus (s i), ∀ x, gs (𝟙 Y) y _ (φ x) = gs π y ⊤ x := fun y hy x =>
    (gs_appLE π ⊤ _ le_top (𝟙 Y) y hy x).trans (by rw [Category.id_comp])
  have hrel : ∀ j k y, y ∈ Out.nonzeroLocus (s i) → y ∈ P.U k →
      gs (𝟙 Y) y _ ((s j).f k) = gs (𝟙 Y) y _ (r j) * gs (𝟙 Y) y _ ((s i).f k) := by
    intro j k y hyD hk
    have hm : y ∈ Out.nonzeroLocus (s i) ⊓ P.U k := ⟨hyD, hk⟩
    have e := congrArg (gs (𝟙 Y) y (Out.nonzeroLocus (s i) ⊓ P.U k)) (hr j k)
    rwa [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
  have hkey : ∀ y ∈ Out.nonzeroLocus (s i), ∀ j k, y ∈ P.U k →
      gs (𝟙 Y) y _ ((DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg
        (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i)))).f k) =
        gs (𝟙 Y) y _ (r j - φ (c j)) * gs (𝟙 Y) y _ ((s i).f k) := by
    intro y hy j k hk
    rw [gs_secSubScale _ _ _ y k hk, hrel j k y hy hk, hc, LBGerm.gs_sub _ y _ hy, hφ y hy]
    ring
  have hiff : ∀ y ∈ Out.nonzeroLocus (s i), ∀ j,
      y ∈ Out.nonzeroLocus (DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg
        (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i)))) ↔ y ∈ Y.basicOpen (r j - φ (c j)) := by
    intro y hy j
    obtain ⟨k, hk⟩ := exists_chart hP y
    rw [GlobalTheory.mem_nonzeroLocus_iff_isUnit _ hk, hkey y hy j k hk, IsUnit.mul_iff,
      ← GlobalTheory.mem_nonzeroLocus_iff_isUnit (s i) hk, LBGerm.isUnit_gs_iff (𝟙 Y) y _ hy]
    exact and_iff_left hy
  have h0 : ∀ j, u t₀ ∉ Y.basicOpen (r j - φ (c j)) := by
    intro j h
    have hu1 := (LBGerm.isUnit_gs_iff u t₀ _ hi _).2 h
    have e1 : gs u t₀ _ (r j) = gs (𝟙 T) t₀ ⊤ (c j) :=
      ((gs_appLE u _ ⊤ hTle (𝟙 T) t₀ trivial (r j)).trans (by rw [Category.id_comp])).symm
    have e2 : gs u t₀ _ (φ (c j)) = gs (𝟙 T) t₀ ⊤ (c j) :=
      (gs_appLE π ⊤ _ le_top u t₀ hi (c j)).trans (by rw [hu])
    rw [LBGerm.gs_sub u t₀ _ hi, e1, e2, sub_self] at hu1
    exact not_isUnit_zero hu1
  refine ⟨fun j => DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i))),
    fun j h => h0 j ((hiff _ hi j).1 h), fun y hy => ?_⟩
  by_cases hyD : y ∈ Out.nonzeroLocus (s i)
  · by_contra hno
    push_neg at hno
    have hPy : ∀ j, r j - φ (c j) ∈ (hD.primeIdealOf ⟨y, hyD⟩).asIdeal := fun j => by
      by_contra h
      exact hno j ((hiff y hyD j).2 ((mem_basicOpen_iff_prime hD hyD _).2 h))
    have hQ : ∀ j, r j - φ (c j) ∈ (hD.primeIdealOf ⟨u t₀, hi⟩).asIdeal := fun j => by
      by_contra h
      exact h0 j ((mem_basicOpen_iff_prime hD hi _).2 h)
    have hb : ∀ z ∈ Out.nonzeroLocus (s i), ∀ x, z ∈ Y.basicOpen (φ x) ↔ π z ∈ T.basicOpen x := fun z hz x =>
      (LBGerm.isUnit_gs_iff (𝟙 Y) z _ hz (φ x)).symm.trans (by rw [hφ z hz]; exact LBGerm.isUnit_gs_iff π z ⊤ trivial x)
    have hPQ : ∀ x, φ x ∈ (hD.primeIdealOf ⟨y, hyD⟩).asIdeal ↔ φ x ∈ (hD.primeIdealOf ⟨u t₀, hi⟩).asIdeal := by
      intro x
      rw [← not_iff_not, ← mem_basicOpen_iff_prime hD hyD, ← mem_basicOpen_iff_prime hD hi, hb y hyD, hb _ hi,
        hT (π y) (π (u t₀))]
    have hE := ideal_eq_of_gen φ r c hs _ _ hPy hQ hPQ
    have e1 := hD.fromSpec_primeIdealOf ⟨y, hyD⟩
    have e2 := hD.fromSpec_primeIdealOf ⟨u t₀, hi⟩
    rw [PrimeSpectrum.ext hE] at e1
    exact hy (e1.symm.trans e2)
  · have hy' : y ∈ (⨆ i, Out.nonzeroLocus (s i)) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
    obtain ⟨k, hk⟩ := exists_chart hP y
    refine ⟨j, ?_⟩
    rw [GlobalTheory.mem_nonzeroLocus_iff_isUnit _ hk, gs_secSubScale _ _ _ y k hk]
    exact isUnit_sub_mul_of_not_isUnit _ ((GlobalTheory.mem_nonzeroLocus_iff_isUnit (s j) hk).1 hj)
      fun h => hyD ((GlobalTheory.mem_nonzeroLocus_iff_isUnit (s i) hk).2 h)

theorem exists_sec_sep_origin : ∀ (K : Type) [Field K] (B : AbVar K) (L : LB B.X.left), L.IsLB →
    Out.RelAmple B.X L → ∃ N : ℕ, 1 ≤ N ∧ ∃ (M : ℕ) (t : Fin M → LB.Sec (Out.powOver B.X L ⊤ N)),
      (∀ j y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y ∉ Out.nonzeroLocus (t j)) ∧
      ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y ≠ B.origin → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  intro K _ B L hL hA
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA ⊤ (isAffineOpen_top _)
  obtain ⟨t₀⟩ : Nonempty (⊤ : (Sp K).Opens).toScheme := ⟨⟨IsLocalRing.closedPoint K, trivial⟩⟩
  have hmem : unitU B t₀ ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨t, h1, h2⟩ := exists_sep_of_chart (B.X.hom ∣_ ⊤) (unitU B) (unitU_comp B) topU_pt_eq
    (LB.isLB_linComb hL _ _) s hcov i hD r hr hsurj t₀ hi
  have hinj : ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y = unitU B t₀ := fun y hy =>
    Subtype.ext ((Scheme.Opens.ι_apply _ _).symm.trans
      (hy.trans ((unitU_ι B t₀).symm.trans (Scheme.Opens.ι_apply _ _))))
  exact ⟨N, hN, M + 1, t, fun j y hy => hinj y hy ▸ h1 j, fun y hy => h2 y fun h => hy (h ▸ unitU_ι B t₀)⟩

end GlobalTheory.RelAmpleSep
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem lam_symm_nat_add : ∀ (K : Type) [Field K] (A B : AbVar K) (c c' : Pic A.X.left) (d : Pic B.X.left) (f : A ⟶ B) (Y Z : Over (Sp K)) (u : Z ⟶ Y) (x y : Y ⟶ A.X), AbVar.lam c x y = AbVar.lam c y x ∧ CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) ∧ AbVar.lam d (x ≫ f.hom) (y ≫ f.hom) = AbVar.lam (CechPic.pull f.hom.left d) x y ∧ AbVar.lam (c + c') x y = AbVar.lam c x y + AbVar.lam c' x y := by
  intro K _ A B c c' d f Y Z u x y
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact CechPic.lam_comm c x y
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact CechPic.pull_lam u c x y
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact (CechPic.lam_pull f.hom d x y).symm
  · simp only [AbVar.lam, map_add (f := _)]; abel

end GlobalTheory.AV
end
