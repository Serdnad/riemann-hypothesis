module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterRestriction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLocalFactorFinitePlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
public import GroundTheory.GlobalFields.Adele.Bundle002
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import GroundTheory.GlobalFields.Adele.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle002
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
public import GroundTheory.GlobalFields.Adele.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.StdFinRat

theorem std_fin_rat : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ x : F,
    ψ (pairA F 0 (algebraMap F (Af F) x)) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) :=
  fun _ _ _ _ hψ x => GlobalTheory.PsiNontriv.isStd_fin_rat hψ x

end GlobalTheory.StdFinRat
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.theta_kernel_archimedean_unipotent_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) → (∀ u : AF F, At (evI F) u → u • (mat h - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat g - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat h - 1) = 0) →
    ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), ∀ u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    (∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) →
    ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (@MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x =>
          om' (g, h) Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u (om' (g, h) Φ) x)) =
        @MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x => Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u Φ x) := by
  first | exact @GlobalTheory.CptCoeff.matrix_coeff | exact GlobalTheory.CptCoeff.matrix_coeff | (intros; apply GlobalTheory.CptCoeff.matrix_coeff <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK


theorem _root_.GlobalTheory.T.exists_hecke_character_restriction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ χ : Chr F E, IsHecke F E χ ∧ ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 1 := by
  first | exact @GlobalTheory.CMHeckeEta.exists_hecke_resEtaPow_one | exact GlobalTheory.CMHeckeEta.exists_hecke_resEtaPow_one | (intros; apply GlobalTheory.CMHeckeEta.exists_hecke_resEtaPow_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inert_place_local_field_data_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : Valued L (WithZero (Multiplicative ℤ))) (_ : CompleteSpace L)
      (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧ (Valued.v δ = 1 ∧ σL δ = -δ) ∧
      (∀ x ∈ Formalism.UG.intL L, σL x = x → ψL x = 1) ∧ (∃ x ∈ Formalism.UG.intL L, σL x = x ∧ ψL (ϖ⁻¹ * x) ≠ 1) ∧
      Function.Injective ι ∧ (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) ∧
      (∀ x y, ι (x * y) = ι x * ι y) ∧ (∀ x, ι (σL x) = cA σ (ι x)) ∧
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) ∧
      (∀ x, B.ψ (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ι x)) = ψL (x + σL x)) := by
  first | exact @GlobalTheory.InertLocField.field_data | exact GlobalTheory.InertLocField.field_data | (intros; apply GlobalTheory.InertLocField.field_data <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.theta_local_factor_finite_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ), (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (S : Finset (Pl (F := F))) (g₁ g₂ g₃ : UA σ G.V'.J) (h₁ h₂ h₃ : UA σ G.W.J), v ∉ S ∧
      g = g₁ * g₂ * g₃ ∧ h = h₁ * h₂ * h₃ ∧ At (evI F) (mat g₁ - 1) ∧ At (evI F) (mat h₁ - 1) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g₂ - 1) = 0) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h₂ - 1) = 0) ∧
      (∀ u : AF F, At (evI F) u → u • (mat g₃ - 1) = 0) ∧ (∀ u : AF F, At (evI F) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat g₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, w ≠ v → w ∉ S → ∀ γ, (mat g₃ * γ * Matrix.transpose (mat h₃) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) ∧
      (∀ w, w ≠ v → w ∉ S → φ w = G.M'.vac w) := by
  first | exact @GlobalTheory.UnitaryTriSplit.factor_away | exact GlobalTheory.UnitaryTriSplit.factor_away | (intros; apply GlobalTheory.UnitaryTriSplit.factor_away <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.tensorLatticeAtFinitePlace_eq_integral_span_generators : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∃ (M : Type) (_ : Fintype M) (g : M → Matrix (Fin n) (Fin d) E), ∀ γ,
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v ↔ ∃ a : M → v.adicCompletionIntegers F,
        γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m) := by
  first | exact @GlobalTheory.LatParam.latAtV_param | exact GlobalTheory.LatParam.latAtV_param | (intros; apply GlobalTheory.LatParam.latAtV_param <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.trace_hermitianTensor_integral_of_char_trivial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)), PsiUnr ψ v →
    ∀ X₀ : Matrix (Fin n) (Fin d) E, (∀ γ ∈ latAtV X Y v,
      ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1) →
    ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v) (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)))
      ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.KFinLoc.trace_hTens_integral_of_char | exact GlobalTheory.KFinLoc.trace_hTens_integral_of_char | (intros; apply GlobalTheory.KFinLoc.trace_hTens_integral_of_char <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.witt_rank_le_hermitian_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
      r₀ ≤ r ∧ r₀ ≤ s := by
  first | exact @GlobalTheory.WittFrameSig.wittFrame_le_signature | exact GlobalTheory.WittFrameSig.wittFrame_le_signature | (intros; apply GlobalTheory.WittFrameSig.wittFrame_le_signature <;> assumption)
end

section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.ThetaMeanSquareF

theorem exists_invariant_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ M : Submodule ℂ (WOF F E nS nT → ℂ), (∀ f ∈ M, IsThetaFunOF σ JS JT ξ₀ B.ψ f) →
      ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ →
        ∃ Bf : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WOF F E nS nT) (f g f' g' : M),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u f → (g' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u g →
            Bf f' g' = Bf f g) ∧
          ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (Bf f f).re := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ M hM μ 𝓕 hμ h𝓕
  have hψ : IsCharAF F B.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := countable_of_discrete_addSubgroup _
  haveI := hμ
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hb : ∀ f ∈ M, ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := fun f hf => by
    have hp : ∀ γ ∈ ratLF F E nS nT, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm ((hM f hf).quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hM f hf).cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  obtain ⟨Bf, hBf, hN⟩ := GlobalTheory.ThetaMeanSquareForm.exists_form (μ.restrict 𝓕) M
    (fun f hf => (hM f hf).cont.measurable) hb
  refine ⟨Bf, fun u f g f' g' hf hg => ?_, hN⟩
  rw [hBf, hBf, hf, hg]
  have key := GlobalTheory.HeisOrtho.setIntegral_add_right (G := WOF F E nS nT) (ratLF F E nS nT) μ 𝓕 h𝓕
    (fun w => (f : WOF F E nS nT → ℂ) w * (starRingEnd ℂ) ((g : WOF F E nS nT → ℂ) w)) (by
      rintro _ ⟨γ, rfl⟩ w
      have h0 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.2.1 (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)))
      have h1 := (hM f f.2).quasi γ w
      have h2 := (hM g g.2).quasi γ w
      show (f : WOF F E nS nT → ℂ) (ratWF γ + w) * (starRingEnd ℂ) ((g : WOF F E nS nT → ℂ) (ratWF γ + w)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]) u
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have h0 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.2.1 (symplOHF σ JS JT ξ₀ w u))
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * (f : WOF F E nS nT → ℂ) (w + u) *
    (starRingEnd ℂ) (B.ψ (symplOHF σ JS JT ξ₀ w u) * (g : WOF F E nS nT → ℂ) (w + u)) = _
  rw [map_mul, mul_mul_mul_comm, h0, one_mul]

end GlobalTheory.ThetaMeanSquareF

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.AnnCompactStd

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_add (a b : Af F) : pairA F 0 (a + b) = pairA F 0 a + pairA F 0 b := by
  refine Prod.ext ?_ rfl
  show (0 : Ainf F) = 0 + 0
  exact (add_zero 0).symm

theorem exists_psi_fin_trivial {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F,
      ψ (pairA F 0 (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) * y)) = 1 := by
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) Circle :=
    { toFun := fun y => ⟨ψ (pairA F 0 y), mem_sphere_zero_iff_norm.2 (GlobalTheory.StdCharFromIsStd.norm_psi_fin hψ y)⟩
      map_zero_eq_one' := by
        apply Subtype.ext
        show ψ (pairA F 0 0) = 1
        exact AddChar.map_zero_eq_one ψ
      map_add_eq_mul' := fun a b => by
        apply Subtype.ext
        show ψ (pairA F 0 (a + b)) = ψ (pairA F 0 a) * ψ (pairA F 0 b)
        rw [pairA_zero_add, AddChar.map_add_eq_mul] }
  have hχ : Continuous χ :=
    Continuous.subtype_mk (hψ.1.comp (continuous_const.prodMk continuous_id)) _
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_finiteChar_mul_eq_one χ hχ
  refine ⟨d, hd0, fun y hy => ?_⟩
  have h := congrArg (fun z : Circle => (z : ℂ)) (hd y hy)
  exact h

end GlobalTheory.AnnCompactStd

namespace GlobalTheory.AnnCompactStd

open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

theorem exists_mul_mem_of_forall {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ z : FiniteAdeleRing (𝓞 F) F,
      (∀ t ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (pairA F 0 (z * t)) = 1) →
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F c) * z ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
  obtain ⟨d, hd0, hd⟩ := exists_psi_fin_trivial hψ
  obtain ⟨m, hm0, hm⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).2
  refine ⟨m * d, mul_ne_zero (nonZeroDivisors.ne_zero hm0) hd0, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) z
  set δ : F := algebraMap (𝓞 F) F d with hδ
  have hint : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := fun a =>
    GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F a
  have htr : ∀ a : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (k * δ * algebraMap (𝓞 F) F a) = n := by
    intro a
    have h1 := hz (algebraMap F _ δ * algebraMap F _ (algebraMap (𝓞 F) F a))
      (Subring.mul_mem _ (hint d) (hint a))
    have hsplit : z * (algebraMap F (FiniteAdeleRing (𝓞 F) F) δ *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a)) =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (k * δ * algebraMap (𝓞 F) F a) +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * ((z - algebraMap F _ k) *
          algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a)) := by
      rw [map_mul, map_mul]; ring
    rw [hsplit, pairA_zero_add, AddChar.map_add_eq_mul, hd _ (Subring.mul_mem _ hk (hint a)), mul_one,
      GlobalTheory.PsiNontriv.isStd_fin_rat hψ, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h2 : ((Algebra.trace ℚ F (k * δ * algebraMap (𝓞 F) F a) : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
      rw [mul_comm (2 * Real.pi * Complex.I : ℂ)] at hn
      push_cast
      exact mul_right_cancel₀ hne hn
    exact_mod_cast h2
  have hdual : k * δ ∈ ((FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F) := by
    rw [FractionalIdeal.coeToSubmodule_dual_one, Submodule.mem_traceDual]
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨n, hn⟩ := htr b
    exact ⟨n, by rw [Algebra.traceForm_apply, hn]; simp⟩
  obtain ⟨b, hb⟩ := hm _ hdual
  have hsum : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (m * d)) * z =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F b) +
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F m) *
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * (z - algebraMap F _ k)) := by
    rw [hb, Algebra.smul_def, map_mul, map_mul, map_mul, map_mul]; ring
  rw [hsum]
  exact Subring.add_mem _ (hint b) (Subring.mul_mem _ (hint m) (Subring.mul_mem _ (hint d) hk))

end GlobalTheory.AnnCompactStd

namespace GlobalTheory.AnnCompactStd

open Topology

theorem isCompact_annihilator : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      IsCompact {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1} := by
  intro F _ _ ψ hψ κ _ L hL
  obtain ⟨c, hc0, hc⟩ := exists_mul_mem_of_forall hψ
  have hW : ∀ i, (fun y : FiniteAdeleRing (𝓞 F) F => (Pi.single i y : κ → FiniteAdeleRing (𝓞 F) F)) ⁻¹' L ∈
      𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := fun i =>
    (hL.preimage (continuous_single i)).mem_nhds (by
      show Pi.single i (0 : FiniteAdeleRing (𝓞 F) F) ∈ L
      rw [Pi.single_zero]; exact L.zero_mem)
  choose d hd0 hd using fun i => GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds (hW i)
  set e : κ → F := fun i => algebraMap (𝓞 F) F (c * d i) with he_def
  have he : ∀ i, e i ≠ 0 := fun i => by
    simp only [he_def]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (mul_ne_zero hc0 (hd0 i))
  let K : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.pi Set.univ fun i =>
    (fun y => algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i)⁻¹ * y) ''
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
  have hK : IsCompact K := isCompact_univ_pi fun i =>
    (GroundTheory.Global.isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)
  refine hK.of_isClosed_subset ?_ ?_
  · have hset : {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1} =
        ⋂ y ∈ L, {x | ψ (pairA F 0 (x ⬝ᵥ y)) = 1} := by
      ext x; simp
    rw [hset]
    refine isClosed_biInter fun y _ => isClosed_eq ?_ continuous_const
    exact hψ.1.comp (continuous_const.prodMk
      (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const))
  · intro x hx i _
    have hz : ∀ t ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F,
        ψ (pairA F 0 ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (d i)) * x i) * t)) = 1 := by
      intro t ht
      have h1 := hx _ (hd i t ht)
      rw [dotProduct_single] at h1
      rwa [mul_comm (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (d i))) (x i), mul_assoc]
    have h2 := hc _ hz
    refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i) * x i, ?_, ?_⟩
    · simp only [he_def, map_mul]
      rw [mul_assoc]
      exact SetLike.mem_coe.mpr h2
    · show algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i) * x i) = x i
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (he i), map_one, one_mul]

end GlobalTheory.AnnCompactStd
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

namespace GlobalTheory.StdCharEq

theorem trace_eq_infiniteTrace (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) =
      GroundTheory.Global.infiniteTrace F x := by
  classical
  rw [← GroundTheory.Global.mixedTrace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply,
    GroundTheory.Global.mixedTrace_apply, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi,
    PI.ProdFormulaE.Tr.trace_pi]
  simp only [Algebra.trace_self_apply, Algebra.trace_complex_apply]

theorem eq_adelicChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ x : AF F, ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := by
  intro F _ _ ψ hψ
  have hadd : ∀ a b : AF F, (GroundTheory.Global.adelicChar F (a + b) : ℂ) =
      (GroundTheory.Global.adelicChar F a : ℂ) * (GroundTheory.Global.adelicChar F b : ℂ) := fun a b => by
    rw [← Circle.coe_mul]
    exact congrArg _ ((GroundTheory.Global.adelicChar F).map_add_eq_mul a b)
  have hinf : ∀ x : Ainf F, ψ (pairA F x 0) = (GroundTheory.Global.adelicChar F (pairA F x 0) : ℂ) := fun x => by
    have h : GroundTheory.Global.adelicChar F (pairA F x 0) = 𝐞 (-GroundTheory.Global.infiniteTrace F x) :=
      GroundTheory.Global.adelicChar_infinite x
    rw [GlobalTheory.StdCharFromIsStd.psi_pairA hψ, trace_eq_infiniteTrace, h, Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  have hp : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  have hc : Continuous fun a : AF F => (GroundTheory.Global.adelicChar F a : ℂ) :=
    continuous_subtype_val.comp GroundTheory.Global.continuous_adelicChar
  have hcl : IsClosed {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)} :=
    isClosed_eq (hψ.1.comp hp) (hc.comp hp)
  have hrange : Set.range (algebraMap F (Af F)) ⊆
      {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    have h2 : (GroundTheory.Global.adelicChar F (algebraMap F (AF F) a) : ℂ) = 1 := by
      have h := GroundTheory.Global.adelicChar_algebraMap (K := F) a
      exact (congrArg (fun z : Circle => (z : ℂ)) h).trans Circle.coe_one
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul, hinf] at h1
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, hadd] at h2
    exact mul_left_cancel₀ (Circle.coe_ne_zero _) (h1.trans h2.symm)
  have hall := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at hall
  intro x
  rw [GlobalTheory.StdCharFromIsStd.pairA_split x, AddChar.map_add_eq_mul, hadd, hinf]
  exact congrArg _ (hall (Set.mem_univ x.2))

end GlobalTheory.StdCharEq
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory

theorem constant_one_mem_cuspForms_of_wittIndex_zero : ∀ {D : D7} {θ : InfFam D} {A B : HSp D} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A}, HidaSetting θ A B sA sB t cA → wittIndex A = 0 → (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := by
  intro D θ A B sA sB t cA _ h
  rw [wittIndex_eq_zero_iff_isAniso] at h
  exact (mem_cuspForms).2 ⟨⟨isAutFunSm_const θ A 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩

end GlobalTheory
end
