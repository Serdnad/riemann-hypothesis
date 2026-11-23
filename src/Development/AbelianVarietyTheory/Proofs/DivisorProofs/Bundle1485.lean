module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

theorem _root_.GlobalTheory.T.adele_quotient_compact_fundamental_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ K : Set (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), IsCompact K ∧ ∀ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  first | exact @GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | exact GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | (intros; apply GlobalTheory.AdeleCocompactExt.exists_compact_adeleE <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finitePlaceComponent_adeleNorm_eq_localNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    evFin F v (Algebra.norm (AF F) x) = Algebra.norm (Fv F v) (compFin F E v x) := by
  first | exact @GlobalTheory.NormAtPlace.evFin_norm_eq | exact GlobalTheory.NormAtPlace.evFin_norm_eq | (intros; apply GlobalTheory.NormAtPlace.evFin_norm_eq <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)


theorem _root_.GlobalTheory.T.skew_determinant_ne_zero_first_space : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsSkew σ B r s → X.J.det ≠ 0 := by
  first | exact @GlobalTheory.SkewGram.det_ne_zero | exact GlobalTheory.SkewGram.det_ne_zero | (intros; apply GlobalTheory.SkewGram.det_ne_zero <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)


theorem _root_.GlobalTheory.T.symplectic_form_restricted_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (JW₁ : Matrix (Fin d₁) (Fin d₁) E)
    (ι : Matrix (Fin d) (Fin d₁) E), ιᵀ * JW * ι.map σ = JW₁ → ∀ z z' : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (1 : Matrix (Fin n) (Fin n) E) * z * ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι)ᵀ)
        ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (1 : Matrix (Fin n) (Fin n) E) * z' * ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι)ᵀ) = symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW₁) z z' := by
  first | exact @GlobalTheory.MixedLagrGram.symp_restrict_gram | exact GlobalTheory.MixedLagrGram.symp_restrict_gram | (intros; apply GlobalTheory.MixedLagrGram.symp_restrict_gram <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.skewHermitian_det_eq_unit_mul_norm_at_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → Even n →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∃ (y : Fv F v ⊗[F] E) (u : Fv F v), Valued.v u = 1 ∧
      (1 : Fv F v) ⊗ₜ[F] W.J.det = algebraMap (Fv F v) (Fv F v ⊗[F] E) u *
        (y * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ y) := by
  first | exact @GlobalTheory.SkewDetParity.det_eq_unit_mul_norm | exact GlobalTheory.SkewDetParity.det_eq_unit_mul_norm | (intros; apply GlobalTheory.SkewDetParity.det_eq_unit_mul_norm <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.standardAddChar_archimedean_eq_exp_nondegenerate : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧ ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0 := by
  first | exact @GlobalTheory.StdBeta.stdBeta | exact GlobalTheory.StdBeta.stdBeta | (intros; apply GlobalTheory.StdBeta.stdBeta <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.distribHaarChar_supportedIdele_eq_localAbsValue : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (u : (AF F)ˣ), At (evFin F v) ((u : AF F) - 1) →
    ((MeasureTheory.distribHaarChar (AF F) u : NNReal) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) (Units.map (evFin F v : AF F →* Fv F v) u) := by
  first | exact @GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at | exact GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at | (intros; apply GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.dense_invertible_antidiagonal_corner_doubledUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ g : UG (cA σ) (dbl (incM F J)), g ∈ closure {h : UG (cA σ) (dbl (incM F J)) | ∃ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * diagCols (Fin n) = diagCols (Fin n) * t.1 ∧ IsUnit (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (-1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((h * p).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (-1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))).det} := by
  first | exact @GlobalTheory.SiegelDense.dense | exact GlobalTheory.SiegelDense.dense | (intros; apply GlobalTheory.SiegelDense.dense <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_unitary_determined_by_split_image : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂ := by
  first | exact @GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq | exact GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq | (intros; apply GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)


theorem _root_.GlobalTheory.T.integral_adelicGL_mulVec_haar_eq_modulus_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ, ∫ u, f ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ u) ∂μ =
      (((distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ u, f u ∂μ := by
  first | exact @GlobalTheory.JacSubst.integral_mulVec | exact GlobalTheory.JacSubst.integral_mulVec | (intros; apply GlobalTheory.JacSubst.integral_mulVec <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.LagrFormNZ

theorem exists_leftInv {F : Type} [Field F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (ha : LinearIndependent F a) : ∃ C : Matrix (Fin r) κ F, ∀ j, C *ᵥ a j = Pi.single j 1 := by
  have hinj : Function.Injective (Fintype.linearCombination F a) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp ha
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F a)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' L, fun j => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have := LinearMap.congr_fun hL (Pi.single j 1)
  simpa [Fintype.linearCombination_apply_single] using this

theorem mulVec_sum_eq {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (C : Matrix (Fin r) κ F) (hC : ∀ j, C *ᵥ a j = Pi.single j 1) (x : Fin r → AF F) :
    C.map (algebraMap F (AF F)) *ᵥ (∑ j, x j • fun k => algebraMap F (AF F) (a j k)) = x := by
  funext i
  have h1 : ∀ j, (C.map (algebraMap F (AF F)) *ᵥ fun k => algebraMap F (AF F) (a j k)) i =
      algebraMap F (AF F) ((Pi.single j (1 : F) : Fin r → F) i) := fun j => by
    rw [← hC j, RingHom.map_mulVec]; rfl
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, h1]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, Ne.symm hj]
  · simp

end GlobalTheory.LagrFormNZ

namespace GlobalTheory.LagrFormNZ

theorem lagrForm_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), LinearIndependent F (fun j => (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ ∈ schA F κ, ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
      (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0 ∂μ ≠ 0 := by
  intro F _ _ ψ hψ κ _ r u hu μ hμ
  letI : MeasurableSpace (Fin r → AF F) := borel _
  haveI : BorelSpace (Fin r → AF F) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨C, hC⟩ := exists_leftInv (fun j => (u j).1) hu
  set U : Fin r → (κ → AF F) × (κ → AF F) := fun j => ((fun k => algebraMap F (AF F) ((u j).1 k)),
    (fun k => algebraMap F (AF F) ((u j).2 k))) with hU
  set Cm : Matrix (Fin r) κ (AF F) := C.map (algebraMap F (AF F)) with hCm
  have hfst : ∀ x : Fin r → AF F, (∑ j, x j • U j).1 = ∑ j, x j • fun k => algebraMap F (AF F) ((u j).1 k) := by
    intro x; simp [U, Prod.fst_sum]
  have hleft : ∀ x : Fin r → AF F, Cm *ᵥ (∑ j, x j • U j).1 = x := fun x => by
    rw [hfst]; exact mulVec_sum_eq (fun j => (u j).1) C hC x
  have hXc : Continuous fun x : Fin r → AF F => ∑ j, x j • U j :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
  set H : (Fin r → AF F) → ℂ := fun x => ψ (0 ⬝ᵥ (∑ j, x j • U j).2 +
    ⅟(2 : AF F) * ((∑ j, x j • U j).1 ⬝ᵥ (∑ j, x j • U j).2)) with hH
  have hHc : Continuous H := hψ.1.comp ((continuous_const.dotProduct (continuous_snd.comp hXc)).add
    (continuous_const.mul ((continuous_fst.comp hXc).dotProduct (continuous_snd.comp hXc))))
  set G : (κ → AF F) → ℂ := fun y => H (Cm *ᵥ y) with hGdef
  have hGc : Continuous G := hHc.comp (Continuous.matrix_mulVec continuous_const continuous_id)
  have hG0 : G 0 = 1 := by simp [G, H]
  have hV : {y | 0 < (G y).re} ∈ 𝓝 (0 : κ → AF F) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp hGc)).mem_nhds (by simp [hG0])
  set e := GlobalTheory.ArchimedeanL2.splitEquiv F κ with he
  have he0 : e.symm (0, 0) = 0 := map_zero e.symm
  have hW : e.symm ⁻¹' {y | 0 < (G y).re} ∈ 𝓝 ((0 : κ → mixedEmbedding.mixedSpace F), (0 : κ → Af F)) := by
    have hV' : {y | 0 < (G y).re} ∈ 𝓝 (e.symm (0, 0)) := by rw [he0]; exact hV
    exact e.symm.continuous.tendsto (0, 0) hV'
  obtain ⟨U1, hU1, U2, hU2, hsub⟩ := mem_nhds_prod_iff.1 hW
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU1
  obtain ⟨c, hc0, hcs⟩ := GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds F κ U2 hU2
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  set S : Set (κ → Af F) := {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ c} with hS
  set g : (κ → Af F) → ℂ := S.indicator (fun _ => (1 : ℂ)) with hg
  have hgSB : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB F κ c hc0 0
  set φ := pureA F f g with hφ
  have hφmem : φ ∈ schA F κ := Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hφe : ∀ y, φ y = f (e y).1 * g (e y).2 := fun y => rfl
  refine ⟨φ, hφmem, ?_⟩
  have hφcases : ∀ y, φ y = ((b (e y).1 : ℝ) : ℂ) ∧ (e y).2 ∈ S ∨ φ y = 0 ∧ (e y).2 ∉ S := by
    intro y
    rw [hφe, hf]
    by_cases hq : (e y).2 ∈ S
    · left; simp [g, Set.indicator_of_mem hq, hq]
    · right; simp [g, Set.indicator_of_notMem hq, hq]
  have hφim : ∀ y, (φ y).im = 0 := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hφre : ∀ y, 0 ≤ (φ y).re := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, b.nonneg]
  have hφmemK : ∀ y, φ y ≠ 0 → (e y).1 ∈ Metric.ball (0 : κ → mixedEmbedding.mixedSpace F) δ ∧
      (e y).2 ∈ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) := by
    intro y hy
    rcases hφcases y with ⟨h, hq⟩ | ⟨h, _⟩
    · refine ⟨?_, by simpa [S] using hq⟩
      have : b (e y).1 ≠ 0 := by
        intro h0; apply hy; rw [h, h0]; simp
      have hs : (e y).1 ∈ Function.support b := this
      rw [b.support_eq] at hs
      exact hs
    · exact absurd h hy
  have hφV : ∀ y, φ y ≠ 0 → 0 < (G y).re := by
    intro y hy
    obtain ⟨h1, h2⟩ := hφmemK y hy
    have : e y ∈ U1 ×ˢ U2 := ⟨hball h1, hcs h2⟩
    have := hsub this
    simpa using this
  have hφ0 : φ 0 = 1 := by
    have e0 : e 0 = (0, 0) := map_zero e
    rw [hφe, e0, hf]
    have hb : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hδ).le)
    have h0S : (0 : κ → Af F) ∈ S := by simp [S]
    simp [g, Set.indicator_of_mem h0S, hb]
  have hφc : Continuous φ := by
    have hg : Continuous g := hgSB.1.continuous
    exact (f.continuous.comp (continuous_fst.comp e.continuous)).mul (hg.comp (continuous_snd.comp e.continuous))
  set I : (Fin r → AF F) → ℂ := fun x => schr ψ (∑ j, x j • U j) φ 0 with hIdef
  have hI : ∀ x, I x = G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := by
    intro x
    show ψ _ * φ (0 + _) = H (Cm *ᵥ _) * _
    rw [hleft, zero_add]
  have hIc : Continuous I := by
    have : I = fun x => G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := funext hI
    rw [this]
    exact (hGc.comp (continuous_fst.comp hXc)).mul (hφc.comp (continuous_fst.comp hXc))

  set K : Set ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) :=
    Metric.closedBall 0 δ ×ˢ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (GlobalTheory.EvAdm.isCompact_scaledInt_of_ne_zero hc0)
  have hKcl : IsClosed K := Metric.isClosed_closedBall.prod
    ((GlobalTheory.EvAdm.scaledInt F κ c).isClosed_of_isOpen (GlobalTheory.EvAdm.isOpen_scaledInt c))
  set T : Set (Fin r → AF F) := {x | e (∑ j, x j • U j).1 ∈ K} with hT
  have hTcl : IsClosed T := hKcl.preimage (e.continuous.comp (continuous_fst.comp hXc))
  have hTsub : T ⊆ (fun p => Cm *ᵥ e.symm p) '' K := by
    intro x hx
    exact ⟨_, hx, by simp only [e.symm_apply_apply, hleft]⟩
  have hes : Continuous (e.symm : _ → _) := e.symm.continuous
  have hcm : Continuous fun p => Cm *ᵥ e.symm p := Continuous.matrix_mulVec continuous_const hes
  have hTc : IsCompact T := (hKc.image hcm).of_isClosed_subset hTcl hTsub
  have hsupp : Function.support I ⊆ T := by
    intro x hx
    have hne : φ (∑ j, x j • U j).1 ≠ 0 := by
      intro h0; apply hx; rw [hI, h0, mul_zero]
    obtain ⟨h1, h2⟩ := hφmemK _ hne
    exact ⟨Metric.ball_subset_closedBall h1, h2⟩
  have hIcs : HasCompactSupport I := hTc.of_isClosed_subset (isClosed_tsupport I) (closure_minimal hsupp hTcl)
  have hIint : Integrable I μ := hIc.integrable_of_hasCompactSupport hIcs
  have hre : ∀ x, (I x).re = (G (∑ j, x j • U j).1).re * (φ (∑ j, x j • U j).1).re := by
    intro x; rw [hI, Complex.mul_re, hφim, mul_zero, sub_zero]
  have hnn : 0 ≤ fun x => (I x).re := by
    intro x
    show 0 ≤ (I x).re
    rw [hre]
    by_cases h0 : φ (∑ j, x j • U j).1 = 0
    · simp [h0]
    · exact mul_nonneg (hφV _ h0).le (hφre _)
  have hI0 : (I 0).re = 1 := by
    rw [hre]
    have : (∑ j, (0 : Fin r → AF F) j • U j).1 = 0 := by simp
    rw [this, hG0, hφ0]; simp
  have hpos : 0 < ∫ x, (I x).re ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hnn hIint.re]
    exact (Complex.continuous_re.comp hIc).isOpen_support.measure_pos μ ⟨0, by simp [Function.mem_support, hI0]⟩
  intro hzero
  have := integral_re hIint
  change ∫ x, (I x).re ∂μ = (∫ x, I x ∂μ).re at this
  rw [show (∫ x, I x ∂μ) = 0 from hzero, Complex.zero_re] at this
  exact hpos.ne' this

end GlobalTheory.LagrFormNZ
end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {m n : ℕ}

abbrev cAl (D : D7) : AE D →ₐ[AF D.host.F] AE D := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig

abbrev UD (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) : Type := UA D.sp.cm.sig J

theorem cAl_eq (z : AE D) : cAl D z = cA D z := GlobalTheory.IwLine.cA_eq_sigR _ z

variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n}

section Witt

variable {J : Matrix (Fin n) (Fin n) D.host.E}

theorem trA_cA (z : AE D) : StdUnn.trA (cA D z) = StdUnn.trA z := by
  let e : AE D ≃ₐ[AF D.host.F] AE D := AlgEquiv.ofAlgHom (cAl D) (cAl D)
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
  rw [← cAl_eq]
  exact Algebra.trace_eq_of_algEquiv e z

theorem trA_inner_comm (V : HSp D) (x y : Mx D V.rank n) :
    StdUnn.trA (Matrix.trace (StdUnn.inner V x y)) = StdUnn.trA (Matrix.trace (StdUnn.inner V y x)) := by
  rw [← trA_cA, ← trace_adj, StdUnn.inner, StdUnn.inner, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

end Witt

end GlobalTheory.SWLink

end
end
