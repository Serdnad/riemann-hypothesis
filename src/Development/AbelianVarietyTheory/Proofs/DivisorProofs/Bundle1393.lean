module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHyperbolicSwapExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSkewHermitianCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
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
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.local_norm_unramified_factorization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (z - 1) →
    At (evFin F v) (Algebra.norm (AF F) z - 1) ∧ evFin F v (Algebra.norm (AF F) z) = piW τ z * piW (τ.comp σ) z := by
  first | exact @GlobalTheory.NormLocSplit.norm_at_split | exact GlobalTheory.NormLocSplit.norm_at_split | (intros; apply GlobalTheory.NormLocSplit.norm_at_split <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.isUnit_det_gram_skewHermitian_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d : ℕ) (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s → IsUnit W.J.det := by
  first | exact @GlobalTheory.SkewUnit.isUnit_det_of_isSkew | exact GlobalTheory.SkewUnit.isUnit_det_of_isSkew | (intros; apply GlobalTheory.SkewUnit.isUnit_det_of_isSkew <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.measurable_theta_sum_of_schrodinger : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)) := by
  first | exact @GlobalTheory.ThetaTransformMeas.main | exact GlobalTheory.ThetaTransformMeas.main | (intros; apply GlobalTheory.ThetaTransformMeas.main <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.unramified_character_at_uniformizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), UnrAt χ (splitPrime t) → chrW χ t (unifAt v) = val χ (splitPrime t) := by
  first | exact @GlobalTheory.ChrWUnif.chrW_unifAt | exact GlobalTheory.ChrWUnif.chrW_unifAt | (intros; apply GlobalTheory.ChrWUnif.chrW_unifAt <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.archHeisenbergDerivative_additive_commutator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (D : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (SInf F κ →L[ℂ] SInf F κ)),
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    (∀ u u', At (evI F) u → At (evI F) u' → D (u + u') = D u + D u') ∧
    (∀ u (r : ℝ), At (evI F) u → D (realAd F r • u) = (r : ℂ) • D u) ∧
    (∀ u u', At (evI F) u → At (evI F) u' → ∀ f, D u (D u' f) - D u' (D u f) =
      ((-2 * Real.pi * Complex.I : ℂ) *
        ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) : ℝ) : ℂ)) • f) := by
  first | exact @GlobalTheory.HeisDerivLaws.heis_deriv_laws | exact GlobalTheory.HeisDerivLaws.heis_deriv_laws | (intros; apply GlobalTheory.HeisDerivLaws.heis_deriv_laws <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaSobolevBase

open scoped Classical SchwartzMap ENNReal

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


variable (F) in
def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evHom_invOf_two [Invertible (2 : AF F)] :
    evHom F (⅟(2 : AF F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
  have h2 : evHom F (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evHom F) 2, ← map_mul, invOf_mul_self, map_one]
  calc evHom F (⅟(2 : AF F)) = evHom F (⅟(2 : AF F)) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (2 * (1 / 2)) := by
        rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, map_one, mul_one]
    _ = (evHom F (⅟(2 : AF F)) * 2) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
        rw [map_mul, map_ofNat]; ring
    _ = _ := by rw [h2, one_mul]

def sumPure {ι : Type} [Fintype ι] (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : ι → SInf F κ) : (κ → AF F) → ℂ :=
  ∑ i, pureA F (f i) (g i)

theorem exists_sumPure {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ (n : ℕ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin n → SInf F κ), (∀ i, g i ∈ SB _) ∧
      Φ = sumPure g f := by
  obtain ⟨n, c, p, hp⟩ := Submodule.mem_span_set'.1 hΦ
  choose f g hg he using fun i => (p i).2
  refine ⟨n, g, fun i => c i • f i, hg, ?_⟩
  rw [← hp, sumPure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he i, ← GlobalTheory.WeilAdm.pureA_smul]
  rfl

theorem memLp_pureA (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (f : SInf F κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB _) :
    MemLp (pureA F f g) 2 μ := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.WeilAdm.HaarSplit.volume_isAddHaar F κ
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  obtain ⟨ν, hν, C, c, hC, -, -, h, -⟩ := GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds F κ g hg ⊤ isOpen_univ
  have hc : Continuous (pureA F f g) := by
    have h1 := GlobalTheory.WeilAdm.HaarSplit.continuous_comp_splitE F κ (pureA F f g)
      (Submodule.subset_span ⟨f, g, hg, rfl⟩)
    have h2 := h1.comp (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)
    convert h2 using 1
    funext x
    simp
  have hf : ∫⁻ z, ‖f z‖ₑ ^ 2 < ⊤ := by
    have := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (p := 2)
      (by norm_num) (by norm_num) (f.memLp 2 volume)
    simpa using this
  have hν2 : MemLp (pureA F f g) 2 ν := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (by norm_num) (by norm_num) hc.aestronglyMeasurable]
    have := (h f).trans_lt (ENNReal.mul_lt_top hC.lt_top hf)
    simpa using this
  rw [Measure.isAddLeftInvariant_eq_smul μ ν]
  exact hν2.smul_measure ENNReal.coe_ne_top

end GlobalTheory.ThetaSobolevBase

end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl


theorem _root_.GlobalTheory.T.diagonal_integral_invariant_form_diagonalLagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  first | exact @GlobalTheory.RealLift.diagLagr_invForm | exact GlobalTheory.RealLift.diagLagr_invForm | (intros; apply GlobalTheory.RealLift.diagLagr_invForm <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HeisTransport

theorem actsD_heisLine_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ →
      ActsD (evI F) (M.heisLine B.ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil g hg h hh T hT hTi u hu f f₁ hf
  have hS := IsUWeilPair.isUSplitting hWeil
  set ψ := B.ψ with hψ
  set p : UA σ X.J × UA σ W.J := (g, h) with hp

  have hrest : ∀ (φ : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Af F) →
      Rest (evI F) (⇑φ) (fun x => g' (fun i => (x i).2)) := by
    intro φ g' hg'
    refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨φ, g', hg', rfl⟩⟩
    change g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
  have hpure : ∀ (φ : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Af F) →
      om p (pureA F φ g') = pureA F (T φ) g' := fun φ g' hg' => hT φ _ (hrest φ g' hg')

  have h0 : ∀ v : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ t : ℝ, M.heisLine ψ v t 0 = 0 := by
    intro v t
    funext x
    simp [Model.heisLine, Darboux.rho, schr]

  obtain ⟨D, hD⟩ := GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hB.std
  have hSDD := (hD u hu f).1
  have hL := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₁ (D u f)
  have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (D u f) f₁).1 _ (h0 u) hSDD
  have hf₁ : f₁ = D u f := hL.2.2.1 _ hf hAD
  rw [← hf₁] at hSDD

  have himpl : ∀ t : ℝ, ∀ Φ ∈ schA F (Fin n × Fin d),
      M.heisLine ψ (mat g * u * (mat h).transpose) t (om p Φ) = om p (M.heisLine ψ u t Φ) := by
    intro t Φ hΦ
    have e := hS.impl p (realAd F t • u) Φ hΦ
    simp only [Model.heisLine]
    rw [e]
    congr 2
    simp only [actAB, hp, mat, Matrix.mul_smul, Matrix.smul_mul]

  have hSD : GlobalTheory.RealLift.SD (M.heisLine ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
    intro g' hg' l hl
    have hΦ : pureA F (⇑f) g' ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g', hg', rfl⟩
    have e : (fun t => l (M.heisLine ψ (mat g * u * (mat h).transpose) t (pureA F (⇑(T f)) g'))) =
        fun t => (l ∘ₗ om p) (M.heisLine ψ u t (pureA F (⇑f) g')) := by
      funext t
      rw [← hpure f g' hg', himpl t _ hΦ]
      rfl
    rw [e, ← hpure f₁ g' hg']
    exact hSDD g' hg' (l ∘ₗ om p) (hS.adm p l hl)
  exact (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (T f) (T f₁) (T f₁)).1 _ (h0 _) hSD

end GlobalTheory.HeisTransport
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertLagChar

theorem haarChar_det_mul_integral_comp_mulVec_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (m : MeasurableSpace (Fin N → k)) (hm : m = borel _)
    (ν : @Measure (Fin N → k) m) (hν : @Measure.IsAddHaarMeasure _ _ _ m ν)
    (T : GL (Fin N) k) (f : (Fin N → k) → ℂ) :
    ((distribHaarChar k (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have h2 : m = MeasurableSpace.pi := hm.trans (@BorelSpace.measurable_eq (Fin N → k) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst h2
  have hc := Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : Fin N => (Measure.addHaar : Measure k))
  rw [hc, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    ← GlobalTheory.WeilM.integral_comp_mulVec (Measure.addHaar : Measure k) T f, mul_smul_comm]

theorem nabs_det_mul_integral_comp_mulVec :
    ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ (T : GL (Fin N) (Fv F v)) (f : (Fin N → Fv F v) → ℂ),
      ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  intro F _ _ v N ν hν T f
  exact haarChar_det_mul_integral_comp_mulVec_localField (Fv F v) N _ rfl ν hν T f

end GlobalTheory.InertLagChar
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

theorem _root_.GlobalTheory.T.exists_cartanInvolution_hyperbolicSwap_extension : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), M.conjTranspose = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y = Complex.I →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    IsCartan (ιᵀ * M * ι.map star) θ₁ →
    ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ ∃ c : ℂ, c ≠ 0 ∧ Y = c • θ *ᵥ X := by
  first | exact @GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap | exact GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap | (intros; apply GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap <;> assumption)
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

theorem _root_.GlobalTheory.T.exists_isotropic_indefinite_skewHermitian_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r s : ℕ), (∀ i j, σ (J j i) = -J i j) →
    (∀ w, HasSig (Complex.I • J.map (B.emb w).1) r s) → 1 ≤ r → 1 ≤ s → 3 ≤ n →
    ∃ x : Fin n → E, x ≠ 0 ∧ form σ J x x = 0 := by
  first | exact @GlobalTheory.PlaneSkew.exists_isotropic_skew | exact GlobalTheory.PlaneSkew.exists_isotropic_skew | (intros; apply GlobalTheory.PlaneSkew.exists_isotropic_skew <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_local_GL_embedding_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ t : E →ₐ[F] Fv F v,
    ∃ K : GL (Fin a') (Fv F v) →* UA σ G.V'.J, ∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t := by
  first | exact @GlobalTheory.LeviAtPlace.levi_at_place | exact GlobalTheory.LeviAtPlace.levi_at_place | (intros; apply GlobalTheory.LeviAtPlace.levi_at_place <;> assumption)
end
