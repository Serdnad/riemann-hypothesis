module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFrameCharacterFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle518
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
noncomputable section
namespace GlobalTheory.RealLift.CharTrace
open scoped Matrix
open GlobalTheory.RealLift.OneParam
variable {R S : ℕ}
theorem deriv_characterTrace_realLift : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ ν : UG (cA σ) J → ℂ,
      (∀ g h : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) →
      ContinuousOn ν {g : UG (cA σ) J | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} →
      (∀ g : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0) →
      ∃ k : InfinitePlace F → ℂ, ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGen τ C γ Y →
        HasDerivAt (fun t : ℝ => ν (γ (Multiplicative.ofAdd t))) (∑ w, k w * (Y w).trace) 0 := by
  intro _ F E _ _ _ _ _ σ β _ _ R S τ J b C hCM hC ν hmul hcont hne
  have := hCM.1
  obtain ⟨ξ, hξ⟩ := exists_moved hCM
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hCM hξ (τ w).1
  choose C' hC' using fun w => (hC w).2
  have hL : ∀ w, C' w * C w = 1 := fun w => frame_inv (hC w).1 (hC' w)
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  set U : Set (InfinitePlace F → Mat R S) := {h | ∀ w, (h w)ᴴ * Jm R S * h w = Jm R S} with hU
  set Λ : (InfinitePlace F → Mat R S) → Matrix β β (AE F E) :=
    fun h => 1 + liftM τ ξ (fun w => C w * h w * C' w - 1) with hΛ
  have Λπ : ∀ h w, (Λ h).map (piInf (τ w)) = C w * h w * C' w := fun h w => by
    rw [hΛ, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ', add_sub_cancel]
  have Λat : ∀ h, At (evI F) (Λ h - 1) := fun h => by
    rw [hΛ, add_sub_cancel_left]
    exact at_liftM τ ξ _
  have Λmul : ∀ h h', Λ (h * h') = Λ h * Λ h' := fun h h' => by
    refine (eq_of_at hCM τ ?_ fun w => ?_).symm
    · have e : Λ h * Λ h' - Λ (h * h') = (Λ h - 1) * Λ h' + (Λ h' - 1) - (Λ (h * h') - 1) := by noncomm_ring
      rw [e]
      exact at_sub (at_add (at_mul_right (Λat h) _) (Λat h')) (Λat _)
    · rw [Matrix.map_mul, Λπ, Λπ, Λπ, Pi.mul_apply]
      calc C w * h w * C' w * (C w * h' w * C' w) = C w * h w * (C' w * C w) * h' w * C' w := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have Λone : Λ 1 = 1 := eq_of_at hCM τ (Λat 1) fun w => by
    rw [Λπ, Pi.one_apply, Matrix.mul_one, hC' w, Matrix.map_one _ (map_zero _) (map_one _)]
  have ΛU : ∀ h ∈ U, (Λ h)ᵀ * J * (Λ h).map (cA σ) = J := fun h hh => by
    refine eq_of_at hCM τ ?_ fun w => ?_
    · have e : (Λ h)ᵀ * J * (Λ h).map (cA σ) - J =
          (Λ h - 1)ᵀ * J * (Λ h).map (cA σ) + J * (Λ h - 1).map (cA σ) := by
        have e1 : (Λ h - 1).map (cA σ) = (Λ h).map (cA σ) - 1 := by
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      exact at_add (at_mul_right (at_mul_right (at_transpose (Λat h)) _) _)
        (at_mul_left (at_map_cA σ (Λat h)) _)
    · have hc : ((Λ h).map (cA σ)).map (piInf (τ w)) = (C w * h w * C' w).map star := by
        rw [← Λπ h w, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, Λπ]
      by_cases hb : b = 0
      · haveI := isEmpty_of_zero (hb ▸ (hC w).1) (hC' w)
        ext i
        exact isEmptyElim i
      · have h1 := conj_unit (hC w).1 (hC' w) ((form_iff (h w)).1 (hh w))
        rw [Matrix.mul_smul, Matrix.smul_mul] at h1
        exact smul_right_injective _ hb h1
  set hinv : (InfinitePlace F → Mat R S) → InfinitePlace F → Mat R S :=
    fun h w => Jm R S * (h w)ᴴ * Jm R S with hhinv
  have inv_mul : ∀ h ∈ U, hinv h * h = 1 := fun h hh => by
    funext w
    rw [Pi.mul_apply, hhinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Jm R S) (h w), hh w,
      _root_.GlobalTheory.RealLift.OneParam.jm_mul_self, Pi.one_apply]
  have mul_inv : ∀ h ∈ U, h * hinv h = 1 := fun h hh => by
    funext w
    have := congrFun (inv_mul h hh) w
    rw [Pi.mul_apply, Pi.one_apply] at this ⊢
    exact mul_eq_one_comm.1 this
  have Λinv1 : ∀ h ∈ U, Λ h * Λ (hinv h) = 1 := fun h hh => by rw [← Λmul, mul_inv h hh, Λone]
  have Λinv2 : ∀ h ∈ U, Λ (hinv h) * Λ h = 1 := fun h hh => by rw [← Λmul, inv_mul h hh, Λone]
  let G : U → UG (cA σ) J := fun h => ⟨⟨Λ h, Λ (hinv h), Λinv1 h h.2, Λinv2 h h.2⟩, ΛU h h.2⟩
  have LevelValuationRings : ∀ h, At (evI F) (((G h).1 : Matrix β β (AE F E)) - 1) := fun h => Λat h
  have Gmul : ∀ h h' : U, ∀ hm : (h : InfinitePlace F → Mat R S) * h' ∈ U, G ⟨_, hm⟩ = G h * G h' :=
    fun h h' hm => Subtype.ext (Units.ext (Λmul h h'))
  have Λc : Continuous Λ := continuous_const.add ((continuous_liftM τ ξ).comp (continuous_pi fun w =>
    (((continuous_const.matrix_mul (continuous_apply w)).matrix_mul continuous_const).sub continuous_const)))
  have hinvc : Continuous hinv := continuous_pi fun w =>
    (continuous_const.matrix_mul (continuous_apply w).matrix_conjTranspose).matrix_mul continuous_const
  have Gc : Continuous G := by
    have hu : Continuous fun h : U => ((G h).1 : GL β (AE F E)) :=
      Units.continuous_iff.2 ⟨Λc.comp continuous_subtype_val, (Λc.comp hinvc).comp continuous_subtype_val⟩
    exact hu.subtype_mk _
  classical
  let χ : (InfinitePlace F → Mat R S) → ℂ := fun h => if hh : h ∈ U then ν (G ⟨h, hh⟩) else 0
  have χG : ∀ h : U, χ h = ν (G h) := fun h => by simp only [χ, dif_pos h.2]
  have memU : ∀ h h' : InfinitePlace F → Mat R S, h ∈ U → h' ∈ U → h * h' ∈ U := fun h h' hh hh' w =>
    mem_mul (hh w) (hh' w)
  obtain ⟨n, hn⟩ := prod_char (R := R) (S := S) χ
    (fun g h hg hh => by
      rw [χG ⟨g, hg⟩, χG ⟨h, hh⟩, χG ⟨g * h, memU g h hg hh⟩, Gmul ⟨g, hg⟩ ⟨h, hh⟩]
      exact hmul _ _ (LevelValuationRings _) (LevelValuationRings _))
    (by
      rw [continuousOn_iff_continuous_restrict]
      convert hcont.comp_continuous Gc LevelValuationRings using 1
      funext h
      exact χG h)
    (fun g hg => by rw [χG ⟨g, hg⟩]; exact hne _ (LevelValuationRings _))
  refine ⟨fun w => (n w : ℂ), fun γ hγ Y hY => ?_⟩
  set e : ℝ → InfinitePlace F → Mat R S := fun t w => NormedSpace.exp (t • Y w) with he
  have hγw : ∀ t w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = C w * e t w * C' w :=
    fun t w => by
      rw [he]; simp only
      rw [← hY t w, Matrix.mul_assoc, hC' w, Matrix.mul_one]
  have heU : ∀ t, e t ∈ U := fun t w => by
    rw [form_iff]
    set g := ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) with hg
    have hgU : gᵀ * (b • J.map (piInf (τ w))) * g.map star = b • J.map (piInf (τ w)) := by
      have hu : ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))ᵀ * J *
          ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (cA σ) = J := (γ (Multiplicative.ofAdd t)).2
      have := congrArg (fun X => X.map (piInf (τ w))) hu
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      have hc : (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (cA σ)).map (piInf (τ w)) = g.map star := by
        rw [hg, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [hc] at this
      rw [Matrix.mul_smul, Matrix.smul_mul, this]
    have hee : e t w = C' w * g * C w := by
      rw [hg, hγw, Matrix.mul_assoc, Matrix.mul_assoc, hL, Matrix.mul_one, ← Matrix.mul_assoc, hL, Matrix.one_mul]
    have t1 : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC' w, Matrix.transpose_one]
    have t2 : (C w).map star * (C' w).map star = 1 := by
      rw [← map_star_mul, hC' w]; exact Matrix.map_one _ (star_zero _) (star_one _)
    rw [hee, ← (hC w).1]
    calc (C' w * g * C w)ᵀ * ((C w)ᵀ * (b • J.map (piInf (τ w))) * (C w).map star) * (C' w * g * C w).map star
        = (C w)ᵀ * (gᵀ * (((C' w)ᵀ * (C w)ᵀ) * (b • J.map (piInf (τ w))) * ((C w).map star * (C' w).map star)) *
            g.map star) * (C w).map star := by
          rw [map_star_mul, map_star_mul, Matrix.transpose_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = (C w)ᵀ * (b • J.map (piInf (τ w))) * (C w).map star := by
          rw [t1, t2, Matrix.one_mul, Matrix.mul_one, hgU]
  have hγe : ∀ t, γ (Multiplicative.ofAdd t) = G ⟨e t, heU t⟩ := fun t => by
    refine Subtype.ext (Units.ext (eq_of_at hCM τ ?_ fun w => ?_))
    · have e1 : ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - Λ (e t) =
          (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) - (Λ (e t) - 1) := by abel
      show At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - Λ (e t))
      rw [e1]
      exact at_sub (hγ.2 _) (Λat _)
    · show ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = (Λ (e t)).map (piInf (τ w))
      rw [hγw, Λπ]
  have hval : ∀ t : ℝ, ν (γ (Multiplicative.ofAdd t)) =
      Complex.exp ((t : ℂ) * ∑ w, (n w : ℂ) * (Y w).trace) := fun t => by
    rw [hγe t, ← χG, hn _ (heU t), Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [he]; simp only
    rw [GlobalTheory.DetSqrtCover.det_exp, ← Complex.exp_int_mul, Matrix.trace_smul]
    congr 1
    simp only [Complex.real_smul]
    ring
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ∑ w, (n w : ℂ) * (Y w).trace))
      (∑ w, (n w : ℂ) * (Y w).trace) 0 := by
    have h0 := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (∑ w, (n w : ℂ) * (Y w).trace)).cexp
    simpa using h0
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hval)
end GlobalTheory.RealLift.CharTrace
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.realLift_characterTrace_hasDerivAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ ν : UG (cA σ) J → ℂ,
      (∀ g h : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) →
      ContinuousOn ν {g : UG (cA σ) J | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} →
      (∀ g : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0) →
      ∃ k : InfinitePlace F → ℂ, ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGen τ C γ Y →
        HasDerivAt (fun t : ℝ => ν (γ (Multiplicative.ofAdd t))) (∑ w, k w * (Y w).trace) 0 := by
  first | exact @_root_.GlobalTheory.RealLift.CharTrace.deriv_characterTrace_realLift | exact _root_.GlobalTheory.RealLift.CharTrace.deriv_characterTrace_realLift | (intros; apply _root_.GlobalTheory.RealLift.CharTrace.deriv_characterTrace_realLift <;> assumption)
end
end

section

section
noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl
namespace GlobalTheory.RealLift.LieSecondPf
theorem lie_second_order_of_real_lift : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DerEx → FockEx → VacLine → LieScalar → LieSecond := by
  intro _ hD hF hV hL F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om χ m hCM hψ hFr hΦ hW hχ
  obtain ⟨hU, dd, omd, hdd, hWS, hres⟩ := hW
  obtain ⟨c, hc⟩ := hL F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hU
  have hFrd := GlobalTheory.T.doubled_hermitian_space_frame_of_frame F E α β P Q R S τ JA JB a b A C hFr
  obtain ⟨Φd, hΦd⟩ := hF F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) hCM hψ hFrd
  obtain ⟨cd, hcd⟩ := hL F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) Φd omd hCM hψ hFrd hΦd hWS.2.1
  have key : ∀ w (Y : Mat R S), c w * Y.trace = (m w : ℂ) / 2 * Y.trace := by
    intro w Y
    rcases Nat.eq_zero_or_pos (R + S) with h0 | hpos
    · have hR : R = 0 := by omega
      have hS : S = 0 := by omega
      subst hR hS
      have : Y.trace = 0 := by simp [Matrix.trace]
      rw [this, mul_zero, mul_zero]
    · have hbox := GlobalTheory.T.doubledFockVacuum_eq_smul_vacuum_mul_conj hD hV F E σ α β κ P Q R S ψ τ JA JB d dd a b A C Φ Φd hCM hψ hFr hΦ hdd hΦd
      have hl := GlobalTheory.T.diagonal_integral_invariant_form_diagonalLagrangian F E σ α β κ ψ JA JB d dd hψ hdd
      have hne : (∫ x : κ → mixedEmbedding.mixedSpace F,
          Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 := by
        obtain ⟨z, hz, hzx⟩ := hbox
        have h1 : ∀ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x) =
            z * (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x * star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x)) := by
          intro x
          rw [hzx, Sum.elim_comp_inl, Sum.elim_comp_inr, mul_assoc]
        simp_rw [h1]
        rw [MeasureTheory.integral_const_mul]
        refine mul_ne_zero hz (GlobalTheory.T.archimedeanSchwartz_integral_mul_star_ne_zero F κ _ ?_)
        intro h0
        exact GlobalTheory.T.tprod_constant_polynomials_ne_zero F P Q R S (hΦ.1 (by rw [h0, map_zero]))
      have h1 := GlobalTheory.T.doubledSpace_splitting_constant_half_realPlaces F E σ α β κ P Q R S ψ τ JA JB dd a b A C Φd omd χ m cd hCM hψ hFr hWS hχ hcd hl hne hpos w
      have h2 := GlobalTheory.T.realPlace_splittingConstant_eq_doubledSpace F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ Φd om omd c cd hCM hψ hΦ hres hc hcd hbox hpos w
      rw [h2, h1]
  intro γ hγ Y hY T
  have e : (fun w => fockAct2 P Q R S (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • (1 : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))) =
      fun w => fockAct2 P Q R S (Y w) + (c w * (Y w).trace) • 1 := by
    funext w
    rw [key w (Y w)]
  have := hc γ hγ Y hY T
  rw [← e] at this
  exact this
end GlobalTheory.RealLift.LieSecondPf
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.real_lift_lie_second_order : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := by
  first | exact @_root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift | exact _root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift | (intros; apply _root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftGrowthDef
theorem lift_moderate_growth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC T, ‖(l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν)) (x * g)‖ ≤ C * normInf θ T g ^ N := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 _ hom hθ hΦ hS hT hν h𝓕 hφ
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) →
      ∃ L : ℂ →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L x)) ∧
        l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) =
          GlobalTheory.DefLift.lift om ν 𝓕 (fun g => L (φ g)) := by
    intro l hl
    induction l with
    | nil =>
      refine ⟨LinearMap.toSpanSingleton ℂ _ Φ, fun x => ?_, ?_⟩
      · exact Formalism.IndefR.Fin.theta_smul S T x hΦ
      · funext h
        simp only [List.foldr_nil, GlobalTheory.DefLift.lift, LinearMap.toSpanSingleton_apply, thetaKO, map_smul,
          Pi.smul_apply, smul_eq_mul, mul_comm]
    | cons p l ih =>
      obtain ⟨L, hL, e⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      obtain ⟨-, hd⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
        hφ.cont hφ.left ν 𝓕 hν h𝓕
      obtain ⟨L', hL', -, hder⟩ := hd p.1 p.2 (hl p List.mem_cons_self)
      refine ⟨L', hL', ?_⟩
      rw [List.foldr_cons, e]
      funext g
      exact (hder g).deriv
  refine ⟨0, fun l hl x => ?_⟩
  obtain ⟨L, hL, e⟩ := key l hl
  obtain ⟨⟨hc, hinv⟩, -⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
    hφ.cont hφ.left ν 𝓕 hν h𝓕
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact T hT
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun g _ => ?_⟩
  rw [e, pow_zero, mul_one]
  obtain ⟨γ, hγ, c, hc', hxc⟩ := hcov (x * g)
  rw [hxc, hinv γ hγ c]
  exact hM c hc'
end GlobalTheory.LiftGrowthDef
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_lift_moderate_growth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC T, ‖(l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν)) (x * g)‖ ≤ C * normInf θ T g ^ N := by
  first | exact @_root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth | exact _root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth | (intros; apply _root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ThetaFinRelDef
open GlobalTheory.SquareComm
open scoped ComplexOrder
theorem theta_integral_finite_relation_eq_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X), GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0) → ∀ (ν : Measure (GA D M)) (𝓕 : Set (GA D M)), IsHaarFD M ν 𝓕 → ∀ Φ ∈ finRel ω (algF ψ θ false A B), thetaInt ω ν 𝓕 Φ = 0 := by
  intro _ D ψ θ hψ hθ M X A B χ χ' ω hω hsig ν 𝓕 hF
  have hω' : IsWeilDatumO ψ M X χ χ' ω := hω
  have hpd : ∀ τ, (gramAt D M τ).PosDef := fun τ => GlobalTheory.Core.CoefGram.posDef_of_hasSignature _ (hsig τ)
  have hcc : GlobalTheory.Unf.CoCpt M := (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D M).2 hpd
  have hth : ∀ Φ ∈ algF ψ θ false A B, IsThetaFunO ψ M X Φ := fun Φ hΦ =>
    GlobalTheory.SquareComm.ThetaLeft.isThetaFunO_of_mem_algF hψ hθ A B hΦ
  have hleft := GlobalTheory.SquareComm.ThetaLeft.main D ψ θ hθ M X A B χ χ' ω hω
  have hsub : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ - Ψ) = thetaKO ω g k Φ - thetaKO ω g k Ψ := by
    intros; simp [thetaKO, map_sub]
  have hadd : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ + Ψ) = thetaKO ω g k Φ + thetaKO ω g k Ψ := by
    intros; simp [thetaKO, map_add (f := _)]
  have hsmul : ∀ g k (c : ℂ) (Φ : WO M X → ℂ), thetaKO ω g k (c • Φ) = c * thetaKO ω g k Φ := by
    intros; simp [thetaKO, map_smul]
  have hzero : ∀ g k, thetaKO ω g k (0 : WO M X → ℂ) = 0 := by
    intros; simp [thetaKO]
  have hint : ∀ Φ ∈ algF ψ θ false A B, ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
    intro Φ hΦ h
    exact (GlobalTheory.Unf.contAut_rapidDec_bounded_integrable D M hcc _
      ⟨fun γ hγ g => hleft Φ hΦ γ hγ g h, (hω'.om_cont Φ (hth Φ hΦ) 0).comp (Continuous.prodMk_left h)⟩).2.2
      ⟨ν, 𝓕, hF.1, hF.2⟩
  intro Φ hΦ
  suffices key : (∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν) ∧ thetaInt ω ν 𝓕 Φ = 0 from key.2
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, -, Ψ, hΨ, rfl⟩ := hx
    have e : ∀ g k, thetaKO ω g k (ω (u, 1) Ψ) = thetaKO ω (g * u) k Ψ := fun g k => by
      unfold thetaKO
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    have tr := fun k => integral_rightTranslate hF (f := fun g => thetaKO ω g k Ψ)
      (fun γ hγ g => hleft Ψ hΨ γ hγ g k) u
    have i1 : ∀ k, IntegrableOn (fun g => thetaKO ω g k (ω (u, 1) Ψ)) 𝓕 ν := fun k => by
      simp only [e]; exact (tr k).1.2 (hint Ψ hΨ k)
    refine ⟨fun k => ?_, ?_⟩
    · simp only [hsub]; exact (i1 k).sub (hint Ψ hΨ k)
    · funext k
      simp only [thetaInt, hsub, Pi.zero_apply]
      rw [integral_sub (i1 k) (hint Ψ hΨ k)]
      simp only [e]
      rw [(tr k).2, sub_self]
  | zero =>
    exact ⟨fun k => by simp only [hzero]; exact integrableOn_zero, by funext k; simp [thetaInt, hzero]⟩
  | add x y _ _ hx hy =>
    refine ⟨fun k => by simp only [hadd]; exact (hx.1 k).add (hy.1 k), ?_⟩
    funext k
    have := integral_add (hx.1 k) (hy.1 k)
    have ex := congrFun hx.2 k
    have ey := congrFun hy.2 k
    simp only [thetaInt, Pi.zero_apply] at ex ey
    simp only [thetaInt, hadd, Pi.zero_apply, this, ex, ey, add_zero]
  | smul c x _ hx =>
    refine ⟨fun k => by simp only [hsmul]; exact (hx.1 k).const_mul c, ?_⟩
    funext k
    have ex := congrFun hx.2 k
    simp only [thetaInt, Pi.zero_apply] at ex
    simp only [thetaInt, hsmul, Pi.zero_apply, integral_const_mul, ex, mul_zero]
end GlobalTheory.ThetaFinRelDef
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X), GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0) → ∀ (ν : Measure (GA D M)) (𝓕 : Set (GA D M)), IsHaarFD M ν 𝓕 → ∀ Φ ∈ finRel ω (algF ψ θ false A B), thetaInt ω ν 𝓕 Φ = 0 := by
  first | exact @_root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero | exact _root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero | (intros; apply _root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TripleWeilTransfer
variable {D : D7}
theorem triple_exists_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → (∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') → ∀ (ωA : GlobalTheory.Grid.WRep W X) (ωB : GlobalTheory.Grid.WRep W₁ X), GlobalTheory.Grid.IsWeil ψ true W X β (β / α) ωA → GlobalTheory.Grid.IsWeil ψ false W₁ X α (α / β) ωB → ∃ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  intro _ _ _ _ D ψ θ hψ hθ W W₁ X A A₁ B α β _ ⟨ωA₀, ωB₀, Pi, rf, rl, p, p', hm⟩ ωA ωB hA hB
  refine ⟨Pi, rf, rl, p, p', hA, hB, hm.irred, ?_, ?_⟩
  · exact isCoinvMap_congr (fun q Φ hΦ => eq_on_theta true hm.weilA hA q Φ (isThetaFunO_of_mem_algF hψ hθ true A B hΦ))
      hm.mapA
  · exact isCoinvMap_congr (fun q Φ hΦ => eq_on_theta false hm.weilB hB q Φ (isThetaFunO_of_mem_algF hψ hθ false A₁ B hΦ))
      hm.mapB
end GlobalTheory.TripleWeilTransfer
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.triple_weil_transfer_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → (∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') → ∀ (ωA : GlobalTheory.Grid.WRep W X) (ωB : GlobalTheory.Grid.WRep W₁ X), GlobalTheory.Grid.IsWeil ψ true W X β (β / α) ωA → GlobalTheory.Grid.IsWeil ψ false W₁ X α (α / β) ωB → ∃ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  first | exact @_root_.GlobalTheory.TripleWeilTransfer.triple_exists_matching | exact _root_.GlobalTheory.TripleWeilTransfer.triple_exists_matching | (intros; apply _root_.GlobalTheory.TripleWeilTransfer.triple_exists_matching <;> assumption)
end
end
