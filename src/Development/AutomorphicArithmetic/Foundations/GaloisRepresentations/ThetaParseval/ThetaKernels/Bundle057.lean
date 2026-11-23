module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle042
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle030
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle069
public import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LmOfLinBar
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle041
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle471
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.WeilBound.ThetaLifts.LatticeBasics.FarRight
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem exists_inf_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : ∃ oi, IsInfWeilF σ JS JT ξ₀ B.ψ oi ∧
    ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → ((HMF JS JT ξ₀ (tauB B)) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f :=
  _root_.PositivityTheory.ThKW.exists_inf_A_k C
theorem det_mMF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (mMF σ JS JT θ (g⁻¹, h⁻¹)).det = ∏ v, tauB B v (b ⊗ₖ aᵀ).det ∧
      (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det = ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det :=
  _root_.PositivityTheory.ThKW.det_mMF_B_k C ha hb
end PositivityTheory.ThKW
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)
namespace GlobalTheory.CompanionTheory.SiegelEisHalf
theorem eisHalf_k : _root_.SiegelEisensteinSeries.EisHalf_k := by
  intro F E _ _ _ _ _ σ B n Y r' s' hB hn hY χ _ c _ b K a hb hK ha s₁ f hf
  obtain ⟨Ê, t, hsum, hhol⟩ := _root_.GlobalTheory.T.eisenstein_series_absolute_convergence F E σ B n Y r' s' hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t₀, hmod⟩ := _root_.GlobalTheory.T.eisenstein_series_left_invariance F E σ B n Y r' s' hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t', ht, ht₀⟩ : ∃ t' : ℝ, t ≤ t' ∧ t₀ ≤ t' := ⟨max t t₀, le_max_left _ _, le_max_right _ _⟩
  have hsum' : ∀ s : ℂ, t' < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x) :=
    fun s hs => hsum s (lt_of_le_of_lt ht hs)
  obtain ⟨hmem, hcont, hbd⟩ := hmod t' Ê ht₀ hsum'
  classical
  let v : ℂ → modFun σ Y := fun s => if h : t' < s.re then ⟨fun x => Ê s x, hmem s h⟩ else 0
  have hv : ∀ s : ℂ, t' < s.re → ∀ x, (v s).1 x = Ê s x := by
    intro s h x
    simp only [v, dif_pos h]
  refine ⟨t', v, fun s h x => by rw [hv s h x]; exact hsum' s h x, ?_⟩
  have hS : IsOpen {s : ℂ | t' < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms v hS ?_ ?_ ?_
  · intro x
    exact ((hhol x).mono fun s hs => lt_of_le_of_lt ht hs).congr fun s hs => hv s hs x
  · refine hcont.congr ?_
    rintro ⟨s, x⟩ ⟨hs, -⟩
    exact hv s hs x
  · intro Q hQ hQc
    rcases Q.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, 0, by simp⟩
    obtain ⟨z₁, hz₁, hmin⟩ := hQc.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨z₂, -, hmax⟩ := hQc.exists_isMaxOn hne Complex.continuous_re.continuousOn
    obtain ⟨C, N, h⟩ := hbd z₁.re z₂.re (hQ hz₁)
    refine ⟨C, N, fun s hs x => ?_⟩
    rw [hv s (hQ hs) x]
    exact h s (hmin hs) (hmax hs) x
end GlobalTheory.CompanionTheory.SiegelEisHalf
end
end
end

section



section
noncomputable section
namespace UpperTheory.TP
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private noncomputable def mulH_pk {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n d : ℕ}
    (a : GL (Fin n) K) (c : GL (Fin d) K) : Matrix (Fin n) (Fin d) K ≃ₜ Matrix (Fin n) (Fin d) K :=
  _root_.UpperTheory.Reformulated.B.MatrixHomeomorphOfGeneralLinearPair.mulH_pk a c
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}
private theorem linBar_of_linW_pk (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (a : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (ha : a.1 * X.J.map (t.comp σ) = -1)
    (hc : (W.J.map (t.comp σ))ᵀ * c.1 = 1) {ι} (hι : M.IsLinW ψ t 1 1 ι) :
    M.IsLinBar ψ (t.comp σ) 1 1 (LinearMap.funLeft ℂ ℂ (mulH_pk a c) ∘ₗ ι) := by
  unfold Model.IsLinBar
  unfold Model.IsLinW at hι
  rw [GlobalTheory.OppLagr.comp_comp hcm]
  have cw : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      ((1 : GL (Fin n) (Fv F v))⁻¹).1 * u * ((1 : GL (Fin d) (Fv F v))⁻¹).1ᵀ = u := fun u => by simp
  have co : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      a.1 * (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map (t.comp σ) * u * (W.J.map (t.comp σ))ᵀ * (1 : GL (Fin d) (Fv F v)).1)) * c.1 = u := by
    intro u
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, Matrix.mul_assoc, hc]
    simp
  have hm : ∀ y, (mulH_pk a c) y = a.1 * y * c.1 := fun _ => rfl
  refine ⟨PositivityTheory.KCo.bij_comp hι.bij (mulH_pk a c), ?_, ?_⟩
  · intro u hu h0 φ hφ φ₁ hφ₁ hA Y
    have e := hι.trans u hu h0 φ hφ φ₁ hφ₁ hA (a.1 * Y * c.1)
    simp only [cw] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm]
    rw [e, Matrix.mul_add, Matrix.add_mul, co]
  · intro u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    have e := hι.mult u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    simp only [cw] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm]
    rw [co, e]
private theorem linW_of_linBar_pk (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (a : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (ha : a.1 = -(X.J.map (t.comp σ)))
    (hc : c.1 = (W.J.map (t.comp σ))ᵀ) {ι} (hι : M.IsLinBar ψ (t.comp σ) 1 1 ι) :
    M.IsLinW ψ t 1 1 (LinearMap.funLeft ℂ ℂ (mulH_pk a c) ∘ₗ ι) := by
  unfold Model.IsLinBar at hι
  unfold Model.IsLinW
  rw [GlobalTheory.OppLagr.comp_comp hcm] at hι
  have cw : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      ((1 : GL (Fin n) (Fv F v))⁻¹).1 * u * ((1 : GL (Fin d) (Fv F v))⁻¹).1ᵀ = u := fun u => by simp
  have co : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map (t.comp σ) * u * (W.J.map (t.comp σ))ᵀ * (1 : GL (Fin d) (Fv F v)).1) = a.1 * u * c.1 := by
    intro u
    rw [ha, hc]
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul]
  have hm : ∀ y, (mulH_pk a c) y = a.1 * y * c.1 := fun _ => rfl
  refine ⟨PositivityTheory.KCo.bij_comp hι.bij (mulH_pk a c), ?_, ?_⟩
  · intro u hu h0 φ hφ φ₁ hφ₁ hA Y
    have e := hι.trans u hu h0 φ hφ φ₁ hφ₁ hA (a.1 * Y * c.1)
    simp only [co] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm, cw]
    rw [e, Matrix.mul_add, Matrix.add_mul]
  · intro u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    have e := hι.mult u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    simp only [co] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm, cw]
    exact e
theorem exists_linW_k (B : Base F E) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    {r s r' s' : ℕ} (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ ι, M.IsLinW B.ψ t 1 1 ι := by
  have hcm : IsCMExt F E σ := hp.base.cm
  have hJX : (X.J.map (t.comp σ)).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_herm hp.herm) _
  have hJW : (W.J.map (t.comp σ)).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_skew hp.skew) _
  let P : GL (Fin n) (Fv F v) := Matrix.nonsingInvUnit (-(X.J.map (t.comp σ))) (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hJX))
  let Q : GL (Fin d) (Fv F v) := Matrix.nonsingInvUnit (W.J.map (t.comp σ))ᵀ (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_transpose]
    exact hJW))
  obtain ⟨⟨ι, hι⟩, -⟩ := _root_.PositivityTheory.KCo.dictX_proof_k F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.weil v (t.comp σ)
  exact ⟨_, linW_of_linBar_pk hcm M B.ψ t P Q rfl rfl hι⟩
theorem split_formula_k (B : Base F E) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    {r s r' s' : ℕ} (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') (v : Pl F) (t : E →ₐ[F] Fv F v) {ι} (hι : M.IsLinW B.ψ t 1 1 ι)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) (h : UA σ W.J) (hh : h ∈ UAt σ W (evFin F v))
    (g₀ : GL (Fin n) (Fv F v)) (h₀ : GL (Fin d) (Fv F v)) (eg : g₀.1 = (mat g).map (piW t)) (eh : h₀.1 = (mat h).map (piW t))
    (φ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) (φ₁) (hφ₁ : φ₁ ∈ SB (Fin n × Fin d → Fv F v))
    (hA : Acts (evFin F v) (om (g, h)) φ φ₁) :
    ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g₀ h₀ (ι φ) := by
  have hcm : IsCMExt F E σ := hp.base.cm
  have hJX : (X.J.map (t.comp σ)).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_herm hp.herm) _
  have hJW : (W.J.map (t.comp σ)).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_skew hp.skew) _
  let P : GL (Fin n) (Fv F v) := Matrix.nonsingInvUnit (-(X.J.map (t.comp σ))) (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hJX))
  let Q : GL (Fin d) (Fv F v) := Matrix.nonsingInvUnit (W.J.map (t.comp σ))ᵀ (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_transpose]
    exact hJW))
  have hPv : P.1 = -(X.J.map (t.comp σ)) := rfl
  have hQv : Q.1 = (W.J.map (t.comp σ))ᵀ := rfl
  have ha : (P⁻¹).1 * X.J.map (t.comp σ) = -1 := by
    have := Units.inv_mul P
    rw [hPv, Matrix.mul_neg] at this
    exact neg_eq_iff_eq_neg.mp this
  have hc : (W.J.map (t.comp σ))ᵀ * (Q⁻¹).1 = 1 := by rw [← hQv]; exact Units.mul_inv Q
  have hι' := linBar_of_linW_pk hcm M B.ψ t P⁻¹ Q⁻¹ ha hc hι
  obtain ⟨-, -, -, k⟩ := _root_.PositivityTheory.KCo.dictX_proof_k F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.weil v (t.comp σ)
  obtain ⟨kg, kh⟩ := k _ hι'
  let g₁ : GL (Fin n) (Fv F v) := Matrix.GeneralLinearGroup.map (piW (t.comp σ)) g.1
  let h₁ : GL (Fin d) (Fv F v) := Matrix.GeneralLinearGroup.map (piW (t.comp σ)) h.1
  obtain ⟨φ', hφ', hA', e'⟩ := kh h hh h₁ rfl φ hφ
  obtain ⟨φ'', hφ'', hA'', e''⟩ := kg g hg g₁ rfl φ' hφ'
  have hcomp : Acts (evFin F v) (om (g, h)) φ φ'' := by
    intro R hR
    have e : om (g, h) = om (g, 1) * om (1, h) := by rw [← map_mul]; simp
    have hR' : Rest (evFin F v) φ' R :=
      ⟨hR.1, by rw [← hA' R hR]; exact hp.weil.isUSplitting.pres (1, h) _ hR.2⟩
    rw [e, Module.End.mul_apply, hA' R hR, hA'' R hR']
  obtain ⟨hex, -, -⟩ := _root_.PositivityTheory.ThKF0.actsEx_k F E σ B n d X W M χX χW om r s r' s' hp v
  have e1 : φ₁ = φ'' := (hex g hg h hh φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ'', hcomp⟩
  have key : (LinearMap.funLeft ℂ ℂ (mulH_pk P⁻¹ Q⁻¹) ∘ₗ ι) φ'' =
      GlobalTheory.SplitFlip.omB (chrW χW (t.comp σ)) (chrW χX (t.comp σ)) g₁ h₁ ((LinearMap.funLeft ℂ ℂ (mulH_pk P⁻¹ Q⁻¹) ∘ₗ ι) φ) := by
    rw [e'', e', ← GlobalTheory.SplitFlip.omB_mul, mul_one, one_mul]
  have ug := GlobalTheory.Div.CoordOpp.unit_map σ g (t.comp σ)
  have uh := GlobalTheory.Div.CoordOpp.unit_map σ h (t.comp σ)
  rw [GlobalTheory.OppLagr.comp_comp hcm, ← eg] at ug
  rw [GlobalTheory.OppLagr.comp_comp hcm, ← eh] at uh
  have ug' : g₁.1ᵀ * X.J.map (t.comp σ) * g₀.1 = X.J.map (t.comp σ) := ug
  have uh' : h₁.1ᵀ * W.J.map (t.comp σ) * h₀.1 = W.J.map (t.comp σ) := uh
  have cg : g₀⁻¹ = P⁻¹ * (GlobalTheory.SplitFlip.invT g₁)⁻¹ * P := by
    symm
    rw [eq_inv_iff_mul_eq_one]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, GlobalTheory.SplitFlip.invT_inv_val]
    have e0 : g₁.1ᵀ * P.1 * g₀.1 = P.1 := by rw [hPv, Matrix.mul_neg, Matrix.neg_mul, ug']
    calc (P⁻¹).1 * g₁.1ᵀ * P.1 * g₀.1 = (P⁻¹).1 * (g₁.1ᵀ * P.1 * g₀.1) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e0]; exact Units.inv_mul P
  have ch : GlobalTheory.SplitFlip.invT h₀ = Q * h₁ * Q⁻¹ := by
    rw [← inv_mul_eq_one]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, GlobalTheory.SplitFlip.invT_inv_val]
    have e0 : h₀.1ᵀ * Q.1 * h₁.1 = Q.1 := by
      have := congrArg Matrix.transpose uh'
      simpa [hQv, Matrix.transpose_mul, Matrix.mul_assoc] using this
    calc h₀.1ᵀ * (Q.1 * h₁.1 * (Q⁻¹).1) = h₀.1ᵀ * Q.1 * h₁.1 * (Q⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e0]; exact Units.mul_inv Q
  have gi : ∀ {m : ℕ} (x : GL (Fin m) (Fv F v)), GlobalTheory.SplitFlip.gdet x⁻¹ = (GlobalTheory.SplitFlip.gdet x)⁻¹ :=
    fun x => map_inv Matrix.GeneralLinearGroup.det x
  have dg : GlobalTheory.SplitFlip.gdet g₁ = (GlobalTheory.SplitFlip.gdet g₀)⁻¹ := by
    have e0 := congrArg GlobalTheory.SplitFlip.gdet cg
    rw [gi, GlobalTheory.SplitFlip.gdet_mul, GlobalTheory.SplitFlip.gdet_mul, gi, gi, GlobalTheory.SplitFlip.gdet_invT] at e0
    rw [e0, inv_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have dh : GlobalTheory.SplitFlip.gdet h₁ = (GlobalTheory.SplitFlip.gdet h₀)⁻¹ := by
    have e0 := congrArg GlobalTheory.SplitFlip.gdet ch
    rw [GlobalTheory.SplitFlip.gdet_invT, GlobalTheory.SplitFlip.gdet_mul, GlobalTheory.SplitFlip.gdet_mul, gi] at e0
    rw [e0, mul_comm (GlobalTheory.SplitFlip.gdet Q), mul_assoc, mul_inv_cancel, mul_one]
  rw [e1]
  funext Y
  have hm : ∀ (ψ' : (Fin n × Fin d → Fv F v) → ℂ) y, (LinearMap.funLeft ℂ ℂ (mulH_pk P⁻¹ Q⁻¹) ∘ₗ ι) ψ' y = ι ψ' ((P⁻¹).1 * y * (Q⁻¹).1) := fun _ _ => rfl
  have hy : ι φ'' Y = (LinearMap.funLeft ℂ ℂ (mulH_pk P⁻¹ Q⁻¹) ∘ₗ ι) φ'' (P.1 * Y * Q.1) := by
    rw [hm]
    congr 1
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have c1 : (g₀⁻¹).1 = (P⁻¹).1 * g₁.1ᵀ * P.1 := by rw [cg]; rfl
  have c2 : (GlobalTheory.SplitFlip.invT h₀).1 = Q.1 * h₁.1 * (Q⁻¹).1 := by rw [ch]; rfl
  have am : (P⁻¹).1 * (g₁.1ᵀ * (P.1 * Y * Q.1) * h₁.1) * (Q⁻¹).1 = (P⁻¹).1 * g₁.1ᵀ * P.1 * Y * (Q.1 * h₁.1 * (Q⁻¹).1) := by
    simp only [Matrix.mul_assoc]
  rw [hy, key, GlobalTheory.OppLagr.chrW_comp hcm χW hp.resW, GlobalTheory.OppLagr.chrW_comp hcm χX hp.resX]
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitFlip.omB]
  rw [hm, am, c1, c2, dg, dh]
  simp only [map_inv, MonoidHom.inv_apply, inv_inv, GlobalTheory.SplitFlip.apow_inv, neg_div]
end UpperTheory.TP
end
theorem UpperTheory.TP.splitFree_k :
    _root_.GlobalTheory.ThK.Dbl.SplitModel_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t
  exact ⟨_root_.UpperTheory.TP.exists_linW_k B M χX χW om hp v t,
    fun ι hι g hg h hh g₀ h₀ eg eh φ hφ φ₁ hφ₁ hA =>
      _root_.UpperTheory.TP.split_formula_k B M χX χW om hp v t hι g hg h hh g₀ h₀ eg eh φ hφ φ₁ hφ₁ hA⟩
end
end

section



section
noncomputable section
namespace PositivityTheory.ThKG.Tow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem modelEx_k : _root_.PositivityTheory.ThKG.Tow.ModelEx_k := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  classical
  obtain ⟨co, hco⟩ := _root_.Tw.RatDarboux.exists_rational_darboux_of_isGood_k B hB X W r s r' s' hX hW
  obtain ⟨-, ⟨μ, 𝓕, hμ, h𝓕⟩, -⟩ := PositivityTheory.ThKF.unimodularity_holds F E σ hB.cm n X.J 1 (by simpa using hX.herm) (det_herm hX)
  have hS := _root_.Tw.VacIndic.eventually_isVac_indicator_k B hB X W r s r' s' hX hW co hco
  have hA := _root_.Tw.VacAny.exists_isVac_any_darboux_k B hB X W r s r' s' hX hW co
  let M₀ : Model σ X W := ⟨co, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (hA v).choose
  refine ⟨⟨co, vac, μ, 𝓕⟩, ⟨hco, fun v => ?_, ?_, hμ, h𝓕⟩⟩
  · show M₀.IsVac B.ψ v (vac v)
    by_cases h : M₀.IsVac B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hA v).choose_spec
  · filter_upwards [hS] with v hv
    show vac v = ind v
    exact if_pos hv
end PositivityTheory.ThKG.Tow
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_meanAdm_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) :
    ∃ Λ ∈ (adeleClass F).adm d.κ, ∀ Ψ ∈ d.sch,
      Λ Ψ = (d.μ.real d.D)⁻¹ • ∫ g in d.D, thetaSum F (d.S g Ψ) ∂d.μ := by
  obtain ⟨l, hl, hlθ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.exists_lth_k d
  have hpres : ∀ g, ∀ Ψ ∈ d.sch, d.S g Ψ ∈ d.sch := fun g Ψ hΨ => d.ok.dbl.lin.pres g Ψ hΨ
  have hfun : ∀ Ψ ∈ d.sch, (fun g => l (d.S g Ψ)) = fun g => thetaSum F (d.S g Ψ) :=
    fun Ψ hΨ => funext fun g => hlθ _ (hpres g Ψ hΨ)
  have hint : ∀ Ψ ∈ d.sch, IntegrableOn (fun g => l (d.S g Ψ)) d.D d.μ := fun Ψ hΨ => by
    rw [hfun Ψ hΨ]; exact _root_.PositivityTheory.SiegelWeilFormula.Tauto.intOn_S_k hS hP hT d hΨ
  set c : ℝ := (d.μ.real d.D)⁻¹ with hc
  let L0 : d.sch →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => c • ∫ g in d.D, l (d.S g Ψ.1) ∂d.μ
      map_add' := fun Ψ Ψ' => by
        simp only [Submodule.coe_add, map_add (f := _)]
        rw [integral_add (hint _ Ψ.2) (hint _ Ψ'.2), smul_add]
      map_smul' := fun a Ψ => by
        simp only [SetLike.val_smul, map_smul, RingHom.id_apply, smul_eq_mul]
        rw [integral_const_mul, mul_smul_comm] }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend L0
  have hΛv : ∀ Ψ (hΨ : Ψ ∈ d.sch), Λ Ψ = c • ∫ g in d.D, l (d.S g Ψ) ∂d.μ := fun Ψ hΨ => by
    have := congrArg (fun L => L ⟨Ψ, hΨ⟩) hΛ
    simpa [L0] using this
  refine ⟨Λ, fun gf hgf => ?_, fun Ψ hΨ => by rw [hΛv Ψ hΨ, hfun Ψ hΨ]⟩
  choose Th hTh using fun h : UA σ d.A.J => d.ok.dbl.lin.adm h l hl gf hgf
  have hmem : ∀ f : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f gf ∈ d.sch :=
    fun f => Submodule.subset_span ⟨f, gf, hgf, rfl⟩
  have hTv : ∀ h f, Th h f = thetaSum F (d.S h (pureA F f gf)) := fun h f => by
    rw [← hTh h f, LinearMap.comp_apply, hlθ _ (hpres h _ (hmem f))]
  haveI : BarrelledSpace ℂ (SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ) := GlobalTheory.T.schwartzMap_barrelledSpace' _
  have hUE : UniformEquicontinuous ((↑) ∘ Th) := (norm_withSeminorms ℂ ℂ).banach_steinhaus fun _ f => by
    obtain ⟨C, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.bdd_S_k hS hP hT d (hmem f)
    refine ⟨C, ?_⟩
    rintro _ ⟨h, rfl⟩
    simpa [hTv] using hC h
  have hpa : ∀ f f' : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ,
      pureA F (f + f') gf = pureA F f gf + pureA F f' gf := fun f f' => funext fun x => by
    simp [pureA, add_mul]
  have hps : ∀ (a : ℂ) (f : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ),
      pureA F (a • f) gf = a • pureA F f gf := fun a f => funext fun x => by
    simp [pureA, mul_assoc]
  let Lf : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun f => Λ (pureA F f gf)
      map_add' := fun f f' => by rw [hpa, map_add (f := _)]
      map_smul' := fun a f => by rw [hps, map_smul]; rfl }
  have hLf : ∀ f, Lf f = c • ∫ g in d.D, Th g f ∂d.μ := fun f => by
    show Λ (pureA F f gf) = _
    rw [hΛv _ (hmem f)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show l (d.S g (pureA F f gf)) = Th g f
    rw [← hTh g f]; rfl
  have hfin : d.μ d.D < ⊤ := (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).fin d.μ d.D d.ok.haar d.ok.dom
  have hpos : 0 < d.μ.real d.D := by
    haveI := (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).cnt
    haveI := d.ok.haar
    exact ENNReal.toReal_pos (fd_ne d.ok.dom) hfin.ne
  have hcont : Continuous Lf := by
    refine continuous_of_continuousAt_zero Lf.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.equicontinuousAt_iff_right.1 (hUE.equicontinuous 0)) (ε / 2) (half_pos hε)] with f hf
    rw [dist_zero_right]
    show ‖Lf f‖ < ε
    rw [hLf]
    have hb : ∀ g ∈ d.D, ‖Th g f‖ ≤ ε / 2 := fun g _ => by
      have := (hf g).le
      simpa [dist_comm] using this
    calc ‖c • ∫ g in d.D, Th g f ∂d.μ‖ ≤ c * (ε / 2 * d.μ.real d.D) := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
          gcongr
          exact norm_setIntegral_le_of_norm_le_const hfin hb
      _ = ε / 2 := by rw [hc]; field_simp
      _ < ε := half_lt_self hε
  exact ⟨⟨Lf, hcont⟩, fun f => rfl⟩
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kunf
theorem unfold_k : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k := by
  intro F E _ _ _ _ _ σ d s₁ f hf hE
  obtain ⟨U, p, Ê, t, -, -, -, -, -, -, -, hmaj⟩ := hE 0
  refine ⟨t, fun z hz nb lam 𝓖 hc ε w hw x => ?_⟩
  have hΦ : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) = flat d.a f s₁ z := funext fun x => by
    rw [_root_.GlobalTheory.ThK.Dbl.flat, _root_.PositivityTheory.SiegelWeilFormula.kunf.ht_eq_k]
  have hmaj' := (hmaj z hz).1
  rw [hΦ] at hmaj'
  have hlaw : Law d.χ (s₁ + d.n / 2) f := hf.law
  have hlawF := hlaw.flat (s₀ := s₁) d.ok.hgt (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d) z
  have hcore := _root_.PositivityTheory.SiegelWeilFormula.kunf.unfoldCore_k d.B d.ok.good d.ok.frame hc (flat d.a f s₁ z)
    (continuous_flat hf.cont (_root_.PositivityTheory.SiegelWeilFormula.kunf.continuous_a_k d) (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d) z)
    (fun p hp hpr y => hlawF.rat d.ok.hecke hp hpr y)
    (fun p t ht hdet y => by rw [hlawF p t y ht, hdet]; simp)
    hmaj' hw x
  refine ⟨hcore.1, fun T hT => ?_⟩
  show fc d.B.ψ d.b nb lam 𝓖 (GlobalTheory.Eis.cosetSum _ _ (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x)) T x = _
  rw [hΦ]
  exact hcore.2 T hT
end PositivityTheory.SiegelWeilFormula.kunf
end
end
end
