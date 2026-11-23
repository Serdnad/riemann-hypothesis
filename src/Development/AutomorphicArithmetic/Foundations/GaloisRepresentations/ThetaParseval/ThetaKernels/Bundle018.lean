module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle005
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle535
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle090
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutGen
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutGenA
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002

@[expose] public section

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.EtaCMType
theorem exists_eta_cmType_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨ξ, hξ, hξe⟩ := _root_.GlobalTheory.T.exists_hecke_character_trivial_exponent F E σ B hB
  obtain ⟨η₀, hη₀, huniq⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E hB.cm.2.2.1
  have hη₀' : IsEtaF E η₀ := hη₀
  let lam : (AF F)ˣ →* Circle := ξ.comp (idFF F E) * η₀⁻¹
  have hlam : ∀ a, lam a = ξ (idFF F E a) * (η₀ a)⁻¹ := fun a => rfl
  have hlc : Continuous lam := by
    have : Continuous fun a => ξ (idFF F E a) * (η₀ a)⁻¹ :=
      (hξ.1.comp continuous_idFF).mul (hη₀.1.inv)
    exact this
  have hlF : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1 := by
    intro a
    rw [hlam, idFF_rat, hξ.2, hη₀.2.1, inv_one, one_mul]
  have hlinf : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1 := by
    intro a ha
    have e1 := hξe _ (at_idFF a ha)
    have e2 := _root_.GlobalTheory.T.eta_character_archimedean_formula F E σ B hB η₀ hη₀' a ha
    have e3 : ξ (idFF F E a) = η₀ a := by
      apply Circle.ext
      rw [e1, e2]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [zpow_one]
    rw [hlam, e3, mul_inv_cancel]
  obtain ⟨lam', hl'H, hl'inf, hl'res⟩ := _root_.GlobalTheory.T.extend_character_to_norm_group F E σ B hB lam hlc hlF hlinf
  refine ⟨ξ * lam'⁻¹, ⟨hξ.1.mul hl'H.1.inv, fun x => ?_⟩, ⟨⟨η₀, hη₀'⟩, fun η hη a => ?_⟩, fun z hz => ?_⟩
  · change ξ _ * (lam' _)⁻¹ = 1
    rw [hξ.2, hl'H.2, inv_one, one_mul]
  · change ξ _ * (lam' _)⁻¹ = _
    rw [huniq η hη, hl'res, hlam, pow_one, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel_comm]
  · change ((ξ z * (lam' z)⁻¹ : Circle) : ℂ) = _
    rw [hl'inf z hz, inv_one, mul_one]
    exact hξe z hz
end GlobalTheory.EtaCMType
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.theta_doubling_inner_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (w : Formalism.IndefR.DatumF.WOF F E nS (nT + nT)) (f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) =
          GlobalTheory.DblTargetDelta.deltaT (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (GlobalTheory.DblTargetDelta.topR w) f₁)
            (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (-GlobalTheory.DblTargetDelta.botR w) f₂) := by
  first | exact @_root_.GlobalTheory.DblHeis.heisOF_dblG_deltaT_k | exact _root_.GlobalTheory.DblHeis.heisOF_dblG_deltaT_k | (intros; apply _root_.GlobalTheory.DblHeis.heisOF_dblG_deltaT_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.theta_inner_product_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) := by
  first | exact @_root_.GlobalTheory.DblTargetThetaF.main_k | exact _root_.GlobalTheory.DblTargetThetaF.main_k | (intros; apply _root_.GlobalTheory.DblTargetThetaF.main_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
namespace GlobalTheory.ThetaSmoothCM
theorem contDiff_thetaTr_real_CM_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
            ∀ w, ContDiff ℝ ∞ fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (w + L t) := by
  intro F E _ _ _ _ _ σ B hgood nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ hψ JA JB ξ hJA hJB κ _ co hrat φ hφ k L hLc hLf w
  exact _root_.GlobalTheory.T.doubled_lagrangian_invariant_functional F E σ B hgood hψ nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ JA JB ξ hJA hJB κ co hrat φ hφ k L hLc hLf w
end GlobalTheory.ThetaSmoothCM
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.doubled_theta_lift_automorphy : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  first | exact @_root_.GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm_k | exact _root_.GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm_k | (intros; apply _root_.GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.doubled_theta_lift_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (Formalism.IndefR.DatumF.ratWF γ + w) =
              B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ w := by
  first | exact @_root_.GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi_k | exact _root_.GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi_k | (intros; apply _root_.GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi_k <;> assumption)
end
end

section



section
noncomputable section
open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF Formalism.IndefR.LiftF
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeExtend GlobalTheory.HeckeExtend.AtInf GlobalTheory.SplitDetCharF
namespace PositivityTheory.ThKW.Eta
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem local_norm_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v)ˣ)
    (h1 : 2 * (u : Fv F v) ∈ v.adicCompletionIntegers F)
    (h2 : 2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F) :
    u ∈ GlobalTheory.QuadSymbol.normGroup F E (Fv F v) := by
  obtain ⟨δ, b, hδ, hb0, hb1, hbb⟩ :=
    GlobalTheory.QuadNormBase.exists_basis F E σ hB.cm.2.2.1 (sig_invol hB.cm) (sig_ne hB.cm)
  have hbb' : b 1 * b 1 = algebraMap F E δ := hbb
  refine (GlobalTheory.QuadSymbol.mem_normGroup_iff_form b hb0 hbb').2 ?_
  rcases _root_.GlobalTheory.T.nonempty_algHom_or_exists_inert_of_goodK F E σ B hB v with ⟨τ⟩ | ⟨w, hw⟩
  · obtain ⟨τ⟩ := τ
    have hs : τ (b 1) * τ (b 1) = algebraMap F (Fv F v) δ := by rw [← map_mul, hbb', AlgHom.commutes]
    have hs0 : τ (b 1) ≠ 0 := (map_ne_zero τ).2 (b.ne_zero 1)
    have h20 : (2 : Fv F v) ≠ 0 := by
      rw [← map_ofNat (algebraMap F (Fv F v)) 2]
      exact (map_ne_zero _).2 two_ne_zero
    refine ⟨((u : Fv F v) + 1) / 2, ((u : Fv F v) - 1) / (2 * τ (b 1)), ?_⟩
    rw [← hs]
    field_simp
    ring
  · have hv2 : Valued.v (2 : Fv F v) = 1 := by
      have e : (2 : Fv F v) = algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) := by rw [map_ofNat, map_ofNat]
      rw [e]
      refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans ?_
      refine le_antisymm (v.valuation_le_one 2) (not_lt.1 fun h => (hB.inert v w hw).1 ?_)
      exact (v.valuation_lt_one_iff_mem 2).1 h
    have a1 : Valued.v (2 * (u : Fv F v)) ≤ 1 := h1
    have a2 : Valued.v (2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v)) ≤ 1 := h2
    rw [map_mul, hv2, one_mul] at a1 a2
    have hu : Valued.v (u : Fv F v) = 1 := by
      refine le_antisymm a1 ?_
      have hm := congrArg Valued.v u.mul_inv
      rw [map_mul, map_one] at hm
      rw [← hm]
      exact mul_le_of_le_one_right' a2
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.InertUnitNorm.unit_eq_mul_conj_k F E σ B hB v w hw (_root_.GlobalTheory.T.inert_completion_isField F E σ B hB v w hw) u hu
    obtain ⟨x, y, rfl⟩ := tensor_decomp (A := Fv F v) (b 1) (fun x => ⟨b.repr x 0, b.repr x 1, by
      have hx := b.sum_repr x
      rw [Fin.sum_univ_two, hb0] at hx
      exact hx.symm⟩) z
    refine ⟨x, y, tensor_inj (F := F) (E := E) ?_⟩
    have e1 : ((1 : Fv F v) ⊗ₜ[F] b 1) * ((1 : Fv F v) ⊗ₜ[F] b 1) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) δ) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb', ← IsScalarTower.algebraMap_apply,
        Algebra.TensorProduct.algebraMap_apply']
    rw [hz, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hb1,
      TensorProduct.tmul_neg, map_sub, map_mul, map_pow, map_pow, ← e1]
    ring
end PositivityTheory.ThKW.Eta
end
end
end

section



section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.archimedean_chart_theta_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  first | exact @_root_.GlobalTheory.RealCharF.psi_symplOHF_iotaVF_k | exact _root_.GlobalTheory.RealCharF.psi_symplOHF_iotaVF_k | (intros; apply _root_.GlobalTheory.RealCharF.psi_symplOHF_iotaVF_k <;> assumption)
end
end

section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
noncomputable section
namespace GlobalTheory.CompanionTheory.Iwasawa
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem height_continuous_pos_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x :=
  fun F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha =>
    continuous_pos (_root_.GlobalTheory.T.isCompact_standard_maximal_compact F E σ B n Y r s hB hn hY b K a hb hK ha) ha
end GlobalTheory.CompanionTheory.Iwasawa
end
end
end

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
theorem infinite_norm_one_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : {t : E | t * σ t = 1}.Infinite :=
  _root_.UpperTheory.Reformulated.B.InfiniteNormOneField.infinite_norm_one_k C
theorem det_kron_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (b ⊗ₖ aᵀ).det * σ (b ⊗ₖ aᵀ).det = 1 ∧
      (b ⊗ₖ aᵀ).det * σ (b ⊗ₖ aᵀ - 1).det = (-1) ^ Fintype.card (Fin nT × Fin nS) * (b ⊗ₖ aᵀ - 1).det := by
  have hu : IsUnit JS.det := isUnit_iff_ne_zero.2 C.hS.2
  have hP : (JT ⊗ₖ JS⁻¹ᵀ).det ≠ 0 := by
    rw [det_kronecker, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ C.hT.2) (pow_ne_zero _ (Matrix.isUnit_nonsing_inv_det JS hu).ne_zero)
  have hunitary {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} {a}
      (h : IsRatF σ J g a) : (a.map σ)ᵀ * J * a = J := by
    have e := GenA.mt_unitary σ J g
    rw [show mtF σ J g = _ from h, GenA.map_unitary] at e
    exact Matrix.map_injective GenA.incAF_injective e
  exact GenA.det_unit_sig σ hP (GenA.kron_unit_sig σ hu (hunitary ha) (hunitary hb))
namespace GenR
theorem compAt_rat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} {a}
    (h : IsRatF σ J g a) (w : InfinitePlace F) : compAtF θ w (mtF σ J g) = a.map (tauB B w) := by
  rw [show mtF σ J g = _ from h]
  ext i j
  show θ w (infPartF F E (incAF F E (a i j))) = tauB B w (a i j)
  rw [GenA.infPart_incAF]
  exact (C.inf w).1 (a i j)
theorem cart_blk_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {sS : InfinitePlace F → Matrix (Fin nS) (Fin nS) ℂ}
    {sT : InfinitePlace F → Matrix (Fin nT) (Fin nT) ℂ}
    (hS : ∀ w, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) (sS w))
    (hT : ∀ w, Formalism.IndefR.Datum.IsCartanInv (((2 * (tauB B w ξ₀).im : ℝ) : ℂ) • JT.map (tauB B w)) (sT w)) :
    CartF σ JS JT ξ₀ B θ (GlobalTheory.RealWeil.blk sT sS) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [GlobalTheory.RealWeil.blk_mul]
    simp only [fun w => (hS w).1, fun w => (hT w).1]
    exact GlobalTheory.RealWeil.blk_one
  · unfold HMF
    rw [GlobalTheory.RealWeil.blk_mul]
    refine GlobalTheory.RealWeil.blk_posDef (fun w => (hT w).2.2) fun w => ?_
    rw [← GlobalTheory.RealSymplForm.cartan_inv_mul (hS w)]
    exact (hS w).2.2.inv
  · intro k t hk
    rw [mMF_apply]
    refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
    · rw [_root_.PositivityTheory.ThKW.GenR.compAt_rat_k C hk]
      have e : (t • (1 : Matrix (Fin nT) (Fin nT) E)).map (tauB B w) = tauB B w t • 1 := by
        ext i j
        by_cases hij : i = j <;> simp [hij]
      rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    · have hone : compAtF θ w (mtF σ JS 1) = 1 := by
        rw [GenA.mt_one, compAtF, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [inv_one, hone, Matrix.one_mul, Matrix.mul_one]
end GenR
theorem rat_gen_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (Q : GAF σ JS × GAF σ JT → Prop)
    (hm : ∀ p q, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → q.1 ∈ GQF σ JS → q.2 ∈ GQF σ JT → Q p → Q q → Q (p * q))
    (hs : ∀ p s, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → CartF σ JS JT ξ₀ B θ s →
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → Q p) :
    ∀ p, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → Q p := by
  have hcm := C.good.cm
  have hσ := GlobalTheory.SplitDetCharF.sig_invol hcm
  obtain ⟨c, hc⟩ : ∃ c : E ≃ₐ[F] E, (c : E →ₐ[F] E) = σ :=
    ⟨AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ), rfl⟩
  subst hc
  have hmem {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF (c : E →ₐ[F] E) J} {a}
      (hJ : IsHermND (c : E →ₐ[F] E) J) (h : IsRatF (c : E →ₐ[F] E) J g a) :
      g ∈ GQF (c : E →ₐ[F] E) J := by
    have e := GenA.mt_unitary (c : E →ₐ[F] E) J g
    rw [show mtF (c : E →ₐ[F] E) J g = _ from h, GenA.map_unitary] at e
    have hu : (a.map (c : E →ₐ[F] E))ᵀ * J * a = J :=
      Matrix.map_injective GenA.incAF_injective e
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a (GenA.det_ne_of_unitary hJ hu), hu, Units.ext h.symm⟩
  have hone {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) :
      compAtF θ w (mtF (c : E →ₐ[F] E) J 1) = 1 := by
    rw [GenA.mt_one, compAtF, Matrix.map_one _ (map_zero _) (map_one _)]
  have hr : ∀ w, (2 * (tauB B w ξ₀).im : ℝ) ≠ 0 := fun w => mul_ne_zero two_ne_zero (GenA.im_ne hcm C.h0 C.hξ _)
  have hcS : ∀ w, ∃ s, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) s := fun w => by
    simpa using GenA.cart_exists _ (GenA.herm_map hcm C.hS (tauB B w)) (GenA.det_map_ne C.hS (tauB B w)) 1 one_ne_zero
  have hcT : ∀ w, ∃ s, Formalism.IndefR.Datum.IsCartanInv (((2 * (tauB B w ξ₀).im : ℝ) : ℂ) • JT.map (tauB B w)) s :=
    fun w => GenA.cart_exists _ (GenA.herm_map hcm C.hT (tauB B w)) (GenA.det_map_ne C.hT (tauB B w)) _ (hr w)
  choose sS0 hS0 using hcS
  choose sT0 hT0 using hcT
  have Q11 : Q (1, 1) := hs (1, 1) (GlobalTheory.RealWeil.blk sT0 sS0) (one_mem _) (one_mem _) (_root_.PositivityTheory.ThKW.GenR.cart_blk_k C hS0 hT0)
    (by
      show _ * mMF _ JS JT θ 1 = mMF _ JS JT θ 1 * _
      rw [map_one, Matrix.mul_one, Matrix.one_mul])
  have hT : ∀ h ∈ GQF (c : E →ₐ[F] E) JT, Q (1, h) := by
    refine GenR.rat_ind c hcm C.hT (fun h => Q (1, h)) Q11 (fun g hg g' hg' a b => ?_) (fun g x u hx hg => ?_)
    · have := hm (1, g) (1, g') (one_mem _) hg (one_mem _) hg' a b
      rwa [Prod.mk_mul_mk, mul_one] at this
    · have := fun w => GenA.cart_refl (JT.map (tauB B w)) (GenA.herm_map hcm C.hT (tauB B w))
        (GenA.det_map_ne C.hT (tauB B w)) _ (hr w) (tauB B w ∘ x)
        (by rw [GenA.quad_map hcm c rfl]; exact (map_ne_zero _).2 hx) (tauB B w ((u - 1) / GlobalTheory.UnRep.hermE c JTᵀ x x))
      choose sT hT1 hT2 using this
      refine hs (1, g) (GlobalTheory.RealWeil.blk sT sS0) (one_mem _) (hmem C.hT hg) (_root_.PositivityTheory.ThKW.GenR.cart_blk_k C hS0 hT1) ?_
      rw [mMF_apply]
      refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
      · rw [_root_.PositivityTheory.ThKW.GenR.compAt_rat_k C hg, GenA.refl_map hcm c rfl]
        exact hT2 w
      · rw [inv_one, hone, Matrix.one_mul, Matrix.mul_one]
  have hS : ∀ g ∈ GQF (c : E →ₐ[F] E) JS, Q (g⁻¹, 1) := by
    refine GenR.rat_ind c hcm C.hS (fun g => Q (g⁻¹, 1)) (by rw [inv_one]; exact Q11) (fun g hg g' hg' a b => ?_)
      (fun g x u hx hg => ?_)
    · have := hm (g'⁻¹, 1) (g⁻¹, 1) (inv_mem hg') (one_mem _) (inv_mem hg) (one_mem _) b a
      rwa [Prod.mk_mul_mk, mul_one, ← _root_.mul_inv_rev] at this
    · have := fun w => GenA.cart_refl (JS.map (tauB B w)) (GenA.herm_map hcm C.hS (tauB B w))
        (GenA.det_map_ne C.hS (tauB B w)) 1 one_ne_zero (tauB B w ∘ x)
        (by rw [GenA.quad_map hcm c rfl]; exact (map_ne_zero _).2 hx) (tauB B w ((u - 1) / GlobalTheory.UnRep.hermE c JSᵀ x x))
      choose sS hS1 hS2 using this
      have hS1' : ∀ w, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) (sS w) := fun w => by simpa using hS1 w
      refine hs (g⁻¹, 1) (GlobalTheory.RealWeil.blk sT0 sS) (inv_mem (hmem C.hS hg)) (one_mem _) (_root_.PositivityTheory.ThKW.GenR.cart_blk_k C hS1' hT0) ?_
      rw [mMF_apply, inv_inv]
      refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
      · rw [hone, Matrix.one_mul, Matrix.mul_one]
      · rw [_root_.PositivityTheory.ThKW.GenR.compAt_rat_k C hg, GenA.refl_map hcm c rfl]
        exact (hS2 w).symm
  intro p h1 h2
  have e : p = (p.1, 1) * (1, p.2) := by
    rw [Prod.mk_mul_mk, mul_one, one_mul]
  have a1 : Q (p.1, 1) := by
    have := hS _ (inv_mem h1)
    rwa [inv_inv] at this
  rw [e]
  exact hm _ _ h1 (one_mem _) (one_mem _) h2 a1 (hT _ h2)
end PositivityTheory.ThKW
end
end
end
