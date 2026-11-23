module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle065
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle092
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle073
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle056
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MfacInvMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle076
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle069
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle049
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinTermLeftInvariant
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle064
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.WeilUnitaryTransportF
theorem isUnitaryOn_transportF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ χS χT hcS hcT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have hψ := hω.std
  rintro μ hμ ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := _root_.GlobalTheory.T.doubled_lagrangian_intertwiner F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm a b
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_rationalMatrices_tower F E nS nT
  obtain ⟨ν', 𝓕', hν', h𝓕', heq⟩ :=
    _root_.GlobalTheory.T.doubled_lagrangian_theta_compatible F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat ν 𝓕 hν h𝓕
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_lintegral_sq_eq_mul_setLIntegral_thetaTransform F B.ψ hψ.1 κ μ hμ ν' hν' 𝓕' h𝓕'
  have hiso : ∀ Ψ ∈ schA F κ, ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂μ =
      c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Ψ w‖ₑ ^ 2 ∂ν := by
    intro Ψ hΨ
    rw [hc Ψ hΨ, ← heq]
    rfl
  have hth : IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) :=
    ⟨_root_.GlobalTheory.T.doubled_lagrangian_continuous F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     _root_.GlobalTheory.T.doubled_lagrangian_unitary F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     _root_.GlobalTheory.T.doubled_lagrangian_equivariant F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     _root_.GlobalTheory.T.doubled_lagrangian_invariant_functional F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ⟩
  have ht := hom a b g h hh hg Φ hΦ
  calc
    _ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ ((om (a, b)) Φ) w‖ₑ ^ 2 ∂ν := hiso _ ht.1
    _ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w‖ₑ ^ 2 ∂ν := by
      exact (congrArg (fun f => c * ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂ν) ht.2).trans
        (congrArg (c * ·) (hω.om_unit ν 𝓕 hν h𝓕 _ _ hth))
    _ = _ := (hiso _ hΦ).symm
end GlobalTheory.WeilUnitaryTransportF
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.NormModulusHeisenberg
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.ThKW.NormModulusHeisenberg
end
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.NormModulusHeisenberg in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.norm_law_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ =
          mfac F E nS t * ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t hht f hf
  obtain ⟨μW, 𝓕W, κ, hμW, h𝓕W, hκ, hcoef⟩ := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.coef_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕
  have hωf := hωd.om_pres (1, h) f hf
  obtain ⟨c1, i1, e1⟩ := hcoef _ hωf
  obtain ⟨c0, i0, e0⟩ := hcoef f hf
  obtain ⟨cL, iL, eL⟩ := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.change_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 t _ c0 i0
  have hκ0 : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ.ne'
  have key : nrm σ JS JT ξ₀ B.ψ ν 𝓕 (ωd (1, h) f) = fun w =>
      ((mfac F E nS t : ℝ) : ℂ) ^ 2 * nrm σ JS JT ξ₀ B.ψ ν 𝓕 f ((t.1.map (cAF σ))ᵀ * w) := by
    refine _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.finj_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 _ _ c1 (continuous_const.mul cL) i1
      (iL.const_mul _) fun y => ?_
    have hact : actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) = dC (AF F ⊗[F] E) nT * y := by
      unfold actOF
      rw [inv_one, show mtF σ JS 1 = 1 by unfold mtF; rw [map_one, Units.val_one], Matrix.mul_one,
        ← Matrix.mul_assoc, hht, Matrix.mul_assoc, ← Matrix.mul_assoc t.1, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    have u := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.unit_coef_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS ωd hωd μW 𝓕W hμW h𝓕W h
      (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) f hf
    rw [hact, e1 y, e0 ((t⁻¹).1 * y), eL y] at u
    have u' := mul_left_cancel₀ hκ0 u
    rw [u', ← integral_const_mul]
    congr 1
    funext w
    ring
  have k0 := congrFun key 0
  rw [Matrix.mul_zero, nrm_zero, nrm_zero] at k0
  have k1 : ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ ^ 2 =
      (mfac F E nS t * ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖) ^ 2 := by
    rw [mul_pow]
    exact_mod_cast k0
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (mfac_pos' nS t).le (norm_nonneg _)) two_ne_zero).1 k1
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.doubled_theta_lift_convergence : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 →
              Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) =
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ := by
  first | exact @_root_.GlobalTheory.ThetaLevelCM.thetaTr_level_k | exact _root_.GlobalTheory.ThetaLevelCM.thetaTr_level_k | (intros; apply _root_.GlobalTheory.ThetaLevelCM.thetaTr_level_k <;> assumption)
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
theorem continuous_th'_k (T' : nF σ L.Y L.b) : Continuous fun β : nA σ L.Y L.b => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β :=
  kfour.continuous_chr (σ := σ) (Y := L.Y) (b := L.b) d.ok.good.std.1 T'.1.1
theorem countable_crat_k : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) := by
  have : Countable L.ratV := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
    refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
      (⟨GlobalTheory.ThK.incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
    obtain ⟨v, hv⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k u.2
    exact ⟨v, Subtype.ext hv.symm⟩
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (Set.range (algebraMap F (AF F))) := (Set.countable_range _).to_subtype
  refine Function.Injective.countable (f := fun c : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L =>
    ((⟨c.1.1, c.2.1⟩ : L.ratV), (⟨c.1.2, c.2.2⟩ : Set.range (algebraMap F (AF F)))))
    fun c c' hcc => ?_
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hcc
  exact Subtype.ext (Prod.ext hcc.1 (congrArg Subtype.val hcc.2))
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem eisenstein_second_term_expand (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {e : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}}
    (he : ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e x).1 = p * (w₁ * (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1)))) (g : d.G) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) g = ∑' x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L), _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM x.2.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1) * g))) ∧
      ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)‖ₑ =
        ∑' x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L), ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM x.2.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1) * g)))‖ₑ := by
  have key : ∀ x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L), _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e x).1 * g) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM x.2.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1) * g))) := fun x => by
    obtain ⟨p, hp, hr, hx⟩ := he x
    rw [hx, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_rat_k hf z hp hr, mul_assoc, mul_assoc]
  constructor
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm, ← e.tsum_eq]
    exact tsum_congr key
  · rw [← e.tsum_eq]
    exact tsum_congr fun x => by rw [key]
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
set_option linter.style.haveILetI false
def rationalCosetEquiv (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L ≃ L.ratV × fA F where
  toFun c := (⟨c.1.1, c.2.1⟩, ⟨c.1.2, c.2.2⟩)
  invFun c := ⟨((c.1 : Fin L.n → AE F E), (c.2 : AF F)), c.1.2, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem countable_rational_vectors (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Countable L.ratV := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
    (⟨GlobalTheory.ThK.incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
  obtain ⟨v, hv⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k u.2
  exact ⟨v, Subtype.ext hv.symm⟩
theorem coset_point_decomposition (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {γ' : G2 σ L.Y}
    {Λ : ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E))}
    {Q : (Fin L.n → AE F E) × (Fin L.n → AE F E) → AF F}
    (hΛ : ∀ b u a, L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM ((Λ (b, u)).2, a + Q (b, u)) * L.j γ')
    {Z : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AF F}
    (hZ : ∀ u₀ a₀ b u a, cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u₀ + u, a₀ + a + Z u₀ b))
    (Y : d.G) (c₀ : (Fin L.n → AE F E) × AF F) (p : (Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀ * (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.1 * (cM (p.1, p.2.2) * Y))))) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM (UnfoldingIntegralSum.sh Λ Q Z c₀ p) * (L.j γ' * Y))) := by
  obtain ⟨u₀, a₀⟩ := c₀
  obtain ⟨u, b, a⟩ := p
  have e1 : L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * (cM (u, a) * Y)) = (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a))) * Y := by simp only [mul_assoc]
  have e2 : ∀ c', cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM c' * L.j γ' * Y) =
      (cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM c')) * (L.j γ' * Y) := by intro c'; simp only [mul_assoc]
  rw [e1, hΛ, e2, hZ, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.section_unipotent_invariant h hf z]
  simp only [UnfoldingIntegralSum.sh, add_assoc]
theorem unfqE_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F)) {γ' : G2 σ L.Y} (hγ : γ' ∈ rat2 σ L.Y) (Y : d.G) :
    ∫⁻ p, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.1 * (cM (p.1, p.2.2) * Y)))))‖ₑ
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐))) =
      ∫⁻ c, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y)))‖ₑ ∂(ν.prod (lamA F)) := by
  obtain ⟨-, hν, hU0, hU1⟩ := hU
  haveI := hν
  haveI := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.countable_rational_vectors L
  obtain ⟨Λ, Q, hQ, hΛeq, hΛrat⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_conj_k (R := R) h γ'
  obtain ⟨Z, hZ, -, hheis⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.heis_k (R := R) h
  have hg : Continuous fun c => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y))) :=
    (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z).comp (continuous_const.mul ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_cM_k h).mul continuous_const))
  rw [← UnfoldingIntegralSum.unf_lint hU0 hU1 (fd_prod hU0 hU0) h𝓐 Λ (hΛrat hγ) hQ.measurable hZ.measurable hg.measurable.enorm]
  refine lintegral_congr fun p => ?_
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.rationalCosetEquiv L).symm.tsum_eq]
  exact tsum_congr fun c => by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.coset_point_decomposition h hf z hΛeq hheis]; rfl
theorem unfqC_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F)) {γ' : G2 σ L.Y} (hγ : γ' ∈ rat2 σ L.Y) (Y : d.G)
    (hfin : ∫⁻ c, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y)))‖ₑ ∂(ν.prod (lamA F)) < ⊤) :
    ∫ p, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.1 * (cM (p.1, p.2.2) * Y)))))
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐))) =
      ∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y))) ∂(ν.prod (lamA F)) := by
  obtain ⟨-, hν, hU0, hU1⟩ := hU
  haveI := hν
  haveI := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.countable_rational_vectors L
  obtain ⟨Λ, Q, hQ, hΛeq, hΛrat⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_conj_k (R := R) h γ'
  obtain ⟨Z, hZ, -, hheis⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.heis_k (R := R) h
  have hg : Continuous fun c => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y))) :=
    (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z).comp (continuous_const.mul ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_cM_k h).mul continuous_const))
  rw [← UnfoldingIntegralSum.unf_int hU0 hU1 (fd_prod hU0 hU0) h𝓐 Λ (hΛrat hγ) hQ.measurable hZ.measurable hg.measurable hfin]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  beta_reduce
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.rationalCosetEquiv L).symm.tsum_eq]
  exact tsum_congr fun c => by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.coset_point_decomposition h hf z hΛeq hheis]; rfl
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
