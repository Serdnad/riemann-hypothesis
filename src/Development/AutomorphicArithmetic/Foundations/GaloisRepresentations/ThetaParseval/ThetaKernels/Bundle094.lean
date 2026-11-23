module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsInvFormDblK
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle065
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BlockDiagonalPreservesFormIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle049
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle093
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle091
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinTermLeftInvariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle071
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.UnitsBorelSpace.BorelSpaceDoubledGroup
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle001
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.TransportHeisF
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem isThetaFunOF_thetaTr_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA hBξ κ _ co hco φ hφ
  exact
    { quasi := _root_.GlobalTheory.T.doubled_theta_lift_identity F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA hBξ κ co hco φ hφ
      level := _root_.GlobalTheory.T.doubled_theta_lift_convergence F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA hBξ κ co hco φ hφ
      cont := _root_.GlobalTheory.T.doubled_theta_lift_automorphy F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA hBξ κ co hco φ hφ
      smooth := _root_.GlobalTheory.T.doubled_theta_lift_nonvanishing F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA hBξ κ co hco φ hφ }

theorem pres_impl_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
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
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) ∧
              ∀ p w, ∀ φ ∈ schA F κ, om p (co.rho B.ψ w φ) = co.rho B.ψ (actAB (cA σ) p w) (om p φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc χS χT hχS hχT rS rT ω hω JA JB ξ hA hBξ κ _ co hco om htr
  have hstd : IsStd B.ψ := hB.std
  have hchar : IsCharAF F B.ψ := hω.std.1
  have key : ∀ p : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB), ∃ (g : Formalism.IndefR.DatumF.GAF σ JS)
      (h : Formalism.IndefR.DatumF.GAF σ JT), Formalism.IndefR.DatumF.mtF σ JT h = p.1.1.1 ∧
        Formalism.IndefR.DatumF.mtF σ JS g = (p.2⁻¹).1.1ᵀ :=
    fun p => match_pairF σ JS JT hS.2 ξ₀ hξ₀ JA JB ξ hA hBξ p.1 p.2
  have pres : ∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ := by
    intro p φ hφ
    obtain ⟨g, h, hh, hg⟩ := key p
    exact (htr p.1 p.2 g h hh hg φ hφ).1
  refine ⟨pres, fun p w φ hφ => ?_⟩
  obtain ⟨a, b⟩ := p
  obtain ⟨g, h, hh, hg⟩ := key (a, b)
  have hs := symp_eq_symplOF (F := F) σ JS JT ξ₀ JA JB ξ hA hBξ
  have hrho : ∀ w', ∀ φ' ∈ schA F κ, co.rho B.ψ w' φ' ∈ schA F κ :=
    fun w' φ' h' => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ φ' h'
  have h1 := htr a b g h hh hg _ (hrho w φ hφ)
  have h2 := htr a b g h hh hg _ hφ
  have hF := _root_.GlobalTheory.TransportHeisF.isThetaFunOF_thetaTr_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hω.std JA JB ξ hA hBξ κ co hco φ hφ
  have E1 := hω.om_heis g h w _ hF
  have E2 := thetaTr_rhoF σ B.ψ hs co w φ
  have E3 := thetaTr_rhoF σ B.ψ hs co (actAB (cA σ) (a, b) w) (om (a, b) φ)
  have E4 := actOF_eq σ a b g h hh hg w
  have E : GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om (a, b) (co.rho B.ψ w φ)) =
      GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (actAB (cA σ) (a, b) w) (om (a, b) φ)) := by
    refine h1.2.trans ?_
    refine (congrArg (ω (g, h)) E2).trans ?_
    refine E1.trans ?_
    refine Eq.trans ?_ E3.symm
    exact congrArg₂ (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ) E4 h2.2.symm
  unfold GlobalTheory.WeilSchrodinger.thetaTr Darboux.rho at E
  refine schr_theta_inj B.ψ hchar κ _ h1.1 _ (hrho _ _ h2.1) fun v => ?_
  obtain ⟨v', rfl⟩ := co.e.surjective v
  exact congrFun E v'
end GlobalTheory.TransportHeisF
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weil_representation_pair_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
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
  first | exact @_root_.GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF_k | exact _root_.GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF_k | (intros; apply _root_.GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.exists_split_functional_doubled : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e →
        ∃ ℓ : (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : Formalism.IndefR.DatumF.WOF F E nS (nT + nT), (∀ i j, Formalism.IndefR.DatumF.cAF σ e * u i j = u i j) →
            ∀ f, Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
              ℓ (Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) ≠ 0 := by
  first | exact @_root_.GlobalTheory.DblSplitForm.exists_invForm_dbl_k | exact _root_.GlobalTheory.DblSplitForm.exists_invForm_dbl_k | (intros; apply _root_.GlobalTheory.DblSplitForm.exists_invForm_dbl_k <;> assumption)
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
theorem unf_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {f : d.G → ℂ} {s₁ : ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖)
    {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (habs : ∀ x, (∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖))) ∧
      Summable fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    {w₁ : d.G} {cM : (Fin L.n → AE F E) × AF F → d.G} {κ : Measure ((Fin L.n → AE F E) × AF F)} {δ : E}
    (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (hcM : Continuous cM) (hκ : κ.IsAddHaarMeasure) :
    ∃ K : ℂ, ∀ x, _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x = K * ∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, ∫ β in 𝓖',
      (∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x))) ∂κ) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β ∂lam' := by
  classical
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) := Quotient.countable
  have : Countable (rat2 σ L.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ L.Y
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd) := Quotient.countable
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.countable_crat_k
  have : ν.IsAddHaarMeasure := hU.2.1
  have : lam.IsAddHaarMeasure := hc.2.1
  have : lam'.IsAddHaarMeasure := hc'.2.1
  have hψc : Continuous d.B.ψ := d.ok.good.std.1
  obtain ⟨P, hP, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pEquiv_k h
  obtain ⟨cP, hcP0, hcPt, hPc⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.lam_map_k (lam := lam) (ν := ν) (lam' := lam') P
  obtain ⟨cK, hcK0, hcKt, hκeq⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.kap_eq_k (ν := ν) (κ := κ)
  obtain ⟨𝓐, h𝓐, h𝓐0, h𝓐t⟩ := exists_fd_fA (F := F)
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hU.2.2.2])
  have : IsFiniteMeasure (lam'.restrict 𝓖') := isFiniteMeasure_restrict.2 (hc'.2.2.2.trans_ne ENNReal.one_ne_top)
  have : IsFiniteMeasure ((lamA F).restrict 𝓐) := isFiniteMeasure_restrict.2 h𝓐t
  obtain ⟨e, he⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.second_orbit_bijection h
  refine ⟨(cP.toReal : ℂ) * ((cK.toReal : ℂ))⁻¹, fun x => ?_⟩
  have hΦc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z
  obtain ⟨hi, hs⟩ := habs x
  obtain ⟨e1, fin1⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.second_orbit_section_integral (L := L) (nb := nb) (uM := uM) hU.2.2.2 hc.2.2.2 x hi hs
  have e2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.coordsC_k (R := R) h hc hU hc' hT h𝓐 hP hPc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z)) (fun r hr hx g => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_term_left_invariant hf z hr hx g) x
  set μO := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμO
  set μI := (ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)) with hμI
  set μN := (lam'.restrict 𝓖').prod μI with hμN
  have hnb' : Continuous nb' := kunf.continuous_nb hc'.1
  have hnew : Continuous fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) =>
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x)) := by
    refine ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_sM'_k (R := R) (L := L)).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul
      ((hcM.comp ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp (continuous_snd.comp continuous_snd)))).mul
        (((L.cont.comp (hnb'.comp continuous_fst))).mul continuous_const))
  have hth' : Continuous fun β : nA σ L.Y L.b => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_th'_k T'
  let G : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) → nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) → ℂ :=
    fun y p => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM y.2.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k y.1) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x)))))) *
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' p.1
  have hGc : ∀ y, Continuous (G y) := fun y =>
    (hΦc.comp (continuous_const.mul (continuous_const.mul (continuous_const.mul hnew)))).mul (hth'.comp continuous_fst)
  letI : OpensMeasurableSpace d.G := by
    letI : BorelSpace (GL (Fin d.n ⊕ Fin d.n) (AE F E)) := GlobalTheory.EisBL.Borel.borelGL
    exact @BorelSpace.opensMeasurable d.G _ _ (Subtype.borelSpace _)
  have fin2 : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂μN < ⊤ := by
    have hE := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.coordsE_k (R := R) h hc hU hc' hT h𝓐 hP hPc
      (fun g => ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)‖ₑ)
      (Measurable.tsum fun q => (hΦc.comp (continuous_const.mul continuous_id)).enorm.measurable)
      (fun r hr hx g => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_norm_sum_invariant hf z hr hx g) x
    have l1 : ∫⁻ p, (∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x)))‖ₑ) *
        ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ ∂μO < ⊤ := by
      refine lt_of_eq_of_lt ?_ fin1
      refine lintegral_congr fun p => ?_
      rw [← ENNReal.tsum_mul_right]
      exact tsum_congr fun q => (enorm_mul _ _).symm
    rw [hE] at l1
    have l2 : ∫⁻ p, (∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)},
        ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))))‖ₑ) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' p.1‖ₑ
        ∂μN < ⊤ := by
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [hcon, ENNReal.mul_top hcP0] at l1
      exact lt_irrefl _ l1
    refine lt_of_eq_of_lt (lintegral_congr fun p => ?_) l2
    rw [(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_second_term_expand h hf z he _).2, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun y => enorm_mul _ _
  have hGm : ∀ y, AEMeasurable (fun p => ‖G y p‖ₑ) μN := fun y => (hGc y).enorm.measurable.aemeasurable
  have hGlt : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂μN < ⊤ := fun y =>
    lt_of_le_of_lt (lintegral_mono fun p => ENNReal.le_tsum (f := fun y => ‖G y p‖ₑ) y) fin2
  have hGi : ∀ y, Integrable (G y) μN := fun y => ⟨(hGc y).aestronglyMeasurable, hGlt y⟩
  have hGs : Summable fun y => ∫ p, ‖G y p‖ ∂μN := by
    have h1 : ∀ y, ∫ p, ‖G y p‖ ∂μN = (∫⁻ p, ‖G y p‖ₑ ∂μN).toReal := fun y =>
      integral_norm_eq_lintegral_enorm (hGi y).aestronglyMeasurable
    simp_rw [h1]
    refine ENNReal.summable_toReal ?_
    rw [← lintegral_tsum hGm]
    exact fin2.ne
  have e3 : ∫ p, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' p.1 ∂μN =
      ∑' y, ∫ p, G y p ∂μN := by
    rw [(hasSum_integral_of_summable_integral_norm hGi hGs).tsum_eq]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [G]
    rw [(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_second_term_expand h hf z he _).1, tsum_mul_right]
  have hsI : Summable fun y => ∫ p, G y p ∂μN := hGs.of_norm_bounded (fun y => norm_integral_le_integral_norm _)
  rw [hsI.tsum_sigma] at e3
  have hκ' : ∀ g : (Fin L.n → AE F E) × AF F → ℂ, ∫ c, g c ∂(ν.prod (lamA F)) = ((cK.toReal : ℂ))⁻¹ * ∫ c, g c ∂κ := by
    intro g
    rw [hκeq, integral_smul_measure, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hcK0, hcKt⟩)
  have e4 : ∀ q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ∫ p, G ⟨q', c₀⟩ p ∂μN = ((cK.toReal : ℂ))⁻¹ *
      ∫ β in 𝓖', (∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x))) ∂κ) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β ∂lam' := by
    intro q'
    have hi' : ∀ c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, Integrable (G ⟨q', c₀⟩) μN := fun c₀ => hGi _
    have hs' : Summable fun c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L => ∫ p, ‖G ⟨q', c₀⟩ p‖ ∂μN := hGs.sigma_factor q'
    obtain ⟨-, hex⟩ := PositivityTheory.SiegelWeilFormula.Act.exch (μ := lam'.restrict 𝓖') (m := μI) (fun c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L => G ⟨q', c₀⟩) hi' hs'
    have hpr : ∀ c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ∫ p, G ⟨q', c₀⟩ p ∂μN = ∫ β, ∫ v, G ⟨q', c₀⟩ (β, v) ∂μI ∂(lam'.restrict 𝓖') :=
      fun c₀ => integral_prod _ (hi' c₀)
    simp_rw [hpr]
    rw [← hex, ← integral_const_mul]
    refine integral_congr_ae ?_
    have hmq : Measurable fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) =>
        ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ p‖ₑ := Measurable.tsum fun c₀ => (hGc _).enorm.measurable
    have hfinq : ∫⁻ p, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ p‖ₑ ∂μN < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono fun p => ?_) fin2
      exact (ENNReal.le_tsum (f := fun q'' => ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q'', c₀⟩ p‖ₑ) q').trans
        (ENNReal.tsum_sigma' (fun y => ‖G y p‖ₑ)).symm.le
    rw [hμN, lintegral_prod _ hmq.aemeasurable] at hfinq
    have hae := ae_lt_top (hmq.lintegral_prod_right') hfinq.ne
    filter_upwards [hae] with β hβ
    have hG' : ∀ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, G ⟨q', c₀⟩ (β, v) = (∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L,
        _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))) *
          _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β := fun v => by simp only [G]; rw [tsum_mul_right]
    simp_rw [hG']
    rw [integral_mul_const]
    have hjj : L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (L.j (nb' β) * x) = L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x := by rw [map_mul, mul_assoc]
    by_cases hθ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β = 0
    · rw [hθ, mul_zero, mul_zero, mul_zero]
    · have hθe : ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β‖ₑ ≠ 0 := enorm_ne_zero.2 hθ
      have hl : ∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L,
          ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))‖ₑ ∂μI < ⊤ := by
        have e5 : ∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ (β, v)‖ₑ ∂μI = (∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L,
            ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))‖ₑ ∂μI) *
              ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β‖ₑ := by
          rw [← lintegral_mul_const' _ _ enorm_ne_top]
          refine lintegral_congr fun v => ?_
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun c₀ => enorm_mul _ _
        rw [e5] at hβ
        by_contra hcon
        rw [not_lt, top_le_iff] at hcon
        rw [hcon, ENNReal.top_mul hθe] at hβ
        exact lt_irrefl _ hβ
      have hγ : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' ∈ rat2 σ L.Y := (Quot.out q').2
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.unfqE_k h hf z hU h𝓐 hγ (L.j (nb' β) * x)] at hl
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.unfqC_k h hf z hU h𝓐 hγ (L.j (nb' β) * x) hl, hκ']
      simp_rw [hjj]
      ring
  rw [e1, e2, e3]
  simp_rw [e4]
  rw [tsum_mul_left, Complex.real_smul]
  ring
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
