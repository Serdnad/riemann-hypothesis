module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPoincareSeriesThetaVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle030
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle007
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle001
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalCoordsCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle706
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle059
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle056
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutLat
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSerA
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.FinIdemSmulOfReal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle057
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle044
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
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ContinuousDualG
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
open scoped ContDiff
namespace SerA
theorem sig_sig'_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
theorem chi_add_lat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ))
    (hw : w + sgOF σ w = 1) {u : XFF F E nS nT} (hu : u ∈ latF F E nS nT Λ) (x : WOF F E nS nT) :
    phaseF σ JS JT ξ₀ B.ψ w u * (B.ψ (symplOHF σ JS JT ξ₀ x u) * chiLatF σ JS JT ξ₀ B.ψ Λ w (x + u)) =
      chiLatF σ JS JT ξ₀ B.ψ Λ w x := by
  have hσ := _root_.PositivityTheory.ThKW.SerA.sig_sig'_k C.good
  have e : finIdem F E • (x + (u : WOF F E nS nT)) = finIdem F E • x + u := by
    rw [smul_add, finIdem_smul_of_fin u.fin]
  have e2 : B.ψ (symplOHF σ JS JT ξ₀ x u) = B.ψ (symplOHF σ JS JT ξ₀ (finIdem F E • x) u) := by
    have hx := finIdem_add_iota C.chart x
    have h3 := _root_.PositivityTheory.ThKW.beta_iota_left_k C (piWF θ x) (u : WOF F E nS nT)
    rw [piWF_fin u.fin, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h3
    conv_lhs => rw [hx]
    rw [GlobalTheory.HeisLineF.symplOHF_add_left, AddChar.map_add_eq_mul, h3, mul_one]
  unfold chiLatF
  rw [e, e2]
  have hy := finIdem_smul_fin (F := F) (E := E) x
  generalize finIdem F E • x = y at hy ⊢
  by_cases h : y ∈ latOF F E nS nT Λ
  · rw [if_pos h, if_pos (add_mem h hu)]
    have h0 : B.ψ (symplOF σ JS JT ξ₀ (intAF F w • y) u) = 1 :=
      (hA _).1 ((latF F E nS nT Λ).smul_mem w (show XFF.mk y hy ∈ latF F E nS nT Λ from h)) u hu
    rw [phaseF, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad hσ C.hS C.hT C.hξ hw,
      AddChar.map_add_eq_mul, h0, mul_one]
  · have h2 : y + (u : WOF F E nS nT) ∉ latOF F E nS nT Λ := fun h' => h (by
      have h3 := sub_mem h' (mem_latF.1 hu)
      rwa [add_sub_cancel_right] at h3)
    rw [if_neg h, if_neg h2, mul_zero, mul_zero]
theorem main_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) (a : IxF F nS nT → ℂ) :
    ∃ hf : IsThetaFunOF σ JS JT ξ₀ B.ψ (serF σ JS JT ξ₀ B θ ι s Λ w a),
      Fixes (opFF hc w) (latF F E nS nT Λ) (⟨_, hf⟩ : thetaSubF σ JS JT ξ₀ B.ψ) ∧
      IsVacF σ JS JT ξ₀ B.ψ ι s (serF σ JS JT ξ₀ B θ ι s Λ w a) := by
  have hσ := _root_.PositivityTheory.ThKW.SerA.sig_sig'_k C.good
  have hψ : IsCharAF F B.ψ := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B C.good).1
  have hA := hO.sd
  have hw := hO.hw
  obtain ⟨-, hJ, hsym, hpos⟩ := omV_laws
    (_root_.PositivityTheory.ThKW.hermitian_form_selfadjoint_global F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ).1 hs.sq hs.pos
  have hl : ∀ x y z : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ (x + y) z) =
      B.ψ (symplOHF σ JS JT ξ₀ x z) * B.ψ (symplOHF σ JS JT ξ₀ y z) :=
    fun x y z => by rw [GlobalTheory.HeisLineF.symplOHF_add_left, AddChar.map_add_eq_mul]
  have hr : ∀ x y z : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ x (y + z)) =
      B.ψ (symplOHF σ JS JT ξ₀ x y) * B.ψ (symplOHF σ JS JT ξ₀ x z) :=
    fun x y z => by rw [GlobalTheory.HeisLineF.symplOHF_add_right, AddChar.map_add_eq_mul]
  have hd : ∀ x : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ x x) = 1 := fun x => by
    rw [symplOHF, GlobalTheory.HeisLineF.symplOF_self σ JS JT hσ C.hS C.hT ξ₀ C.hξ, mul_zero, AddChar.map_zero_eq_one]
  have hβ : ∀ (x : WOF F E nS nT) (v : IxF F nS nT → ℂ), B.ψ (symplOHF σ JS JT ξ₀ x (iotaA ι v)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWA θ x) v : ℝ)) :=
    fun x v => _root_.PositivityTheory.ThKW.beta_iota_right_k C x v
  have fl : ∀ u ∈ latF F E nS nT Λ, ∀ x : WOF F E nS nT, phaseF σ JS JT ξ₀ B.ψ w u *
      (B.ψ (symplOHF σ JS JT ξ₀ x u) * serF σ JS JT ξ₀ B θ ι s Λ w a (x + u)) = serF σ JS JT ξ₀ B θ ι s Λ w a x :=
    fun u hu x => GlobalTheory.GaussSeriesVacuum.series_inv_scalar (G := WOF F E nS nT)
      (β := fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) hl hr hd hβ a u (piWF_fin u.fin) _ (_root_.PositivityTheory.ThKW.SerA.chi_add_lat_k C hA hw hu) x
  obtain ⟨U, hUo, hlev⟩ := exists_level (F := F) (E := E) (nS := nS) (nT := nT) hG 2 two_pos
  let U₀ : AddSubgroup (WOF F E nS nT) :=
    (latOF F E nS nT Λ).comap (DistribSMul.toAddMonoidHom (WOF F E nS nT) (finIdem F E))
  obtain ⟨fc, fs, fv⟩ := GlobalTheory.GaussSeriesVacuum.series_regular (piWA θ) (iotaA ι)
    (fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) (omV (HMF JS JT ξ₀ (tauB B))) (jV s) (ratLF F E nS nT) U₀ U
    (chiLatF σ JS JT ξ₀ B.ψ Λ w) (_root_.PositivityTheory.ThKW.continuous_piWF_k C) (continuous_iotaVF C.chart) (piWF_iotaVF C.chart) hl hr hd
    (fun x y => hψ.2.1 _)
    (hψ.1.comp (GlobalTheory.RealWeilF.continuous_symplOHF σ JS JT ξ₀ continuous_fst continuous_snd)) hβ hJ hsym hpos
    (by
      rintro _ ⟨y, rfl⟩ h
      have e : piWF θ (ratWF (F := F) y) = 0 := h
      rw [_root_.PositivityTheory.ThKW.piWF_ratWF_k C] at e
      have : y = 0 := infRatF_injective B (by rw [e, map_zero])
      subst this
      exact map_zero _)
    (fun R => by
      refine ((_root_.PositivityTheory.ThKW.finite_lat_k C.good hG R).image (fun y => ratWF (F := F) y)).subset ?_
      rintro _ ⟨⟨y, rfl⟩, h1, h2⟩
      refine ⟨y, ⟨(_root_.PositivityTheory.ThKW.finRatF_mem_iff_k C hG hR hA y).1 h1, ?_⟩, rfl⟩
      have e : piWF θ (ratWF (F := F) y) = infRatF (tauB B) y := _root_.PositivityTheory.ThKW.piWF_ratWF_k C y
      rw [← e]
      exact h2)
    (fun x hx => by unfold chiLatF; exact if_neg hx)
    (fun x => by
      unfold chiLatF
      split_ifs
      · exact (hψ.2.1 _).le
      · rw [norm_zero]; exact zero_le_one)
    (fun x v => by
      show chiLatF σ JS JT ξ₀ B.ψ Λ w (x + iotaVF ι v) = _
      unfold chiLatF
      rw [smul_add, finIdem_smul_of_real (real_iotaVF C.chart v), add_zero])
    hUo
    (fun u hu x => by
      obtain ⟨l, hl', e⟩ := hlev u hu
      have e3 : u - iotaA ι (piWA θ u) = ((2 • l : XFF F E nS nT) : WOF F E nS nT) :=
        (sub_eq_of_eq_add (finIdem_add_iota C.chart u)).trans e
      rw [e3]
      have e2 := _root_.PositivityTheory.ThKW.SerA.chi_add_lat_k C hA hw (nsmul_mem hl' 2) x
      rw [phase_two' hA w hl', one_mul] at e2
      exact e2) a
  have hquasi : ∀ (γ : Matrix (Fin nT) (Fin nS) E) (x : WOF F E nS nT),
      serF σ JS JT ξ₀ B θ ι s Λ w a (ratWF γ + x) =
        B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) x)) * serF σ JS JT ξ₀ B θ ι s Λ w a x := by
    intro γ x
    have e : B.ψ (symplOHF σ JS JT ξ₀ (ratWF γ) x) * serF σ JS JT ξ₀ B θ ι s Λ w a (ratWF γ + x) =
        serF σ JS JT ξ₀ B θ ι s Λ w a x :=
      GlobalTheory.HeisenbergGaussianSeries.series_quasi (G := WOF F E nS nT) (p := piWA θ) (ι := iotaA ι)
        (β := fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) (om := omV (HMF JS JT ξ₀ (tauB B))) (J := jV s)
        (Γ := ratLF F E nS nT) (χ := chiLatF σ JS JT ξ₀ B.ψ Λ w) hl hr
        (by rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩; exact _root_.PositivityTheory.ThKW.psi_rat_k C y y') a (ratWF γ) ⟨γ, rfl⟩ x
    rw [← e, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have hlevel : ∀ u ∈ U, u.map (infPartF F E) = 0 →
      heisOF σ JS JT ξ₀ B.ψ u (serF σ JS JT ξ₀ B θ ι s Λ w a) = serF σ JS JT ξ₀ B θ ι s Λ w a := by
    intro u hu h
    obtain ⟨l, hl', e⟩ := hlev u hu
    rw [finIdem_smul_of_fin h] at e
    subst e
    funext x
    have e2 := fl _ (nsmul_mem hl' 2) x
    rw [phase_two' hA w hl', one_mul] at e2
    exact e2
  have hsm : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L → (∀ t, (L t).map (finPartF F E) = 0) →
      ∀ x, ContDiff ℝ ∞ fun t => serF σ JS JT ξ₀ B θ ι s Λ w a (x + L t) := by
    intro k L hL hL0 x
    let c : (Fin k → ℝ) →+ (IxF F nS nT → ℂ) := (piWA θ).comp L
    have hc : Continuous c := (_root_.PositivityTheory.ThKW.continuous_piWF_k C).comp hL
    have hLc : ∀ t, L t = iotaA ι (c t) := fun t => by
      have := finIdem_add_iota C.chart (L t)
      rw [finIdem_smul_of_real (hL0 t), zero_add] at this
      exact this
    have h := (fs x).comp (c.toRealLinearMap hc).contDiff
    refine (congrArg (ContDiff ℝ ∞) (funext fun t => ?_)).mp h
    show _ = serF σ JS JT ξ₀ B θ ι s Λ w a (x + L t)
    rw [hLc t]
    rfl
  refine ⟨⟨hquasi, ⟨U, hUo, hlevel⟩, fc, hsm⟩, fun u hu => Subtype.ext (funext fun x => ?_), fun x z => fv x z⟩
  rw [coe_opFF]
  exact fl u hu x
end SerA
end PositivityTheory.ThKW
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace PositivityTheory.ThKW
def ThetaLiftNonvanishing : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
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
              ∃ (dd : Darboux (symp (cA σ) ξ (incM F JB) (dbl (incM F JA))) (κ ⊕ κ))
                (omd : UG (cA σ) (dbl (incM F JA)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)),
                IsDblCoord (cA σ) ξ (incM F JB) (incM F JA) (GlobalTheory.WeilSchrodinger.transD (cA σ) co) dd ∧
                IsUWeilSplit (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (dbl (incM F JA)) dd χS (diagCols (Fin nT)) omd ∧
                ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (dbl (incM F JA))),
                  gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                  ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂
def ThetaLiftConvergence : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
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
              ∃ (dd : Darboux (symp (cA σ) ξ (incM F JA) (dbl (incM F JB))) (κ ⊕ κ))
                (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)),
                IsDblCoord (cA σ) ξ (incM F JA) (incM F JB) co dd ∧
                IsUWeilSplit (cA σ) (adeleClass F) B.ψ ξ (incM F JA) (dbl (incM F JB)) dd χT (diagCols (Fin nS)) omd ∧
                ∀ (g : UG (cA σ) (incM F JB)) (gd : UG (cA σ) (dbl (incM F JB))),
                  gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                  ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open Formalism.IndefR.DatumF Sw in

theorem dblS_of_dblT_k (H : _root_.PositivityTheory.ThKW.ThetaLiftNonvanishing) : _root_.PositivityTheory.ThKW.ThetaLiftConvergence := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ hL χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have lS := invT_mul hS
  have lT := invT_mul hT
  have hsm : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) E), incM F (ξ₀ • M) = incAF F E ξ₀ • incM F M := fun M => by
    ext i j
    exact map_mul (incAF F E) _ _
  have hB' : ξ • incM F JB = incAF F E ξ₀ • incM F JS⁻¹ := hBm.trans (hsm _)
  have hx : IsUnit (incAF F E ξ₀) := (IsUnit.mk0 _ hξ).map _
  have hd : IsUnit (incM F JS⁻¹).det := by
    have h1 : IsUnit (JS⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)
    have h2 : (incM F JS⁻¹).det = incAF F E (JS⁻¹).det := (RingHom.map_det (incAF F E) _).symm
    rw [h2]
    exact h1.map _
  have hle := ug_le (cA σ) hB' hx hd
  have hge := ug_ge (cA σ) hB' hx
  have hD := smul_dbl hB'
  have hge' := ug_ge (cA σ) hD hx
  have htr := swap_transport σ lS lT B.ψ hle co _ (castD_transD_rho _ hB' co B.ψ) hom _ (swapHom_apply hle om)
  have hrat' : ∀ x : Matrix (Fin nS) (Fin nT) E, ∃ y z : κ → F,
      (castD _ hB' (GlobalTheory.WeilSchrodinger.transD (cA σ) co)).e (incM F x) =
        (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    obtain ⟨y, z, h⟩ := hrat xᵀ
    exact ⟨y, z, (castD_transD_e _ hB' co _).trans h⟩
  have g1 : JS⁻¹ = (JS⁻¹ᵀ)ᵀ := (Matrix.transpose_transpose _).symm
  have g2 : incAF F E ξ₀ • incM F JA = incM F (ξ₀ • (JT⁻¹ᵀ)⁻¹) := by
    rw [(dual_inv lT).2, hsm, hA]
  obtain ⟨dd, omd, k1, k2, k3⟩ := H F E σ B hB nT nS JT⁻¹ᵀ JS⁻¹ᵀ (isHermND_invT hT) (isHermND_invT hS) ξ₀ hξ hσξ
    (LatH.swap hS hT hL) χT χS cT cS rT rS _ (swap_datum σ lS lT ξ₀ B.ψ hω) JS⁻¹ JA (incAF F E ξ₀) g1 g2 κ _ hrat' _ htr
  refine ⟨castD₂ _ hD dd, omd.comp (Subgroup.inclusion hge'), isDblCoord_cast₂ _ hB' co k1,
    isUWeilSplit_cast₂ _ hD hge' (isLagr_diagCols _ _) k2, fun g gd hgd φ₁ hφ₁ φ₂ hφ₂ => ?_⟩
  have k4 := k3 (Subgroup.inclusion hge g) (Subgroup.inclusion hge' gd) hgd φ₁ hφ₁ φ₂ hφ₂
  rw [swapHom_fst] at k4
  rw [MonoidHom.comp_apply]
  exact k4
end PositivityTheory.ThKW
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ThetaTransformF
open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff
section Phase
variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}
end Phase
end GlobalTheory.ThetaTransformF
end
noncomputable section
namespace GlobalTheory.ThetaTransformF
open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff
section Crit
variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}
end Crit
end GlobalTheory.ThetaTransformF
end
noncomputable section
namespace GlobalTheory.ThetaTransformF
open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Invertible (2 : AF F)]
  {σ : E →ₐ[F] E} {nS nT N : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ} {e : WOF F E nS nT ≃ₗ[AF F] VA F N}
end Main
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem isThetaFunOF_thV_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ hstd N e he hrat Φ hΦ
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hstd.1
  obtain ⟨hc, -, hfin, hinf⟩ := coordF nT nS N e
  have hcont : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Continuous (thV B.ψ Φ) := fun Φ hΦ =>
    GlobalTheory.T.continuous_adelicThetaTransformSymplectic_of_decay F N B.ψ hR hψ Φ (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ)
  refine ⟨fun γ w => ?_, ?_, (hcont Φ hΦ).comp hc, ?_⟩
  · obtain ⟨y, z, h⟩ := hrat γ
    simp only [Function.comp_apply, map_add (f := _), symplOHF_eq he, h]
    exact quasiV_thV B.ψ hψ.2.2.1 Φ y z (e w)
  · obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.adelicSchwartz_fixed_by_schroedinger_open_finite_subgroup F N B.ψ hR hψ Φ hΦ
    refine ⟨U.comap e.toLinearMap.toAddMonoidHom, hUo.preimage hc, fun u hu h0 => ?_⟩
    rw [heisOF_comp he, ← thV_schr, hU (e u) hu ((hinf u).1 h0).1 ((hinf u).1 h0).2]
  · intro k L hL hL0 w
    have h := contDiff_of_heisV_closed B.ψ hψ.1 {g | ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), g = thV B.ψ Φ}
      (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hcont Φ hΦ)
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ M hM
        obtain ⟨Φ', hΦ', hd⟩ := GlobalTheory.T.hasDerivAt_heisenbergOperator_thetaTransform_realLine F N B.ψ hR hψ Φ hΦ M hM
        exact ⟨_, ⟨Φ', hΦ', rfl⟩, hd⟩)
      _ ⟨Φ, hΦ, rfl⟩ k (e.toLinearMap.toAddMonoidHom.comp L) (hc.comp hL) (fun t => (hfin _).1 (hL0 t)) (e w)
    simpa [Function.comp_def] using h
end GlobalTheory.ThetaTransformF
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.theta_preserving_endomorphism_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ M : Module.End ℂ (WOF F E nS nT → ℂ),
      (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f)) →
      (∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ w f) = heisOF σ JS JT ξ₀ B.ψ w (M f)) →
      (∀ (μ : MeasureTheory.Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        MeasureTheory.IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
      ∃ c : ℂ, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  first | exact @_root_.GlobalTheory.ThetaSchurF.schur_k | exact _root_.GlobalTheory.ThetaSchurF.schur_k | (intros; apply _root_.GlobalTheory.ThetaSchurF.schur_k <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace PositivityTheory.ThKF0
theorem thetaBasic_k : _root_.GlobalTheory.ThK.ThetaBasic_k := _root_.PositivityTheory.ThKF0.thetaBasic_of_k _root_.PositivityTheory.ThKF0.weil_schwartz_decay_bound
end PositivityTheory.ThKF0
end
end

section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.eisenstein_half_plane_holds : _root_.SiegelEisensteinSeries.EisHalf_k := by
  first | exact @_root_.GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf_k | exact _root_.GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf_k | (intros; apply _root_.GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf_k <;> assumption)
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem thetaAuto_at_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) :
    d.μ d.D ≠ 0 ∧ d.μ d.D ≠ ⊤ ∧ ∀ Φ ∈ d.sch,
      (∀ x, IntegrableOn (fun g => thetaSum F (d.om x (d.S g Φ))) d.D d.μ) ∧ Continuous (d.I Φ) ∧
      ∀ γ ∈ rat2 σ d.Y, ∀ x, d.I Φ (γ * x) = d.I Φ x := by
  have hc := _root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d
  haveI := hc.cnt
  haveI := d.ok.haar
  have hom : ∀ x, ∀ Ψ ∈ d.sch, d.om x Ψ ∈ d.sch := fun x Ψ hΨ => d.ok.dbl.weil.2.1.pres x Ψ hΨ
  have hcomm : ∀ Φ ∈ d.sch, ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ) := fun Φ hΦ => (hT F E σ d Φ hΦ).2
  obtain ⟨Λ, hΛ, hΛv⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.exists_meanAdm_k hS hP hT d
  refine ⟨fd_ne d.ok.dom, (hc.fin d.μ d.D d.ok.haar d.ok.dom).ne, fun Φ hΦ => ⟨fun x => ?_, ?_, fun γ hγ x => ?_⟩⟩
  · simp only [hcomm Φ hΦ]
    exact _root_.PositivityTheory.SiegelWeilFormula.Tauto.intOn_S_k hS hP hT d (hom x Φ hΦ)
  · have e : d.I Φ = fun x => Λ (d.om x Φ) := funext fun x => by
      rw [hΛv _ (hom x Φ hΦ)]
      show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ x = _
      rw [PositivityTheory.SiegelWeilFormula.thetaMean, setAverage_eq]
      simp only [hcomm Φ hΦ]
    rw [e]
    exact d.ok.dbl.weil.2.1.cont Λ hΛ Φ hΦ
  · show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ (γ * x) = PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ x
    simp only [PositivityTheory.SiegelWeilFormula.thetaMean, map_mul, Module.End.mul_apply]
    refine congrArg (fun f : UA σ d.A.J → ℂ => ⨍ g in d.D, f g ∂d.μ) (funext fun g => ?_)
    exact _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaSum_rational_invariant d γ hγ _ (hom x _ (d.ok.dbl.lin.pres g Φ hΦ))
theorem thetaAuto_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k :=
  fun _ _ _ _ _ _ _ _ d => _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaAuto_at_k hS hP hT d
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end
