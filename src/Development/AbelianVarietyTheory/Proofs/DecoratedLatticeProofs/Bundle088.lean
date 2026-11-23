module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle062
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulOfSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrbitLocallyConstant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle053
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipB
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormNearNegOneAtRealPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOneIntegral

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def omRight (μ : kˣ →* ℂˣ) : Representation ℂ (GL n k) (SB (Matrix n n' k)) where
  toFun g :=
    { toFun := fun Ψ => ⟨om μ (1 : GL n' k) g Ψ.1, om_mem_SB μ 1 g Ψ.2⟩
      map_add' := fun Φ Ψ => by
        apply Subtype.ext
        funext x
        simp only [om, Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := fun z Φ => by
        apply Subtype.ext
        funext x
        simp only [om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_one' := by
    apply LinearMap.ext
    intro Ψ
    apply Subtype.ext
    exact om_one μ Ψ.1
  map_mul' g h := by
    apply LinearMap.ext
    intro Ψ
    apply Subtype.ext
    show om μ (1 : GL n' k) (g * h) Ψ.1 = om μ 1 g (om μ 1 h Ψ.1)
    rw [← om_mul μ 1 1 g h Ψ.1, mul_one]

variable {c : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]

theorem bilPos_iff_isPos (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (p : ℕ)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) :
    BilPos ψ μ p σ B ↔ IsPos ψ p (omRight μ) σ B := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g Ψ v => h2 g Ψ _ v rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g Ψ Ψ₁ v hΨ => ?_⟩
    have : Ψ₁ = omRight μ g Ψ := Subtype.ext hΨ
    rw [this]
    exact h2 g Ψ v

end GlobalTheory.PosOneIntegral
end

open GlobalTheory.PosOneIntegral in
theorem GlobalTheory.PosOneIntegral.positionOne_invariantIntegral_exchange_step (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) (hν : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [hμX : μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [hμG : μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (hρ' : IsSrc μ ρ') :
    ∀ q : ℕ, q + 1 ≤ c → ∀ (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ (q + 1) σ B →
      ∀ (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ),
      (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG (q + 1) (tInt ψ ν μ (q + 1) σ B F Φ.1) (Rr Φ)) →
      ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
        IsQuotInt ν μX μG 1 (tIntOne ψ ν μ (q + 1) σ B F Φ.1) (toOne ν ρ' (q + 1) Rr Φ) := by
  haveI : ν.IsAddHaarMeasure := hν.1
  intro q
  induction q with
  | zero =>
    intro _ B _ Rr hRr Φ
    exact hRr Φ
  | succ q ih =>
    intro hqc B hB Rr hRr Φ
    have hq1 : 1 ≤ q + 1 := Nat.succ_le_succ (Nat.zero_le q)
    have hqlt : q + 1 < c := by omega

    obtain ⟨B₀, hB₀e, hB₀⟩ := ((GlobalTheory.RootEx.Exchange.exchange_isPos k n c (q + 1) hq1 hqlt ψ hψc hψ1 ν A σ hσ).2.2
      (SB (Matrix n n' k)) (omRight μ) B).2 ((bilPos_iff_isPos ψ μ _ σ B).1 hB)
    have hB₀' : BilPos ψ μ (q + 1) σ B₀ := (bilPos_iff_isPos ψ μ _ σ B₀).2 hB₀
    have hB₀f : ∀ Ψ, (⇑(B₀ Ψ) : A → ℂ) = exDown ν (q + 1) σ (⇑(B Ψ)) := fun Ψ => funext (hB₀e Ψ)

    have hsm' : IsSmoothRep ρ' := (GlobalTheory.T.exists_weilSourceAction_and_smooth k (n' ⊕ Fin (c + 1)) (n ⊕ Fin c) μ hμ).2 ρ' hρ'
    obtain ⟨Rr₀, hRr₀, hRr₀N⟩ := GlobalTheory.T.exists_linear_isQuotInt_tInt_alt k n n' c (q + 1) hq1 hqlt.le ψ hψc hψ1 ν μ hμ μX μG A σ hσ B₀ hB₀' F ρ' hρ'
    have hIH := ih hqlt.le B₀ hB₀' Rr₀ hRr₀ Φ

    have hBup : ∀ Ψ v, B Ψ v = exUp ν (q + 1) σ (B₀ Ψ) v := by
      intro Ψ v
      rw [hB₀f Ψ]
      exact ((GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n c (q + 1) hq1 hqlt ψ hψc hψ1 ν hν A σ hσ (B Ψ) v).2
        (hB.1 Ψ)).symm

    have hRrup : ∀ Φ', Rr Φ' = exUp ν (q + 1) ρ' Rr₀ Φ' := by
      intro Φ'
      have hst := GlobalTheory.T.invariantIntegral_succ_position_eq_exchange k n n' c (q + 1) hq1 hqlt ψ hψc hψ1 ν hν μ hμ μX μG A σ hσ B₀ B hB₀' hBup F ρ' hρ' Rr₀ hRr₀ Φ'
      exact (@GlobalTheory.QuotInt.quotInt_unique_exists k _ _ _ _ _ _ n _ _ c (q + 1 + 1) (by omega) hqc
        ν hν.1 μX hμX μG hμG _).1 _ _ (hRr Φ') hst
    have hdown : exDown ν (q + 1) ρ' (⇑Rr) = ⇑Rr₀ := by
      funext v
      have hRrf : (⇑Rr : _ → ℂ) = exUp ν (q + 1) ρ' ⇑Rr₀ := funext hRrup
      rw [hRrf]
      exact (GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n' (c + 1) (q + 1) hq1 (by omega) ψ hψc hψ1 ν hν _ ρ' hsm' Rr₀ v).1 hRr₀N
    have hval : toOne ν ρ' (q + 1 + 1) Rr Φ = toOne ν ρ' (q + 1) Rr₀ Φ := by
      rw [toOne_succ, hdown]
    have hfun : tIntOne ψ ν μ (q + 1 + 1) σ B F Φ.1 = tIntOne ψ ν μ (q + 1) σ B₀ F Φ.1 := by
      funext h
      simp only [tIntOne]
      rw [toOne_succ]
      congr 1
      funext v
      by_cases hm : opE ψ ν 1 (om μ 1 h Φ.1) ∈ SB (Matrix n n' k)
      · simp only [app, hm, dite_true]
        exact congrFun (hB₀f _).symm v
      · simp [app, hm, exDown]
    rw [hfun, hval]
    exact hIH

theorem GlobalTheory.PosOneIntegral.isQuotInt_toOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ P σ B) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ) (_ : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG P (tInt ψ ν μ P σ B F Φ.1) (Rr Φ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), IsQuotInt ν μX μG 1 (tIntOne ψ ν μ P σ B F Φ.1) (toOne ν ρ' P Rr Φ) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP1 hPc ψ hψc hψ1 ν hν μ hμ μX _ μG _ A _ _ σ hσ B hB F ρ' hρ' Rr hRr Φ
  obtain ⟨q, rfl⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
  exact GlobalTheory.PosOneIntegral.positionOne_invariantIntegral_exchange_step k n n' c ψ hψc hψ1 ν hν μ hμ μX μG A σ hσ F ρ' hρ' q hPc B hB Rr hRr Φ
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL ev)

noncomputable section
namespace GlobalTheory.PosOne

theorem avg_self_and_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∃ Φ₀ : SB (n' → k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 = Φ.1) ∧ ∀ Φ₀ : SB (n' → k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) ∧ (∀ h, opE ψ ν p (om μ 1 h (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1)) = opEFJ ψ ν p Φ₀.1 (om μ 1 h Φ.1)) ∧ ∀ (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ), app L (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1) = ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * L (ρ' (rowE (c + 1) p u) Φ) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψ hψ1 ν hν μ hμ' Φ
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have hF := GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n' ψ hψ hψ1 ν hν
  have main : ∀ Φ₀ : SB (n' → k),
      ∃ w : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 = w.1 ∧
      (∀ h, opE ψ ν p (om μ 1 h w.1) = opEFJ ψ ν p Φ₀.1 (om μ 1 h Φ.1)) ∧
      ∀ L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ,
        L w = ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * L (omR μ (rowE (c + 1) p u, 1) Φ) ∂(Measure.pi fun _ => ν) := by
    intro Φ₀
    have hh := hF.1 Φ₀
    let T : (n' → k) → SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := fun u =>
      GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u • omR μ (rowE (c + 1) p u, 1) Φ
    have hT : IsLocallyConstant T :=
      (hh.1.prodMk ((orbit_locallyConstant (omR_smooth hμ') Φ).comp_continuous
        (ExchangeSupport.continuous_rowE.prodMk continuous_const))).comp fun z => z.1 • z.2
    obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n' → k)
      (Measure.pi fun _ => ν) _ T hT _ hh.2 fun u hu => by
        simp only [T, image_eq_zero_of_notMem_tsupport hu, zero_smul]
    refine ⟨w, funext fun x => (hw (ev x)).symm, fun h => funext fun x₀ => ?_, fun L => ?_⟩
    · refine (hw ((ev x₀).comp ((opL hψ ν p).comp (omR μ (1, h))))).trans ?_
      rw [opEFJ]
      congr 1; funext u
      simp only [T, LinearMap.comp_apply, map_smul, smul_eq_mul]
      congr 1
      have := GlobalTheory.T.rootExchangeOperator_weil_rowUnipotent k n n' c p hp1 hpc ψ hψ ν μ (omR μ (1, h) Φ) u x₀
      rw [← omR_val, omR_mul, one_mul, mul_one] at this
      rw [omR_mul, one_mul, mul_one]
      exact this
    · rw [hw L]
      congr 1; funext u
      simp only [T, map_smul, smul_eq_mul]
  refine ⟨?_, fun Φ₀ => ?_⟩
  · have hU : {u : n' → k | omR μ (rowE (c + 1) p u, 1) Φ = Φ} ∈ 𝓝 (0 : n' → k) :=
      ((omR_smooth hμ' Φ).preimage (ExchangeSupport.continuous_rowE.prodMk continuous_const)).mem_nhds (by
        change omR μ (rowE (c + 1) p 0, 1) Φ = Φ
        rw [ExchangeSupport.rowE_zero, ← Prod.one_eq_mk, map_one, Module.End.one_apply])
    obtain ⟨g, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n' ν _ hU
    obtain ⟨Φ₀, h0⟩ := hF.2 g
    refine ⟨Φ₀, funext fun x => ?_⟩
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg, h0, GlobalTheory.RootEx.FourierJacobi.integral_mul_of_support (z := Φ.1 x) a, a1, one_mul]
    intro u hu
    exact congrArg (fun t : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) => t.1 x) hu
  · obtain ⟨w, e1, e2, e3⟩ := main Φ₀
    refine ⟨e1 ▸ w.2, fun h => e1 ▸ e2 h, fun ρ' hρ' L => ?_⟩
    rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe, e3 L]
    congr 1; funext u
    congr 2
    exact Subtype.ext ((hρ' _ Φ).trans (omR_val μ _ 1 Φ).symm).symm

end GlobalTheory.PosOne
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.InertFrameLoc

open Formalism.UG (IsInertAt)

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

def secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) :
    w.adicCompletion D.host.E →+ AE D :=
  (GlobalTheory.EmbChart.tensAt D.host.E v).toAddMonoidHom.comp
    (GlobalTheory.LFun.InertChart.complEquiv hw h).symm.toRingHom.toAddMonoidHom

def uPt (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E))
    (aT : GL (Fin T.rank) (w.adicCompletion D.host.E))
    (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) : WO S T :=
  (k • (aT.1 * x * (aS⁻¹).1)).map (secW hw h)

def thW (ψ : AddChar (AF D.host.F) ℂ) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (k : w.adicCompletion D.host.E) : AddChar (w.adicCompletion D.host.E) ℂ :=
  ψ.compAddMonoidHom ((Algebra.trace (AF D.host.F) (AE D)).toAddMonoidHom.comp
    ((AddMonoidHom.mulLeft (incA D D.host.xi0)).comp ((secW hw h).comp (AddMonoidHom.mulLeft k))))

variable {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v} {S T : HSp D}
  {k : w.adicCompletion D.host.E} {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)}
  {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)}

theorem thW_apply (ψ : AddChar (AF D.host.F) ℂ) (z : w.adicCompletion D.host.E) :
    thW ψ hw h k z = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * secW hw h (k * z))) := rfl

theorem uPt_add (x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    uPt hw h k aS aT (x + y) = uPt hw h k aS aT x + uPt hw h k aS aT y := by
  ext i j
  simp [uPt, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem uPt_zero : uPt hw h k aS aT (0 : Matrix (Fin T.rank) (Fin S.rank) _) = 0 := by
  ext i j
  simp [uPt]

theorem infPart_tensAt (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    infPart D (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    rw [GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
    show (fstA D.host.F) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin v a)) ⊗ₜ[D.host.F] x = 0
    rw [show (fstA D.host.F) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin v a)) = 0 from rfl, TensorProduct.zero_tmul]
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy, add_zero]

theorem infPart_secW (z : w.adicCompletion D.host.E) : infPart D (secW hw h z) = 0 :=
  infPart_tensAt _

theorem map_infPart_uPt (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    (uPt hw h k aS aT x).map (infPart D) = 0 := by
  ext i j
  exact infPart_secW _

section Anti

open Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil

variable {L : Type} [Field L]

theorem antiJ_herm (σ : L →+* L) (n : ℕ) (i j : Fin n) : σ (antiJ L n i j) = antiJ L n j i := by
  simp only [antiJ]
  rw [show j.val + i.val = i.val + j.val from add_comm _ _]
  split_ifs <;> simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem antiG_mem (n : ℕ) : GlobalTheory.SphTheta.antiG L n ∈ GLint (Fin n) (intL L) := by
  let A : Matrix (Fin n) (Fin n) (intL L) := fun i j => if i.val + j.val + 1 = n then 1 else 0
  have hA : A.map (intL L).subtype = antiJ L n := by
    ext i j
    show ((if i.val + j.val + 1 = n then 1 else 0 : intL L) : L) = antiJ L n i j
    simp only [antiJ]
    split_ifs <;> simp
  have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) (intL L) => M.map (intL L).subtype :=
    fun M N e => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun e i) j)
  have hAA : A * A = 1 := hinj (by
    show (A * A).map (intL L).subtype = (1 : Matrix (Fin n) (Fin n) (intL L)).map (intL L).subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA]
    exact P.fIwasawa_antiJ_mul_antiJ)
  exact ⟨⟨A, A, hAA, hAA⟩, Units.ext hA⟩

end Anti

section Build

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {X : Type} (u : X → WO S T) (f : WO S T → ℂ)

def spanT : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ (Set.range fun x => heisO ψ S T (u x) f)

variable {ψ u f}

theorem mem_spanT_of {g : Module.End ℂ (WO S T → ℂ)} (hg : ∀ x, g (heisO ψ S T (u x) f) ∈ spanT ψ u f) {m : WO S T → ℂ}
    (hm : m ∈ spanT ψ u f) : g m ∈ spanT ψ u f := by
  have key : spanT ψ u f ≤ (spanT ψ u f).comap g := Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    exact hg x)
  exact key hm

theorem heis_mem_spanT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) {m : WO S T → ℂ} (hm : m ∈ spanT ψ u f) :
    heisO ψ S T (u x) m ∈ spanT ψ u f :=
  mem_spanT_of (g := GlobalTheory.SplitScalar.heisL ψ S T (u x)) (fun y => by
    show heisO ψ S T (u x) (heisO ψ S T (u y) f) ∈ spanT ψ u f
    rw [GlobalTheory.SplitScalar.heisO_heisO, ← hu]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x + y, rfl⟩)) hm

theorem self_mem_spanT [Zero X] (hu : u 0 = 0) : f ∈ spanT ψ u f :=
  Submodule.subset_span ⟨0, by
    show heisO ψ S T (u 0) f = f
    rw [hu, GlobalTheory.SplitScalar.heisO_zero]⟩


variable (ψ u f) in
def rhoT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) : Module.End ℂ (spanT ψ u f) :=
  (GlobalTheory.SplitScalar.heisL ψ S T (u x)).restrict fun _ hm => heis_mem_spanT hu x hm

theorem coe_rhoT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) (m : spanT ψ u f) :
    (rhoT ψ u f hu x m : WO S T → ℂ) = heisO ψ S T (u x) m := rfl


variable (ψ u f) in
def omT {G : Type} [Monoid G] (π : G →* Module.End ℂ (WO S T → ℂ))
    (hπ : ∀ g, ∀ m ∈ spanT ψ u f, π g m ∈ spanT ψ u f) : G →* Module.End ℂ (spanT ψ u f) where
  toFun g := (π g).restrict (hπ g)
  map_one' := LinearMap.ext fun m => Subtype.ext (by
    show π 1 m = m
    rw [map_one, Module.End.one_apply])
  map_mul' g g' := LinearMap.ext fun m => Subtype.ext (by
    show π (g * g') m = π g (π g' m)
    rw [map_mul, Module.End.mul_apply])

theorem span_rhoT_eq_top [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (hf : f ∈ spanT ψ u f) :
    Submodule.span ℂ (Set.range fun x => rhoT ψ u f hu x ⟨f, hf⟩) = ⊤ := by
  have e : (Set.range fun x => rhoT ψ u f hu x ⟨f, hf⟩) =
      ((↑) : spanT ψ u f → WO S T → ℂ) ⁻¹' Set.range fun x => heisO ψ S T (u x) f := by
    ext m
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  rw [e]
  exact Submodule.span_span_coe_preimage

end Build

end GlobalTheory.InertFrameLoc

end
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.exists_norm_near_neg_one_at_real_place : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (j : K →+* ℂ), NumberField.ComplexEmbedding.IsReal j → ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (M : ℕ) (W : Set (Ideles E)), W ∈ nhds (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E (InfinitePlace.mk (j.comp (algebraMap E K))) (-1)) → ∃ a : Kˣ, (∀ w ∈ T, w.valuation K ((a : K) - 1) ≤ WithZero.exp (-(M : ℤ))) ∧ Units.map (ReciprocityTheory.Neutral.Bridge.HCFR.infPart E) (diagUnits E (Units.map (Algebra.norm E (S := K)) a)) ∈ W := by
  first | exact @GlobalTheory.NormSign.exists_norm_sign | exact GlobalTheory.NormSign.exists_norm_sign | (intros; apply GlobalTheory.NormSign.exists_norm_sign <;> assumption)
end
