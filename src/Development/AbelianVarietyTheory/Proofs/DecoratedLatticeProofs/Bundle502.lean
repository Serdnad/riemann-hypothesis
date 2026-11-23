module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle476
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle271
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle496
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle400
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle497
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlace
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiActCont

variable {D : D7} {X Y A S A' : HSp D} (d : OrthDec X S A) (e : OrthDec Y S A')

def four (C : WO A S → WO S A' → ℂ) (φ₁ : WO A A' → ℂ) (φ₂ : WO S S → ℂ) : WO X Y → ℂ := fun x =>
  C (sandwich e.pA d.jB x) (sandwich e.pB d.jA x) * (φ₁ (sandwich e.pB d.jB x) * φ₂ (sandwich e.pA d.jA x))

theorem four_eq (C : WO A S → WO S A' → ℂ) (φ₁ : WO A A' → ℂ) (φ₂ : WO S S → ℂ) (x : WO X Y) :
    four d e C φ₁ φ₂ x = C (e.resT A (d.resS Y x).2).1 (e.resT S (d.resS Y x).1).2 *
      (φ₁ (e.resT A (d.resS Y x).2).2 * φ₂ (e.resT S (d.resS Y x).1).1) := by
  simp only [four, sandwich_apply, OrthDec.resT_apply, OrthDec.resS_apply, Matrix.mul_assoc]

theorem four_symm (C : WO A S → WO S A' → ℂ) (φ₁ : WO A A' → ℂ) (φ₂ : WO S S → ℂ) (s₁ : WO S S) (s₂ : WO S A')
    (u₁ : WO A S) (u₂ : WO A A') :
    four d e C φ₁ φ₂ ((d.resS Y).symm ((e.resT S).symm (s₁, s₂), (e.resT A).symm (u₁, u₂))) =
      C u₁ s₂ * (φ₁ u₂ * φ₂ s₁) := by
  simp only [four_eq, AddEquiv.apply_symm_apply]

theorem symplOH_four (x y : WO X Y) : symplOH X Y x y =
    symplOH A S (sandwich e.pA d.jB x) (sandwich e.pA d.jB y) + symplOH S A' (sandwich e.pB d.jA x) (sandwich e.pB d.jA y) +
    (symplOH A A' (sandwich e.pB d.jB x) (sandwich e.pB d.jB y) +
      symplOH S S (sandwich e.pA d.jA x) (sandwich e.pA d.jA y)) := by
  rw [d.symplOH_resS, e.symplOH_resT, e.symplOH_resT]
  simp only [sandwich_apply, OrthDec.resT_apply, OrthDec.resS_apply, Matrix.mul_assoc]
  ring

variable {ψ : AddChar (AF D.host.F) ℂ} {C : WO A S → WO S A' → ℂ} {φ₁ : WO A A' → ℂ} {φ₂ : WO S S → ℂ}

theorem isThetaFunO_four (h : IsBiTheta ψ A S A' C) (h₁ : IsThetaFunO ψ A A' φ₁) (h₂ : IsThetaFunO ψ S S φ₂) :
    IsThetaFunO ψ X Y (four d e C φ₁ φ₂) := {
  quasi γ w := by
    have e₁ : sandwich e.pA d.jB (ratW Y X γ) = ratW S A (e.qA * γ * d.iB) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    have e₂ : sandwich e.pB d.jA (ratW Y X γ) = ratW A' S (e.qB * γ * d.iA) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    have e₃ : sandwich e.pB d.jB (ratW Y X γ) = ratW A' A (e.qB * γ * d.iB) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    have e₄ : sandwich e.pA d.jA (ratW Y X γ) = ratW S S (e.qA * γ * d.iA) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    rw [symplOH_four d e]
    simp only [four, map_add (f := _)]
    rw [e₁, e₂, e₃, e₄, h.quasiL, h.quasiR, h₁.quasi, h₂.quasi]
    simp only [neg_add, AddChar.map_add_eq_mul]
    ring
  level := by
    obtain ⟨U₁, hU₁, k₁⟩ := h.levL
    obtain ⟨U₂, hU₂, k₂⟩ := h.levR
    obtain ⟨U₃, hU₃, k₃⟩ := h₁.level
    obtain ⟨U₄, hU₄, k₄⟩ := h₂.level
    refine ⟨(U₁.comap (sandwich e.pA d.jB) ⊓ U₂.comap (sandwich e.pB d.jA)) ⊓
      (U₃.comap (sandwich e.pB d.jB) ⊓ U₄.comap (sandwich e.pA d.jA)),
      ((hU₁.preimage (continuous_sandwich _ _)).inter (hU₂.preimage (continuous_sandwich _ _))).inter
      ((hU₃.preimage (continuous_sandwich _ _)).inter (hU₄.preimage (continuous_sandwich _ _))), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1.1 (map_sandwich _ _ _ h0) (sandwich e.pB d.jA w + sandwich e.pB d.jA u))
      (sandwich e.pA d.jB w)
    have e₂ := congrFun (k₂ _ hu.1.2 (map_sandwich _ _ _ h0) (sandwich e.pA d.jB w)) (sandwich e.pB d.jA w)
    have e₃ := congrFun (k₃ _ hu.2.1 (map_sandwich _ _ _ h0)) (sandwich e.pB d.jB w)
    have e₄ := congrFun (k₄ _ hu.2.2 (map_sandwich _ _ _ h0)) (sandwich e.pA d.jA w)
    simp only [heisO] at e₁ e₂ e₃ e₄ ⊢
    rw [symplOH_four d e]
    simp only [four, map_add (f := _), AddChar.map_add_eq_mul]
    rw [← e₂, ← e₁, ← e₃, ← e₄]
    ring
  cont := (h.cont.comp ((continuous_sandwich _ _).prodMk (continuous_sandwich _ _))).mul
    ((h₁.cont.comp (continuous_sandwich _ _)).mul (h₂.cont.comp (continuous_sandwich _ _)))
  smooth k L hL h0 w := by
    simp only [four, map_add (f := _)]
    exact (h.smooth k ((sandwich e.pA d.jB).comp L) ((sandwich e.pB d.jA).comp L) ((continuous_sandwich _ _).comp hL)
      ((continuous_sandwich _ _).comp hL) (fun t => map_sandwich _ _ _ (h0 t)) (fun t => map_sandwich _ _ _ (h0 t)) _ _).mul
      ((h₁.smooth k ((sandwich e.pB d.jB).comp L) ((continuous_sandwich _ _).comp hL)
        (fun t => map_sandwich _ _ _ (h0 t)) _).mul
      (h₂.smooth k ((sandwich e.pA d.jA).comp L) ((continuous_sandwich _ _).comp hL)
        (fun t => map_sandwich _ _ _ (h0 t)) _)) }

theorem end_const_mul {Z : Type} (L : Module.End ℂ (Z → ℂ)) (c : ℂ) (f : Z → ℂ) (z : Z) :
    L (fun y => c * f y) z = c * L f z :=
  congrFun (L.map_smul c f) z

theorem om_four {χA χS χS' χA' : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S A'} {Ω : Om X Y} {ΩS : Om S Y}
    {ΩA : Om A Y} {ω₁ : Om A A'} {ω₂ : Om S S} (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb)
    (hΩ : IsWeilDatumO ψ X Y (χS' * χA) (χS * χA') Ω) (hS : IsWeilDatumO ψ S Y χS' (χS * χA') ΩS)
    (hA : IsWeilDatumO ψ A Y χA (χS * χA') ΩA) (hω₁ : IsWeilDatumO ψ A A' χA χA' ω₁) (hω₂ : IsWeilDatumO ψ S S χS' χS ω₂)
    (hΦ : IsThetaFunO ψ X Y (four d e C φ₁ φ₂)) (a : GA D A) (h h' : GA D S) (b : GA D A') (w : WO A S) (w' : WO S A') :
    Ω (d.emb (h', a), e.emb (h, b)) (four d e C φ₁ φ₂)
        ((d.resS Y).symm ((e.resT S).symm (0, w'), (e.resT A).symm (w, 0))) =
      (ω₁ (a, b) φ₁ 0 * ω₂ (h', h) φ₂ 0) * omb (h', b) (fun v => oma (a, h) (fun u => C u v) w) w' := by
  have hψ := ha.std
  have tS := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hψ X S A d Y
  have tA := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hψ Y S A' e A
  have tB := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hψ Y S A' e S
  obtain ⟨th, ev⟩ := tS.om_slice χS' χA (χS * χA') Ω ΩS ΩA hΩ hS hA h' a (e.emb (h, b)) _ hΦ ((e.resT A).symm (w, 0))
  have inner : ∀ s₁ s₂, ΩA (a, e.emb (h, b))
      (fun v' => four d e C φ₁ φ₂ ((d.resS Y).symm ((e.resT S).symm (s₁, s₂), v'))) ((e.resT A).symm (w, 0)) =
      (ω₁ (a, b) φ₁ 0 * φ₂ s₁) * oma (a, h) (fun u => C u s₂) w := by
    intro s₁ s₂
    rw [(tA.om_slice χA χS χA' ΩA oma ω₁ hA ha hω₁ a h b _ ((tS.slice_theta _ hΦ).2 _) 0).2 w, ← end_const_mul]
    refine congrArg (fun f => oma (a, h) f w) (funext fun u => ?_)
    have : (fun v' => four d e C φ₁ φ₂ ((d.resS Y).symm ((e.resT S).symm (s₁, s₂), (e.resT A).symm (u, v')))) =
        fun v' => (C u s₂ * φ₂ s₁) * φ₁ v' := by
      funext v'; rw [four_symm]; ring
    rw [this, end_const_mul]; ring
  rw [ev, (tB.om_slice χS' χS χA' ΩS ω₂ omb hS hω₂ hb h' h b _ th w').2 0]
  simp only [inner, end_const_mul]
  have : (fun s₁ => ω₁ (a, b) φ₁ 0 * φ₂ s₁ * omb (h', b) (fun v => oma (a, h) (fun u => C u v) w) w') =
      fun s₁ => (ω₁ (a, b) φ₁ 0 * omb (h', b) (fun v => oma (a, h) (fun u => C u v) w) w') * φ₂ s₁ := by
    funext s₁; ring
  rw [this, end_const_mul]; ring

theorem exists_kernel_ne_zero {V W : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χ χ' om)
    (p : GA D V × GA D W) : ∃ f, IsThetaFunO ψ V W f ∧ om p f 0 ≠ 0 := by
  obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero h.std V W
  obtain ⟨w, hw⟩ := Function.ne_iff.1 f0
  refine ⟨om p⁻¹ (heisO ψ V W w f), h.om_pres _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all h.std hf w), ?_⟩
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, heisO, zero_add,
    symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]
  exact hw

theorem hecke_mul {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') : IsHeckeChar D (χ * χ') :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2, h'.2, mul_one]⟩

theorem continuous_biAct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'), IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C → Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' => omb x.2.1 (fun v => oma x.1 (fun u => C u v) x.2.2.1) x.2.2.2 := by
  intro D ψ A S A' χA χS χS' χA' oma omb ha hb C hC
  have hψ := ha.std
  have ex := GlobalTheory.T.exists_weilDatum_hermitianPair D
  obtain ⟨X, ⟨d⟩⟩ : ∃ X, Nonempty (OrthDec X S A) := ⟨_, ⟨GlobalTheory.BiTransfer.sumDec S A⟩⟩
  obtain ⟨Y, ⟨e⟩⟩ : ∃ Y, Nonempty (OrthDec Y S A') := ⟨_, ⟨GlobalTheory.BiTransfer.sumDec S A'⟩⟩
  have hY := hecke_mul ha.hecT hb.hecT
  have rY : ResEta D (χS * χA') Y.rank := e.rank_add ▸ resEta_mul ha.resT hb.resT
  have rX : ResEta D (χS' * χA) X.rank := d.rank_add ▸ resEta_mul hb.resS ha.resS
  obtain ⟨Ω, hΩ⟩ := ex X Y ψ _ _ hψ (hecke_mul hb.hecS ha.hecS) hY rX rY
  obtain ⟨ΩS, hS⟩ := ex S Y ψ _ _ hψ hb.hecS hY hb.resS rY
  obtain ⟨ΩA, hA⟩ := ex A Y ψ _ _ hψ ha.hecS hY ha.resS rY
  obtain ⟨ω₁, hω₁⟩ := ex A A' ψ _ _ hψ ha.hecS hb.hecT ha.resS hb.resT
  obtain ⟨ω₂, hω₂⟩ := ex S S ψ _ _ hψ hb.hecS ha.hecT hb.resS ha.resT
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨φ₁, h₁, n₁⟩ := exists_kernel_ne_zero hω₁ (x₀.1.1, x₀.2.1.2)
  obtain ⟨φ₂, h₂, n₂⟩ := exists_kernel_ne_zero hω₂ (x₀.2.1.1, x₀.1.2)
  have hΦ := isThetaFunO_four d e hC h₁ h₂
  have cK : Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' =>
      ω₁ (x.1.1, x.2.1.2) φ₁ 0 * ω₂ (x.2.1.1, x.1.2) φ₂ 0 :=
    ((hω₁.om_cont _ h₁ 0).comp (continuous_fst.fst.prodMk continuous_snd.fst.snd)).mul
      ((hω₂.om_cont _ h₂ 0).comp (continuous_snd.fst.fst.prodMk continuous_fst.snd))
  have cG : Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' =>
      ((d.emb (x.2.1.1, x.1.1), e.emb (x.1.2, x.2.1.2)),
        (d.resS Y).symm ((e.resT S).symm (0, x.2.2.2), (e.resT A).symm (x.2.2.1, 0))) :=
    ((d.continuous_emb.comp (continuous_snd.fst.fst.prodMk continuous_fst.fst)).prodMk
      (e.continuous_emb.comp (continuous_fst.snd.prodMk continuous_snd.fst.snd))).prodMk
      ((d.continuous_resS_symm Y).comp
        (((e.continuous_resT_symm S).comp (continuous_const.prodMk continuous_snd.snd.snd)).prodMk
          ((e.continuous_resT_symm A).comp (continuous_snd.snd.fst.prodMk continuous_const))))
  have cN := (GlobalTheory.Unf.jointCont_all D ψ X Y _ _ Ω hΩ _ hΦ).comp cG
  have nK := mul_ne_zero n₁ n₂
  refine (cN.continuousAt.div cK.continuousAt nK).congr ?_
  filter_upwards [cK.continuousAt.eventually_ne nK] with x hx
  rw [Pi.div_apply, div_eq_iff hx, mul_comm]
  exact om_four d e ha hb hΩ hS hA hω₁ hω₂ hΦ _ _ _ _ _ _

end GlobalTheory.BiActCont

end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

section Model

variable {X Y G H : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [Monoid G] [Monoid H]

theorem exists_hom_of_model (P : X → Prop) (s : X → Y) (S : Submodule ℂ Y)
    (hadd : ∀ f f', P f → P f' → P (f + f') ∧ s (f + f') = s f + s f')
    (hsmul : ∀ (c : ℂ) f, P f → P (c • f) ∧ s (c • f) = c • s f)
    (hin : ∀ f, P f → s f ∈ S) (honto : ∀ φ ∈ S, ∃ f, P f ∧ s f = φ)
    (hinj : ∀ f f', P f → P f' → s f = s f' → f = f')
    (om : G →* Module.End ℂ X) (hpres : ∀ g f, P f → P (om g f)) (κ : G ≃* H) :
    ∃ ρ : H →* Module.End ℂ S, ∀ g f, P f → ∀ Φ : S, Φ.1 = s f → (ρ (κ g) Φ).1 = s (om g f) := by
  classical
  choose lift hlP hls using fun Φ : S => honto Φ.1 Φ.2
  have hlift : ∀ (Φ : S) f, P f → Φ.1 = s f → lift Φ = f := fun Φ f hf h =>
    hinj _ _ (hlP Φ) hf ((hls Φ).trans h)
  let act : H → Module.End ℂ S := fun h =>
    { toFun := fun Φ => ⟨s (om (κ.symm h) (lift Φ)), hin _ (hpres _ _ (hlP Φ))⟩
      map_add' := fun Φ Ψ => by
        have e : lift (Φ + Ψ) = lift Φ + lift Ψ :=
          hlift _ _ (hadd _ _ (hlP Φ) (hlP Ψ)).1 (by rw [(hadd _ _ (hlP Φ) (hlP Ψ)).2, hls, hls]; rfl)
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [e, map_add (f := _)]
        exact (hadd _ _ (hpres _ _ (hlP Φ)) (hpres _ _ (hlP Ψ))).2
      map_smul' := fun c Φ => by
        have e : lift (c • Φ) = c • lift Φ :=
          hlift _ _ (hsmul c _ (hlP Φ)).1 (by rw [(hsmul c _ (hlP Φ)).2, hls]; rfl)
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [e, map_smul]
        exact (hsmul c _ (hpres _ _ (hlP Φ))).2 }
  have hact : ∀ h (Φ : S), ((act h Φ : S) : Y) = s (om (κ.symm h) (lift Φ)) := fun _ _ => rfl
  refine ⟨{ toFun := act, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [hact, map_one, map_one]
    exact hls Φ
  · intro h₁ h₂
    refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [Module.End.mul_apply, hact, hact, map_mul, map_mul, Module.End.mul_apply,
      hlift (act h₂ Φ) _ (hpres _ _ (hlP Φ)) (hact h₂ Φ)]
  · intro g f hf Φ hΦ
    show s (om (κ.symm (κ g)) (lift Φ)) = s (om g f)
    rw [κ.symm_apply_apply, hlift Φ f hf hΦ]

end Model

theorem exists_transport_std : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, ∃ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS := by
  intro D ψ A B χB omh hW ν 𝓨 hν θ hθ κ
  have hS := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hW.std θ hθ A B ν 𝓨 hν
  have hL := GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hW.std A B ν 𝓨 hν
  obtain ⟨ρ, hρ⟩ := exists_hom_of_model (IsThetaFunO ψ (dblSp A) B) (sch ψ A B ν 𝓨) (schwartzA θ B.rank A.rank)
    (fun f f' hf hf' => ⟨(hL f f' hf hf' 0).1, (hL f f' hf hf' 0).2.2.1⟩)
    (fun c f hf => ⟨(hL f f hf hf c).2.1, (hL f f hf hf c).2.2.2⟩)
    hS.1 hS.2.1 hS.2.2 (omh.comp (MonoidHom.inl _ _)) (fun g f hf => hW.om_pres _ _ hf) κ
  exact ⟨ρ, fun g f hf Φ hΦ => hρ g f hf Φ hΦ⟩

end GlobalTheory.StdUnn

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw.LastPrim
variable {D : D7}

theorem latV_entry_mem' {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, -, hβ, c, -, x, -, rfl⟩ := hz
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hβ _
  | zero => exact zero_mem _
  | add z z' _ _ hz hz' => exact add_mem hz hz'
  | neg z _ hz => exact neg_mem hz

theorem incAdj_yZero_mulVec : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (hρ : 0 < ρ) (a : AE D) (y : Fin B.V₀.rank → AE D),
    Matrix.mulVec (show Matrix (Fin J.W.rank) (Fin B.V₀.rank) (AE D) from J.d.incAdj B.V₀ (a • yZero B.V₀ ρ (vecB B.o B.ζ))) y =
      colMul J.d.jY ⟨ρ - 1, by omega⟩ (incA D D.host.xi0⁻¹ * cA D a * (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l)) := by
  intro D ρ B J hρ a y
  funext k
  have hell : ∀ i : Fin ρ, cA D (ell D ρ i) = if i = ⟨ρ - 1, by omega⟩ then 1 else 0 := by
    intro i
    simp only [ell, Fin.ext_iff]
    split_ifs with h1 h2 h2 <;> first | omega | simp
  simp only [HypDec.incAdj_apply, HypDec.incY_apply, yZero, zEll, adj_smul, adj_neg, colMul, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply, adj, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_mul, map_neg, hell]
  rw [Finset.sum_congr rfl fun l _ => by
    rw [Finset.sum_eq_single (⟨ρ - 1, by omega⟩ : Fin ρ) (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]]
  simp only [ite_true, mul_one, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem cA_mem_idAt'' {v : Pl D} {y : AE D} (h : y ∈ idAt D (· = v)) : cA D y ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

theorem smul_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (s t : AE D) :
    s • colMul d.jY i t = colMul d.jY i (s * t) := by
  funext k
  simp only [colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem colMul_jY_mem_latA_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (L : Lat S) (𝔟 : FI D) (v : Pl D) (i : Fin ρ), 𝔟 ≠ 0 →
      (∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latV S L (· = v) ↔ cA D t ∈ idV 𝔟⁻¹ v) →
      ∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latA S L (· = v) ↔ cA D t ∈ idV ((D.host.AAbar : FI D) * 𝔟⁻¹) v := by
  intro D ψ hψ S S₀ ρ d L 𝔟 v i h𝔟 hL t ht
  obtain ⟨-, h2, -, h4, -, -, h7⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hAAb : (D.host.AAbar : FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hct := cA_mem_idAt'' ht
  have hconj : ∀ s, s ∈ idV (D.host.AA : FI D)⁻¹ v ↔ cA D s ∈ idV (D.host.AAbar : FI D)⁻¹ v := by
    intro s
    have := h4 (-1) s
    rwa [_root_.zpow_neg_one, _root_.zpow_neg_one] at this
  rw [h7, ← inv_inv (D.host.AAbar : FI D), mul_comm, ← h2 _ _ (inv_ne_zero hAAb) (inv_ne_zero h𝔟) _ hct]
  constructor
  · rintro ⟨-, h⟩ a ha
    have hs : cA D a ∈ idV (D.host.AA : FI D)⁻¹ v := by rw [hconj, cA_cA]; exact ha
    have h1 := h _ hs
    rw [smul_colMul, hL _ (Ideal.mul_mem_left _ _ ht), map_mul, cA_cA] at h1
    rw [mul_comm]; exact h1
  · intro h
    refine ⟨fun k => Ideal.mul_mem_right _ _ ht, fun s hs => ?_⟩
    rw [smul_colMul, hL _ (Ideal.mul_mem_left _ _ ht), map_mul, mul_comm]
    exact h _ ((hconj s).1 hs)

end GlobalTheory.SeeSaw.LastPrim
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QSuppTwo

theorem prod_mul_inv_mem {G : Type} [Group G] (H : Subgroup G) : ∀ (n : ℕ) (f : Fin n → G) (i : Fin n),
    (∀ i', i' ≠ i → f i' ∈ H) → (∀ y ∈ H, f i * y = y * f i) → (List.ofFn f).prod * (f i)⁻¹ ∈ H := by
  intro n
  induction n with
  | zero => intro f i; exact i.elim0
  | succ n ih =>
    intro f i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro hf0 hc0
      have hP : (List.ofFn fun k : Fin n => f k.succ).prod ∈ H := by
        apply Subgroup.list_prod_mem
        intro x hx
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
        exact hf0 _ (Fin.succ_ne_zero k)
      rw [List.ofFn_succ, List.prod_cons, hc0 _ hP, mul_assoc, mul_inv_cancel, mul_one]
      exact hP
    · intro hfk hck
      rw [List.ofFn_succ, List.prod_cons, mul_assoc]
      exact mul_mem (hfk 0 (Fin.succ_ne_zero k).symm)
        (ih (fun k => f k.succ) k (fun k' hk' => hfk _ (fun e => hk' (Fin.succ_injective _ e))) hck)

theorem mem_support_conv {G : Type} [Monoid G] : ∀ (n : ℕ) (f : Fin n → (G →₀ ℂ)) (g : G),
    g ∈ (GlobalTheory.QPl.conv (List.ofFn f)).support → ∃ x : Fin n → G, (∀ i, x i ∈ (f i).support) ∧ g = (List.ofFn x).prod := by
  classical
  intro n
  induction n with
  | zero =>
    intro f g hg
    simp only [List.ofFn_zero, GlobalTheory.QPl.conv, List.foldr_nil] at hg
    have := Finsupp.support_single_subset hg
    rw [Finset.mem_singleton] at this
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    intro f g hg
    rw [List.ofFn_succ] at hg
    simp only [GlobalTheory.QPl.conv, List.foldr_cons] at hg
    have h1 := Finsupp.support_sum hg
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g₀, hg₀, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨g', hg', h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    obtain ⟨x, hx, hxe⟩ := ih (fun k => f k.succ) g' hg'
    refine ⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩
    rw [List.ofFn_succ, List.prod_cons, h5, hxe]
    simp

end GlobalTheory.QSuppTwo

open GlobalTheory.QSuppTwo in
theorem GlobalTheory.QSuppTwo.main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ A : ∀ i, Finset (GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∀ α, ∀ g ∈ (w.ε j α).support, ∃ a : ∀ i, GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k, ∀ i, a i ∈ A i ∧ g * ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) (a i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v) := by
  classical
  intro D c v t w F hF j σ h
  have hd : ∀ i, j + (2 * σ + 2) = (F.Q i).s := fun i => by have := (F.Q i).hs; omega
  choose e he using fun i (α' : (F.Q i).Ch j) => (F.Q i).εL_at j (σ + 1) h (2 * σ + 2) (hd i) α'
  refine ⟨fun i => Finset.univ.biUnion fun α' => (e i α').support, ?_⟩
  intro α g hg
  rw [hF.ε j (σ + 1) h α] at hg
  have hg' := Finsupp.support_smul hg
  obtain ⟨x, hx, rfl⟩ := mem_support_conv _ _ g hg'
  have hpt : ∀ i, ∃ a ∈ (e i (F.eqv j α i)).support,
      (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a = x i := by
    intro i
    have := hx i
    rw [(he i (F.eqv j α i)).2] at this
    have := Finsupp.mapDomain_support this
    rw [Finset.mem_image] at this
    exact this
  choose a ha hax using hpt
  refine ⟨a, fun i => ⟨Finset.mem_biUnion.2 ⟨F.eqv j α i, Finset.mem_univ _, ha i⟩, ?_⟩⟩
  have I := fun i => GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V j) _ ((F.Q i).FY j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega))
    ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega)) ((F.Q i).gl_loc j _ _)
  rw [hax i]
  apply prod_mul_inv_mem _ _ x i
  · intro i' hi'
    rw [← hax i']
    have hr : (F.Q i').gl j (2 * σ + 2 + 1) (by have := (F.Q i').hs; omega) (a i') ∈ GlobalTheory.FinPl.grpAt (c.V j) (· = (F.Q i').q.v) := by
      rw [← (I i').2.1]; exact ⟨_, rfl⟩
    exact (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V j) ∅).2.2.2.2.2.2.1 _ _ (fun p hp hn => hi' (hF.inj (hp.symm.trans hn))) hr
  · intro y hy
    rw [← hax i]
    exact (I i).2.2.2.1 (a i) y hy
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.doubleUnfoldingStep_at_glued_finite_place : ∀ D : D7, GlobalTheory.FinPl.VertexGlued D := by
  first | exact @GlobalTheory.FinPl.Vertex.vertexGlued | exact GlobalTheory.FinPl.Vertex.vertexGlued | (intros; apply GlobalTheory.FinPl.Vertex.vertexGlued <;> assumption)
end
