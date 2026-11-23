module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfEqOfEqOnRational
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleDescentOfParity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle428
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftLastStepsCouplingCosetOrbitInvari
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle472
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle524
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle526
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle331
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle492
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle521
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.schwartzBruhat_half_eq_of_eq_on_rational : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf E₂ (stdHom S T) Φ₁ → IsSBHalf E₂ (stdHom S T) Φ₂ → (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Φ₁ (γ.map fun a => E₂ * incA D a) = Φ₂ (γ.map fun a => E₂ * incA D a)) → Φ₁ = Φ₂ := by
  first | exact @GlobalTheory.RatHalfDense.eq_of_rat | exact GlobalTheory.RatHalfDense.eq_of_rat | (intros; apply GlobalTheory.RatHalfDense.eq_of_rat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.GValAll

theorem gValue_common : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → GValue (t := t) (v.withCG a) := by
  intro D c v n G hc hv hG
  classical
  refine ⟨fun j => if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose
    else if h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
      (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram then
      (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose else 1, ?_, ?_⟩
  · intro j
    dsimp only
    by_cases h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m
    · rw [dite_eq_left h1]; exact (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.1
    · rw [dite_eq_right h1]
      by_cases h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
          (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram
      · rw [dite_eq_left h2]; exact (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.1
      · rw [dite_eq_right h2]; exact one_ne_zero
  · intro t _ hw
    refine ⟨fun j σ h Ψ₁ Ψ₂ h₁ h₂ => ?_, fun j h Ψ₁ Ψ₂ h₁ h₂ => ?_⟩
    · have h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m := ⟨σ, h⟩
      have hσ : h1.choose = σ := by have := h1.choose_spec; omega
      show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _
      rw [dite_eq_left h1]
      have key := (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.2
      revert key
      generalize (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose = C
      intro key
      subst hσ
      exact key _ _ Ψ₁ Ψ₂ h₁ h₂
    · have h1 : ¬ ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m := by rintro ⟨σ, hσ⟩; omega
      obtain ⟨hr, hτ⟩ := hw.tau j h
      have h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
          (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram := ⟨h, hr, hτ⟩
      show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _
      rw [dite_eq_right h1, dite_eq_left h2]
      exact (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.2 _ Ψ₁ Ψ₂ h₁ h₂

end GlobalTheory.SeeSaw.GValAll
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinOneAt



theorem core {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} (hψ : IsStdChar D c.ψ (-1)) (hv : v.Is) (ht : t.Is)
    {χ : ℕ → (AE D)ˣ →* Circle} (Q' : QAt v χ) (χz : (AE D)ˣ →* Circle) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (V₁ : (t.sBF j (σ + 1) h).χV = χ j * χz) (W₁ : (t.sBF j (σ + 1) h).χW = χ j)
    (V₂ : (t.sFB j σ h).χV = χ (j + 1)) (W₂ : (t.sFB j σ h).χW = χ (j + 1) * χz)
    (ka : IsWeilDatumO c.ψ _ _ (χ j) (χ j) (t.kom j)) (kb : IsWeilDatumO c.ψ _ _ (χ (j + 1)) (χ (j + 1)) (t.kom (j + 1)))
    (a : GL (Q'.X j ⊕ Fin (2 * σ + 2 + 1)) Q'.k) :
    ∃ T : Finset (GL (Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) Q'.k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Q'.q.v) f₁ →
      ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = Q'.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = Q'.q.v), ∀ x,
        flatBF (t.sBF j (σ + 1) h) (t.om j (g * Q'.gl j (2 * σ + 2 + 1) (by have := Q'.hs; omega) a,
          h₁ * Q'.gl (j + 1) (2 * σ + 2) (by have := Q'.hs; omega) x) (comb c.ψ _ _ (Q'.eL j) f₁)) ≠ 0 →
        ∃ τ ∈ T, ∃ r, Q'.gl (j + 1) (2 * σ + 2) (by have := Q'.hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧
          ∃ κ ∈ (Q'.T.lev (j + 1) (2 * σ + 2) (by have := Q'.hs; omega)).J, x = r * τ * κ := by
  classical
  haveI := Q'.unitVol.1
  have e0 : j + (2 * σ + 2 + 1) = Q'.s + 1 := by have := Q'.hs; omega
  have e1 : j + 1 + (2 * σ + 2) = Q'.s + 1 := by have := Q'.hs; omega
  have e2 : j + 1 + 1 + (2 * σ + 1) = Q'.s + 1 := by have := Q'.hs; omega
  have e01 : j + (2 * σ + 2) = Q'.s := by have := Q'.hs; omega
  have e12 : j + 1 + (2 * σ + 1) = Q'.s := by have := Q'.hs; omega
  let S : Dbl2 c.ψ σ :=
    { B := c.B j (σ + 1) h, J := c.J j (σ + 1) h, B' := c.B (j + 1 + 1) σ (idx_step h),
      s₁ := t.sBF j (σ + 1) h, s₂ := t.sFB j σ h, l := c.lnk j σ h, vL := c.vL j σ h,
      χ₁ := χ j, χ₂ := χ (j + 1), χz := χz, oma := t.kom j, omb := t.kom (j + 1),
      V₁ := V₁, W₁ := W₁, V₂ := V₂, W₂ := W₂, weila := ka, weilb := kb }
  let Fd : Dbl (ofSplit Q'.q) S.B S.J S.B' (Q'.X j) (Q'.X (j + 1)) (Q'.X (j + 1 + 1)) (2 * σ) :=
    { s := Q'.sc j, s_ne := Q'.sc_ne j, F₀ := Q'.FX j (by omega), F₁ := Q'.FX (j + 1) (by omega),
      F₂ := Q'.FX (j + 1 + 1) (by omega), G₀ := Q'.FY j _ e0, G₁ := Q'.FY (j + 1) _ e1, G₂ := Q'.FY (j + 1 + 1) _ e2,
      bes := Q'.bes j (σ + 1) h _ e0, jac := Q'.jac j (σ + 1) h _ e1,
      bes' := by rw [← Q'.sc_step j]; exact Q'.bes (j + 1 + 1) σ (idx_step h) _ e2 }
  have reg1 := (Q'.reg.2.2 (j + 1) _ e1)
  have reg2 := (Q'.reg.2.2 (j + 1 + 1) _ e2)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, A₁, A₂, cov₁, cov₂, d₁, d₂, ent₁, ent₂, e₀, e₂, one₀, one₂, m₁, m₂, haar₁, haar₂,
      vol₁, vol₂, -, -, -⟩ :=
    GlobalTheory.QPl.Inhab.exists_qstep hψ S Q'.ν Q'.unitVol Q'.q Q'.ψk Q'.char Q'.cond (Q'.X j) (Q'.X (j + 1)) (Q'.X (j + 1 + 1))
      (2 * σ) Fd (Q'.T.mu (j + 1)) (Q'.T.mu (j + 1 + 1)) (Q'.mu j (by omega)).1 (Q'.mu (j + 1) (by omega)).1
      (Q'.mu j (by omega)).2 (Q'.mu (j + 1) (by omega)).2 (Q'.T.lev j _ e0) (Q'.T.lev (j + 1) _ e1) (Q'.T.lev (j + 1 + 1) _ e2)
      (Q'.reg.2.2 j _ e0).1 ⟨reg1.1, reg1.2.1⟩ ⟨reg2.1, reg2.2.1⟩ (Q'.le _ _ e1) (Q'.le _ _ e2)
      ⟨Q'.T.Phi j _ e01, Q'.reg.1 _ _ e01⟩ ⟨Q'.T.Phi (j + 1) _ e12, Q'.reg.1 _ _ e12⟩ (Q'.laws.1 j _ e01) (Q'.laws.1 (j + 1) _ e12)
      a 1 1
  let Q : QStep S :=
    { k := Q'.k, ν := Q'.ν, unitVol := Q'.unitVol, q := Q'.q, ψk := Q'.ψk, char := Q'.char, cond := Q'.cond,
      n₀ := Q'.X j, n₁ := Q'.X (j + 1), n₂ := Q'.X (j + 1 + 1), c := 2 * σ, F := Fd,
      gl₀ := Q'.gl j _ e0, gl₁ := Q'.gl (j + 1) _ e1, gl₂ := Q'.gl (j + 1 + 1) _ e2,
      loc₀ := Q'.gl_loc j _ e0, loc₁ := Q'.gl_loc (j + 1) _ e1, loc₂ := Q'.gl_loc (j + 1 + 1) _ e2,
      μ₁ := Q'.T.mu (j + 1), μ₂ := Q'.T.mu (j + 1 + 1), comp₁ := (Q'.mu j (by omega)).1, comp₂ := (Q'.mu (j + 1) (by omega)).1,
      open₁ := (Q'.mu j (by omega)).2, open₂ := (Q'.mu (j + 1) (by omega)).2,
      L₀ := Q'.T.lev j _ e0, L₁ := Q'.T.lev (j + 1) _ e1, L₂ := Q'.T.lev (j + 1 + 1) _ e2,
      co₁ := ⟨reg1.1, reg1.2.1⟩, co₂ := ⟨reg2.1, reg2.2.1⟩, le₁ := Q'.le _ _ e1, le₂ := Q'.le _ _ e2,
      Φ₁ := ⟨Q'.T.Phi j _ e01, Q'.reg.1 _ _ e01⟩, Φ₂ := ⟨Q'.T.Phi (j + 1) _ e12, Q'.reg.1 _ _ e12⟩,
      ty₁ := Q'.laws.1 j _ e01, ty₂ := Q'.laws.1 (j + 1) _ e12,
      D₁ := Q'.eL j, D₂ := Q'.eL (j + 1), dat₁ := Q'.eL_at j _ e01, dat₂ := Q'.eL_at (j + 1) _ e12,
      α := a, A₁ := A₁, A₂ := A₂, cov₁ := cov₁, cov₂ := cov₂, d₁ := d₁, d₂ := d₂, ent₁ := ent₁, ent₂ := ent₂,
      e₀ := e₀, e₂ := e₂, one₀ := one₀, one₂ := one₂, m₁ := m₁, m₂ := m₂, haar₁ := haar₁, haar₂ := haar₂,
      vol₁ := vol₁, vol₂ := vol₂ }
  obtain ⟨T₁, hT₁, -⟩ := GlobalTheory.T.splitPlaceDoubleStepFinitelyManyCellsUniform_proof D c.ψ hψ σ S Q a
  refine ⟨T₁, fun f₁ hf₁ g hg h₁ hh₁ x hx => ?_⟩
  obtain ⟨Tm, hTm, hTmO⟩ := (GlobalTheory.LocMod.indicator_vac D Q'.k Q'.q Q'.unit (Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) (Q'.X j ⊕ Fin (2 * σ + 2 + 1))
    (c.V j) (c.V (j + 1)) (Q'.FY j _ e0) (Q'.FY (j + 1) _ e1) c.ψ Q'.ψk hψ Q'.char Q'.cond (v.N j) (v.N (j + 1))
    (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (Q'.latY j _ e0) (Q'.latY (j + 1) _ e1)).2 f₁ hf₁
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Q'.k) (Y := Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) (Y' := Q'.X j ⊕ Fin (2 * σ + 2 + 1))
  obtain ⟨f₀, f₂, -, -, -, -, hv2⟩ := GlobalTheory.QPl.Inhab.exists_vac hψ (ι := Unit) (fun _ => Q) (fun _ _ _ => rfl)
  have hvac : Q.Vac f₁ f₂ := ⟨⟨Tm, O, hTm, hO, hTmO O hO⟩, (hv2 ()).2⟩
  have hom := (ht.sBF j (σ + 1) h).1
  obtain ⟨τ, hτ, r, hr, κ, hκ, hx'⟩ := hT₁ f₁ f₂ hvac g hg h₁ hh₁ x (by
    change flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om _ _) ≠ 0
    rw [hom]; exact hx)
  exact ⟨τ, hτ, r, hr, κ, hκ, hx'⟩

theorem finOne_pin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ ((F.Q i).eL j) f₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  intro D c v t w F hc ht hv _ hP j σ h i a
  obtain ⟨χz, V₁, W₁, V₂, W₂⟩ := hP.mid j σ h
  exact core hc.std hv ht (F.Q i) χz j σ h V₁ W₁ V₂ W₂ (hP.kom j (by omega)) (hP.kom (j + 1) (by omega)) a

end GlobalTheory.QFinOneAt
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

theorem _root_.GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ α (S : Finset ((Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂)), Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S → ∀ (d₁ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) (d₁ yb) (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb)) → (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM (d₂ yb) (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb)) → c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂) = ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
  first | exact @GlobalTheory.QPl.LastPt.kernel_eq_sum | exact GlobalTheory.QPl.LastPt.kernel_eq_sum | (intros; apply GlobalTheory.QPl.LastPt.kernel_eq_sum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubleThetaLift_lastSteps_couplingCoset_orbit_invariant : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ α u y yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb → ∀ d₁ d₂, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) d₁ (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb) → (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM d₂ (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁]) (aconv [c₂, d₂]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) = c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  first | exact @GlobalTheory.QPl.LastOrb.orb | exact GlobalTheory.QPl.LastOrb.orb | (intros; apply GlobalTheory.QPl.LastOrb.orb <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.IP

variable {D : D7}

theorem integrable_star_comp {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => conj (f x)) μ := by
  simpa using (Complex.conjCLE.toContinuousLinearMap).integrable_comp hf

theorem memL2_conj_comp (V : HSp D) (μ : Measure (GA D V)) {f : GA D V → ℂ}
    (hf : MemL2Quotient (GQ V) μ f) : MemL2Quotient (GQ V) μ (fun x => conj (f x)) := by
  refine ⟨fun γ hγ g => by simp only [hf.1 γ hγ g], ?_⟩
  have := (Complex.conjCLE.toContinuousLinearMap).comp_memLp' hf.2
  convert this using 1
  funext q
  simp [GlobalTheory.AutomorphicL2Unitary.descend]

theorem petersson_star_comp (V : HSp D) (μ : Measure (GA D V)) (f₁ f₂ : GA D V → ℂ) :
    petersson V μ (fun x => conj (f₁ x)) (fun x => conj (f₂ x)) = conj (petersson V μ f₁ f₂) := by
  simp only [petersson, pet]
  rw [← integral_conj]
  congr 1; funext q
  simp [GlobalTheory.AutomorphicL2Unitary.descend]

theorem innerProduct_convergent_conj : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ) (m : Measure (GA D A)) (ν : Measure (GA D B)) (f₁ f₂ : GA D A → ℂ), HidaSetting θ A B sA sB t cA → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c → m.IsHaarMeasure → ν.IsHaarMeasure → f₁ ∈ A0 θ A cA → f₂ ∈ A0 θ A cA → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₁ f₁ ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₂ f₂ ∧ Integrable (fun g => c g * conj (petersson A m (rTr A g f₁) f₂)) m ∧ petersson B ν (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₁ f₁) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₂ f₂) = volQ B ν * ∫ g, c g * conj (petersson A m (rTr A g f₁) f₂) ∂m := by
  intro hRD hWS hSE D ψ θ A B χA χB sA sB t cA K₁ K₂ c m ν f₁ f₂ hS hw ht hK hm hν hf₁ hf₂
  obtain ⟨om, Φ₁, Φ₂, hW, hF₁, hF₂, -, -, hK₁, hK₂, μ, 𝓕, hcov, hc⟩ := hK
  obtain ⟨a, ha, ha'⟩ := GlobalTheory.T.exists_adelicMajorantFrame_for_cartanInvolutions D θ A sA hS.2.2.2.1 hS.2.2.2.2.2.2.1
  have hP : Pair ψ θ A B χA χB sA sB t cA a om μ 𝓕 := ⟨hS, ha, ha', hW, hcov⟩
  obtain ⟨hU₁, hU₂, hI, hE⟩ := GlobalTheory.T.unitary_theta_innerProduct_formula_convergent_range hRD hWS hSE D ψ θ A B χA χB sA sB t cA a om μ 𝓕 hP hw ht m ν hm hν
    Φ₁ Φ₂ hF₁ hF₂ f₁ hf₁ f₂ hf₂
  have hcg : ∀ g, c g = conj (wcoef om μ 𝓕 Φ₁ Φ₂ g) := by
    intro g
    have h1 : wcoef om μ 𝓕 Φ₁ Φ₂ g = conj (c g) := by
      have h2 := hc g
      simp only at h2
      rw [h2]; rfl
    rw [h1, Complex.conj_conj]
  have hlift : ∀ (K : GA D A → GA D B → ℂ) (Φ : WO A B → ℂ) (u : GA D A → ℂ),
      (∀ g h, K g h = conj (thetaKO om g h Φ)) →
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K u = fun h => conj (up om m Φ u h) := by
    intro K Φ u hK; funext h
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift, up, petersson, pet, hK]
    rw [← integral_conj]
    congr 1; funext q
    simp [GlobalTheory.AutomorphicL2Unitary.descend]
  have hconv : ∀ (K : GA D A → GA D B → ℂ) (Φ : WO A B → ℂ) (u : GA D A → ℂ),
      (∀ g h, K g h = conj (thetaKO om g h Φ)) → UpConv om m ν Φ u → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K u := by
    intro K Φ u hK hU
    refine ⟨fun h => ?_, ?_⟩
    · have := integrable_star_comp (hU.1 h)
      convert this using 2 with q
      simp [GlobalTheory.AutomorphicL2Unitary.descend, hK]
    · rw [hlift K Φ u hK]
      exact memL2_conj_comp B ν hU.2
  refine ⟨hconv K₁ Φ₁ f₁ hK₁ hU₁, hconv K₂ Φ₂ f₂ hK₂ hU₂, ?_, ?_⟩
  · have := integrable_star_comp hI
    convert this using 2 with g
    simp [hcg, rcoef]
  · rw [hlift K₁ Φ₁ f₁ hK₁, hlift K₂ Φ₂ f₂ hK₂, petersson_star_comp, hE, map_mul, ← integral_conj]
    simp [hcg, rcoef]

end GlobalTheory.Core.Rk.IP

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.unfold_over_flagUnipotent_thetaLift : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → IntegrableOn (fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ)) 𝓑 vW.μ ∧ ∫ n in vN.𝓝, Th n.1 * liftS om vW.μ vW.𝓕 G Φ n.1 ∂vN.ν = ∫ h in 𝓑, G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) ∂vW.μ := by
  first | exact @GlobalTheory.Unf.unfold_over_N_lift | exact GlobalTheory.Unf.unfold_over_N_lift | (intros; apply GlobalTheory.Unf.unfold_over_N_lift <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.TLastAll

theorem combAt_fin {D : D7} {P : Pl D → Prop} {S T : HSp D} {c : WO S T →₀ ℂ} (h : CombAt P c) : IsFinComb c := by
  intro u hu
  ext i j
  have := (Ideal.mem_inf.1 (h u hu i j)).1
  simpa using this



theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, ∀ f, IsContAut c.T f → ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ = o.mono r e (t.sBF j 0 h).χW * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)))) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  intro D c v k _ _ _ _ ι o hc hv hS j h
  have hPl : Places o.p o.I (· ∈ v.tP) :=
    ⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, hS.pre.tP, fun i => (hS.pre.char i).2⟩
  have hstd := hc.std
  have hjm : j + 1 < D.R.m := by omega
  have hx0 : IsSelfDualC _ (c.x j).L := (hc.x j (by omega)).sd
  have hx1 : IsSelfDualC _ (c.x (j + 1)).L := (hc.x (j + 1) (by omega)).sd
  have hx2 : IsSelfDualC _ (c.x (j + 1 + 1)).L := (hc.x (j + 1 + 1) (by omega)).sd
  have hpl : Nonempty (Pl D) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (α := NumberField.RingOfIntegers D.host.F)
    exact ⟨⟨M, hM.isPrime, (Ideal.bot_lt_of_maximal M (NumberField.RingOfIntegers.not_isField D.host.F)).ne'⟩⟩
  have hM : IsSelfDualC _ (o.M j 0 h) := ((hS.good (Classical.arbitrary _)).bf j 0 h).sdV₀
  obtain ⟨lam, hlam, hlamv⟩ := hS.pre.lam j h
  obtain ⟨ε', hε'⟩ := GlobalTheory.T.lastSeeSawDatumAtSplitPlaces_proof D k ι o.p o.I (· ∈ v.tP) hPl o.q c.ψ hstd o.χ o.hχ (fun i => (hS.pre.char i).1)
    (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) (Fin c.T.rank) (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1))
    (c.X (j + 1 + 1)) c.T c.Lz (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (c.bes j 0 h).ζ o.ζ₀ (c.bes j 0 h).line hS.pre.line
    (v.τ j h) lam hlam (fun i => (hlamv i).1) (hS.pre.tau j h)
  obtain ⟨Λ, hΛ, u, hγ, hrep⟩ := GlobalTheory.SeeSaw.lastKernel_reps D c v k ι o hc hv hS j h
  haveI : ∀ i, (Λ i).IsFullLattice k := hΛ
  let ε : ι → 𝓀[k]ˣ := fun i => (ε' i)⁻¹ * u i
  let Q : ι → Pair k (Fin (c.X (j + 1)).rank) := fun i => ε i • o.Q (j + 1) i
  obtain ⟨r, e, hr, hSm⟩ := GlobalTheory.T.smallPairPairingAllGluedPlaces_proof D k ι o.p o.I (· ∈ v.tP) hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) o.q o.χ o.hχ
  have hAC := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D
  let Ψ' : ι → Matrix (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1) k → ℂ := fun i =>
    tensCol (phiOne (o.Q j i) (o.Q (j + 1) i)) (charInd (resChar (o.χ i) (o.hχ i) o.q) (Q i))
  have hAC1 := hAC k ι o.p o.I (· ∈ v.tP) hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1) c.ψ hstd
    (c.bes j 0 h).V₀ (c.X (j + 1)) (o.β₀ j 0 h) (o.β (j + 1)) (o.M j 0 h) (c.x (j + 1)).L hM hx1 Ψ'
  obtain ⟨e0, he0⟩ := hAC1.1 fun i => Comm.tensCol_mem (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _) (SBFacts.charInd_mem _ _)
  have hrep' : Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L
      (fun i => phiOne (ε' i • Q i) (lastPair o.q (Λ i))) o.I (· ∈ v.tP) (v.dT (j + 1)) := by
    have hf : (fun i => phiOne (ε' i • Q i) (lastPair o.q (Λ i))) =
        (fun i => phiOne (u i • o.Q (j + 1) i) (lastPair o.q (Λ i))) := by
      funext i
      simp only [Q, ε, smul_smul, mul_inv_cancel_left]
    rw [hf]
    exact hrep
  obtain ⟨e₁, e₂, he₁, he₂, hE⟩ := hε' (o.β j) (o.β₀ j 0 h) (o.β (j + 1)) o.γ (o.γ₀ (j + 1 + 1) h)
    (fun i => ⟨(hS.glued j 0 h i).sum, (hS.pre.topT (j + 1 + 1) h i).1⟩) Q Λ
    (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) (c.x j).L (c.x (j + 1)).L v.NT (c.x (j + 1 + 1)).L (o.M j 0 h)
    hx0 hx1 hv.sdT hx2 hM (fun i => ⟨hS.pre.latT (j + 1) (by omega) i, hγ i⟩) (v.dT j) (v.dT (j + 1))
    ⟨(hv.atT j).1, hS.rep j (by omega)⟩ hrep'
  have hLO := GlobalTheory.T.lastSeeSaw_combinations_operatorDatum D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
    (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 hS.pre.line.1 (hS.pre.tau j h)
  obtain ⟨op0, hop0, hop0e⟩ := (hLO (· ∈ v.tP)).1 e0 he0.1
  obtain ⟨op, hop, hope⟩ := ((GlobalTheory.T.biVacuumOperator_zero_or_left_invertible D) k ι o.p o.I _ hPl c.ψ hstd _ _ _ op0 hop0).2 e₁ e₂ he₁ he₂
  refine ⟨ε, op, r, e, hr, hop, ?_⟩
  intro t ht hW hU hK Ψ₁ Ψ₂ hΨ₁ hΨ₂
  obtain ⟨χA, χz, χS', χT, omz, omT', omz'', hχV, hwA, hwz, hwX, hwT, hwTi, hwz''⟩ := hW.last j h
  have hunrT := GlobalTheory.T.seesawLastStage_chars_unramified_at_levelPrime D c v k ι o hS j h t hU hK χz χS' χT hwX hwTi
  have hFV := GlobalTheory.T.flatMapPreservesVacuum_proof D c.ψ (· ∈ v.tP)
  have hΞ : Vac c.ψ (c.bes j 0 h).V₀ (c.X (j + 1)) (o.M j 0 h) (c.x (j + 1)).L (· ∈ v.tP) (flatBF (t.sBF j 0 h) Ψ₁) :=
    hFV.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) (v.N j) (o.M j 0 h) (v.N (j + 1)) (c.x (j + 1)).L
      (fun x _ => (hS.good x).bf j 0 h) Ψ₁ hΨ₁
  have hΦ : Vac c.ψ (c.X (j + 1)) c.T (c.x (j + 1)).L v.NT (· ∈ v.tP) (fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w)) :=
    hFV.2.2 (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d (v.N (j + 1)) (c.x (j + 1)).L v.NT (hv.sd (j + 1) hjm) hx1
      hv.sdT (fun x _ => ((hS.good x).bf j 0 h).monoW) Ψ₂ hΨ₂
  set Ξ := flatBF (t.sBF j 0 h) Ψ₁ with hΞdef
  set Φ₂ : WO (c.X (j + 1)) c.T → ℂ := fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w) with hΦdef
  have hΞ' := he0.2 Ξ hΞ
  obtain ⟨hBV, hEq⟩ := hE Ξ (comb c.ψ _ _ e0 Ξ) Φ₂ hΞ hΞ' hΦ
  have hlst : c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂ = lastBi (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) Ξ Φ₂ := rfl
  have hopX : op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) = biComb c.ψ _ _ _ e₁ e₂
      (lastBi (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (comb c.ψ _ _ e0 Ξ) Φ₂) := by
    rw [hope, hlst, ← hop0e]
  refine ⟨hopX ▸ hBV, ?_⟩
  intro d d' hd hd' φ hφ f hf
  rw [hopX, ← hEq]
  obtain ⟨N, a, b, hab, hdec⟩ := (hLO (· ∉ v.tP)).2 d d' hd hd'
  rw [hlst, hdec, hdec]
  have hAC2 := hAC k ι o.p o.I (· ∈ v.tP) hPl (Fin c.T.rank) (Fin (c.X (j + 1)).rank) c.ψ hstd (c.X (j + 1)) c.T
    (o.β (j + 1)) o.γ (c.x (j + 1)).L v.NT hx1 hv.sdT (fun _ _ => 0)
  have hw₁ : IsWeilDatumO c.ψ _ _ (χA * χz) (t.sBF j 0 h).χW (t.sBF j 0 h).om₀ := by
    rw [← hχV]; exact (t.sBF j 0 h).weil₀
  have hSS := GlobalTheory.T.lastSeeSaw_doubleLift_additive D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
    (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 hS.pre.line.1 (hS.pre.tau j h)
    (hc.x j (by omega)).cpt (hc.x (j + 1) (by omega)).cpt hc.cpt χA χz (t.sBF j 0 h).χW χS' χT (t.sBF j 0 h).om₀
    (t.kom j) omz (t.kom (j + 1)) omT' omz'' hw₁ hwA hwz hwX hwT hwz'' (c.x j).vol (c.x (j + 1)).vol c.volT N
  have hRam : PairDat.Ram (⟨o.β j, o.β₀ j 0 h, o.Q j⟩ : PairDat o.p (c.X j) (c.bes j 0 h).V₀ (Fin (c.X j).rank)) φ := hφ
  have hRam' := (GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D k ι o.p o.q o.χ o.hχ ε (Fin (c.X j).rank) (c.X j) (c.bes j 0 h).V₀
    ⟨o.β j, o.β₀ j 0 h, o.Q j⟩ hS.pre.inj o.I).1.mapsTo hRam
  have L1 := hSS (fun i => comb c.ψ _ _ (a i) Ξ) (fun i => comb c.ψ _ _ (b i) Φ₂)
    (fun i => ⟨((hAC1.2.2 (a i) (hab i).1 Ξ hΞ).1).1, ((hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1).1⟩) φ f hφ.1 hf
  have L2 := hSS (fun i => comb c.ψ _ _ (a i) (comb c.ψ _ _ e0 Ξ)) (fun i => comb c.ψ _ _ (b i) Φ₂)
    (fun i => ⟨GlobalTheory.AvgMid.theta_comb hstd (combAt_fin (hab i).1) (GlobalTheory.AvgMid.theta_comb hstd (combAt_fin he0.1) hΞ.1),
      ((hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1).1⟩) (o.S (fun _ => ε) j φ) f hRam'.1 hf
  beta_reduce at L1 L2
  unfold Comm.bl
  rw [L1, L2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hSm c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) c.T (c.bes j 0 h).o (c.bes j 0 h).ζ
    (c.bes j 0 h).line (hc.x j (by omega)).cpt (hc.x (j + 1) (by omega)).cpt hc.cpt (t.sBF j 0 h).χV (t.sBF j 0 h).χW
    χS' χT (t.sBF j 0 h).om₀ omT' (t.sBF j 0 h).weil₀ hwT
    (fun x hx => ⟨(hU.bf j 0 h x hx).1, (hU.bf j 0 h x hx).2, (hunrT x hx).1, (hunrT x hx).2⟩)
    (c.x j).vol (c.x (j + 1)).vol c.volT ⟨o.β j, o.β₀ j 0 h, o.Q j⟩ ⟨o.β (j + 1), o.Q (j + 1)⟩ ε (o.M j 0 h)
    (c.x (j + 1)).L v.NT hM hx1 hv.sdT
    (fun i => ⟨(hS.glued j 0 h i).sum, (hS.glued j 0 h i).lat, hS.pre.latT (j + 1) (by omega) i⟩)
    (comb c.ψ _ _ (a i) Ξ) (comb c.ψ _ _ (a i) (comb c.ψ _ _ e0 Ξ)) (comb c.ψ _ _ (b i) Φ₂)
    (hAC1.2.2 (a i) (hab i).1 Ξ hΞ).1 (hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1
    ((hAC1.2.2 (a i) (hab i).1 Ξ hΞ).2 _ hΞ') φ hRam f hf

end GlobalTheory.FinPl.TLastAll

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
open GlobalTheory.QVal GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.iteratedIntegralValueAtRPlaces_zero : ∀ D : D7, ValQr D 0 := by
  first | exact @GlobalTheory.QVal.valQr_zero | exact GlobalTheory.QVal.valQr_zero | (intros; apply GlobalTheory.QVal.valQr_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.ampleTheta_wideRange_large_constants : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → Formalism.L2.SG.RowsConc.TFrameAt D → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  first | exact @GlobalTheory.Core.Deg.ptWide_at_record_gap | exact GlobalTheory.Core.Deg.ptWide_at_record_gap | (intros; apply GlobalTheory.Core.Deg.ptWide_at_record_gap <;> assumption)
end

end

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.convergentInnerProduct_conjugateOrientation_weil : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ) (m : Measure (GA D A)) (ν : Measure (GA D B)) (f₁ f₂ : GA D A → ℂ), HidaSetting θ A B sA sB t cA → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c → m.IsHaarMeasure → ν.IsHaarMeasure → f₁ ∈ A0 θ A cA → f₂ ∈ A0 θ A cA → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₁ f₁ ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₂ f₂ ∧ Integrable (fun g => c g * conj (petersson A m (rTr A g f₁) f₂)) m ∧ petersson B ν (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₁ f₁) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₂ f₂) = volQ B ν * ∫ g, c g * conj (petersson A m (rTr A g f₁) f₂) ∂m := by
  first | exact @GlobalTheory.Core.Rk.IP.innerProduct_convergent_conj | exact GlobalTheory.Core.Rk.IP.innerProduct_convergent_conj | (intros; apply GlobalTheory.Core.Rk.IP.innerProduct_convergent_conj <;> assumption)

end
end
