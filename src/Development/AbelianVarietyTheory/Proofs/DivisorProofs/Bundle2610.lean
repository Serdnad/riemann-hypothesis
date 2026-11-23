module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle659
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle259
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle550
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle122
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle646
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

private theorem isVacO_move {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hW : IsWeilDatumO ψ S T χS χT om)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS MS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT MT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hLS : IsSelfDualC S LS) (hMS : IsSelfDualC S MS) (hLT : IsSelfDualC T LT) (hMT : IsSelfDualC T MT)
    (g : GA D S) (hg : g ∈ GfC S) (h : GA D T) (hh : h ∈ GfC T)
    (mg : GlobalTheory.FinPl.Moves S g LS MS (fun _ => True)) (mh : GlobalTheory.FinPl.Moves T h LT MT (fun _ => True))
    (f : WO S T → ℂ) (hf : IsVacO ψ θ S T sS sT LS LT f) : IsVacO ψ θ S T sS sT MS MT (om (g, h) f) := by
  have hθ : IsInfFam θ := hf.2.inf
  refine GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ g h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul]) (fun u => ?_) f hf
  have key := GlobalTheory.VacMove.mem_latO_iff_actO hLS hMS hLT hMT mg mh
  have back : actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
    have := GlobalTheory.WeilVacMove.actO_inv_actO g⁻¹ h⁻¹ u
    rwa [inv_inv, inv_inv] at this
  refine ⟨fun hu => ⟨actO S T g⁻¹ h⁻¹ u, (key _).2 (by rwa [back]), back.symm⟩, ?_⟩
  rintro ⟨u₀, hu₀, rfl⟩
  exact (key _).1 hu₀

theorem _root_.GlobalTheory.T.movedVacuum_negHom_eq_vacuum_movedLattices : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    IsVacO ψ θ (neg A) WW (fun τ => -(moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.s τ) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.s (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mg mg' mh t₀ r r' hr hrt hrt'
  have hWd : IsWeilDatumO ψ (neg A) WW _ _ ((Y.ω t₀).toSgn true) := hY.weil t₀
  have hg₁ : (GlobalTheory.Grid.ofSgn true A).symm g ∈ GfC (neg A) := hg
  have mg₁ : GlobalTheory.FinPl.Moves (neg A) ((GlobalTheory.Grid.ofSgn true A).symm g) Y.rA.Λ ΛA (fun _ => True) := mg
  have key := isVacO_move ψ θ (neg A) WW _ _ ((Y.ω t₀).toSgn true) hWd (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.Λ ΛA Y.rW.Λ ΛW
    (GlobalTheory.RowTest.isSelfDualC_neg' hY.rigA.1) (GlobalTheory.RowTest.isSelfDualC_neg' hA) hY.rigW.1 hW
    ((GlobalTheory.Grid.ofSgn true A).symm g) hg₁ h hh mg₁ mh Y.vac hY.isVac
  have e : ((Y.ω t₀).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm g, h) Y.vac = Y.ω t₀ (g, h) Y.vac := rfl
  rw [e] at key
  have e1 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.s = Y.rA.s := rfl
  have e2 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.s = Y.rW.s := rfl
  have e3 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ = ΛA := rfl
  have e4 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ = ΛW := rfl
  have e5 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac = Y.ω t₀ (g, h) Y.vac := rfl
  rw [e1, e2, e3, e4, e5]
  exact key
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

noncomputable section

namespace GlobalTheory.BotMoveSnd

variable {D : D7}

theorem heisO_smul' {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (ζ : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (ζ • g) = ζ • heisO ψ S T w g := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem isPlaceModel_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ}
    (a : ℂ) {g₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c g₀ Tm) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (a • g₀) (a • Tm) :=
  { trans := fun Φ hΦ x hx => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.trans Φ hΦ x hx, heisO_smul']
    modul := fun Φ hΦ y hy => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.modul Φ hΦ y hy, heisO_smul']
    vac := by rw [LinearMap.smul_apply, hT.vac] }

theorem isThetaAt_rescale {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c κ : ℂ}
    {f₀ Φ f : WO S T → ℂ} (hκ : κ ≠ 0) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (κ • f₀) Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ (κ⁻¹ • f) := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  refine ⟨⟨κ⁻¹ • Tm, ?_⟩, fun Tm' hT' => ?_⟩
  · have := isPlaceModel_smul κ⁻¹ hT
    rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul] at this
  · rw [hall _ (isPlaceModel_smul κ hT'), LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hκ, one_smul]

theorem isHalf_iff_smul {m n : ℕ} (c : AE D) (u : Mx D m n) : IsHalf c u ↔ c • u = u :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem isHalf_actO' {S T : HSp D} (c : AE D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf c x) :
    IsHalf c (actO S T g h x) := by
  rw [isHalf_iff_smul] at hx ⊢
  rw [GlobalTheory.VacMove.actO_eq]
  conv_rhs => rw [← hx]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_actO_inv_iff {S T : HSp D} (c : AE D) (g : GA D S) (h : GA D T) (x : WO S T) :
    IsHalf c (actO S T g⁻¹ h⁻¹ x) ↔ IsHalf c x := by
  refine ⟨fun hx => ?_, isHalf_actO' c _ _⟩
  have := isHalf_actO' c g h hx
  have e := GlobalTheory.SplitHecke.actO_inv_actO (S := S) (T := T) g⁻¹ h⁻¹ x
  simp only [inv_inv] at e
  rwa [e] at this

theorem frame_move_alg {R : Type} [CommRing R] {s t : ℕ} (a βS : GL (Fin s) R) (b βT : GL (Fin t) R)
    (K : Matrix (Fin s) (Fin t) R) :
    ((a * βS)⁻¹ : GL (Fin s) R).1 * K * (b * βT).1 =
      (βS⁻¹).1 * (a⁻¹).1 * βS.1 * ((βS⁻¹).1 * K * βT.1) * ((βT⁻¹ * b⁻¹ * βT)⁻¹ : GL (Fin t) R).1 := by
  have e1 : (βS.1 : Matrix (Fin s) (Fin s) R) * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : (βT.1 : Matrix (Fin t) (Fin t) R) * (βT⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e3 : ((βT⁻¹ * b⁻¹ * βT)⁻¹ : GL (Fin t) R) = βT⁻¹ * b * βT := by group
  rw [e3, _root_.mul_inv_rev]
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1 (βS⁻¹).1, e1, Matrix.one_mul, ← Matrix.mul_assoc βT.1 (βT⁻¹).1, e2, Matrix.one_mul]

theorem frMapAdj_move (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D S)
    (h : GA D T) (x : WO S T) :
    frMapAdj S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = frMapAdj S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  have split : actO S T g⁻¹ h⁻¹ x = actO S T g⁻¹ 1 (actO S T 1 h⁻¹ x) := by
    simp only [GlobalTheory.VacMove.actO_eq, inv_one, GlobalTheory.VacMove.mt_one₀, Matrix.one_mul, Matrix.mul_one]
  rw [split, GlobalTheory.FreeBlockTwist.frMapAdj_actO_one, GlobalTheory.AdjAct.frMapAdj_actO, ← GlobalTheory.AdjAct.finE_inv_val, ← map_inv]
  unfold frMapAdj
  rw [map_inv (Lev.finE S), map_inv (Lev.finE T), ← Matrix.mul_assoc]
  exact frame_move_alg (R := EAf D) (Lev.finE S g) βS (Lev.finE T h) βT _

theorem stdSnd_move (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (S T : HSp D)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) (x : WO S T) :
    stdSnd ν e I a S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = stdSnd ν e I a S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  unfold stdSnd dualCoord
  rw [frMapAdj_move]
  rw [propext (isHalf_actO_inv_iff (cA D e) g h x)]

theorem snd_moved : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    ∀ t, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t)) (latO A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac'
    (stdSnd (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A.rank A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f' t) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv' t
  have hWe : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := (GlobalTheory.Grid.isWeil_false ψ A' WW _ _ _).1 (hY.weil' t)
  have hee : cA D (Y.e t) * cA D (Y.e t) = cA D (Y.e t) := by
    rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self (hY.idem t)]
  have hinf : infPart D (cA D (Y.e t)) = 0 :=
    GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum (hY.idem t))
  have hm := GlobalTheory.VacMove.isThetaAt_moveLat D ψ A' WW (α t) (α t / β t) (Y.ω' t) hWe Y.rA'.Λ ΛA' Y.rW.Λ ΛW hY.rigA'.1 hA'
    hY.rigW.1 hW g' hg' h hh mA' mW (cA D (Y.e t)) _ Y.vac' (Y.f' t) hee hinf hY.isVac'.2.theta
    (GlobalTheory.ConstRatio.theta_f hY t).2 (hY.snd t)
  rw [hv' t] at hm
  have hm2 := isThetaAt_rescale (hr t).2 hm
  have hΦ : (fun x => stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW Y.rA'.β Y.rW.β (actO A' WW g'⁻¹ h⁻¹ x)) =
      stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW (Lev.finE A' g' * Y.rA'.β) (Lev.finE WW h * Y.rW.β) :=
    funext fun x => (stdSnd_move _ _ _ _ _ _ _ _ _ _ x).symm
  rw [hΦ] at hm2
  exact hm2

end GlobalTheory.BotMoveSnd

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

namespace GlobalTheory.BotMove.Fst

private theorem selfDual_neg {D : D7} {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (hA : IsSelfDualC A Λ) :
    IsSelfDualC (GlobalTheory.Grid.neg A) Λ := by
  refine ⟨hA.1, fun y => (hA.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
  · simp [GlobalTheory.Grid.neg_gram, hc]
  · simp [GlobalTheory.Grid.neg_gram] at hc ⊢
    exact neg_eq_iff_eq_neg.2 hc

private theorem placeModel_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) (c : ℂ) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • f₀) (c • Tm) := by
  have hs : ∀ x (F : WO S T → ℂ), heisO ψ S T x (c • F) = c • heisO ψ S T x F := fun x F => by
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hs, h.trans Φ hΦ x hx]
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hs, h.modul Φ hΦ y hy]
  · rw [LinearMap.smul_apply, h.vac]

private theorem thetaAt_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)}
    {f₀ Φ f : WO S T → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • f₀) Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ (c⁻¹ • f) := by
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := h
  refine ⟨⟨c⁻¹ • T₀, ?_⟩, fun T' hT' => ?_⟩
  · have := placeModel_smul hT₀ c⁻¹
    rwa [inv_smul_smul₀ hc] at this
  · have e1 : f = (c • T') Φ := hall _ (placeModel_smul hT' c)
    show c⁻¹ • f = T' Φ
    rw [e1, LinearMap.smul_apply, inv_smul_smul₀ hc]

private theorem thetaAt_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ')
    (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hb : GlobalTheory.FinPl.Moves S b Λ M (fun _ => True))
    (hb' : GlobalTheory.FinPl.Moves T b' Λ' M' (fun _ => True)) {e : AE D} {Φ f₀ f : WO S T → ℂ} (hee : e * e = e)
    (hinf : infPart D e = 0) (hf₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀)
      (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) (om (b, b') f) := by
  have key := GlobalTheory.VacMove.mem_latO_iff_actO hΛ hM hΛ' hM' hb hb'
  have key' := GlobalTheory.VacMove.mem_latO_iff_actO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb')
  have omm : ∀ p q (X : WO S T → ℂ), om p (om q X) = om (p * q) X := fun p q X => by
    rw [map_mul]; rfl
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hf
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T Λ Λ' hΛ hΛ' e hee hinf f₀ hf₀ T₀ hT₀
  refine ⟨⟨_, GlobalTheory.SplitMove.isPlaceModel_move₂ hW key hT₀ th0⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T M M' hM hM' e hee hinf _
    (hW.om_pres _ _ hf₀) T' hT'
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW key' hT' th1
  have ev : om (b⁻¹, b'⁻¹) (om (b, b') f₀) = f₀ := by
    rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
  rw [ev] at pm
  have hf' : f = om (b⁻¹, b'⁻¹) (T' fun t => Φ (actO S T b⁻¹ b'⁻¹ t)) := hall _ pm
  rw [hf', omm, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one]; rfl

private theorem frMapO_move {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (g : GA D S) (h : GA D T) (x : WO S T) :
    frMapO S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  have e1 : (Formalism.L2.Theta.mt T h⁻¹).map (toEAf D) = ((Lev.finE T h)⁻¹).val := by
    rw [← map_inv]; rfl
  have e2 : (Formalism.L2.Theta.mt S g).map (toEAf D) = (Lev.finE S g).val := rfl
  rw [frMapO, frMapO, actO, inv_inv, Matrix.map_mul, Matrix.map_mul, e1, e2, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

private theorem stdFst_move {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (S T : HSp D)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) :
    stdFst ν e I S T (Lev.finE S g * βS) (Lev.finE T h * βT) = fun x => stdFst ν e I S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  funext x
  unfold stdFst
  rw [frMapO_move, GlobalTheory.SchrMove.isHalf_actO_iff g⁻¹ h⁻¹ x]

end GlobalTheory.BotMove.Fst

theorem _root_.GlobalTheory.T.movedFiniteDatum_negHom_eq_standardPair_first : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    ∀ t, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) (latO (neg A) WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac
    (stdFst (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f t) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA _ hW g _ g' _ h _ mA _ mW t₀ r r' hr hv _ t
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hY.idem t)
  have mA' : GlobalTheory.FinPl.Moves (neg A) ((ofSgn true A).symm g) Y.rA.Λ ΛA (fun _ => True) := mA
  have h1 := GlobalTheory.BotMove.Fst.thetaAt_move (S := neg A) (hY.weil t) (GlobalTheory.BotMove.Fst.selfDual_neg hY.rigA.1)
    (GlobalTheory.BotMove.Fst.selfDual_neg hA) hY.rigW.1 hW mA' mW ho.idem ho.infPart_eq hY.isVac.2.theta (hY.fst t)
  have e1 : ∀ F, (Y.ω t).toSgn true ((ofSgn true A).symm g, h) F = Y.ω t (g, h) F := fun F => rfl
  rw [e1, e1, hv t] at h1
  have h2 := GlobalTheory.BotMove.Fst.thetaAt_smul (hr t).1 h1
  have e2 := GlobalTheory.BotMove.Fst.stdFst_move (α t / β t) (Y.e t) (Y.ideal S t) A WW Y.rA.β Y.rW.β g h
  show IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) (Y.e t) (latO (neg A) WW ΛA ΛW fun _ => True) 1 (Y.ω t₀ (g, h) Y.vac)
    (stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW (Lev.finE A g * Y.rA.β) (Lev.finE WW h * Y.rW.β))
    ((r t)⁻¹ • Y.ω t (g, h) (Y.f t))
  rw [e2]
  exact h2
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

theorem frameVector_isCombination_tangentBasis_flagCover_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}
    (X : GlobalTheory.FlagMod.FlagCover Y) (U : Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left))
    (h1 : ∀ i, IsTanAtG Y.t (LogKS.chart U) (v i))
    (h2 : ∀ w', IsTanAtG Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (LogKS.chart U) v cf w')
    (h3 : ∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG Y.t (LogKS.chart U) v
      (Pi.single (e ⟨τ, i⟩) (algX Y.s U.1 (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (Y.t.act.act a).left))
    (k : X.F.J) (S : Type) [CommRing S] (z' : Sp S ⟶ X.YY) (x : Sp S ⟶ Y.X) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (hk : ⊤ ≤ z' ⁻¹ᵁ X.F.U k) (hx : z' ≫ X.π = x) :
    ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
      IsCombAtG Y.t x (fun j => spMap (dualMap (ev x U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i)
        (tv (X.F.vecAt k z' hk hx σ i)).left := by
  classical
  subst hx
  have hxψ : spMap (ev (z' ≫ X.π) U.1 hU) ≫ LogKS.chart U = z' ≫ X.π := GlobalTheory.FlagMod.spMap_ev _ U.2 hU
  obtain ⟨b1, b2⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange Y.t (ev (z' ≫ X.π) U.1 hU) (LogKS.chart U) n v h1 h2
  rw [hxψ] at b1 b2

  set ψ := ev (z' ≫ X.π) U.1 hU with hψ
  let φ : c.F →+* S := (ev ((z' ≫ X.π) ≫ Y.s) ⊤ le_top).comp (toΓ c.F)
  have hφ : z' ≫ X.π ≫ Y.s = spMap φ := by
    rw [GlobalTheory.FlagMod.spMap_ev_top, Category.assoc]
  have hφψ : ∀ r : c.F, ψ (algX Y.s U.1 r) = φ r := fun r =>
    GlobalTheory.FlagMod.ev_appLE (z' ≫ X.π) Y.s (by simp) hU le_top (toΓ c.F r)
  let V : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (z' ≫ X.π) Y.t.G := fun m => GlobalTheory.LieMet.tanOf (b1 m)
  have hb : ∀ W, ∃! a : Fin n → S, ∑ i, a i • V i = W := fun W => by
    obtain ⟨a, ha, hu⟩ := b2 _ (GlobalTheory.LieMet.isTan_tv W)
    exact ⟨a, ((GlobalTheory.LieMet.isComb_iff V a W).1 ha).symm,
      fun a' ha' => hu a' ((GlobalTheory.LieMet.isComb_iff V a' W).2 ha'.symm)⟩
  have hV : ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)) (a : 𝓞 E),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a (V (e ⟨τ, j⟩)) = φ (embK c τ a) • V (e ⟨τ, j⟩) := by
    intro τ j a
    have h := (GlobalTheory.TanBaseChange.tan_comb_baseChange E H Y.X Y.t _ S ψ (LogKS.chart U) _ hxψ).2 n v _ _ (h3 a τ j)
    have e1 : (fun i => ψ ((Pi.single (e ⟨τ, j⟩) (algX Y.s U.1 (embK c τ a)) : Fin n → Γ(Y.X, U.1)) i)) =
        fun i => (Pi.single (e ⟨τ, j⟩) (φ (embK c τ a)) : Fin n → S) i := by
      funext i
      by_cases hi : i = e ⟨τ, j⟩
      · subst hi; simp [hφψ]
      · simp [Pi.single_apply, hi]
    rw [e1] at h
    have e2 : spMap (dualMap ψ) ≫ v (e ⟨τ, j⟩) ≫ (Y.t.act.act a).left =
        (tv (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a (V (e ⟨τ, j⟩)))).left := by
      rw [← Category.assoc]; rfl
    rw [e2] at h
    rw [(GlobalTheory.LieMet.isComb_iff V _ _).1 h]
    simp [Pi.single_apply]
  letI : Algebra c.F S := φ.toAlgebra
  have hs := GlobalTheory.FlagEmb.EigSpread.splits (E := E) c
  have hu : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act) (embK c z.1) (V (e z)) :=
    fun z a => hV z.1 z.2 a
  have hb' : ∀ w, ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S, ∑ z, a z • V (e z) = w := fun w => by
    obtain ⟨a, ha, hu⟩ := hb w
    refine ⟨fun z => a (e z), ?_, fun a' ha' => ?_⟩
    · rw [← ha]; exact Equiv.sum_comp e (fun i => a i • V i)
    · have h' : ∑ i, a' (e.symm i) • V i = w := by
        rw [← ha', ← Equiv.sum_comp e.symm (fun z => a' z • V (e z))]; simp
      have := hu _ h'
      funext z
      have := congrFun this (e z)
      simpa using this
  have key : ∀ σ i, ∃ cf : Fin (Dw.mult σ) → S, ∑ j, cf j • V (e ⟨σ, j⟩) = X.F.vecAt k z' hk rfl σ i :=
    fun σ i => (GlobalTheory.FlagEmb.EigSpread.block_basis hs (fun z => V (e z)) hu hb' σ _
      (fun a => GlobalTheory.VarFlag.actR_vecAt X φ z' k hk hφ σ i a)).exists
  choose C hC using key
  refine ⟨fun σ => Matrix.of fun i j => C σ i j, fun σ i => ?_⟩
  exact (GlobalTheory.LieMet.isComb_iff (fun j => V (e ⟨σ, j⟩)) (C σ i) _).2 (hC σ i).symm

theorem isCombAtG_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z), ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv k S _ z hU hk hx
  exact frameVector_isCombination_tangentBasis_flagCover_point TF.X U e v hv.1 hv.2.1 hv.2.2 k S (z ≫ inc₀ TF.X Z) (z ≫ toBase TF Z) hU hk hx

end GlobalTheory.LogPole
end
end

section

namespace GlobalTheory

theorem abelianDualCrystal_of_dualAbelianScheme :
    GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.AbelianDualCrystal :=
  fun h ↦ ⟨h, GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.toCrystallineDeRham⟩

end GlobalTheory
end
