module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle277
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle323
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle326
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle328
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle267
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isVac_of_nodeAgree {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}
    {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) {N₁ N₂ : GlobalTheory.Grid.Node D} {X₁ X₂ : GlobalTheory.ChiGrid.Node}
    (h₁ : NodeAgree N₁ W X₁) (h₂ : NodeAgree N₂ W X₂) (f : WO (G'.V X₁) (G'.V X₂) → ℂ)
    (hf : IsVacO W.ψ W.θ (G'.V X₁) (G'.V X₂) (W.cart X₁) (W.cart X₂) (G'.Λ X₁ : Set _) (G'.Λ X₂ : Set _) f) :
    ∃ f' : WO N₁.V N₂.V → ℂ, GlobalTheory.Grid.IsVac W.ψ W.θ false N₁ N₂ f' := by
  obtain ⟨V₁, S₁, M₁, Λ₁, β₁⟩ := N₁
  obtain ⟨V₂, S₂, M₂, Λ₂, β₂⟩ := N₂
  obtain ⟨sp₁, lat₁, cart₁, -⟩ := h₁
  obtain ⟨sp₂, lat₂, cart₂, -⟩ := h₂
  dsimp only at sp₁ sp₂ lat₁ lat₂ cart₁ cart₂
  subst sp₁ sp₂
  cases eq_of_heq lat₁
  cases eq_of_heq lat₂
  refine ⟨f, ?_⟩
  have c₁ := eq_of_heq cart₁
  have c₂ := eq_of_heq cart₂
  unfold GlobalTheory.Grid.IsVac GlobalTheory.Grid.cartS
  simp only [GlobalTheory.Grid.sgnM, cond]
  rw [c₁, c₂]
  exact hf

theorem exists_isVac_col : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ j, j < D.R.m → ∃ f : WO (G.Xp j).V (G.nX j).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ false (G.Xp j) (G.nX j) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hA _ j hj
  have hp : (GlobalTheory.ChiGrid.Pair.top A.μ0 j).InRange D.R.m := by
    simp only [GlobalTheory.ChiGrid.Pair.InRange, GlobalTheory.ChiGrid.Pair.big, GlobalTheory.ChiGrid.Node.InRange]
    omega
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev hp
  obtain ⟨f', hf'⟩ := exists_isVac_of_nodeAgree W (hA.top j hj.le) (hA.top (j + 1) hj) f hf
  rw [hW.ψ, hW.θ] at hf'
  exact ⟨f', hf'⟩

end GlobalTheory.GridJoin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GridJoin

theorem isVacO_transport {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) :
    ∀ (S S' S₀ S₀' : HSp D) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (a' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ)
      (a₀ : D.what₂.Tau → Matrix (Fin S₀.rank) (Fin S₀.rank) ℂ)
      (a₀' : D.what₂.Tau → Matrix (Fin S₀'.rank) (Fin S₀'.rank) ℂ)
      (Λ : Set (Fin S.rank → D.host.E)) (Λ' : Set (Fin S'.rank → D.host.E))
      (Λ₀ : Set (Fin S₀.rank → D.host.E)) (Λ₀' : Set (Fin S₀'.rank → D.host.E)),
      S = S₀ → S' = S₀' → HEq a a₀ → HEq a' a₀' → HEq Λ Λ₀ → HEq Λ' Λ₀' →
      (∃ f, IsVacO ψ θ S₀ S₀' a₀ a₀' Λ₀ Λ₀' f) → ∃ f, IsVacO ψ θ S S' a a' Λ Λ' f := by
  rintro S S' _ _ a a' a₀ a₀' Λ Λ' Λ₀ Λ₀' rfl rfl h1 h2 h3 h4 h
  cases eq_of_heq h1; cases eq_of_heq h2; cases eq_of_heq h3; cases eq_of_heq h4
  exact h

theorem heq_coe_lat {D : D7} {V V' : HSp D} (h : V = V') {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (hΛ : HEq Λ Λ') :
    HEq (Λ : Set (Fin V.rank → D.host.E)) (Λ' : Set (Fin V'.rank → D.host.E)) := by
  subst h; cases eq_of_heq hΛ; rfl

theorem exists_isVac_th_rows : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∃ f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hS _ i j hi hj
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .mu A.μ0 (i + 1) j) ⟨hi, by omega⟩
  have a := hS.vert (i + 1) j hi hj.le
  have b := hS.vert (i + 1) (j + 1) hi hj
  rw [← hW.ψ, ← hW.θ]
  exact isVacO_transport W.ψ W.θ _ _ _ _ _ _ _ _ _ _ _ _ a.sp b.sp a.cart b.cart
    (heq_coe_lat a.sp a.lat) (heq_coe_lat b.sp b.lat) ⟨f, hf⟩

end GlobalTheory.GridJoin
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin.VacX

variable {D : D7}

theorem transport (ψ ψ' : AddChar (AF D.host.F) ℂ) (θ θ' : InfFam D) (hψ : ψ' = ψ) (hθ : θ' = θ)
    {S S' T T' : HSp D} (hS : S = S') (hT : T = T')
    {cS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {cS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ}
    (hcS : HEq cS cS')
    {cT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {cT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ}
    (hcT : HEq cT cT')
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    (hΛS : HEq ΛS ΛS')
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    (hΛT : HEq ΛT ΛT')
    {f : WO (negSp S') T' → ℂ}
    (h : IsVacO ψ' θ' (negSp S') T' (fun τ => -cS' τ) cT' (ΛS' : Set _) (ΛT' : Set _) f) :
    ∃ f' : WO (GlobalTheory.Grid.sgn true S) T → ℂ,
      IsVacO ψ θ (GlobalTheory.Grid.sgn true S) T (fun τ => GlobalTheory.Grid.sgnM true (cS τ)) cT (ΛS : Set _) (ΛT : Set _) f' ∧ HEq f' f := by
  subst hS hT hψ hθ
  obtain rfl := eq_of_heq hcS
  obtain rfl := eq_of_heq hcT
  obtain rfl := eq_of_heq hΛS
  obtain rfl := eq_of_heq hΛT
  exact ⟨f, h, HEq.rfl⟩

end GlobalTheory.GridJoin.VacX


open GlobalTheory.GridJoin.VacX in
theorem GlobalTheory.GridJoin.exists_vacX : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∃ f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f ∧ (j = 0 → HEq f (W.vac i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hag _ i j hi hj
  have hS := hag.vert (i + 1) j (by omega) hj
  have hT := hag.vert i j (by omega) hj
  have key : ∀ f, W.IsVac (.chi i j) f → ∃ f' : WO (G.V (i + 1) j).V (G.V i j).V → ℂ,
      GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f' ∧ HEq f' f := fun f hf =>
    transport R.ψ W.ψ R.θ W.θ hW.ψ hW.θ hS.sp hT.sp hS.cart hT.cart hS.lat hT.lat hf
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · obtain ⟨f, h1, h2⟩ := key (W.vac i) (W.vac_is i hi)
    exact ⟨f, h1, fun _ => h2⟩
  · obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .chi i j) ⟨hi, hj⟩
    obtain ⟨f', h1, -⟩ := key f hf
    exact ⟨f', h1, fun h => by omega⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol


open GlobalTheory.HolRead in
theorem holUpTo_of_lowKilled : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (la : Wt C.X.Ψ T.rank) (m : D.what₂.Tau → ℤ) (φ : GA D T → ℂ), LowKilled C.θ T B φ → (∀ (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (g : GA D T), φ (g * torAt C.θ T B ρ t) = cexp (((∑ a, ((m ρ - la (C.m.e ρ) a : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) * φ g) → HolUpTo C B la (detPow C.θ T m) φ := by
  intro D S T C B hB la m φ hL htor g
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  obtain ⟨U1, U2, U3⟩ := GlobalTheory.T.conjugateModel_unitFrames_eq_movedOrthonormalFrames D S T C B hB
  obtain ⟨dMul, dNe, dExp⟩ := GlobalTheory.T.realPlaceDeterminantPower_mul_ne_zero_exp D C.θ C.inf T m
  let F : Frame C.X.Ψ T.rank → ℂ := fun y =>
    if h : IsUnitFr C.X y then φ (g * (U2 y h).choose) / detPow C.θ T m (U2 y h).choose else 0
  have hF : ∀ a ∈ GinfC T, F (C.xB (C.mvB a B)) = φ (g * a) / detPow C.θ T m a := by
    intro a ha
    have hy := U1 a
    simp only [F, dif_pos hy]
    rw [U3 _ (U2 _ hy).choose_spec.1 a ha (U2 _ hy).choose_spec.2]
  obtain ⟨Q, Q1, Q2⟩ := GlobalTheory.T.exists_extension_torusEquivariant_orthonormalFrames _ _ C.X la F (by
    intro y hy t
    obtain ⟨a, ha, rfl⟩ := U2 y hy
    let s : D.what₂.Tau → Fin T.rank → ℝ := fun ρ c => -t (C.m.e ρ) c
    obtain ⟨hk, hk2⟩ := GlobalTheory.T.compactTorusProductRealPlaces_spec D S T C B hB s
    have e1 := xB_mvB_mul C B hB a (torProd C.θ T B s) (fun τ => diagonal fun c => cexp ((t τ c : ℂ) * I)) fun ρ => ?_
    · erw [← e1]
      rw [hF _ (mul_mem ha hk), hF a ha, ← mul_assoc,
      apply_mul_torProd C.θ T B _ φ htor, apply_mul_torProd C.θ T B _ _ (GlobalTheory.T.realPlaceDeterminantPower_mul_compactTorusElement D S T C B hB m)]
      have hb : (bchar la fun τ => (diagonal fun c => cexp ((t τ c : ℂ) * I) : Matrix (Fin T.rank) (Fin T.rank) ℂ)) =
          cexp (((∑ ρ, ∑ c, ((la (C.m.e ρ) c : ℝ)) * t (C.m.e ρ) c : ℝ) : ℂ) * I) := by
        unfold bchar
        rw [← Equiv.prod_comp C.m.e]
        push_cast
        rw [Finset.sum_mul, Complex.exp_sum]
        refine Finset.prod_congr rfl fun ρ _ => ?_
        rw [Finset.sum_mul, Complex.exp_sum]
        refine Finset.prod_congr rfl fun c _ => ?_
        rw [diagonal_apply_eq, ← Complex.exp_int_mul, mul_assoc]
      have hA : cexp (((∑ ρ, ∑ c, ((m ρ - la (C.m.e ρ) c : ℤ) : ℝ) * s ρ c : ℝ) : ℂ) * I) =
          cexp (((∑ ρ, ∑ c, ((m ρ : ℤ) : ℝ) * s ρ c : ℝ) : ℂ) * I) *
            cexp (((∑ ρ, ∑ c, ((la (C.m.e ρ) c : ℝ)) * t (C.m.e ρ) c : ℝ) : ℂ) * I) := by
        rw [← Complex.exp_add, ← add_mul]
        congr 2
        rw [← Complex.ofReal_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [s]; push_cast; ring
      rw [hb, hA]
      field_simp [dNe a, Complex.exp_ne_zero]
      <;> ring
    · rw [hk2]
      show _ = B ρ * (diagonal fun c => cexp ((t (C.m.e ρ) c : ℂ) * I)).map (starRingEnd ℂ) * (B ρ)⁻¹
      rw [diagonal_map (map_zero _)]
      congr 3
      funext c
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      simp only [s]; push_cast; ring_nf)
  have hQ : ∀ a ∈ GinfC T, Q (C.xB (C.mvB a B)) = φ (g * a) / detPow C.θ T m a := fun a ha => by
    rw [Q1 _ (U1 a), hF a ha]
  refine ⟨Q, GlobalTheory.T.differentiableOn_frames_of_killedNilpotentDerivative _ _ C.X la Q Q2 fun y hy => ?_, Q2, fun a ha => ?_⟩
  swap
  · rw [hQ a ha]; field_simp [dNe a]
  obtain ⟨a, ha, rfl⟩ := U2 y hy
  have hs : DifferentiableAt ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 :=
    (((GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 hL.1) (g * a)).differentiable
      (by simp)) 0
  let L : Frame C.X.Ψ T.rank →L[ℝ] GlobalTheory.SmoothForms.LieN T := LinearMap.toContinuousLinearMap (toLieC C R B)
  let lam : GlobalTheory.SmoothForms.LieN T →L[ℝ] ℂ :=
    { toLinearMap := trLin T m
      cont := by
        change Continuous (fun Y : GlobalTheory.SmoothForms.LieN T => ∑ ρ, (m ρ : ℂ) * trace (Y ρ).1)
        fun_prop }
  let f : GlobalTheory.SmoothForms.LieN T → ℂ := fun Y =>
    (detPow C.θ T m a)⁻¹ * (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y) * cexp (-lam Y))
  have key : ∀ Z ∈ unitLie C.X, Q (rmul (C.xB (C.mvB a B)) (expFr Z)) = f (L Z) := by
    intro Z hZ
    have he := GlobalTheory.SmoothForms.isExpFam_expInf R (L Z)
    rw [← xB_mvB_mul C B hB a _ _ fun ρ => ?_, hQ _ (mul_mem ha he.1), dMul, dExp]
    · simp only [f, lam, mul_assoc, Complex.exp_neg]
      field_simp [dNe a]
      rfl
    · show infMat _ _ (C.θ ρ) _ = _
      rw [he.2 ρ]
      change NormedSpace.exp ((toLieC C R B Z ρ).1) = _
      rw [(GlobalTheory.T.conjFrameToRealLieAlgebra_spec D S T C R B hB Z hZ).1 ρ,
        Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det _).2 (isUnit_det_B C hB ρ))]
      congr 2
      exact (exp_map_conj _).symm
  have h0 : (0 : Frame C.X.Ψ T.rank) ∈ unitLie C.X := fun τ => by
    have : mat (0 : Frame C.X.Ψ T.rank) τ = 0 := rfl
    simp [this]
  let Dφ := fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0
  have hE : HasFDerivAt (fun Y : GlobalTheory.SmoothForms.LieN T => cexp (-lam Y)) (cexp (-lam 0) • -lam) 0 :=
    lam.hasFDerivAt.neg.cexp
  have hfd := (hs.hasFDerivAt.mul hE).const_mul (detPow C.θ T m a)⁻¹
  have hfd' : HasFDerivAt f ((detPow C.θ T m a)⁻¹ • (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) •
      (cexp (-lam 0) • -lam) + cexp (-lam 0) • Dφ)) (L 0) := by
    have h0L : L 0 = 0 := map_zero L
    rw [h0L]; exact hfd
  refine ⟨_ , (hfd'.comp (0 : Frame C.X.Ψ T.rank) L.hasFDerivAt).hasFDerivWithinAt.congr key (key 0 h0), ?_⟩
  intro τ c d hcd Z hZ Z' hZ' e
  obtain ⟨ρ, rfl⟩ := C.m.e.surjective τ
  have hD := GlobalTheory.T.fderiv_conjFrameToRealLie_loweringOperator_eq_zero D S T C R B hB φ hL (g * a) ρ c d hcd Z Z' hZ hZ' e
  have hT := GlobalTheory.T.weightedTrace_conjFrameToRealLie_loweringOperator D S T C R B hB m ρ c d hcd Z Z' hZ hZ' e
  have hℓ : ∀ W : Frame C.X.Ψ T.rank, ((detPow C.θ T m a)⁻¹ • (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) •
      (cexp (-lam 0) • -lam) + cexp (-lam 0) • Dφ)).comp L W = (detPow C.θ T m a)⁻¹ *
      (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) * (cexp (-lam 0) * -trLin T m (toLieC C R B W)) +
        cexp (-lam 0) * Dφ (toLieC C R B W)) := by
    intro W
    simp [L, lam, ContinuousLinearMap.comp_apply, mul_assoc]
    <;> ring
  rw [hℓ, hℓ]
  linear_combination ((detPow C.θ T m a)⁻¹ * cexp (-lam 0)) * hD -
    ((detPow C.θ T m a)⁻¹ * φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) * cexp (-lam 0)) * hT

end GlobalTheory.AdSpan.ConjHol
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdSpan.ReVec

variable {D : D7}

def reWEquiv (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : WO S T ≃+ WO S T where
  toFun := reW S T b
  invFun := reWi S T b
  left_inv := reWi_reW S T b
  right_inv := reW_reWi S T b
  map_add' := reW_add S T b

theorem continuous_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reW S T b) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  exact continuous_id.matrix_mul continuous_const

theorem continuous_reWi (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reWi S T b) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  exact continuous_id.matrix_mul continuous_const

theorem reW_mem_ratL_iff (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x : WO S T) :
    reW S T b x ∈ ratL T S ↔ x ∈ ratL T S := by
  have key : ∀ (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (N : Matrix (Fin S.rank) (Fin S.rank) D.host.E),
      x ∈ ratL T S → HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (β := Matrix (Fin S.rank) (Fin S.rank) (AE D))
        (γ := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x (N.map (incA D)) ∈ ratL T S := by
    rintro x N ⟨γ, rfl⟩
    refine ⟨γ * N, ?_⟩
    show (γ * N).map (incA D) = _
    exact Matrix.map_mul (f := incA D)
  constructor
  · intro h
    have h2 := key _ (frP S b) h
    have : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (reW S T b x) ((frP S b).map (incA D)) = x :=
      reWi_reW S T b x
    rwa [this] at h2
  · exact key x _

theorem reframeFunctionOnHoms_norm_one_covolumeOne (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) :
    AllSome (fun p : Measure (WO S T) × Set (WO S T) => IsCovolOne (ratL T S) p.1 p.2) (fun p => nrm2 p.1 p.2 f = 1) → AllSome (fun p : Measure (WO (reS S b) T) × Set (WO (reS S b) T) => IsCovolOne (ratL T (reS S b)) p.1 p.2) (fun p => nrm2 p.1 p.2 (reF S T b f) = 1) := by
  rintro ⟨⟨p0, hp0⟩, hall⟩
  have he : Continuous (reWEquiv S T b) := continuous_reW S T b
  have he' : Continuous (reWEquiv S T b).symm := continuous_reWi S T b
  have hr : ∀ x, reWEquiv S T b x ∈ ratL T S ↔ x ∈ ratL T S := reW_mem_ratL_iff S T b
  have hr' : ∀ x, (reWEquiv S T b).symm x ∈ ratL T S ↔ x ∈ ratL T S := fun x => by
    rw [← hr, AddEquiv.apply_symm_apply]
  refine ⟨⟨(p0.1.map (reWEquiv S T b).symm, (reWEquiv S T b).symm '' p0.2),
    (GlobalTheory.Unf.ParCont.isCovolOne_map hp0 (reWEquiv S T b).symm he' he hr').1⟩, ?_⟩
  have aux : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      nrm2 μ 𝓕 (fun x => f (reWEquiv S T b x)) = 1 := by
    intro μ 𝓕 hp
    obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hp (reWEquiv S T b) he he' hr
    have h2 := hall (μ.map (reWEquiv S T b), reWEquiv S T b '' 𝓕) h1
    simp only [nrm2] at h2 ⊢
    rw [hemb.setIntegral_map, Set.preimage_image_eq _ (reWEquiv S T b).injective] at h2
    exact h2
  rintro ⟨μ', 𝓕'⟩ hp
  exact aux μ' 𝓕' hp

end GlobalTheory.AdSpan.ReVec
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.relIndex_integralMatrices_unitaryDiagonal_translate : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q → ∀ (r n : ℕ) (d : Fin r → ℤ) (t : GU c r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c r, ∀ k₂ ∈ KU c r, (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (k₁ * t * k₂).1.1)) = (q ^ 2) ^ (n * (∑ i, max (d i) 0).toNat) := by
  first | exact @GlobalTheory.LatIdx.relIndex_intMat_translate | exact GlobalTheory.LatIdx.relIndex_intMat_translate | (intros; apply GlobalTheory.LatIdx.relIndex_intMat_translate <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.levelCharacter_on_stabilizer_eq_prod_residue_characters_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ R.Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → X.chi2 ((iotaX X h).toMulEquiv κ).2 = ∏ PP ∈ R.Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ))) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ))) := by
  first | exact @GlobalTheory.SeeConjChar.levelCharacter_on_stabilizer_eq_prod_residue_characters | exact GlobalTheory.SeeConjChar.levelCharacter_on_stabilizer_eq_prod_residue_characters | (intros; apply GlobalTheory.SeeConjChar.levelCharacter_on_stabilizer_eq_prod_residue_characters <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift

theorem mem_range_map_subtype_of_contr (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)]
    [∀ i, Module ℂ (K i)] (N : ∀ i, Submodule ℂ (K i)) (x : ⨂[ℂ] i, K i)
    (h : ∀ i (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i), (∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L) → L x ∈ N i) :
    x ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by
  first
  | exact @_root_.GlobalTheory.TensorContraction.mem_range_map
  | exact _root_.GlobalTheory.TensorContraction.mem_range_map
  | (apply _root_.GlobalTheory.TensorContraction.mem_range_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorContraction.mem_range_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorContraction.mem_range_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorContraction.mem_range_map ..)

end GlobalTheory.Chain.IoLift
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.normalizedKernelOfVector_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (c • f) x y = c • kkVec S p f x y := by
  first | exact @GlobalTheory.TopZeroInv.kkVec_smul | exact GlobalTheory.TopZeroInv.kkVec_smul | (intros; apply GlobalTheory.TopZeroInv.kkVec_smul <;> assumption)
end
