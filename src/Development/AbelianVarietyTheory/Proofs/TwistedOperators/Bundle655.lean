module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle649
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenberg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle627
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle407
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle648
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle562
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.conjugatePlaces_liftLevelDatum_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∃ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q ∧ IdemTwo Lv.w ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), Lv.dat hn y = omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) := by
  first | exact @GlobalTheory.LiftDat.level_datum_eq | exact GlobalTheory.LiftDat.level_datum_eq | (intros; apply GlobalTheory.LiftDat.level_datum_eq <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict.ExactBig

variable {D : D7}

theorem exists_change {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χ χ₁ χ' : (AE D)ˣ →* Circle}
    {ω₁ : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (H₁ : IsWeilDatumO ψ S T χ₁ χ' ω₁)
    (hχ : IsHeckeChar D χ) (rχ : ResEta D χ S.rank) :
    ∃ ω, IsWeilDatumO ψ S T χ χ' ω ∧ ∀ u g y, IsDetRoot T g y → ω₁ (u, g) = (((χ₁ / χ) y : Circle) : ℂ) • ω (u, g) := by
  have r0 : ResEta D (χ * χ₁⁻¹) 0 :=
    Formalism.L2.Theta.resEta_parity (Formalism.L2.Theta.resEta_mul rχ (Formalism.L2.Theta.resEta_inv H₁.resS)) (by omega)
  have r1 : ResEta D 1 0 := ⟨r0.1, fun _ _ _ => by simp⟩
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  obtain ⟨ω, H, hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ H₁.std S T χ₁ χ' (χ * χ₁⁻¹) 1 ω₁ H₁
    (GlobalTheory.WeilChange.hecke_mul hχ (GlobalTheory.WeilChange.hecke_inv H₁.hecS)) h1 r0 r1
  have e : χ₁ * (χ * χ₁⁻¹) = χ := by rw [mul_comm χ, mul_inv_cancel_left]
  rw [e, mul_one] at H
  refine ⟨ω, H, fun u g y hy => ?_⟩
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D S u
  have e1 : (χ₁ / χ) y * (((1 : (AE D)ˣ →* Circle) x)⁻¹ * (χ * χ₁⁻¹) y) = 1 := by
    rw [MonoidHom.one_apply, inv_one, one_mul, ← MonoidHom.mul_apply, ← mul_assoc, div_mul_cancel, mul_inv_cancel,
      MonoidHom.one_apply]
  rw [hv u g x y hx hy, smul_smul, ← Circle.coe_mul, e1, Circle.coe_one, one_smul]

theorem seesaw_exact {ψ : AddChar (AF D.host.F) ℂ} {S A B : HSp D} {χ χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle}
    {ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)} {ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)}
    {ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ)}
    (H₁ : IsWeilDatumO ψ S A χ₁ χ₁' ω₁) (H₂ : IsWeilDatumO ψ S B χ₂ χ₂' ω₂)
    (H : IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ (χ₁' * χ₂') ω)
    {φ : WO S A → ℂ} {φ' : WO S B → ℂ} (hφ : IsThetaFunO ψ S A φ) (hφ' : IsThetaFunO ψ S B φ')
    (u : GA D S) (g : GA D A) (g₁ : GA D B) {x y : (AE D)ˣ} (hx : IsDetRoot A g x) (hy : IsDetRoot B g₁ y) :
    thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ' = (((χ₁ / χ) x : Circle) : ℂ) * (((χ₂ / χ) y : Circle) : ℂ) *
      thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') := by
  obtain ⟨o₁, K₁, e₁⟩ := exists_change H₁ H.hecS H.resS
  obtain ⟨o₂, K₂, e₂⟩ := exists_change H₂ H.hecS H.resS
  have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ H.std _ A B (GlobalTheory.BiTransfer.sumDec A B) S).om_box χ χ₁' χ₂' ω o₁
    o₂ H K₁ K₂ u g g₁ φ φ' hφ hφ'
  simp only [thetaKO]
  rw [← GlobalTheory.SeesawSumTarget.emb_sumDec, ← GlobalTheory.SeesawSumTarget.boxT_sumDec, key, GlobalTheory.MixModel.OrthDec.boxT_zero,
    e₁ u g x hx, e₂ u g₁ y hy]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem adjoint_exact {ψ : AddChar (AF D.host.F) ℂ} {S B : HSp D} {χB χS : (AE D)ˣ →* Circle}
    {ω₂ : GA D B × GA D S →* Module.End ℂ (WO B S → ℂ)} (H : IsWeilDatumO ψ B S χB χS ω₂) :
    ∃ ω : GA D (negSp S) × GA D B →* Module.End ℂ (WO (negSp S) B → ℂ),
      IsWeilDatumO ψ (negSp S) B χS⁻¹ χB⁻¹ ω ∧ ∀ f : WO B S → ℂ, IsThetaFunO ψ B S f →
        IsThetaFunO ψ (negSp S) B (fun y => f (adjM S B y)) ∧
        ∀ g₁ u, thetaKO ω (negGA S u) g₁ (fun y => f (adjM S B y)) = thetaKO ω₂ g₁ u f := by
  have hψ := H.std
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂),
    GlobalTheory.ConjWeil.weil_conjSource D ψ S B _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ B S _ _ ω₂ H),
    fun f hf => ?_⟩
  have e : (fun y : WO (negSp S) B => f (adjM S B y)) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.AdjSwap.dagger_eq_adjM]
  rw [e]
  have h1 : IsThetaFunO ψ S B (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) :=
    ((GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ B S).2.2.1 f).2 hf
  refine ⟨((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S B).1 _).2.2 h1, fun g₁ u => ?_⟩
  show GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂) (negGA S u, g₁) _ 0 = ω₂ (g₁, u) f 0
  rw [GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.AdjSwap.dagger_eq_adjM, adjM_zero]

theorem attChr_eq {C : Type} [CommGroup C] (χ η : C) (n : ℕ) :
    Formalism.IndefR.Lift.attChr χ η n = χ / η ^ (n % 2) := by
  unfold Formalism.IndefR.Lift.attChr
  rcases Nat.even_or_odd n with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]; simp
  · rw [if_pos h, Nat.odd_iff.1 h]; simp [div_eq_mul_inv]

theorem kerBig_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerBig W Θ g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωA u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumA W Θ) := by
  intro D T L sc G μ₀ hL W t i j ωA hA B ρ Θ Θ' hΘ g g₁ u
  have hd := isThetaFunO_of_isMatched hL W B ρ t i j Θ Θ' hΘ
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, hω₂, hadj⟩ := adjoint_exact h2
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  obtain ⟨s, hs⟩ := odd_sLen D
  obtain ⟨t', ht⟩ := D.R.t_odd
  have pW : (G.V (.grid (i + 1) (j + 1))).rank % 2 = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
    rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
    simp only [rankV, add_mul, one_mul]
    omega
  have pV : (G.V (.grid i (j + 1))).rank % 2 = (G.V (.grid (i + 1) j)).rank % 2 := by
    rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
    simp only [rankV, add_mul, one_mul]
    omega
  have cT : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j =
      G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹ := by
    simp only [GridData.chrT, GridData.chrS, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha]
    rw [pV, mul_div_mul_right_eq_div, ← div_eq_mul_inv, div_div_div_cancel_right]
  have cV : G.chrS (.chi i (j + 1)) / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = (L.eta ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j))⁻¹ := by
    simp only [GridData.chrS, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta]
    rw [pW, two_mul, pow_add, div_div, mul_left_comm, div_mul_cancel_left]
  have cV₁ : (G.chrT (.mu t (i + 1) j))⁻¹ / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j =
      (L.mu t (j + 1) * G.ch.chi (D.R.m - i))⁻¹ := by
    simp only [GridData.chrT, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta]
    rw [pW, inv_div, div_div, ← mul_assoc, div_mul_cancel_right]
  rw [cT] at hA
  let S := G.V (.grid (↑i + 1) (↑j + 1))
  let A := G.V (.grid (↑i) (↑j + 1))
  let Bs := G.V (.grid (↑i + 1) ↑j)
  have hA' : IsWeilDatumO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs) _ _ (ωA.toSgn true) := hA
  have e : ∀ d ∈ Θ.support, W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁ =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ * ωA (u, GlobalTheory.SquareComm.blk A Bs (g, g₁))
        (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) 0 := fun d hdm => by
    have k := seesaw_exact h1 hω₂ hA' (hd d hdm).1 (hadj _ (hd d hdm).2).1 (negGA S u) g g₁
      (GlobalTheory.RecDict.exists_isDetRoot D _ g).choose_spec (GlobalTheory.RecDict.exists_isDetRoot D _ g₁).choose_spec
    rw [(hadj _ (hd d hdm).2).2, cV, cV₁] at k
    exact k

  simp only [thetaKO, GlobalTheory.SquareDict.datumA, kerBig, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
  smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hdm => ?_
  rw [e d hdm]
  ring

end GlobalTheory.SquareDict.ExactBig

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharComb

variable {D : D7}

theorem pairA_zero_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  exact Prod.ext (zero_mul _) rfl

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) :
    α * β ∈ intAf D.host.F := fun v => by
  rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem complId_mul {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x y : AE D} (hx : x ∈ complId 𝔞)
    (hy : y ∈ complId 𝔟) : x * y ∈ complId (𝔞 * 𝔟) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, a, ha, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, b, hb, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_zero_mul]
      exact tmul_mem_complId (intAf_mul hα hβ) (FractionalIdeal.mul_mem_mul ha hb)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem infPart_of_mem {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : AE D} (hx : x ∈ complId 𝔠) :
    infPart D x = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, a, -, rfl⟩ := hx
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] a = 0
    exact TensorProduct.zero_tmul _ _
  | zero => exact map_zero _
  | add x z _ _ hx hz => rw [RingHom.map_add (f := _), hx, hz, add_zero]
  | neg x _ hx => rw [RingHom.map_neg, hx, neg_zero]

def finId (𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : AddSubgroup (EAf D) :=
  (complId 𝔠).map (toEAf D).toAddMonoidHom

theorem finId_mul {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x y : EAf D} (hx : x ∈ finId 𝔞)
    (hy : y ∈ finId 𝔟) : x * y ∈ finId (𝔞 * 𝔟) := by
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  exact ⟨x₀ * y₀, complId_mul hx₀ hy₀, map_mul (toEAf D) x₀ y₀⟩

theorem tmul_one_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {a : D.host.E} (ha : a ∈ 𝔠) :
    a ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ finId 𝔠 :=
  ⟨_, tmul_mem_complId one_mem_intAf ha, rfl⟩

theorem int_mem_finId_one {z : EAf D} (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    z ∈ finId (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  induction hz using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨b, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨b, hb⟩ := b
      exact tmul_one_mem_finId ((FractionalIdeal.mem_one_iff _).2 hb)
    · exact ⟨_, tmul_mem_complId y.2 (FractionalIdeal.one_mem_one _), rfl⟩
  | zero => exact zero_mem _
  | one => exact tmul_one_mem_finId (FractionalIdeal.one_mem_one _)
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy => simpa using finId_mul hx hy

theorem idS_mem_finId (𝔪 : Ideal (𝓞 D.host.E)) {t : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (ht : t ∈ Formalism.L2.DIV.idS D.host.F 𝔪) :
    (t : EAf D) ∈ finId ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe]
    exact tmul_one_mem_finId ((FractionalIdeal.mem_coeIdeal _).2 ⟨m, hm, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => rw [Subring.coe_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul]
    simpa using finId_mul (int_mem_finId_one c.2) hx

theorem idem_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {e : AE D} {Q : Formalism.L2.DIV.Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt e Q) {a : D.host.E} (ha : a ∈ 𝔠)
    (hv : Valued.v (algebraMap D.host.E (Kw Q) a) = 1) : toEAf D e ∈ finId 𝔠 := by
  have ha0 : a ≠ 0 := fun h => by rw [h, map_zero, map_zero] at hv; exact zero_ne_one hv
  obtain ⟨h1, h2⟩ := GlobalTheory.StdFrames.cpt_of_isIdemAt he
  have hu : toEAf D e * (a⁻¹ ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    refine (GlobalTheory.StdFrames.mem_OA_iff _).2 fun Q' => ?_
    rw [map_mul, GlobalTheory.FunObj.Comparison₂.cpt_tmul]
    by_cases hQ : Q' = Q
    · subst hQ
      rw [h1, one_mul, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, hv, inv_one]
    · rw [h2 Q' hQ, zero_mul]
      exact zero_mem _
  have e1 : toEAf D e = (toEAf D e * (a⁻¹ ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F))) *
      (a ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) := by
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ ha0, one_mul,
      Algebra.TensorProduct.one_def.symm, mul_one]
  rw [e1]
  simpa using finId_mul (int_mem_finId_one hu) (tmul_one_mem_finId ha)

theorem toEAf_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : AE D} (hx : x ∈ complId 𝔠) :
    toEAf D x ∈ finId 𝔠 := ⟨x, hx, rfl⟩

theorem ring_key {R : Type*} [CommRing R] (e c : R) : c = e * (e * c) + ((1 + e) * (1 - e)) * c := by ring

theorem mem_complId_of_finId {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {c : AE D} (hc : c ∈ complId 𝔞)
    (h : toEAf D c ∈ finId 𝔟) : c ∈ complId 𝔟 := by
  obtain ⟨z, hz, hze⟩ := h
  have hze' : toEAf D z = toEAf D c := hze
  have hzc : z = c := GlobalTheory.DepthFix.ext_cpt (by rw [infPart_of_mem hz, infPart_of_mem hc])
    fun Q => by rw [hze']
  exact hzc ▸ hz

theorem core {𝔞 𝔟 𝔪 𝔡 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hid : 𝔪 * 𝔡 = 𝔞 * 𝔟) {e c : EAf D}
    (he : e ∈ finId 𝔞) (hec : e * c ∈ finId 𝔟) (hm : (1 + e) * (1 - e) ∈ finId 𝔪) (hc : c ∈ finId 𝔡) :
    c ∈ finId (𝔞 * 𝔟) := by
  have h3 := finId_mul hm hc
  rw [hid] at h3
  have h4 := add_mem (finId_mul he hec) h3
  rwa [← ring_key e c] at h4

theorem ideal_key {M A B : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hM : M ≠ 0) :
    M * (A * (B * M⁻¹)) = A * B := by
  calc _ = A * B * (M * M⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hM, mul_one]

theorem mem_complId_AA_AAbar : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 →
    ∀ {sc : Consts} (G : GridData L sc) (c : AE D), c ∈ complId (D.host.AA * G.pl.stAbar sc) →
    (∀ e, IsIdemSum e G.pl.W0 → e * c ∈ complId D.host.AAbar) → c ∈ complId (D.host.AA * D.host.AAbar) := by
  classical
  intro D hq T L μ0 hL sc G c hc hec
  obtain ⟨e, he⟩ := GlobalTheory.GridIdem.exists_idempotentSum_auxiliaryPlaces D T L G.pl
  have h1 := hec e he
  obtain ⟨-, heO, t, ht, hte⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props e G.pl.W0
    (fun Q => G.pl.depth sc (Q.under (𝓞 D.host.F))) he
  have hprod : (∏ Q ∈ G.pl.W0, Q.asIdeal ^ G.pl.depth sc (Q.under (𝓞 D.host.F))) = G.pl.modul sc := by
    unfold Places.W0 Places.modul
    rw [Finset.prod_image fun v hv v' hv' h =>
      (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))]
    exact Finset.prod_congr rfl fun v hv => by rw [G.pl.under_w hv]
  rw [hprod] at ht

  have heA : toEAf D e ∈ finId D.host.AA := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := id he

    rw [show toEAf D (∑ Q ∈ G.pl.W0, es Q) = ∑ Q ∈ G.pl.W0, toEAf D (es Q) from
    map_sum (toEAf D).toAddMonoidHom (fun Q => es Q) G.pl.W0]
    refine sum_mem fun Q hQ => ?_
    obtain ⟨a, ha, hv⟩ := GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hq hL G Q hQ
    exact idem_mem_finId (hes Q hQ) ha hv

  have ht2 : ((⟨1 + toEAf D e, add_mem (one_mem _) heO⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * t) ∈
      Formalism.L2.DIV.idS D.host.F (G.pl.modul sc) := Ideal.mul_mem_left _ _ ht
  have hM : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hid : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
      (D.host.AA * G.pl.stAbar sc) = D.host.AA * D.host.AAbar := ideal_key hM
  have hm := idS_mem_finId _ ht2
  rw [Subring.coe_mul, hte] at hm
  have h1f := toEAf_mem_finId h1
  rw [RingHom.map_mul] at h1f
  exact mem_complId_of_finId hc (core hid heA h1f hm (toEAf_mem_finId hc))

end GlobalTheory.XCharComb
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FirstRowTermLaw

theorem law_gen {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (ht : t ∈ U) {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ}
    (hτ : S.IsExpansion t Φ β τ) (k : FinPt G (.grid 0 D.R.m)) (lam : locPl G t → ℂ)
    (hlam : ∀ w : locPl G t, (locGrid G t w).pathAct .one (GlobalTheory.SplitFlip.oppositePath D.R.m)
      (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (Tflip W S.B t Φ w) = lam w • Tflip W S.B t Φ w)
    (s : ℂ) (hs : s * ∏ w, lam w = ∏ w : locPl G t, (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (.ex 0 D.R.m))
    (xs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
    (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    s * (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) := by
  obtain ⟨e, he, hsupp, hexp⟩ := hτ
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  by_cases hh : (∀ j, IsHalf e (xs j)) ∧ ∀ i, IsHalf e (ys i)
  · have hh' : ∀ i, IsHalf e (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) := by
      intro i
      by_cases h : i = (GlobalTheory.FirstRowVertex.firstIx D)
      · subst h; rw [Function.update_self]; exact (GlobalTheory.SchrMove.isHalf_actO_iff _ _ _).2 (hh.2 _)
      · rw [Function.update_of_ne h]; exact hh.2 i
    rw [hexp xs _ hh.1 hh', hexp xs ys hh.1 hh.2]
    have hloc : ∀ w : locPl G t, (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (.ex 0 D.R.m) *
        (S.term t Φ β w).datum (S.colAt t w xs) (S.rowAt t w (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))))) =
        lam w * (S.term t Φ β w).datum (S.colAt t w xs) (S.rowAt t w ys) := by
      intro w
      rw [GlobalTheory.T.firstRowArgument_conjugateMove_left_mul_inv_component S ht w w.2 k ys]
      exact GlobalTheory.FirstRowTermLaw.datum_law (Γ := locGrid G t w) one_le_sLen hm _ _ _ _ _ _ _ _ (hlam w) _ _
    have hprod := Finset.prod_congr rfl fun w (_ : w ∈ Finset.univ) => hloc w
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hprod
    exact key_cancel _ _ _ _ _ (Finset.prod_ne_zero_iff.2 fun w _ => edgeFactor_ne_zero _ _ _) hs hprod
  · have hz : ∀ d ∈ τ.support, (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) = 0 ∧
        (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) = 0 := by
      intro d hd
      have hX : ∀ j, (d.1 j).fn (xs j) ≠ 0 → IsHalf e (xs j) := fun j h => ((hsupp d hd).1 j).2.1 ▸ (d.1 j).sb.1 _ h
      have hY : ∀ i y, (d.2 i).fn y ≠ 0 → IsHalf e y := fun i y h => ((hsupp d hd).2 i).2.1 ▸ (d.2 i).sb.1 _ h
      by_cases hx : ∀ j, IsHalf e (xs j)
      · obtain ⟨i, hi⟩ : ∃ i, ¬ IsHalf e (ys i) := by
          by_contra hc; push_neg at hc; exact hh ⟨hx, hc⟩
        have h1 : (d.2 i).fn (ys i) = 0 := by by_contra h; exact hi (hY i _ h)
        have h2 : (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) = 0 := by
          by_contra h
          have h' := hY i _ h
          by_cases hi0 : i = (GlobalTheory.FirstRowVertex.firstIx D)
          · subst hi0; rw [Function.update_self] at h'; exact hi ((GlobalTheory.SchrMove.isHalf_actO_iff _ _ _).1 h')
          · rw [Function.update_of_ne hi0] at h'; exact hi h'
        exact ⟨by rw [show (∏ i, (d.2 i).fn (ys i)) = 0 from Finset.prod_eq_zero (Finset.mem_univ i) h1, mul_zero],
          by rw [show (∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i)) = 0 from
            Finset.prod_eq_zero (Finset.mem_univ i) h2, mul_zero]⟩
      · push_neg at hx
        obtain ⟨j, hj⟩ := hx
        have h1 : (d.1 j).fn (xs j) = 0 := by by_contra h; exact hj (hX j h)
        rw [show (∏ j, (d.1 j).fn (xs j)) = 0 from Finset.prod_eq_zero (Finset.mem_univ j) h1]
        simp only [zero_mul, and_self]
    simp only [Finsupp.sum]
    rw [Finset.sum_eq_zero fun d hd => by rw [mul_assoc, (hz d hd).2, mul_zero],
      Finset.sum_eq_zero fun d hd => by rw [mul_assoc, (hz d hd).1, mul_zero], mul_zero]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw


end GlobalTheory.FirstRowTermLaw

end
end
