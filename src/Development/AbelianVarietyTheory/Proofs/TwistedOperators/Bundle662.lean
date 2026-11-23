module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle479
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle526
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle530
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle653
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle490
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle656
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle365
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle657
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

noncomputable section

namespace GlobalTheory.ChainColRead



theorem givenFn_eq_extDat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ → L.Pg ⊆ G.pl.W0 → ∀ (t : T) (j : ℕ), j + 1 < D.R.m → ∀ (Φ : G.Datum) (e e' : AE D), IsIdemSum e (locPl G t) → IsIdemSum e' (L.Pg ∪ L.Q t) → (∀ w ∈ locPl G t, w ∉ L.Pg ∪ L.Q t → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ x : WO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)), GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) x = extDat e e' (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True) (stepDat (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (colDat L t j) (L.chi (j + 1)) (L.xiR t) (L.Q t) e') x := by
  intro D T L sc G B μ₀ hL hPg t j hj1 Φ e e' he he' hAA x
  have hj : j < D.R.m := by omega
  have hsub : L.Pg ∪ L.Q t ⊆ locPl G t := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (hPg h)
    · exact Finset.mem_union_right _ h
  obtain ⟨he₁, -⟩ := GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal he he' hsub
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he'
  have h2 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  obtain ⟨-, c1, c0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he'
  obtain ⟨-, d1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁
  have ha := GlobalTheory.FlipTop.rank_col G hj.le
  have hb := GlobalTheory.FlipTop.rank_col G hj
  unfold GlobalTheory.FlipStart.givenFn extDat
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg fun h => hx h.1]
  rw [if_pos hx]
  set N := GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) with hN
  have hfr : ∀ a : AE D, GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((x.map (a * ·)).map (toEAf D)) = toEAf D a • N := by
    intro a
    rw [hN, ← GlobalTheory.FunObj.Comparison₂.fr_smul]
    congr 1
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul]
  have hcomp : ∀ (a : AE D) (w : Pl D.host.E), cpt (D := D) w (toEAf D a) = 1 →
      (GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((x.map (a * ·)).map (toEAf D))).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by
    intro a w hw
    rw [hfr]
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul, hw]
  have hsubm : ∀ w : Pl D.host.E, GlobalTheory.StepData.IntM ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb)
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) ↔ GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := fun w =>
    ⟨fun h i l => by simpa using h ((GlobalTheory.FunObj.Comparison₂.ixOf G t w hb).symm i) ((GlobalTheory.FunObj.Comparison₂.ixOf G t w ha).symm l),
      fun h i l => h _ _⟩
  have hR : ∀ w, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) x) =
      stepFn L t w j ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    intro w
    have hla : locArg B t w (.down t 0 j) x = B.coord t w (X := (0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩
        ⟨Nat.zero_le _, hj.le⟩ ((x.map (toEAf D)).map (cpt (D := D) w)) := by
      rw [Matrix.map_map]
      exact dif_pos ⟨Nat.zero_le _, hj⟩
    rw [hla]
    exact GlobalTheory.FunObj.Comparison₂.givenDatum_theta_coord B t w Φ hj ha hb (x.map (toEAf D))
  rw [Finset.prod_congr rfl fun w _ => hR w, ← Finset.prod_sdiff hsub]
  have hout : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), stepFn L t w j ((N.map (cpt (D := D) w)).submatrix
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) =
      if GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) then 1 else 0 := by
    intro w hw
    obtain ⟨-, hw2⟩ := Finset.mem_sdiff.1 hw
    have hP : w ∉ L.Pg := fun h => hw2 (Finset.mem_union_left _ h)
    have hQ : w ∉ L.Q t := fun h => hw2 (Finset.mem_union_right _ h)
    unfold stepFn
    rw [if_neg hP, if_neg hQ, Set.indicator_apply]
    exact if_congr (hsubm w) rfl rfl
  rw [Finset.prod_congr rfl hout, Finset.prod_boole]

  have hx1 : IsHalf (e - e') (x.map ((e - e') * ·)) := fun p q => by
    simp only [Matrix.map_apply, ← mul_assoc, h2]
  have hS : IsSelfDualC (G.pS (.mu t 0 j)) (G.latS (.mu t 0 j)) := (colY_isV D T L μ₀ hL j hj.le).sd
  have hT : IsSelfDualC (G.pT (.mu t 0 j)) (G.latT (.mu t 0 j)) := (colY_isV D T L μ₀ hL (j + 1) hj).sd
  have hAA' : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := fun w hw =>
    hAA w (Finset.mem_sdiff.1 hw).1 (Finset.mem_sdiff.1 hw).2
  have hlat := GlobalTheory.T.mem_completedHomLattice_iff_integral_on_unit_half hS hT (B.isFrame_β hL (Nat.zero_le _) hj.le) (B.isFrame_β hL (Nat.zero_le _) hj) he₁ hAA'
    (x.map ((e - e') * ·)) hx1
  have k1 : x.map ((e - e') * ·) ∈ latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _)
      (G.latT (.mu t 0 j) : Set _) (fun _ => True) ↔
      ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    rw [hlat]
    exact forall₂_congr fun w hw => by rw [hcomp _ w (d1 w hw)]

  have hint : IsIntM (toEAf D e' • N) ↔ ∀ w ∈ L.Pg ∪ L.Q t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    constructor
    · intro h w hw i l
      have := (mem_OA_iff _).1 (h i l) w
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, c1 w hw, one_mul] at this
      exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.2 this
    · intro h i l
      refine (mem_OA_iff _).2 fun w => ?_
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      by_cases hw : w ∈ L.Pg ∪ L.Q t
      · rw [c1 w hw, one_mul]
        exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.1 (h w hw i l)
      · rw [c0 w hw, zero_mul]
        exact zero_mem _
  have hx0 : IsHalf e' (x.map (e' * ·)) := fun p q => by
    simp only [Matrix.map_apply, ← mul_assoc, h1]
  have hfrO : frMapO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (x.map (e' * ·)) =
      toEAf D e' • N := hfr e'
  have k0 : stepDat (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (colDat L t j)
      (L.chi (j + 1)) (L.xiR t) (L.Q t) e' (x.map (e' * ·)) = ∏ w ∈ L.Pg ∪ L.Q t, stepFn L t w j
      ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    unfold stepDat
    rw [hfrO]
    by_cases H : ∀ w ∈ L.Pg ∪ L.Q t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
    · rw [if_pos ⟨hx0, hint.2 H⟩]
      have key := GlobalTheory.FunObj.Comparison₂.omega_eq_prod_stepFn G t hL hj ha hb (r_le_colY L j) (toEAf D e' • N) (hint.2 H)
      refine key.trans (Finset.prod_congr rfl fun w hw => ?_)
      have e1 : (toEAf D e' • N).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by
        rw [← hfr e']; exact hcomp e' w (c1 w hw)
      rw [e1]
    · rw [if_neg fun h => H (hint.1 h.2)]
      push_neg at H
      obtain ⟨w, hw, hn⟩ := H
      refine (Finset.prod_eq_zero hw ?_).symm
      by_contra h0
      exact hn ((hsubm w).1 (GlobalTheory.FunObj.LocTest.intM_of_stepFn t w j h0))
  rw [k0]
  by_cases hl : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
  · rw [if_pos hl, one_mul, if_pos ⟨hx, k1.2 hl⟩]
  · rw [if_neg hl, zero_mul, if_neg fun h => hl (k1.1 h.2)]

end GlobalTheory.ChainColRead

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.vacuum_self_dual_lattices : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F F' : WO S T → ℂ,
    GlobalTheory.MovedAlg.IsAlgComb ψ S T v F → GlobalTheory.MovedAlg.IsAlgComb ψ S T v F' → IsAlgebraic ℚ (GlobalTheory.RawLift.thetaIP μ 𝓕 F F') := by
  first | exact @GlobalTheory.AlgPair.thetaIP_algComb | exact GlobalTheory.AlgPair.thetaIP_algComb | (intros; apply GlobalTheory.AlgPair.thetaIP_algComb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.isThetaAt_halfExtensionLatticeIndicatorFn : ∀ {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {f₀ Φ f : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → (∀ t y, IsHalf (e₀ + e₁) t → IsHalf (cA D e₀) y → B t y = B (e₀ • t) y) → (∃ T, IsPlaceModel ψ B hs (e₀ + e₁) Λ 1 f₀ T) → IsThetaAt ψ B hs e₀ Λ 1 f₀ Φ f → IsThetaAt ψ B hs (e₀ + e₁) Λ 1 f₀ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) f := by
  first | exact @GlobalTheory.CosetRow.isThetaAt_extFn | exact GlobalTheory.CosetRow.isThetaAt_extFn | (intros; apply GlobalTheory.CosetRow.isThetaAt_extFn <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FibreAtTau

variable {D : D7}

def atPHom {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : GA D V →* GA D V where
  toFun x := atTau θ V τ (cmp θ τ x)
  map_one' := by
    show atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) 1) = 1
    rw [GlobalTheory.PointAtPlaceHom.infMat_one]
    exact GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ
  map_mul' x y := by
    show atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) (x * y)) = _
    rw [GlobalTheory.PointAtPlaceHom.infMat_mul]
    exact GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ)
      (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V y τ)

theorem atPHom_spec {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) (x : GA D V) :
    IsAtTau θ V τ (cmp θ τ x) (atPHom hθ V τ x) :=
  GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ)


open Classical in
theorem matHom_atPHom {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D) (τ : D.what₂.Tau) (x : GA D V) (i j : Fin V.rank) :
    ((matHom V (atPHom hθ V τ x)).1 - 1) i j = σ (Pi.single τ 1) * ((matHom V x).1 - 1) i j := by
  have hs := atPHom_spec hθ V τ x
  have inf1 : ∀ (y : GA D V) (ρ : D.what₂.Tau),
      θ ρ (infPart D (((matHom V y).1 - 1) i j)) = infMat D.sp.cm.sig V.gram (θ ρ) y i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := by
    intro y ρ
    have e1 : θ ρ (infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := congrFun (congrFun (GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)) i) j
    rw [Matrix.sub_apply, RingHom.map_sub, RingHom.map_sub, e1]
    rfl
  rw [← sub_eq_zero]
  refine hσ.ext _ ?_ fun ρ => ?_
  · have a2 : (finHom V (atPHom hθ V τ x)).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val hs.1
    have e : finPart D ((matHom V (atPHom hθ V τ x)).1 i j) = finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
      congrFun (congrFun a2 i) j
    rw [Matrix.sub_apply, RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, e, hσ.fin, zero_mul, sub_self, sub_zero]
  · let π : AE D →+* ℂ := (θ ρ).comp (infPart D)
    have hπ : ∀ z, θ ρ (infPart D z) = π z := fun _ => rfl
    have hc : π (σ (Pi.single τ 1)) = (Pi.single τ 1 : D.what₂.Tau → ℂ) ρ := hσ.comp (Pi.single τ 1) ρ
    have i1 : ∀ y : GA D V, π (((matHom V y).1 - 1) i j) =
        infMat D.sp.cm.sig V.gram (θ ρ) y i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := fun y => inf1 y ρ
    rw [hπ, RingHom.map_sub π, RingHom.map_mul π, i1, i1, hc]
    by_cases c : ρ = τ
    · subst c
      rw [hs.2.1, Pi.single_eq_same, one_mul, sub_self]
    · rw [hs.2.2 ρ c, Pi.single_eq_of_ne c, zero_mul, sub_self, sub_zero]

theorem mul_eq_zero_of_entry {n k : ℕ} {A : Type} [CommRing A] {m m' : Matrix (Fin n) (Fin n) A} {e : A}
    (he : ∀ i j, m' i j = e * m i j) {N : Matrix (Fin n) (Fin k) A} (h : m * N = 0) : m' * N = 0 := by
  ext i l
  have := congrFun (congrFun h i) l
  simp only [Matrix.mul_apply, Matrix.zero_apply] at this ⊢
  simp only [he, mul_assoc, ← Finset.mul_sum, this, mul_zero]

theorem entry_mul_eq_zero {n k : ℕ} {A : Type} [CommRing A] {m m' : Matrix (Fin n) (Fin n) A} {e : A}
    (he : ∀ i j, m' i j = e * m i j) {N : Matrix (Fin k) (Fin n) A} (h : N * m = 0) : N * m' = 0 := by
  ext i l
  have := congrFun (congrFun h i) l
  simp only [Matrix.mul_apply, Matrix.zero_apply] at this ⊢
  simp only [he, mul_left_comm _ e, ← Finset.mul_sum, this, mul_zero]

theorem mulVec_of_entry {n k : ℕ} {A : Type} [CommRing A] {m m' : Matrix (Fin n) (Fin n) A} {e : A}
    (he : ∀ i j, m' i j = e * m i j) {N : Matrix (Fin n) (Fin k) A} {y : Fin n → A} {a : Fin k → A}
    (h : m *ᵥ y = N *ᵥ a) : m' *ᵥ y = N *ᵥ fun l => e * a l := by
  funext i
  have := congrFun h i
  simp only [Matrix.mulVec, dotProduct] at this ⊢
  simp only [he, mul_assoc, mul_left_comm _ e, ← Finset.mul_sum, this]

theorem atPHom_mem_NI {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) {h : GA D V} (hh : h ∈ NI V C) : atPHom hθ V τ h ∈ NI V C := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have key : NI V C ≤ (NI V C).comap (atPHom hθ V τ) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    obtain ⟨h1, h2, h3⟩ := hx
    have hm := matHom_atPHom hθ hσ V τ x
    refine Subgroup.subset_closure ⟨mul_eq_zero_of_entry hm h1, entry_mul_eq_zero hm h2, fun y hy => ?_⟩
    obtain ⟨a, ha⟩ := h3 y hy
    exact ⟨_, mulVec_of_entry hm ha⟩
  exact key hh

theorem decomp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ (τ : D.what₂.Tau) (h : NI V C), ∃ p ∈ GlobalTheory.FibreAtTau.atP θ V C τ, ∃ q ∈ GlobalTheory.FibreAtTau.offP θ V C τ, h = p * q := by
  intro D θ hθ V r C _ τ h
  have hs := atPHom_spec hθ V τ (h : GA D V)
  let p : NI V C := ⟨atPHom hθ V τ h, atPHom_mem_NI hθ V C τ h.2⟩
  refine ⟨p, mem_atP.2 ⟨hs.1, hs.2.2⟩, p⁻¹ * h, mem_offP.2 ?_, (mul_inv_cancel_left p h).symm⟩
  show infMat D.sp.cm.sig V.gram (θ τ) ((atPHom hθ V τ h)⁻¹ * h) = 1
  have e : infMat D.sp.cm.sig V.gram (θ τ) (atPHom hθ V τ h) = infMat D.sp.cm.sig V.gram (θ τ) h := hs.2.1
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← e, ← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel,
    GlobalTheory.PointAtPlaceHom.infMat_one]

end GlobalTheory.FibreAtTau

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem coef_factor : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v a : ∀ τ, M.H τ) (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (q : NI V C), q ∈ GlobalTheory.FibreAtTau.offP θ V C τ → ∀ x y : GA D V, ∃ R : ℂ, ∀ p ∈ GlobalTheory.FibreAtTau.atP θ V C τ, coef θ M K v a (x * ((p * q : NI V C) : GA D V) * y) = ⟪v τ, M.rep τ (cmp θ τ x * cmp θ τ (p : GA D V) * cmp θ τ y) (a τ)⟫_ℂ * R := by
  intro D θ _ V S M K v a τ r C q hq x y
  classical
  rw [mem_offP] at hq
  have hcmp : ∀ τ' (g h : GA D V), cmp θ τ' (g * h) = cmp θ τ' g * cmp θ τ' h := fun τ' g h =>
    (GlobalTheory.RowReal.infMatHom V (θ τ')).map_mul g h
  refine ⟨if Lev.finE V (x * (q : GA D V) * y) ∈ K then
      ∏ τ' ∈ Finset.univ.erase τ, ⟪v τ', M.rep τ' (cmp θ τ' (x * (q : GA D V) * y)) (a τ')⟫_ℂ else 0, ?_⟩
  intro p hp
  rw [mem_atP] at hp
  have hfin : Lev.finE V (p : GA D V) = 1 := by
    have h1 : (p : GA D V) ∈ (⊥ : Subgroup (GL (Fin V.rank) (Lev.EAf D))).comap (Lev.finE V) := by
      rw [GlobalTheory.Mass.Levels.comap_finE]
      exact Subgroup.mem_sup_right hp.1
    simpa using h1
  have hF : Lev.finE V (x * ((p * q : NI V C) : GA D V) * y) = Lev.finE V (x * (q : GA D V) * y) := by
    simp only [Subgroup.coe_mul, map_mul, hfin, one_mul]
  simp only [coef, coefR, hF]
  split_ifs with h
  · have e1 : cmp θ τ (x * ((p * q : NI V C) : GA D V) * y) = cmp θ τ x * cmp θ τ (p : GA D V) * cmp θ τ y := by
      rw [Subgroup.coe_mul, hcmp, hcmp, hcmp, hq, mul_one]
    have e2 : ∀ τ' ∈ Finset.univ.erase τ,
        ⟪v τ', M.rep τ' (cmp θ τ' (x * ((p * q : NI V C) : GA D V) * y)) (a τ')⟫_ℂ =
          ⟪v τ', M.rep τ' (cmp θ τ' (x * (q : GA D V) * y)) (a τ')⟫_ℂ := by
      intro τ' hτ'
      have hp' := hp.2 τ' (Finset.ne_of_mem_erase hτ')
      rw [Subgroup.coe_mul, hcmp, hcmp, hcmp, hcmp, hcmp, hp', one_mul]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), e1, Finset.prod_congr rfl e2]
  · simp

end GlobalTheory.FibreAtTau
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem comm_and_inf_trivial : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau), (∀ p ∈ GlobalTheory.FibreAtTau.atP θ V C τ, ∀ q ∈ GlobalTheory.FibreAtTau.offP θ V C τ, p * q = q * p) ∧ ∀ h, h ∈ GlobalTheory.FibreAtTau.atP θ V C τ → h ∈ GlobalTheory.FibreAtTau.offP θ V C τ → h = 1 := by
  intro D θ hθ V r C τ
  have hc : ∀ (ρ : D.what₂.Tau) (x : GA D V), cmp θ ρ x = GlobalTheory.RowReal.infMatHom V (θ ρ) x := fun _ _ => rfl
  have one_spec : GlobalTheory.RowReal.IsRealAll θ V 1 (1 : GA D V) :=
    ⟨one_mem _, fun _ => GlobalTheory.PointAtPlaceHom.infMat_one V _⟩
  refine ⟨fun p hp q hq => ?_, fun h hp hq => ?_⟩
  · rw [mem_atP] at hp
    rw [mem_offP] at hq
    obtain ⟨hpf, hpc⟩ := hp
    have hpf' : finHom V (p : GA D V) = 1 := hpf
    set c : GA D V := (p : GA D V) * q * (p : GA D V)⁻¹ * (q : GA D V)⁻¹ with hcdef
    have hcR : GlobalTheory.RowReal.IsRealAll θ V 1 c := by
      refine ⟨?_, fun ρ => ?_⟩
      · show finHom V c = 1
        simp only [hcdef, map_mul, map_inv, hpf', one_mul, inv_one, mul_one, mul_inv_cancel]
      · show GlobalTheory.RowReal.infMatHom V (θ ρ) c = 1
        by_cases hρ : ρ = τ
        · have hinv : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x * GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x => by rw [← map_mul, mul_inv_cancel, map_one]
          have hinv1 : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x = 1 → GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x hx => by have := hinv x; rwa [hx, Matrix.one_mul] at this
          subst hρ
          have hq' : GlobalTheory.RowReal.infMatHom V (θ ρ) (q : GA D V) = 1 := by rw [← hc]; exact hq
          rw [hcdef, map_mul, map_mul, map_mul, hq', hinv1 _ hq', Matrix.mul_one, Matrix.mul_one, hinv]
        · have hinv : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x * GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x => by rw [← map_mul, mul_inv_cancel, map_one]
          have hinv1 : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x = 1 → GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x hx => by have := hinv x; rwa [hx, Matrix.one_mul] at this
          have hp' : GlobalTheory.RowReal.infMatHom V (θ ρ) (p : GA D V) = 1 := by rw [← hc]; exact hpc ρ hρ
          rw [hcdef, map_mul, map_mul, map_mul, hp', hinv1 _ hp', Matrix.one_mul, Matrix.mul_one, hinv]
    have e : c = 1 := hcR.unique hθ one_spec
    apply Subtype.ext
    have e2 : (p : GA D V) * q * (p : GA D V)⁻¹ * (q : GA D V)⁻¹ = 1 := e
    have e3 : (p : GA D V) * q = (q : GA D V) * p := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at e2
      exact e2
    simpa using e3
  · rw [mem_atP] at hp
    rw [mem_offP] at hq
    apply Subtype.ext
    have hR : GlobalTheory.RowReal.IsRealAll θ V 1 (h : GA D V) := by
      refine ⟨hp.1, fun ρ => ?_⟩
      by_cases hρ : ρ = τ
      · subst hρ; exact hq
      · exact hp.2 ρ hρ
    exact hR.unique hθ one_spec

end GlobalTheory.FibreAtTau
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem isClosed_cmp_eq_one {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau) :
    IsClosed {p : NI V C | cmp θ τ (p : GA D V) = 1} :=
  isClosed_eq ((GlobalTheory.Cusp.KinfCompact.continuous_realMat hθ V τ).comp continuous_subtype_val)
    continuous_const

theorem isClosed_atP_and_isClosed_offP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau), IsClosed (GlobalTheory.FibreAtTau.atP θ V C τ : Set (NI V C)) ∧ IsClosed (GlobalTheory.FibreAtTau.offP θ V C τ : Set (NI V C)) := by
  intro D θ hθ V r C τ
  constructor
  · have e : (atP θ V C τ : Set (NI V C)) = (Subtype.val ⁻¹' (GinfC V : Set (GA D V))) ∩
        ⋂ (τ' : D.what₂.Tau) (_ : τ' ≠ τ), {p : NI V C | cmp θ τ' (p : GA D V) = 1} := by
      ext p
      simp only [SetLike.mem_coe, mem_atP, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [e]
    exact ((GlobalTheory.Cusp.KinfCompact.isClosed_realPts V).preimage continuous_subtype_val).inter
      (isClosed_iInter fun τ' => isClosed_iInter fun _ => isClosed_cmp_eq_one hθ V C τ')
  · have e : (offP θ V C τ : Set (NI V C)) = {p : NI V C | cmp θ τ (p : GA D V) = 1} := by
      ext p
      simp only [SetLike.mem_coe, mem_offP, Set.mem_ofPred_eq]
    rw [e]
    exact isClosed_cmp_eq_one hθ V C τ

end GlobalTheory.FibreAtTau
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_perfectPairing_coefficientSpace_tensorModel : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsInfFam θ → GlobalTheory.DefLift.AllPlus M → c.Is → IsDualPair θ M c pr → ∃ E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ), ∀ (u : UG D.what₂.Tau V.rank) (w : c.W), E (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = E w ∘ₗ PiTensorProduct.map (fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) := by
  first | exact @GlobalTheory.CoefPairTens.pairEquiv_realAll | exact GlobalTheory.CoefPairTens.pairEquiv_realAll | (intros; apply GlobalTheory.CoefPairTens.pairEquiv_realAll <;> assumption)
end
