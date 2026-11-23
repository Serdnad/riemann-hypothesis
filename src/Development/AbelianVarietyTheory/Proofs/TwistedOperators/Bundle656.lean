module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle490
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle526
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorSmallCosetHalfIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle649
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle530
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle647
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle479
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

noncomputable section

namespace GlobalTheory.FlipStart.ColSB

open GlobalTheory.FunObj.Comparison₂

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem stepFn_congr_red' (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) {j : ℕ} (hj : j < D.R.m) (w : Pl D.host.E)
    {a b : ℕ} (ha : a = D.R.r + j * D.R.t) (hb : b = D.R.r + (j + 1) * D.R.t)
    (N N' : Matrix (Fin b) (Fin a) (OA D)) (h : N.map (resS D.host.F w) = N'.map (resS D.host.F w)) :
    stepFn L t w j ((N.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) =
      stepFn L t w j ((N'.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
  by_cases hw : w ∈ GlobalTheory.FlipTop.topPl L t
  · exact GlobalTheory.FlipTop.stepFn_congr_red G hL t hj hw ha hb N N' h
  · have hP : w ∉ L.Pg := fun h => hw (Finset.mem_union_left _ h)
    have hQ : w ∉ L.Q t := fun h => hw (Finset.mem_union_right _ h)
    have hI : ∀ M : Matrix (Fin b) (Fin a) (OA D),
        GlobalTheory.StepData.IntM ((M.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
      intro M i l
      have h1 := (mem_OA_iff _).1 (M (ixOf G t w hb i) (ixOf G t w ha l)).2 w
      show cptO w (M (ixOf G t w hb i) (ixOf G t w ha l)) ∈ _
      rw [cptO_apply]
      exact (vEq w).le_one_iff_le_one.2 h1
    unfold stepFn
    simp only [if_neg hP, if_neg hQ, Set.indicator_apply, Set.mem_setOf_eq, if_pos (hI N), if_pos (hI N'), Pi.one_apply]


open Classical in
def colFn {G : GridData L sc} (B : Frames G) (t : T) (e : AE D) (j : ℕ) (ha : (G.V (.grid 0 j)).rank = D.R.r + j * D.R.t)
    (hb : (G.V (.grid 0 (j + 1))).rank = D.R.r + (j + 1) * D.R.t)
    (x : Mx D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank) : ℂ :=
  if IsHalf e x ∧ IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) then
    ∏ w ∈ locPl G t, stepFn L t w j
      (((fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w)).submatrix (ixOf G t w hb) (ixOf G t w ha))
  else 0



theorem isSBHalf_colFn (G : GridData L sc) (B : Frames G) {μ₀ : T} (hL : L.Is μ₀) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (j : ℕ) (hj : j < D.R.m) :
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _)
      fun _ => True) (colFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) := by
  classical
  have hFS : IsFrame (B.β 0 j) (G.Λ (.grid 0 j)) := B.isFrame_β hL (Nat.zero_le _) hj.le
  have hFT : IsFrame (B.β 0 (j + 1)) (G.Λ (.grid 0 (j + 1))) := B.isFrame_β hL (Nat.zero_le _) hj
  obtain ⟨a, ha, h1⟩ := WeilOver.exists_hom_le (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 j) ⟨Nat.zero_le _, hj.le⟩).sd)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 (j + 1)) ⟨Nat.zero_le _, hj⟩).sd)
  obtain ⟨b, hb, h2⟩ := WeilOver.exists_le_hom (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFS) (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFT)
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  set 𝔪 : Ideal (𝓞 D.host.E) := ∏ w ∈ locPl G t, w.asIdeal ^ 1 with h𝔪
  have hN : 0 < Ideal.absNorm 𝔪 :=
    Nat.pos_of_ne_zero fun h => CosSB.prod_pow_ne_bot (locPl G t) 1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hle : ∀ w ∈ locPl G t, 𝔪 ≤ w.asIdeal ^ 1 := fun w hw =>
    Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ 1) hw)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = a * (b * Ideal.absNorm 𝔪) := ⟨_, rfl⟩
  refine ⟨fun x hx => ?_, K, by rw [hK]; positivity, fun u hu hh x => ?_, fun x hx => ?_⟩
  · by_contra h
    exact hx (by unfold colFn; rw [if_neg fun H => h H.1])
  · have hk : K • u ∈ hatMx (𝔪 • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      have := nsmul_mem (CosSB.nsmul_mem_hatMx h2 𝔪 hu) a
      rwa [smul_smul, ← hK] at this
    have hk2 := ((mem_hatMx_iff hFS hFT 𝔪 _).1 hk).2
    have hXYZ : fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) =
        fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) + fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) := by
      have hm : (x + K • u).map (toEAf D) = x.map (toEAf D) + (K • u).map (toEAf D) := by
        ext i l
        exact (toEAf D).map_add _ _
      rw [hm, fr_add]
    have hZ : ∀ i l, fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) i l ∈ OA D := fun i l => by
      obtain ⟨s, -, hs⟩ := hk2 i l
      rw [← hs]
      exact s.2
    have hint : IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))) ↔
        IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      refine forall₂_congr fun i l => ?_
      rw [hXYZ, Matrix.add_apply]
      exact ⟨fun h => by simpa using sub_mem h (hZ i l), fun h => add_mem h (hZ i l)⟩
    unfold colFn
    split_ifs with H1 H2 H2
    · refine Finset.prod_congr rfl fun w hw => ?_
      let NX : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H1.2 i l⟩
      let NY : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H2.2 i l⟩
      have eX : (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))).map (cpt (D := D) w) = NX.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NX i l)).symm
      have eY : (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w) = NY.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NY i l)).symm
      rw [eX, eY]
      refine stepFn_congr_red' G hL t hj w _ _ NX NY (Matrix.ext fun i l => ?_)
      rw [Matrix.map_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, (isRed w).ker, cptO_apply]
      obtain ⟨s, hs, hs'⟩ := hk2 i l
      have e3 : ((NX i l - NY i l : OA D) : EAf D) = s.1 := by
        rw [hs', AddSubgroupClass.coe_sub]
        change fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) i l -
          fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) i l = _
        rw [hXYZ, Matrix.add_apply, add_sub_cancel_left]
      rw [e3]
      exact (vEq w).lt_one_iff_lt_one.2 ((v_lt_one_iff _).2 (v_le_of_mem_idS (hle w hw) hs))
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).1 H1.1, hint.1 H1.2⟩ H2
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).2 H2.1, hint.2 H2.2⟩ H1
    · rfl
  · obtain ⟨hth, hti⟩ : IsHalf e x ∧ IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      by_contra h
      exact hx (by unfold colFn; rw [if_neg h])
    have hmem : x ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      refine (mem_hatMx_iff hFS hFT ⊤ _).2 ⟨fun i l => ?_, fun i l => ⟨⟨_, hti i l⟩, ?_, rfl⟩⟩
      · rw [← hth i l, map_mul, e0, zero_mul]
      · rw [idS, Ideal.map_top]
        exact Submodule.mem_top
    have := nsmul_mem (CosSB.nsmul_mem_latO h1 ⊤ hmem) (b * Ideal.absNorm 𝔪)
    rwa [smul_smul, mul_comm (b * Ideal.absNorm 𝔪) a, ← hK] at this


open Classical in
theorem givenFn_down_eq_colFn (G : GridData L sc) (B : Frames G) {μ₀ : T} (hL : L.Is μ₀) (t : T) (j : ℕ) (hj : j < D.R.m)
    (Φ : G.Datum) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) = colFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj) := by
  have ha := GlobalTheory.FlipTop.rank_col G hj.le
  have hb := GlobalTheory.FlipTop.rank_col G hj
  obtain ⟨-, c1, c0⟩ := cpt_idemSum he
  funext x
  set N := fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) with hN
  have hsubm : ∀ w : Pl D.host.E, GlobalTheory.StepData.IntM ((N.map (cpt (D := D) w)).submatrix (ixOf G t w hb)
      (ixOf G t w ha)) ↔ GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := fun w =>
    ⟨fun h i l => by simpa using h ((ixOf G t w hb).symm i) ((ixOf G t w ha).symm l), fun h i l => h _ _⟩
  have hR : ∀ w, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) x) =
      stepFn L t w j ((N.map (cpt (D := D) w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
    intro w
    have hla : locArg B t w (.down t 0 j) x = B.coord t w (X := (0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩
        ⟨Nat.zero_le _, hj.le⟩ ((x.map (toEAf D)).map (cpt (D := D) w)) := by
      rw [Matrix.map_map]
      exact dif_pos ⟨Nat.zero_le _, hj⟩
    rw [hla]
    exact givenDatum_theta_coord B t w Φ hj ha hb (x.map (toEAf D))
  unfold GlobalTheory.FlipStart.givenFn colFn
  rw [Finset.prod_congr rfl fun w _ => hR w]
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg fun h => hx h.1]
  have hex : e • x = x := Matrix.ext fun p q => by rw [Matrix.smul_apply, smul_eq_mul]; exact hx p q
  have hNe : N = toEAf D e • N := by
    rw [hN, ← fr_smul]
    congr 1
    conv_lhs => rw [← hex]
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul]
  have hint : IsIntM N ↔ ∀ w ∈ locPl G t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    constructor
    · intro h w hw i l
      exact (vEq w).le_one_iff_le_one.2 ((mem_OA_iff _).1 (h i l) w)
    · intro h i l
      refine (mem_OA_iff _).2 fun w => ?_
      by_cases hw : w ∈ locPl G t
      · exact (vEq w).le_one_iff_le_one.1 (h w hw i l)
      · rw [hNe, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, c0 w hw, zero_mul]
        simp
  rw [if_pos hx]
  by_cases H : ∀ w ∈ locPl G t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
  · rw [if_pos ⟨hx, hint.2 H⟩]
  · rw [if_neg fun h => H (hint.1 h.2)]
    push_neg at H
    obtain ⟨w, hw, hn⟩ := H
    refine Finset.prod_eq_zero hw ?_
    by_contra h0
    exact hn ((hsubm w).1 (GlobalTheory.FunObj.LocTest.intM_of_stepFn t w j h0))

theorem isSBHalf_givenFn_down : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T) (j : ℕ), j < D.R.m → ∀ (Φ : G.Datum) (e : AE D), IsIdemSum e (locPl G t) →
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _)
      fun _ => True) (GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j)) := by
  intro D T L sc G B μ₀ hL t j hj Φ e he
  rw [givenFn_down_eq_colFn G B hL t j hj Φ he]
  exact isSBHalf_colFn G B hL t he j hj

end GlobalTheory.FlipStart.ColSB
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.AlgPair

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem alg_star {a : ℂ} (ha : a ∈ algebraicClosure ℚ ℂ) : star a ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff] at ha ⊢
  exact ha.algHom ((Complex.conjAe.restrictScalars ℚ).toAlgHom)

theorem fin_neg {x : WO S T} (hx : x.map (infPart D) = 0) : (-x).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hx i) j
  simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.zero_apply] at h ⊢
  rw [RingHom.map_neg, h, neg_zero]

theorem fin_add {x y : WO S T} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + y).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hx i) j
  have h' := congrFun (congrFun hy i) j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at h h' ⊢
  rw [RingHom.map_add (f := _), h, h', add_zero]

variable {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem thetaInner_zero_left (G : WO S T → ℂ) : GlobalTheory.RawLift.thetaIP μ 𝓕 0 G = 0 := by
  have h := GlobalTheory.RawLift.thetaInner_smul_left μ 𝓕 0 0 G
  simpa using h

theorem thetaInner_zero_right (G : WO S T → ℂ) : GlobalTheory.RawLift.thetaIP μ 𝓕 G 0 = 0 := by
  have h := GlobalTheory.RawLift.thetaInner_smul_right μ 𝓕 0 G 0
  simpa using h

theorem sum_left (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {G : WO S T → ℂ}
    (hG : IsThetaFunO ψ S T G) : ∀ {n : ℕ} (c : Fin n → ℂ) (g : Fin n → WO S T → ℂ), (∀ p, IsThetaFunO ψ S T (g p)) →
    IsThetaFunO ψ S T (∑ p, c p • g p) ∧
      GlobalTheory.RawLift.thetaIP μ 𝓕 (∑ p, c p • g p) G = ∑ p, star (c p) * GlobalTheory.RawLift.thetaIP μ 𝓕 (g p) G := by
  intro n
  induction n with
  | zero =>
    intro c g _
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_left G⟩
  | succ n ih =>
    intro c g hg
    obtain ⟨ht, he⟩ := ih (fun p => c p.succ) (fun p => g p.succ) (fun p => hg p.succ)
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul _ (hg 0)) ht,
      by rw [GlobalTheory.VacSchurFin.thetaInner_left hψ hcv _ (hg 0) ht hG, he]⟩

theorem sum_right (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ {n : ℕ} (c : Fin n → ℂ) (g : Fin n → WO S T → ℂ), (∀ p, IsThetaFunO ψ S T (g p)) →
    IsThetaFunO ψ S T (∑ p, c p • g p) ∧
      GlobalTheory.RawLift.thetaIP μ 𝓕 f (∑ p, c p • g p) = ∑ p, c p * GlobalTheory.RawLift.thetaIP μ 𝓕 f (g p) := by
  intro n
  induction n with
  | zero =>
    intro c g _
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_right f⟩
  | succ n ih =>
    intro c g hg
    obtain ⟨ht, he⟩ := ih (fun p => c p.succ) (fun p => g p.succ) (fun p => hg p.succ)
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul _ (hg 0)) ht,
      by rw [GlobalTheory.VacSchurFin.thetaInner_right hψ hcv _ hf (hg 0) ht, he]⟩

variable {θ : InfFam D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
  {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {v : WO S T → ℂ}

theorem vac_translate (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hcv : IsCovolOne (ratL T S) μ 𝓕) {u : WO S T}
    (hu : u.map (infPart D) = 0) : GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) ∈ algebraicClosure ℚ ℂ := by
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have hlat := hv.2.lat
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  obtain ⟨h1, -, h3⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  by_cases hmem : u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
  · obtain ⟨ε, hε, hεv⟩ := h3 v hlat u hmem
    have hself : GlobalTheory.RawLift.thetaIP μ 𝓕 v v = 1 := by
      rw [GlobalTheory.RawLift.thetaInner_self]
      have hn := hv.2.norm.2 (μ, 𝓕) hcv
      simp only [nrm2] at hn
      rw [hn, Complex.ofReal_one]
    rw [hεv v hlat, GlobalTheory.RawLift.thetaInner_smul_right, hself, mul_one]
    rcases hε with rfl | rfl
    · exact one_mem _
    · exact neg_mem (one_mem _)
  · have hne : ∃ u' ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        ψ (symplO S T u u') ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hmem ((h1 u hu).2 hcon)
    obtain ⟨u', hu', hψu⟩ := hne
    obtain ⟨ε, hε, hεv⟩ := h3 v hlat u' hu'
    have hεv' := hεv v hlat
    have comm := GlobalTheory.SplitScalar.heisO_comm ψ S T u u' v
    rw [hεv', GlobalTheory.VacSchurFin.heisO_smul'] at comm
    have inv := GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv hvt (laws.1 u v hvt) u'
    rw [hεv'] at inv
    have hεε : star ε * ε = 1 := by
      rcases hε with h | h <;> rw [h] <;> simp only [star_one, star_neg, one_mul, neg_mul_neg]
    have hfix : ψ (symplO S T u u') * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) =
        GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) := by
      conv_lhs => rw [← inv, ← GlobalTheory.RawLift.thetaInner_smul_right, ← comm, GlobalTheory.RawLift.thetaInner_smul_left,
        GlobalTheory.RawLift.thetaInner_smul_right, ← mul_assoc, hεε, one_mul]
    have h0 : (ψ (symplO S T u u') - 1) * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) = 0 := by
      rw [sub_mul, hfix, one_mul, sub_self]
    rw [(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hψu)]
    exact zero_mem _

theorem translates (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hcv : IsCovolOne (ratL T S) μ 𝓕) {x y : WO S T}
    (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    GlobalTheory.RawLift.thetaIP μ 𝓕 (heisO ψ S T x v) (heisO ψ S T y v) ∈ algebraicClosure ℚ ℂ := by
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have e1 : heisO ψ S T (-x) (heisO ψ S T x v) = ψ (symplOH S T (-x) x) • v := by
    rw [GlobalTheory.SplitScalar.heisO_heisO, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero]
  have e2 : heisO ψ S T (-x) (heisO ψ S T y v) = ψ (symplOH S T (-x) y) • heisO ψ S T (-x + y) v :=
    GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) y v
  rw [← GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv (laws.1 x v hvt) (laws.1 y v hvt) (-x), e1, e2,
    GlobalTheory.RawLift.thetaInner_smul_left, GlobalTheory.RawLift.thetaInner_smul_right]
  refine mul_mem (alg_star (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hx))
    (mul_mem (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hy) ?_)
  exact vac_translate hv hS hT hcv (fin_add (fin_neg hx) hy)

theorem thetaIP_algComb : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F F' : WO S T → ℂ,
    GlobalTheory.MovedAlg.IsAlgComb ψ S T v F → GlobalTheory.MovedAlg.IsAlgComb ψ S T v F' → IsAlgebraic ℚ (GlobalTheory.RawLift.thetaIP μ 𝓕 F F') := by
  intro D ψ θ S T sS sT ΛS ΛT v hv hS hT μ 𝓕 hcv F F' hF hF'
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨m, c', w', hc', hw', rfl⟩ := hF'
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hth : ∀ x, IsThetaFunO ψ S T (heisO ψ S T x v) := fun x => laws.1 x v hvt
  have hR := (sum_right hψ hcv (hth 0) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).1
  rw [(sum_left hψ hcv hR c (fun p => heisO ψ S T (w p) v) fun p => hth _).2, ← mem_algebraicClosure_iff]
  refine Subalgebra.sum_mem _ fun p _ => mul_mem (alg_star (mem_algebraicClosure_iff.2 (hc p))) ?_
  rw [(sum_right hψ hcv (hth (w p)) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).2]
  exact Subalgebra.sum_mem _ fun q _ =>
    mul_mem (mem_algebraicClosure_iff.2 (hc' q)) (translates hv hS hT hcv (hw p) (hw' q))

end GlobalTheory.AlgPair

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.CosetRow


open Classical in
theorem givenFn_right_eq_extFn {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (B : Frames G) (t : T) (Φ : G.Datum) {e e₀ : AE D} (he : IsIdemSum e (locPl G t))
    (he₀ : IsIdemSum e₀ G.pl.W0)
    (hAA : ∀ w ∈ L.Q t, w ∉ G.pl.W0 → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) (i : Fin D.R.m) :
    GlobalTheory.FlipStart.givenFn B t Φ e (.right i 0) = GlobalTheory.CosetRow.extFn e₀ (e - e₀)
      (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _)
        (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) (cosInd e₀ (Φ i)) := by
  have hsub : G.pl.W0 ⊆ locPl G t := Finset.subset_union_left
  obtain ⟨he₁, h01⟩ := GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal he he₀ hsub
  have hee : e₀ + (e - e₀) = e := add_sub_cancel e₀ e
  have h0 := GlobalTheory.PlaceDatum.idemSum_mul_self he₀
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  obtain ⟨-, c0, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₀
  obtain ⟨-, c1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁
  have hAA' : ∀ w ∈ locPl G t \ G.pl.W0, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := fun w hw => by
    rw [Finset.mem_sdiff] at hw
    exact hAA w ((Finset.mem_union.1 hw.1).resolve_left hw.2) hw.2

  have hmap : ∀ (a : AE D) (w : Pl D.host.E), cpt (D := D) w (toEAf D a) = 1 →
      ∀ x : WO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)),
      (a • x).map (cpt (D := D) w ∘ toEAf D) = x.map (cpt (D := D) w ∘ toEAf D) := fun a w ha x => by
    ext p q
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Function.comp_apply, RingHom.map_mul, ha, one_mul]
  funext x
  unfold GlobalTheory.FlipStart.givenFn GlobalTheory.CosetRow.extFn
  rw [hee]
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg hx]
  rw [if_pos hx, if_pos hx]

  have hfac : ∀ w, givenDatum t w B Φ (edgeOf (.right i 0)) (locArg B t w (.right i 0) x) =
      if B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0)) ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩
        (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i) then 1 else 0 := fun w => by
    have hh : (i : ℕ) < D.R.m ∧ 0 ≤ D.R.m := ⟨i.2, Nat.zero_le _⟩
    have hla : locArg B t w (.right i 0) x = B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
        ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) := by
      exact dif_pos hh
    rw [hla]
    simp only [edgeOf, givenDatum, dif_pos i.2, Set.indicator_apply, Pi.one_apply, Fin.eta]
  rw [Finset.prod_congr rfl fun w _ => hfac w, ← Finset.prod_sdiff hsub, Finset.prod_boole, Finset.prod_boole]
  have hx0 : IsHalf e₀ (e₀ • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h0]
  have hx1 : IsHalf (e - e₀) ((e - e₀) • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h1]
  have k0 : cosInd e₀ (Φ i) (e₀ • x) = if ∀ w ∈ G.pl.W0, B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
      ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i)
      then 1 else 0 := by
    unfold cosInd
    rw [Set.indicator_apply, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    rw [GlobalTheory.FunObj.Comparison₂.mem_cosSet_iff_cosetSet B t hL he₀ i.2 (Φ i) hx0]
    exact forall₂_congr fun w hw => by rw [hmap e₀ w (c0 w hw)]
  have k1 : halfInd (e - e₀) (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _)
        (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) ((e - e₀) • x) = if ∀ w ∈ locPl G t \ G.pl.W0,
      B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
      ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i)
      then 1 else 0 := by
    unfold halfInd
    refine if_congr ?_ rfl rfl
    rw [and_iff_left hx1, GlobalTheory.T.mem_completedGridArrowLattice_iff_integral_frameMatrix hL B t he₁ hAA' i _ hx1]
    refine forall₂_congr fun w hw => ?_
    rw [hmap _ w (c1 w hw), GlobalTheory.FunObj.Comparison₂.cosetSet_of_notMem B t w hL (Finset.mem_sdiff.1 hw).2 i.2 (Φ i)]
    rfl
  rw [k0, k1, mul_comm]

end GlobalTheory.CosetRow
end
