module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle234
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle301
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalKill
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulBrStdOfEquivariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hasSum_norm_sphericalZetaKernel_unramifiedUnitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∃ α : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α ∧ HasSum (fun a : GU σ r ⧸ KU σ r => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹)) := by
  first | exact @GlobalTheory.ZetaAbsU.hasSum_norm_kerU | exact GlobalTheory.ZetaAbsU.hasSum_norm_kerU | (intros; apply GlobalTheory.ZetaAbsU.hasSum_norm_kerU <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.otherInstanceForm_flagPairing_integral_on_frameLattice : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ (PP : Pl D.host.E) (a : Fin (Yc D 0).rank) (z : Fin (Yc D 0).rank → EAf D), (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.SeeConjChar.hT_pairAt_int | exact GlobalTheory.SeeConjChar.hT_pairAt_int | (intros; apply GlobalTheory.SeeConjChar.hT_pairAt_int <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem cT_mul_entry {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (U J W : Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (Formalism.UG.cT σ U * J * W) a b = Formalism.UG.hform σ J (fun i => U i a) (fun i => W i b) := by
  unfold Formalism.UG.cT Formalism.UG.hform
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_comm

theorem over_g {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) {Q : Pl D.host.E}
    (hQ : Q ∈ R.Pg) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
  obtain ⟨k, hk⟩ := (hL.Pg Q).1 hQ
  have hmem : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (Q.under (𝓞 D.host.K)).asIdeal := by
    rw [show Q.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact R.C.P.pb_over k
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hmem
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ hmem
  · exact Ideal.mul_mem_left _ _ hmem

theorem exists_frame_redIs : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL _
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    rw [show (Yc D 0).rank = D.R.rankY 0 from D.sp.Y_rank 0 (Nat.zero_le _)]
    have hm := D.R.m_even
    have h2 := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rankY Formalism.BasicNotions.Ranks.rS Formalism.BasicNotions.Ranks.r
    obtain ⟨c, hc⟩ := hm
    omega
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.StdFrames.exists_base (Yc D 0)
  have hG := (GlobalTheory.StdFrames.unimod_of_isSD (GlobalTheory.StdFrames.isSD_one hβ₀)).1
  have hint : ∀ (PP : Pl D.host.E) (i j : Fin (Yc D 0).rank),
      ((β₀⁻¹).val * colMat (flagAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      ((β₀⁻¹).val * colMat (pairAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have cast_fun_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) {m : ℕ}
        (f : Fin m → Formalism.L2.SG.HidaSetting.VA I) (hf : ∀ a, f a ∈ I.Lf) (a : Fin m) :
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin m → Formalism.L2.SG.HidaSetting.VA I) h) f) a ∈ J.Lf := by
      subst h
      exact hf a
    have cast_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J)
        (v : Formalism.L2.SG.HidaSetting.VA I) (hv : v ∈ I.Lf) :
        cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) v ∈ J.Lf := by
      subst h
      exact hv
    have flagV_mem {M : Type} [Zero M] (S : Set M) (h0 : (0 : M) ∈ S) (ρ k n : ℕ)
        (e f : Fin ρ → M) (b : Fin k → M) (z : M) (he : ∀ a, e a ∈ S)
        (hf : ∀ a, f a ∈ S) (hb : ∀ a, b a ∈ S) (hz : z ∈ S) (i : Fin n) :
        flagV ρ k n e f b z i ∈ S := by
      unfold flagV
      split_ifs
      exacts [he _, hb _, hz, hf _, h0]
    intro PP i j
    have hF : IsFrame β₀ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := hβ₀ ▸ GlobalTheory.StdFrames.isFrame_lat β₀
    have hLf := GlobalTheory.KgFrame.Lf_eq D
    have key : ∀ v : Fin (Yc D 0).rank → EAf D, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf →
        Matrix.mulVec (β₀⁻¹).val v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro v hv
      rw [hLf] at hv
      exact (hF v).1 hv i
    set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf}
    have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
      show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
      exact zero_mem _
    obtain ⟨hef, hz, hbw⟩ := X.vectorsInLattice
    have he : ∀ a, e0T X h a ∈ S := cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
    have hf : ∀ a, f0T X h a ∈ S := cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
    have hb : ∀ a, bwT X h a ∈ S := cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
    have hbd : ∀ a, bwdT X h a ∈ S := cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
    have hzz : z0T X h ∈ S := cast_mem_Lf h X.z0 hz
    constructor
    · change Matrix.mulVec (β₀⁻¹).val (flagAt X h PP j) i ∈ _
      apply key
      unfold flagAt
      split_ifs
      · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf hb hzz j
      · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf (fun a => hbd _) hzz j
    · change Matrix.mulVec (β₀⁻¹).val (pairAt X h PP j) i ∈ _
      apply key
      unfold pairAt
      split_ifs
      · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz j
      · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun a => hb _) hzz j
  have hdet : ∀ Q ∈ R.Pg,
      Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * colMat (flagAt X h Q)).det) = 1 := by
    intro Q hQ
    have hg := over_g R hL hQ
    refine GlobalTheory.T.standard_frame_integrality_conditions β₀ (GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram) (colMat (pairAt X h Q))
      (colMat (flagAt X h Q)) Q (fun a => sgnD D.R.rS D.R.k a) hG (fun i j => (hint Q i j).2)
      (fun i j => (hint Q i j).1) ?_ ?_
    · intro a
      unfold sgnD
      split_ifs <;> simp
    · intro a b
      rw [cT_mul_entry]
      change SmallAt Q (hY D (pairAt X h Q a) (flagAt X h Q b) - _)
      by_cases hc : GlobalTheory.StdFrames.cpt Q (ewT X h) = 1
      · rw [pairAt, flagAt, if_pos hc, if_pos hc]
        exact GlobalTheory.T.flagPairingTable_diagonal_modSmall (hY D) (SmallAt Q) D.R.rS D.R.k _ hn _ _ _ _ _ (GlobalTheory.T.flagPairingTable_idempotentComponent_one X h Q hg hc) a b
      · rw [pairAt, flagAt, if_neg hc, if_neg hc]
        exact GlobalTheory.T.flagPairingTable_diagonal_modSmall (hY D) (SmallAt Q) D.R.rS D.R.k _ hn _ _ _ _ _ (GlobalTheory.T.flagPairingTable_idempotentComponent_ne_one X h Q hg hc) a b
  obtain ⟨β, hβ, hred⟩ := GlobalTheory.T.exists_frame_lifting_prescribed_reductions β₀ R.Pg (flagAt X h) (fun Q _ i j => (hint Q i j).1) hdet
  refine ⟨β, ?_, hred⟩
  rw [hβ₀, ← hβ]
  exact GlobalTheory.StdFrames.isFrame_lat β

end GlobalTheory.SeeConjRead

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopLevelInv

section Local

variable {k : Type} [Field k]

def colMove {G : Grid k} (j : ℕ) (κ : GL (Fin (topRank G (j + 1))) k) (x : ColArgs G) : ColArgs G :=
  Function.update (Function.update x j ((κ⁻¹).val * x j)) (j + 1) (x (j + 1) * κ.val)


open Classical in
def stepVol [MeasurableSpace k] (ν : Measure k) (n : Type) [Fintype n] (c : ℕ) (n' : Type) [Fintype n'] :
    Measure (StepVar n c n' → k) := Measure.pi fun _ => ν

theorem varsVol_eq [MeasurableSpace k] (G : Grid k) (ν : Measure k) :
    varsVol G ν = Measure.pi fun j : Fin (G.m - 1) => stepVol ν (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)) := rfl

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem gdet_of_mem_N {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) : gdet g = 1 := by
  refine (show N k n c p ≤ (Matrix.GeneralLinearGroup.det (n := n ⊕ Fin c) (R := k)).ker from
    (Subgroup.closure_le _).2 fun g hg => ?_) hg
  apply Units.ext
  change g.val.det = 1
  rw [(GlobalTheory.RootEx.Model.inN_tri hg).det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : g.val.toSquareBlock (lev p) a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [hg i j (by rw [hi, hj]), Matrix.one_apply, Matrix.one_apply]
    simp [Subtype.ext_iff]
  rw [this, det_one]

theorem gdet_of_mem_symN {g : GL (n ⊕ Fin c) k} (hg : g ∈ symN k n c) : gdet g = 1 :=
  (show symN k n c ≤ (Matrix.GeneralLinearGroup.det (n := n ⊕ Fin c) (R := k)).ker from
    sup_le (fun _ h => gdet_of_mem_N h) fun _ h => gdet_of_mem_N h) hg

theorem gdet_embX (g : GL n k) : gdet (embX c g) = gdet g :=
  Units.ext (by
    change (fromBlocks g.val 0 0 (1 : Matrix (Fin c) (Fin c) k)).det = g.val.det
    rw [det_fromBlocks_zero₂₁, det_one, mul_one])

theorem gdet_toFrame {G : Grid k} (hs : 1 ≤ G.s) {j : ℕ} (hj : j < G.m) (g : GL (Fin (G.rank (G.m, j))) k) :
    gdet (toFrame hs hj g) = gdet g :=
  Units.ext (det_submatrix_equiv_self _ _)

theorem exists_of_mem_symPr {G : Grid k} (hs : 1 ≤ G.s) {J : G.Level} {g : G.VertexGroup} {j : ℕ} (hj : j < G.m)
    {κ : GL (Fin (topRank G j)) k} (hκ : κ ∈ symPr (conjLevel hs J g hj)) :
    ∃ u ∈ J (G.m, j), ∃ v ∈ symN k (Fin (topRank G j)) (G.m - 1 - j),
      toFrame hs hj (g (G.m, j) * u * (g (G.m, j))⁻¹) = v * embX _ κ ∧ gdet κ = gdet u := by
  obtain ⟨v, hv, _, ⟨u, hu, rfl⟩, h⟩ := hκ
  refine ⟨u, hu, v, hv, h, ?_⟩
  have := congrArg gdet h
  rw [gdet_mul, gdet_of_mem_symN hv, one_mul, gdet_embX] at this
  rw [← this]
  change gdet (toFrame hs hj (g (G.m, j) * u * (g (G.m, j))⁻¹)) = _
  rw [gdet_toFrame, gdet_mul, gdet_mul, mul_right_comm, ← gdet_mul, mul_inv_cancel]
  simp

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def movedPt (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1)))
    (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) :=
  Function.update (Function.update x ⟨j, by omega⟩ (actO _ _ 1⁻¹ (g : GA D (G.V (.top (j + 1))))⁻¹ (x ⟨j, by omega⟩)))
    ⟨j + 1, hj⟩ (actO _ _ (g : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ (x ⟨j + 1, hj⟩))

theorem movedFn_apply (S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1)))
    (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T))) (j' : Fin D.R.m) :
    movedFn S d j hj g j' (x j') = (d.1 j').fn (movedPt t j hj g x j') := by
  rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1
  · simp only [movedFn, movedPt, Function.update_self]
  rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | h2
  · simp only [movedFn, movedPt, Function.update_of_ne h1, Function.update_self]
  · simp only [movedFn, movedPt, Function.update_of_ne h1, Function.update_of_ne h2]

def kapAt (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
    GL (Fin (topRank (locGrid G t w) (j + 1))) (Kw w) :=
  inBasis (topRank_eq G t w hj.le) (S.βp (j + 1)) w (finG (G.V (.top (j + 1))) k)

theorem kapAt_mem (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {j : ℕ} (hj : j + 1 < D.R.m)
    {k : FinPt G (.top (j + 1))} (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) (w : locPl G t) :
    kapAt S t j hj k w ∈ (S.term t Φ β w).pr (j + 1) j.succ_pos hj :=
  Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w

theorem givenLevel_col (t : T) (w : Pl D.host.E) (j : ℕ) : givenLevel G t w (D.R.m, j + 1) = KO (Kw w) _ := by
  have key : ∀ i, 0 < i → givenLevel G t w (i, j + 1) = KO (Kw w) _ := by
    rintro (_ | i) h
    · omega
    · rfl
  exact key _ (by have := D.R.two_le_m; omega)

theorem valuation_gdet_kapAt (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {j : ℕ} (hj : j + 1 < D.R.m)
    {k : FinPt G (.top (j + 1))} (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) (w : locPl G t) :
    valuation (Kw w.1) (gdet (kapAt S t j hj k w) : Kw w.1) = 1 := by
  obtain ⟨u, hu, -, -, -, h⟩ := exists_of_mem_symPr (G := locGrid G t w) one_le_sLen hj (kapAt_mem S hj hk w)
  rw [h]
  exact valuation_gdet_of_mem_KO (givenLevel_col t w.1 j ▸ hu)

end GlobalTheory.TopLevelInv

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.IoLift.Factor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem kerLe_finset {A B Z₁ Z₂ σ : Type} [AddCommMonoid Z₁] [AddCommMonoid Z₂] {q₁ : A → B → Z₁} {q₂ : A → B → Z₂}
    (h : KerLe q₁ q₂) (s : Finset σ) (a : σ → A) (b : σ → B) (h0 : ∑ r ∈ s, q₁ (a r) (b r) = 0) :
    ∑ r ∈ s, q₂ (a r) (b r) = 0 := by
  have e := s.equivFin.symm
  rw [← Finset.sum_coe_sort s, ← e.sum_comp] at h0 ⊢
  exact h _ (fun k => a (e k)) (fun k => b (e k)) h0

theorem section_eq {ι : Type} [Fintype ι] {N K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (α : ∀ i, N i →ₗ[ℂ] K i) (s : ∀ i, K i →ₗ[ℂ] N i) (hs : ∀ i x, α i (s i x) = x)
    (M : (Π i, N i) →ₘₗ[ℂ] Z) (hM : ∀ n i z, α i z = 0 → M (Function.update n i z) = 0) (n : ∀ i, N i) :
    M (fun i => s i (α i (n i))) = M n := by
  have key : ∀ S : Finset ι, M (S.piecewise (fun i => s i (α i (n i))) n) = M n := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      rw [Finset.piecewise_insert, ← ih]
      have h1 := hM (S.piecewise (fun i => s i (α i (n i))) n) j (s j (α j (n j)) - n j) (by simp [hs])
      rw [MultilinearMap.map_update_sub, sub_eq_zero] at h1
      rw [h1]
      congr 1
      rw [Function.update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ hj]
  simpa using key Finset.univ

theorem factor :
    ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (P Y : ι → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (A : ∀ i, P i →ₗ[ℂ] Y i →ₗ[ℂ] K i), (∀ i, Submodule.span ℂ {x | ∃ p y, A i p y = x} = ⊤) → Submodule.span ℂ {x : ⨂[ℂ] i, K i | ∃ (p : ∀ i, P i) (y : ∀ i, Y i), PiTensorProduct.tprod ℂ (fun i => A i (p i) (y i)) = x} = ⊤ ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (B : (Π i, P i) →ₘₗ[ℂ] ((Π i, Y i) →ₘₗ[ℂ] Z)), (∀ i p y, KerLe (fun x z => A i x z) fun x z => B (Function.update p i x) (Function.update y i z)) → ∃ T : (⨂[ℂ] i, K i) →ₗ[ℂ] Z, ∀ p y, T (PiTensorProduct.tprod ℂ fun i => A i (p i) (y i)) = B p y := by
  intro ι _ K _ _ P Y _ _ _ _ A hA
  let α : ∀ i, (P i × Y i →₀ ℂ) →ₗ[ℂ] K i := fun i => Finsupp.linearCombination ℂ fun r => A i r.1 r.2
  have hα : ∀ i, LinearMap.range (α i) = ⊤ := by
    intro i
    rw [Finsupp.range_linearCombination, ← hA i]
    congr 1
    ext x
    simp
  choose s hs using fun i => (α i).exists_rightInverse_of_surjective (hα i)
  have hs' : ∀ i x, α i (s i x) = x := fun i x => LinearMap.congr_fun (hs i) x
  let b0 : ∀ i, Module.Basis (P i × Y i) ℂ (P i × Y i →₀ ℂ) := fun i => Finsupp.basisSingleOne
  have hb0 : ∀ i r, α i (b0 i r) = A i r.1 r.2 := by
    intro i r
    simp [α, b0]
  let b := Basis.piTensorProduct b0
  refine ⟨?_, ?_⟩
  · have hsurj : LinearMap.range (PiTensorProduct.map α) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro t
      refine ⟨PiTensorProduct.map s t, ?_⟩
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      simp [hs]
    rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span] at hsurj
    rw [eq_top_iff, ← hsurj]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨fun i => (q i).1, fun i => (q i).2, ?_⟩
    simp [b, hb0]
  · intro Z _ _ B hB
    let M : (Π i, P i × Y i →₀ ℂ) →ₘₗ[ℂ] Z :=
      (b.constr ℂ fun q => B (fun i => (q i).1) (fun i => (q i).2)).compMultilinearMap (PiTensorProduct.tprod ℂ)
    have hMb : ∀ q : ∀ i, P i × Y i, M (fun i => b0 i (q i)) = B (fun i => (q i).1) (fun i => (q i).2) := by
      intro q
      simp only [M, LinearMap.compMultilinearMap_apply]
      rw [← Basis.piTensorProduct_apply b0 q]
      exact b.constr_basis ℂ _ q
    have hM0 : ∀ (q : ∀ i, P i × Y i) i z, α i z = 0 → M (Function.update (fun i => b0 i (q i)) i z) = 0 := by
      intro q i z hz
      have h1 : ∀ r, M (Function.update (fun i => b0 i (q i)) i (b0 i r)) =
          B (Function.update (fun i => (q i).1) i r.1) (Function.update (fun i => (q i).2) i r.2) := by
        intro r
        have := hMb (Function.update q i r)
        convert this using 2 <;> [skip; congr 1; skip] <;> funext j <;> by_cases h : j = i <;>
          first | (subst h; simp) | simp [h]
      have h2 : M (Function.update (fun i => b0 i (q i)) i z) = ∑ r ∈ z.support,
          B (Function.update (fun i => (q i).1) i (z r • r.1)) (Function.update (fun i => (q i).2) i r.2) := by
        have hz' : z = ∑ r ∈ z.support, z r • b0 i r := by
          conv_lhs => rw [← Finsupp.sum_single z]
          simp [Finsupp.sum, b0]
        conv_lhs => rw [hz']
        rw [MultilinearMap.map_update_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [MultilinearMap.map_update_smul, MultilinearMap.map_update_smul, h1]
        rfl
      rw [h2]
      refine kerLe_finset (hB i (fun i => (q i).1) (fun i => (q i).2)) z.support (fun r => z r • r.1)
        (fun r => r.2) ?_
      simpa [α, Finsupp.linearCombination_apply, Finsupp.sum] using hz
    have hM : ∀ n i z, α i z = 0 → M (Function.update n i z) = 0 := by
      intro n i z hz
      let φ : (P i × Y i →₀ ℂ) →ₗ[ℂ] (P i × Y i →₀ ℂ) := Finsupp.linearCombination ℂ fun _ => z
      have hφ : ∀ r, φ (b0 i r) = z := by
        intro r
        simp [φ, b0]
      let f : ∀ j, (P j × Y j →₀ ℂ) →ₗ[ℂ] (P j × Y j →₀ ℂ) := Function.update (fun j => LinearMap.id) i φ
      have hf : ∀ m : ∀ j, (P j × Y j →₀ ℂ), (fun j => f j (m j)) = Function.update m i (φ (m i)) := by
        intro m
        funext j
        by_cases h : j = i
        · subst h; simp [f]
        · simp [f, h]
      have h0 : M.compLinearMap f = 0 := by
        refine Module.Basis.ext_multilinear b0 fun q => ?_
        rw [MultilinearMap.compLinearMap_apply, hf, hφ]
        exact hM0 q i z hz
      have := congrArg (fun F => F (Function.update n i (b0 i 0))) h0
      simpa [hf, hφ] using this
    refine ⟨PiTensorProduct.lift (M.compLinearMap s), fun p y => ?_⟩
    rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, ← hMb fun i => (p i, y i),
      ← section_eq α s hs' M hM fun i => b0 i (p i, y i)]
    simp only [hb0]

end GlobalTheory.Chain.IoLift.Factor

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift

theorem adjZ_eq_neg_of_mem_upq {p q : ℕ} {Z : Mat p q} (h : Z ∈ upq p q) : adjZ Z = -Z := by
  have h0 : Zᴴ * Jm p q + Jm p q * Z = 0 := h
  have h1 : Zᴴ * Jm p q = -(Jm p q * Z) := eq_neg_of_add_eq_zero_left h0
  rw [adjZ, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc,
    GlobalTheory.InvPairingTensor.Jm_mul_self, Matrix.one_mul]

theorem finiteSupport_of_admissible :
    ∀ (p q r s : ℕ) (T : GrpData r s) (R : DSRep T), Formalism.MainNotions.SchurIrreducible.AdmGK R.HK → FiniteSupport p q R := by
  intro p q r s T R hA A _ _ B hB P
  refine GlobalTheory.InvPairingTensor.exists_finiteDimensional_kill R hA B (fun Z hZ Q y => ?_) P
  rw [hB Z Q y, adjZ_eq_neg_of_mem_upq hZ, map_neg, LinearMap.neg_apply, map_neg, neg_add_cancel]

end GlobalTheory.Chain.IoLift
end

section

open Formalism.BasicNotions Formalism.L2.DIV

theorem _root_.GlobalTheory.T.exists_eq_smul_brStd_of_equivariant : ∀ {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1), 1 ≤ n → ∀ (Λ : ι → DomWeight N) (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) → ∀ φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ, (∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) = rhoK σ g (φ v)) → ∃ c : ℂ, φ = c • Formalism.L2.Col.Br.brStd hN Λ σ := by
  first | exact @GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant | exact GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant | (intros; apply GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant <;> assumption)
end
