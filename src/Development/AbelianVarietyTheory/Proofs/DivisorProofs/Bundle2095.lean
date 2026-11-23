module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSumSizeBoundLargeDataFromFactors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
public import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle432
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990

@[expose] public section

section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorusCent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem swap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : IsWittFrame σ J Y X :=
  ⟨hW.yy, hW.xx, yx h hJ hW, fun z h1 h2 h3 => hW.aniso z h2 h1 h3⟩

end GlobalTheory.IdTorusCent

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SumSize.PairInt

open GlobalTheory.SumSize.TopInt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

section Claims

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

def PairIntRatAt : Prop := ∃ dl, Loss dl (bOne ch.G C b) ∧ ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ w, Away ch.G t w →
  ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl ch.G t →
    (∀ l : ℕ, l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → padicValNat l k ≤ depL ch.G l) →
    ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y → ∀ (a : ℝ) v,
      InLat _ w a (latAt ch.S.toGridChoice p.small x) v →
        InLat _ w (a + dl w) (latAt ch.S.toGridChoice p.big y) (ch.S.Z.kkMap 1 d x y v)

end Claims

def PairIntRatK : Prop := BigC fun _ ch C b => PairIntRatAt ch C b

end GlobalTheory.SumSize.PairInt

end
end

section

open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.archimedeanSumSizeBound_largeData_from_factors : SumOKK → DepthK → InfScalK → InfTensK → InfCountK → InfClassK → InfTopK → InfRowK → InfPairK → InfPsiK → InfFormK → InfK := by
  first | exact @GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors | exact GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors | (intros; apply GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
open GlobalTheory.SignedHC

namespace GlobalTheory.KerConjMean.TopSizes

theorem natW_wtOf_le (n : ℕ) (E : Finset ℚ) (lo hi : ℝ) (hM : lo ≤ hi) (hE : ∀ x ∈ E, lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi) (a : Fin n) :
    (((wtOf n E).natW a : ℕ) : ℝ) ≤ hi - lo + 1 := by
  have hn : 0 < n := a.pos
  have key : (wtOf n E).natW a = ((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩).toNat := by
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn]
  have hd : (((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩ : ℤ) : ℝ) ≤ hi - lo + 1 := by
    unfold wtOf
    split_ifs with h
    · have e0 := hE _ (descEnum_mem E h.1 a)
      have e1 := hE _ (descEnum_mem E h.1 ⟨n - 1, by omega⟩)
      have f0 : ((⌊highestWeight E h.1 a⌋ : ℤ) : ℝ) ≤ ((highestWeight E h.1 a : ℚ) : ℝ) := by
        exact_mod_cast Int.floor_le _
      have f1 : ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ) - 1 <
          ((⌊highestWeight E h.1 ⟨n - 1, by omega⟩⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.sub_one_lt_floor _
      have hr : ((a : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast a.2
      have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
      have g0 : ((highestWeight E h.1 a : ℚ) : ℝ) ≤ hi + ((n : ℝ) - 1) / 2 := by
        simp only [highestWeight]; push_cast; linarith [e0.2]
      have g1 : lo + ((n : ℝ) - 1) / 2 ≤ ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ) := by
        simp only [highestWeight, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, hc]
        linarith [e1.1]
      push_cast
      linarith
    · simp; linarith
  rw [key]
  have c : ∀ z : ℤ, (z.toNat : ℝ) = (((z.toNat : ℕ) : ℤ) : ℝ) := fun z => (Int.cast_natCast _).symm
  rw [c, Int.toNat_eq_max]
  push_cast
  exact max_le (by push_cast at hd; exact hd) (by linarith)

theorem extend_bounds {n : ℕ} (d : ℕ) (f : Fin n → ℚ) (h : ℝ) (hh : 0 ≤ h)
    (hf : ∀ i, 0 ≤ ((f i : ℚ) : ℝ) ∧ ((f i : ℚ) : ℝ) ≤ h) (j : ℕ) :
    0 ≤ ((GridData.extend d f j : ℤ) : ℝ) ∧ ((GridData.extend d f j : ℤ) : ℝ) ≤ h := by
  unfold GridData.extend
  split_ifs with hj
  · obtain ⟨h1, h2⟩ := hf ⟨j - d, hj⟩
    have a1 : (0 : ℚ) ≤ f ⟨j - d, hj⟩ := by exact_mod_cast h1
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 a1, le_trans ?_ h2⟩
    exact_mod_cast Int.floor_le _
  · simp [hh]

theorem entry_bounds {D : D7} (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (j : ℕ) (τ : D.what₂.Tau) :
    ∀ x ∈ (num D 1 τ).weightX j, -(5 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
  obtain ⟨hN, -, -, -, hm2, -, -, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, hbe, -⟩ := hs
  have hSc := large₂.Sc_pos
  have hg0 : (0 : ℝ) ≤ (gap D 1 : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hScb : large₂.Sc ≤ large₂.sc.b := by nlinarith
  have hts : D.R.t + sLen D + 1 ≤ bigN D := by
    have : D.R.t + sLen D + 1 ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_left _ (by omega)
    unfold bigN; omega
  have hts' : (D.R.t : ℝ) + (sLen D : ℝ) + 1 ≤ large₂.sc.b := le_trans (by exact_mod_cast hts) hN
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (sLen D : ℝ) := Nat.cast_nonneg _
  have hv : ∀ j, 0 ≤ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ∧ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ≤ large₂.Sc :=
    extend_bounds 2 _ _ hSc.le fun l => large₂.cloud_v τ l
  have hel : ∀ l : Fin D.R.m, 0 ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * large₂.sc.b := fun l => by
    obtain ⟨h1, h2⟩ := hbe τ l
    have h3 := (D.hc τ).gap_be l
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have h4 : 0 ≤ (D.hc τ).e l := by linarith
    exact ⟨by exact_mod_cast h4, h2⟩
  have he := extend_bounds 1 _ _ (by linarith) hel
  have hcen : ∀ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ ((cen D 1 τ j : ℤ) : ℝ) ∧ ((cen D 1 τ j : ℤ) : ℝ) ≤ large₂.sc.b := by
    intro j hj1 hj2
    have e := GridData.mid_eq (GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0) hj1
    have hv2 := hv 2
    have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hj2' : (j : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hj2
    have hmid : 0 ≤ (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ∧
        (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ≤ large₂.sc.b := by
      rw [e]
      simp only [GridData.a, GridData.ofHCParam]
      push_cast
      constructor <;> nlinarith
    unfold cen
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 (by exact_mod_cast hmid.1), le_trans ?_ hmid.2⟩
    exact_mod_cast Int.floor_le _
  intro x hx
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, -, -, h⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    have hi' : (i : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast (show i ≤ D.R.m from hi)
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    have hv2 := hv 2
    simp only [GridData.a, num, GridData.ofHCParam]
    push_cast
    constructor <;> nlinarith
  · obtain ⟨i, -, -, rfl⟩ := GridData.mem_cloudHalf.1 h
    have h : 0 ≤ (((num D 1 τ).v i : ℤ) : ℝ) ∧ (((num D 1 τ).v i : ℤ) : ℝ) ≤ large₂.Sc := hv i
    simp only [GridData.vHalf]
    push_cast
    constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have h : 0 ≤ (((num D 1 τ).cen i : ℤ) : ℝ) ∧ (((num D 1 τ).cen i : ℤ) : ℝ) ≤ large₂.sc.b := hcen i hi1 hi2
    have h1 : (((num D 1 τ).s - 1 : ℕ) : ℝ) ≤ (sLen D : ℝ) := by
      exact_mod_cast (show sLen D - 1 ≤ sLen D from Nat.sub_le _ _)
    have ha' : (a : ℝ) + 1 ≤ (((num D 1 τ).s - 1 : ℕ) : ℝ) := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_one, Rat.cast_ofNat]
    constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have h : 0 ≤ (((num D 1 τ).e l : ℤ) : ℝ) ∧ (((num D 1 τ).e l : ℤ) : ℝ) ≤ 4 * large₂.sc.b := he l
    have h1 : ((num D 1 τ).t : ℝ) = (D.R.t : ℝ) := rfl
    have ha' : (a : ℝ) ≤ ((num D 1 τ).t : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 ha
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    push_cast
    constructor <;> linarith

theorem sizesK : BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b => 3 ≤ b ∧ 1 ≤ bigN D ∧ (bigN D : ℝ) ≤ b ∧ 1 ≤ D.R.f ∧ (D.R.f : ℝ) ≤ b ∧
  Fintype.card D.what₂.Tau ≤ D.R.f ∧ 0 ≤ D.host.rdE ∧ D.host.rdE ≤ b ∧ ∀ j : ℕ, j ≤ D.R.m →
    (ch.G.V (.top j)).rank ≤ bigN D ∧ ∀ τ i, ((wt ch.G (.top j) τ).natW i : ℝ) ≤ 8 * b := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hch _
  obtain ⟨hN, hf, hN1, hf1, -, hrd1, hrd, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
  have hc : ch.sc.cGap = 1 := by
    have h : ch.sc = { cGap := 1, cDep := CF, b := large₂.sc.b } := hch
    rw [h]
  refine ⟨by linarith, hN1, hN, hf1, hf, (Lnk.card_Tau D).le, by linarith, ?_, fun j hj => ⟨?_, fun τ i => ?_⟩⟩
  · exact (Real.log_le_log_iff (by linarith) (by linarith)).1 (by linarith)
  · exact GlobalTheory.DefRank.rank_le_bigN ch.G (.top j) hj
  · have key : ∀ x ∈ _root_.GlobalTheory.SignedHC.entries (Node.par D ch.sc.cGap (.top j) τ), -(5 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
      rw [hc]
      intro x hx
      have e : _root_.GlobalTheory.SignedHC.entries (Node.par D 1 (.top j) τ) = (num D 1 τ).weightX j := entries_plus _
      exact entry_bounds large₂ hS.size j τ x (e ▸ hx)
    have hw := natW_wtOf_le _ _ _ _ (by linarith) key i
    calc (((wt ch.G (.top j) τ).natW i : ℕ) : ℝ)
        = (((wtOf _ (_root_.GlobalTheory.SignedHC.entries (Node.par D ch.sc.cGap (.top j) τ))).natW i : ℕ) : ℝ) := rfl
      _ ≤ _ := hw
      _ ≤ 8 * large₂.sc.b := by linarith

end GlobalTheory.KerConjMean.TopSizes
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

theorem _root_.GlobalTheory.T.absNorm_gridModulus_le_exp_depthLogNormSum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), D.host.F = maximalRealSubfield D.host.E → (Ideal.absNorm G.modul : ℝ) ≤ Real.exp (2 * sig G) := by
  first | exact @GlobalTheory.ModulNorm.absNorm_modul_le | exact GlobalTheory.ModulNorm.absNorm_modul_le | (intros; apply GlobalTheory.ModulNorm.absNorm_modul_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

open GlobalTheory.MovedTwist GlobalTheory.MovedField Formalism.L2.Host GlobalTheory.ChiUnit in

theorem _root_.GlobalTheory.T.movedTensorFactor_coeffValuationLossLe_awayPrime : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∉ ch.G.pl.W0 → ∀ (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    ∀ (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z) c := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β _ P hP w hw c _ hT z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  set q : ℕ := Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) with hqdef
  have hq0 : q ≠ 0 := (Formalism.EigenvalueLevelCeiling.plc_prime _).ne_zero
  have hq : (q : 𝓞 D.host.E) ∈ (P : Pl D.host.E).asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem _
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (P : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt P.1 (.inr ⟨t, P.2⟩))
  have hmu : ∀ j (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).mu j x : ℂˣ) : ℂ) := fun j x => by
    change UnitIn K q (((GlobalTheory.FunObj.muBase R.toLevCh j).loc P.1 x : ℂ) *
      ((R.xiH t).loc P.1 x : ℂ))
    refine UnitIn.mul ?_ ⟨(hK _).1 (hF.chars.xi t _ x), ?_⟩
    · rcases j with _ | j
      · exact unitIn_one K q
      · rw [GlobalTheory.FunObj.muBase]
        split_ifs with hj
        · obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 ⟨j, hj⟩).inf
          exact ⟨(hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x), unitOff_loc _ hn _ hq x⟩
        · exact unitIn_one K q
    · obtain ⟨n, hn, ho⟩ := hS.core.lev.xi_fin t
      refine unitOff_of_pow_eq_one q hn ?_
      have : ((R.toLevCh.xiH t) ^ n).loc P.1 x = 1 := by rw [show (R.toLevCh.xiH t) ^ n = 1 from ho]; rfl
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg Units.val this
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).chi i x : ℂˣ) : ℂ) :=
    fun i h1 h2 x => ⟨(hK _).1 (hF.chars.chi i h1 h2 _ x), unitOff_loc _ (ch.G.ch.inf i h1 h2) _ hq x⟩
  have heta : ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).eta x : ℂˣ) : ℂ) := fun x => by
    have hu := R.toLevCh.C.isEta.unr P.1
    obtain ⟨y, hy⟩ := hF.chars.eta P.1 hu
    exact ⟨loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x, unitOff_loc _ R.toLevCh.C.isEta.inf _ hq x⟩
  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).kappa e X x : ℂˣ) : ℂ) := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, div_eq_mul_inv]
    refine UnitIn.mul ?_ ((heta x).pow _).inv
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw P.1)ˣ) (n : ℕ), UnitIn K q (apow x ((n : ℂ) / 2)) ∧ UnitIn K q (apow x (-(n : ℂ) / 2)) := fun x n =>
    ⟨⟨by simpa using apow_half_mem hsq x n, by simpa using unitOff_apow_half hq0 hq x n⟩,
      by simpa using apow_half_mem hsq x (-n), by simpa using unitOff_apow_half hq0 hq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, UnitIn K q ((locGrid ch.G t P).edgeFactor .one g e) := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact (((hkap e he _ _).mul (hkap e he _ _).inv).mul (hap _ _).1).mul (hap _ _).2
  have hk : keepAt ch.G (P : Pl D.host.E) = true := by
    classical
    simp [keepAt, hP]
  have hg := unitIn_prod _ _ (hedge ((repsAt ch.G t P).elt (β P)))
  simp only [moved, Grid.pathAct, hk, ite_true, one_mul]
  exact lossLe_unit_mul hw hg.1 hg.2 (hT _)
end

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.NuExpModulus

open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop

theorem levelLe_mono {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m n : ℕ}
    (h : χ.LevelLe w m) (hmn : m ≤ n) : χ.LevelLe w n := fun x hx hv =>
  h x hx (hv.trans (WithZero.exp_le_exp.2 (by omega)))

theorem exp_eq {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {c n : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt χ w c) (h1 : χ.LevelLe w (n + 1)) (h2 : ¬ χ.LevelLe w n) : c = n + 1 := by
  have a := (hc _).1 h1
  have b := (hc n).not.1 h2
  omega

theorem exp_div {E : Type} [Field E] [NumberField E] {a b : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {c n : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt (a / b) w c) (ha : a.LevelLe w n) (h1 : b.LevelLe w (n + 1)) (h2 : ¬ b.LevelLe w n) :
    c = n + 1 := by
  refine exp_eq hc ?_ fun h => h2 ?_
  · rw [div_eq_mul_inv]
    exact Formalism.L2.Host.HChar.LevelLe.mul (levelLe_mono ha (Nat.le_succ n)) (Formalism.L2.Host.HChar.LevelLe.inv h1)
  · have e : b = a * (a / b)⁻¹ := by rw [inv_div, mul_div_cancel]
    rw [e]
    exact Formalism.L2.Host.HChar.LevelLe.mul ha (Formalism.L2.Host.HChar.LevelLe.inv h)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem gridBaseCharacter_unramified_off_badPlaces (j : Fin D.R.m) {P : HeightOneSpectrum (𝓞 D.host.E)} (hS : P.under (𝓞 D.host.F) ∉ S1 D) :
    (L.C.mu0 j).UnrAt P := by
  refine (L.C.isMu0 j).unr P fun k hk => hS ((S1_mem_OmF D).2 ?_)
  have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
    rw [map_natCast]; exact hk
  fin_cases k
  · exact Or.inl this
  · exact Or.inr (Or.inl this)

theorem exp_w (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ G.pl.S0) {c : ℕ} (hc : GlobalTheory.CMVal.ExpAt (nuH G t i j) (G.pl.w v) c) : c = condExp G.pl v := by
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hu := G.pl.under_w hv
  by_cases h0 : v = G.pl.v0
  · rw [condExp, if_pos h0]
    have hu0 : (G.pl.w v).under (𝓞 D.host.F) = G.pl.v0 := hu.trans h0
    obtain ⟨l1, l2⟩ := G.ch.lev0 _ a1 a2 _ hu0
    have hmu : (L.C.mu0 j).UnrAt (G.pl.w v) := gridBaseCharacter_unramified_off_badPlaces j (by rw [hu0]; exact G.ch.basePlace_not_mem_chiGridBadPlaces)
    have hxi : (L.xiH t).UnrAt (G.pl.w v) := by
      by_contra hn
      rcases (hL.Q_ram t _).1 hn with hq | ⟨PP', hq, hcj⟩
      · exact G.pl.levelPlace_ne_basePlace t _ hq hu0
      · exact G.pl.levelPlace_ne_basePlace t _ hq ((GlobalTheory.BadPlaceExp.under_eq_of_isConjPl hcj).trans hu0)
    exact exp_div (n := 0) hc (Formalism.L2.Host.HChar.UnrAt.levelLe (hmu.mul hxi) 0) l1
      (fun h => l2 ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h))
  · rw [condExp, if_neg h0]
    have h1 : v ∈ S1 D := (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left h0
    obtain ⟨l1, l2⟩ := G.ch.lev1 _ a1 a2 (G.pl.w v) (by rw [hu]; exact h1)
    exact exp_div (n := 1) hc (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame _) (hL.xi_tame t _)) l1 l2

theorem exp_twPl (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : P ∈ twPl G t) {c : ℕ} (hc : GlobalTheory.CMVal.ExpAt (nuH G t i j) P c) : c = 1 := by
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hP
    exact ⟨hP.1.resolve_left hP.2, hP.2⟩
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => by
    have e := G.pl.w_Q t P hP'.1 h
    refine hP'.2 ?_
    rw [e]
    exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
    (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t P hP'.1) hS1
  refine exp_eq (n := 0) hc ?_ fun h => nuH_not_unrAt_twPl G hL t i j P hP ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
  rw [nuH, div_eq_mul_inv]
  exact Formalism.L2.Host.HChar.LevelLe.mul (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame _) (hL.xi_tame t _))
    (Formalism.L2.Host.HChar.LevelLe.inv (Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ a1 a2 P hS0) _))

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ →
  ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ),
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, GlobalTheory.CMVal.ExpAt (GlobalTheory.FunObj.SqNum.nuH G t i j) w (c w)) →
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, 0 < c w) ∧ ∏ w ∈ GlobalTheory.FunObj.locPl G t, w.asIdeal ^ c w = GlobalTheory.SqTop.modT G t := by
  intro D T L sc G μ₀ hL t i j c hc
  have hW : ∀ v ∈ G.pl.S0, G.pl.w v ∈ locPl G t := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  have hT : ∀ P ∈ twPl G t, P ∈ locPl G t := fun P hP => (Finset.mem_filter.1 hP).1
  have h1 : ∀ v ∈ G.pl.S0, c (G.pl.w v) = condExp G.pl v := fun v hv => exp_w G hL t i j hv (hc _ (hW v hv))
  have h2 : ∀ P ∈ twPl G t, c P = 1 := fun P hP => exp_twPl G hL t i j hP (hc _ (hT P hP))
  refine ⟨fun w hw => ?_, ?_⟩
  · by_cases h : w ∈ G.pl.W0
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      rw [h1 v hv, condExp]
      split_ifs <;> omega
    · rw [h2 w (Finset.mem_filter.2 ⟨hw, h⟩)]
      omega
  · rw [← Finset.prod_filter_mul_prod_filter_not (locPl G t) (fun w => w ∈ G.pl.W0), modT]
    congr 1
    · have e : (locPl G t).filter (fun w => w ∈ G.pl.W0) = G.pl.S0.image G.pl.w := by
        ext w
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_union_left _ h, h⟩⟩
      rw [e, Finset.prod_image fun v hv v' hv' h =>
        (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv')), condE]
      exact Finset.prod_congr rfl fun v hv => by rw [h1 v hv]
    · refine Finset.prod_congr ?_ fun P hP => by rw [h2 P hP, pow_one]
      ext w
      simp only [twPl, Finset.mem_filter]

end GlobalTheory.NuExpModulus
end

section

open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.log_cmConstant_add_logDerivative_le_squareTopBound : ∀ ε : ℝ, ∃ Cx x₁ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (large₂ : Formalism.BasicNotions.SizeData₂ D), large₂.sc.eps = ε → x₁ ≤ large₂.sc.x → Rec large₂ → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) + (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤ bTH D Cx large₂.sc.x large₂.sc.b := by
  first | exact @GlobalTheory.SizesArch.sizes | exact GlobalTheory.SizesArch.sizes | (intros; apply GlobalTheory.SizesArch.sizes <;> assumption)
end
