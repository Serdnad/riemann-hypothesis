module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsColumnArrows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle486
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialSuperdiagonalOffException
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle487
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle488
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
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreOntoPar
open GlobalTheory.SignedHC GlobalTheory.PairLift Finset

theorem mem_dualPar' {S : SPar} {x : ℚ × Bool} : x ∈ dualPar S ↔ (-x.1, x.2) ∈ S := by
  simp only [dualPar, mem_image, Prod.exists]
  constructor
  · rintro ⟨a, b, h, he⟩
    rw [← he]; simpa using h
  · intro h; exact ⟨_, _, h, by simp⟩

theorem mem_block_neg {c y : ℚ} {t : ℕ} : y ∈ TPar.block (-c) t ↔ -y ∈ TPar.block c t := by
  rw [mem_block, mem_block]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨t - 1 - a, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  · rintro ⟨a, ha, h⟩
    refine ⟨t - 1 - a, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; linarith

theorem dual_partner (t : ℕ) (c : ℚ) (P : SPar) (hc : ∀ x ∈ P, x.1 ≠ c) :
    partner t true (-c) (-c) (dualPar P) = dualPar (GlobalTheory.SignedHC.flip (partner t false c c P)) := by
  ext ⟨y, b⟩
  rw [mem_dualPar', GlobalTheory.SignedHC.mem_flip]
  simp only [partner, mem_union, mem_image, Prod.exists, Prod.mk.injEq, mem_dualPar', sub_neg_eq_add,
    add_neg_cancel_right, sub_add_cancel]
  constructor
  · rintro (⟨a, b', h, rfl, h2⟩ | ⟨a, ha, rfl, rfl⟩)
    · left
      refine ⟨-a, b', h, rfl, ?_⟩
      have hne : -a ≠ c := hc _ h
      by_cases h1 : a < -c
      · have h3 : ¬ (-a < c) := by linarith
        rw [if_pos h1] at h2; rw [if_neg h3]; subst h2; simp
      · have h3 : -a < c := lt_of_le_of_ne (by linarith) hne
        rw [if_neg h1] at h2; rw [if_pos h3]; subst h2; simp
    · right; exact ⟨-a, mem_block_neg.1 ha, rfl, rfl⟩
  · rintro (⟨a, b', h, rfl, h2⟩ | ⟨a, ha, ha', hb⟩)
    · left
      have hne : -y ≠ c := hc _ h
      refine ⟨y, b', h, rfl, ?_⟩
      by_cases h1 : y < -c
      · have h3 : ¬ (-y < c) := by linarith
        rw [if_neg h3] at h2; rw [if_pos h1]; subst h2; simp
      · have h3 : -y < c := lt_of_le_of_ne (by linarith) hne
        rw [if_pos h3] at h2; rw [if_neg h1]; exact Bool.not_inj h2
    · right
      subst ha'
      refine ⟨y, mem_block_neg.2 ha, rfl, ?_⟩
      cases b
      · exact absurd hb (by decide)
      · rfl

theorem parOK_core : ParOK := by
  intro D hS i hi τ
  show GlobalTheory.EvenOnto.UpPair (GlobalTheory.ChiGrid.sLen D - 1) ((GlobalTheory.ChiGrid.num D 1 τ).parPi i) ((GlobalTheory.ChiGrid.num D 1 τ).parPi (i + 1)) _ _
  set G := GlobalTheory.ChiGrid.num D 1 τ with hGdef
  set c : ℚ := (GlobalTheory.ChiGrid.cen D 1 τ (D.R.m - i) : ℚ) with hc
  have hN : G.NearMid := GlobalTheory.ChiGrid.num_nearMid D 1 τ
  have hgp := (GlobalTheory.ChiGrid.isLeast_gap D 1).1
  have hγ : 2 * GlobalTheory.ChiGrid.bigN D ^ 3 + 2 * GlobalTheory.ChiGrid.sLen D + 2 < GlobalTheory.ChiGrid.gap D 1 := hgp.2.1
  have hr := hS.1
  have hsl : GlobalTheory.ChiGrid.sLen D = D.R.r + 6 := rfl
  have hrk : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hkm := D.R.m_add_three_le_k
  have hs1 : 1 ≤ G.s := show 1 ≤ GlobalTheory.ChiGrid.sLen D by omega
  have hq : G.s = 2 * (a + b + 2) + 1 := show GlobalTheory.ChiGrid.sLen D = _ by rw [hsl, hrk]; omega
  have hmN : D.R.m ≤ D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hN1 : 1800 < GlobalTheory.ChiGrid.bigN D := by unfold GlobalTheory.ChiGrid.bigN; omega
  have hγq : (G.s : ℚ) + 4 ≤ G.ga := by
    show (GlobalTheory.ChiGrid.sLen D : ℚ) + 4 ≤ (GlobalTheory.ChiGrid.gap D 1 : ℚ)
    exact_mod_cast (by omega : GlobalTheory.ChiGrid.sLen D + 4 ≤ GlobalTheory.ChiGrid.gap D 1)
  have hγ2 : 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 < G.ga := by
    show 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 < (GlobalTheory.ChiGrid.gap D 1 : ℚ)
    exact_mod_cast (by omega : 2 * GlobalTheory.ChiGrid.bigN D ^ 3 < GlobalTheory.ChiGrid.gap D 1)
  have hs0 : (0 : ℚ) ≤ G.s := by positivity
  have hsγ : (G.s : ℚ) ≤ G.ga := by linarith
  have hsq : (G.s : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) := rfl
  have hcastT : ((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ GlobalTheory.ChiGrid.sLen D by omega)]; simp
  have hfar : FarFrom c (((GlobalTheory.ChiGrid.sLen D : ℚ) + 2) / 2) (G.parPi i) :=
    GlobalTheory.ParPairArrows.far_parPi G hN hs1 hγq hi
  have hpart : partner (GlobalTheory.ChiGrid.sLen D - 1) false c c (G.parPi i) = GlobalTheory.SignedHC.flip (G.parPi (i + 1)) :=
    GlobalTheory.ParPairArrows.partner_parPi G hN hs1 hγq hi
  have hcne : ∀ x ∈ G.parPi i, x.1 ≠ c := fun x hx e => by
    have := hfar x.1 (fst_mem_entries hx)
    rw [e, sub_self, abs_zero] at this
    linarith
  have hflip : ∀ S : SPar, GlobalTheory.SignedHC.flip (GlobalTheory.SignedHC.flip S) = S := fun S => by
    ext ⟨x, s⟩; simp [mem_flip]
  have hP1 : partner (GlobalTheory.ChiGrid.sLen D - 1) true (-c) (-c) (dualPar (G.parPi i)) = dualPar (G.parPi (i + 1)) := by
    rw [dual_partner _ _ _ hcne, hpart, hflip]
  have hgapP : ∀ j, j ≤ D.R.m → GapOver (dualPar (G.parPi j)) (2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3) := by
    intro j hj x hx y hy hne
    rw [mem_dualPar'] at hx hy
    have := GlobalTheory.ParPairArrows.gap_parPi G hN hs1 hsγ hj _ hx _ hy hne
    have e : |(-x.1) - (-y.1)| = |x.1 - y.1| := by rw [show (-x.1) - (-y.1) = -(x.1 - y.1) by ring, abs_neg]
    rw [e] at this
    linarith
  have hne : (dualPar (G.parPi i)).Nonempty := by
    have h0 : (G.parPi i).Nonempty := ⟨_, GridData.mem_parPi.2 (Or.inl ⟨0, Nat.zero_le _, rfl⟩)⟩
    exact h0.image _
  have hreg : IsRegular (dualPar (G.parPi i)) := by
    intro x hx y hy e
    by_contra hne'
    rw [mem_dualPar'] at hx hy
    have := GlobalTheory.ParPairArrows.gap_parPi G hN hs1 hsγ hi.le _ hx _ hy hne'
    rw [e, sub_self, abs_zero] at this
    linarith
  have hco : InCoset (-c + (((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) + 1) / 2) (GlobalTheory.SignedHC.entries (dualPar (G.parPi i))) := by
    intro x hx
    obtain ⟨s', hs'⟩ := mem_entries.1 hx
    rw [mem_dualPar'] at hs'
    simp only at hs'
    obtain ⟨z, hz⟩ := GlobalTheory.ParPairArrows.inCoset_parPi G hq (GlobalTheory.ChiGrid.cen D 1 τ (D.R.m - i) - GlobalTheory.ChiGrid.sLen D) i (-x)
      (fst_mem_entries hs')
    have hcastG : ((G.s - 1 : ℕ) : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) - 1 := hcastT
    rw [hcastG] at hz
    push_cast at hz
    refine ⟨-z, ?_⟩
    rw [hcastT]; push_cast
    linarith
  have hfar' : FarFrom (-c) ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) + 1) / 2) (dualPar (G.parPi i)) := by
    intro x hx
    obtain ⟨s', hs'⟩ := mem_entries.1 hx
    rw [mem_dualPar'] at hs'
    simp only at hs'
    have := hfar _ (fst_mem_entries hs')
    simp only at this
    have e : |x - -c| = |-x - c| := by rw [show x - -c = -(-x - c) by ring, abs_neg]
    rw [hcastT, e]
    linarith
  have hcard : (dualPar (G.parPi i)).card + (GlobalTheory.ChiGrid.sLen D - 1) ≤ GlobalTheory.ChiGrid.bigN D := by
    have hc0 : (dualPar (G.parPi i)).card ≤ (G.parPi i).card := card_image_le
    have hc := GlobalTheory.ParPairArrows.card_parPi G i
    have h1 : (i + 1) * (GlobalTheory.ChiGrid.sLen D - 1) ≤ D.R.m * (GlobalTheory.ChiGrid.sLen D - 1) := Nat.mul_le_mul_right _ hi
    have h2 : (i + 1) * (GlobalTheory.ChiGrid.sLen D - 1) = i * (GlobalTheory.ChiGrid.sLen D - 1) + (GlobalTheory.ChiGrid.sLen D - 1) := Nat.succ_mul _ _
    have h3 : D.R.m * (GlobalTheory.ChiGrid.sLen D - 1) + D.R.m ≤ D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    change _ ≤ (D.R.m + 1) + (D.R.k - 1) + i * (GlobalTheory.ChiGrid.sLen D - 1) at hc
    show _ ≤ D.R.k + D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1)
    omega
  have hth := GlobalTheory.PairLift.FromSigned.thetaPar_partner (GlobalTheory.ChiGrid.sLen D - 1) true (-c) (-c) (dualPar (G.parPi i))
    (GlobalTheory.ChiGrid.bigN D) (by omega) hne hreg hco hfar' hcard hN1 (hgapP i hi.le) (by rw [hP1]; exact hgapP (i + 1) hi)
  obtain ⟨al, be, ga, de, hPe, (⟨hD, hP'⟩ | ⟨_, hP'⟩)⟩ := hth
  · refine ⟨al, be, ga, de, hD, ?_, ?_, ?_⟩
    · intro e he
      have hmem : ∃ s, (e + -c, s) ∈ dualPar (G.parPi i) := by
        rw [hPe]
        simp only [List.mem_append] at he
        rcases he with ((h | h) | h) | h
        · exact ⟨true, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inl ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨true, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inl ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨false, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨false, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [h]⟩)⟩
      obtain ⟨s, hs⟩ := hmem
      rw [mem_dualPar'] at hs
      simp only at hs
      have := hfar _ (fst_mem_entries hs)
      simp only at this
      have e1 : |-(e + -c) - c| = |e| := by rw [show -(e + -c) - c = -e by ring, abs_neg]
      rw [e1] at this
      rw [hcastT]
      linarith
    · rw [← hPe, dualPar_dualPar]
    · rw [← hP', hP1, dualPar_dualPar]
  · exfalso
    have hg := hgapP (i + 1) hi
    rw [← hP1, hP'] at hg
    have e0m : (((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 ∈ block (GlobalTheory.ChiGrid.sLen D - 1) :=
      GlobalTheory.PairLift.FromSigned.mem_blockList.2 ⟨0, by omega, by simp⟩
    have hf : ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 + -c, false) ∈
        GlobalTheory.Chain.signed (al ++ de) (ga ++ block (GlobalTheory.ChiGrid.sLen D - 1) ++ be) (-c) :=
      GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [e0m]⟩)
    have ht : ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 + -c, true) ∈
        GlobalTheory.Chain.signed (al ++ de) (ga ++ block (GlobalTheory.ChiGrid.sLen D - 1) ++ be) (-c) := by
      rw [← hP']
      refine mem_union.2 (Or.inr (mem_image.2 ⟨_, mem_block.2 ⟨0, by omega, ?_⟩, rfl⟩))
      push_cast; ring
    have := hg _ ht _ hf (by simp)
    simp only [sub_self, abs_zero] at this
    have : (0 : ℚ) ≤ 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 := by positivity
    linarith

end GlobalTheory.CoreOntoPar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.automorphic_cusp_forms_hermitianSpaceSignTwist : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (V : HSp D) (φ : GA D V → ℂ), (IsAutFunSm θ (sgn ε V) (fun g => φ (ofSgn ε V g)) ↔ IsAutFunSm θ V φ) ∧ (IsCuspFun (sgn ε V) (fun g => φ (ofSgn ε V g)) ↔ IsCuspFun V φ) := by
  first | exact @GlobalTheory.sgn_fun_cusp | exact GlobalTheory.sgn_fun_cusp | (intros; apply GlobalTheory.sgn_fun_cusp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.depthLatticeGridRow_stable_witt_projections : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (_ : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), u * ((F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX) ∈ latRow G (2 * σ + 2) ∧ u * ((F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY) ∈ latRow G (2 * σ + 2) := by
  first | exact @GlobalTheory.ProjLat.latRow_proj | exact GlobalTheory.ProjLat.latRow_proj | (intros; apply GlobalTheory.ProjLat.latRow_proj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.genericCharacter_trivial_superdiagonal_off_exceptional : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  first | exact @GlobalTheory.UniOff.uni_off | exact GlobalTheory.UniOff.uni_off | (intros; apply GlobalTheory.UniOff.uni_off <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColTypeLift

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

def FinCoef (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  ∀ x, ∃ (n : ℕ) (L : Fin n → (M.H τ →L[ℂ] ℂ)) (v : Fin n → M.H τ),
    (∀ i, SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v i)) ∧
    ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), φ (x * atTau θ V τ g) = ∑ i, L i (M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (v i))

theorem FinCoef.zero (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    FinCoef θ M τ 0 := fun _ => ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun g _ => by simp⟩

theorem FinCoef.add {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {φ ψ : GA D V → ℂ} (h₁ : FinCoef θ M τ φ) (h₂ : FinCoef θ M τ ψ) : FinCoef θ M τ (φ + ψ) := fun x => by
  obtain ⟨n₁, L₁, v₁, hv₁, e₁⟩ := h₁ x
  obtain ⟨n₂, L₂, v₂, hv₂, e₂⟩ := h₂ x
  refine ⟨n₁ + n₂, Fin.append L₁ L₂, Fin.append v₁ v₂, fun i => ?_, fun g hg => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using hv₁ i
    · simpa using hv₂ i
  · rw [Fin.sum_univ_add, Pi.add_apply, e₁ g hg, e₂ g hg]
    simp

theorem FinCoef.smul {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {φ : GA D V → ℂ} (c : ℂ) (h : FinCoef θ M τ φ) : FinCoef θ M τ (c • φ) := fun x => by
  obtain ⟨n, L, v, hv, e⟩ := h x
  refine ⟨n, fun i => c • L i, v, hv, fun g hg => ?_⟩
  rw [Pi.smul_apply, e g hg, Finset.smul_sum]
  simp

theorem FinCoef.sum {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {n : ℕ} {φ : Fin n → GA D V → ℂ} (h : ∀ i, FinCoef θ M τ (φ i)) : FinCoef θ M τ (∑ i, φ i) := by
  classical
  have : ∀ s : Finset (Fin n), FinCoef θ M τ (∑ i ∈ s, φ i) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using FinCoef.zero θ M τ
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih
  exact this Finset.univ

theorem finCoef_lift {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (z : SmT M) : FinCoef θ M τ (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    intro x
    obtain ⟨ℓ, -, hℓ⟩ := GlobalTheory.DefiniteEnd.exists_sobCont M τ T f x
    have hsv : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (f τ : M.H τ) := by
      have hw : ∀ w ∈ M.sm τ, SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) w := by
        intro w hw
        rw [GlobalTheory.SmVec.sm_eq M τ] at hw
        exact hw
      exact hw _ (f τ).2
    refine ⟨1, fun _ => r • LinearMap.toContinuousLinearMap ℓ, fun _ => (f τ : M.H τ), fun _ => hsv, fun g hg => ?_⟩
    have e1 := congrFun (hT.equiv τ g hg f ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩ rfl) x
    have e3 : T f (x * atTau θ V τ g) = ℓ (M.rep τ g (f τ)) := by
      rw [hℓ ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩]
      exact e1.symm
    rw [Fin.sum_univ_one, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, e3, LinearMap.coe_toContinuousLinearMap']
    rfl
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact ha.add hb

end GlobalTheory.ColTypeLift

namespace GlobalTheory.ColTypeLift

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem finCoef_multT {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] (F : MultT θ M ∅ 1) (z : SmT M) : FinCoef θ M τ (F.1 z) := by
  have hm : PiTensorProduct.lift.symm F.1 ∈ Mult θ M ∅ 1 := (mem_multT θ M ∅ 1 F.1).1 F.2
  have key : ∀ T ∈ Mult θ M ∅ 1, FinCoef θ M τ (PiTensorProduct.lift T z) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem x hx => exact finCoef_lift M τ hx z
    | zero => simpa using FinCoef.zero θ M τ
    | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply]; exact hx.add hy
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply]; exact hx.smul c
  have := key _ hm
  rwa [LinearEquiv.apply_symm_apply] at this

theorem isTypeAt_sum (θ : InfFam D) (N : Node D) (hs : N.V.SigOK) (hd : N.V.IsDefinite) (τ : D.what₂.Tau) {n : ℕ}
    (F : Fin n → N.Cusp θ) (z : Fin n → SmT N.M) : IsTypeAt θ N.V τ (N.S τ) (∑ i, (F i).1 (z i)) := by
  haveI := GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  exact GlobalTheory.EndCusp.isTypeAt_of_finSum θ N.V τ (N.M.enum τ) (N.M.ds τ) (N.M.fr_unit τ) (N.M.fr_gram τ) _
    (FinCoef.sum fun i => finCoef_multT N.M τ (F i) (z i))

theorem xp_definite {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R} (hG : G.Is)
    (k : ℕ) (hk : k ≤ D.R.m) : (G.Xp k).V.SigOK ∧ (G.Xp k).V.IsDefinite := by
  cases k with
  | zero =>
    have h := hG.spaces.P D.R.m le_rfl
    refine ⟨h.sigOK, fun τ => Or.inl ?_⟩
    rw [h.sig, h.rank]
    simp
  | succ k =>
    have h := hG.spaces.X k hk
    refine ⟨h.sigOK, fun τ => Or.inl ?_⟩
    rw [h.sig, h.rank]
    simp

end GlobalTheory.ColTypeLift
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.testChoices_exist_largeCoeffField_adelicData : GlobalTheory.RowEx.ExField → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLg fun K B f T => ∀ (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (L : SizeData₂ (w.st Z).toD7), L.sc = K.s → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 → ∃ ch : GlobalTheory.RowTest.Choice z.R.toRealDat, ch.Is ∧ ch.AtScale CF L.sc.b ∧ ch.FieldOK := by
  exact @GlobalTheory.RowEx.dat_choice_exists
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitChoose

theorem isUnit_two_of_not_mem : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    IsUnit (2 : v.adicCompletionIntegers F) := by
  intro F _ _ v h
  have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h
  rwa [map_ofNat] at this

theorem exists_admissible_unipotent_splitPlace_alt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v hv hψ h2 g hg
  obtain ⟨π₁, π₂, b₁, b₂, hP, hS⟩ := GlobalTheory.T.exists_local_dictionary_splitPlace σ B W r s hB hW v hv hψ
  exact GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt GlobalTheory.T.exists_dual_pair_isUnit_det_blocks' σ W v hW.skew (isUnit_two_of_not_mem v h2) π₁ π₂ b₁ b₂ hP hS g hg

end GlobalTheory.SplitChoose
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.squareTriple_finitePlaces_of_orientedRoutes : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m),
    SquareStanding G t → ∀ (M : Vol G), M.Is t → ∀ (en : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G ↑i ↑j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G ↑i ↑j) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) om om',
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t ↑i ↑j en Bs Γ X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      (GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t ↑i ↑j) ∧ GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G ↑i ↑j)) ∨
      (¬ GlobalTheory.WeilParts.NonSplitAt D v ε ∧ ¬ GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t ↑i ↑j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G ↑i ↑j) ∧
        ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.TripleRam.ram_clause | exact GlobalTheory.TripleRam.ram_clause | (intros; apply GlobalTheory.TripleRam.ram_clause <;> assumption)
end
