module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle002
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle126
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.OneLetterJetKernel
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle004
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle127
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary

@[expose] public section

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob alG capG lsG deLoss dSet lgN DivAB)
open Formalism.GrowthSums (excessGain)
open Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights (young_second_row_length_count yd_size yd_one_le_colLen yd_colLen_le)
open Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel (tieFrame)

namespace GlobalTheory.KerGaussA

theorem card_height_one (μ : YoungDiagram) :
    (Finset.univ.filter (fun c : Fin (μ.rowLen 0) => μ.colLen c = 1)).card = μ.rowLen 0 - μ.rowLen 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (μ.rowLen 0))))
    (fun c => 2 ≤ μ.colLen c)
  rw [young_second_row_length_count, Finset.card_univ, Fintype.card_fin] at h
  have e : (Finset.univ.filter (fun c : Fin (μ.rowLen 0) => μ.colLen c = 1)) =
      Finset.univ.filter (fun c : Fin (μ.rowLen 0) => ¬ 2 ≤ μ.colLen c) := by
    ext c
    have := yd_one_le_colLen μ c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [e]; omega

theorem mem_dSet {ν : ℕ} [NeZero ν] (TT : Finset (ZMod (2 * ν))) (s : ZMod (2 * ν)) (e : ℕ) :
    2 * e + 1 ∈ dSet TT s ↔ (2 * e + 1 < 2 * ν ∧ s + ((2 * e + 1 : ℕ) : ZMod (2 * ν)) ∈ TT) := by
  have hν : 0 < ν := Nat.pos_of_ne_zero (NeZero.ne ν)
  have : NeZero (2 * ν) := ⟨by omega⟩
  unfold dSet
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨s', ⟨h1, -⟩, h3⟩
    refine ⟨h3 ▸ ZMod.val_lt _, ?_⟩
    rw [← h3, ZMod.natCast_zmod_val]
    simpa using h1
  · rintro ⟨h1, h2⟩
    refine ⟨_, ⟨h2, ?_⟩, ?_⟩
    · rw [ZMod.val_add, ZMod.val_cast_of_lt h1, Nat.mod_mod_of_dvd _ (Dvd.intro ν rfl)]
      omega
    · rw [add_sub_cancel_left, ZMod.val_cast_of_lt h1]

theorem tsum_odd (f : ℕ → ℝ) (hf : ∀ e, ¬ Odd e → f e = 0) : ∑' e : ℕ, f (2 * e + 1) = ∑' e : ℕ, f e := by
  refine Function.Injective.tsum_eq (g := fun e : ℕ => 2 * e + 1) (fun a b h => by simpa using h) ?_
  intro e he
  have ho : Odd e := by
    by_contra h
    exact he (hf e h)
  obtain ⟨k, hk⟩ := ho
  exact ⟨k, hk.symm⟩

theorem constantCoeff_sumE {K ι : Type} [Field K] [Fintype ι] {N0 N1 : ℕ} (be : MvPowerSeries (Fin 2) K)
    (h : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.constantCoeff (sumE (ι := ι) (N0 := N0) (N1 := N1) be) = 0 := by
  unfold sumE

  rw [map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  refine MvPowerSeries.constantCoeff_subst_eq_zero ?_ ?_ h
  · exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun a => by simp)
  · intro a; simp

theorem exists_root_sq (l : ℕ) [hl : Fact l.Prime] : ∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1) := by
  have h1 : 1 < l ^ 2 := by have := hl.out.two_le; nlinarith
  refine Formalism.L2.Th1.D.kurRoots l (l ^ 2 - 1) (by omega) fun hd => ?_
  have h2 : l ∣ l ^ 2 := dvd_pow_self l two_ne_zero
  have h3 : l ∣ 1 := by
    have := (Nat.dvd_sub h2 hd)
    rwa [Nat.sub_sub_self h1.le] at this
  exact hl.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem exists_pi (l : ℕ) [hl : Fact l.Prime] : ∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l]) := by
  have h1 : 1 < l ^ 2 := by have := hl.out.two_le; nlinarith
  exact IsAlgClosed.exists_pow_nat_eq _ (by omega)

theorem kernel_bound (l : ℕ) [Fact l.Prime] (ν m N0 N1 : ℕ) [NeZero ν] (hm : m = ν) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin m → MaximalUnramifiedExtension l)
    (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) (hF : IsLawOfLog l F) (h1 : F1 F be0) (h2 : F2 l σ be0)
    (hO : OwOK (2 * ν) σ om oms) (hT : TrDual (2 * ν) σ om oms)
    (U0 : MvPowerSeries (Bool × Fin m × Fin N0 × Fin N1) ℂ_[l]) (hU : Formalism.DworkPowerSeriesWeights.Integral U0)
    (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (hp : ∀ s c, hts s c ≤ N0) (I : ∀ s c, Fin (hts s c) → Fin N1) (n : (ZMod (2 * ν) × Fin N0 × Fin N0) →₀ ℕ) :
    ‖AddMonoidAlgebra.coeff (Formalism.DworkPowerSeriesWeights.frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms
        (Formalism.DworkPowerSeriesWeights.mvExp (-(sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))) * U0))) n‖ ≤
      (l : ℝ) ^ (-(excessGain (l : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss l N0 N1 TT (alG TT colN hts) (lsG TT colN hts)))) := by
  subst hm
  have : CompleteSpace (MaximalUnramifiedExtension l) := Formalism.L2.Th1.D.kurComplete l
  have hb : MvPowerSeries.constantCoeff (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0) = 0 := by
    have h0 : MvPowerSeries.constantCoeff be0 = 0 := h1.1 0 (Or.inl rfl)
    rw [MvPowerSeries.constantCoeff_map, h0, map_zero]
  exact (Formalism.L2.Th1.D.kernelOfF l (MaximalUnramifiedExtension l) σ hσ (exists_root_sq l) F hF be0 h1 h2 ℂ_[l] (MaximalUnramifiedExtension l).subtype m N0 N1
    (fun _ => rfl) (exists_pi l) om oms hO hT U0 _ hU (constantCoeff_sumE _ hb)
    ((Formalism.InvariantFactorPaths.G7.equivalence_rules ℂ_[l] _).1 _) TT colN hts hp I n).1

theorem kvalGe_gainA : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (be : MvPowerSeries (ZMod Lc.d) ℂ_[Lc.l]), ‖ep‖ = 1 → BeStd Lc.l Lc.d be → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) be → product_zeroth_first_parts.KvalGe Lc.N0 Lc.N1 Lc.l Lc.nu Lc.Th (gainA Lc) := by
  rintro Lc ep be hep ⟨σ, F, be0, om, oms, ζ, hD, rfl⟩ hB
  obtain ⟨U0, hU, hTh⟩ := GlobalTheory.T.exists_integral_orbit_series Lc ep σ F be0 om oms ζ hD hB
  have hp : ∀ s (c : Fin ((Lc.nu s).rowLen 0)), (Lc.nu s).colLen c ≤ Lc.N0 :=
    fun s c => (yd_colLen_le _ _).trans (Lc.nu_rows s)
  refine tieFrame Lc.l Lc.d Lc.N0 Lc.N1 Lc.nu hp Lc.Th ep _ hep ?_
  intro I n
  rw [hTh]
  clear hTh hB
  obtain ⟨hσ, hF, h1, h2, hO, hT, -⟩ := hD
  obtain ⟨J, rank_lt_alt, nu, hnu, TT⟩ := Lc
  obtain @⟨l, hl, h5, d, hd, hev, h2d, N0, N1, Th⟩ := J
  obtain ⟨ν, hν⟩ : ∃ ν, d = 2 * ν := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k, by omega⟩
  subst hν
  have : NeZero ν := ⟨by omega⟩
  refine (kernel_bound l ν (2 * ν / 2) N0 N1 (by omega) σ F be0 om oms hσ hF h1 h2 hO hT U0 hU TT
    (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) hp I n).trans (le_of_eq ?_)
  set Lc : product_zeroth_first_parts.Loc := ⟨⟨l, h5, 2 * ν, hev, h2d, N0, N1, Th⟩, rank_lt_alt, nu, hnu, TT⟩ with hLc
  have hal : alG TT (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) = alLoc Lc := by
    funext s
    unfold alG alLoc
    by_cases hs : s ∈ TT
    · rw [if_pos hs, if_pos (show s ∈ Lc.TT from hs)]
      exact card_height_one _
    · rw [if_neg hs, if_neg (show s ∉ Lc.TT from hs)]
  have hcap : capG TT (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) = Lc.cap := by
    funext s
    unfold capG
    rw [hal]
    unfold alLoc product_zeroth_first_parts.Loc.cap
    have hle : (nu s).rowLen 1 ≤ (nu s).rowLen 0 := (nu s).rowLen_anti 0 1 (Nat.zero_le _)
    by_cases hs : s ∈ Lc.TT
    · rw [if_pos hs, if_pos hs]
      show (nu s).rowLen 0 - ((nu s).rowLen 0 - (nu s).rowLen 1) = (nu s).rowLen 1
      omega
    · rw [if_neg hs, if_neg hs]
      rfl
  have hls : lsG TT (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) = fun s => Lc.size s - alLoc Lc s := by
    funext s
    unfold lsG
    rw [hal, ← yd_size]
    rfl
  rw [hcap, hls, hal]
  congr 2
  unfold excessGain gainA deLoss
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← tsum_odd _ (fun e he => if_neg (fun h => he h.1))]
  refine tsum_congr fun e => ?_
  have ho : Odd (2 * e + 1) := ⟨e, rfl⟩
  by_cases h : 2 * e + 1 ∈ dSet TT s
  · rw [if_pos h, if_neg (fun h' => h'.2 ((mem_dSet TT s e).1 h))]
  · rw [if_neg h, if_pos ⟨ho, fun h' => h ((mem_dSet TT s e).2 h')⟩]

end GlobalTheory.KerGaussA
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.ThLoc.ModelThree

theorem norm_add_of_lt {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem norm_sub_le_max' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_le_one_of_lt {K : Type} [NormedField K] [IsUltrametricDist K] {α β : K} (hlt : ‖α‖ < ‖β‖)
    (hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1) : ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1 := by
  have hb : 0 < ‖β‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have h1 : ‖α ^ 2 - α * β‖ < ‖β ^ 2‖ := by
    refine lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt ?_ ?_)
    · rw [norm_pow, norm_pow]; exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
    · rw [norm_mul, norm_pow, sq]; exact mul_lt_mul_of_pos_right hlt hb
  have h2 : ‖β ^ 2 + (α ^ 2 - α * β)‖ = ‖β ^ 2‖ := norm_add_of_lt h1
  have h3 : α ^ 2 - α * β + β ^ 2 = β ^ 2 + (α ^ 2 - α * β) := by ring
  rw [h3, h2, norm_pow] at hN
  have h4 : ‖β‖ ≤ 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  exact ⟨(hlt.trans_le h4).le, h4⟩

theorem norm_le_one_of_disc {K : Type} [NormedField K] [IsUltrametricDist K] {α β : K}
    (h : ‖α * β * (α - β)‖ = 1) (hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1) : ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1 := by
  rcases lt_trichotomy ‖α‖ ‖β‖ with hlt | heq | hgt
  · exact norm_le_one_of_lt hlt hN
  · have hc : ‖α - β‖ ≤ ‖α‖ := by
      refine (norm_sub_le_max' _ _).trans ?_
      rw [heq, max_self]
    rcases hc.lt_or_eq with hc | hc
    · have h1 : ‖(α - β) ^ 2‖ < ‖α * β‖ := by
        rw [norm_pow, norm_mul, ← heq, ← sq]
        exact pow_lt_pow_left₀ hc (norm_nonneg _) (by norm_num)
      have h2 : ‖α * β + (α - β) ^ 2‖ = ‖α * β‖ := norm_add_of_lt h1
      have h3 : α ^ 2 - α * β + β ^ 2 = α * β + (α - β) ^ 2 := by ring
      rw [h3, h2, norm_mul, ← heq] at hN
      have h4 : ‖α‖ ≤ 1 := by
        by_contra hc'
        push Not at hc'
        nlinarith
      exact ⟨h4, heq ▸ h4⟩
    · rw [norm_mul, norm_mul, hc, ← heq] at h
      have h4 : ‖α‖ ^ 3 = 1 := by rw [← h]; ring
      have h5 : ‖α‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4
      exact ⟨h5.le, (heq ▸ h5).le⟩
  · have hN' : ‖β ^ 2 - β * α + α ^ 2‖ ≤ 1 := by
      have : β ^ 2 - β * α + α ^ 2 = α ^ 2 - α * β + β ^ 2 := by ring
      rw [this]; exact hN
    exact (norm_le_one_of_lt hgt hN').symm

theorem exists_roots {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (g2 g3 : K) :
    ∃ α β : K, 16 * (α ^ 2 - α * β + β ^ 2) = 12 * g2 ∧
      64 * (α + β) ^ 3 - 288 * (α + β) * (α * β) = 216 * g3 := by
  let f : Polynomial K := Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C g2 * Polynomial.X - Polynomial.C g3
  have hdeg : f.degree ≠ 0 := by
    have h3 : f.natDegree = 3 := by
      simp only [f]
      compute_degree!
    intro h
    have h0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 h.le
    omega
  obtain ⟨e, he⟩ := IsAlgClosed.exists_root f hdeg
  have he' : 4 * e ^ 3 - g2 * e - g3 = 0 := by simpa [f, Polynomial.IsRoot] using he
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (g2 - 3 * e ^ 2) (n := 2) (by norm_num)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  refine ⟨(-3 * e + s) / 2, (-3 * e - s) / 2, ?_, ?_⟩
  · field_simp
    linear_combination (48 : K) * hs
  · have e1 : g3 = 4 * e ^ 3 - g2 * e := by linear_combination -he'
    rw [e1]
    field_simp
    linear_combination (-1728 * e : K) * hs

def twoTorsionModel {K : Type} [Field K] (α β : K) : WeierstrassCurve K := ⟨0, -(α + β), 0, α * β, 0⟩

theorem c₄_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).c₄ = 16 * (α ^ 2 - α * β + β ^ 2) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, twoTorsionModel]
  ring

theorem c₆_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).c₆ = 64 * (α + β) ^ 3 - 288 * (α + β) * (α * β) := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, twoTorsionModel]
  ring

theorem Δ_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).Δ = 16 * (α * β * (α - β)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, twoTorsionModel]
  ring

theorem norm_two : ‖(2 : ℂ_[3])‖ = 1 := by
  have e : (2 : ℂ_[3]) = algebraMap ℚ_[3] ℂ_[3] ((2 : ℕ) : ℚ_[3]) := by rw [map_natCast]; norm_num
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  norm_num

theorem exists_model (g2 g3 : ℂ_[3]) (hΔ : g2 ^ 3 - 27 * g3 ^ 2 = 1) (hj : ‖1728 * g2 ^ 3‖ ≤ 1) :
    ∃ W : WeierstrassCurve ℂ_[3], Formalism.L2.Th1.A.g₂ W = g2 ∧ Formalism.L2.Th1.A.g₃ W = g3 ∧ IntCurve W := by
  obtain ⟨α, β, h4, h6⟩ := exists_roots g2 g3
  have c4 : (twoTorsionModel α β).c₄ = 12 * g2 := by rw [c₄_model, h4]
  have c6 : (twoTorsionModel α β).c₆ = 216 * g3 := by rw [c₆_model, h6]
  have hD : (twoTorsionModel α β).Δ = 1 := by
    have hc := (twoTorsionModel α β).c_relation
    rw [c4, c6] at hc
    have : (1728 : ℂ_[3]) * (twoTorsionModel α β).Δ = 1728 * (g2 ^ 3 - 27 * g3 ^ 2) := by
      linear_combination hc
    exact (mul_left_cancel₀ (by norm_num) this).trans hΔ
  have n16 : ‖(16 : ℂ_[3])‖ = 1 := by
    have : (16 : ℂ_[3]) = 2 ^ 4 := by norm_num
    rw [this, norm_pow, norm_two, one_pow]
  have hprod : ‖α * β * (α - β)‖ = 1 := by
    have h1 := congrArg norm hD
    rw [Δ_model, norm_mul, n16, one_mul, norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  have hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1 := by
    have e : (16 * (α ^ 2 - α * β + β ^ 2)) ^ 3 = 1728 * g2 ^ 3 := by rw [h4]; ring
    have h1 : ‖(16 * (α ^ 2 - α * β + β ^ 2)) ^ 3‖ ≤ 1 := by rw [e]; exact hj
    rw [norm_pow, norm_mul, n16, one_mul] at h1
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  obtain ⟨ha, hb⟩ := norm_le_one_of_disc hprod hN
  refine ⟨twoTorsionModel α β, ?_, ?_, ?_⟩
  · unfold Formalism.L2.Th1.A.g₂
    rw [c4]; field_simp
  · unfold Formalism.L2.Th1.A.g₃
    rw [c6]; field_simp
  · refine ⟨by simp [twoTorsionModel], ?_, by simp [twoTorsionModel], ?_, by simp [twoTorsionModel], ?_⟩
    · simp only [twoTorsionModel, norm_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · simp only [twoTorsionModel, norm_mul]
      exact mul_le_one₀ ha (norm_nonneg _) hb
    · rw [hD, norm_one]

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_iota_le_one (ι : ℂ ≃+* ℂ_[3]) {x : ℂ} (hx : IsIntegral ℤ x) : ‖ι x‖ ≤ 1 := by
  obtain ⟨f, hf, hr⟩ := hx
  refine norm_le_one_of_isIntegral ⟨f, hf, ?_⟩
  have h := congrArg (ι : ℂ →+* ℂ_[3]) hr
  rw [map_zero, Polynomial.hom_eval₂] at h
  have e : (@algebraMap ℤ ℂ_[3] _ _ (Ring.toIntAlgebra ℂ_[3])) = (ι : ℂ →+* ℂ_[3]).comp (algebraMap ℤ ℂ) :=
    Subsingleton.elim _ _
  rw [e]
  exact h

theorem goodModelThree : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ ι : ℂ ≃+* ℂ_[3], ∃ W : WeierstrassCurve ℂ_[3], Unif 3 (cmL a₀ b₀ D.host.d ha hd lam hlam) ι W ∧ IntCurve W := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hL ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hLdef
  have hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have hL' : (L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair (TaylorLogMetric.lamOf D cc δ) L hL'
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
    rw [← e2, ← e3]
    exact h
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d L :=
    Formalism.L2.Th1.F.hasCMByScale D.host.d _ lam hlam (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ D.host.d ha hd hok.1
      (Formalism.L2.Th1.H.CmData.odd_b a₀ b₀ c₀ D.host.d hok.1 hok.2.2.1))
  have hd8 := hok.2.2.1
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv L) :=
    hIn.jInt D.host.d L hok.2.2.2.prime.squarefree (by omega) hcm
  have hj' : Formalism.L2.Th1.CM.jInv L = 1728 * L.g₂ ^ 3 := by
    unfold Formalism.L2.Th1.CM.jInv
    rw [hdisc, div_one]
  rw [hj'] at hj
  have hn := norm_iota_le_one ι hj
  have hΔ : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 = 1 := by
    have := congrArg ι hdisc
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_one] using this
  have hn' : ‖1728 * ι L.g₂ ^ 3‖ ≤ 1 := by
    simpa only [map_mul, map_pow, map_ofNat] using hn
  obtain ⟨W, h2, h3, hW⟩ := exists_model _ _ hΔ hn'
  exact ⟨W, ⟨h2, h3⟩, hW⟩

end GlobalTheory.ThLoc.ModelThree
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualJumps_mem_window_box : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG), Roomy L C → ∀ a, (∀ u ∈ jT1 (hcAt D (g a)) j (pos ε (g a)), u ∈ (recWord L j ε g).win a ∧ u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ)) ∧ (∀ u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)), u ∈ jT1 (hcAt D (g a)) j (pos ε (g a))) ∧ ∑ u ∈ Finset.Icc (-(etaHat L : ℤ)) (etaHat L), (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) ≤ D.R.m := by
  first | exact @GlobalTheory.HTW.Rec.recWord_jumps | exact GlobalTheory.HTW.Rec.recWord_jumps | (intros; apply GlobalTheory.HTW.Rec.recWord_jumps <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualSizeWord_long_orbit_small_prime : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C C₂ : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 2 * C₂ ≤ C → 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf ψ.2 → WordsB L l C₂ (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.wordsB_recWord_of_long_orbit | exact GlobalTheory.HTW.Rec.wordsB_recWord_of_long_orbit | (intros; apply GlobalTheory.HTW.Rec.wordsB_recWord_of_long_orbit <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

theorem _root_.GlobalTheory.T.rowTypeCharacter_blockSumOne_eq : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N n : ℕ} (hN : N = n + 1) (r : ℕ), r ≤ n → ∀ j : Sp E n ≃ₗ[E] Sp E n, LocE.lamQB ξ r N (sumE hN j 1).toLinearMap = LocE.lamQB ξ r n j.toLinearMap := by
  first | exact @GlobalTheory.SumRowType.lamQB_sumE | exact GlobalTheory.SumRowType.lamQB_sumE | (intros; apply GlobalTheory.SumRowType.lamQB_sumE <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

theorem _root_.GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Fin n → kˣ) V) (x : V) (θ : Fin n → kˣ →* ℂˣ), IsSmooth ρ → HasFiniteLength ρ → (∀ i, IsSmoothChar (θ i)) → x ≠ 0 → (∀ t ∈ torusO k (Fin n), ρ t x = (torusChar θ t : ℂ) • x) → ∃ (ψ : Fin n → kˣ →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ t y, l (ρ t y) = (torusChar ψ t : ℂ) * l y) ∧ ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u := by
  first | exact @GlobalTheory.TorusEigenform.main | exact GlobalTheory.TorusEigenform.main | (intros; apply GlobalTheory.TorusEigenform.main <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

theorem _root_.GlobalTheory.T.prinSeries_append_isSubquotient_prod₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W), Nonempty (A.Equiv (prinSeries ψ₁)) → Nonempty (B.Equiv (prinSeries ψ₂)) → IsSubquotient (prinSeries (Fin.append ψ₁ ψ₂)) (prod₂ A B) := by
  first | exact @GlobalTheory.SmGL.PrinProd.prinSeries_append | exact GlobalTheory.SmGL.PrinProd.prinSeries_append | (intros; apply GlobalTheory.SmGL.PrinProd.prinSeries_append <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem acris_mem_clos : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ (ϖ : Per.Fl l),
  (∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ) → (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ x : Per.Acris l, j x ∈ Clos (Sg ϖ) (betaD ϖ) := by
  intro l _ j hj ϖ hS hF x n
  obtain ⟨N, hN⟩ := hj.bdd n
  obtain ⟨s, z, rfl⟩ := (acris_basic l).2.2.1 x N
  obtain ⟨a, ha⟩ := hN z
  refine ⟨algebraMap (Per.AinfP l) (Per.BdRp l) ((s : Per.AinfP l) + algebraMap (Per.Ainf l) (Per.AinfP l) a),
    ⟨_, add_mem (hS s) (Subalgebra.algebraMap_mem _ a), rfl⟩, ?_⟩
  rw [← Ideal.mem_span_singleton, ← hF, GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, map_add (f := _), map_add (f := _), map_mul, map_pow,
    map_natCast, hj.on0, ev_algebraMap, ev_algebraMap]
  rw [ha, map_add (f := _)]
  ring

end GlobalTheory.Pst.StLat
end
