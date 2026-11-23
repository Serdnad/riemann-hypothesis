module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle002
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle019
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle022
public import Formalism.PeriodIntegrals.Bundle018
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle003
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogClosed
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle009
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SpansOverField

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameTwistCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (CZ)
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix

attribute [local instance] Over.cartesianMonoidalCategory

section Series

open MvPowerSeries

variable {S : Type} [CommRing S]

variable {n d : ℕ}

variable {c : Fin d → Fin d → S} {P Q : Pt S n d}

variable [Algebra ℚ S]



omit [Algebra ℚ S] in
theorem cc_pt (j : Fin n) (i : Fin d) : constantCoeff (pt S d j i) = 0 := by
  simp [pt]


end Series

section Jets

open MvPolynomial

variable {S : Type} [CommRing S] {d : ℕ}

theorem jetSubstP_psJet {n n' : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    {a : Fin n → Pt S n' d} (ha : CZ a) (hφ : ∀ p, constantCoeff (φ p) = 0)
    (hmk : ∀ p : Fin n × Fin d,
      Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (φ p) = psJet m (a p.1 p.2))
    (f : PS S n d) : jetSubstP m φ (psJet m f) = psJet m (ev a f) := by
  rw [ev, FBIdJet.psJet_subst m _ (fun p => ha p.1 p.2) f]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [GermD.jetMap_mk, aeval_X]
  simp only [jetSubstP, GermD.jetMap_mk, aeval_X, hφ p, map_zero, sub_zero]
  rw [hmk p]
  rfl

theorem mk_psIn_psJet {n' : ℕ} (m : ℕ) (k : Fin n') (f : PS S 1 d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (psIn d m ![k] f) =
      psJet m (ev ![pt S d k] f) := by
  have e : (![pt S d k] : Fin 1 → Pt S n' d) = fun i => pt S d ((![k] : Fin 1 → Fin n') i) := by
    funext i; fin_cases i; rfl
  rw [e, FBIdPh.psJet_ev_rel, psIn, FBIdPh.mk_rename]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [GermD.jetMap_mk, aeval_X]
  simp only [jetSubstP, GermD.jetMap_mk, aeval_X, FBIdPh.rel, constantCoeff_X, map_zero, sub_zero]

theorem cz_left {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    CZ (![comp1 φ (pt S d 0), pt S d 1] : Fin 2 → Pt S 2 d) := by
  intro j i
  fin_cases j
  · exact (TB.LogPf.cc_ev TB.LogPf.czX _).trans (hφ i)
  · exact cc_pt _ i

theorem cz_right {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    CZ (![pt S d 0, comp1 φ (pt S d 1)] : Fin 2 → Pt S 2 d) := by
  intro j i
  fin_cases j
  · exact cc_pt _ i
  · exact (TB.LogPf.cc_ev TB.LogPf.czY _).trans (hφ i)

theorem jetSubstP_left (m : ℕ) {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (f : PS S 2 d) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (φ j), fun j => X ((1 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m f) =
      psJet m (ev (n := 2) ![comp1 φ (pt S d 0), pt S d 1] f) := by
  refine jetSubstP_psJet m _ (cz_left hφ) ?_ ?_ f
  · rintro ⟨i, j⟩
    fin_cases i
    · exact (FBIdPh.cc_psIn d m _ _).trans (hφ j)
    · simp
  · rintro ⟨i, j⟩
    fin_cases i
    · exact mk_psIn_psJet m 0 (φ j)
    · exact (FBIdSy.mk_psTrunc_X m _).symm

theorem jetSubstP_right (m : ℕ) {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (f : PS S 2 d) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (φ j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m f) =
      psJet m (ev (n := 2) ![pt S d 0, comp1 φ (pt S d 1)] f) := by
  refine jetSubstP_psJet m _ (cz_right hφ) ?_ ?_ f
  · rintro ⟨i, j⟩
    fin_cases i
    · simp
    · exact (FBIdPh.cc_psIn d m _ _).trans (hφ j)
  · rintro ⟨i, j⟩
    fin_cases i
    · exact (FBIdSy.mk_psTrunc_X m _).symm
    · exact mk_psIn_psJet m 1 (φ j)

variable [Algebra ℚ S]

end Jets

section Frames

open MvPolynomial (X)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} {d : ℕ}
variable {x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G}

variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
  {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} {e e' : ∀ m, FrTy y d x m}

end Frames

section Clauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]
variable (y : FrPt Xo c S) (C : ChartAt Xo c y)

end Clauses

end GlobalTheory.FrameTwistCompare
end
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselPeriodCompare

open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open Formalism.FourierDecayAlt.B2 (IsClosedSubgroup mulM invM)
open Formalism.FourierDecayAlt.P.B2x1
open GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient (Mat leviW IsClosedMatGroup)

variable {k r : ℕ}

theorem exists_pos_lt_top {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (h : μ ≠ 0) : ∃ t : Set X, μ t ≠ 0 ∧ μ t ≠ ⊤ := by
  have h0 : (0 : ℝ≥0∞) < μ Set.univ := by
    rw [pos_iff_ne_zero]; exact fun h' => h (Measure.measure_univ_eq_zero.mp h')
  obtain ⟨t, -, -, h1, h2⟩ := Measure.exists_subset_measure_lt_top MeasurableSet.univ h0
  exact ⟨t, h1.ne', h2.ne⟩

theorem haar_unique {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : PI.BesselPeriodGGP.IsHaarOn U ν) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  obtain ⟨m1, m2, m3, m4⟩ := hμ
  obtain ⟨n1, n2, n3, n4⟩ := hν
  have em : (pull hU μ).map inc = μ := map_pull μ m3
  have en : (pull hU ν).map inc = ν := map_pull ν n3
  have : (pull hU μ).IsMulLeftInvariant := pull_left μ m4
  have : (pull hU ν).IsMulLeftInvariant := pull_left ν n4
  have : SigmaFinite (pull hU μ) :=
    SigmaFinite.of_map _ inc_memb.measurable.aemeasurable (by rw [em]; exact m1)
  have : SigmaFinite (pull hU ν) :=
    SigmaFinite.of_map _ inc_memb.measurable.aemeasurable (by rw [en]; exact n1)
  obtain ⟨s, s0, s1⟩ := exists_pos_lt_top (pull hU ν) (by
    intro h; apply n2; rw [← en, h, Measure.map_zero])
  have e := measure_eq_div_smul (pull hU μ) (pull hU ν) s0 s1
  generalize pull hU μ s / pull hU ν s = c at e
  have e' : μ = c • ν := by
    rw [← em, e, Measure.map_smul, en]
    exact inc_memb.measurable.aemeasurable
  refine ⟨c, ?_, ?_, e'⟩
  · rintro rfl
    exact m2 (by rw [e', zero_smul])
  · rintro rfl
    obtain ⟨t, t0, t1⟩ := exists_pos_lt_top μ m2
    rw [e', Measure.smul_apply, smul_eq_mul] at t0 t1
    by_cases h : ν t = 0
    · exact t0 (by rw [h, mul_zero])
    · exact t1 (ENNReal.top_mul h)

theorem haar_of_compact {U : Set (Mat k r)} (hU : IsClosed U) {μ : Measure (Mt k r)}
    (hμ : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn U μ) : PI.BesselPeriodGGP.IsHaarOn U μ := by
  obtain ⟨m1, m2, m3, m4⟩ := hμ
  have : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hle : μ K ≤ μ (K ∩ amb U) := by
      refine measure_mono_ae ?_
      have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ U := by rw [ae_iff]; exact m1
      filter_upwards [hae] with x hx hK using ⟨hK, hx⟩
    exact lt_of_le_of_lt hle (m3 _ (hK.inter_right hU) fun x hx => hx.2)
  exact ⟨inferInstance, m4, m1, m2⟩

theorem exists_haar {U : Set (Mat k r)} (hU : IsClosedSubgroup U) :
    ∃ μ, GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn U μ := by
  let m : Measure (Gp U hU) := Measure.haar
  have hm : Measurable (inc : Gp U hU → Mt k r) := inc_memb.measurable
  refine ⟨m.map inc, ?_, ?_, ?_, ?_⟩
  · rw [inc_memb.map_apply]
    have : (inc : Gp U hU → Mt k r) ⁻¹' {x | Matrix.of x ∉ U} = ∅ := by
      ext x; simpa using inc_mem x
    rw [this, measure_empty]
  · intro a ha
    let g : Gp U hU := ⟨Matrix.of.symm a, ha⟩
    rw [Measure.map_map (lmulM_cont a).measurable hm]
    have : (lmulM a ∘ inc : Gp U hU → Mt k r) = inc ∘ (fun x => g * x) := rfl
    rw [this, ← Measure.map_map hm (continuous_const_mul g).measurable, map_mul_left_eq_self]
  · intro C hC _
    rw [inc_memb.map_apply]
    exact (inc_closedEmb.isCompact_preimage hC).measure_lt_top
  · intro h
    rw [Measure.map_eq_zero_iff hm.aemeasurable] at h
    exact NeZero.ne m h

theorem isHaarOn_iff {U : Set (Mat k r)} (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) :
    PI.BesselPeriodGGP.IsHaarOn U μ ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn U μ := by
  refine ⟨fun h => ?_, haar_of_compact hU.closed⟩
  obtain ⟨ν, hν⟩ := exists_haar hU
  obtain ⟨c, -, c1, e⟩ := haar_unique hU h (haar_of_compact hU.closed hν)
  refine ⟨h.2.2.1, h.2.2.2, fun C hC hCU => ?_, h.2.1⟩
  rw [e, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top c1.lt_top (hν.2.2.1 C hC hCU)

def uinv (k r : ℕ) (h : Mat k r) : Mat k r := Hpk k r * hᴴ * Hpk k r

theorem uinv_eq {h : Mat k r} (hh : h ∈ UH (Hpk k r)) : uinv k r h = h⁻¹ := by
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh
  refine (Matrix.inv_eq_left_inv ?_).symm
  calc uinv k r h * h = Hpk k r * (hᴴ * Hpk k r * h) := by simp only [uinv, Matrix.mul_assoc]
    _ = 1 := by rw [hU, (Formalism.QuantumDeterminants.hpkFacts k r).2.1]

theorem continuous_uinv : Continuous (uinv k r) :=
  (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const

theorem continuous_leviW : Continuous (leviW k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold leviW
  split_ifs
  · exact continuous_id.matrix_elem i j
  · exact continuous_const
  · exact continuous_const

def split (k r : ℕ) (s : Mt k r) : Mt k r × Mt k r :=
  (leviW k r (Matrix.of s), uinv k r (leviW k r (Matrix.of s)) * Matrix.of s)

theorem continuous_split : Continuous (split k r) :=
  (continuous_leviW (k := k) (r := r)).prodMk
    (((continuous_uinv (k := k) (r := r)).comp continuous_leviW).matrix_mul continuous_id)

theorem split_mul {z : Fin (2 * r + k + 1) → ℂ} {h n : Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) : split k r (h * n) = (h, n) := by
  have e : leviW k r (h * n) = h := GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.leviW_mul hh hn
  refine Prod.ext e ?_
  show uinv k r (leviW k r (h * n)) * (h * n) = n
  rw [e, uinv_eq hh.1, Matrix.nonsing_inv_mul_cancel_left _ _
    ((Formalism.FourierDecayAlt.P.B2x3.closedW k r z).unit h hh)]

theorem closedS {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : IsClosedSubgroup (Sset k r z) := by
  obtain ⟨h1, h2, h3⟩ := Formalism.QuantumDeterminants.sGroup k r z hz
  have hW := Formalism.FourierDecayAlt.P.B2x3.closedW k r z
  have hN := Formalism.FourierDecayAlt.P.B2x2.closedN k r
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · rintro a ⟨h, hh, n, hn, rfl⟩
    rw [Matrix.det_mul]
    exact (hW.unit h hh).mul (hN.unit n hn)
  · have e : Sset k r z = split k r ⁻¹' (amb (UWset k r z) ×ˢ amb (Nset k r)) := by
      ext s
      constructor
      · rintro ⟨h, hh, n, hn, rfl⟩
        show split k r (h * n) ∈ amb (UWset k r z) ×ˢ amb (Nset k r)
        rw [split_mul hh hn]
        exact ⟨hh, hn⟩
      · rintro ⟨hh, hn⟩
        have hh' : leviW k r s ∈ UWset k r z := hh
        refine ⟨_, hh', uinv k r (leviW k r s) * s, hn, ?_⟩
        rw [uinv_eq hh'.1, Matrix.mul_nonsing_inv_cancel_left _ _ (hW.unit _ hh')]
    rw [e]
    exact ((amb_closed hW).prod (amb_closed hN)).preimage continuous_split

end GlobalTheory.BesselPeriodCompare

end
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory

theorem hcParam_sub_integral : ∀ (n : ℕ) (lam lam' : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.IsHCParam lam' → ∃ ν : Fin n → ℤ, lam' = (fun a => lam a + (ν a : ℝ)) ∧ ((BranchingSupport.n1 ν : ℕ) : ℝ) = l1 lam' lam ∧ ∀ s, |lam' s - lam s| ≤ l1 lam' lam := by
  intro n lam lam' h h'
  choose m hm using h.2
  choose m' hm' using h'.2
  have key : ∀ a, lam' a - lam a = ((m' a - m a : ℤ) : ℝ) := by
    intro a
    push_cast
    linarith [hm a, hm' a]
  refine ⟨fun a => m' a - m a, ?_, ?_, ?_⟩
  · funext a
    linarith [key a]
  · unfold BranchingSupport.n1 l1
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [key a, Nat.cast_natAbs, Int.cast_abs]
  · intro s
    unfold l1
    exact Finset.single_le_sum (f := fun a => |lam' a - lam a|) (fun a _ => abs_nonneg _) (Finset.mem_univ s)

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeastExponentCompare

open NumberField Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem (bar balancedForms quad IsPosSemidef IsPosDef Exponent pairing pairingValues IsPhiC)
open GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace (IsBalancedSpace evalSum)
open GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement (outer IsPosHerm)

variable {E : Type} [Field E] [NumberField E]

theorem finite_projective_iff (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    (Module.Finite (𝓞 E) Y ∧ Module.Projective (𝓞 E) Y) ↔ (Module.Finite ℤ Y ∧ Module.Free ℤ Y) := by
  constructor
  · rintro ⟨hf, hp⟩
    have hfin : Module.Finite ℤ Y := Module.Finite.trans (𝓞 E) Y
    have hfl : Module.Flat ℤ Y := Module.Flat.trans ℤ (𝓞 E) Y
    exact ⟨hfin, inferInstance⟩
  · rintro ⟨hf, hfr⟩
    exact ⟨Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Y, GlobalTheory.PointStepCompare.projective_of_free E⟩

variable [IsCMField E] {cj : E → E}

def IsConj (cj : E → E) : Prop := ∀ c : 𝓞 E, cj c = IsCMField.complexConj E (c : E)

variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

theorem isBalancedSpace (h : IsConj cj) : IsBalancedSpace E (SymB cj Y) := by
  intro β
  change ((∀ a b, β a b = β b a) ∧ ∀ (c c' : 𝓞 E), (c' : E) = cj (c : E) → ∀ a b, β (c • a) b = β a (c' • b)) ↔ _
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun a x y => hb a _ ?_ x y⟩
    rw [h a, IsCMField.coe_ringOfIntegersComplexConj]
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun c c' hc x y => ?_⟩

    have hc' : c' = IsCMField.ringOfIntegersComplexConj E c := by
      apply RingOfIntegers.ext
      rw [hc, h c, IsCMField.coe_ringOfIntegersComplexConj]
    rw [hc']
    exact hb c x y


variable (Y) in
def formsEquiv (h : IsConj cj) : SymB cj Y ≃ₗ[ℝ] balancedForms E Y where
  toFun β := ⟨AddMonoidHom.mk' (fun x => ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x).toAddMonoidHom)
      (fun x x' => by ext y; simp),
    ((isBalancedSpace h _).1 β.2).1, ((isBalancedSpace h _).1 β.2).2⟩
  invFun β := ⟨LinearMap.mk₂ ℤ (fun x y => β.1 x y) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp),
    (isBalancedSpace h _).2 ⟨β.2.1, β.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def Admissible (l : SymB cj Y →ₗ[ℝ] ℝ) : Prop :=
  (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    ∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β

def functionalValues (b : SymB cj Y) : Set ℝ := {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ, Admissible l ∧ x = l b}

variable [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

theorem functionalValues_nonempty (h : IsConj cj) (b : SymB cj Y) : (functionalValues b).Nonempty := by
  obtain ⟨_, _⟩ := (finite_projective_iff (E := E) Y).1 ⟨inferInstance, inferInstance⟩
  obtain ⟨l, hi, hp⟩ := GlobalTheory.PointStepCompare.exists_admissible E (isBalancedSpace (Y := Y) h)
  exact ⟨l b, l, ⟨hi, hp⟩, rfl⟩

section Host

open Formalism.BasicNotions

end Host

end GlobalTheory.LeastExponentCompare

end
end
