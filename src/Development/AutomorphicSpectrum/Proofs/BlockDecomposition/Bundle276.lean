module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle226
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle270
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle261
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle269
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WavePairingTimeSymmetry
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeDimensionUpper
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle020
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle271
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_fixed_near : ∀ {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ), 0 < f → ‖(l : ℂ_[l])‖ ≤ ρ → ρ < 1 → ∀ c : ℂ_[l],
    ‖c‖ ≤ 1 → ‖c ^ l ^ f - c‖ ≤ ρ → ∃ y : Tl l, y ^ l ^ f = y ∧ ‖sh y - c‖ ≤ ρ := by
  intro l _ f ρ hf hρ hρ1 c hc hcf
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  obtain ⟨a, ha⟩ := exists_sh_near c hc
  have ha' : ‖sh a - c‖ ≤ ρ := ha.trans hρ
  have hq1 : 1 ≤ l ^ f := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hq2 : 2 ≤ l ^ f := Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt

  have h0 : ‖a ^ l ^ f - a‖ ≤ ρ := by
    refine norm_sub_le_of_near hρ ?_
    have e : sh (a ^ l ^ f) - sh a =
        (sh (a ^ l ^ f) - c ^ l ^ f) + ((c ^ l ^ f - c) + -(sh a - c)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (near_pow hρ hc ha' _) ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hcf ?_)
    rwa [norm_neg]
  let u : ℕ → Tl l := fun n => a ^ l ^ (f * n)
  have hstep : ∀ n, u (n + 1) = u n ^ l ^ f := by
    intro n
    show a ^ l ^ (f * (n + 1)) = (a ^ l ^ (f * n)) ^ l ^ f
    rw [← pow_mul, ← pow_add, Nat.mul_succ]
  have hdiff : ∀ n, ‖u (n + 1) - u n‖ ≤ ρ ^ (l ^ (f * n)) := by
    intro n
    have e : u (n + 1) - u n = (a ^ l ^ f) ^ l ^ (f * n) - a ^ l ^ (f * n) := by
      show a ^ l ^ (f * (n + 1)) - a ^ l ^ (f * n) = _
      rw [← pow_mul, ← pow_add, Nat.mul_succ, Nat.add_comm]
    rw [e, norm_sub_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h0 _
  have hdiff1 : ∀ n, ‖u (n + 1) - u n‖ ≤ ρ := by
    intro n
    refine (hdiff n).trans ?_
    have : 1 ≤ l ^ (f * n) := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
    simpa using pow_le_pow_of_le_one hρ0 hρ1.le this
  have hgeom : ∀ n, dist (u n) (u (n + 1)) ≤ 1 * ρ ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, one_mul]
    refine (hdiff n).trans (pow_le_pow_of_le_one hρ0 hρ1.le ?_)
    have h1 : n < l ^ n := Nat.lt_pow_self (Fact.out : l.Prime).one_lt
    have h2 : l ^ n ≤ l ^ (f * n) :=
      Nat.pow_le_pow_right (Fact.out : l.Prime).pos (Nat.le_mul_of_pos_left n hf)
    omega
  have hcau : CauchySeq u := cauchySeq_of_le_geometric ρ 1 hρ1 hgeom
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
  have hclose : ∀ n, ‖u n - a‖ ≤ ρ := by
    intro n
    induction n with
    | zero => simpa [u] using hρ0
    | succ n ih =>
      have e : u (n + 1) - a = (u (n + 1) - u n) + (u n - a) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hdiff1 n) ih)
  have hya : ‖y - a‖ ≤ ρ :=
    le_of_tendsto ((hy.sub_const a).norm) (Filter.Eventually.of_forall hclose)
  refine ⟨y, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun n => u n ^ l ^ f) Filter.atTop (nhds (y ^ l ^ f)) := hy.pow _
    have h2 : Filter.Tendsto (fun n => u n ^ l ^ f) Filter.atTop (nhds y) := by
      simpa only [hstep] using (Filter.tendsto_add_atTop_iff_nat 1).2 hy
    exact tendsto_nhds_unique h1 h2
  · have e : sh y - c = (sh y - sh a) + (sh a - c) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (near_of_norm_sub_le hρ hya) ha')

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt.Normz

theorem norm_bounds_of_rec {F : Type*} [NormedField F] [IsUltrametricDist F] (w : ℕ → F) (p : F)
    (q : ℕ) (hq : 2 ≤ q) (hp : ‖p‖ < 1) (h0 : w 0 = 0) (h1 : w 1 ≠ 0)
    (hr : ∀ n, w (n + 1) ^ q + p * w (n + 1) = w n) :
    (∀ n, ‖w n‖ < 1) ∧ ∀ n, 2 ≤ n → ‖p‖ < ‖w n‖ := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  have hmax : ∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := fun x y => IsUltrametricDist.norm_add_le_max x y
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg p
  have hlt : ∀ n, ‖w n‖ < 1 := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      by_contra hge
      rw [not_lt] at hge
      have hapos : 0 < ‖w (n + 1)‖ := lt_of_lt_of_le one_pos hge
      have hq1 : ‖w (n + 1)‖ ≤ ‖w (n + 1)‖ ^ (k + 2) := by
        calc ‖w (n + 1)‖ = ‖w (n + 1)‖ ^ 1 := (pow_one _).symm
          _ ≤ ‖w (n + 1)‖ ^ (k + 2) := pow_le_pow_right₀ hge (by omega)
      have key : w (n + 1) ^ (k + 2) = w n + -(p * w (n + 1)) := by linear_combination hr n
      have h2 : ‖w (n + 1) ^ (k + 2)‖ ≤ max ‖w n‖ ‖-(p * w (n + 1))‖ := by
        rw [key]; exact hmax _ _
      rw [norm_pow, norm_neg, norm_mul] at h2
      have h3 : ‖p‖ * ‖w (n + 1)‖ < ‖w (n + 1)‖ ^ (k + 2) := by
        calc ‖p‖ * ‖w (n + 1)‖ < 1 * ‖w (n + 1)‖ := mul_lt_mul_of_pos_right hp hapos
          _ = ‖w (n + 1)‖ := one_mul _
          _ ≤ ‖w (n + 1)‖ ^ (k + 2) := hq1
      have h4 : ‖w n‖ < ‖w (n + 1)‖ ^ (k + 2) := lt_of_lt_of_le ih (le_trans hge hq1)
      exact absurd h2 (not_le.mpr (max_lt h4 h3))
  have hrec1 : w 1 ^ (k + 2) + p * w 1 = 0 := by
    have := hr 0
    rw [h0] at this
    exact this
  have hpw : w 1 ^ (k + 1) = -p := by
    have e : w 1 * (w 1 ^ (k + 1) + p) = 0 := by linear_combination hrec1
    rcases mul_eq_zero.mp e with h | h
    · exact absurd h h1
    · linear_combination h
  have hnorm1 : ‖w 1‖ ^ (k + 1) = ‖p‖ := by rw [← norm_pow, hpw, norm_neg]
  have hp_pos : 0 < ‖p‖ := by
    rw [← hnorm1]
    exact pow_pos (norm_pos_iff.mpr h1) _
  have hw1 : ‖p‖ ≤ ‖w 1‖ := by
    rw [← hnorm1]
    calc ‖w 1‖ ^ (k + 1) ≤ ‖w 1‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (hlt 1).le (by omega)
      _ = ‖w 1‖ := pow_one _
  have hsmall : ∀ a : F, ‖a‖ ≤ ‖p‖ → ‖a ^ (k + 2) + p * a‖ ≤ ‖p‖ ^ 2 := by
    intro a ha
    have ha0 : 0 ≤ ‖a‖ := norm_nonneg a
    refine le_trans (hmax _ _) (max_le ?_ ?_)
    · rw [norm_pow]
      calc ‖a‖ ^ (k + 2) ≤ ‖a‖ ^ 2 := pow_le_pow_of_le_one ha0 (ha.trans hp.le) (by omega)
        _ ≤ ‖p‖ ^ 2 := by gcongr
    · rw [norm_mul, sq]
      exact mul_le_mul_of_nonneg_left ha hp0
  have hstep : ∀ n, ‖p‖ ≤ ‖w n‖ → ‖p‖ < ‖w (n + 1)‖ := by
    intro n hn
    by_contra hc
    rw [not_lt] at hc
    have hb := hsmall (w (n + 1)) hc
    rw [hr n] at hb
    have hp2 : ‖p‖ ^ 2 < ‖p‖ := by
      rw [sq]
      calc ‖p‖ * ‖p‖ < 1 * ‖p‖ := mul_lt_mul_of_pos_right hp hp_pos
        _ = ‖p‖ := one_mul _
    linarith
  have hge : ∀ n, ‖p‖ ≤ ‖w (n + 1)‖ := by
    intro n
    induction n with
    | zero => exact hw1
    | succ n ih => exact (hstep _ ih).le
  refine ⟨hlt, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact hstep (m + 1) (hge m)

theorem norm_z_bounds : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → 2 ≤ qOf π → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) ∧ ∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖ := by
  intro l _ K χ π z hz hq hp
  obtain ⟨_, h0, h1, hr, _⟩ := hz
  have e : GlobalTheory.CompanionTheory.LTPer.Tilt.omC (((π : ↥K.1) : Om l)) = GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π := by
    rw [GlobalTheory.CompanionTheory.LTPer.Tilt.omC_apply, GlobalTheory.CompanionTheory.LTPer.Tilt.oc_apply]
  refine norm_bounds_of_rec (fun n => GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z n)) (GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π) (qOf π) hq hp
    (by simp [h0]) ?_ ?_
  · show GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z 1) ≠ 0
    intro h
    have hn := congrArg norm h
    rw [GlobalTheory.CompanionTheory.LTPer.Tilt.norm_omC, norm_zero] at hn
    exact h1 (norm_eq_zero.mp hn)
  · intro n
    show GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z (n + 1)) ^ qOf π + GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π * GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z (n + 1))
      = GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z n)
    have hr' : z (n + 1) ^ qOf π + ((π : ↥K.1) : Om l) * z (n + 1) = z n := hr n
    rw [← e, ← map_pow, ← map_mul, ← map_add (f := _), hr']

end GlobalTheory.CompanionTheory.LTPer.Tilt.Normz
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

variable {l : ℕ} [Fact l.Prime]

private def vv (a : ℕ → Tl l) (f n m : ℕ) : Tl l := a (n + m) ^ l ^ (f * m)

private theorem vv_step (a : ℕ → Tl l) {f : ℕ} {ρ : ℝ} (h : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ)
    (n m : ℕ) : ‖vv a f n (m + 1) - vv a f n m‖ ≤ ρ ^ l ^ (f * m) := by
  have e : vv a f n (m + 1) = (a (n + m + 1) ^ l ^ f) ^ l ^ (f * m) := by
    rw [vv, ← pow_mul, ← pow_add, ← add_assoc, mul_add, mul_one, add_comm (f * m) f]
  rw [e, vv, norm_sub_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h _) _

private theorem pow_bound {f : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hf : 0 < f) (m : ℕ) :
    ρ ^ l ^ (f * m) ≤ ρ ^ m := by
  refine pow_le_pow_of_le_one hρ0 hρ1.le ?_
  have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h3 : m ≤ f * m := Nat.le_mul_of_pos_left m hf
  exact h3.trans (Nat.lt_pow_self h2).le

private theorem vv_near (a : ℕ → Tl l) {f : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ) (n m : ℕ) : ‖vv a f n m - a n‖ ≤ ρ := by
  induction m with
  | zero => simpa [vv] using hρ0
  | succ m ih =>
    have e : vv a f n (m + 1) - a n = (vv a f n (m + 1) - vv a f n m) + (vv a f n m - a n) := by
      abel
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
    refine (vv_step a h n m).trans ?_
    exact pow_le_of_le_one hρ0 hρ1.le (pow_pos (Fact.out : l.Prime).pos _).ne'

theorem exists_tilt_lift_compat {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ) (hf : 0 < f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ρ) (hρ1 : ρ < 1) (Z : ℕ → ℂ_[l])
    (hZ : ∀ n, ‖Z n‖ ≤ 1) (hc : ∀ n, ‖Z (n + 1) ^ l ^ f - Z n‖ ≤ ρ) :
    ∃ u : ℕ → Tl l, (∀ n, u (n + 1) ^ l ^ f = u n) ∧ ∀ n, ‖sh (u n) - Z n‖ ≤ ρ := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hl
  choose a ha using fun n => exists_sh_near (l := l) (Z n) (hZ n)
  have ha' : ∀ n, ‖sh (a n) - Z n‖ ≤ ρ := fun n => (ha n).trans hl
  have hd : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ := by
    intro n
    refine norm_sub_le_of_near hl ?_
    have h1 := near_pow hl (hZ (n + 1)) (ha' (n + 1)) (l ^ f)
    have e : sh (a (n + 1) ^ l ^ f) - sh (a n) =
        (sh (a (n + 1) ^ l ^ f) - Z (n + 1) ^ l ^ f) +
          ((Z (n + 1) ^ l ^ f - Z n) + -(sh (a n) - Z n)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc n) ?_)
    rw [norm_neg]
    exact ha' n
  have hcau : ∀ n, CauchySeq (vv a f n) := by
    intro n
    refine cauchySeq_of_le_geometric ρ 1 hρ1 fun m => ?_
    rw [dist_comm, dist_eq_norm, one_mul]
    exact (vv_step a hd n m).trans (pow_bound hρ0 hρ1 hf m)
  choose u hu using fun n => cauchySeq_tendsto_of_complete (hcau n)
  refine ⟨u, fun n => ?_, fun n => ?_⟩
  · have h1 : Filter.Tendsto (fun m => vv a f (n + 1) m ^ l ^ f) Filter.atTop
        (nhds (u (n + 1) ^ l ^ f)) := (hu (n + 1)).pow _
    have h2 : Filter.Tendsto (fun m => vv a f n (m + 1)) Filter.atTop (nhds (u n)) :=
      (hu n).comp (Filter.tendsto_add_atTop_nat 1)
    have e : (fun m => vv a f (n + 1) m ^ l ^ f) = fun m => vv a f n (m + 1) := by
      funext m
      rw [vv, vv, ← pow_mul, ← pow_add, mul_add, mul_one, add_comm (f * m) f, add_assoc,
        add_comm 1 m]
    rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  · have h1 : ‖u n - a n‖ ≤ ρ :=
      le_of_tendsto (((hu n).sub_const (a n)).norm)
        (Filter.Eventually.of_forall fun m => vv_near a hρ0 hρ1 hd n m)
    have h2 := near_of_norm_sub_le hl h1
    have e : sh (u n) - Z n = (sh (u n) - sh (a n)) + (sh (a n) - Z n) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (ha' n))

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.RwCauchy

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  (Matrix.isUnits_det_units y).ne_zero

theorem Rw_sub_on {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {a b : Mat n → V}
    (ha : ContDiffOn ℝ ∞ a (GLs n)) (hb : ContDiffOn ℝ ∞ b (GLs n))
    (w : List (Bool × Fin n × Fin n)) :
    ∀ z ∈ GLs n, Rw w (a - b) z = Rw w a z - Rw w b z := by
  induction w with
  | nil => intro z _; rfl
  | cons p w ih =>
    intro z hz
    have h1 : Rw (p :: w) (a - b) z = Rd (bs p) (Rw w a - Rw w b) z :=
      Rd_congr (f := Rw w (a - b)) (f' := Rw w a - Rw w b) (fun y hy => ih y hy) (bs p) z hz
    rw [h1]
    have hU := isOpen_GLs.mem_nhds hz
    have da : DifferentiableAt ℝ (Rw w a) z :=
      ((GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' ha w).contDiffAt hU).differentiableAt (by simp)
    have db : DifferentiableAt ℝ (Rw w b) z :=
      ((GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' hb w).contDiffAt hU).differentiableAt (by simp)
    show fderiv ℝ (Rw w a - Rw w b) z (z * bs p) =
      fderiv ℝ (Rw w a) z (z * bs p) - fderiv ℝ (Rw w b) z (z * bs p)
    have e := (da.hasFDerivAt.sub db.hasFDerivAt).fderiv
    exact DFunLike.congr_fun e (z * bs p)

theorem uniformCauchy : SobG → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (g : ℕ → Mat n → V) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) → (∀ k w, MemLp (fun y : G n => Rw w (g k) y.val) 2 μ) → (∀ w, Tendsto (fun k => cls μ (Rw w (g k))) atTop (𝓝 (x w))) → ∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n) := by
  intro hS n _ _ μ _ V _ _ _ g x hg hm hc w
  obtain ⟨S, C, hC, hsup⟩ := GlobalTheory.CompanionTheory.PresSobA.SupG.sup_sq_bound hS n μ
  have hbound : ∀ k l, ∀ z ∈ GLs n, ‖Rw w (g k) z - Rw w (g l) z‖ ^ 2 ≤
      C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g k)) - cls μ (Rw (w' ++ w) (g l))‖ ^ 2 := by
    intro k l z hz
    have sk := GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg k) w
    have sl := GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg l) w
    have key : ∀ w', ∀ y ∈ GLs n, Rw w' (Rw w (g k) - Rw w (g l)) y =
        Rw (w' ++ w) (g k) y - Rw (w' ++ w) (g l) y := by
      intro w' y hy
      rw [Rw_sub_on sk sl w' y hy, Rw_append, Rw_append]
    have hcl : ∀ w', MemLp (fun y : G n => Rw w' (Rw w (g k) - Rw w (g l)) y.val) 2 μ ∧
        cls μ (Rw w' (Rw w (g k) - Rw w (g l))) =
          cls μ (Rw (w' ++ w) (g k)) - cls μ (Rw (w' ++ w) (g l)) := by
      intro w'
      refine cls_of_ae μ ?_
      filter_upwards [Lp.coeFn_sub (cls μ (Rw (w' ++ w) (g k))) (cls μ (Rw (w' ++ w) (g l))),
        coe_cls μ (hm k (w' ++ w)), coe_cls μ (hm l (w' ++ w))] with y h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, key w' _ (val_mem_GLs y)]
    have := hsup V (Rw w (g k) - Rw w (g l)) (sk.sub sl) (fun w' => (hcl w').1) z hz
    simp only [hcl] at this
    exact this
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hT : Tendsto (fun p : ℕ × ℕ =>
      C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g p.1)) - cls μ (Rw (w' ++ w) (g p.2))‖ ^ 2)
      (atTop ×ˢ atTop) (𝓝 0) := by
    have h0 : Tendsto (fun p : ℕ × ℕ =>
        C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g p.1)) - cls μ (Rw (w' ++ w) (g p.2))‖ ^ 2)
        (atTop ×ˢ atTop) (𝓝 (C * ∑ w' ∈ S, ‖x (w' ++ w) - x (w' ++ w)‖ ^ 2)) := by
      refine Tendsto.const_mul _ (tendsto_finsetSum _ fun w' _ => ?_)
      exact ((((hc _).comp tendsto_fst).sub ((hc _).comp tendsto_snd)).norm).pow 2
    simpa using h0
  have hev := hT.eventually (gt_mem_nhds (pow_pos hε 2))
  rw [prod_atTop_atTop_eq] at hev
  obtain ⟨N, hN⟩ := eventually_atTop_prod_self'.1 hev
  refine ⟨N, fun k hk l hl z hz => ?_⟩
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le ((hbound k l z hz).trans_lt (hN k hk l hl))

end GlobalTheory.CompanionTheory.PresSobA.RwCauchy
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.l2_limit_eq_pointwise_limit_holds : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (a : ℕ → Mat n → V) (b : Mat n → V) (x : Lp V 2 μ), (∀ k, MemLp (fun y : G n => a k y.val) 2 μ) → Tendsto (fun k => cls μ (a k)) atTop (𝓝 x) → (∀ z ∈ GLs n, Tendsto (fun k => a k z) atTop (𝓝 (b z))) → MemLp (fun y : G n => b y.val) 2 μ ∧ cls μ b = x := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.l2_limit_eq_pointwise_limit | exact GlobalTheory.CompanionTheory.PresSobA.l2_limit_eq_pointwise_limit | (intros; apply GlobalTheory.CompanionTheory.PresSobA.l2_limit_eq_pointwise_limit <;> assumption)
end
end

section


theorem _root_.GlobalTheory.T.sobolev_inequality_on_group : PositivityTheory.RgBcC.SobG := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.sobG | exact GlobalTheory.CompanionTheory.SobGL.sobG | (intros; apply GlobalTheory.CompanionTheory.SobGL.sobG <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.wave_kernel_word_order_swap : WaveSpeed → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E (w ++ w') g K → IsKer μ E (w' ++ w) g K := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.KerSwap.isKer_swap | exact GlobalTheory.CompanionTheory.WaveMult.KerSwap.isKer_swap | (intros; apply GlobalTheory.CompanionTheory.WaveMult.KerSwap.isKer_swap <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.wave_pairing_time_symmetry : LgFacts → RCalc → WaveSpeed → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → Cpt (u 0) → Cpt (v 0) → ∀ t, ∫ y : G n, ⟪u t y.val, v 0 y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪u 0 y.val, v t y.val⟫_ℂ ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.wave_symm | exact GlobalTheory.CompanionTheory.WaveMult.wave_symm | (intros; apply GlobalTheory.CompanionTheory.WaveMult.wave_symm <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem _root_.GlobalTheory.T.chart_lattice_dimension_upper : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a b : K → ℤ), 1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnGenericDeg (mCoordIdeal y) a → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + b) 1) : ℝ) ≤ ((genDeg (mCoordIdeal y) D a : ℝ) + ε) * (n : ℝ) ^ D / (D.factorial : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le | exact GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le | (intros; apply GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le <;> assumption)
end

section


theorem _root_.GlobalTheory.T.segre_chart_integral_holds : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | exact GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral <;> assumption)
end
