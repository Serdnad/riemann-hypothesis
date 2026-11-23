module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexConjFrobeniusDepthContentBoundProof
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthContentBoundProof
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle105
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Formalism.HermitianCurvature.StatementB
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle106
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle098
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.GrowthSphericalBound
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.chartDepth_le_of_characterFlags : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → (∀ τ, ∃ a0, IsUnit (τO τ a0 - τO τ (star a0))) → (∀ x : X.O, x ≠ 0 → ∃ N : ℕ, X.v (N : X.C) < X.v (algebraMap X.O X.C x) ∧ ∀ τ, ∃ a : 𝓞 E, star a * a = (N : 𝓞 E) ∧ X.v (algebraMap X.O X.C (τO τ a - 1)) < X.v (algebraMap X.O X.C x)) → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ (len : (E →+* ℂ) → ℝ), (∀ τ, 0 ≤ len τ) → (∀ τ, ∃ χ : Fin (Dw.mult τ) → PS X.O 1 (chD Ch.ch), (∀ b, IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (χ b)) ∧ ∀ i : Fin (Dw.mult τ), (X.v (p : X.C) : ℝ) ^ len τ ≤ (X.v (algebraMap X.O X.C (Matrix.of fun s b : Fin (i.val + 1) => ∑ j, X.ι (Ch.uvecT ⟨τ, Fin.castLE i.isLt s⟩ j) * dl (χ (Fin.castLE i.isLt b)) j).det) : ℝ)) → nuLocC Ch e k a n ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * ∑ τ, len τ * (a (τ, 0) : ℝ) : ℝ) : EReal) := by
  first | exact @GlobalTheory.CharDepth.nuLocC_le_of_character_flags | exact GlobalTheory.CharDepth.nuLocC_le_of_character_flags | (intros; apply GlobalTheory.CharDepth.nuLocC_le_of_character_flags <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.SmallTors

variable {q : ℕ} [hq : Fact q.Prime]

lemma norm_zc' (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap']
  rfl

lemma norm_nat_coprime {m : ℕ} (hm : Nat.Coprime m q) : ‖(m : ℂ_[q])‖ = 1 := by
  have h0 : (m : ℂ_[q]) = zc (m : ℤ_[q]) := by simp [zc]
  rw [h0, norm_zc']
  have h1 : ¬ ‖((m : ℤ) : ℤ_[q])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    have := (Nat.Prime.coprime_iff_not_dvd hq.out).1 hm.symm
    exact_mod_cast this
  push_cast at h1
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 h1)

lemma norm_q_pow (n : ℕ) : ‖((q : ℂ_[q])) ^ n‖ = (q : ℝ) ^ (-(n : ℤ)) := by
  have h0 : (q : ℂ_[q]) ^ n = zc ((q : ℤ_[q]) ^ n) := by simp [zc]
  rw [h0, norm_zc', PadicInt.norm_p_pow]

lemma norm_eq_one {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) : ‖ξ‖ = 1 := by
  have : ξ = (ξ - 1) + 1 := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne), norm_one]
  exact max_eq_right h.le

lemma norm_pow_sub_one {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) (n : ℕ) : ‖ξ ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : ξ ^ (n + 1) - 1 = ξ * (ξ ^ n - 1) + (ξ - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
    rw [norm_mul, norm_eq_one h, one_mul]; exact ih

lemma norm_geom_sub {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, ξ ^ i - n‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : ∑ i ∈ Finset.range (n + 1), ξ ^ i - ((n + 1 : ℕ) : ℂ_[q])
        = (∑ i ∈ Finset.range n, ξ ^ i - n) + (ξ ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (norm_pow_sub_one h n))

lemma eq_one_of_pow {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) {m : ℕ} (hm : Nat.Coprime m q) (h1 : ξ ^ m = 1) :
    ξ = 1 := by
  have h2 := geom_sum_mul ξ m
  rw [h1, sub_self, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · have h3 := norm_geom_sub h m
    rw [h2, zero_sub, norm_neg, norm_nat_coprime hm] at h3
    exact absurd h3 (lt_irrefl _)
  · exact sub_eq_zero.1 h2

lemma inOK_int (d : ℕ) (k : ℤ) : InOK d (k : ℂ) := ⟨k, 0, by simp⟩

lemma inOK_of_eq {d : ℕ} {x y : ℂ} (h : InOK d x) (e : x = y) : InOK d y := e ▸ h

end GlobalTheory.MomOne.SmallTors

namespace GlobalTheory.MomOne
open SmallTors

theorem smallTors : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → (∀ p p', M.Small p → M.Small p' → M.Small (p + p') ∧ M.Small (-p)) ∧ (∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]), ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧ ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p)) ∧ (∀ p, PrimeTo d q p → M.Small p → InOK d p) ∧ ∀ (p α s : ℂ), InOK d α → α ≠ 0 → PrimeTo d q s → InOK d (α * p + s - 1 / 2) → M.Small p → q ≠ 2 ∧ InOK d (s - 1 / 2) := by
  intro d q hq M ω hd hd16 hsp hL hM
  obtain ⟨hadd, hcm⟩ := GlobalTheory.T.multiplicativeCoord_add_and_complexMul q M ω hM
  obtain ⟨hex, hex', huniq, hlat, h10⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω hM
  obtain ⟨⟨-, -, hring⟩, halg, -, -, hhalf, -, -⟩ := okArith d q M.ι hd hd16 hsp
  have iadd : ∀ {a b}, InOK d a → InOK d b → InOK d (a + b) := fun ha hb => (hring _ _ ha hb).1
  have imul : ∀ {a b}, InOK d a → InOK d b → InOK d (a * b) := fun ha hb => (hring _ _ ha hb).2.1
  have iconj : ∀ {a}, InOK d a → InOK d (conj a) := fun ha => (hring _ _ ha ha).2.2.2
  have one_iff : ∀ p, M.At ω 1 p ↔ InOK d p := by
    intro p
    rw [hlat 1 0 p h10, zero_sub, neg_mem_iff, hL]
  have hpow : ∀ ζ p (N : ℕ), M.At ω ζ p → M.At ω (ζ ^ N) ((N : ℂ) * p) := by
    intro ζ p N h
    induction N with
    | zero => simpa using h10
    | succ N ih =>
      have := hadd _ _ _ _ ih h
      rw [pow_succ]; push_cast; rw [add_mul, one_mul]; exact this
  have htors : ∀ ζ p (N : ℕ), M.At ω ζ p → InOK d ((N : ℂ) * p) → ζ ^ N = 1 :=
    fun ζ p N h hN => huniq _ _ _ (hpow ζ p N h) ((one_iff _).2 hN)
  have h2 : ∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]),
      ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧
        ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p) := by
    intro p N hN hNp hp
    obtain ⟨ζ, hζ⟩ := hex' p hp
    obtain ⟨n, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.out.ne_one
    have hm' : Nat.Coprime m q := ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hm).symm
    have hz : ζ ^ (q ^ n) = 1 := by
      refine eq_one_of_pow (norm_pow_sub_one hζ.2.1 _) hm' ?_
      rw [← pow_mul]; exact htors _ _ _ hζ hNp
    refine ⟨n, ζ, hz, hζ, fun α hα hn => ?_⟩
    obtain ⟨⟨a, ha⟩, -⟩ := halg α hα
    have := hcm α a n 0 ζ p (fun l hl => (hL _).2 (imul hα ((hL _).1 hl))) ha
      (by rw [ha, norm_zc'] at hn; simpa using hn) hz hζ
    rw [pow_zero] at this
    exact (one_iff _).1 this
  refine ⟨?_, h2, ?_, ?_⟩
  · intro p p' hp hp'
    obtain ⟨ζ, hζ⟩ := hex' p hp
    obtain ⟨ζ', hζ'⟩ := hex' p' hp'
    refine ⟨(hadd _ _ _ _ hζ hζ').1, ?_⟩
    have hn : ‖ζ‖ = 1 := norm_eq_one hζ.2.1
    have h0 : ζ ≠ 0 := by rintro rfl; simp at hn
    have hinv : ‖ζ⁻¹ - 1‖ < 1 := by
      have : ζ⁻¹ - 1 = -(ζ⁻¹ * (ζ - 1)) := by field_simp; ring
      rw [this, norm_neg, norm_mul, norm_inv, hn, inv_one, one_mul]; exact hζ.2.1
    obtain ⟨r, hr⟩ := hex _ hinv
    have h3 := hadd _ _ _ _ hr hζ
    rw [inv_mul_cancel₀ h0, one_iff, ← hL] at h3
    exact ((hlat _ r (-p) hr).2 (by rwa [sub_neg_eq_add])).1
  · rintro p ⟨s, -, hsq, hsp⟩ hp
    obtain ⟨ζ, hζ⟩ := hex' p hp
    have := eq_one_of_pow hζ.2.1 hsq (htors _ _ _ hζ hsp)
    subst this
    exact (one_iff _).1 hζ
  · rintro p α s hα hα0 ⟨t, ht, htq, hts⟩ hin hp
    obtain ⟨-, ⟨N, hN⟩, -⟩ := halg α hα
    have hN0 : N ≠ 0 := by
      rintro rfl
      have : α * conj α = 0 := by simpa using hN.symm
      rcases mul_eq_zero.1 this with h | h
      · exact hα0 h
      · exact hα0 (by simpa using h)
    have h2t : InOK d (((2 * t : ℕ) : ℂ) * (s - 1 / 2)) :=
      inOK_of_eq (iadd (imul (inOK_int d 2) hts) (inOK_int d (-t))) (by push_cast; ring)
    have hNp : InOK d (((2 * t * N : ℕ) : ℂ) * p) := by
      refine inOK_of_eq (imul (iconj hα) (iadd (imul (inOK_int d (2 * t)) hin)
        (imul (inOK_int d (-1)) h2t))) ?_
      push_cast; rw [hN]; ring
    obtain ⟨n, ζ, -, -, hk⟩ := h2 p _ (by positivity) hNp hp
    have hβ : ∀ β, InOK d β → ‖M.ι β‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (β * (s - 1 / 2)) := by
      intro β hβ hn
      refine inOK_of_eq (iadd (imul hβ hin) (imul (inOK_int d (-1)) (imul hα (hk β hβ hn)))) ?_
      push_cast; ring
    have hq2 : q ≠ 2 := by
      intro h
      obtain ⟨β, hβ1, hβ2, hβ3⟩ := hhalf n
      apply hβ3
      have hodd : Odd t := by
        rw [h] at htq; exact Nat.coprime_two_right.1 htq
      obtain ⟨k, hk'⟩ := hodd
      have hk2 : (t : ℂ) = 2 * k + 1 := by exact_mod_cast hk'
      refine inOK_of_eq (iadd (iadd (imul hβ1 hts) (imul (inOK_int d (-t)) (hβ β hβ1 hβ2)))
        (imul (inOK_int d (-k)) hβ1)) ?_
      push_cast; rw [hk2]; ring
    refine ⟨hq2, ?_⟩
    have hc : Nat.Coprime (2 * t) (q ^ n) := by
      refine Nat.Coprime.pow_right n (Nat.Coprime.mul_left ?_ htq)
      exact (Nat.coprime_primes Nat.prime_two hq.out).2 hq2.symm
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
    have hab' : (a : ℂ) * ((2 * t : ℕ) : ℂ) + b * (q : ℂ) ^ n = 1 := by exact_mod_cast hab
    have h3 := hβ ((q : ℂ) ^ n) (inOK_of_eq (inOK_int d (q ^ n)) (by push_cast; rfl))
      (by rw [map_pow, map_natCast, norm_q_pow])
    refine inOK_of_eq (iadd (imul (inOK_int d a) h2t) (imul (inOK_int d b) h3)) ?_
    linear_combination (s - 1 / 2) * hab'

end GlobalTheory.MomOne
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.complexConjFrobeniusDepthContentBound_proof : PhiCBd := by
  first | exact @GlobalTheory.GoodDepth.ConjPkg.phiCBd | exact GlobalTheory.GoodDepth.ConjPkg.phiCBd | (intros; apply GlobalTheory.GoodDepth.ConjPkg.phiCBd <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.inertPrimeDepthContentBound_proof : InertBd := by
  first | exact @GlobalTheory.InertContent.main | exact GlobalTheory.InertContent.main | (intros; apply GlobalTheory.InertContent.main <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besselInner_haar {k r : ℕ} {U : Set (Mx k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : B.IsHaarOn U μ) :
    PI.BesselPeriodGGP.IsHaarOn U μ :=
  ⟨Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite h, h.ne_zero, h.conc, h.left⟩

theorem besselInner_integral {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    (D : B.RealPlaceData k r Wp Wq)
    (hmul : ∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v))
    (huni : ∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    {γ : Mx k r} (hγ : γ ∈ GG k r) (x y : R.H) (X : Wq →L[ℂ] Wp)
    (a : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (ha1 : Matrix.of a.1 ∈ GG k r) (ha2 : Matrix.of a.2 ∈ GG k r)
    (hint : Integrable (beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x))
      (D.μW'.prod D.μN)) :
    ∫ b, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ (a, b) ∂(D.μW'.prod D.μN) =
      Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) • (D.π (Matrix.of a.1)).comp (X.comp
        (be D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ D.μW' D.μN y (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x))) := by
  obtain ⟨-, -, -, hT, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos
    (besselInner_haar D.haarW') (besselInner_haar D.haarN)
  obtain ⟨-, -, -, hconj, hW, hN⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  set v := R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x with hv
  set G := beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y v with hG
  set T : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r := fun p =>
    ((fun i j => (Matrix.of p.1 : Mx k r) i j),
      (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) with hTdef
  let L : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) :=
    Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) •
      ContinuousLinearMap.compL ℂ Wq Wq Wp ((D.π (Matrix.of a.1)).comp X)
  have hL : ∀ A, L A = Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) •
      (D.π (Matrix.of a.1)).comp (X.comp A) := fun A => rfl
  have key : (fun b => JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ (a, b)) =ᵐ[D.μW'.prod D.μN]
      fun b => L (G (T b)) := by
    filter_upwards [hae] with b hb
    obtain ⟨hb1, hb2⟩ := hb
    have hb1G : Matrix.of b.1 ∈ GG k r := (hW _ hb1 _ hb1).2.2
    have hb2G : Matrix.of b.2 ∈ GG k r := hN _ hb2
    have u1 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ha1
    have u2 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ha2
    have u3 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hγ
    have u4 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hb1G
    have hg0 : γ⁻¹ * Matrix.of a.2 * Matrix.of a.1 ∈ GG k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hγ) ha2) ha1
    have hs : B.sgs (a, b) γ ∈ GG k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
        (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha2)) hγ) hb2G) hb1G
    have e1 : (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) * B.sgs (a, b) γ =
        Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1) := by
      simp only [B.sgs, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u1,
        Matrix.mul_nonsing_inv_cancel_left _ _ u2, Matrix.mul_nonsing_inv_cancel_left _ _ u4,
        Matrix.nonsing_inv_mul_cancel_left _ _ u3]
    have e2 : ⟪x, R.σ (B.sgs (a, b) γ) y⟫_ℂ =
        ⟪v, R.σ (Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1)) y⟫_ℂ := by
      rw [← e1, hmul _ hg0 _ hs, hv, huni _ hg0]
    have e3 := (hconj _ hb1 _ hb2).2.2.2
    have e4 : G (T b) = (⟪v, R.σ (Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1)) y⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1))) •
        D.π' (Matrix.of b.1)⁻¹ := rfl
    rw [hL, e4, e3, ← e2]
    ext w
    simp only [JF.integrand, JF.xiP, B.rho, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      map_smul, smul_smul]
    congr 1
    ring
  have hGT : Integrable (fun b => G (T b)) (D.μW'.prod D.μN) := hT.integrable_comp_of_integrable hint
  rw [integral_congr_ae key, L.integral_comp_comm hGT, ← hL]
  congr 1
  have h2 := integral_map hT.aemeasurable (f := G) (by rw [hT.map_eq]; exact hint.aestronglyMeasurable)
  rw [hT.map_eq] at h2
  exact h2.symm

theorem besselJ_coef_through_right : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ Bb : R.H → Wp → Wq → Wp, (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = Bb x (X (l' y)) c := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hOK _ hl' γ hγ
  obtain ⟨hmul, -, huni, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  refine ⟨fun x b c => ∫ a : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) *
        ⟪l' (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x), c⟫_ℂ) • D.π (Matrix.of a.1) b ∂(D.μW.prod D.μN), ?_, ?_⟩
  · intro x b c t
    simp only
    rw [← integral_smul]
    congr 1
    funext a
    rw [map_smul, smul_comm]
  intro x hx y hy X c
  have hcoef : IsCoef R l l' (fun g => ⟪x, R.σ g y⟫_ℂ • X) ⟪l x, X (l' y)⟫_ℂ :=
    ⟨1, fun _ => x, fun _ => y, fun _ => X, fun _ => ⟨hx, hy⟩, fun g _ => by simp, by simp⟩
  have hcc := (GlobalTheory.isCoef_ckOn_inCC hH k r ε mu h R Wp Wq l l' _ _ hDS hgap hOK hcoef).2 0
  have hI := (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ _ (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hOK).1 hcc).1 γ hγ
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hJ : B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ =
      ∫ p, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) := rfl
  have hI' : Integrable (JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ)
      ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) := hI
  rw [hJ, integral_prod _ hI', ContinuousLinearMap.integral_apply hI'.integral_prod_left]
  obtain ⟨-, -, -, -, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos
    (besselInner_haar D.haarW) (besselInner_haar D.haarN)
  obtain ⟨-, -, -, -, hW, hN⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  refine integral_congr_ae ?_
  filter_upwards [hae] with a ha
  have ha1 : Matrix.of a.1 ∈ GG k r := (hW _ ha.1 _ ha.1).2.2
  have ha2 : Matrix.of a.2 ∈ GG k r := hN _ ha.2
  have hg0 : γ⁻¹ * Matrix.of a.2 * Matrix.of a.1 ∈ GG k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hγ.1) ha2) ha1
  obtain ⟨hint, hbe⟩ := hl'.2 y (hsm y hy) _ (hTK _ hg0 x hx)
  rw [besselInner_integral R D hmul huni hγ.1 x y X a ha1 ha2 hint, hbe]
  simp [smul_smul]

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.isometric_bessel_compare : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp) (Bm' : R'.H → Wp), R.IsDS ε mu → R'.IsDS ε mu' → mu ≠ mu' → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → IsIsoB R' z π νq Bm' → ∀ w ∈ R.sm, ∀ y ∈ R'.sm, ∫ x, ⟪Bm' (R'.σ (Matrix.of x) y), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = 0 := by
  first | exact @GlobalTheory.bessel_orth_of_param_ne | exact GlobalTheory.bessel_orth_of_param_ne | (intros; apply GlobalTheory.bessel_orth_of_param_ne <;> assumption)
end

section

namespace GlobalTheory

theorem besselXiIntegrable_holds : GlobalTheory.HCXi.BesselXiIntegrable :=
  ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselGrowth_stabilizer_unipotent : Formalism.FourierDecayAlt.ThreeDimData.GrowthS :=
  @_root_.Formalism.FourierDecayAlt.P.growth_spherical_bound
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.betaInf_eq_integral_of_integrable_coefficient : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → B.InCC A 4 F → Integrable (B.Ph D F F) D.μSS → B.betaInf D F F = ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS := by
  first | exact @GlobalTheory.RegularisedIntegral.betaInf_eq_integral | exact GlobalTheory.RegularisedIntegral.betaInf_eq_integral | (intros; apply GlobalTheory.RegularisedIntegral.betaInf_eq_integral <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.aestronglyMeasurable_besselFunction_continuousFamily : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (α : Type) [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α] (μ : Measure α) [SFinite μ] (U : Set α) (γ : α → B.Mat k r) (V : Set (B.Mat k r)) (H : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U → ContinuousOn γ U → (∀ x ∈ U, ∀ q, Bs.inSS q → B.sgs q (γ x) ∈ V) → ContinuousOn H V → AEStronglyMeasurable (fun x => B.JF Bs H (γ x)) (μ.restrict U) := by
  first | exact @GlobalTheory.besselJ_family_aestronglyMeasurable | exact GlobalTheory.besselJ_family_aestronglyMeasurable | (intros; apply GlobalTheory.besselJ_family_aestronglyMeasurable <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

open Matrix in
theorem eh_inv_entry : ∀ (k r : ℕ) (a b c i : Fin (2 * r + k + 1)), ∀ g ∈ B.GV k r, Q.EH k r a b (fun y : B.Mat k r => y⁻¹ c i) g = -(if a = c then g⁻¹ b i else 0) := by
  intro k r a b c i g _
  have h := Formalism.FourierDecayAlt.P.Qx5.eh_inv (k := k) (r := r) (LinearMap.proj c) (Pi.single i 1) g a b
  have e : (fun y : B.Mat k r => y⁻¹ c i) = fun y : B.Mat k r => (LinearMap.proj c : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (y⁻¹ *ᵥ Pi.single i 1) := by
    funext y
    simp [Matrix.mulVec_single_one]
  rw [e]
  refine h.trans ?_
  by_cases hac : a = c
  · subst hac
    simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single, hac]
end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.ShortMove

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

def Marked {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (l : Level H)
    (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (mk : Dw.La → (Fin r → D.host.E)) (h : GA D V) : Prop :=
  (Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V h : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V h, finVec V (mk a ∘ Fin.cast hr) - (finHom V h).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
def FormPlus {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (io x)) (V.frame.equivFun.symm (io y)))

end GlobalTheory.ShortMove
end
end
