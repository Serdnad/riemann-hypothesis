module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle002
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle341
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle405
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section

open GlobalTheory.WachUse GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing

namespace GlobalTheory.WachUse.HeightsProof

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem letφ_letE (i : ZMod n) : letφ W.φ₀ (letE (i - 1) : LetA O n) = letE i := by
  funext j
  change W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = (letE i : LetA O n) j
  by_cases hj : j = i
  · subst hj
    simp [letE]
  · have hj' : j - 1 ≠ i - 1 := fun h => hj (sub_left_injective h)
    simp [letE, hj, hj']

theorem φD_letE (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    W.φD T ((letE (i - 1) : LetA O n) • x) = (letE i : LetA O n) • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE (letE (i - 1))) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul, letφ_letE] at this

theorem Nl_le (T : LocLat G Qp LL O) (i : ZMod n) : W.Nl T i ≤ W.N T := by
  rintro _ ⟨x, hx, rfl⟩
  exact (W.N T).smul_mem _ hx

theorem of_heightBounds (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) (hb : HeightBounds W T M h) (i : ZMod n) :
    (∀ x ∈ W.N T, W.Q ^ M i • (letE i : LetA O n) • W.φD T x ∈ W.N T) ∧
      ∀ y ∈ W.N T, W.Q ^ h i • (letE i : LetA O n) • y ∈ W.φpull T := by
  refine ⟨fun x hx => Nl_le W T i ((hb i).1 _ ?_), fun y hy => ?_⟩
  · rw [← φD_letE]
    exact Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · exact Submodule.span_mono (Set.image_mono (Nl_le W T (i - 1))) ((hb i).2 _ ⟨y, hy, rfl⟩)

theorem jumpsOverLetters_of_crysWith (T : LocLat G Qp LL O) [FiniteDimensional LL ↥(DdR PD T.ρ)]
    (U : ZMod n → Multiset ℤ) (M h : ZMod n → ℕ) (hU : CrysWith PD W.emb T.ρ U)
    (hb : ∀ i, ∀ u ∈ U i, -(M i : ℤ) ≤ u ∧ u ≤ h i) : JumpsOverLetters W T M h := by
  intro i τ hτ a ha
  have h1 := (GlobalTheory.Per.JumpMult.jump_iff_of_finite PD T.ρ τ a).2.2.1 ha
  rw [hU.2 i τ hτ a] at h1
  exact hb i a (Multiset.count_ne_zero.1 (by exact_mod_cast h1))

end Generic

theorem heights_of_finite {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {E : LocFon l P AI H} {C : LocCmpT l P AI H E} (hJ : HeightsFromJumps l P AI H E C)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (hfin : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) T.ρ)) :
    Heights (H.W K s LL h) := by
  intro T U M hh hU hb
  haveI := hfin T
  exact of_heightBounds _ T M hh
    (hJ K s LL h T hU.1 M hh (jumpsOverLetters_of_crysWith _ T U M hh hU hb)).1

theorem heights_of_caseA : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (E : LocFon l P AI H) (C : LocCmpT l P AI H E), Nonempty (LocTied l P AI) → GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.HeightsFromJumps l P AI H E C → ∀ (K LL : FinExt l) (h : CaseA K LL), Heights (H.W K 1 LL h.2.2) := by
  rintro l _ P AI H E C ⟨Ti⟩ hJ K LL h
  exact heights_of_finite hJ K 1 LL h.2.2 fun T => (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI Ti K LL T.V T.ρ).1

end GlobalTheory.WachUse.HeightsProof
end
end

section

noncomputable section

open Filter Topology
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.GaussMono

theorem eventually_iSup_eq_monomial_left (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hG : (⨆ n, c n * ρ ^ n) ≠ 0) :
    ∃ i, ∀ᶠ r in 𝓝[≤] ρ, (⨆ n, c n * r ^ n) = c i * r ^ i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < c j := by
    by_contra h
    push_neg at h
    apply hG
    have : ∀ n, c n = 0 := fun n => le_antisymm (h n) (h0 n)
    simp [this]
  have hσ0 : 0 < ρ / 2 := by positivity
  have hσρ : ρ / 2 < ρ := by linarith
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (mul_pos hj (pow_pos hσ0 j)) hρ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (insert j (Finset.range M))
    (fun n => toLex (c n * ρ ^ n, OrderDual.toDual n)) ⟨j, Finset.mem_insert_self _ _⟩
  have hpos : ∀ᶠ r in 𝓝[≤] ρ, ρ / 2 < r := (eventually_gt_nhds hσρ).filter_mono nhdsWithin_le_nhds
  have key : ∀ n ∈ insert j (Finset.range M), ∀ᶠ r in 𝓝[≤] ρ, c n * r ^ n ≤ c i * r ^ i := by
    intro n hn
    rcases Prod.Lex.toLex_le_toLex.1 (hi n hn) with h | ⟨h, h'⟩
    · have : ∀ᶠ r in 𝓝 ρ, c n * r ^ n < c i * r ^ i :=
        ContinuousAt.eventually_lt (f := fun r : ℝ => c n * r ^ n) (g := fun r : ℝ => c i * r ^ i)
          (by fun_prop) (by fun_prop) h
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
    · filter_upwards [self_mem_nhdsWithin, hpos] with r hr hr0
      have hr : r ≤ ρ := hr
      have hr0 : 0 ≤ r := hσ0.le.trans hr0.le
      simp only at h h'
      have hin : i ≤ n := OrderDual.toDual_le_toDual.1 h'
      have e : ∀ m, c m * r ^ m = c m * ρ ^ m * (r / ρ) ^ m := fun m => by
        rw [div_pow]; field_simp
      rw [e n, e i, h]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (div_nonneg hr0 hρ.le) ((div_le_one hρ).2 hr) hin)
        (mul_nonneg (h0 _) (pow_nonneg hρ.le _))
  refine ⟨i, ?_⟩
  filter_upwards [(eventually_all_finset _).2 key, hpos, self_mem_nhdsWithin] with r hk hrσ hr
  have hr : r ≤ ρ := hr
  have hr0 : 0 ≤ r := hσ0.le.trans hrσ.le
  have hall : ∀ n, c n * r ^ n ≤ c i * r ^ i := by
    intro n
    by_cases hn : n < M
    · exact hk n (Finset.mem_insert_of_mem (Finset.mem_range.2 hn))
    · refine le_trans ?_ (hk j (Finset.mem_insert_self _ _))
      calc c n * r ^ n ≤ 1 * ρ ^ n := by gcongr; exact h1 n
        _ ≤ ρ ^ M := by rw [one_mul]; exact pow_le_pow_of_le_one hρ.le hρ1.le (not_lt.1 hn)
        _ ≤ c j * (ρ / 2) ^ j := hM.le
        _ ≤ c j * r ^ j := by gcongr
  exact le_antisymm (ciSup_le hall) (le_ciSup (f := fun n => c n * r ^ n) ⟨_, Set.forall_mem_range.2 hall⟩ i)

theorem eventually_monomial {R : Type} [CommRing R] (p : R) {L ρ : ℝ} (hL : 0 < L) (hLρ : L ≤ ρ) (hρ1 : ρ < 1)
    (N : ℝ → R → ℝ)
    (hN : ∀ r, L ≤ r → r < 1 → (∀ x, N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧
      (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ N r p = r)
    (b : R) (hb : 0 < N ρ b)
    (hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : R) (c : ℕ → ℝ), p ^ k * b = a + p ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, L ≤ r → r < 1 → N r a = ⨆ n, c n * r ^ n)
    (f : Filter ℝ) (hf : f ≤ 𝓝 ρ) (hf0 : pure ρ ≤ f) (hfL : ∀ᶠ r in f, L ≤ r ∧ r < 1)
    (hmono : ∀ c : ℕ → ℝ, (∀ n, 0 ≤ c n) → (∀ n, c n ≤ 1) → (⨆ n, c n * ρ ^ n) ≠ 0 →
      ∃ i, ∀ᶠ r in f, (⨆ n, c n * r ^ n) = c i * r ^ i) :
    ∃ (c : ℝ) (k : ℤ), 0 < c ∧ ∀ᶠ r in f, N r b = c * r ^ k := by
  have hρ : 0 < ρ := hL.trans_le hLρ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb hρ1
  obtain ⟨k, a, z, c, hab, h0, h1, hc⟩ := hd n
  have hz : ∀ r, L ≤ r → r < 1 → N r (p ^ (k + n) * z) ≤ r ^ (k + n) := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [GlobalTheory.GaussSlope.map_pow_mul _ e4, e5]
    exact mul_le_of_le_one_right (pow_nonneg (hL.le.trans hr) _) (e1 z)
  have hbb : ∀ r, L ≤ r → r < 1 → N r (p ^ k * b) = r ^ k * N r b := by
    intro r hr hr1
    obtain ⟨-, -, -, e4, e5⟩ := hN r hr hr1
    rw [GlobalTheory.GaussSlope.map_pow_mul _ e4, e5]
  have ha : ρ ^ (k + n) < N ρ a := by
    obtain ⟨-, e2, e3, -, -⟩ := hN ρ hLρ hρ1
    have h2 : ρ ^ (k + n) < N ρ (p ^ k * b) := by
      rw [hbb ρ hLρ hρ1, pow_add]
      exact mul_lt_mul_of_pos_left hn (pow_pos hρ _)
    have h3 : a = p ^ k * b + -(p ^ (k + n) * z) := by rw [hab]; ring
    rw [h3, GlobalTheory.GaussSlope.add_eq_of_lt _ e2 e3 (by rw [e3]; exact (hz ρ hLρ hρ1).trans_lt h2)]
    exact h2
  rw [hc ρ hLρ hρ1] at ha
  obtain ⟨i, hi⟩ := hmono c h0 h1 ((pow_pos hρ _).trans ha).ne'
  have hiρ : (⨆ n, c n * ρ ^ n) = c i * ρ ^ i := Filter.mem_pure.1 (hf0 hi)
  rw [hiρ] at ha
  have hci : 0 < c i := (mul_pos_iff_of_pos_right (pow_pos hρ i)).1 ((pow_pos hρ _).trans ha)
  have h4 : ∀ᶠ r in 𝓝 ρ, r ^ (k + n) < c i * r ^ i :=
    ContinuousAt.eventually_lt (f := fun r : ℝ => r ^ (k + n)) (g := fun r : ℝ => c i * r ^ i)
      (by fun_prop) (by fun_prop) ha
  refine ⟨c i, (i : ℤ) - k, hci, ?_⟩
  filter_upwards [hi, hf h4, hfL] with r hr1 hr2 hr
  obtain ⟨hr, hr3⟩ := hr
  have hr0 : 0 < r := hL.trans_le hr
  obtain ⟨-, e2, e3, -, -⟩ := hN r hr hr3
  have h6 := hbb r hr hr3
  have h7 : N r a = c i * r ^ i := by rw [hc r hr hr3, hr1]
  rw [hab, GlobalTheory.GaussSlope.add_eq_of_lt _ e2 e3 (by rw [h7]; exact (hz r hr hr3).trans_lt hr2), h7] at h6
  rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc, h6]
  field_simp

end GlobalTheory.GaussMono

namespace GlobalTheory.PMon.Gauss

theorem gC_monomial_near : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ₀ : ℝ, (l : ℝ)⁻¹ ≤ ρ₀ →
    ρ₀ < 1 → (∃ (c : ℝ) (k : ℤ) (ρ₂ : ℝ), 0 < c ∧ ρ₀ < ρ₂ ∧ ρ₂ < 1 ∧
      ∀ ρ ∈ Set.Icc ρ₀ ρ₂, gC l ρ x = c * ρ ^ k) ∧
    ((l : ℝ)⁻¹ < ρ₀ → ∃ (c : ℝ) (k : ℤ) (ρ₁ : ℝ), 0 < c ∧ (l : ℝ)⁻¹ ≤ ρ₁ ∧ ρ₁ < ρ₀ ∧
      ∀ ρ ∈ Set.Icc ρ₁ ρ₀, gC l ρ x = c * ρ ^ k) := by
  intro l _ x hx ρ₀ hρl hρ1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hL : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hρ0 : 0 < ρ₀ := hL.trans_le hρl
  have hN : ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ y, gC l r y ≤ 1) ∧
      (∀ y z, gC l r (y + z) ≤ max (gC l r y) (gC l r z)) ∧ (∀ y, gC l r (-y) = gC l r y) ∧
      (∀ y z, gC l r (y * z) = gC l r y * gC l r z) ∧ gC l r (l : Formalism.Per.Acris l) = r := by
    intro r hr hr1
    obtain ⟨e1, e2, e3, e4, e5⟩ := isGauss_gC_target l r hr hr1
    refine ⟨fun y => (e1 y).2, e2, e3, e4, ?_⟩
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, e5]
    exact GlobalTheory.GaussSlope.gauss_l l (hL.le.trans hr)
  have hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : Formalism.Per.Acris l) (c : ℕ → ℝ),
      (l : Formalism.Per.Acris l) ^ k * x = a + (l : Formalism.Per.Acris l) ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → gC l r a = ⨆ n, c n * r ^ n := by
    intro n
    obtain ⟨s, z, h⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x n
    obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
    refine ⟨k, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a, z,
      fun n => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n), ?_,
      fun n => by positivity, fun n => ?_, fun r hr hr1 => (isGauss_gC_target l r hr hr1).2.2.2.2 a⟩
    · rw [h, mul_add, ha, pow_add, mul_assoc]
    · exact Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)
  have hb : 0 < gC l ρ₀ x := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ₀ hρl hρ1
  constructor
  · have hfL : ∀ᶠ r in 𝓝[≥] ρ₀, (l : ℝ)⁻¹ ≤ r ∧ r < 1 := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hρ1).filter_mono nhdsWithin_le_nhds] with r hr hr1
      exact ⟨hρl.trans hr, hr1⟩
    obtain ⟨c, k, hc, hev⟩ := GlobalTheory.GaussMono.eventually_monomial (l : Formalism.Per.Acris l) hL hρl hρ1 (gC l) hN x hb
      hd (𝓝[≥] ρ₀) nhdsWithin_le_nhds (pure_le_nhdsWithin (Set.mem_Ici.2 le_rfl)) hfL
      (fun c h0 h1 hG => GlobalTheory.GaussSlope.eventually_iSup_eq_monomial c h0 h1 hρ0 hρ1 hG)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
    have hu : ρ₀ < u := hu
    obtain ⟨ρ₂, h2a, h2b⟩ := exists_between (lt_min hu hρ1)
    exact ⟨c, k, ρ₂, hc, h2a, h2b.trans_le (min_le_right _ _),
      fun r hr => hsub ⟨hr.1, hr.2.trans_lt (h2b.trans_le (min_le_left _ _))⟩⟩
  · intro hlt
    have hfL : ∀ᶠ r in 𝓝[≤] ρ₀, (l : ℝ)⁻¹ ≤ r ∧ r < 1 := by
      filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds] with r hr hr1
      exact ⟨(hr1 : (l : ℝ)⁻¹ < r).le, (hr : r ≤ ρ₀).trans_lt hρ1⟩
    obtain ⟨c, k, hc, hev⟩ := GlobalTheory.GaussMono.eventually_monomial (l : Formalism.Per.Acris l) hL hρl hρ1 (gC l) hN x hb
      hd (𝓝[≤] ρ₀) nhdsWithin_le_nhds (pure_le_nhdsWithin (Set.mem_Iic.2 le_rfl)) hfL
      (fun c h0 h1 hG => GlobalTheory.GaussMono.eventually_iSup_eq_monomial_left c h0 h1 hρ0 hρ1 hG)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsLE_iff_exists_Ioc_subset.1 hev
    have hu : u < ρ₀ := hu
    obtain ⟨ρ₁, h1a, h1b⟩ := exists_between (max_lt hu hlt)
    exact ⟨c, k, ρ₁, hc, (le_max_right _ _).trans h1a.le, h1b,
      fun r hr => hsub ⟨(le_max_left _ _).trans_lt (h1a.trans_le hr.1), hr.2⟩⟩

end GlobalTheory.PMon.Gauss

end
end

section

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable (l : ℕ) [Fact l.Prime]

lemma vrlaw_one_lt : (1 : ℝ) < l := by
  exact_mod_cast (Fact.out : l.Prime).one_lt

lemma vrlaw_rad (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1) :
    (l : ℝ)⁻¹ ≤ (l : ℝ) ^ (-r) ∧ (l : ℝ) ^ (-r) < 1 := by
  have hl := vrlaw_one_lt l
  constructor
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hl.le (by linarith)
  · exact Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)

lemma vrlaw_gC_zero (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : gC l ρ 0 = 0 := by
  have hG := isGauss_gC_target l ρ h0 h1
  have hm := hG.2.2.2.1 0 (l : Formalism.Per.Acris l)
  rw [zero_mul, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1] at hm
  have : gC l ρ 0 * (1 - ρ) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd h (by linarith)

theorem vr_laws : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ), 0 < r → r ≤ 1 →
    (∀ x y : Formalism.Per.Acris l, x ≠ 0 → y ≠ 0 → vr l r (x * y) = vr l r x + vr l r y) ∧
    (∀ x : Formalism.Per.Acris l, x ≠ 0 → φc l x ≠ 0 ∧ vr l r (φc l x) = l * vr l (r / l) x) ∧
    (∀ (x : Formalism.Per.Acris l) (n : ℕ), x ≠ 0 → vr l r ((l : Formalism.Per.Acris l) ^ n * x) = n * r + vr l r x) ∧
    ∀ x : Formalism.Per.Acris l, x ≠ 0 → vr l r x = -Real.logb l (gC l ((l : ℝ) ^ (-r)) x) := by
  intro l _ r hr0 hr1
  have hl := vrlaw_one_lt l
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨hρ0, hρ1⟩ := vrlaw_rad l r hr0 hr1
  set ρ : ℝ := (l : ℝ) ^ (-r) with hρ
  have hG := isGauss_gC_target l ρ hρ0 hρ1
  have hpos : ∀ x : Formalism.Per.Acris l, x ≠ 0 → 0 < gC l ρ x := fun x hx => GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ hρ0 hρ1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    simp only [vr]
    rw [← hρ, hG.2.2.2.1 x y, Real.logb_mul (hpos x hx).ne' (hpos y hy).ne']
    ring
  · intro x hx
    have hl' : (0 : ℝ) < l := hl0
    have hrl0 : 0 < r / l := div_pos hr0 hl'
    have hrl1 : r / l ≤ 1 := by
      rw [div_le_one hl']; linarith
    obtain ⟨hσ0, hσ1⟩ := vrlaw_rad l (r / l) hrl0 hrl1
    have he : ρ ^ ((1 : ℝ) / l) = (l : ℝ) ^ (-(r / l)) := by
      rw [hρ, ← Real.rpow_mul hl0.le]
      congr 1
      ring
    have hF := GlobalTheory.T.gaussNormAcris_frobenius_eq_pow_root_radius l ρ hρ0 hρ1 x
    rw [he] at hF
    have hxp : 0 < gC l ((l : ℝ) ^ (-(r / l))) x := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ hσ0 hσ1
    refine ⟨?_, ?_⟩
    · intro h0
      rw [h0, vrlaw_gC_zero l ρ hρ0 hρ1] at hF
      exact (pow_pos hxp l).ne' hF.symm
    · simp only [vr]
      rw [← hρ, hF, Real.logb_pow]
      ring
  · intro x n hx
    have hpow : ∀ m : ℕ, gC l ρ ((l : Formalism.Per.Acris l) ^ m * x) = ρ ^ m * gC l ρ x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', mul_assoc, hG.2.2.2.1, ih, (GlobalTheory.T.gaussNormAcris_basic_values l ρ hρ0 hρ1).2.1]
        ring
    simp only [vr]
    rw [← hρ, hpow n, Real.logb_mul (pow_pos (by rw [hρ]; exact Real.rpow_pos_of_pos hl0 _) n).ne' (hpos x hx).ne', Real.logb_pow,
      hρ, Real.logb_rpow hl0 hl.ne']
    ring
  · intro x _
    rfl

end GlobalTheory.PMon.Gauss

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.local_cup_pairing_reduced_cocycles : LocalTateDuality → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ (x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) (y : Z1 ((red i K ρ).comp (DecV N v).subtype)), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v → ∀ (lam : K →+ ZMod (X.l i ^ 1)) (w : Z2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))), (∀ g h : ↥(DecV N v), w.1 (g, h) = lam (x.1 g ⬝ᵥ red i K ρ g (y.1 h))) → (Submodule.Quotient.mk w : H2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))) = 0 := by
  first | exact @GlobalTheory.CupAbove.cup_eq_zero_above | exact GlobalTheory.CupAbove.cup_eq_zero_above | (intros; apply GlobalTheory.CupAbove.cup_eq_zero_above <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LatTied

theorem latStable_tied : ∀ (D : D7) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M) (Q : D.what₂.places.Pl → Finset (PlE D.host)),
    (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) →
    ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → GlobalTheory.EtaJoin.LatStable Tn.B j w := by
  intro D M Tn Q hQ hI j w h1 h2 hw
  classical
  by_cases hne : (D.nd.locs j w).Nonempty
  · obtain ⟨i, hi⟩ := hne
    have hwi : D.nd.w i = w := ((D.nd.locs_mem j w i).1 hi).2
    have hQc : Tn.B.Qc j w = Q w := by rw [← Tn.Q_eq j w i hi, hQ i, hwi]
    apply GlobalTheory.T.heckeStableLocalLattice_of_integral D M Tn.B j h1 h2 w
    rw [hQc]; exact hI j h1 h2 w hw
  · have hsub : Subsingleton (heckeAlg Tn.B j w) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      obtain ⟨I, hI'⟩ := Ideal.exists_maximal (heckeAlg Tn.B j w)
      obtain ⟨i, hi, -⟩ := Tn.mx_all j w h1 h2 hw I hI'
      exact hne ⟨i, hi⟩
    have h10 : (1 : Module.End (FractionRing (Tn.B.Oc j w)) (Tn.B.V j w)) = 0 := by
      have := congrArg Subtype.val (Subsingleton.elim (1 : heckeAlg Tn.B j w) 0)
      simpa using this
    have hx : ∀ y : Tn.B.V j w, y = 0 := fun y => by
      have := LinearMap.congr_fun h10 y
      simpa using this
    intro v k _ x _
    rw [hx (Tn.B.hK j w v k x)]
    exact Submodule.zero_mem _

end GlobalTheory.LatTied

end
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.exists_monodromy_eq_leadingCoeff_breuilKisinDescent : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → 1 ≤ η → η < H → 14 * H + (N + 2) * η < l → 10 * H + 2 ≤ l → IsAdicComplete (Ideal.span {(l : O)}) D.Y' → IsHausdorff (Ideal.span {(l : O)}) D.Z → ∀ y ∈ D.Y', ∃ y₀ ∈ D.Y', D.Mon y₀ = D.Lc (D.cls y) := by
  first | exact @GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent.exists_Mon_eq_Lc_cls | exact GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent.exists_Mon_eq_Lc_cls | (intros; apply GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent.exists_Mon_eq_Lc_cls <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtCore

theorem exists_continuous_complementFamily {D : D7} (h : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) :
    ∃ ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i)),
      (∀ π, Continuous
        (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))) ∧
      ∀ π ∈ D.nd.Z i, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.IsComplement D.nd i (r π) (ρ π) := by
  have key : ∀ π : D.nd.X i, ∃ ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i),
      Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
      (π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.IsComplement D.nd i (r π) ρ) := by
    intro π
    by_cases hπ : π ∈ D.nd.Z i
    · obtain ⟨ρ, hρ⟩ := h i π hπ (r π) (hr π)
      exact ⟨ρ, hρ.cont, fun _ => hρ⟩
    · exact ⟨1, continuous_const, fun h' => absurd h' hπ⟩
  choose ρ h1 h2 using key
  exact ⟨ρ, h1, h2⟩

theorem exists_ptFam : GlobalTheory.TwSys.Cheb → ∀ (D : D7), GlobalTheory.BlockComplement.GaloisRepsCusp D →
    (∀ i, ∃ r, GoodR D.nd i r) → ∃ r ρ, PtFam D r ρ := by
  intro hC D hG hr
  choose r hr using hr
  choose ρ h1 h2 using fun i =>
    exists_continuous_complementFamily (GlobalTheory.BlockComplement.complement_at hC D hG) i (r i) (hr i)
  exact ⟨r, ρ, hr, h1, h2⟩

end GlobalTheory.PtCore
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.senWeight_subquotient_model_mem_residues : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (N : Lats k n A.m), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.U i, ((u - Dt.w i : ℤ) : k) = x := by
  first | exact @GlobalTheory.Models.ModTh.sen_model_subquot_mem_U | exact GlobalTheory.Models.ModTh.sen_model_subquot_mem_U | (intros; apply GlobalTheory.Models.ModTh.sen_model_subquot_mem_U <;> assumption)
end
