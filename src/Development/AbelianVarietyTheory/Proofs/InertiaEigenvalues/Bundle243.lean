module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle152
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle221
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle232
public import GroundTheory.LocalFields.HerbrandFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle226
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle233
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.PhiSat

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    W.φD T (a • y) = W.φA a • W.φD T y := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) y
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

theorem φD_map_Q {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) (y : W.DD T₂)
    (hy : y ∈ (W.N T₁).map (mapA W π)) : ∃ j : ℕ, W.Q ^ j • W.φD T₂ y ∈ (W.N T₁).map (mapA W π) := by
  obtain ⟨n₁, hn₁, rfl⟩ := hy
  obtain ⟨j, hj⟩ := W.N_φ T₁ n₁ hn₁
  refine ⟨j, W.Q ^ j • W.φD T₁ n₁, hj, ?_⟩
  rw [map_smul]
  congr 1
  exact W.map_φ π n₁

theorem φD_satM_gen (l : ℕ) (hlp : l.Prime) (hp : PD.p = l) {T₁ T₂ : LocLat G Qp LL O}
    (π : LatHom T₁.L T₂.L) (x : W.DD T₂)
    (hx : x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) :
    ∃ k : ℕ, W.Q ^ k • W.φD T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) := by
  set N'' := (W.N T₁).map (mapA W π) with hN''
  obtain ⟨hxN, k, hk1, hk2⟩ := hx
  let J : Ideal (LetA O n) :=
    { carrier := {a | ∃ j : ℕ, W.Q ^ j • a • W.φD T₂ x ∈ N''}
      add_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        rw [add_smul, smul_add, pow_add]
        refine N''.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact N''.smul_mem _ hi
        · rw [mul_smul]; exact N''.smul_mem _ hj
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨j, hj⟩
        refine ⟨j, ?_⟩
        rw [smul_eq_mul, mul_smul, smul_comm]
        exact N''.smul_mem c hj }
  have hJ : ∀ (a : LetA O n) (j : ℕ), W.Q ^ j • a • W.φD T₂ x ∈ N'' → ∀ (b : LetA O n) (E : ℕ), j ≤ E →
      W.Q ^ E • (b * a) • W.φD T₂ x ∈ N'' := by
    intro a j hj b E hjE
    have : W.Q ^ E • (b * a) • W.φD T₂ x = (W.Q ^ (E - j) * b) • (W.Q ^ j • a • W.φD T₂ x) := by
      rw [smul_smul, smul_smul, smul_smul]
      congr 1
      conv_lhs => rw [← Nat.sub_add_cancel hjE, pow_add]
      ring
    rw [this]
    exact N''.smul_mem _ hj
  have hl : ((l : ℕ) : LetA O n) ^ k ∈ J := by
    obtain ⟨j, hj⟩ := φD_map_Q W π _ hk1
    refine ⟨j, ?_⟩
    rw [φD_smulA, map_pow, map_natCast] at hj
    exact hj
  have hπq : (letπ * W.q) ^ k ∈ J := by
    obtain ⟨j, hj⟩ := φD_map_Q W π _ hk2
    refine ⟨j, ?_⟩
    rw [φD_smulA, map_pow, W.φA_π] at hj
    exact hj
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hlp (letπ : LetA O n) 1
  have hq : letπ * W.q = (letπ + 1 : LetA O n) ^ l - 1 := by
    funext i
    have := W.q₀_def
    rw [hp] at this
    simp [letπ, LocWach.q, this, add_comm]
  have hπl : (letπ : LetA O n) ^ l = letπ * W.q - (l : LetA O n) * (letπ * r) := by
    rw [hq, hr]; ring
  have hrad : (letπ : LetA O n) ^ l ∈ J.radical := by
    rw [hπl]
    refine Ideal.sub_mem _ (Ideal.mem_radical_of_pow_mem (Ideal.le_radical hπq)) ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mem_radical_of_pow_mem (Ideal.le_radical hl))
  obtain ⟨m, j₁, hj₁⟩ := hrad
  obtain ⟨j₂, hj₂⟩ := hl
  obtain ⟨a, ha⟩ := W.N_φ T₂ x hxN
  change W.Q ^ a • W.φD T₂ x ∈ W.N T₂ at ha
  refine ⟨a + j₁ + j₂, ?_, k + l * m, ?_, ?_⟩
  · rw [add_assoc, pow_add, mul_comm, mul_smul]
    exact (W.N T₂).smul_mem _ ha
  · have := hJ _ j₂ hj₂ ((l : LetA O n) ^ (l * m)) (a + j₁ + j₂) (by omega)
    rw [← pow_add, Nat.add_comm (l * m) k] at this
    rw [smul_comm]
    exact this
  · have := hJ _ j₁ hj₁ ((letπ : LetA O n) ^ k) (a + j₁ + j₂) (by omega)
    rw [← pow_mul, ← pow_add] at this
    rw [smul_comm]
    exact this

theorem φD_satM_Q : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), ∃ k : ℕ, W.Q ^ k • W.φD T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) := by
  intro D HW F l _ K s LL h W T₁ T₂ π _hc₁ _hc₂ x hx
  exact φD_satM_gen W l Fact.out ((D.loc l).PD_p K) π x hx

end GlobalTheory.NL.PhiSat
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.GamSat

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem γ_smul (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.γ T (a • x) = W.γA W.gam a • W.γ T x := by
  have := W.γD_smul T W.gam (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem γA_π (g : W.Gam) : ∃ u u' : LetA O n, u * u' = 1 ∧ W.γA g letπ = letπ * u := by
  obtain ⟨h0, h1⟩ := W.γ₀_X g
  obtain ⟨u₀, hu₀⟩ := PowerSeries.X_dvd_iff.mpr h0
  have hc : PowerSeries.constantCoeff u₀ = ((W.χΓ g : Oˣ) : O) := by
    rw [← h1, hu₀, PowerSeries.coeff_succ_X_mul]
    simp
  refine ⟨fun _ => u₀, fun _ => PowerSeries.invOfUnit u₀ (W.χΓ g), ?_, ?_⟩
  · funext i
    exact PowerSeries.mul_invOfUnit u₀ _ hc
  · funext i
    simp [LocWach.γA, letγ, letπ, hu₀]

theorem map_γ_mem {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) :
    ∀ y ∈ (W.N T₁).map (mapA W π), W.γ T₂ y ∈ (W.N T₁).map (mapA W π) := by
  rintro _ ⟨n₁, hn₁, rfl⟩
  refine ⟨W.γD T₁ W.gam n₁, W.N_Γ T₁ W.gam n₁ hn₁, ?_⟩
  change W.map π (W.γD T₁ W.gam n₁) = W.γD T₂ W.gam (W.map π n₁)
  exact W.map_γ π W.gam n₁

theorem pow_smul_γ_mem (T : LocLat G Qp LL O) (P : Submodule (LetA O n) (W.DD T))
    (hP : ∀ y ∈ P, W.γ T y ∈ P) (p k : ℕ) (x : W.DD T)
    (h1 : ((p : LetA O n)) ^ k • x ∈ P) (h2 : (letπ : LetA O n) ^ k • x ∈ P) :
    ((p : LetA O n)) ^ k • W.γ T x ∈ P ∧ (letπ : LetA O n) ^ k • W.γ T x ∈ P := by
  constructor
  · have := hP _ h1
    rw [γ_smul, map_pow, map_natCast] at this
    exact this
  · obtain ⟨u, u', huu, hu⟩ := γA_π W W.gam
    have := P.smul_mem (u' ^ k) (hP _ h2)
    have e : u' ^ k * (letπ * u) ^ k = letπ ^ k := by
      rw [← mul_pow, mul_left_comm, mul_comm u' u, huu, mul_one]
    rw [γ_smul, map_pow, hu, smul_smul, e] at this
    exact this

theorem gam_sat (p : ℕ) (T₁ T₂ : LocLat G Qp LL O) (π : LatHom T₁.L T₂.L) :
    (∀ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂),
      W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧
    ∀ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂),
      W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂)).map
        (smulA W T₂ letπ) := by
  set P := (W.N T₁).map (mapA W π) with hPdef
  have hP := map_γ_mem W π
  refine ⟨?_, ?_⟩
  · rintro x ⟨hx, k, h1, h2⟩
    exact ⟨W.N_Γ T₂ W.gam x hx, k, pow_smul_γ_mem W T₂ P hP p k x h1 h2⟩
  · rintro x ⟨hx, k, h1, h2⟩
    obtain ⟨y, hy, hxy⟩ := W.N_π T₂ W.gam x hx
    obtain ⟨n₁, hn₁, hn₁x⟩ := h1
    obtain ⟨m₁, hm₁, hnm⟩ := W.N_π T₁ W.gam n₁ hn₁
    have hγ := pow_smul_γ_mem W T₂ P hP p k x ⟨n₁, hn₁, hn₁x⟩ h2

    have hinj : ∀ z w : W.DD T₂, (letπ : LetA O n) • z = (letπ : LetA O n) • w → z = w := by
      intro z w hzw
      obtain ⟨u, hu⟩ := W.EE_π
      rw [← algebraMap_smul W.EE (letπ : LetA O n) z, ← algebraMap_smul W.EE (letπ : LetA O n) w,
        ← hu] at hzw
      have := congrArg (fun z => ((u⁻¹ : W.EEˣ) : W.EE) • z) hzw
      simpa [smul_smul] using this
    have hly : ((p : LetA O n)) ^ k • y = mapA W π m₁ := by
      apply hinj
      rw [smul_comm, ← hxy, smul_sub, ← LinearMap.map_smul, ← hnm]
      have e1 : W.γD T₂ W.gam (((p : LetA O n)) ^ k • x) = ((p : LetA O n)) ^ k • W.γD T₂ W.gam x := by
        have := γ_smul W T₂ (((p : LetA O n)) ^ k) x
        rw [map_pow, map_natCast] at this
        exact this
      rw [← e1, ← hn₁x]
      change W.γD T₂ W.gam (W.map π n₁) - W.map π n₁ = W.map π (W.γD T₁ W.gam n₁ - n₁)
      rw [map_sub, W.map_γ]
    refine ⟨y, ⟨hy, k + 1, ?_, ?_⟩, ?_⟩
    · rw [pow_succ', mul_smul, hly]
      exact P.smul_mem _ ⟨m₁, hm₁, rfl⟩
    · rw [pow_succ, mul_smul, ← hxy, smul_sub]
      exact P.sub_mem hγ.2 h2
    · change (letπ : LetA O n) • y = _
      rw [← hxy]
      rfl

end Generic

theorem wachSaturation_gamma_stable_and_sub_one_mem_pi_smul : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → (∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).map (smulA W T₂ letπ) := by
  intro D HW F l _ K s LL h W T₁ T₂ π _ _
  exact gam_sat W l T₁ T₂ π

end GlobalTheory.NL.GamSat
end

section

noncomputable section

open Formalism.Per GlobalTheory.PSer Filter Topology
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem summable_Lam_terms (l : ℕ) [Fact l.Prime] (h i : ℕ) (y : ℕ → Fl l) (ρ : ℝ)
    (hh : 1 ≤ h) (hρ : ρ < 1) (hy : ∀ k, ‖sh (y k)‖ ≤ ρ) :
    Summable fun k : ℕ => (l : ℂ_[l]) ^ k * lam h i (y k) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h2 : Tendsto (fun k : ℕ => ((l : ℝ)⁻¹) ^ k * gam l h i ρ) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (by linarith))
      (inv_lt_one_of_one_lt₀ hl)).mul_const (gam l h i ρ)
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) h2
  rw [norm_mul, norm_pow, Laws.norm_l]
  exact mul_le_mul_of_nonneg_left (lam_hasSum_norm_le_frob l h i ρ (y k) hh hρ (hy k)).2.1
    (pow_nonneg (inv_nonneg.2 (by linarith)) _)

theorem sum_mul_Lam_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (i : ℕ) (y : ℕ → Fin h → Fl l) (ρ : ℝ),
    1 ≤ h → ρ < 1 → (∀ k j, ‖sh (y k j)‖ ≤ ρ) →
    HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * ∑ j, μ j * lam h i (y k j)) 0 →
    ∑ j, μ j * abelian₂ h i (fun k => y k j) = 0 := by
  intro l _ h μ i y ρ hh hρ hy hs
  have hsum : ∀ j, Summable fun k : ℕ => μ j * ((l : ℂ_[l]) ^ k * lam h i (y k j)) := fun j =>
    (summable_Lam_terms l h i (fun k => y k j) ρ hh hρ (fun k => hy k j)).mul_left (μ j)
  calc ∑ j, μ j * abelian₂ h i (fun k => y k j)
      = ∑ j, ∑' k : ℕ, μ j * ((l : ℂ_[l]) ^ k * lam h i (y k j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold abelian₂
        rw [tsum_mul_left]
    _ = ∑' k : ℕ, ∑ j, μ j * ((l : ℂ_[l]) ^ k * lam h i (y k j)) :=
        (Summable.tsum_finsetSum fun j _ => hsum j).symm
    _ = ∑' k : ℕ, (l : ℂ_[l]) ^ k * ∑ j, μ j * lam h i (y k j) := by
        refine tsum_congr fun k => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = 0 := hs.tsum_eq

end GlobalTheory.PSer

end
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem gam_norm_natCast_eq (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  simpa using h

theorem gam_exists_max_of_tendsto (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : Filter.Tendsto f Filter.cofinite (nhds 0)) : ∃ n₀, ∀ n, f n ≤ f n₀ := by
  by_cases hall : ∀ n, f n = 0
  · exact ⟨0, fun n => by rw [hall n, hall 0]⟩
  push_neg at hall
  obtain ⟨m, hm⟩ := hall
  have hmpos : 0 < f m := lt_of_le_of_ne (hf0 m) (Ne.symm hm)
  have hev : ∀ᶠ n in Filter.cofinite, f n < f m := hf (Iio_mem_nhds hmpos)
  have hfin : {n | ¬ f n < f m}.Finite := Filter.eventually_cofinite.mp hev
  have hmem : m ∈ hfin.toFinset := by simp
  obtain ⟨n₀, hn₀, hmax⟩ := hfin.toFinset.exists_max_image f ⟨m, hmem⟩
  refine ⟨n₀, fun n => ?_⟩
  by_cases hn : f n < f m
  · exact hn.le.trans (hmax m hmem)
  · exact hmax n (by simpa using hn)

theorem gam_laws : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ n : ℤ, ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j r) ∧ (∃ n : ℤ, gam l h j r = ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) ∧ 0 ≤ gam l h j r ∧ (0 < r → 0 < gam l h j r) ∧ gam l h j (r ^ l ^ h) = ‖(l : ℂ_[l])‖ * gam l h j r ∧ ∀ s : ℝ, r < s → s < 1 → gam l h j r < gam l h j s := by
  intro l _ h j r h1 hr0 hr1
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hlR : (1 : ℝ) < l := by exact_mod_cast hl
  have ha := gam_norm_natCast_eq l
  set a := ‖(l : ℂ_[l])‖ with ha_def
  have ha0 : 0 < a := by rw [ha]; positivity

  have key : ∀ t : ℝ, 0 ≤ t → t < 1 →
      (∀ n : ℤ, a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j t) ∧
      (∃ n : ℤ, gam l h j t = a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ))) := by
    intro t ht0 ht1
    set f : ℤ → ℝ := fun n => a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ)) with hf_def
    have hf0 : ∀ n, 0 ≤ f n := fun n => mul_nonneg (zpow_nonneg ha0.le _) (Real.rpow_nonneg ht0 _)
    obtain ⟨n₀, hn₀⟩ := gam_exists_max_of_tendsto f hf0 (GlobalTheory.T.tendsto_untiltFrobeniusSeries_term_norms_zero l h j t h1 ht0 ht1)
    have hbdd : BddAbove (Set.range f) := ⟨f n₀, by rintro _ ⟨n, rfl⟩; exact hn₀ n⟩
    have hg : gam l h j t = ⨆ n, f n := rfl
    refine ⟨fun n => ?_, n₀, ?_⟩
    · rw [hg]; exact le_ciSup hbdd n
    · rw [hg]; exact le_antisymm (ciSup_le hn₀) (le_ciSup hbdd n₀)
  obtain ⟨hle, n₀, hn₀⟩ := key r hr0 hr1
  refine ⟨hle, ⟨n₀, hn₀⟩, ?_, ?_, ?_, ?_⟩
  · rw [hn₀]; exact mul_nonneg (zpow_nonneg ha0.le _) (Real.rpow_nonneg hr0 _)
  · intro hr
    exact lt_of_lt_of_le (mul_pos (zpow_pos ha0 _) (Real.rpow_pos_of_pos hr _)) (hle 0)
  ·
    have hq0 : 0 ≤ r ^ l ^ h := pow_nonneg hr0 _
    have hq1 : r ^ l ^ h < 1 := pow_lt_one₀ hr0 hr1 (by positivity)
    obtain ⟨hle', m₀, hm₀⟩ := key (r ^ l ^ h) hq0 hq1
    have shift : ∀ n : ℤ, a ^ (-n) * (r ^ l ^ h) ^ ((l : ℝ) ^ (n * h + j : ℤ)) =
        a * (a ^ (-(n + 1)) * r ^ ((l : ℝ) ^ ((n + 1) * h + j : ℤ))) := by
      intro n
      have e1 : (r ^ l ^ h) ^ ((l : ℝ) ^ (n * h + j : ℤ)) = r ^ ((l : ℝ) ^ ((n + 1) * h + j : ℤ)) := by
        rw [← Real.rpow_natCast r (l ^ h), ← Real.rpow_mul hr0]
        congr 1
        have hl0 : (l : ℝ) ≠ 0 := by positivity
        rw [show ((n + 1) * h + j : ℤ) = (h : ℤ) + (n * h + j) by ring, zpow_add₀ hl0 (h : ℤ) (n * h + j), zpow_natCast, Nat.cast_pow]
      have e2 : a ^ (-n) = a * a ^ (-(n + 1)) := by
        rw [show -n = 1 + (-(n + 1)) by ring, zpow_add₀ ha0.ne', zpow_one]
      rw [e1, e2]; ring
    apply le_antisymm
    · rw [hm₀, shift]
      exact mul_le_mul_of_nonneg_left (hle (m₀ + 1)) ha0.le
    · rw [hn₀]
      have := hle' (n₀ - 1)
      rw [shift, show n₀ - 1 + 1 = n₀ by ring] at this
      exact this
  · intro s hrs hs1
    have hs0 : 0 < s := lt_of_le_of_lt hr0 hrs
    obtain ⟨hles, -⟩ := key s hs0.le hs1
    rw [hn₀]
    refine lt_of_lt_of_le ?_ (hles n₀)
    apply mul_lt_mul_of_pos_left _ (zpow_pos ha0 _)
    exact Real.rpow_lt_rpow hr0 hrs (zpow_pos (by positivity) _)

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_mem_upperRamificationGroup_jumpSum_not_mem :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L]
      [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
      [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)),
      lowerRamificationGroup F L 0 = ⊤ → B ≠ ⊤ →
        ∃ σ ∈ upperRamificationGroup F L ((jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ)), σ ∉ B := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ B h0 hB
  obtain ⟨hanti, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_initialSegment_not_inf_le_filtration _ (wild F L) ⊤ B hanti hbot
  have hjs := GlobalTheory.T.ramificationJumpSum_eq_sum_range _ (wild F L) ⊤ B n hanti hn
  have hphi := GlobalTheory.T.card_mul_herbrandPhi_natCast_totallyRamified F L h0 n
  simp only [top_inf_eq] at hjs hn
  have hcard : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ) := by
    exact_mod_cast Nat.card_pos
  have hidx : (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ) = herbrandPhi F L n := by
    rw [hjs, ← hphi]
    field_simp
  rw [hidx, upperRamificationGroup_herbrandPhi, lowerRamificationGroupReal_natCast]
  cases n with
  | zero =>
    obtain ⟨σ, hσ⟩ : ∃ σ, σ ∉ B := by
      by_contra h
      push_neg at h
      exact hB (eq_top_iff.mpr fun σ _ => h σ)
    refine ⟨σ, ?_, hσ⟩
    rw [Nat.cast_zero, h0]
    exact Subgroup.mem_top σ
  | succ k =>
    have hk : ¬ wild F L k ≤ B := (hn k).mp (Nat.lt_succ_self k)
    obtain ⟨σ, hσ, hσB⟩ := SetLike.not_le_iff_exists.mp hk
    refine ⟨σ, ?_, hσB⟩
    have : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
    rw [this]
    exact hσ

end GlobalTheory.PMon.Ram
end

section

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass.FamCont

theorem epsU_cont {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    Continuous fun g => ((epsU N i g : (N.O i)ˣ) : N.O i) := by
  have h : ∀ g, ((epsU N i g : (N.O i)ˣ) : N.O i) =
      ((N.chi i 1 g : (N.O i)ˣ) : N.O i) * ((N.chi i 2 g⁻¹ : (N.O i)ˣ) : N.O i) := by
    intro g
    have := R.rank_add_five_le
    rw [← Units.val_mul, N.chi_def i 2 (by omega) (by omega)]
    simp [Glob.epsO]
  simp only [h]
  exact (N.chi_cont i 1).mul ((N.chi_cont i 2).comp continuous_inv)

theorem stepCont : StepCont := by
  intro D i r hr x
  have hc := (hr x).1
  constructor
  · have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
      (D.nd.chi_cont i 1).comp continuous_inv
    refine (h1.smul hc).congr fun g => ?_
    simp [rTwO, twistM, rO]
  · have h1 := (D.nd.chi_cont i 1).mul (epsU_cont D.nd i)
    have h2 := (hc.comp continuous_inv).matrix_transpose
    refine (h1.smul h2).congr fun g => ?_
    rfl

end GlobalTheory.Pass.FamCont

end
end
