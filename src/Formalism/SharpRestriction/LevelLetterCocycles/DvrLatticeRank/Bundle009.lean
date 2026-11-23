module

public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.SplitROfSteps
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 PowerSeries

section PS

variable {LL : Type*} [Field LL]

theorem eq_X_mul_shift (f : PowerSeries LL) (h0 : constantCoeff f = 0) :
    f = X * mk (fun k => coeff (k + 1) f) := by
  ext n
  rcases n with _ | n
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]

end PS

section Ev

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)

def Vs : PowerSeries LL := mk fun k => coeff (k + 1) (W.lev c ζ Eπ)

def Ui : PowerSeries LL := (Vs W c ζ Eπ)⁻¹ ^ h'

def ev (a : LetA O n) (i : ℤ) : LL :=
  if 0 ≤ i + h' then coeff (i + h').toNat (W.lev c ζ a * Ui W c ζ Eπ h') else 0

variable {W c ζ Eπ h'}

theorem levE_eq (h0 : constantCoeff (W.lev c ζ Eπ) = 0) : W.lev c ζ Eπ = X * Vs W c ζ Eπ :=
  eq_X_mul_shift _ h0

theorem Vs_cc (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) : constantCoeff (Vs W c ζ Eπ) ≠ 0 := by
  rw [Vs, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  exact h1

theorem Vs_Ui (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) : Vs W c ζ Eπ ^ h' * Ui W c ζ Eπ h' = 1 := by
  rw [Ui, ← mul_pow, PowerSeries.mul_inv_cancel _ (Vs_cc h1), one_pow]

theorem levΛ_eq (h0 : constantCoeff (W.lev c ζ Eπ) = 0) :
    W.lev c ζ (Eπ ^ h') = X ^ h' * Vs W c ζ Eπ ^ h' := by
  rw [map_pow, levE_eq h0, mul_pow]

theorem levΛ_Ui (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) :
    W.lev c ζ (Eπ ^ h') * Ui W c ζ Eπ h' = X ^ h' := by
  rw [levΛ_eq h0, mul_assoc, Vs_Ui h1, mul_one]

theorem ev_of_lt (a : LetA O n) {i : ℤ} (hi : i + h' < 0) : ev W c ζ Eπ h' a i = 0 := by
  unfold ev
  rw [if_neg (by omega)]

theorem ev_eq (a : LetA O n) {i : ℤ} (hi : 0 ≤ i + h') :
    ev W c ζ Eπ h' a i = coeff (i + h').toNat (W.lev c ζ a * Ui W c ζ Eπ h') := by
  unfold ev
  rw [if_pos hi]

theorem ev_add (a b : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (a + b) i = ev W c ζ Eπ h' a i + ev W c ζ Eπ h' b i := by
  unfold ev
  split_ifs
  · rw [map_add (W.lev c ζ) a b, add_mul, map_add (f := _)]
  · rw [add_zero]

theorem ev_zero (i : ℤ) : ev W c ζ Eπ h' (0 : LetA O n) i = 0 := by
  unfold ev
  split_ifs <;> simp

theorem ev_sum {ι : Type*} (s : Finset ι) (a : ι → LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (∑ k ∈ s, a k) i = ∑ k ∈ s, ev W c ζ Eπ h' (a k) i := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty, ev_zero]) ?_
  intro x s hx ih
  rw [Finset.sum_insert hx, Finset.sum_insert hx, ev_add, ih]

theorem ev_alg (x : O) (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (algebraMap O (LetA O n) x * a) i = algebraMap O LL x * ev W c ζ Eπ h' a i := by
  unfold ev
  split_ifs
  · rw [map_mul (W.lev c ζ), AlgHom.commutes, mul_assoc, ← Algebra.smul_def, PowerSeries.coeff_smul,
      Algebra.smul_def]
  · rw [mul_zero]

theorem ev_letE (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' ((letE c : LetA O n) * a) i = ev W c ζ Eπ h' a i := by
  unfold ev
  rw [map_mul (W.lev c ζ), Formalism.MainNotions.N.Ln34.ModelFPf.lev_letE (W := W) c ζ, one_mul]

private theorem coeff_lev_pow_eq_zero_of_lt (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (j : ℕ) (hj : j < h') :
    coeff j (W.lev c ζ (Eπ ^ h')) = 0 := by
  rw [levΛ_eq h0, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

private theorem coeff_lev_eq_sum_coeff_lev_pow_mul_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (a : LetA O n) (i : ℕ) :
    coeff i (W.lev c ζ a) = ∑ j ∈ Finset.range (i + h' + 1),
      coeff j (W.lev c ζ (Eπ ^ h')) * ev W c ζ Eπ h' a ((i : ℤ) - j) := by
  have e1 : coeff i (W.lev c ζ a) =
      coeff (i + h') (W.lev c ζ (Eπ ^ h') * (W.lev c ζ a * Ui W c ζ Eπ h')) := by
    have e : W.lev c ζ (Eπ ^ h') * (W.lev c ζ a * Ui W c ζ Eπ h') = W.lev c ζ a * X ^ h' := by
      rw [← levΛ_Ui h0 h1]
      ring
    rw [e, PowerSeries.coeff_mul_X_pow]
  rw [e1, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [ev_eq a (by omega), show ((i : ℤ) - j + h').toNat = i + h' - j by omega]

theorem serMul_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    {V : Type} [AddCommGroup V] [Module LL V] (a : LetA O n) (d : V) (i : ℤ) :
    serMul (W.lev c ζ (Eπ ^ h')) (fun k => ev W c ζ Eπ h' a k • d) i = serC (W.lev c ζ a) d i := by
  unfold serMul serC
  split_ifs with hi
  · obtain ⟨i', rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (i' + h' + 1)) ?_]
    · simp only [smul_smul, ← Finset.sum_smul]
      rw [Int.toNat_natCast, coeff_lev_eq_sum_coeff_lev_pow_mul_ev h0 h1 a i']
    · intro j hj
      rw [Function.mem_support] at hj
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hj
      simp only
      rw [ev_of_lt a (by omega), zero_smul, smul_zero]
  · have hz : (fun j : ℕ => coeff j (W.lev c ζ (Eπ ^ h')) •
        (fun k => ev W c ζ Eπ h' a k • d) (i - j)) = fun _ => 0 := by
      funext j
      by_cases hj : j < h'
      · rw [coeff_lev_pow_eq_zero_of_lt h0 j hj, zero_smul]
      · simp only
        rw [ev_of_lt a (by omega), zero_smul, smul_zero]
    rw [hz, finsum_zero]

theorem lev_zero_of_ev (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) (a : LetA O n) (t₀ : ℤ)
    (h : ∀ t < t₀, ev W c ζ Eπ h' a t = 0) (i : ℕ) (hi : (i : ℤ) < t₀ + h') :
    coeff i (W.lev c ζ a) = 0 := by
  have e : W.lev c ζ a = (W.lev c ζ a * Ui W c ζ Eπ h') * Vs W c ζ Eπ ^ h' := by
    rw [mul_assoc, mul_comm (Ui W c ζ Eπ h'), Vs_Ui h1, mul_one]
  rw [e, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hev := h ((p.1 : ℤ) - h') (by omega)
  rw [ev_eq a (by omega), show ((p.1 : ℤ) - h' + h').toNat = p.1 by omega] at hev
  rw [hev, zero_mul]

theorem lev_const_of_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (a : LetA O n) (t₁ : ℤ) (h : ∀ t < t₁, t ≠ 0 → ev W c ζ Eπ h' a t = 0) (i : ℕ)
    (hi : (i : ℤ) < t₁ + h') :
    coeff i (W.lev c ζ a) = ev W c ζ Eπ h' a 0 * coeff i (W.lev c ζ (Eπ ^ h')) := by
  rw [coeff_lev_eq_sum_coeff_lev_pow_mul_ev h0 h1 a i, Finset.sum_eq_single i]
  · rw [sub_self, mul_comm]
  · intro j _ hji
    by_cases hjh : j < h'
    · rw [coeff_lev_pow_eq_zero_of_lt h0 j hjh, zero_mul]
    · rw [h ((i : ℤ) - j) (by omega) (by omega), mul_zero]
  · intro hi'
    exact absurd (Finset.mem_range.mpr (by omega)) hi'

end Ev

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

private theorem gammaA_letE_eq_letE (g : W.Gam) (c : ZMod n) : W.γA g (letE c) = (letE c : LetA O n) := by
  funext i
  change (W.γ₀ g) ((letE c : LetA O n) i) = (letE c : LetA O n) i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, h]

theorem gradNPf_γD_smul (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have h := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at h
  first
  | exact h
  | simpa [Formalism.BasicNotions.LocWach.γA] using h

theorem gradNPf_tf (a : LetA O n) (ha : IsUnit (algebraMap (LetA O n) W.EE a)) (x : W.DD T)
    (hx : a • x = 0) : x = 0 := by
  obtain ⟨u, hu⟩ := ha
  have h1 : (algebraMap (LetA O n) W.EE a) • x = 0 := by rw [algebraMap_smul]; exact hx
  calc x = (↑(u⁻¹) : W.EE) • ((↑u : W.EE) • x) := by rw [smul_smul, Units.inv_mul, one_smul]
    _ = 0 := by rw [hu, h1, smul_zero]

private theorem mem_DelS_iff_forall_gammaD_fixed {x : W.DD T} : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  first
  | exact mem_DelS W T x
  | simp only [DelS, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]

theorem gradNPf_DelS_γ (g : W.Gam) {x : W.DD T} (hx : x ∈ DelS W T) : W.γD T g x ∈ DelS W T := by
  have hx' := (mem_DelS_iff_forall_gammaD_fixed W T).mp hx
  refine (mem_DelS_iff_forall_gammaD_fixed W T).mpr fun δ hδ => ?_
  rw [← W.γD_mul, mul_comm, W.γD_mul, hx' δ hδ]

private theorem mem_letS_iff_letE_smul_eq (c : ZMod n) {x : W.DD T} :
    x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  first
  | exact mem_letS W T c x
  | simp only [letS, LinearMap.mem_ker, LinearMap.restrictScalars_apply, LinearMap.coe_restrictScalars,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem gradNPf_letS_γ (g : W.Gam) (c : ZMod n) {x : W.DD T} (hx : x ∈ letS W T c) :
    W.γD T g x ∈ letS W T c := by
  have hx' := (mem_letS_iff_letE_smul_eq W T c).mp hx
  refine (mem_letS_iff_letE_smul_eq W T c).mpr ?_
  rw [← gammaA_letE_eq_letE W g c, ← gradNPf_γD_smul W T g (letE c) x, hx']

theorem gradNPf_PiNS_DelS (π' : LetA O n) (k : ℕ) {x : W.DD T} (hx : x ∈ PiNS W T π' k) :
    x ∈ DelS W T := by
  first
  | exact (Submodule.mem_inf.mp hx).2
  | (simp only [PiNS, Submodule.mem_inf] at hx; exact hx.2)

theorem gradNPf_PiNS_anti (π' : LetA O n) {j k : ℕ} (h : j ≤ k) {x : W.DD T}
    (hx : x ∈ PiNS W T π' k) : x ∈ PiNS W T π' j := by
  simp only [PiNS, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_inf, Submodule.restrictScalars_mem,
    Submodule.mem_map] at hx ⊢
  obtain ⟨⟨y, hy, rfl⟩, h2⟩ := hx
  refine ⟨⟨π' ^ (k - j) • y, Submodule.smul_mem _ _ hy, ?_⟩, h2⟩
  change π' ^ j • (π' ^ (k - j) • y) = π' ^ k • y
  rw [smul_smul, ← pow_add, Nat.add_sub_of_le h]

theorem exists_gam_pow_smul_sub_eq (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (y : ℕ) (r₀ : W.DD T) (hr₀ : r₀ ∈ W.NΔ T) :
    ∃ w ∈ W.N T, W.γD T W.gam (π' ^ y • r₀) - π' ^ y • r₀ - (c₀ ^ y - 1) • (π' ^ y • r₀) =
      π' ^ (y + 1) • w := by
  have hr₀N : r₀ ∈ W.N T := hr₀.1
  obtain ⟨d, hdN, hd⟩ := hγN r₀ hr₀
  have hd' : W.γD T W.gam r₀ = r₀ + π' • d := sub_eq_iff_eq_add'.mp hd
  obtain ⟨e, he⟩ := sub_dvd_pow_sub_pow f (algebraMap O (LetA O n) c₀) y
  rw [ht] at he
  have hs : f ^ y = algebraMap O (LetA O n) c₀ ^ y + π' * (t * e) := by linear_combination he
  refine ⟨(t * e) • r₀ + f ^ y • d, Submodule.add_mem _ (Submodule.smul_mem _ _ hr₀N)
    (Submodule.smul_mem _ _ hdN), ?_⟩
  rw [gradNPf_γD_smul, map_pow, hf, mul_pow, hd', ← algebraMap_smul (LetA O n) (c₀ ^ y - 1)]
  simp only [map_sub, map_pow, map_one]
  simp only [smul_add, smul_smul]
  have c2 : π' ^ y * f ^ y * π' = π' ^ (y + 1) * f ^ y := by ring
  have c1 : π' ^ (y + 1) * (t * e) =
      π' ^ y * f ^ y - π' ^ y - (algebraMap O (LetA O n) c₀ ^ y - 1) * π' ^ y := by
    rw [hs]; ring
  rw [c2, c1, sub_smul, sub_smul]
  abel

theorem gradNPf_coker (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (c : ZMod n) (z : W.DD T) (hz : z ∈ PiNS W T π' 1 ⊓ letS W T c) (k : ℕ) (hk : 1 ≤ k) :
    ∃ x ∈ PiNS W T π' 1 ⊓ letS W T c,
      (∏ y ∈ Finset.Ico 1 k, (c₀ ^ y - 1)) • z - (W.γD T W.gam x - x) ∈
        PiNS W T π' k ⊓ letS W T c := by
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    simp only [Finset.Ico_self, Finset.prod_empty, one_smul, map_zero, sub_zero]
    exact hz
  | succ k hk ih =>
    obtain ⟨xk, hxk, hr⟩ := ih
    set R := (∏ y ∈ Finset.Ico 1 k, (c₀ ^ y - 1)) • z - (W.γD T W.gam xk - xk) with hR
    have hrP := (Submodule.mem_inf.mp hr).1
    have hrL := (Submodule.mem_inf.mp hr).2
    have hrP' := hrP
    simp only [PiNS, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_inf, Submodule.restrictScalars_mem,
      Submodule.mem_map] at hrP'
    obtain ⟨⟨r', hr'N, hr'eq⟩, hrΔ⟩ := hrP'
    have hr'eq' : π' ^ k • r' = R := hr'eq
    have hΔr := (mem_DelS_iff_forall_gammaD_fixed W T).mp hrΔ
    have hr'Δ : r' ∈ W.NΔ T := by
      show r' ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ r' = r'
      refine ⟨hr'N, fun δ hδ => ?_⟩
      have h2 : W.γA δ (π' ^ k) = π' ^ k := by rw [map_pow, hπΔ δ hδ]
      have h1 : π' ^ k • (W.γD T δ r' - r') = 0 := by
        rw [smul_sub, ← h2, ← gradNPf_γD_smul, h2, hr'eq', hΔr δ hδ, sub_self]
      have hu' : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by
        rw [map_pow]; exact hu.pow k
      exact sub_eq_zero.mp (gradNPf_tf W T (π' ^ k) hu' _ h1)
    obtain ⟨w, hwN, hw⟩ := exists_gam_pow_smul_sub_eq W T π' f t c₀ hf ht hγN k r' hr'Δ
    rw [hr'eq'] at hw
    have hxkP := (Submodule.mem_inf.mp hxk).1
    have hxkL := (Submodule.mem_inf.mp hxk).2
    have hzP := (Submodule.mem_inf.mp hz).1
    have hzL := (Submodule.mem_inf.mp hz).2
    have hRP1 : R ∈ PiNS W T π' 1 := gradNPf_PiNS_anti W T π' hk hrP
    have hxP : (c₀ ^ k - 1) • xk + R ∈ PiNS W T π' 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hxkP) hRP1
    have hxL : (c₀ ^ k - 1) • xk + R ∈ letS W T c :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hxkL) hrL
    refine ⟨(c₀ ^ k - 1) • xk + R, Submodule.mem_inf.mpr ⟨hxP, hxL⟩, ?_⟩
    have hPz : (∏ y ∈ Finset.Ico 1 k, (c₀ ^ y - 1)) • z = R + (W.γD T W.gam xk - xk) := by
      rw [hR]; abel
    have hE : (∏ y ∈ Finset.Ico 1 (k + 1), (c₀ ^ y - 1)) • z -
        (W.γD T W.gam ((c₀ ^ k - 1) • xk + R) - ((c₀ ^ k - 1) • xk + R)) = π' ^ (k + 1) • (-w) := by
      rw [Finset.prod_Ico_succ_top hk, mul_comm, mul_smul, hPz, map_add (f := _), map_smul, smul_neg, ← hw]
      simp only [smul_add, smul_sub]
      abel
    have hγxP : W.γD T W.gam ((c₀ ^ k - 1) • xk + R) ∈ DelS W T :=
      gradNPf_DelS_γ W T W.gam (gradNPf_PiNS_DelS W T π' 1 hxP)
    have hγxL := gradNPf_letS_γ W T W.gam c hxL
    have hzΔ := gradNPf_PiNS_DelS W T π' 1 hzP
    have hxΔ := gradNPf_PiNS_DelS W T π' 1 hxP
    rw [PiNS]
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hE]
      exact (Submodule.restrictScalars_mem _ _ _).mpr
        (Submodule.mem_map.mpr ⟨-w, Submodule.neg_mem _ hwN, rfl⟩)
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hzΔ) (Submodule.sub_mem _ hγxP hxΔ)
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hzL) (Submodule.sub_mem _ hγxL hxL)

theorem gradNPf_local (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (hK : W.gamK = W.gam) (σ M : ℕ) (hM : 1 ≤ M) (a : O)
    (ha : ((PD.p : ℕ) : O) ^ σ = a * ∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) :
    GradN W T π' σ M := by
  intro c z hz
  obtain ⟨x, hx, hr⟩ := gradNPf_coker W T π' f t c₀ hf ht hu hπΔ hγN c z hz M hM
  refine ⟨a • x, Submodule.smul_mem _ _ hx, ?_⟩
  have e : ((PD.p : ℕ) : O) ^ σ • z - (W.γD T W.gamK (a • x) - a • x) =
      a • ((∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) • z - (W.γD T W.gam x - x)) := by
    rw [hK, ha, map_smul, mul_smul, smul_sub, smul_sub]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.mem_inf.1 hr).1

theorem gradNPf_small (π' : LetA O n) (σ M : ℕ) (hM : M ≤ 1) : GradN W T π' σ M := by
  unfold GradN
  intro c z hz
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  simp only [map_zero, sub_zero]
  exact gradNPf_PiNS_anti W T π' hM (Submodule.smul_mem _ _ (Submodule.mem_inf.mp hz).1)

end Local

end Formalism.MainNotions.N.Ln34

end
end
