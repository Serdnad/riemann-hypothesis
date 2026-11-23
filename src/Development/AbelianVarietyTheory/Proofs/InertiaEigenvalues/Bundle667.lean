module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle638
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Mathlib.RingTheory.FiniteLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle636
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle641
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterDefiniteUnitaryInertPlace
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
import Mathlib.NumberTheory.Padics.LocalField
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CokerFinLen

theorem divApprox : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧), g ∈ A O K → ∀ n₀ : ℕ, ‖coeff n₀ g‖ = 1 → (∀ i < n₀, ‖coeff i g‖ < 1) → ∀ δ : ℝ, 0 < δ → ∀ f ∈ A O K, ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := GlobalTheory.T.exists_integral_powerSeries_division_approx

theorem exists_net {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : Finset K, (∀ t ∈ T, ‖t‖ ≤ 1) ∧ ∀ x : K, ‖x‖ ≤ 1 → ∃ t ∈ T, ‖x - t‖ < δ := by
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[l] K
  obtain ⟨t, hts, ht, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : K) 1) hδ
  refine ⟨ht.toFinset, fun y hy => by simpa using hts (ht.mem_toFinset.1 hy), fun x hx => ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : K) 1 := by simpa using hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx')
  exact ⟨y, ht.mem_toFinset.2 hy, by simpa [dist_eq_norm] using hxy⟩

theorem exists_finset_reps {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (g : K⟦X⟧) (hg : g ∈ A O K) (hprim : ∃ n, ‖coeff n g‖ = 1) (c : K) (hc : c ≠ 0) :
    ∃ R : Finset K⟦X⟧, ∀ f ∈ A O K, ∃ r ∈ R, r ∈ A O K ∧ ∃ q ∈ A O K, ∃ h ∈ A O K,
      f = r + q * g + C c * h := by
  classical
  have hδ : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨T, hT1, hT⟩ := exists_net (K := K) l hδ
  let n₀ := Nat.find hprim
  have hn₀ : ‖coeff n₀ g‖ = 1 := Nat.find_spec hprim
  have hlow : ∀ i < n₀, ‖coeff i g‖ < 1 := fun i hi =>
    lt_of_le_of_ne ((mem_A.1 hg) i) (Nat.find_min hprim hi)
  let mkR : (Fin n₀ → T) → K⟦X⟧ := fun t => PowerSeries.mk fun n =>
    if h : n < n₀ then ((t ⟨n, h⟩ : T) : K) else 0
  refine ⟨Finset.univ.image mkR, fun f hf => ?_⟩
  obtain ⟨q, hq, r, hr0, hr1, hrem⟩ := divApprox O K g hg n₀ hn₀ hlow _ hδ f hf
  choose t ht hrt using fun i : Fin n₀ => hT (coeff i r) (hr1 i)
  let r' := mkR fun i => ⟨t i, ht i⟩
  have hcoeff : ∀ n, coeff n r' = if h : n < n₀ then t ⟨n, h⟩ else 0 := fun n => by
    simp [r', mkR, coeff_mk]
  have hr'A : r' ∈ A O K := mem_A.2 fun n => by
    rw [hcoeff]; split_ifs
    · exact hT1 _ (ht _)
    · simp
  set d := f - q * g - r' with hd
  have hdn : ∀ n, ‖coeff n d‖ ≤ ‖c‖ := fun n => by
    have : d = (f - q * g - r) + (r - r') := by rw [hd]; ring
    rw [this, map_add (f := _)]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hrem n) ?_)
    rw [map_sub, hcoeff]
    split_ifs with h
    · exact (hrt ⟨n, h⟩).le
    · rw [hr0 n (not_lt.1 h), sub_zero, norm_zero]; exact hδ.le
  refine ⟨r', Finset.mem_image_of_mem mkR (Finset.mem_univ (fun i => (⟨t i, ht i⟩ : T))), hr'A, q, hq, C c⁻¹ * d,
    mem_A.2 fun n => ?_, ?_⟩
  · rw [coeff_C_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hdn n) (norm_nonneg _)
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul, hd]; ring

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), (∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → (∀ τ, (1 : K⟦X⟧) ∈ F.rdivSet τ) → IsFiniteLength (A O K) F.coker := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F hY h1
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
  have hc : ∀ τ, ∃ c : K, c ≠ 0 ∧ ∃ Y : Matrix ι κ K⟦X⟧, (∀ i j, Y i j ∈ A O K) ∧
      F.mat τ * Y = C c • (1 : Matrix κ κ K⟦X⟧) := by
    intro τ
    obtain ⟨-, Y, ⟨B, hB⟩, hFY⟩ := h1 τ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖(l : K)‖ ^ m * B < 1 := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
        (norm_l_lt_one (K := K) l)).mul_const B
      rw [zero_mul] at h
      exact (h.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨(l : K) ^ m, pow_ne_zero _ (l_ne_zero l), C ((l : K) ^ m) • Y,
      fun i j => mem_A.2 fun n => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul, coeff_C_mul, norm_mul, norm_pow]
      calc _ ≤ ‖(l : K)‖ ^ m * B := mul_le_mul_of_nonneg_left (hB i j n) (by positivity)
        _ ≤ 1 := hm.le
    · rw [Matrix.mul_smul, hFY, one_smul]
  choose c hc0 Y₁ hY₁A hY₁ using hc
  choose Yg g hYgA hgprim hYg using hY
  have hgA : ∀ τ (j : κ), g τ ∈ A O K := fun τ j => by
    have h := congrFun (congrFun (hYg τ) j) j
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.mul_apply] at h
    rw [← h]
    exact Subalgebra.sum_mem _ fun k _ => mul_mem (F.mem τ j k) (hYgA τ k j)
  have hR : ∀ τ (j : κ), ∃ R : Finset K⟦X⟧, ∀ f ∈ A O K, ∃ r ∈ R, r ∈ A O K ∧ ∃ q ∈ A O K,
      ∃ h ∈ A O K, f = r + q * g τ + C (c τ) * h := fun τ j =>
    exists_finset_reps l (g τ) (hgA τ j) (hgprim τ) (c τ) (hc0 τ)
  choose R hR using hR
  let Sset : Set Q.M := {v | ∀ τ j, (v : Vec K a κ) τ j ∈ R τ j}
  have hS : Sset.Finite := by
    have hfin : (Set.pi Set.univ fun τ => Set.pi Set.univ fun j => ((R τ j : Set K⟦X⟧))).Finite :=
      Set.Finite.pi fun τ => Set.Finite.pi fun j => (R τ j).finite_toSet
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro v hv
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Finset.mem_coe]
    exact hv
  have hsurj : ∀ x : F.coker, x ∈ (Submodule.Quotient.mk '' Sset : Set F.coker) := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hv : ∀ τ j, (v : Vec K a κ) τ j ∈ A O K := fun τ j => mem_tot.1 v.2 τ j
    choose r hrR hrA q hqA h hhA hdec using fun τ j => hR τ j _ (hv τ j)
    refine ⟨⟨fun τ j => r τ j, mem_tot.2 fun τ j => hrA τ j⟩, hrR, ?_⟩
    rw [Submodule.Quotient.eq]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    unfold Hom.imM
    rw [Submodule.mem_map]
    refine ⟨fun τ => -(Yg τ *ᵥ q τ + Y₁ τ *ᵥ h τ), mem_tot.2 fun τ i => ?_, ?_⟩
    · have hmv : ∀ (Y : Matrix ι κ K⟦X⟧) (w : κ → K⟦X⟧), (∀ i j, Y i j ∈ A O K) →
          (∀ j, w j ∈ A O K) → ∀ i, (Y *ᵥ w) i ∈ A O K := fun Y w hY hw i =>
        Subalgebra.sum_mem _ fun j _ => mul_mem (hY i j) (hw j)
      exact neg_mem (add_mem (hmv _ _ (hYgA τ) (hqA τ) i) (hmv _ _ (hY₁A τ) (hhA τ) i))
    · ext τ j
      simp only [LinearMap.restrictScalars_apply, Hom.app_apply, Matrix.mulVec_neg,
        Matrix.mulVec_add, Matrix.mulVec_mulVec, hYg, hY₁, Matrix.smul_mulVec,
        Matrix.one_mulVec, Submodule.coe_sub, Pi.sub_apply, Pi.neg_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hdec τ j]
      ring_nf
  haveI : Finite F.coker :=
    Set.finite_univ_iff.1 ((hS.image _).subset fun x _ => hsurj x)
  exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨isNoetherian_of_finite _ _, isArtinian_of_finite⟩

end GlobalTheory.CokerFinLen
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.RdivSlice

theorem frobSlice_frob_mul {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime] {i : ℕ} (hi : i < l)
    (f z : K⟦X⟧) : frobSlice l i (frob K l f * z) = f * frobSlice l i z := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_frobSlice, coeff_mul, coeff_mul]
  symm
  refine Finset.sum_of_injOn (fun p : ℕ × ℕ => (l * p.1, l * p.2 + i)) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ - ⟨p', q'⟩ - h
    simp only [Prod.mk.injEq, add_left_inj] at h ⊢
    exact ⟨Nat.eq_of_mul_eq_mul_left hl h.1, Nat.eq_of_mul_eq_mul_left hl h.2⟩
  · rintro ⟨p, q⟩ h
    simp only [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
    rw [← h]; ring
  · rintro ⟨p, q⟩ h hn
    rw [coeff_frob]
    split_ifs with hd
    · exfalso
      obtain ⟨t, rfl⟩ := hd
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at h
      have ht : t ≤ n := by
        by_contra hc
        have : l * (n + 1) ≤ l * t := Nat.mul_le_mul_left l (by omega)
        rw [mul_add, mul_one] at this
        omega
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
      refine hn ⟨(t, s), by simp, ?_⟩
      rw [mul_add] at h
      simp only [Prod.mk.injEq, true_and]
      omega
    · simp
  · rintro ⟨p, q⟩ -
    simp only [coeff_frob, coeff_frobSlice, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hl]

theorem frobSlice_sum {K : Type} [Field K] (l i : ℕ) {μ : Type} (s : Finset μ) (f : μ → K⟦X⟧) :
    frobSlice l i (∑ j ∈ s, f j) = ∑ j ∈ s, frobSlice l i (f j) := by
  ext n

  simp only [coeff_frobSlice, map_sum]

theorem bdd_matrix_mul {K : Type} [NormedField K] [IsUltrametricDist K] {μ ν ρ : Type} [Fintype ν]
    {Y : Matrix μ ν K⟦X⟧} {Z : Matrix ν ρ K⟦X⟧} (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c)
    (hZ : ∃ c : ℝ, ∀ i j n, ‖coeff n (Z i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y * Z) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hY
  obtain ⟨b, hb⟩ := hZ
  refine ⟨max a 0 * max b 0, fun i j n => ?_⟩

  rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    (le_max_right a 0) (le_max_right b 0) (f := Y i k) (g := Z k j)
    (fun m => by rw [mul_one]; exact (ha i k m).trans (le_max_left _ _))
    (fun m => by rw [mul_one]; exact (hb k j m).trans (le_max_left _ _)) n

theorem exists_pow_smul_bdd {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} [NeZero a] {μ : Type} [Fintype μ]
    (Y : ZMod a → Matrix μ μ K⟦X⟧) (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K)) :
    ∃ N : ℕ, ∀ τ i j n, ‖coeff n ((E K l e ^ N • Y τ) i j)‖ ≤ 1 := by
  choose n hn using fun p : ZMod a × μ × μ => hY p.1 p.2.1 p.2.2
  refine ⟨Finset.univ.sup n, fun τ i j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
  rw [Matrix.smul_apply, smul_eq_mul, hc, pow_add, mul_assoc]
  exact mem_A.1 (mul_mem (pow_mem (E_mem l e (A O K)) c) (hn (τ, i, j)))

theorem exists_frobSlice_mem_rdivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.rdivSet (τ - 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  obtain ⟨α, hα⟩ := exists_pow_smul_bdd P.mxInv P.mxInv_mem
  obtain ⟨β, hβ⟩ := exists_pow_smul_bdd Q.mx Q.mx_mem
  refine ⟨α + β, fun τ h hh i hi => ?_⟩
  obtain ⟨hb, Y, hY, hFY⟩ := hh
  obtain ⟨c, hc⟩ := GlobalTheory.BK.Hom.bdd_mul (f := E K l e ^ (α + β))
    ⟨1, mem_A.1 (pow_mem (E_mem l e (A O K)) _)⟩ hb
  obtain ⟨d, hd⟩ := bdd_matrix_mul (bdd_matrix_mul ⟨1, hα τ⟩ hY) ⟨1, hβ τ⟩
  have h1 : (F.mat (τ - 1)).map (frob K l) * P.mxInv τ = Q.mxInv τ * F.mat τ := by
    calc _ = Q.mxInv τ * (Q.mx τ * (F.mat (τ - 1)).map (frob K l)) * P.mxInv τ := by
          rw [← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]
      _ = _ := by
          rw [← F.comm, Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one]
  have h2 : (F.mat (τ - 1)).map (frob K l) *
      ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)) =
      (E K l e ^ (α + β) * h) • (1 : Matrix κ κ K⟦X⟧) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc (Q.mxInv τ), hFY,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Q.mxInv_mul_mx, smul_smul, smul_smul,
      pow_add]
  refine ⟨⟨c, fun n => by rw [coeff_frobSlice]; exact hc _⟩,
    ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)).map (frobSlice l i),
    ⟨d, fun s t n => by rw [Matrix.map_apply, coeff_frobSlice]; exact hd _ _ _⟩, ?_⟩
  ext1 s t
  have h3 := congrArg (fun M : Matrix κ κ K⟦X⟧ => frobSlice l i (M s t)) h2
  simp only [Matrix.mul_apply (M := (F.mat (τ - 1)).map (frob K l)), frobSlice_sum,
    Matrix.map_apply, frobSlice_frob_mul l hi] at h3
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [h3, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · simp
  · ext n
    simp [coeff_frobSlice]

end GlobalTheory.BK.RdivSlice
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.Hom

section Bounds

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_sum_le {s : Type} (t : Finset s) (f : s → K⟦X⟧) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ k n, ‖coeff n (f k)‖ ≤ C) (n : ℕ) : ‖coeff n (∑ k ∈ t, f k)‖ ≤ C := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hC
  | insert k t hk ih =>
    rw [Finset.sum_insert hk, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf k n) ih)

theorem bdd_matMul {μ ν ρ : Type} [Fintype ν] {Y : Matrix μ ν K⟦X⟧} {Z : Matrix ν ρ K⟦X⟧}
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) (hZ : ∃ c : ℝ, ∀ i j n, ‖coeff n (Z i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y * Z) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hY
  obtain ⟨b, hb⟩ := hZ
  refine ⟨max a 0 * max b 0, fun i j n => ?_⟩
  rw [Matrix.mul_apply]
  refine norm_coeff_sum_le _ (fun k => Y i k * Z k j)
    (mul_nonneg (le_max_right _ _) (le_max_right _ _)) (fun k m => ?_) n
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    (le_max_right a 0) (le_max_right b 0) (f := Y i k) (g := Z k j)
    (fun p => by rw [mul_one]; exact (ha i k p).trans (le_max_left _ _))
    (fun p => by rw [mul_one]; exact (hb k j p).trans (le_max_left _ _)) m

theorem bdd_frob (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (frob K l f)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, fun n => ?_⟩
  rw [coeff_frob]
  split_ifs
  · exact hc _
  · simpa using (norm_nonneg _).trans (hc 0)

theorem bdd_map_frob (l : ℕ) [Fact l.Prime] {μ ν : Type} {Y : Matrix μ ν K⟦X⟧}
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y.map (frob K l)) i j)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hY
  refine ⟨max c 0, fun i j n => ?_⟩
  rw [Matrix.map_apply, coeff_frob]
  split_ifs
  · exact (hc _ _ _).trans (le_max_left _ _)
  · simp

end Bounds

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem exists_pow_E_mul_mem (l e : ℕ) {s : Type} [Finite s] (f : s → K⟦X⟧)
    (hf : ∀ x, f x ∈ invE l e (A O K)) : ∃ N : ℕ, ∀ x, E K l e ^ N * f x ∈ A O K := by
  classical
  cases nonempty_fintype s
  choose n hn using fun x => mem_away.1 (hf x)
  refine ⟨Finset.univ.sup n, fun x => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ x))
  rw [hc, pow_add, mul_assoc]
  exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn x)

theorem bdd_of_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c := ⟨1, hf⟩

theorem map_frob_smul_one (l : ℕ) [Fact l.Prime] {μ : Type} [DecidableEq μ] (h : K⟦X⟧) :
    (h • (1 : Matrix μ μ K⟦X⟧)).map (frob K l) = frob K l h • (1 : Matrix μ μ K⟦X⟧) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

section Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

theorem mxInv_mul_mat (F : Hom P Q) (τ : ZMod a) :
    Q.mxInv τ * F.mat τ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
  calc Q.mxInv τ * F.mat τ = Q.mxInv τ * (F.mat τ * P.mx τ) * P.mxInv τ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one]
    _ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
        rw [F.comm, ← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]

theorem frob_ldiv_eq (F : Hom P Q) (τ : ZMod a) {h : K⟦X⟧} {Y : Matrix ι κ K⟦X⟧}
    (hY : Y * F.mat (τ - 1) = h • (1 : Matrix ι ι K⟦X⟧)) :
    P.mx τ * Y.map (frob K l) * Q.mxInv τ * F.mat τ = frob K l h • (1 : Matrix ι ι K⟦X⟧) := by
  have hφ : Y.map (frob K l) * (F.mat (τ - 1)).map (frob K l) = frob K l h • (1 : Matrix ι ι K⟦X⟧) := by
    rw [← map_frob_smul_one l h, ← hY]
    exact (Matrix.map_mul (f := ((frob K l : K⟦X⟧ →ₐ[K] K⟦X⟧) : K⟦X⟧ →+* K⟦X⟧))).symm
  rw [Matrix.mul_assoc, mxInv_mul_mat, ← Matrix.mul_assoc,
    Matrix.mul_assoc (P.mx τ) (Y.map (frob K l)), hφ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, P.mx_mul_mxInv]

end Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem exists_pow_E_mul_frob_mem_ldivSet (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NeZero a] (κ : Type) [Fintype κ] [DecidableEq κ]
    (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : Hom P Q) :
    ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.ldivSet τ := by
  obtain ⟨N₁, hN₁⟩ := exists_pow_E_mul_mem (O := O) l e (fun p : ZMod a × ι × ι => P.mx p.1 p.2.1 p.2.2)
    fun p => P.mx_mem _ _ _
  obtain ⟨N₂, hN₂⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × κ × κ => Q.mxInv p.1 p.2.1 p.2.2) fun p => Q.mxInv_mem _ _ _
  refine ⟨N₁ + N₂, fun τ h ⟨hb, Y, hY, hYF⟩ => ⟨?_, ?_⟩⟩
  · exact bdd_mul (bdd_of_mem_A (pow_mem (E_mem l e (A O K)) _)) (bdd_frob l hb)
  · refine ⟨(E K l e ^ N₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ N₂ • Q.mxInv τ),
      bdd_matMul (bdd_matMul ⟨1, fun i j n => ?_⟩ (bdd_map_frob l hY)) ⟨1, fun i j n => ?_⟩, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]; exact hN₁ (τ, i, j) n
    · rw [Matrix.smul_apply, smul_eq_mul]; exact hN₂ (τ, i, j) n
    · simp only [Matrix.smul_mul, Matrix.mul_smul]
      rw [frob_ldiv_eq F τ hYF, smul_smul, smul_smul, pow_add]
      congr 1
      ring

end GlobalTheory.BK.Hom

theorem GlobalTheory.BK.Hom.frob_mem_ldivSet_target : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.ldivSet τ := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  exact GlobalTheory.BK.Hom.exists_pow_E_mul_frob_mem_ldivSet l e a ι κ P Q F
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.JumpDR

section General

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K] [NeZero a]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_Ehat_pow_mul (w : ZMod a → ι → AhatE O K l e) :
    ∃ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), ∀ τ i,
      algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * w τ i := by
  classical
  choose r z hz using fun p : ZMod a × ι => IsLocalization.Away.surj (Ehat O K l e) (w p.1 p.2)
  refine ⟨Finset.univ.sup r, fun τ i => Ehat O K l e ^ (Finset.univ.sup r - r (τ, i)) * z (τ, i),
    fun τ i => ?_⟩
  have hle : r (τ, i) ≤ Finset.univ.sup r := Finset.le_sup (Finset.mem_univ _)
  rw [map_mul, map_pow, ← hz (τ, i), mul_left_comm, ← pow_add, Nat.sub_add_cancel hle, mul_comm]

end General

theorem hsum_mul_Ehat_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl), ∃ (N : ℕ) (x : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (x τ i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P n s m
  exact exists_Ehat_pow_mul (GlobalTheory.BKGal.JumpDR.hsum P s fun k => (m k).1)

end GlobalTheory.BKGal.JumpDR
end

section

open NumberField Matrix GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.isStandardAdelicAddChar_global_adelicChar : ∀ (E : Type) [Field E] [NumberField E], GlobalTheory.CuspGeneric.StdPsi (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) := by
  first | exact @GlobalTheory.StdCharStd.stdPsi_adelicChar | exact GlobalTheory.StdCharStd.stdPsi_adelicChar | (intros; apply GlobalTheory.StdCharStd.stdPsi_adelicChar <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.Published

theorem _root_.GlobalTheory.T.discreteAutomorphicRepGL_exists_localComponent : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ w : HeightOneSpectrum (𝓞 E), ∃ σ' , IsLocCompGL V w σ' := by
  first | exact @GlobalTheory.DiscLocEx.exists_isLocCompGL | exact GlobalTheory.DiscLocEx.exists_isLocCompGL | (intros; apply GlobalTheory.DiscLocEx.exists_isLocCompGL <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.exists_satakeParameter_definiteUnitary_inertPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → Formalism.UG.IsUnramInv ϖ s q → (∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C → FiniteDimensional ℂ (Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C})) → (∃ ι : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) →* UA E n, Continuous ι ∧ (∀ g, ι g ∈ locU n w ∧ cLoc w (ι g) = g.1) ∧ (∀ x ∈ locU n w, cLoc w x = 1 → x = 1) ∧ ∀ x g, cLoc w x = 1 → x * ι g = ι g * x) → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → IsUnramU π w → ∃ α, HasSatAt π w s ϖ q α := by
  first | exact @GlobalTheory.UnitaryBC.SatEx.exists_hasSatAt | exact GlobalTheory.UnitaryBC.SatEx.exists_hasSatAt | (intros; apply GlobalTheory.UnitaryBC.SatEx.exists_hasSatAt <;> assumption)
end
