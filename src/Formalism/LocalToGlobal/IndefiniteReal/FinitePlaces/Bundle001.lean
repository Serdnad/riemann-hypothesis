module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SmulSubMulLe
public import Mathlib.Algebra.Module.LinearMap.End
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.IndefR.Fin.Four

variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]

def IsSB (L X : AddSubgroup W) (Φ : W → ℂ) : Prop :=
  (∀ t, Φ t ≠ 0 → t ∈ X) ∧ ∃ k : ℕ, 0 < k ∧ (∀ u ∈ L ⊓ X, ∀ t, Φ (t + k • u) = Φ t) ∧ ∀ t, Φ t ≠ 0 → k • t ∈ L

section Defs

variable (ρ : W → Module.End ℂ V) (χ : W → W → ℂ) (L X Y : AddSubgroup W) (f₀ : V)

def coef (Φ : W → ℂ) (a y : W) : ℂ := integ (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹)

def term (Φ : W → ℂ) (a y : W) : V := coef χ L X Φ a y • ρ (-a) (ρ y f₀)

abbrev QX : Type _ := W ⧸ (L ⊓ X)

abbrev QY : Type _ := W ⧸ (L ⊓ Y)


open Classical in
def tfun (Φ : W → ℂ) : V :=
  ∑ᶠ q : QX L X × QY L Y, if q.2.out ∈ Y then term ρ χ L X f₀ Φ q.1.out q.2.out else 0

end Defs

section Chi

variable {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)

include hχl hχ0 in
theorem chi_zero_left (y : W) : χ 0 y = 1 := by
  have h := hχl 0 0 y
  rw [add_zero] at h
  exact mul_left_cancel₀ (hχ0 0 y) (by rw [mul_one, ← h])

include hχr hχ0 in
theorem chi_zero_right (t : W) : χ t 0 = 1 := by
  have h := hχr t 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (hχ0 t 0) (by rw [mul_one, ← h])

include hχl hχ0 in
theorem chi_neg_left (t y : W) : χ (-t) y = (χ t y)⁻¹ := by
  have h : χ t y * χ (-t) y = 1 := by
    rw [← hχl, add_neg_cancel, chi_zero_left hχl hχ0]
  exact eq_inv_of_mul_eq_one_right h

include hχl hχ0 in
theorem chi_nsmul_left (k : ℕ) (t y : W) : χ (k • t) y = χ t y ^ k := by
  induction k with
  | zero => rw [zero_smul, chi_zero_left hχl hχ0, pow_zero]
  | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]

include hχr hχ0 in
theorem chi_nsmul_right (k : ℕ) (t y : W) : χ t (k • y) = χ t y ^ k := by
  induction k with
  | zero => rw [zero_smul, chi_zero_right hχr hχ0, pow_zero]
  | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]

end Chi

section Rep

variable {L X Y : AddSubgroup W}

theorem QX_out (a : W) : ∃ l ∈ L ⊓ X, (QuotientAddGroup.mk a : QX L X).out = a + l := by
  refine ⟨-a + (QuotientAddGroup.mk a : QX L X).out, ?_, (add_neg_cancel_left a _).symm⟩
  have h : (QuotientAddGroup.mk (QuotientAddGroup.mk a : QX L X).out : QX L X) = QuotientAddGroup.mk a :=
    QuotientAddGroup.out_eq' _
  exact QuotientAddGroup.eq.mp h.symm

theorem QY_out (y : W) : ∃ μ ∈ L ⊓ Y, (QuotientAddGroup.mk y : QY L Y).out = y + μ := by
  refine ⟨-y + (QuotientAddGroup.mk y : QY L Y).out, ?_, (add_neg_cancel_left y _).symm⟩
  have h : (QuotientAddGroup.mk (QuotientAddGroup.mk y : QY L Y).out : QY L Y) = QuotientAddGroup.mk y :=
    QuotientAddGroup.out_eq' _
  exact QuotientAddGroup.eq.mp h.symm

end Rep

section Coef

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y) (hχ0 : ∀ t y, χ t y ≠ 0)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X)))

include hχl hχ0 hfinX in
theorem coef_add_left (Φ : W → ℂ) (a y : W) {l : W} (hl : l ∈ L ⊓ X) :
    coef χ L X Φ (a + l) y = χ l y * coef χ L X Φ a y := by
  have hc := hχ0 l y
  have hH : ∀ t, Φ (a + l + t) * (χ t y)⁻¹ = χ l y * (Φ (a + (t + l)) * (χ (t + l) y)⁻¹) := by
    intro t
    have e : (χ t y)⁻¹ = χ l y * (χ (t + l) y)⁻¹ := by
      rw [hχl, mul_inv, mul_left_comm, mul_inv_cancel₀ hc, mul_one]
    rw [e, add_comm t l, ← add_assoc]
    ring
  have hiff : ∀ k, IsInv k (L ⊓ X) (fun t => Φ (a + l + t) * (χ t y)⁻¹) ↔
      IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹) := by
    intro k
    unfold IsInv
    simp only [hH]
    constructor
    · intro h t ht u hu
      have := h (t - l) (sub_mem ht hl) u hu
      rw [sub_add_cancel, show t - l + k • u + l = t + k • u by abel] at this
      exact mul_left_cancel₀ hc this
    · intro h t ht u hu
      rw [show t + k • u + l = (t + l) + k • u by abel, h (t + l) (add_mem ht hl) u hu]
  unfold coef
  by_cases h0 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹)
  · obtain ⟨k, hk, hinv⟩ := h0
    have hinv1 := (hiff k).mpr hinv
    have hinvs : IsInv k (L ⊓ X) (fun t => Φ (a + (t + l)) * (χ (t + l) y)⁻¹) := by
      intro t ht u hu
      beta_reduce
      rw [show t + k • u + l = (t + l) + k • u by abel]
      exact hinv (t + l) (add_mem ht hl) u hu
    rw [integ_eq hfinX hk hinv1, ← integ_shift hfinX hk hinv hl, integ_eq hfinX hk hinvs]
    unfold avg
    haveI := hfinX k hk
    simp only [hH]
    rw [← mul_finsum]
    ring
  · have h1 : ¬ ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + l + t) * (χ t y)⁻¹) :=
      fun ⟨k, hk, hi⟩ => h0 ⟨k, hk, (hiff k).mp hi⟩
    unfold integ
    rw [dite_eq_right h1, dite_eq_right h0, mul_zero]

include hfinX in
theorem coef_add_right (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y')
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (Φ : W → ℂ) (a y : W) {μ : W} (hμ : μ ∈ L ⊓ Y) :
    coef χ L X Φ a (y + μ) = coef χ L X Φ a y := by
  unfold coef
  apply integ_congr hfinX
  intro t ht
  rw [hχr, hLL t ht μ hμ, mul_one]

include hfinX in
theorem coef_eq_zero (Φ : W → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → t ∈ X) {a : W} (ha : a ∉ X) (y : W) :
    coef χ L X Φ a y = 0 := by
  have h0 : ∀ t ∈ L ⊓ X, Φ (a + t) * (χ t y)⁻¹ = (fun _ : W => (0 : ℂ)) t := by
    intro t ht
    have hz : Φ (a + t) = 0 := by
      by_contra hne
      exact ha (by simpa using X.sub_mem (hΦ _ hne) (AddSubgroup.mem_inf.mp ht).2)
    simp [hz]
  unfold coef
  rw [integ_congr hfinX h0]
  unfold integ
  split_ifs with h
  · simp [avg]
  · rfl

include hχl hχ0 hfinX in
theorem term_add_left (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x)) (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀)
    (Φ : W → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → t ∈ X) (a : W) {y : W} (hy : y ∈ Y) {l : W} (hl : l ∈ L ⊓ X) :
    term ρ χ L X f₀ Φ (a + l) y = term ρ χ L X f₀ Φ a y := by
  by_cases ha : a ∈ X
  · have hl' := AddSubgroup.mem_inf.mp hl
    have hnl : -l ∈ L ⊓ X := neg_mem hl
    have key : ρ (-l) (ρ y f₀) = (χ l y)⁻¹ • ρ y f₀ := by
      have h1 := congrArg (fun T => T f₀) (hXY (-l) (neg_mem hl'.2) y hy)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at h1
      rw [h1, hfX (-l) hnl, chi_neg_left hχl hχ0]
    unfold term
    rw [coef_add_left hχl hχ0 hfinX Φ a y hl, neg_add, hX (-a) (neg_mem ha) (-l) (neg_mem hl'.2),
      Module.End.mul_apply, key, map_smul, smul_smul, mul_comm (χ l y), mul_assoc, mul_inv_cancel₀ (hχ0 l y), mul_one]
  · have hal : a + l ∉ X := fun h => ha (by simpa using X.sub_mem h (AddSubgroup.mem_inf.mp hl).2)
    unfold term
    rw [coef_eq_zero hfinX Φ hΦ ha, coef_eq_zero hfinX Φ hΦ hal, zero_smul, zero_smul]

include hfinX in
theorem term_add_right (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y')
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
    (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀) (Φ : W → ℂ) (a : W) {y : W} (hy : y ∈ Y) {μ : W} (hμ : μ ∈ L ⊓ Y) :
    term ρ χ L X f₀ Φ a (y + μ) = term ρ χ L X f₀ Φ a y := by
  unfold term
  rw [coef_add_right hfinX hχr hLL Φ a y hμ, hY y hy μ (AddSubgroup.mem_inf.mp hμ).2, Module.End.mul_apply,
    hfY μ hμ]

end Coef

end Formalism.IndefR.Fin.Four

end
end

section

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology Filter

namespace Formalism.IndefR.Fin.U1

variable {F : Type} [Field F] [NumberField F]

theorem norm_le_one_iff_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

theorem norm_nat_le_one (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) : ‖(m : v.adicCompletion F)‖ ≤ 1 := (norm_le_one_iff_int v _).mpr (natCast_mem _ m)

theorem nat_ne_zero_fin (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (hm : m ≠ 0) : (m : v.adicCompletion F) ≠ 0 := by
  rw [← map_natCast (algebraMap F (v.adicCompletion F)) m]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hm)

theorem natCast_apply' (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) : (N : Af F) v = (N : v.adicCompletion F) := by
  first
  | rfl
  | simp

theorem natCast_mul_apply' (N : ℕ) (z : Af F) (v : HeightOneSpectrum (𝓞 F)) :
    ((N : Af F) * z) v = (N : v.adicCompletion F) * z v := by
  rw [← natCast_apply' N v]
  rfl

theorem norm_natCast_lt_one' (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : ((c : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem v.asIdeal)
  rw [Valued.toNormedField.norm_lt_one_iff]
  have h1 : ((c : v.adicCompletion F)) = ((algebraMap (𝓞 F) F (c : 𝓞 F) : F) : v.adicCompletion F) := by
    rw [map_natCast]
    first
    | exact (map_natCast (algebraMap F (v.adicCompletion F)) c).symm
    | norm_cast
    | rfl
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_lt_one_iff_mem _).mpr hmem

theorem finNhd (U : Set (Af F)) (hU : U ∈ 𝓝 (0 : Af F)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z : Af F, (∀ v, z v ∈ v.adicCompletionIntegers F) → (N : Af F) * z ∈ U := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun _ => Valued.isOpen_valuationSubring _
  have hU' : U ∈ Filter.map (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
      (𝓝 (fun v => ⟨0, zero_mem (v.adicCompletionIntegers F)⟩)) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hAopen]
    exact hU
  have hU2 : (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) ⁻¹'
      (U : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)) ∈
      𝓝 (fun v : HeightOneSpectrum (𝓞 F) => (⟨0, zero_mem (v.adicCompletionIntegers F)⟩ :
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := hU'
  rw [nhds_pi, Filter.mem_pi] at hU2
  obtain ⟨I, hI, t, ht, hIt⟩ := hU2
  have hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > (0 : ℝ),
      ∀ y : (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        ‖(y : v.adicCompletion F)‖ < ε → y ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨ε, hε, fun y hy => hut (hball ?_)⟩
    simpa [Metric.mem_ball, dist_zero_right] using hy
  choose ε hεpos hεt using hε
  set c : ℕ := ∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ I, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one' v c (Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv))
  have hev : ∀ v ∈ I, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k < ε v := fun v hv =>
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).eventually
      (Iio_mem_nhds (hεpos v))
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite hI).2 hev).exists
  refine ⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun z hz => ?_⟩
  have hmem : ∀ v, (((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v ∈
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro v
    rw [natCast_mul_apply']
    exact mul_mem (natCast_mem _ _) (hz v)
  have hx : ((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z = RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
      (fun v => ⟨_, hmem v⟩) := by
    ext v
    rfl
  rw [hx]
  apply hIt
  intro v hv
  apply hεt
  show ‖(((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v‖ < ε v
  rw [natCast_mul_apply', norm_mul, Nat.cast_pow, norm_pow]
  have hz1 : ‖z v‖ ≤ 1 := (norm_le_one_iff_int v _).2 (hz v)
  calc ‖(c : v.adicCompletion F)‖ ^ k * ‖z v‖ ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 :=
        mul_le_mul_of_nonneg_left hz1 (pow_nonneg (norm_nonneg _) _)
    _ < ε v := by rw [mul_one]; exact hk v hv

theorem int_of_le (y : Af F) (N M : ℕ) (hN : N ≠ 0)
    (hy : ∀ v, ‖y v‖ ≤ ‖(N : v.adicCompletion F)‖ * ‖(M : v.adicCompletion F)‖) :
    ∃ z : Af F, (∀ v, z v ∈ v.adicCompletionIntegers F) ∧ y = (N : Af F) * z := by
  refine ⟨algebraMap F (Af F) ((N : F)⁻¹) * y, fun v => ?_, ?_⟩
  · rw [← norm_le_one_iff_int]
    show ‖algebraMap F (v.adicCompletion F) ((N : F)⁻¹) * y v‖ ≤ 1
    have hN0 : 0 < ‖(N : v.adicCompletion F)‖ := norm_pos_iff.2 (nat_ne_zero_fin v hN)
    rw [map_inv₀, map_natCast, norm_mul, norm_inv, inv_mul_le_iff₀ hN0, mul_one]
    calc ‖y v‖ ≤ ‖(N : v.adicCompletion F)‖ * ‖(M : v.adicCompletion F)‖ := hy v
      _ ≤ ‖(N : v.adicCompletion F)‖ * 1 := mul_le_mul_of_nonneg_left (norm_nat_le_one v M) hN0.le
      _ = ‖(N : v.adicCompletion F)‖ := mul_one _
  · rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN), map_one, one_mul]

end Formalism.IndefR.Fin.U1

end
end
