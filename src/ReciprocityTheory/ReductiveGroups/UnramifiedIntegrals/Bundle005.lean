module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement

@[expose] public section

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem mem_Tm {m : ℕ} (hm : 0 < m) (t : ℕ × ℕ × ℕ) :
    t ∈ Tm m ↔ t.1 * t.2.2 = m ∧ t.2.1 < t.2.2 := by
  rw [Tm, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hx, rfl⟩
    rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at hx
    exact ⟨Nat.mul_div_cancel' hx.1.1, hx.2⟩
  · obtain ⟨a, b, e⟩ := t
    rintro ⟨h1, h2⟩
    simp only at h1 h2
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have he : m / a = e := by rw [← h1, Nat.mul_div_cancel_left _ ha]
    refine ⟨⟨a, b⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
      exact ⟨⟨⟨e, h1.symm⟩, hm.ne'⟩, by rw [he]; exact h2⟩
    · simp only [he]

theorem Tm_pos {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : 0 < t.1 ∧ 0 < t.2.2 := by
  have h := ((mem_Tm hm t).mp ht).1
  have hpos : 0 < t.1 * t.2.2 := h ▸ hm
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.pos_of_ne_zero fun h0 => ?_⟩ <;>
    rw [h0] at hpos <;> simp at hpos

theorem pt_coe {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    ((pt a b e τ : ℍ) : ℂ) = ((a : ℂ) * τ + b) / e := by
  have hz : 0 < (((a : ℂ) * τ + b) / e).im := by
    rw [Complex.div_natCast_im]
    simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
      UpperHalfPlane.coe_im]
    exact div_pos (mul_pos (by exact_mod_cast ha) τ.im_pos) (by exact_mod_cast he)
  unfold pt
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem DD_ne_zero (τ : ℍ) : DD τ ≠ 0 := by
  exact ModularForm.discriminant_ne_zero τ

theorem smul_of_form {k : ℤ} (g : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    g (γ • τ) = denom γ τ ^ k * g τ := by
  have h := SlashInvariantForm.slash_action_eqn'' g (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ)
    (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) τ
  exact h

theorem isMF_AA : IsMF 12 AA := by
  refine ⟨ModularForm.mcast (by norm_num) (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)), fun τ => ?_⟩
  show (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)) τ = AA τ
  rw [ModularForm.coe_mul, Pi.mul_apply, ModularForm.coe_mul, Pi.mul_apply]
  unfold AA
  ring

theorem isMF_DD : IsMF 12 DD := by
  first
    | exact ⟨ModularFormClass.modularForm CuspForm.discriminant, fun τ => rfl⟩
    | exact ⟨ModularFormClass.modularForm CuspForm.discriminant, fun τ => rfl⟩

theorem IsMF.smul_eq {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = denom γ τ ^ k * f τ := by
  obtain ⟨g, hg⟩ := h
  rw [← hg, ← hg]
  exact smul_of_form g γ τ

theorem AA_smul (γ : SL(2, ℤ)) (τ : ℍ) : AA (γ • τ) = denom γ τ ^ 12 * AA τ := by
  exact isMF_AA.smul_eq γ τ

theorem DD_smul (γ : SL(2, ℤ)) (τ : ℍ) : DD (γ • τ) = denom γ τ ^ 12 * DD τ := by
  exact isMF_DD.smul_eq γ τ

theorem jT_smul (γ : SL(2, ℤ)) (τ : ℍ) : jT (γ • τ) = jT τ := by
  unfold jT
  rw [AA_smul, DD_smul, mul_div_mul_left _ _ (pow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ τ))]

theorem IsMF.congr_weight {k k' : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (hk : k = k') : IsMF k' f := by
  subst hk
  exact h

theorem IsMF.add {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ + g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' + g', fun τ => by simp [hf', hg']⟩

theorem IsMF.sub {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ - g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' - g', fun τ => by simp [hf', hg']⟩

theorem IsMF.const_mul {k : ℤ} {f : ℍ → ℂ} (c : ℂ) (hf : IsMF k f) : IsMF k (fun τ => c * f τ) := by
  obtain ⟨f', hf'⟩ := hf
  exact ⟨c • f', fun τ => by simp [hf']⟩

theorem IsMF.mul {k k' : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k' g) :
    IsMF (k + k') (fun τ => f τ * g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f'.mul g', fun τ => by rw [ModularForm.coe_mul, Pi.mul_apply, hf', hg']⟩

theorem IsMF.pow {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (n : ℕ) : IsMF (n * k) (fun τ => f τ ^ n) := by
  induction n with
  | zero =>
    refine IsMF.congr_weight (k := 0) ⟨1, fun τ => ?_⟩ (by simp)
    simp
  | succ n ih =>
    have h := (ih.mul hf).congr_weight (show (n : ℤ) * k + k = ((n + 1 : ℕ) : ℤ) * k by push_cast; ring)
    simpa [pow_succ] using h

theorem zetaC_pow_self {m : ℕ} (hm : 0 < m) : zetaC m ^ m = 1 := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I := by field_simp
  rw [this, Complex.exp_two_pi_mul_I]

theorem zetaC_mem (m : ℕ) : zetaC m ∈ Rm m := by
  exact Subring.subset_closure (Set.mem_singleton _)

theorem Rm_isIntegral {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ∈ Rm m) : IsIntegral ℤ x := by
  have hζ : IsIntegral ℤ (zetaC m) :=
    IsIntegral.of_pow hm (by rw [zetaC_pow_self hm]; exact isIntegral_one)
  have hle : Rm m ≤ (integralClosure ℤ ℂ).toSubring :=
    Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hζ)
  exact hle hx

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem coeff_xp {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (xp k f) = if k ∣ n then PowerSeries.coeff (n / k) f else 0 := by
  rw [xp, PowerSeries.coeff_mk]

theorem xp_eq_expand {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) :
    xp k f = PowerSeries.expand k hk f := by
  ext n
  rw [coeff_xp, PowerSeries.coeff_expand]

theorem xp_add {R : Type*} [CommRing R] (k : ℕ) (f g : PowerSeries R) : xp k (f + g) = xp k f + xp k g := by
  ext n
  simp only [coeff_xp, map_add (f := _)]
  split_ifs <;> simp

theorem xp_sub {R : Type*} [CommRing R] (k : ℕ) (f g : PowerSeries R) : xp k (f - g) = xp k f - xp k g := by
  ext n
  simp only [coeff_xp, map_sub]
  split_ifs <;> simp

theorem xp_mul {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f g : PowerSeries R) :
    xp k (f * g) = xp k f * xp k g := by
  rw [xp_eq_expand hk, xp_eq_expand hk, xp_eq_expand hk, map_mul]

theorem xp_pow {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) (n : ℕ) :
    xp k (f ^ n) = xp k f ^ n := by
  rw [xp_eq_expand hk, xp_eq_expand hk, map_pow]

theorem xp_C_mul {R : Type*} [CommRing R] (k : ℕ) (c : R) (f : PowerSeries R) :
    xp k (PowerSeries.C c * f) = PowerSeries.C c * xp k f := by
  ext n
  simp only [coeff_xp, PowerSeries.coeff_C_mul]
  split_ifs <;> simp

theorem xp_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) (f : PowerSeries R) :
    xp k (f.map φ) = (xp k f).map φ := by
  ext n
  simp only [coeff_xp, PowerSeries.coeff_map]
  split_ifs <;> simp

theorem CoeffIn.map_int (R : Subring ℂ) (f : PowerSeries ℤ) : CoeffIn R (f.map (Int.castRingHom ℂ)) := by
  intro n
  rw [PowerSeries.coeff_map, eq_intCast]
  exact intCast_mem R _

theorem CoeffIn.add {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f + g) := by
  intro n
  rw [map_add (f := _)]
  exact add_mem (hf n) (hg n)

theorem CoeffIn.sub {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f - g) := by
  intro n
  rw [map_sub]
  exact sub_mem (hf n) (hg n)

theorem CoeffIn.mul {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hf _) (hg _)

theorem CoeffIn.one (R : Subring ℂ) : CoeffIn R 1 := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact one_mem R
  · exact zero_mem R

theorem CoeffIn.pow {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (n : ℕ) : CoeffIn R (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.one R
  | succ n ih =>
    rw [pow_succ]
    exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.mul ih hf

theorem CoeffIn.xp {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (k : ℕ) : CoeffIn R (xp k f) := by
  intro n
  rw [coeff_xp]
  split_ifs
  · exact hf _
  · exact zero_mem R

theorem CoeffIn.sub1 {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) {c : ℂ} (hc : c ∈ R) (k : ℕ) :
    CoeffIn R (sub1 c k f) := by
  have hr : ReciprocityTheory.ChartRestriction.L1.CoeffIn R (PowerSeries.rescale c f) := fun m => by
    rw [PowerSeries.coeff_rescale]
    exact mul_mem (pow_mem hc m) (hf m)
  exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.xp hr k

theorem LowUnit.mul {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ} (hf : LowUnit R f n u)
    (hg : LowUnit R g n' u') : LowUnit R (f * g) (n + n') (u * u') := by
  obtain ⟨hu, hui, hu0, hlow, hc⟩ := hf
  obtain ⟨hu', hui', hu0', hlow', hc'⟩ := hg
  refine ⟨mul_mem hu hu', by rw [mul_inv]; exact mul_mem hui hui', mul_ne_zero hu0 hu0', ?_, ?_⟩
  · intro m hm
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : p.1 < n
    · rw [hlow _ h1, zero_mul]
    · rw [hlow' _ (by omega), mul_zero]
  · rw [PowerSeries.coeff_mul, Finset.sum_eq_single (n, n')]
    · rw [hc, hc']
    · intro p hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases h1 : p.1 < n
      · rw [hlow _ h1, zero_mul]
      · have h2 : p.2 < n' := by
          by_contra h2
          exact hne (Prod.ext (by show p.1 = n; omega) (by show p.2 = n'; omega))
        rw [hlow' _ h2, mul_zero]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (rfl : n + n' = n + n')) h

theorem LowUnit.one (R : Subring ℂ) : LowUnit R 1 0 1 := by
  refine ⟨one_mem R, by rw [inv_one]; exact one_mem R, one_ne_zero,
    fun n hn => absurd hn (Nat.not_lt_zero n), ?_⟩
  simp

theorem LowUnit.prod {R : Subring ℂ} {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ)
    (hf : ∀ t ∈ s, ∃ n u, LowUnit R (f t) n u) : ∃ n u, LowUnit R (∏ t ∈ s, f t) n u := Finset.prod_induction f (fun g => ∃ n u, ReciprocityTheory.ChartRestriction.L1.LowUnit R g n u)
    (fun a b ⟨n, u, ha⟩ ⟨n', u', hb⟩ => ⟨n + n', u * u', ReciprocityTheory.ChartRestriction.L1.LowUnit.mul ha hb⟩)
    ⟨0, 1, ReciprocityTheory.ChartRestriction.L1.LowUnit.one R⟩ hf

end ReciprocityTheory.ChartRestriction.L1
end
end
