module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Mathlib.RingTheory.DividedPowers.DPMorphism
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.RingTheory.Ideal.Quotient.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open PositivityTheory.PfSWUS.Loc
namespace GlobalTheory.CompanionTheory.SiegLoc

variable {R : Type} [CommRing R]

theorem psi_pow {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (k j : ℕ) (a : R) :
    ψ (k + j) (Ideal.Quotient.mk _ (ϖ ^ j * a)) = ψ k (Ideal.Quotient.mk _ a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih, ← Nat.add_assoc, pow_succ', mul_assoc]
    exact hψ.compat (k + j) (ϖ ^ j * a)

theorem mem_lev_iff {ϖ : R} {k : ℕ} {a : R} : a ∈ lev ϖ k ↔ ∃ c, a = ϖ ^ k * c := by
  rw [lev, Ideal.mem_span_singleton, dvd_def]

theorem fixed_nondeg {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (hfix : σ ϖ = ϖ) (hreg : IsSMulRegular R ϖ) (k : ℕ) (a : R)
    (ha : σ a = a) (h : ∀ b, σ b = b → ψ k (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev ϖ k := by
  induction k generalizing a with
  | zero => simp [lev]
  | succ k ih =>
    have ha' : a ∈ lev ϖ k := ih a ha (fun b hb => by
      have := h (ϖ * b) (by simp [hfix, hb])
      rw [show a * (ϖ * b) = ϖ * (a * b) by ring, hψ.compat] at this
      exact this)
    obtain ⟨c, rfl⟩ := mem_lev_iff.1 ha'
    have hregk : IsSMulRegular R (ϖ ^ k) := hreg.pow k
    have hc : σ c = c := by
      apply hregk
      simpa [map_mul, map_pow, hfix] using ha
    have hc1 : c ∈ lev ϖ 1 := hψ.prim c hc (fun b hb => by
      have h1 := h b hb
      have h2 := psi_pow hψ 1 k (c * b)
      rw [Nat.add_comm 1 k, ← mul_assoc] at h2
      rw [← h2]; exact h1)
    obtain ⟨d, rfl⟩ := mem_lev_iff.1 hc1
    exact mem_lev_iff.2 ⟨d, by ring⟩

theorem trace_nondeg {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ) (k : ℕ) (y : R)
    (h : ∀ t, ψ k (Ideal.Quotient.mk _ (t * y + σ (t * y))) = 1) : y ∈ lev ϖ k := by
  obtain ⟨u, hu, -⟩ := hR.basis
  have key : ∀ t, t * y + σ (t * y) ∈ lev ϖ k := fun t => by
    refine fixed_nondeg hψ hR.fix_ϖ hR.reg k _ (by simp [hR.inv, add_comm]) (fun b hb => ?_)
    have := h (b * t)
    convert this using 3
    simp only [map_mul, hb]; ring
  have h1 := key 1
  have h2 := key u
  have h3 : (u - σ u) * y ∈ lev ϖ k := by
    have : (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y)) := by
      simp only [map_mul, map_one]; ring
    rw [this]
    exact Ideal.sub_mem _ h2 (Ideal.mul_mem_left _ _ h1)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have : y = v * ((u - σ u) * y) := by rw [← mul_assoc, hv, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h3

end GlobalTheory.CompanionTheory.SiegLoc
end
end

section

open PositivityTheory.PfSWUS.Loc

namespace GlobalTheory.CompanionTheory.UnrDens

private def mulPow {R : Type} [CommRing R] (ϖ : R) (k : ℕ) : R →+ R ⧸ lev ϖ (k + 1) :=
  ((Ideal.Quotient.mk (lev ϖ (k + 1))).toAddMonoidHom).comp (AddMonoidHom.mulLeft (ϖ ^ k))

private theorem mulPow_apply {R : Type} [CommRing R] (ϖ : R) (k : ℕ) (a : R) :
    mulPow ϖ k a = Ideal.Quotient.mk (lev ϖ (k + 1)) (ϖ ^ k * a) := rfl

private theorem lev_succ_le {R : Type} [CommRing R] (ϖ : R) (k : ℕ) : lev ϖ (k + 1) ≤ lev ϖ k := by
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ k))

private theorem mulPow_ker {R : Type} [CommRing R] {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) :
    (mulPow ϖ k).ker = (lev ϖ 1).toAddSubgroup := by
  ext a
  rw [AddMonoidHom.mem_ker, mulPow_apply, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_toAddSubgroup]
  simp only [lev, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hinj : Function.Injective (fun y : R => ϖ ^ k • y) := hr.pow k
    apply hinj
    show ϖ ^ k • a = ϖ ^ k • (ϖ ^ 1 * c)
    rw [smul_eq_mul, smul_eq_mul, hc]
    ring
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; ring⟩

theorem card_quot_lev_succ {R : Type} [CommRing R] {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) :
    Nat.card (R ⧸ lev ϖ (k + 1)) = Nat.card (R ⧸ lev ϖ 1) * Nat.card (R ⧸ lev ϖ k) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⧸ lev ϖ (k + 1) →+ R ⧸ lev ϖ k,
      ∀ a, φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a :=
    ⟨(Ideal.Quotient.lift (lev ϖ (k + 1)) (Ideal.Quotient.mk (lev ϖ k))
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (lev_succ_le ϖ k ha))).toAddMonoidHom,
      fun a => by simp⟩
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, hφ a⟩
  have hker : φ.ker = (mulPow ϖ k).range := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [AddMonoidHom.mem_ker, hφ, AddMonoidHom.mem_range, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
      exact ⟨c, by rw [mulPow_apply, ← hc]⟩
    · rintro ⟨c, hc⟩
      rw [mulPow_apply, Ideal.Quotient.eq] at hc
      have h1 : ϖ ^ k * c - a ∈ lev ϖ k := lev_succ_le ϖ k hc
      have h2 : ϖ ^ k * c ∈ lev ϖ k := Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      have := sub_mem h2 h1
      simpa using this
  have e1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  have e2 : Nat.card ((R ⧸ lev ϖ (k + 1)) ⧸ φ.ker) = Nat.card (R ⧸ lev ϖ k) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
  have e3 : Nat.card φ.ker = Nat.card (R ⧸ lev ϖ 1) := by
    rw [hker]
    have := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (mulPow ϖ k)).toEquiv
    rw [← this, mulPow_ker hr]
    rfl
  rw [e1, e2, e3]
  ring

theorem card_quot_lev : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ k : ℕ, Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := by
  intro R _ σ ϖ q ε hR k
  induction k with
  | zero =>
    have htop : lev ϖ 0 = ⊤ := by
      show Ideal.span {ϖ ^ 0} = ⊤
      rw [pow_zero]
      exact Ideal.span_singleton_one
    rw [Nat.mul_zero, pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨Ideal.Quotient.subsingleton_iff.mpr htop, ⟨0⟩⟩
  | succ k ih =>
    rw [card_quot_lev_succ hR.reg k, ih, hR.card]
    ring

end GlobalTheory.CompanionTheory.UnrDens
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.RootsUpToUnits

theorem subsingleton_of_mul_eq_one {S : Type} [CommRing S] {ϖ c : S}
    (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) (h : ϖ * c = 1) : Subsingleton S := by
  have hu := (Ideal.mem_jacobson_bot.mp hJ) (-c)
  rw [mul_neg, h, neg_add_cancel] at hu
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)

theorem normal_form {S : Type} [CommRing S] (ϖ : S) (h : ∀ f : S, ϖ ∣ f ∨ f ∣ ϖ) (f : S) (M : ℕ) :
    ϖ ^ M ∣ f ∨ ∃ (j : ℕ) (f' : S), f = ϖ ^ j * f' ∧ f' ∣ ϖ := by
  induction M generalizing f with
  | zero => left; simp
  | succ M ih =>
    rcases h f with ⟨g, rfl⟩ | hf
    · rcases ih g with hg | ⟨j, f', rfl, hf'⟩
      · left; rw [pow_succ']; exact mul_dvd_mul_left ϖ hg
      · right; exact ⟨j + 1, f', by ring, hf'⟩
    · right; exact ⟨0, f, by simp, hf⟩

theorem root_of_dvd {S : Type} [CommRing S] {ϖ g : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson)
    (hA : Aic (S := S ⧸ Ideal.span {ϖ ^ 2})) (hg : g ∣ ϖ) {i : ℕ} (hi : 0 < i) :
    ∃ (r : S) (u : Sˣ), g = u * r ^ i := by
  obtain ⟨h, hh⟩ := hg
  by_cases hn : Nontrivial (S ⧸ Ideal.span {ϖ ^ 2})
  · haveI := hn
    obtain ⟨x, hx⟩ := hA (Polynomial.X ^ i - Polynomial.C (Ideal.Quotient.mk _ g))
      (Polynomial.monic_X_pow_sub_C _ hi.ne') (by rw [Polynomial.natDegree_X_pow_sub_C _]; exact hi)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) r) ^ i - Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) g = 0 := by
      simpa using hx
    have hmem : r ^ i - g ∈ Ideal.span {ϖ ^ 2} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
      exact hx'
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
    have hu := (Ideal.mem_jacobson_bot.mp hJ) (t * h)
    have key : r ^ i = g * (ϖ * (t * h) + 1) := by
      have e1 : r ^ i = g + t * ϖ ^ 2 := by rw [ht]; ring
      rw [e1, hh]; ring
    refine ⟨r, hu.unit⁻¹, ?_⟩
    rw [key]
    calc g = ((↑hu.unit⁻¹ : S) * (ϖ * (t * h) + 1)) * g := by rw [hu.val_inv_mul, one_mul]
      _ = (↑hu.unit⁻¹ : S) * (g * (ϖ * (t * h) + 1)) := by ring
  · have hs : Subsingleton (S ⧸ Ideal.span {ϖ ^ 2}) := not_nontrivial_iff_subsingleton.mp hn
    have h1 : (1 : S) ∈ Ideal.span {ϖ ^ 2} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; exact Subsingleton.elim _ _
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    have hS : Subsingleton S := subsingleton_of_mul_eq_one (c := ϖ * a) hJ (by rw [← ha]; ring)
    exact ⟨1, 1, Subsingleton.elim _ _⟩

theorem roots_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S := S ⧸ Ideal.span {ϖ ^ 2}) → Roots ϖ := by
  intro S _ ϖ hJ hϖ hD hA f N i hf hi
  have hdich : ∀ g : S, ϖ ∣ g ∨ g ∣ ϖ := fun g =>
    hD g ϖ ⟨1, by rw [pow_one]; exact Ideal.subset_span (by simp)⟩
  rcases normal_form ϖ hdich f (N + 1) with hM | ⟨j, f', rfl, hf'⟩
  · obtain ⟨k, hk⟩ := dvd_trans hM hf
    have e0 : (1 - ϖ * k) * ϖ ^ N = 0 := by linear_combination hk
    have e1 : 1 - ϖ * k = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hϖ N)).mp e0
    have hS : Subsingleton S := subsingleton_of_mul_eq_one (c := k) hJ (by linear_combination -e1)
    exact ⟨1, 1, Subsingleton.elim _ _⟩
  · obtain ⟨r0, u0, h0⟩ := root_of_dvd hJ hA (dvd_refl ϖ) hi
    obtain ⟨r, u, hr⟩ := root_of_dvd hJ hA hf' hi
    refine ⟨r0 ^ j * r, u0 ^ j * u, ?_⟩
    rw [hr, h0]; push_cast; ring

end GlobalTheory.CompanionTheory.RootsUpToUnits
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValIntClosed

theorem exists_eq_of_isIntegral : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ →
    ∀ x : Localization.Away ϖ, IsIntegral S x → ∃ y : S, algebraMap S (Localization.Away ϖ) y = x := by
  intro S _ ϖ hϖ hV x hx
  obtain ⟨P, hm, hP⟩ := hx
  obtain ⟨N, f, hf⟩ := IsLocalization.Away.surj ϖ x
  set a := algebraMap S (Localization.Away ϖ) with ha
  have hinj : Function.Injective a :=
    IsLocalization.injective (Localization.Away ϖ) (Submonoid.powers_le.2 hϖ)
  have hwnz : ϖ ^ N ∈ nonZeroDivisors S := pow_mem hϖ N
  have hwu : IsUnit (a (ϖ ^ N)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit ϖ).pow N
  obtain ⟨e, he, ⟨b, hb⟩, ⟨h, hh⟩⟩ := (by
    obtain ⟨e, he, h1, h2⟩ := hV f (ϖ ^ N) ⟨N, Ideal.subset_span (by simp)⟩
    exact ⟨e, he, Ideal.mem_span_singleton.1 h1, Ideal.mem_span_singleton.1 h2⟩ :
      ∃ e : S, IsIdempotentElem e ∧ ϖ ^ N ∣ e * f ∧ f ∣ (1 - e) * ϖ ^ N)
  set u := 1 - e with hu
  have hui : IsIdempotentElem u := he.one_sub
  set d := P.natDegree with hd

  have hhx : a h * x = a u := by
    apply hwu.mul_left_cancel
    calc a (ϖ ^ N) * (a h * x) = a h * (x * a (ϖ ^ N)) := by ring
      _ = a h * a f := by rw [map_pow, hf]
      _ = a u * a (ϖ ^ N) := by rw [← map_mul, ← map_mul, hh]; ring_nf
      _ = a (ϖ ^ N) * a u := by ring
  have hUi : a u * a u = a u := by rw [← map_mul, hui.eq]
  have hUp : ∀ i : ℕ, a u * a u ^ i = a u := by
    intro i
    induction i with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, hUi]
  set k : S := ∑ i ∈ Finset.range d, P.coeff i * h ^ (d - 1 - i) with hk
  have hrel : a (u * (1 + h * k)) = 0 := by
    have h0 : a u * a h ^ d * Polynomial.eval₂ a x P = 0 := by
      have : Polynomial.eval₂ a x P = 0 := hP
      rw [this, mul_zero]
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, mul_add, Finset.mul_sum] at h0
    have hlead : P.coeff d = 1 := hm
    have t1 : a u * a h ^ d * (a (P.coeff d) * x ^ d) = a u := by
      rw [hlead, map_one, one_mul, mul_assoc, ← mul_pow, hhx, hUp]
    have t2 : ∀ i ∈ Finset.range d, a u * a h ^ d * (a (P.coeff i) * x ^ i)
        = a u * (a h * a (P.coeff i * h ^ (d - 1 - i))) := by
      intro i hi
      have hi' : i < d := Finset.mem_range.1 hi
      have hd' : d = i + (1 + (d - 1 - i)) := by omega
      have : a h ^ d = a h ^ i * (a h * a h ^ (d - 1 - i)) := by
        conv_lhs => rw [hd', pow_add, pow_add, pow_one]
      rw [this]
      calc a u * (a h ^ i * (a h * a h ^ (d - 1 - i))) * (a (P.coeff i) * x ^ i)
          = (a u * (a h * x) ^ i) * (a h * (a (P.coeff i) * a h ^ (d - 1 - i))) := by
            rw [mul_pow]; ring
        _ = a u * (a h * a (P.coeff i * h ^ (d - 1 - i))) := by
            rw [hhx, hUp, map_mul, map_pow]
    rw [t1, Finset.sum_congr rfl t2, ← Finset.mul_sum, ← Finset.mul_sum] at h0

    rw [map_mul, map_add (f := _), map_one, map_mul, hk, map_sum]
    rw [mul_add, mul_one, add_comm]
    exact h0
  have hrel' : u * (1 + h * k) = 0 := hinj (by rw [hrel, map_zero])
  have hu' : u = - (u * h * k) := by linear_combination hrel'
  have hdiv : ϖ ^ N ∣ f := by
    have hfe : f = e * f + u * f := by rw [hu]; ring
    have huf : u * f = ϖ ^ N * (-(k * u)) := by
      calc u * f = - (u * h * k) * f := by rw [← hu']
        _ = - (k * u * (f * h)) := by ring
        _ = - (k * u * (u * ϖ ^ N)) := by rw [hh]
        _ = - (k * (u * u) * ϖ ^ N) := by ring
        _ = ϖ ^ N * (-(k * u)) := by rw [hui.eq]; ring
    exact ⟨b + -(k * u), by rw [hfe, hb, huf]; ring⟩
  obtain ⟨y, hy⟩ := hdiv
  refine ⟨y, ?_⟩
  apply hwu.mul_left_cancel
  rw [← map_mul, ← hy, ← hf, map_pow, mul_comm]

end GlobalTheory.CompanionTheory.ValIntClosed
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.AicLimit

theorem mem_pow_smul_top_iff {S : Type} [CommRing S] (t y : S) (n : ℕ) :
    y ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule S S) ↔ t ^ n ∣ y := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem step_at {S : Type} [CommRing S] {ϖ : S} (hS : Step ϖ) (P : Polynomial S) (hP : P.Monic)
    (hd : 0 < P.natDegree) (n : ℕ) (x : S) (hx : ϖ ^ n ∣ P.eval x) :
    ∃ z, ϖ ^ (n + 1) ∣ P.eval (x + z) ∧ ϖ ^ n ∣ z ^ P.natDegree := by
  have hnt : Nontrivial S := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [Subsingleton.elim P 0, Polynomial.natDegree_zero] at hd
    exact lt_irrefl 0 hd
  have hq : (Polynomial.X + Polynomial.C x).natDegree = 1 := Polynomial.natDegree_X_add_C x
  have hQm : (P.comp (Polynomial.X + Polynomial.C x)).Monic :=
    hP.comp (Polynomial.monic_X_add_C x) (by rw [hq]; exact one_ne_zero)
  have hQd : (P.comp (Polynomial.X + Polynomial.C x)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero (by
      rw [hP.leadingCoeff, (Polynomial.monic_X_add_C x).leadingCoeff, one_pow, one_mul]
      exact one_ne_zero), hq, mul_one]
  obtain ⟨z, hz1, hz2⟩ := hS (P.comp (Polynomial.X + Polynomial.C x)) n hQm (by rw [hQd]; exact hd)
    (by simpa [Polynomial.eval_comp] using hx)
  refine ⟨z, ?_, ?_⟩
  · simpa [Polynomial.eval_comp, add_comm] using hz1
  · rwa [hQd] at hz2

theorem exists_seq {S : Type} [CommRing S] {ϖ : S} (hS : Step ϖ) (P : Polynomial S) (hP : P.Monic)
    (hd : 0 < P.natDegree) :
    ∃ x : ℕ → S, (∀ n, ϖ ^ n ∣ P.eval (x n)) ∧ ∀ n, ϖ ^ n ∣ (x (n + 1) - x n) ^ P.natDegree := by
  let next : ∀ n, {x : S // ϖ ^ n ∣ P.eval x} → {x : S // ϖ ^ (n + 1) ∣ P.eval x} := fun n x =>
    ⟨x.1 + Classical.choose (step_at hS P hP hd n x.1 x.2),
      (Classical.choose_spec (step_at hS P hP hd n x.1 x.2)).1⟩
  let seq : ∀ n, {x : S // ϖ ^ n ∣ P.eval x} := fun n =>
    Nat.rec (motive := fun n => {x : S // ϖ ^ n ∣ P.eval x}) ⟨0, by simp⟩ next n
  refine ⟨fun n => (seq n).1, fun n => (seq n).2, fun n => ?_⟩
  have h := (Classical.choose_spec (step_at hS P hP hd n (seq n).1 (seq n).2)).2
  have he : (seq (n + 1)).1 - (seq n).1 = Classical.choose (step_at hS P hP hd n (seq n).1 (seq n).2) :=
    add_sub_cancel_left (seq n).1 _
  show ϖ ^ n ∣ ((seq (n + 1)).1 - (seq n).1) ^ P.natDegree
  rw [he]
  exact h

theorem aic_of_step : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S],
    Step ϖ → (∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z) → Aic (S := S) := by
  intro S _ ϖ _ hS hroot P hP hd0
  obtain ⟨x, hx1, hx2⟩ := exists_seq hS P hP hd0
  obtain ⟨d, hdd⟩ : ∃ d, d = P.natDegree := ⟨_, rfl⟩
  rw [← hdd] at hx2 hd0
  have hΔ : ∀ n, ϖ ^ (n / d) ∣ x (n + 1) - x n := fun n =>
    hroot _ (n / d) d hd0 ((pow_dvd_pow ϖ (Nat.div_mul_le_self n d)).trans (hx2 n))
  have hstep : ∀ k, ϖ ^ k ∣ x ((k + 1) * d) - x (k * d) := by
    intro k
    have hi : ∀ i, ϖ ^ k ∣ x (k * d + i) - x (k * d) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have h1 : ϖ ^ k ∣ x (k * d + i + 1) - x (k * d + i) :=
          (pow_dvd_pow ϖ ((Nat.le_div_iff_mul_le hd0).2 (Nat.le_add_right _ _))).trans (hΔ (k * d + i))
        rw [show k * d + (i + 1) = k * d + i + 1 from rfl,
          ← sub_add_sub_cancel (x (k * d + i + 1)) (x (k * d + i)) (x (k * d))]
        exact dvd_add h1 ih
    have h3 := hi d
    rwa [show k * d + d = (k + 1) * d by ring] at h3
  have hcauchy : ∀ m n, m ≤ n → ϖ ^ m ∣ x (n * d) - x (m * d) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [← sub_add_sub_cancel (x ((n + 1) * d)) (x (n * d)) (x (m * d))]
      exact dvd_add ((pow_dvd_pow ϖ hmn).trans (hstep n)) ih
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {ϖ}) inferInstance
    (f := fun k => x (k * d)) (fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_smul_top_iff]
      exact dvd_sub_comm.1 (hcauchy m n hmn))
  refine ⟨L, ?_⟩
  show Polynomial.eval L P = 0
  apply IsHausdorff.haus (I := Ideal.span {ϖ}) inferInstance
  intro k
  rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top_iff]
  have h1 : ϖ ^ k ∣ x (k * d) - L := by
    have h0 := hL k
    rw [SModEq.sub_mem, mem_pow_smul_top_iff] at h0
    exact h0
  have h2 : ϖ ^ k ∣ P.eval (x (k * d)) :=
    (pow_dvd_pow ϖ (Nat.le_mul_of_pos_right k hd0)).trans (hx1 (k * d))
  have h4 : ϖ ^ k ∣ P.eval (x (k * d)) - P.eval L := h1.trans (Polynomial.sub_dvd_eval_sub _ _ _)
  have h5 : P.eval L = P.eval (x (k * d)) - (P.eval (x (k * d)) - P.eval L) := by ring
  rw [h5]
  exact dvd_sub h2 h4

end GlobalTheory.CompanionTheory.AicLimit
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdMor

theorem isDPMorphism_of_isPd : ∀ {S : Type} [CommRing S] {S' E E' : Type} [CommRing S'] [CommRing E] [CommRing E'] (π : S →+* E) (π' : S' →+* E') (I : Ideal S) (I' : Ideal S') {J : Ideal E} {J' : Ideal E'} (δ : DividedPowers J) (δ' : DividedPowers J') (F₀ : S →+* S') (F : E →+* E'), Function.Surjective π → PdI I → IsPd π I δ → IsPd π' I' δ' → (∀ x ∈ I, F₀ x ∈ I') → (∀ x, F (π x) = π' (F₀ x)) → DividedPowers.IsDPMorphism δ δ' F := by
  intro S _ S' E E' _ _ _ π π' I I' J J' δ δ' F₀ F hπ hI hP hP' hF₀ hF
  have hmem : ∀ a ∈ J, ∃ x ∈ I, π x = a := fun a ha => by
    rw [hP.1] at ha
    exact (Ideal.mem_map_iff_of_surjective π hπ).mp ha
  have hdp : ∀ (k : ℕ) (x : S), x ∈ I → ∃ y : S, (k.factorial : S) * y = x ^ k := by
    intro k x hx
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, by simp⟩
    · obtain ⟨y, -, hy⟩ := hI x hx k hk.ne'
      exact ⟨y, hy⟩
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨x, hx, rfl⟩ := hmem a ha
    rw [Ideal.mem_comap, hF, hP'.1]
    exact Ideal.mem_map_of_mem π' (hF₀ x hx)
  · intro n a ha
    obtain ⟨x, hx, rfl⟩ := hmem a ha
    obtain ⟨y, hy⟩ := hdp n x hx
    rw [hP.2 n x y hx hy, hF, hF,
      hP'.2 n (F₀ x) (F₀ y) (hF₀ x hx) (by rw [← map_pow, ← hy, map_mul, map_natCast])]

end GlobalTheory.CompanionTheory.PdMor
end
