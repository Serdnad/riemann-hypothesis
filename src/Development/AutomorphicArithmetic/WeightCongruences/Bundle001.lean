module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.NumberTheory.NumberField.Norm

@[expose] public section

section

namespace UpperTheory

variable {E K K' : Type} [Field E] [Field K] [Field K'] {ι ι' : Type} [Fintype ι] [Fintype ι']

def MU (φ : ι → E →+* K) (e : ι → ℤ) : Prop :=
  ∀ z : E, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → ∏ i, φ i z ^ e i = 1

def MUQ (φ : ι → E →+* K) (e : ι → ℚ) : Prop :=
  ∃ a : ι → ℤ, (∀ i, e i = a i) ∧ MU φ a

theorem root_ne_zero {z : E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : z ≠ 0 := by
  obtain ⟨m, hm, h⟩ := hz
  rintro rfl
  rw [zero_pow hm.ne'] at h
  exact zero_ne_one h

theorem prod_neg_one_zpow (e : ι → ℤ) : ∏ i, (-1 : K) ^ e i = (-1) ^ (∑ i, e i) := by
  classical
  refine Finset.induction_on (motive := fun s => ∏ i ∈ s, (-1 : K) ^ e i = (-1) ^ (∑ i ∈ s, e i)) Finset.univ (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (by norm_num)]

namespace MU

variable {φ : ι → E →+* K} {e e' : ι → ℤ}

theorem add (h : MU φ e) (h' : MU φ e') : MU φ (e + e') := by
  intro z hz
  have hne : ∀ i, φ i z ≠ 0 := fun i => (map_ne_zero (φ i)).2 (root_ne_zero hz)
  show ∏ i, φ i z ^ (e i + e' i) = 1
  rw [Finset.prod_congr rfl fun i _ => zpow_add₀ (hne i) (e i) (e' i), Finset.prod_mul_distrib, h z hz, h' z hz, one_mul]

theorem neg (h : MU φ e) : MU φ (-e) := by
  intro z hz
  show ∏ i, φ i z ^ (-e i) = 1
  simp_rw [zpow_neg]
  rw [Finset.prod_inv_distrib, h z hz, inv_one]

theorem smul (h : MU φ e) (c : ℤ) : MU φ (fun i => c * e i) := by
  intro z hz
  show ∏ i, φ i z ^ (c * e i) = 1
  simp_rw [mul_comm c, zpow_mul]
  rw [Finset.prod_zpow, h z hz, one_zpow]

theorem const (h : MU φ (fun _ => 1)) (c : ℤ) : MU φ (fun _ => c) := by
  have h2 := h.smul c
  simpa using h2

theorem add_const (h : MU φ e) (h1 : MU φ (fun _ => 1)) (c : ℤ) : MU φ (fun i => e i + c) :=
  h.add (h1.const c)

theorem even [CharZero K] (h : MU φ e) : Even (∑ i, e i) := by
  have h1 := h (-1) ⟨2, by norm_num, by norm_num⟩
  simp only [map_neg, map_one] at h1
  rw [prod_neg_one_zpow] at h1
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  rw [hodd.neg_one_zpow] at h1
  norm_num at h1

end MU

namespace MUQ

variable {φ : ι → E →+* K} {e : ι → ℚ}

theorem even [CharZero K] (h : MUQ φ e) : ∃ z : ℤ, ∑ i, e i = 2 * (z : ℚ) := by
  obtain ⟨a, ha, hm⟩ := h
  obtain ⟨z, hz⟩ := hm.even
  refine ⟨z, ?_⟩
  simp only [ha]
  rw [← Int.cast_sum, hz]
  push_cast
  ring

theorem mu (h : MUQ φ e) {a : ι → ℤ} (ha : ∀ i, e i = a i) : MU φ a := by
  obtain ⟨b, hb, hm⟩ := h
  have hab : a = b := funext fun i => by
    have h3 := (ha i).symm.trans (hb i)
    exact_mod_cast h3
  subst hab
  exact hm

theorem add_const (h : MUQ φ e) (h1 : MU φ (fun _ => 1)) (c : ℤ) : MUQ φ (fun i => e i + c) := by
  obtain ⟨a, ha, hm⟩ := h
  exact ⟨fun i => a i + c, fun i => by simp [ha], hm.add_const h1 c⟩

end MUQ

end UpperTheory
end

section

open NumberField IsDedekindDomain
open scoped Pointwise

private theorem exists_nat_residue {L : Type} [Field L] [NumberField L] {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 L)) (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) (hn : Ideal.absNorm v.asIdeal = p)
    (x : 𝓞 L) : ∃ a : ℕ, Ideal.Quotient.mk v.asIdeal x = (a : 𝓞 L ⧸ v.asIdeal) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : CharP (𝓞 L ⧸ v.asIdeal) p := (CharP.charP_iff_prime_eq_zero hp).2 (by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hv)
  have hcard : Nat.card (𝓞 L ⧸ v.asIdeal) = p := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hn]
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) (𝓞 L ⧸ v.asIdeal)) :=
    (ZMod.castHom (dvd_refl p) _).injective
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])
  obtain ⟨k, hk⟩ := hbij.2 (Ideal.Quotient.mk v.asIdeal x)
  refine ⟨k.val, ?_⟩
  rw [← hk, ZMod.castHom_apply, ZMod.natCast_val]

private theorem smul_natCast_eq {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (n : ℕ) :
    σ • (n : 𝓞 L) = n :=
  map_natCast (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) σ) n

private theorem stab_trivial {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 L)) (hv : ((p : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (hn : Ideal.absNorm w.asIdeal = p) (h2 : ((p : ℕ) : 𝓞 L) ∉ w.asIdeal ^ 2)
    (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal) : σ = 1 := by
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  haveI := w.isPrime
  let Q := w.under (𝓞 K)
  haveI := Q.isPrime
  haveI := Q.isMaximal
  haveI : w.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have hin : σ ∈ w.asIdeal.inertia (L ≃ₐ[K] L) := by
    intro x
    obtain ⟨a, ha⟩ := exists_nat_residue hp w hv hn x
    have h1 : x - (a : 𝓞 L) ∈ w.asIdeal := by
      rw [← Ideal.Quotient.eq, ha, map_natCast]
    have h3 : σ • (x - (a : 𝓞 L)) ∈ w.asIdeal := by
      rw [← hσ]; exact Ideal.smul_mem_pointwise_smul _ _ _ h1
    rw [smul_sub, smul_natCast_eq] at h3
    have h4 := w.asIdeal.sub_mem h3 h1
    rw [sub_sub_sub_cancel_right] at h4
    exact h4
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx Q.asIdeal w.asIdeal Q.ne_bot]
    apply Ideal.ramificationIdx'_spec
    · rw [pow_one]; exact Ideal.map_le_iff_le_comap.2 le_rfl
    · intro h
      apply h2
      have h1 : ((p : ℕ) : 𝓞 K) ∈ Q.asIdeal := by
        show ((p : ℕ) : 𝓞 K) ∈ Ideal.under (𝓞 K) w.asIdeal
        rw [Ideal.mem_under, map_natCast]; exact hv
      have h5 := h (Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) h1)
      rwa [map_natCast] at h5
  have hc : Nat.card (w.asIdeal.inertia (L ≃ₐ[K] L)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn Q.asIdeal w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx Q.asIdeal w.asIdeal (L ≃ₐ[K] L), he]
  rw [Subgroup.card_eq_one.1 hc] at hin
  exact Subgroup.mem_bot.1 hin

theorem UpperTheory.prod_residue_char_norm_one_unit_eq_one :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (p : ℕ), p.Prime →
      ∀ (Q : HeightOneSpectrum (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∈ S ↔ w.under (𝓞 K) = Q) →
      (∀ w ∈ S, Ideal.absNorm w.asIdeal = p ∧ ((p : ℕ) : 𝓞 L) ∉ w.asIdeal ^ 2) →
      ∀ (ω : (ZMod p)ˣ →* ℂˣ) (θ : ∀ w : HeightOneSpectrum (𝓞 L), (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ),
      (∀ w ∈ S, ∀ (a : ℕ) (ha : a.Coprime p), ∃ b : (𝓞 L ⧸ w.asIdeal)ˣ,
        (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) ∧ θ w b = ω (ZMod.unitOfCoprime a ha)) →
      ∀ u : (𝓞 L)ˣ, Algebra.norm K ((u : 𝓞 L) : L) = 1 →
        ∏ w ∈ S, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom u) = 1 := by
  intro K L _ _ _ _ _ _ p hp Q S memS hs ω θ hθ ζ hζ
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have overp : ∀ w ∈ S, ((p : ℕ) : 𝓞 L) ∈ w.asIdeal := by
    intro w hw
    rw [← (hs w hw).1]
    exact Ideal.absNorm_mem _
  rcases S.eq_empty_or_nonempty with hE | ⟨w₀, hw₀⟩
  · rw [hE, Finset.prod_empty]

  have hres : ∀ w ∈ S, ∃ a : ℕ, Ideal.Quotient.mk w.asIdeal (ζ : 𝓞 L) = (a : 𝓞 L ⧸ w.asIdeal) := fun w hw =>
    exists_nat_residue hp w (overp w hw) (hs w hw).1 _
  choose! a ha using hres
  have hcop : ∀ w ∈ S, (a w).Coprime p := by
    intro w hw
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_)
    have h0 : ((a w : ℕ) : 𝓞 L ⧸ w.asIdeal) = 0 := by
      obtain ⟨c, hc⟩ := hd
      rw [hc, Nat.cast_mul, ← map_natCast (Ideal.Quotient.mk w.asIdeal) p,
        Ideal.Quotient.eq_zero_iff_mem.2 (overp w hw), zero_mul]
    have hu : IsUnit (Ideal.Quotient.mk w.asIdeal (ζ : 𝓞 L)) := ζ.isUnit.map _
    rw [ha w hw, h0] at hu
    haveI : w.asIdeal.IsMaximal := w.isMaximal
    exact not_isUnit_zero hu

  have hσ : ∀ w ∈ S, ∃ σ : L ≃ₐ[K] L, σ • w.asIdeal = w₀.asIdeal := by
    intro w hw
    haveI := w.isPrime
    haveI := w₀.isPrime
    haveI : w.asIdeal.LiesOver Q.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal ((memS w).1 hw).symm⟩
    haveI : w₀.asIdeal.LiesOver Q.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal ((memS w₀).1 hw₀).symm⟩
    exact Ideal.exists_smul_eq_of_isGaloisGroup Q.asIdeal w.asIdeal w₀.asIdeal (L ≃ₐ[K] L)
  choose! σ hσw using hσ

  have hσres : ∀ w ∈ S, Ideal.Quotient.mk w₀.asIdeal (σ w • (ζ : 𝓞 L)) = (a w : 𝓞 L ⧸ w₀.asIdeal) := by
    intro w hw
    have h1 : (ζ : 𝓞 L) - (a w : 𝓞 L) ∈ w.asIdeal := by
      rw [← Ideal.Quotient.eq, ha w hw, map_natCast]
    have h2 : σ w • ((ζ : 𝓞 L) - (a w : 𝓞 L)) ∈ w₀.asIdeal := by
      rw [← hσw w hw]; exact Ideal.smul_mem_pointwise_smul _ _ _ h1
    rw [smul_sub, smul_natCast_eq] at h2
    rw [← map_natCast (Ideal.Quotient.mk w₀.asIdeal)]
    exact Ideal.Quotient.eq.2 h2

  have hprod : ∏ w ∈ S, σ w • (ζ : 𝓞 L) = 1 := by
    have hre : ∏ w ∈ S, σ w • (ζ : 𝓞 L) = ∏ τ : L ≃ₐ[K] L, τ • (ζ : 𝓞 L) := by
      refine Finset.prod_bij (fun w _ => σ w) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro w₁ h₁ w₂ h₂ h'
        apply HeightOneSpectrum.ext
        rw [eq_inv_smul_iff.2 (hσw w₁ h₁), eq_inv_smul_iff.2 (hσw w₂ h₂), h']
      · intro τ _
        haveI := w₀.isPrime
        have hne : τ⁻¹ • w₀.asIdeal ≠ ⊥ := by
          intro h
          apply w₀.ne_bot
          rw [← smul_inv_smul τ w₀.asIdeal, h]
          ext x
          simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
        let w : HeightOneSpectrum (𝓞 L) := ⟨τ⁻¹ • w₀.asIdeal, inferInstance, hne⟩
        have hw : w ∈ S := by
          rw [memS, ← (memS w₀).1 hw₀]
          apply HeightOneSpectrum.ext
          exact Ideal.under_smul (𝓞 K) w₀.asIdeal τ⁻¹
        refine ⟨w, hw, ?_⟩
        have h1 := stab_trivial hp w (overp w hw) (hs w hw).1 (hs w hw).2 (τ⁻¹ * σ w)
          (by rw [mul_smul, hσw w hw])
        exact (inv_mul_eq_one.1 h1).symm
      · intro w hw
        rfl
    rw [hre]
    apply RingOfIntegers.ext
    have h := Algebra.norm_eq_prod_automorphisms K ((ζ : 𝓞 L) : L)
    rw [hζ, map_one] at h
    have h' : ∀ τ : L ≃ₐ[K] L, algebraMap (𝓞 L) L (τ • (ζ : 𝓞 L)) = τ ((ζ : 𝓞 L) : L) :=
      fun τ => rfl
    show algebraMap (𝓞 L) L (∏ τ : L ≃ₐ[K] L, τ • (ζ : 𝓞 L)) = algebraMap (𝓞 L) L 1
    rw [map_prod, map_one]
    exact (Finset.prod_congr rfl fun τ _ => h' τ).trans h.symm

  haveI : w₀.asIdeal.IsMaximal := w₀.isMaximal
  haveI : CharP (𝓞 L ⧸ w₀.asIdeal) p := (CharP.charP_iff_prime_eq_zero hp).2 (by
    rw [← map_natCast (Ideal.Quotient.mk w₀.asIdeal)]; exact Ideal.Quotient.eq_zero_iff_mem.2 (overp w₀ hw₀))
  have hmod : ∏ w ∈ S, ((a w : ℕ) : ZMod p) = 1 := by
    apply (ZMod.castHom (dvd_refl p) (𝓞 L ⧸ w₀.asIdeal)).injective
    rw [map_prod, map_one]
    have : ∏ w ∈ S, (ZMod.castHom (dvd_refl p) (𝓞 L ⧸ w₀.asIdeal)) ((a w : ℕ) : ZMod p) =
        ∏ w ∈ S, Ideal.Quotient.mk w₀.asIdeal (σ w • (ζ : 𝓞 L)) :=
      Finset.prod_congr rfl fun w hw => by rw [map_natCast, hσres w hw]
    rw [this, ← map_prod, hprod, map_one]

  let u : HeightOneSpectrum (𝓞 L) → (ZMod p)ˣ := fun w =>
    if h : (a w).Coprime p then ZMod.unitOfCoprime (a w) h else 1
  have hval : ∀ w ∈ S, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = ω (u w) := by
    intro w hw
    simp only [u, dif_pos (hcop w hw)]
    obtain ⟨b, hb, hθb⟩ := hθ w hw (a w) (hcop w hw)
    rw [← hθb]
    congr 1
    apply Units.ext
    rw [hb, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ha w hw, map_natCast]
  rw [Finset.prod_congr rfl hval, ← map_prod]
  have hu1 : ∏ w ∈ S, u w = 1 := by
    apply Units.ext
    rw [Units.coe_prod, Units.val_one, ← hmod]
    refine Finset.prod_congr rfl fun w hw => ?_
    simp only [u, dif_pos (hcop w hw), ZMod.coe_unitOfCoprime]
  rw [hu1, map_one]
end

section

open NumberField IsDedekindDomain

private theorem prod_interp_mod {Ω ι : Type*} [CommRing Ω] (n : ℕ) (e t : Ω) (he : e * e - e = n * t)
    (hei : IsIntegral ℤ e) (hti : IsIntegral ℤ t) (f g : ι → Ω) (hf : ∀ i, IsIntegral ℤ (f i))
    (hg : ∀ i, IsIntegral ℤ (g i)) (s : Finset ι) :
    ∃ z, IsIntegral ℤ z ∧ ∏ i ∈ s, (e * f i + (1 - e) + n * g i) = e * ∏ i ∈ s, f i + (1 - e) + n * z := by
  classical
  have hn : IsIntegral ℤ (n : Ω) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := Ω) (x := (n : ℤ)))
  induction s using Finset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨z, hz, hprod⟩ := ih
    set P := ∏ i ∈ s, f i with hP
    have hPi : IsIntegral ℤ P := IsIntegral.prod _ fun i _ => hf i
    refine ⟨t * f a * P - t * f a - t * P + t + g a * (e * P + (1 - e)) +
      z * (e * f a + (1 - e)) + n * g a * z, ?_, ?_⟩
    · have h1e : IsIntegral ℤ (1 - e) := isIntegral_one.sub hei
      exact ((((((hti.mul (hf a)).mul hPi).sub (hti.mul (hf a))).sub (hti.mul hPi)).add hti).add
        ((hg a).mul ((hei.mul hPi).add h1e))).add (hz.mul ((hei.mul (hf a)).add h1e)) |>.add
        ((hn.mul (hg a)).mul hz)
    · rw [Finset.prod_insert ha, Finset.prod_insert ha, hprod]
      linear_combination (f a * P - f a - P + 1) * he

private theorem descend_mod {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (n : ℕ) (a : F) (z : Ω)
    (hz : IsIntegral ℤ z) (h : algebraMap F Ω a = 1 + n * z) :
    ∃ w : F, IsIntegral ℤ w ∧ a = 1 + n * w := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, isIntegral_zero, ?_⟩
    apply (algebraMap F Ω).injective
    simpa using h
  · have hnF : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
    refine ⟨(a - 1) / n, ?_, by field_simp; ring⟩
    have hmap : algebraMap F Ω ((a - 1) / n) = z := by
      have hnΩ : (n : Ω) ≠ 0 := by
        rw [← map_natCast (algebraMap F Ω)]
        exact (map_ne_zero _).mpr hnF
      rw [map_div₀, map_sub, map_one, map_natCast, h]
      field_simp
      ring
    rw [← isIntegral_algebraMap_iff (B := Ω), hmap]
    exact hz

theorem UpperTheory.dvd_norm_sub_one_of_idempotent_interpolation_relNorm_one :
    ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (n : ℕ) (e t δ y : 𝓞 E), (e : E) ∈ K → e * e - e = n * t →
      Algebra.norm K (δ : E) = 1 → (n : ℤ) ∣ Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) - 1 := by
  intro E _ _ K n e t δ y heK he hδ
  classical
  let Ω := AlgebraicClosure E
  have hint : ∀ u : 𝓞 E, IsIntegral ℤ (u : E) := fun u => u.2
  have hintΩ : ∀ (u : 𝓞 E) (σ : E →ₐ[K] Ω), IsIntegral ℤ (σ u) := fun u σ =>
    (hint u).map (σ.restrictScalars ℚ).toRingHom.toIntAlgHom
  have hσe : ∀ σ : E →ₐ[K] Ω, σ (e : E) = algebraMap E Ω e := by
    intro σ
    have h := σ.commutes (⟨e, heK⟩ : K)
    rw [IsScalarTower.algebraMap_apply K E Ω] at h
    exact h
  have heE : ((e : E) * e - e) = n * (t : E) := by
    have h := congrArg (fun u : 𝓞 E => (u : E)) he
    simpa using h
  have heΩ : algebraMap E Ω e * algebraMap E Ω e - algebraMap E Ω e = n * algebraMap E Ω t := by
    have h := congrArg (algebraMap E Ω) heE
    simpa using h
  obtain ⟨z, hz, hprod⟩ := prod_interp_mod n (algebraMap E Ω e) (algebraMap E Ω t) heΩ
    ((hint e).map (IsScalarTower.toAlgHom ℤ E Ω)) ((hint t).map (IsScalarTower.toAlgHom ℤ E Ω))
    (fun σ : E →ₐ[K] Ω => σ δ) (fun σ => σ y) (fun σ => hintΩ δ σ) (fun σ => hintΩ y σ) Finset.univ
  have hδΩ : ∏ σ : E →ₐ[K] Ω, σ δ = 1 := by
    rw [← Algebra.norm_eq_prod_embeddings, hδ, map_one]
  have hK : algebraMap K Ω (Algebra.norm K ((e * δ + (1 - e) + n * y : 𝓞 E) : E)) = 1 + n * z := by
    rw [Algebra.norm_eq_prod_embeddings]
    have hσ : ∀ σ : E →ₐ[K] Ω, σ ((e * δ + (1 - e) + n * y : 𝓞 E) : E) =
        algebraMap E Ω e * σ δ + (1 - algebraMap E Ω e) + n * σ y := by
      intro σ
      push_cast
      rw [map_add (f := _), map_add (f := _), map_mul, map_sub, map_one, map_mul, map_natCast, hσe]
    simp_rw [hσ]
    rw [hprod, hδΩ]
    ring
  obtain ⟨w, hw, hwK⟩ := descend_mod n _ z hz hK
  let Ω₂ := AlgebraicClosure K
  obtain ⟨z₂, hz₂, hprod₂⟩ := prod_interp_mod (Ω := Ω₂) n 1 0 (by simp) isIntegral_one isIntegral_zero
    (fun _ : K →ₐ[ℚ] Ω₂ => 1) (fun τ => τ w) (fun _ => isIntegral_one)
    (fun τ => hw.map τ.toRingHom.toIntAlgHom) Finset.univ
  simp only [one_mul, sub_self, add_zero, Finset.prod_const_one] at hprod₂
  have hQ : algebraMap ℚ Ω₂ (Algebra.norm ℚ (1 + n * w)) = 1 + n * z₂ := by
    rw [Algebra.norm_eq_prod_embeddings]
    simp_rw [map_add (f := _), map_one, map_mul, map_natCast]
    exact hprod₂
  obtain ⟨w₂, hw₂, hw₂Q⟩ := descend_mod n _ z₂ hz₂ hQ
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hw₂
  have hnorm : ((Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) : ℤ) : ℚ) = 1 + n * m := by
    rw [Algebra.coe_norm_int, ← Algebra.norm_norm (S := K), hwK, hw₂Q, ← hm]
    simp
  have hZ : Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) = 1 + n * m := by
    exact_mod_cast hnorm
  exact ⟨m, by rw [hZ]; ring⟩
end
