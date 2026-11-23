module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.UPel.HT.Gen

namespace UpperTheory.Gal.FiniteEtaleModels.O

theorem tResim : TResim := by
  intro G k _ Q _ act e I g hg
  have hn : ∀ n : ℕ, 0 < n → ∀ z : G.La, I.ev n (n • z) = 1 := fun n h0 z =>
    (I.ker n h0 _).2 ⟨z, rfl⟩
  have hadd : ∀ n : ℕ, 0 < n → ∀ (x z : G.La), I.ev n (x + n • z) = I.ev n x := by
    intro n h0 x z
    rw [I.add, hn n h0, mul_one]
  refine ⟨{ ζ := I.ζ
            ζ_prim := I.ζ_prim
            ζ_pow := I.ζ_pow
            ev := fun n x => if 0 < n then I.ev n (g n x) else I.ev n x
            add := ?_
            lin := ?_
            ker := ?_
            onto := ?_
            tower := ?_
            isom := ?_ }, ?_⟩
  · intro n x y
    by_cases h0 : 0 < n
    · simp only [if_pos h0, map_add (f := _), I.add]
    · simp only [if_neg h0, I.add]
  · intro n b x
    by_cases h0 : 0 < n
    · simp only [if_pos h0]
      obtain ⟨z, hz⟩ := hg.lin n h0 b x
      rw [hz, hadd n h0, I.lin]
    · simp only [if_neg h0, I.lin]
  · intro n h0 x
    simp only [if_pos h0]
    rw [I.ker n h0]
    constructor
    · rintro ⟨y, hy⟩
      exact hg.inj n h0 x y hy
    · rintro ⟨v, rfl⟩
      exact ⟨g n v, map_nsmul (g n) n v⟩
  · intro n h0 q
    simp only [if_pos h0]
    rw [I.onto n h0]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, z, hy⟩ := hg.onto n h0 x
      exact ⟨y, by rw [hy, hadd n h0]⟩
    · rintro ⟨x, hx⟩
      exact ⟨g n x, hx⟩
  · intro n m hn0 hm0 x
    have h0 : 0 < n * m := Nat.mul_pos hn0 hm0
    simp only [if_pos h0, if_pos hn0]
    rw [I.tower n m hn0 hm0]
    obtain ⟨z, hz⟩ := hg.tow n m hn0 hm0 x
    rw [hz, hadd n hn0]
  · intro n h0 x y
    simp only [if_pos h0]
    have h := I.isom n h0 (g n x) (g n y)
    obtain ⟨c, hc⟩ := hg.iso n h0 x y
    have hz : I.ζ n ^ (n : ℤ) = 1 := by
      rw [zpow_natCast]
      exact (I.ζ_prim n h0).pow_eq_one
    have hE : I.ζ n ^ (2 * G.EF (g n x) (g n y)) = I.ζ n ^ (2 * G.EF x y) := by
      have : 2 * G.EF (g n x) (g n y) = 2 * G.EF x y + (n : ℤ) * (2 * c) := by
        linarith [hc]
      rw [this, zpow_add, zpow_mul (I.ζ n) (n : ℤ), hz, one_zpow, mul_one]
    rw [hE] at h
    exact h
  · intro n h0 x
    simp only [if_pos h0]

end UpperTheory.Gal.FiniteEtaleModels.O
end
end

section

open NumberField

namespace UpperTheory.Gal.FiniteEtaleModels.O

private theorem idem_core {A : Type} [CommRing A] (bar : A ≃+* A) (ω : A) (tr nm r : ℤ) (q : ℕ)
    (h1 : ω + bar ω = (tr : A)) (h2 : ω * bar ω = (nm : A))
    (hd : IsCoprime (q : ℤ) (tr ^ 2 - 4 * nm)) (hr : (q : ℤ) ∣ r ^ 2 - tr * r + nm)
    (u : Ideal A) (hu : u = Ideal.span {(q : A), ω - (r : A)}) :
    ∃ ε : ℕ → A, ∀ e : ℕ,
      1 - ε e ∈ u ^ e ∧ bar (ε e) ∈ u ^ e ∧ (∀ x ∈ u ^ e, (q : A) ^ e ∣ ε e * x) ∧
      (q : A) ^ e ∣ ε e + bar (ε e) - 1 ∧ (q : A) ^ e ∣ ε (e + 1) - ε e ∧
      ∀ (𝔞 : Ideal A), (∃ f : ℕ, u ^ f ≤ 𝔞) → (q : A) ^ e ∈ 𝔞 → u ^ e ≤ 𝔞 := by
  classical
  obtain ⟨m, hm⟩ := hr
  obtain ⟨s, t, hst⟩ := hd
  have hmA : (r : A) ^ 2 - (tr : A) * r + nm = (q : A) * m := by
    have := congrArg (fun z : ℤ => (z : A)) hm
    push_cast at this
    exact this
  have hstA : (s : A) * q + t * ((tr : A) ^ 2 - 4 * nm) = 1 := by
    have := congrArg (fun z : ℤ => (z : A)) hst
    push_cast at this
    exact this
  obtain ⟨v, hv⟩ : ∃ v : Ideal A, v = Ideal.span {(q : A), bar ω - (r : A)} := ⟨_, rfl⟩
  have hbb : bar (bar ω) = ω := by
    have := congrArg bar h1
    rw [map_add (f := _), map_intCast] at this
    linear_combination this - h1
  have Mu : Ideal.map bar u = v := by
    rw [hu, hv, Ideal.map_span, Set.image_pair, map_natCast, map_sub, map_intCast]
  have Mv : Ideal.map bar v = u := by
    rw [hu, hv, Ideal.map_span, Set.image_pair, map_natCast, map_sub, map_intCast, hbb]
  have pu : ∀ e, ∀ x ∈ u ^ e, bar x ∈ v ^ e := fun e x hx => by
    rw [← Mu, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem bar hx
  have pv : ∀ e, ∀ x ∈ v ^ e, bar x ∈ u ^ e := fun e x hx => by
    rw [← Mv, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem bar hx
  have hqu : (q : A) ∈ u := hu ▸ Ideal.subset_span (by simp)
  have hwu : ω - (r : A) ∈ u := hu ▸ Ideal.subset_span (by simp)
  have hwv : bar ω - (r : A) ∈ v := hv ▸ Ideal.subset_span (by simp)
  have hsup : u ⊔ v = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have hd' : (tr : A) - 2 * r ∈ u ⊔ v := by
      have := Ideal.add_mem _ (Ideal.mem_sup_left hwu) (Ideal.mem_sup_right hwv)
      convert this using 1
      linear_combination -h1
    have key : (1 : A) = (q : A) * ((s : A) - 4 * t * m) + (t : A) * ((tr : A) - 2 * r) * ((tr : A) - 2 * r) := by
      linear_combination -hstA - 4 * (t : A) * hmA
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_sup_left hqu)) (Ideal.mul_mem_left _ _ hd')
  have hmul : u * v ≤ Ideal.span {(q : A)} := by
    rw [hu, hv, Submodule.mul_le]
    intro x hx y hy
    rw [Ideal.mem_span_pair] at hx hy
    obtain ⟨c, d, rfl⟩ := hx
    obtain ⟨c', d', rfl⟩ := hy
    rw [Ideal.mem_span_singleton']
    refine ⟨c * c' * q + c * d' * (bar ω - r) + d * c' * (ω - r) + d * d' * m, ?_⟩
    linear_combination (-(d * d')) * (h2 - (r : A) * h1 + hmA)
  have hcop : ∀ f e, u ^ f ⊔ v ^ e = ⊤ := fun f e =>
    Ideal.isCoprime_iff_sup_eq.1 (IsCoprime.pow (Ideal.isCoprime_iff_sup_eq.2 hsup))
  have hinf : ∀ e, u ^ e ⊓ v ^ e ≤ Ideal.span {(q : A) ^ e} := fun e => by
    rw [← Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 (hcop e e)), ← mul_pow,
      ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hmul e
  have dv : ∀ e y, y ∈ u ^ e → y ∈ v ^ e → (q : A) ^ e ∣ y := fun e y hy1 hy2 =>
    Ideal.mem_span_singleton.1 (hinf e (Submodule.mem_inf.2 ⟨hy1, hy2⟩))
  have ex : ∀ e, ∃ b, b ∈ v ^ e ∧ 1 - b ∈ u ^ e := fun e => by
    have h1' : (1 : A) ∈ u ^ e ⊔ v ^ e := by rw [hcop e e]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1'
    exact ⟨b, hb, by rw [← hab, add_sub_cancel_right]; exact ha⟩
  choose ε hεv hεu using ex
  refine ⟨ε, fun e => ⟨hεu e, pv e _ (hεv e), ?_, ?_, ?_, ?_⟩⟩
  · intro x hx
    exact dv e _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ (hεv e))
  · apply dv e
    · have h3 := Ideal.sub_mem _ (pv e _ (hεv e)) (hεu e)
      convert h3 using 1
      ring
    · have h3 := Ideal.sub_mem _ (hεv e) (pu e _ (hεu e))
      convert h3 using 1
      rw [map_sub, map_one]
      ring
  · apply dv e
    · have h3 := Ideal.sub_mem _ (hεu e) (Ideal.pow_le_pow_right (Nat.le_succ e) (hεu (e + 1)))
      convert h3 using 1
      ring
    · exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (Nat.le_succ e) (hεv (e + 1))) (hεv e)
  · rintro 𝔞 ⟨f, hf⟩ hq x hx
    have h1' : (1 : A) ∈ u ^ f ⊔ v ^ e := by rw [hcop f e]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1'
    have hx' : x = x * a + x * b := by rw [← mul_add, hab, mul_one]
    rw [hx']
    refine Ideal.add_mem _ (hf (Ideal.mul_mem_left _ _ ha)) ?_
    have h4 := dv e _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ _ hb)
    obtain ⟨c, hc⟩ := h4
    rw [hc]
    exact Ideal.mul_mem_right _ _ hq

end UpperTheory.Gal.FiniteEtaleModels.O

theorem UpperTheory.Gal.FiniteEtaleModels.O.idem :
    UpperTheory.Gal.FiniteEtaleModels.O.Idem := by
  intro q hq D r hr
  have hprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq.out
  exact UpperTheory.Gal.FiniteEtaleModels.O.idem_core D.bar D.ω D.tr D.nm r q D.tr_eq D.nm_eq
    (hprime.coprime_iff_not_dvd.2 D.disc_p) hr _ rfl
end

section

theorem UpperTheory.Gal.FiniteEtaleModels.O.epsEx :
    UpperTheory.Gal.FiniteEtaleModels.O.EpsEx := by
  intro A _ _ _ 𝔟₁ 𝔟₂ a₁ a₂ M₁ M₂ t hpos hM hle h₁ h₂
  unfold UpperTheory.Gal.Int.Geo.IsGen at h₁ h₂
  have hM1 : (M₁ : A) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hMc : (M₁ : A) = (t : A) * (M₂ : A) := by rw [hM]; push_cast; ring
  set I₁ := Ideal.span {a₁} ⊔ Ideal.span {(M₁ : A)} with hI₁
  have hI₁0 : I₁ ≠ ⊥ := by
    intro h
    have hmem : (M₁ : A) ∈ I₁ := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [h, Ideal.mem_bot] at hmem
    exact hM1 hmem
  have h𝔟0 : 𝔟₁ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    exact hM1 h₁
  have hkey : ∀ {J : Ideal A}, J * 𝔟₂ ≤ Ideal.span {(M₁ : A)} → J ≤ I₁ := by
    intro J hJ
    have h3 : J * 𝔟₁ ≤ I₁ * 𝔟₁ := by
      rw [h₁]
      exact le_trans (Ideal.mul_mono_right hle) hJ
    rw [← Ideal.dvd_iff_le] at h3 ⊢
    exact (mul_dvd_mul_iff_right h𝔟0).mp h3
  have hta : (t : A) * a₂ ∈ I₁ := by
    have hsp : Ideal.span {(t : A) * a₂} ≤ I₁ := by
      apply hkey
      rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc, hMc,
        ← Ideal.span_singleton_mul_span_singleton, ← h₂]
      exact Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_left)
    exact hsp (Ideal.mem_span_singleton_self _)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hta
  obtain ⟨ε, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨ε, ⟨-d, by rw [← hyz]; ring⟩, ?_⟩
  have hJK : I₁ * Ideal.span {ε} ⊔ Ideal.span {(M₁ : A)} =
      Ideal.span {(t : A)} * (Ideal.span {a₂} ⊔ Ideal.span {(M₂ : A)}) := by
    rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton, ← hMc, hI₁, Ideal.sup_mul,
      Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) le_sup_right
      · rw [Ideal.span_singleton_le_iff_mem]
        have hae : a₁ * ε = (t : A) * a₂ - d * M₁ := by rw [← hyz]; ring
        rw [hae]
        exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      · rw [Ideal.span_singleton_le_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · refine sup_le ?_ le_sup_right
      rw [Ideal.span_singleton_le_iff_mem, ← hyz]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_sup_left ?_))
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      rw [mul_comm]
      exact Ideal.mem_span_singleton_self _
  apply mul_left_cancel₀ hI₁0
  rw [h₁, ← mul_assoc, Ideal.mul_sup, h₁, hJK, mul_assoc, h₂,
    Ideal.span_singleton_mul_span_singleton, ← hMc]
end

section

set_option autoImplicit false

namespace UpperTheory.Gal.FiniteEtaleModels.O.LU

private theorem exists_sep {A : Type} [CommRing A] [IsDedekindDomain A] (u 𝔞 : Ideal A) (hu : u ≠ ⊥) :
    ∃ s t : A, s ∈ 𝔞 ∧ s + t = 1 ∧ ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → u ≤ 𝔪 → ¬ 𝔞 ≤ 𝔪 → t ∈ 𝔪 := by
  classical
  have hfin := Ideal.finite_factors (R := A) hu
  let S := hfin.toFinset.filter (fun v => ¬ 𝔞 ≤ v.asIdeal)
  have hc : IsCoprime 𝔞 (∏ v ∈ S, v.asIdeal) := by
    apply IsCoprime.prod_right
    intro v hv
    have hm : v.asIdeal.IsMaximal := v.isMaximal
    rw [Ideal.isCoprime_iff_sup_eq]
    exact hm.out.2 _ (right_lt_sup.2 (Finset.mem_filter.1 hv).2)
  obtain ⟨s, hs, t, ht, hst⟩ := Ideal.isCoprime_iff_exists.1 hc
  refine ⟨s, t, hs, hst, fun 𝔪 hm hum ha => ?_⟩
  have hne : 𝔪 ≠ ⊥ := fun h => hu (le_bot_iff.1 (h ▸ hum))
  let v : IsDedekindDomain.HeightOneSpectrum A := ⟨𝔪, hm.isPrime, hne⟩
  have hv : v ∈ S := by
    refine Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ?_, ha⟩
    exact Ideal.dvd_iff_le.2 hum
  exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun v : IsDedekindDomain.HeightOneSpectrum A => v.asIdeal) hv) ht

private theorem sup_range_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (g : M →ₗ[A] M) (u : Ideal A)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → u ≤ 𝔪 → LinearMap.range g ⊔ (𝔪 • ⊤ : Submodule A M) = ⊤) (e : ℕ) :
    LinearMap.range g ⊔ (u ^ e • ⊤ : Submodule A M) = ⊤ := by
  set R := LinearMap.range g with hR
  let I : Ideal A := Module.annihilator A (M ⧸ R)
  have hIu : I ⊔ u ^ e = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hum : u ≤ 𝔪 := hm.isPrime.le_of_pow_le (le_sup_right.trans hle)
    have hQ : (⊤ : Submodule A (M ⧸ R)) ≤ 𝔪 • ⊤ := by
      intro y _
      obtain ⟨x, rfl⟩ := R.mkQ_surjective y
      have hx : x ∈ R ⊔ (𝔪 • ⊤ : Submodule A M) := by rw [h 𝔪 hm hum]; trivial
      obtain ⟨r, hr, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      have h1 : R.mkQ (r + z) = R.mkQ z := by
        rw [map_add (f := _), show R.mkQ r = 0 from (Submodule.Quotient.mk_eq_zero R).2 hr, zero_add]
      rw [h1]
      have h2 := Submodule.mem_map_of_mem (f := R.mkQ) hz
      rw [Submodule.map_smul''] at h2
      simpa using h2
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 ⊤
      Module.Finite.fg_top hQ
    have hrI : r ∈ I := Module.mem_annihilator.2 fun y => hr y trivial
    have hrm : r ∈ 𝔪 := hle (Ideal.mem_sup_left hrI)
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hrm hr1))
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hIu ▸ (Submodule.mem_top : (1 : A) ∈ ⊤))
  have h1 : a • x ∈ R := by
    have : a • R.mkQ x = 0 := Module.mem_annihilator.1 ha _
    rw [← map_smul] at this
    exact (Submodule.Quotient.mk_eq_zero R).1 this
  have h2 : b • x ∈ (u ^ e • ⊤ : Submodule A M) := Submodule.smul_mem_smul hb trivial
  have h3 : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
  rw [h3]
  exact Submodule.add_mem_sup h1 h2

private theorem exists_inv {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] (g : M →ₗ[A] M) (J : Ideal A)
    (h : LinearMap.range g ⊔ (J • ⊤ : Submodule A M) = ⊤) :
    ∃ k : M →ₗ[A] M, ∀ x, g (k x) - x ∈ (J • ⊤ : Submodule A M) ∧ k (g x) - x ∈ (J • ⊤ : Submodule A M) := by
  set P : Submodule A M := J • ⊤ with hP
  have hs : Function.Surjective (P.mkQ ∘ₗ g) := by
    intro y
    obtain ⟨x, rfl⟩ := P.mkQ_surjective y
    have hx : x ∈ LinearMap.range g ⊔ P := by rw [h]; trivial
    obtain ⟨r, ⟨a, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨a, ?_⟩
    simp [(Submodule.Quotient.mk_eq_zero P).2 hz]
  obtain ⟨k, hk⟩ := Module.projective_lifting_property (P.mkQ ∘ₗ g) P.mkQ hs
  have hk' : ∀ x, P.mkQ (g (k x)) = P.mkQ x := fun x => LinearMap.congr_fun hk x
  have hle : P ≤ P.comap g := by
    intro x hx
    have h1 := Submodule.mem_map_of_mem (f := g) hx
    rw [hP, Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1
  let gb : (M ⧸ P) →ₗ[A] (M ⧸ P) := P.mapQ P g hle
  have hgb : ∀ x, gb (P.mkQ x) = P.mkQ (g x) := fun x => rfl
  have hsb : Function.Surjective gb := by
    intro y
    obtain ⟨z, hz⟩ := hs y
    exact ⟨P.mkQ z, by rw [hgb]; exact hz⟩
  have hib : Function.Injective gb := OrzechProperty.injective_of_surjective_endomorphism gb hsb
  refine ⟨k, fun x => ⟨?_, ?_⟩⟩
  · exact (Submodule.Quotient.eq P).1 (hk' x)
  · refine (Submodule.Quotient.eq P).1 (hib ?_)
    change gb (P.mkQ _) = gb (P.mkQ _)
    rw [hgb, hgb, hk']

end UpperTheory.Gal.FiniteEtaleModels.O.LU

open UpperTheory.Gal.FiniteEtaleModels.O.LU in
theorem UpperTheory.Gal.FiniteEtaleModels.O.liftUnit :
    UpperTheory.Gal.FiniteEtaleModels.O.LiftUnit := by
  intro A M _ _ _ _ _ _ u 𝔞 hu _
  set N : Submodule A M := 𝔞 • ⊤ with hN
  intro g₀
  obtain ⟨g', hg'⟩ := Module.projective_lifting_property N.mkQ (g₀.toLinearMap ∘ₗ N.mkQ) N.mkQ_surjective
  obtain ⟨s, t, hs, hst, ht⟩ := exists_sep u 𝔞 hu
  let g : M →ₗ[A] M := t • g' + s • LinearMap.id
  have hgv : ∀ x, g x = t • g' x + s • x := fun x => rfl
  have ht1 : t = 1 - s := by rw [← hst]; ring
  have hs1 : s = 1 - t := by rw [← hst]; ring
  have hgg' : ∀ x, g x - g' x ∈ N := fun x => by
    have h1 : g x - g' x = s • (x - g' x) := by
      rw [hgv, ht1, sub_smul, one_smul, smul_sub]; abel
    rw [h1]
    exact Submodule.smul_mem_smul hs trivial
  have hlift : ∀ x, N.mkQ (g x) = g₀ (N.mkQ x) := fun x => by
    have h1 : N.mkQ (g x) = N.mkQ (g' x) := (Submodule.Quotient.eq N).2 (hgg' x)
    rw [h1]
    exact LinearMap.congr_fun hg' x
  have hmax : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → u ≤ 𝔪 →
      LinearMap.range g ⊔ (𝔪 • ⊤ : Submodule A M) = ⊤ := by
    intro 𝔪 hm hum
    rw [eq_top_iff]
    intro x _
    by_cases ha : 𝔞 ≤ 𝔪
    · obtain ⟨y, hy⟩ := g₀.surjective (N.mkQ x)
      obtain ⟨y, rfl⟩ := N.mkQ_surjective y
      have h1 : x - g y ∈ N := (Submodule.Quotient.eq N).1 (show N.mkQ x = N.mkQ (g y) by rw [hlift, hy])
      have h2 : x - g y ∈ (𝔪 • ⊤ : Submodule A M) := Submodule.smul_mono_left ha h1
      have h3 := Submodule.add_mem_sup (LinearMap.mem_range_self g y) h2
      simpa using h3
    · have htm := ht 𝔪 hm hum ha
      have h1 : x - g x = t • (x - g' x) := by
        rw [hgv, hs1, sub_smul, one_smul, smul_sub]; abel
      have h2 : x - g x ∈ (𝔪 • ⊤ : Submodule A M) := by
        rw [h1]
        exact Submodule.smul_mem_smul htm trivial
      have h3 := Submodule.add_mem_sup (LinearMap.mem_range_self g x) h2
      simpa using h3
  choose h hh using fun e => exists_inv g (u ^ e) (sup_range_pow g u hmax e)
  exact ⟨g, h, hlift, fun e x => hh e x⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem ev_nsmul {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n c : ℕ) (x : G.La) :
    I.ev n (c • x) = I.ev n x ^ c := by
  induction c with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have h := I.add n 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  | succ c ih =>
    rw [succ_nsmul, I.add, ih, pow_succ]

theorem UpperTheory.Gal.FiniteEtaleModels.etaPtB_holds :
    EtaPtB := by
  unfold UpperTheory.Gal.FiniteEtaleModels.EtaPtB
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT Ω _ _ z x y hv
  unfold UpperTheory.Gal.Int.Geo.IsTrans at hT
  obtain ⟨-, -, -, -, hgeo⟩ := hT
  obtain ⟨I', I'', h1, h2, hiff⟩ := hgeo Ω z (Spec.preimage (z ≫ s)).hom (by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage])
  have hN' : 0 < (N' : ℕ) := by
    have := N'.2.1
    omega
  have hN : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  have key := (hiff _ (Nat.mul_pos hN' hN) (Nat.Coprime.mul_left N'.2.2 N.2.2)
    ((N : ℕ) • x) ((N' : ℕ) • y)).2 hv
  have ex : I'.ev ((N' : ℕ) * N) ((N : ℕ) • x) = I'.ev N' x := by
    have t1 := I'.tower (N' : ℕ) N hN' hN x
    have t2 := ev_nsmul I' ((N' : ℕ) * N) N x
    exact t2.trans t1
  have ey : I''.ev ((N' : ℕ) * N) ((N' : ℕ) • y) = I''.ev N y := by
    have t1 := I''.tower (N : ℕ) N' hN hN' y
    have t2 := ev_nsmul I'' ((N' : ℕ) * N) N' y
    rw [mul_comm] at t1
    exact t2.trans t1
  have key2 := (ex ▸ ey ▸ key : I'.ev N' x ≫ ψ = I''.ev N y)
  have e1 := h1 x
  have e2 := h2 y
  rw [← Category.assoc]
  exact (congrArg (fun f => f ≫ ψ) e1).trans (key2.trans e2.symm)
end
