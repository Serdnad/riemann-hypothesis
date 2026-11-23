module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.LocAic

theorem mem_of_compare {A : Type} [CommRing A] {e f : A}
    (h1 : e * (1 - f) ∈ Ideal.span {f}) (h2 : (1 - e) * f ∈ Ideal.span {1 - f}) :
    e ∈ Ideal.span {f} ∧ 1 - e ∈ Ideal.span {1 - f} := by
  constructor
  · have hsplit : e = e * (1 - f) + e * f := by ring
    rw [hsplit]
    exact Ideal.add_mem _ h1 (Ideal.mul_mem_left _ e (Ideal.mem_span_singleton_self f))
  · have hsplit : 1 - e = (1 - e) * f + (1 - e) * (1 - f) := by ring
    rw [hsplit]
    exact Ideal.add_mem _ h2 (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem local_of_val {S : Type} [CommRing S] (π : S) (hV : Val π) (f : S) :
    ∃ e : S, IsIdempotentElem e ∧ e ∈ Ideal.span {f} ∧ 1 - e ∈ Ideal.span {1 - f} := by
  have hV' : ∀ f g : S, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
      ∃ e, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f} := hV
  obtain ⟨e, he, h1, h2⟩ := hV' f (1 - f) ⟨0, by
    rw [pow_zero, Ideal.mem_span_pair]
    exact ⟨1, 1, by ring⟩⟩
  refine ⟨1 - e, he.one_sub, mem_of_compare h2 ?_⟩
  rw [sub_sub_cancel]
  exact h1

theorem local_away_of_val {S : Type} [CommRing S] (π : S) (hV : Val π) (f : Localization.Away π) :
    ∃ e : Localization.Away π, IsIdempotentElem e ∧ e ∈ Ideal.span {f} ∧ 1 - e ∈ Ideal.span {1 - f} := by
  have hV' : ∀ f g : S, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
      ∃ e, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f} := hV
  obtain ⟨⟨a, s⟩, hf⟩ := IsLocalization.surj (Submonoid.powers π) f
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
  have hu : IsUnit (algebraMap S (Localization.Away π) (s : S)) :=
    IsLocalization.map_units (Localization.Away π) s
  have hA : algebraMap S (Localization.Away π) a = f * algebraMap S (Localization.Away π) (s : S) := hf.symm
  have hB : algebraMap S (Localization.Away π) ((s : S) - a) =
      (1 - f) * algebraMap S (Localization.Away π) (s : S) := by
    rw [map_sub, hA]
    ring
  obtain ⟨e, he, h1, h2⟩ := hV' a ((s : S) - a) ⟨n, by
    rw [hn, Ideal.mem_span_pair]
    exact ⟨1, 1, by ring⟩⟩
  have d1 : (1 - f) ∣ algebraMap S (Localization.Away π) e * f := by
    have hd := map_dvd (algebraMap S (Localization.Away π)) (Ideal.mem_span_singleton.1 h1)
    rw [hB, map_mul, hA, ← mul_assoc] at hd
    exact hu.dvd_mul_right.1 (dvd_trans (dvd_mul_right _ _) hd)
  have d2 : f ∣ (1 - algebraMap S (Localization.Away π) e) * (1 - f) := by
    have hd := map_dvd (algebraMap S (Localization.Away π)) (Ideal.mem_span_singleton.1 h2)
    rw [map_mul, hB, map_sub, map_one, hA, ← mul_assoc] at hd
    exact hu.dvd_mul_right.1 (dvd_trans (dvd_mul_right _ _) hd)
  have hē : IsIdempotentElem (algebraMap S (Localization.Away π) e) := by
    rw [IsIdempotentElem, ← map_mul, he.eq]
  refine ⟨1 - algebraMap S (Localization.Away π) e, hē.one_sub,
    mem_of_compare (Ideal.mem_span_singleton.2 d2) ?_⟩
  rw [sub_sub_cancel]
  exact Ideal.mem_span_singleton.2 d1


open Polynomial in
theorem aic_away {S : Type} [CommRing S] (π : S) (hA : Aic (S := S)) :
    Aic (S := Localization.Away π) := by
  have hA' : ∀ P : Polynomial S, P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x := hA
  unfold Aic
  intro P hP hdeg
  have hlift := IsLocalization.scaleRoots_commonDenom_mem_lifts (M := Submonoid.powers π)
    (Rₘ := Localization.Away π) P (by rw [hP.leadingCoeff]; exact ⟨1, map_one _⟩)
  obtain ⟨q, hq, hqdeg, hqm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift ((Polynomial.monic_scaleRoots_iff _).2 hP)
  obtain ⟨y, hy⟩ := hA' q hqm (by rw [hqdeg, Polynomial.natDegree_scaleRoots]; exact hdeg)
  have hs : IsUnit (algebraMap S (Localization.Away π)
      (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S)) :=
    IsLocalization.map_units (Localization.Away π) _
  refine ⟨↑hs.unit⁻¹ * algebraMap S (Localization.Away π) y, ?_⟩
  have h1 := Polynomial.scaleRoots_eval₂_mul (p := P) (RingHom.id (Localization.Away π))
    (↑hs.unit⁻¹ * algebraMap S (Localization.Away π) y)
    (algebraMap S (Localization.Away π) (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S))
  simp only [RingHom.id_apply] at h1
  rw [← mul_assoc, hs.mul_val_inv, one_mul] at h1
  have h3 : Polynomial.eval₂ (RingHom.id _) (algebraMap S (Localization.Away π) y)
      (P.scaleRoots (algebraMap S (Localization.Away π)
        (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S))) = 0 := by
    rw [← hq, Polynomial.eval₂_map, RingHom.id_comp, Polynomial.eval₂_hom]
    rw [show q.eval y = 0 from hy, map_zero]
  rw [h3] at h1
  exact (hs.pow _).mul_right_eq_zero.1 h1.symm

theorem main : ∀ {S : Type} [CommRing S] (ϖ : S),
    (Val ϖ → Loc (S := S) ∧ Loc (S := Localization.Away ϖ)) ∧
      (Aic (S := S) → Aic (S := Localization.Away ϖ)) := by
  intro S _ ϖ
  refine ⟨fun hV => ⟨?_, ?_⟩, fun hA => aic_away ϖ hA⟩
  · unfold Loc
    exact fun f => local_of_val ϖ hV f
  · unfold Loc
    exact fun f => local_away_of_val ϖ hV f

end GlobalTheory.CompanionTheory.LocAic
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdTF

theorem natCast_mul_cancel {S : Type} [CommRing S] (hS : TF (S := S)) {n : ℕ} (hn : n ≠ 0) {a b : S}
    (e : (n : S) * a = (n : S) * b) : a = b := by
  have h0 : (n : S) * (a - b) = 0 := by rw [mul_sub, e, sub_self]
  have := (mem_nonZeroDivisors_iff.mp (hS n hn)).1 _ h0
  exact sub_eq_zero.mp this

theorem exists_dividedPowers {S : Type} [CommRing S] (hS : TF (S := S)) (I : Ideal S) (hI : PdI I) :
    ∃ δ : DividedPowers I, IsPd (RingHom.id S) I δ := by
  classical
  have ex : ∀ (k : ℕ) (x : S), ∃ y : S,
      (x ∈ I → (k.factorial : S) * y = x ^ k ∧ (k ≠ 0 → y ∈ I)) ∧ (x ∉ I → y = 0) := by
    intro k x
    by_cases hx : x ∈ I
    · by_cases hk : k = 0
      · subst hk
        exact ⟨1, fun _ => ⟨by simp, fun h => absurd rfl h⟩, fun h => absurd hx h⟩
      · obtain ⟨y, hy, e⟩ := hI x hx k hk
        exact ⟨y, fun _ => ⟨e, fun _ => hy⟩, fun h => absurd hx h⟩
    · exact ⟨0, fun h => absurd h hx, fun _ => rfl⟩
  choose d hd using ex
  have spec : ∀ (k : ℕ) {x : S}, x ∈ I → (k.factorial : S) * d k x = x ^ k :=
    fun k x hx => ((hd k x).1 hx).1
  have hmem : ∀ {k : ℕ} {x : S}, k ≠ 0 → x ∈ I → d k x ∈ I :=
    fun {k x} hk hx => ((hd k x).1 hx).2 hk
  have fne : ∀ k : ℕ, k.factorial ≠ 0 := Nat.factorial_ne_zero
  refine ⟨{ dpow := d
            dpow_null := fun {n x} hx => (hd n x).2 hx
            dpow_zero := fun {x} hx => ?_
            dpow_one := fun {x} hx => ?_
            dpow_mem := fun {n x} hn hx => hmem hn hx
            dpow_add := fun {n x y} hx hy => ?_
            dpow_mul := fun {n a x} hx => ?_
            mul_dpow := fun {m n x} hx => ?_
            dpow_comp := fun {m n x} hn hx => ?_ }, (Ideal.map_id I).symm, ?_⟩
  · have := spec 0 hx
    simpa using this
  · have := spec 1 hx
    simpa using this
  · apply natCast_mul_cancel hS (fne n)
    rw [spec n (I.add_mem hx hy), (Commute.all x y).add_pow', Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨i, j⟩ := p
    have hij : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    subst hij
    have hf : (((i + j).factorial : ℕ) : S)
        = ((i + j).choose i : S) * (i.factorial : S) * (j.factorial : S) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
      push_cast
      ring
    simp only
    rw [hf, nsmul_eq_mul, ← spec i hx, ← spec j hy]
    ring
  · apply natCast_mul_cancel hS (fne n)
    rw [spec n (I.mul_mem_left a hx), mul_pow, ← spec n hx]
    ring
  · apply natCast_mul_cancel hS (Nat.mul_ne_zero (fne m) (fne n))
    have hf : (((m + n).factorial : ℕ) : S)
        = ((m + n).choose m : S) * (m.factorial : S) * (n.factorial : S) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
      push_cast
      ring
    have h1 : ((m.factorial * n.factorial : ℕ) : S) * (d m x * d n x) = x ^ (m + n) := by
      push_cast
      rw [pow_add, ← spec m hx, ← spec n hx]
      ring
    have h2 : ((m.factorial * n.factorial : ℕ) : S) * (((m + n).choose m : S) * d (m + n) x)
        = x ^ (m + n) := by
      rw [← spec (m + n) hx, hf]
      push_cast
      ring
    rw [h1, h2]
  · by_cases hm : m = 0
    · subst hm
      have h0 := spec 0 (hmem hn hx)
      have h1 := spec 0 hx
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero] at h0 h1
      simp [h0, h1, Nat.uniformBell_zero_left]
    · apply natCast_mul_cancel hS (Nat.mul_ne_zero (fne m) (pow_ne_zero m (fne n)))
      have hdx : d n x ∈ I := hmem hn hx
      have hb : ((Nat.uniformBell m n : ℕ) : S) * ((n.factorial : S) ^ m) * (m.factorial : S)
          = ((m * n).factorial : S) := by
        rw [← Nat.uniformBell_mul_eq _ hn]
        push_cast
        ring
      have h1 : ((m.factorial * n.factorial ^ m : ℕ) : S) * d m (d n x) = x ^ (m * n) := by
        push_cast
        calc (m.factorial : S) * (n.factorial : S) ^ m * d m (d n x)
            = (n.factorial : S) ^ m * ((m.factorial : S) * d m (d n x)) := by ring
          _ = ((n.factorial : S) * d n x) ^ m := by rw [spec m hdx, mul_pow]
          _ = x ^ (m * n) := by rw [spec n hx, ← pow_mul, mul_comm]
      have h2 : ((m.factorial * n.factorial ^ m : ℕ) : S)
          * (((Nat.uniformBell m n : ℕ) : S) * d (m * n) x) = x ^ (m * n) := by
        rw [← spec (m * n) hx, ← hb]
        push_cast
        ring
      rw [h1, h2]
  · intro k x y hx e
    apply natCast_mul_cancel hS (fne k)
    simp only [RingHom.id_apply]
    rw [spec k hx, e]

end GlobalTheory.CompanionTheory.PdTF
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonSlope

theorem exists_dvd_all {S ι : Type} [CommRing S] (T : Finset ι) (hT : T.Nonempty) (r : ι → S)
    (hc : ∀ i ∈ T, ∀ j ∈ T, r i ∣ r j ∨ r j ∣ r i) :
    ∃ i₀ ∈ T, ∀ j ∈ T, r j ∣ r i₀ := by
  classical
  revert hT hc
  refine Finset.induction_on T ?_ ?_
  · intro hT
    exact absurd hT Finset.not_nonempty_empty
  · intro a s ha ih hT hc
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨a, Finset.mem_insert_self a ∅, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact dvd_refl _
      · exact absurd hj (Finset.notMem_empty j)
    · obtain ⟨i₀, hi₀, hmax⟩ := ih hs (fun i hi j hj =>
        hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      rcases hc a (Finset.mem_insert_self a s) i₀ (Finset.mem_insert_of_mem hi₀) with h | h
      · refine ⟨i₀, Finset.mem_insert_of_mem hi₀, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact h
        · exact hmax j hj
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact dvd_refl _
        · exact (hmax j hj).trans h

theorem dich_of_dvd {S : Type} [CommRing S] {ϖ : S} (hD : Dich ϖ) {a b : S} {M : ℕ}
    (h : a ∣ ϖ ^ M) : b ∣ a ∨ a ∣ b := by
  obtain ⟨k, hk⟩ := h
  refine hD a b ⟨M, ?_⟩
  rw [hk]
  exact Ideal.mul_mem_right k _ (Ideal.subset_span (by simp))

theorem first_slope : ∀ {S : Type} [CommRing S] (ϖ : S), Dich ϖ → Roots ϖ → ∀ (q : ℕ → S) (d M : ℕ),
    0 < d → q d = 1 → q 0 ∣ ϖ ^ M → ∃ c : S, (∀ i, 1 ≤ i → i ≤ d → q 0 ∣ q i * c ^ i) ∧
      ∃ i, 1 ≤ i ∧ i ≤ d ∧ q i * c ^ i ∣ q 0 := by
  intro S _ ϖ hD hR q d M hd hqd h0
  classical
  have hex : ∀ j : ℕ, ∃ s : S, (1 ≤ j → q j ∣ q 0 → ∃ u : Sˣ, q 0 = q j * (↑u * s ^ j)) := by
    intro j
    by_cases hj : 1 ≤ j ∧ q j ∣ q 0
    · obtain ⟨t, ht⟩ := hj.2
      have htd : t ∣ ϖ ^ M := (Dvd.intro_left (q j) ht.symm).trans h0
      obtain ⟨r, u, hru⟩ := hR t M j htd (by omega)
      exact ⟨r, fun _ _ => ⟨u, by rw [ht, hru]⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose s hs using hex
  set T := (Finset.Icc 1 d).filter (fun j => q j ∣ q 0) with hTdef
  have hmemT : ∀ j, j ∈ T ↔ (1 ≤ j ∧ j ≤ d) ∧ q j ∣ q 0 := by
    intro j
    rw [hTdef, Finset.mem_filter, Finset.mem_Icc]
  have hdT : d ∈ T := (hmemT d).mpr ⟨⟨hd, le_refl d⟩, by rw [hqd]; exact one_dvd _⟩
  have hsdvd : ∀ j ∈ T, s j ∣ ϖ ^ M := by
    intro j hj
    obtain ⟨⟨hj1, _⟩, hjq⟩ := (hmemT j).mp hj
    obtain ⟨u, hu⟩ := hs j hj1 hjq
    have h1 : s j ^ j ∣ q 0 := ⟨q j * ↑u, by rw [hu]; ring⟩
    exact ((dvd_pow_self (s j) (by omega)).trans h1).trans h0
  have hcomp : ∀ i ∈ T, ∀ j ∈ T, s i ∣ s j ∨ s j ∣ s i := by
    intro i hi j _
    exact (dich_of_dvd hD (b := s j) (hsdvd i hi)).symm
  obtain ⟨i₀, hi₀T, hmax⟩ := exists_dvd_all T ⟨d, hdT⟩ s hcomp
  obtain ⟨⟨hi₀1, hi₀d⟩, hi₀q⟩ := (hmemT i₀).mp hi₀T
  refine ⟨s i₀, ?_, i₀, hi₀1, hi₀d, ?_⟩
  · intro i hi1 hid
    rcases dich_of_dvd hD (b := q i) h0 with h | h
    · have hiT : i ∈ T := (hmemT i).mpr ⟨⟨hi1, hid⟩, h⟩
      obtain ⟨u, hu⟩ := hs i hi1 h
      have h2 : q 0 ∣ q i * s i ^ i := by
        rw [hu, mul_left_comm, Units.mul_left_dvd]
      obtain ⟨k, hk⟩ := hmax i hiT
      exact h2.trans ⟨k ^ i, by rw [hk, mul_pow]; ring⟩
    · exact dvd_mul_of_dvd_left h _
  · obtain ⟨u, hu⟩ := hs i₀ hi₀1 hi₀q
    exact ⟨↑u, by rw [hu]; ring⟩

end GlobalTheory.CompanionTheory.NewtonSlope
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.SecRules

theorem secOn_zero {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)) :
    SecOn f 0 := by
  haveI : Subsingleton (Localization.Away (0 : S)) :=
    IsLocalization.subsingleton (M := Submonoid.powers (0 : S)) (Submonoid.mem_powers 0)
  haveI : IsEmpty (Spec (CommRingCat.of (Localization.Away (0 : S)))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (Localization.Away (0 : S))))
  exact ⟨isInitialOfIsEmpty.to Y, isInitialOfIsEmpty.hom_ext _ _⟩

theorem secOn_mul {S : Type} [CommRing S] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of S)}
    (e e' : S) (h : SecOn f e) : SecOn f (e * e') := by
  obtain ⟨s, hs⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away e) (P := Localization.Away (e * e')) e e')) ≫ s, ?_⟩
  rw [Category.assoc, hs, ← Spec.map_comp]
  congr 1
  ext a
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom]
  exact IsLocalization.Away.awayToAwayRight_eq e e' a

theorem section_of_secOn_one {S : Type} [CommRing S] {Y : Scheme.{0}}
    {f : Y ⟶ Spec (CommRingCat.of S)} (h : SecOn f 1) :
    ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _ := by
  obtain ⟨s, hs⟩ := h
  let eqv := IsLocalization.atUnit S (Localization.Away (1 : S)) 1 isUnit_one
  refine ⟨Spec.map (CommRingCat.ofHom (eqv.symm : Localization.Away (1 : S) →+* S)) ≫ s, ?_⟩
  rw [Category.assoc, hs, ← Spec.map_comp]
  have hid : CommRingCat.ofHom (Algebra.algebraMap S (Localization.Away (1 : S))) ≫
      CommRingCat.ofHom (eqv.symm : Localization.Away (1 : S) →+* S) = 𝟙 _ := by
    ext a
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, CommRingCat.id_apply]
    exact eqv.symm.commutes a
  rw [hid, Spec.map_id]

theorem main : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)),
    SecOn f 0 ∧ (∀ e e' : S, SecOn f e → SecOn f (e * e')) ∧
      (SecOn f 1 → ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _) := by
  intro S _ Y f
  exact ⟨secOn_zero Y f, fun e e' h => secOn_mul e e' h, section_of_secOn_one⟩

end GlobalTheory.CompanionTheory.SecRules
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValQuot

theorem valuation_comparable_quotient : ∀ {S : Type} [CommRing S] (π : S), Val π → Val0 (S := S ⧸ Ideal.span {π}) := by
  intro S _ π hV f' g'
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f'
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g'
  have hpi : ∀ x : S, ∃ N : ℕ, π ^ N ∈ Ideal.span {x, π} := fun x =>
    ⟨1, Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩⟩
  obtain ⟨e₁, he1, h1f, h1π⟩ := hV f π (hpi f)
  obtain ⟨e₂, he2, h2g, h2π⟩ := hV g π (hpi g)
  obtain ⟨a1, ha1⟩ := Ideal.mem_span_singleton'.mp h1f
  obtain ⟨b1, hb1⟩ := Ideal.mem_span_singleton'.mp h1π
  obtain ⟨a2, ha2⟩ := Ideal.mem_span_singleton'.mp h2g
  have he1' : e₁ * e₁ = e₁ := he1
  have he2' : e₂ * e₂ = e₂ := he2
  obtain ⟨u, hu⟩ : ∃ u : S, u = (1 - e₁) * (1 - e₂) := ⟨_, rfl⟩
  have hu2 : u * u = u := by subst hu; linear_combination (1 - e₂) ^ 2 * he1' + (1 - e₁) * he2'
  have he1u : e₁ * u = 0 := by subst hu; linear_combination (-(1 - e₂)) * he1'
  have huπ : u * π = (1 - e₂) * b1 * f := by subst hu; linear_combination (-(1 - e₂)) * hb1
  obtain ⟨e₃, he3, h3, h3'⟩ := hV (u * f + (1 - u)) (u * g + (1 - u))
    ⟨1, Ideal.mem_span_pair.mpr ⟨(1 - e₂) * b1 * u + π * (1 - u), 0, by
      linear_combination ((1 - e₂) * b1 * f - (1 - e₂) * b1 - π * f + 2 * π) * hu2 - u * huπ⟩⟩
  have he3' : e₃ * e₃ = e₃ := he3
  obtain ⟨c3, hc3⟩ := Ideal.mem_span_singleton'.mp h3
  obtain ⟨d3, hd3⟩ := Ideal.mem_span_singleton'.mp h3'
  refine ⟨Ideal.Quotient.mk _ (e₁ + u * e₃), ?_, ?_, ?_⟩
  · show Ideal.Quotient.mk _ (e₁ + u * e₃) * Ideal.Quotient.mk _ (e₁ + u * e₃) =
      Ideal.Quotient.mk _ (e₁ + u * e₃)
    rw [← map_mul]
    exact congrArg (Ideal.Quotient.mk _)
      (by linear_combination he1' + 2 * e₃ * he1u + e₃ ^ 2 * hu2 + u * he3')
  · refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (c3 * u), ?_⟩
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨-a1, by linear_combination -ha1 - u * hc3 + (c3 * g - c3 - e₃ * f + e₃) * hu2⟩
  · refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (d3 * u), ?_⟩
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {π})), ← map_sub, ← map_mul, ← map_mul, Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-((1 - e₁) * a2), by
      linear_combination -(1 - e₁) * ha2 - g * hu - u * hd3 + (d3 * f - d3 - (1 - e₃) * g + (1 - e₃)) * hu2⟩

end GlobalTheory.CompanionTheory.ValQuot
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.MonicSplit

open Polynomial

theorem exists_multiset_of_natDegree_eq {S : Type} [CommRing S] (hS : Aic (S := S)) (d : ℕ) :
    ∀ P : Polynomial S, P.Monic → P.natDegree = d →
      ∃ s : Multiset S, P = (s.map fun b => X - C b).prod := by
  rcases subsingleton_or_nontrivial S with hS' | hS'
  · intro P _ _
    exact ⟨0, Subsingleton.elim _ _⟩
  · induction d with
    | zero =>
      intro P hP hd
      refine ⟨0, ?_⟩
      rw [Multiset.map_zero, Multiset.prod_zero]
      exact Polynomial.eq_one_of_monic_natDegree_zero hP hd
    | succ d ih =>
      intro P hP hd
      obtain ⟨x, hx⟩ := hS P hP (by omega)
      have hmul : (X - C x) * (P /ₘ (X - C x)) = P := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hx
      have hQ : (P /ₘ (X - C x)).Monic :=
        Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C x) (by rw [hmul]; exact hP)
      have hQd : (P /ₘ (X - C x)).natDegree = d := by
        have h := (Polynomial.monic_X_sub_C x).natDegree_mul hQ
        rw [hmul, Polynomial.natDegree_X_sub_C, hd] at h
        omega
      obtain ⟨s, hs⟩ := ih _ hQ hQd
      refine ⟨x ::ₘ s, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

theorem monic_splits : ∀ {S : Type} [CommRing S], Aic (S := S) → ∀ P : Polynomial S, P.Monic →
    ∃ s : Multiset S, P = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro S _ hS P hP
  exact exists_multiset_of_natDegree_eq hS _ P hP rfl

end GlobalTheory.CompanionTheory.MonicSplit
end
