module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.LinearAlgebra.Span.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Coeff
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Algebra.CharP.Lemmas

@[expose] public section

section

universe u

theorem UpperTheory.pseudo_division :
    ∀ (R : Type u) [CommRing R] (g p : Polynomial R), g ≠ 0 → ∃ (k : ℕ) (q r : Polynomial R), Polynomial.C (g.leadingCoeff ^ k) * p = g * q + r ∧ r.degree < g.degree := by
  intro R _ g p hg
  induction p using (Polynomial.degree_lt_wf (R := R)).induction with
  | _ p ih =>
    by_cases h : p.degree < g.degree
    · exact ⟨0, 0, p, by simp, h⟩
    · have hle : g.degree ≤ p.degree := not_lt.mp h
      have hp : p ≠ 0 := by
        rintro rfl
        rw [Polynomial.degree_zero, le_bot_iff, Polynomial.degree_eq_bot] at hle
        exact hg hle
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Polynomial.natDegree_le_natDegree hle)
      have hlt : (Polynomial.C g.leadingCoeff * p
          - g * Polynomial.monomial d p.leadingCoeff).degree < p.degree := by
        rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_lt_iff_coeff_zero]
        intro m hm
        obtain ⟨j, rfl⟩ : ∃ j, m = j + d := ⟨m - d, by omega⟩
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_mul_monomial]
        rcases Nat.eq_or_lt_of_le hm with he | hl
        · have hj : j = g.natDegree := by omega
          rw [← he, hj]
          exact sub_self _
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hl,
            Polynomial.coeff_eq_zero_of_natDegree_lt (show g.natDegree < j by omega)]
          simp
      obtain ⟨k, q, r, he, hr⟩ := ih _ hlt
      refine ⟨k + 1, q + Polynomial.C (g.leadingCoeff ^ k) * Polynomial.monomial d p.leadingCoeff,
        r, ?_, hr⟩
      rw [pow_succ, Polynomial.C_mul]
      linear_combination he
end

section

noncomputable def UpperTheory.Reformulated.B.Qn19.AIC :
    (A : Type) → [CommRing A] → Prop :=
    fun (A : Type) [CommRing A] ↦
      ∀ (p : Polynomial A), p.Monic → (0 : ℕ) < p.natDegree → ∃ (a : A), Polynomial.eval a p = (0 : A)

private theorem UpperTheory.Reformulated.B.Qn19.commonDenom {R L : Type} [CommRing R] [CommRing L] (φ : R →+* L)
    (h : ∀ z : L, ∃ a b : R, IsUnit (φ b) ∧ z * φ b = φ a) (s : Finset L) :
    ∃ b : R, IsUnit (φ b) ∧ ∀ z ∈ s, ∃ a : R, φ a = z * φ b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert x s _ ih =>
    obtain ⟨b, hb, hs⟩ := ih
    obtain ⟨a, c, hc, hx⟩ := h x
    refine ⟨b * c, by rw [map_mul]; exact hb.mul hc, ?_⟩
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨a * b, by rw [map_mul, map_mul, ← hx]; ring⟩
    · obtain ⟨d, hd⟩ := hs z hz
      exact ⟨d * c, by rw [map_mul, map_mul, hd]; ring⟩

theorem UpperTheory.Reformulated.B.Qn19.aicFrac :
    ∀ (R L : Type) [inst : CommRing R] [inst_1 : CommRing L] (φ : R →+* L),
      UpperTheory.Reformulated.B.Qn19.AIC R →
        (∀ (z : L), ∃ (a : R) (b : R), IsUnit ((φ : R → L) b) ∧ z * (φ : R → L) b = (φ : R → L) a) → UpperTheory.Reformulated.B.Qn19.AIC L := by
  intro R L _ _ φ hR h p hp hdeg
  obtain ⟨b, hb, hs⟩ := UpperTheory.Reformulated.B.Qn19.commonDenom φ h p.coeffs
  have hmon : (p.scaleRoots (φ b)).Monic := (Polynomial.monic_scaleRoots_iff _).2 hp
  have hlift : p.scaleRoots (φ b) ∈ Polynomial.lifts φ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · by_cases h0 : p.coeff i = 0
      · exact ⟨0, by simp [h0]⟩
      · obtain ⟨a, ha⟩ := hs _ (Polynomial.coeff_mem_coeffs h0)
        obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
        exact ⟨a * b ^ k, by rw [map_mul, map_pow, ha, hk]; ring⟩
    · subst hi
      exact ⟨1, by simp [hp.coeff_natDegree]⟩
    · exact ⟨0, by simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]⟩
  obtain ⟨q, hq, hqd, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmon
  rw [Polynomial.natDegree_scaleRoots] at hqd
  obtain ⟨a, ha⟩ := hR q hqm (by rw [hqd]; exact hdeg)
  obtain ⟨u, hu⟩ := hb
  refine ⟨(↑u⁻¹ : L) * φ a, ?_⟩
  have h1 : Polynomial.eval (φ a) (p.scaleRoots (φ b)) = 0 := by
    rw [← hq, Polynomial.eval_map, Polynomial.eval₂_hom, ha, map_zero]
  have h2 := Polynomial.scaleRoots_eval_mul p ((↑u⁻¹ : L) * φ a) (φ b)
  have h3 : φ b * ((↑u⁻¹ : L) * φ a) = φ a := by
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  rw [h3, h1, ← hu] at h2
  exact ((u.isUnit.pow p.natDegree).mul_right_eq_zero).1 h2.symm
end

section

noncomputable def UpperTheory.Reformulated.B.Qf17.heckePol :
    {A : Type} → [inst : CommRing A] → ℕ → ℕ → (ℕ → A) → Polynomial A :=
    fun {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) ↦
      ∑ j ∈ Finset.range (n + (1 : ℕ)),
        (Polynomial.C : A → Polynomial A) ((-1 : A) ^ j * (↑q : A) ^ (j * (j - (1 : ℕ)) / (2 : ℕ)) * a j) *
          Polynomial.X ^ (n - j)

theorem UpperTheory.Reformulated.B.Qf17.hecke_map :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A),
      Polynomial.map f (UpperTheory.Reformulated.B.Qf17.heckePol n q a) = UpperTheory.Reformulated.B.Qf17.heckePol n q fun (j : ℕ) ↦ (f : A → B) (a j) := by
  intro A B _ _ f n q a
  unfold UpperTheory.Reformulated.B.Qf17.heckePol

  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    map_mul f, map_mul f, map_pow f, map_pow f, map_neg f, map_one f, map_natCast f]
end

section

noncomputable def UpperTheory.Reformulated.B.Qk6.heckePol :
    {A : Type} → [inst : CommRing A] → ℕ → ℕ → (ℕ → A) → Polynomial A :=
    fun {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) ↦
      ∑ j ∈ Finset.range (n + (1 : ℕ)),
        (Polynomial.C : A → Polynomial A) ((-1 : A) ^ j * (↑q : A) ^ (j * (j - (1 : ℕ)) / (2 : ℕ)) * a j) *
          Polynomial.X ^ (n - j)

theorem UpperTheory.Reformulated.B.Qk6.heckePol_map :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A),
      Polynomial.map f (UpperTheory.Reformulated.B.Qk6.heckePol n q a) = UpperTheory.Reformulated.B.Qk6.heckePol n q fun (j : ℕ) ↦ (f : A → B) (a j) := by
  intro A B _ _ f n q a
  unfold UpperTheory.Reformulated.B.Qk6.heckePol

  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    map_mul f, map_mul f, map_pow f, map_pow f, map_neg f, map_one f, map_natCast f]
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR :
    ℕ → Type :=
    fun (q : ℕ) ↦ LaurentPolynomial (Localization.Away (↑q : ℤ))

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux3 :
    ∀ {S : Type} [inst : CommRing S] (q : ℕ), IsUnit (↑q : S) → IsUnit ((Int.castRingHom S : ℤ → S) (↑q : ℤ)) := by
  intro S _ q hq
  rwa [map_natCast]

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.lam :
    {S : Type} → [inst : CommRing S] → (q : ℕ) → IsUnit (↑q : S) → Localization.Away (↑q : ℤ) →+* S :=
    fun {S : Type} [CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) ↦
      IsLocalization.Away.lift (↑q : ℤ) (UpperTheory.Reformulated.B.LaurentCharacterLambda.aux3 q hq)

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 :
    ∀ (S : Type) [inst : CommRing S], LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1 : ℤ) = (1 : LaurentPolynomial S) := by
  intro S _
  rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 :
    ∀ (S : Type) [inst : CommRing S], LaurentPolynomial.T (-1 : ℤ) * LaurentPolynomial.T (1 : ℤ) = (1 : LaurentPolynomial S) := by
  intro S _
  rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.tU :
    (S : Type) → [inst : CommRing S] → (LaurentPolynomial S)ˣ :=
    fun (S : Type) [CommRing S] ↦
      { val := LaurentPolynomial.T (1 : ℤ), inv := LaurentPolynomial.T (-1 : ℤ), val_inv := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 S,
        inv_val := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 S : (LaurentPolynomial S)ˣ }

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.iot :
    {S : Type} → [inst : CommRing S] → (q : ℕ) → IsUnit (↑q : S) → UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* LaurentPolynomial S :=
    fun {S : Type} [CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) ↦
      LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp (UpperTheory.Reformulated.B.LaurentCharacterLambda.lam q hq)) (UpperTheory.Reformulated.B.LaurentCharacterLambda.tU S)

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux9 :
    ∀ (q : ℕ), LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1 : ℤ) = (1 : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q) := by
  intro q
  exact UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 _

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_T_neg_one_mul_T_one :
    ∀ (q : ℕ), LaurentPolynomial.T (-1 : ℤ) * LaurentPolynomial.T (1 : ℤ) = (1 : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q) := by
  intro q
  exact UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 _

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.tR :
    (q : ℕ) → (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ :=
    fun (q : ℕ) ↦
      { val := LaurentPolynomial.T (1 : ℤ), inv := LaurentPolynomial.T (-1 : ℤ), val_inv := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux9 q,
        inv_val := UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_T_neg_one_mul_T_one q : (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ }

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.chi :
    {S : Type} →
      [inst : CommRing S] →
        (q : ℕ) →
          {R : Type} → [inst_1 : CommRing R] → (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) → (S →+* R) → LaurentPolynomial S →+* R :=
    fun {S : Type} [CommRing S] (q : ℕ) {R : Type} [CommRing R] (φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) (ψ : S →+* R) ↦
      LaurentPolynomial.eval₂ ψ
        ((Units.map (↑φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →* R) : (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ → Rˣ) (UpperTheory.Reformulated.B.LaurentCharacterLambda.tR q))

private theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_hom_ext {S R : Type} [CommRing S] [CommRing R]
    (f g : LaurentPolynomial S →+* R)
    (hC : ∀ a : S, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial S))
  apply Polynomial.ringHom_ext
  · intro a
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hC a
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hT

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.chi_uniq :
    ∀ {S : Type} [inst : CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) {R : Type} [inst_1 : CommRing R]
      (φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) (ψ : S →+* R) (χ : LaurentPolynomial S →+* R),
      χ.comp (UpperTheory.Reformulated.B.LaurentCharacterLambda.iot q hq) = φ → χ.comp LaurentPolynomial.C = ψ → χ = UpperTheory.Reformulated.B.LaurentCharacterLambda.chi q φ ψ := by
  intro S _ q hq R _ φ ψ χ h1 h2
  apply UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_hom_ext
  · intro a
    rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.chi, LaurentPolynomial.eval₂_C, ← h2, RingHom.comp_apply]
  · rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.chi, LaurentPolynomial.eval₂_T, zpow_one, Units.coe_map, ← h1]
    change _ = χ (UpperTheory.Reformulated.B.LaurentCharacterLambda.iot q hq (LaurentPolynomial.T 1))
    rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.iot, LaurentPolynomial.eval₂_T, zpow_one]
    rfl
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR :
    ℕ → Type :=
    fun (q : ℕ) ↦ LaurentPolynomial (Localization.Away (↑q : ℤ))

theorem UpperTheory.Reformulated.B.LocalQuotientHomExt.hom_ext :
    ∀ (q : ℕ) {R : Type} [inst : CommRing R] {f g : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q →+* R},
      (f : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q → R) (LaurentPolynomial.T (1 : ℤ)) =
          (g : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q → R) (LaurentPolynomial.T (1 : ℤ)) →
        f = g := by
  intro q R _ f g h
  have hC : f.comp LaurentPolynomial.C = g.comp LaurentPolynomial.C := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ))
    exact RingHom.ext_int _ _
  have hCa : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a) :=
    fun a => RingHom.congr_fun hC a
  have hmul : ∀ m n : ℤ, (LaurentPolynomial.T m : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q) * LaurentPolynomial.T n
      = LaurentPolynomial.T (m + n) := fun m n => (LaurentPolynomial.T_add m n).symm
  have h1 : f (LaurentPolynomial.T 1) * f (LaurentPolynomial.T (-1)) = 1 := by
    rw [← map_mul, hmul]; simp
  have h2 : g (LaurentPolynomial.T 1) * g (LaurentPolynomial.T (-1)) = 1 := by
    rw [← map_mul, hmul]; simp
  have hinv : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1)) := by
    calc f (LaurentPolynomial.T (-1))
        = f (LaurentPolynomial.T (-1)) * (g (LaurentPolynomial.T 1) * g (LaurentPolynomial.T (-1))) := by
          rw [h2, mul_one]
      _ = (f (LaurentPolynomial.T 1) * f (LaurentPolynomial.T (-1))) * g (LaurentPolynomial.T (-1)) := by
          rw [← h]; ring
      _ = g (LaurentPolynomial.T (-1)) := by rw [h1, one_mul]
  have hT : ∀ n : ℤ, f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ i ih => rw [← hmul, map_mul, map_mul, ih, h]
    | pred i ih => rw [sub_eq_add_neg, ← hmul, map_mul, map_mul, ih, hinv]
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => rw [map_add (f := _), map_add (f := _), hp, hr]
  | C_mul_T n a =>
    rw [map_mul, map_mul, hCa, hT]
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh37.Lp :
    (L : Type) → [Field L] → Type :=
    fun (L : Type) [Field L] ↦ ↥(NumberField.maximalRealSubfield L)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh37.Lsq :
    (R : Type) → [CommRing R] → R → Type :=
    fun (R : Type) [CommRing R] (Δ : R) ↦ QuadraticAlgebra R Δ (0 : R)


open NumberField NumberField.IsCMField in
private theorem UpperTheory.Reformulated.B.Qh37.exists_anti (L : Type) [Field L] [NumberField L] [IsCMField L] :
    ∃ δ : L, δ ≠ 0 ∧ complexConj L δ = -δ := by
  have h : ∃ x : L, complexConj L x ≠ x := by
    by_contra h
    push Not at h
    exact complexConj_ne_one L (AlgEquiv.ext h)
  obtain ⟨x, hx⟩ := h
  refine ⟨x - complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, complexConj_apply_apply, neg_sub]

theorem UpperTheory.Reformulated.B.Qh37.globEx :
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] [inst_2 : NumberField.IsCMField L],
      ∃ (Δ : UpperTheory.Reformulated.B.Qh37.Lp L) (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ ≃+* L),
        (∀ (x : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ),
            (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L) (Star.star x) =
              (NumberField.IsCMField.complexConj L : L → L) ((e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L) x)) ∧
          (∀ (a : UpperTheory.Reformulated.B.Qh37.Lp L),
              (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L)
                  ((Algebra.algebraMap (UpperTheory.Reformulated.B.Qh37.Lp L) (UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ) :
                      UpperTheory.Reformulated.B.Qh37.Lp L → UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ)
                    a) =
                (Algebra.algebraMap (UpperTheory.Reformulated.B.Qh37.Lp L) L : UpperTheory.Reformulated.B.Qh37.Lp L → L) a) ∧
            ∀ (σ : UpperTheory.Reformulated.B.Qh37.Lp L →+* ℝ), (σ : UpperTheory.Reformulated.B.Qh37.Lp L → ℝ) Δ < (0 : ℝ) := by
  intro L _ _ _
  obtain ⟨δ, hδ0, hδ⟩ := UpperTheory.Reformulated.B.Qh37.exists_anti L
  have hmem : δ * δ ∈ NumberField.maximalRealSubfield L := by
    rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_mul, hδ, neg_mul_neg]
  let Δ : NumberField.maximalRealSubfield L := ⟨δ * δ, hmem⟩
  have hΔ : algebraMap (NumberField.maximalRealSubfield L) L Δ = δ * δ := rfl
  let f : QuadraticAlgebra (NumberField.maximalRealSubfield L) Δ 0 →ₐ[NumberField.maximalRealSubfield L] L :=
    QuadraticAlgebra.lift ⟨δ, by rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, hΔ]⟩
  have hω : f QuadraticAlgebra.omega = δ := by
    have := (QuadraticAlgebra.lift (R := NumberField.maximalRealSubfield L) (a := Δ) (b := 0)
      (A := L)).symm_apply_apply ⟨δ, by rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, hΔ]⟩
    exact congrArg Subtype.val this
  have hf : ∀ x y, f ⟨x, y⟩ = algebraMap _ L x + algebraMap _ L y * δ := by
    intro x y
    rw [QuadraticAlgebra.mk_eq_add_smul_omega, map_add (f := _), map_smul, AlgHom.commutes, hω,
      Algebra.smul_def]
  have hstar : ∀ z, f (star z) = NumberField.IsCMField.complexConj L (f z) := by
    rintro ⟨x, y⟩
    rw [QuadraticAlgebra.star_mk, hf, hf, map_add (f := _), map_add (f := _), map_mul, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes, hδ, map_neg, map_zero]
    ring
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ h
    have h' := hstar ⟨x, y⟩
    rw [h, map_zero, QuadraticAlgebra.star_mk, hf, map_add (f := _), map_mul, map_neg, map_zero] at h'
    rw [hf] at h
    have hx : algebraMap _ L x = 0 := by linear_combination (h + h') / 2
    have hy : algebraMap _ L y * δ = 0 := by linear_combination (h - h') / 2
    have hy' := (mul_eq_zero.mp hy).resolve_right hδ0
    rw [map_eq_zero] at hx hy'
    subst hx hy'
    rfl
  have hsurj : Function.Surjective f := by
    intro z
    have h1 : (z + NumberField.IsCMField.complexConj L z) / 2 ∈
        NumberField.maximalRealSubfield L := by
      rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), map_ofNat,
        NumberField.IsCMField.complexConj_apply_apply, add_comm]
    have h2 : (z - NumberField.IsCMField.complexConj L z) / (2 * δ) ∈
        NumberField.maximalRealSubfield L := by
      rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, map_ofNat,
        NumberField.IsCMField.complexConj_apply_apply, hδ]
      field_simp
      ring
    refine ⟨⟨⟨_, h1⟩, ⟨_, h2⟩⟩, ?_⟩
    rw [hf]
    change (z + NumberField.IsCMField.complexConj L z) / 2 +
      (z - NumberField.IsCMField.complexConj L z) / (2 * δ) * δ = z
    field_simp
    ring
  refine ⟨Δ, RingEquiv.ofBijective f.toRingHom ⟨hinj, hsurj⟩, hstar, f.commutes, fun σ ↦ ?_⟩
  let φ : L →+* ℂ := NumberField.ComplexEmbedding.lift L (Complex.ofRealHom.comp σ)
  have h1 : φ δ * φ δ = (σ Δ : ℂ) := by
    rw [← map_mul, ← hΔ]
    exact NumberField.ComplexEmbedding.lift_algebraMap_apply L (Complex.ofRealHom.comp σ) Δ
  have h2 : (starRingEnd ℂ) (φ δ) = -φ δ := by
    rw [← NumberField.IsCMField.complexEmbedding_complexConj, hδ, map_neg]
  have h3 : ((Complex.normSq (φ δ) : ℝ) : ℂ) = ((-σ Δ : ℝ) : ℂ) := by
    rw [← Complex.mul_conj, h2, mul_neg, h1, Complex.ofReal_neg]
  have h4 : 0 < Complex.normSq (φ δ) := Complex.normSq_pos.mpr ((map_ne_zero φ).mpr hδ0)
  rw [Complex.ofReal_injective h3] at h4
  exact neg_pos.mp h4
end

section

noncomputable def UpperTheory.Reformulated.B.FrobeniusElementAlt.frb :
    {l : ℕ} → [Fact (Nat.Prime l)] → {B : Type} → [inst : CommRing B] → (↑l : B) = (0 : B) → B →+* B :=
  fun {l} hl {B} _ h =>
    { toFun := fun x => x ^ l
      map_one' := one_pow l
      map_mul' := fun x y => mul_pow x y l
      map_zero' := zero_pow hl.out.ne_zero
      map_add' := fun x y => by
        rw [add_pow_prime_eq hl.out x y, h]
        simp }
end

section

noncomputable def UpperTheory.Reformulated.B.FrobeniusElement.frb :
    {l : ℕ} → [Fact (Nat.Prime l)] → {B₀ : Type} → [inst : CommRing B₀] → (↑l : B₀) = (0 : B₀) → B₀ →+* B₀ :=
  fun {l} [hl : Fact (Nat.Prime l)] {B₀} [CommRing B₀] h =>
    { toFun := fun x => x ^ l
      map_one' := one_pow l
      map_mul' := fun x y => mul_pow x y l
      map_zero' := zero_pow hl.out.ne_zero
      map_add' := fun x y => by
        obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl.out x y
        rw [hr, h]
        ring }
end

section

theorem UpperTheory.Reformulated.B.ExistsNsmulMemClosure.exists_nsmul_mem_closure.{u_1} :
    ∀ {V : Type u_1} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℚ V] (s : Set V),
    ∀ w ∈ Submodule.span ℚ s, ∃ (k : ℕ), (0 : ℕ) < k ∧ k • w ∈ AddSubgroup.closure s := by
  intro V _ _ s w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using AddSubgroup.subset_closure hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have h : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact add_mem (nsmul_mem hx b) (nsmul_mem hy a)
  | smul q x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    refine ⟨q.den * a, Nat.mul_pos q.den_pos ha, ?_⟩
    have h : (q.den * a) • (q • x) = q.num • (a • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ a x,
        ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
      congr 1
      rw [← Rat.mul_den_eq_num q]
      push_cast
      ring
    rw [h]
    exact zsmul_mem hx _
end
