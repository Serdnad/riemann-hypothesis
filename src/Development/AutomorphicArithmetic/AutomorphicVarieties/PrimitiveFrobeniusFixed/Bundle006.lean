module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem derivation_ne_zero (q : ℕ) (t : G ℚ Ω) {u : Ω} (hu : u ≠ 0) : der1 q t u ≠ 0 := by
  unfold der1
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ((map_ne_zero _).2 hu)

private theorem derivation_mul (q : ℕ) (t : G ℚ Ω) (u v : Ω) : der1 q t (u * v) = der1 q t u * der1 q t v := by
  unfold der1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, mul_pow]

private theorem derivation_zpow (q : ℕ) (t : G ℚ Ω) (u : Ω) (k : ℤ) : der1 q t (u ^ k) = der1 q t u ^ k := by
  unfold der1
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow₀, ← zpow_natCast ((t ^ i) u ^ k) i, ← zpow_natCast ((t ^ i) u) i, ← zpow_mul, ← zpow_mul,
    mul_comm]

private theorem derivation_galois_equivariant (q : ℕ) (t g : G ℚ Ω) (u : Ω) (h : ∀ s : G ℚ Ω, g (s u) = s (g u)) :
    g (der1 q t u) = der1 q t (g u) := by
  unfold der1
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, h]

private theorem der_mul (τ : ℕ → G ℚ Ω) (L : List ℕ) (u v : Ω) : der τ L (u * v) = der τ L u * der τ L v := by
  induction L with
  | nil => simp only [der.eq_1]
  | cons q L ih => rw [der.eq_2, der.eq_2, der.eq_2, ih, derivation_mul]

private theorem der_one (τ : ℕ → G ℚ Ω) (L : List ℕ) : der τ L (1 : Ω) = 1 := by
  induction L with
  | nil => rw [der.eq_1]
  | cons q L ih =>
    rw [der.eq_2, ih]
    unfold der1
    simp

private def derHom (τ : ℕ → G ℚ Ω) (L : List ℕ) : Ω →* Ω where
  toFun := der τ L
  map_one' := der_one τ L
  map_mul' := der_mul τ L

private theorem tele (q : ℕ) (t : G ℚ Ω) (u : Ω) (hu : u ≠ 0) (h : (t ^ (q - 1)) u = u) :
    t (der1 q t u) / der1 q t u = u ^ (q - 1) / nrm q t u := by
  have key : ∀ (a : ℕ → Ω) (n : ℕ),
      (∏ i ∈ Finset.range n, a (i + 1) ^ i) * (∏ i ∈ Finset.range n, a i) * a n =
        a 0 * a n ^ n * ∏ i ∈ Finset.range n, a i ^ i := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
      calc (∏ i ∈ Finset.range n, a (i + 1) ^ i) * a (n + 1) ^ n * ((∏ i ∈ Finset.range n, a i) * a n) * a (n + 1)
          = ((∏ i ∈ Finset.range n, a (i + 1) ^ i) * (∏ i ∈ Finset.range n, a i) * a n) * a (n + 1) ^ (n + 1) := by ring
        _ = a 0 * a n ^ n * (∏ i ∈ Finset.range n, a i ^ i) * a (n + 1) ^ (n + 1) := by rw [ih]
        _ = a 0 * a (n + 1) ^ (n + 1) * ((∏ i ∈ Finset.range n, a i ^ i) * a n ^ n) := by ring
  have hD : der1 q t u ≠ 0 := derivation_ne_zero q t hu
  have hN : nrm q t u ≠ 0 := by
    unfold nrm
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hu
  have htD : t (der1 q t u) = ∏ i ∈ Finset.range (q - 1), ((t ^ (i + 1)) u) ^ i := by
    unfold der1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, pow_succ', AlgEquiv.mul_apply]
  have hk := key (fun i => (t ^ i) u) (q - 1)
  simp only [pow_zero, AlgEquiv.one_apply, h] at hk
  rw [div_eq_div_iff hD hN, htD]
  have hD' : der1 q t u = ∏ i ∈ Finset.range (q - 1), ((t ^ i) u) ^ i := rfl
  have hN' : nrm q t u = ∏ i ∈ Finset.range (q - 1), (t ^ i) u := rfl
  rw [hD', hN']
  apply mul_right_cancel₀ hu
  linear_combination hk

end

theorem UpperTheory.V.ML.derBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N r : ℕ), N ≠ 0 → ∀ (τ : ℕ → G ℚ Ω) (L : List ℕ) (u : Ω), u ≠ 0 → (∀ g ∈ fixMu ℚ Ω N, g u = u) →
    der τ L u ≠ 0 ∧ (∀ g ∈ fixMu ℚ Ω N, g (der τ L u) = der τ L u) ∧ (∀ g : G ℚ Ω, g (der τ L u) = der τ L (g u)) ∧
    ((∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) → ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (der τ L u) = 1) ∧
    (∀ v : Ω, der τ L (u * v) = der τ L u * der τ L v) ∧ (∀ k : ℤ, der τ L (u ^ k) = der τ L u ^ k) ∧
    (∀ q, der τ L (der1 q (τ q) u) = der1 q (τ q) (der τ L u)) ∧ (∀ L', L.Perm L' → der τ L u = der τ L' u) ∧
    ∀ q : ℕ, 1 ≤ q → (τ q ^ (q - 1)) u = u → τ q (der1 q (τ q) u) / der1 q (τ q) u = u ^ (q - 1) / nrm q (τ q) u := by
  intro Ω _ _ _ N r hN τ L u hu hfix
  obtain ⟨-, -, -, -, -, hcomm, -, -, -, -⟩ := galBasic Ω N hN
  have hfix1 : ∀ (q : ℕ) (t : G ℚ Ω) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g ∈ fixMu ℚ Ω N, g (der1 q t x) = der1 q t x := by
    intro q t x hx g hg
    rw [derivation_galois_equivariant q t g x (fun s => hcomm x hx g s), hx g hg]
  have hfixL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g ∈ fixMu ℚ Ω N, g (der τ L x) = der τ L x := by
    intro L x hx
    induction L with
    | nil => simpa only [der.eq_1] using hx
    | cons q L ih =>
      rw [der.eq_2]
      exact hfix1 q (τ q) _ ih
  have hneL : ∀ L : List ℕ, der τ L u ≠ 0 := by
    intro L
    induction L with
    | nil =>
      rw [der.eq_1]
      exact hu
    | cons q L ih =>
      rw [der.eq_2]
      exact derivation_ne_zero q (τ q) ih
  have hcommL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g : G ℚ Ω, g (der τ L x) = der τ L (g x) := by
    intro L x hx g
    induction L with
    | nil => simp only [der.eq_1]
    | cons q L ih =>
      rw [der.eq_2, der.eq_2, derivation_galois_equivariant q (τ q) g _ (fun s => hcomm _ (hfixL L x hx) g s), ih]
  have hder1 : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ (q : ℕ) (t : G ℚ Ω), der τ L (der1 q t x) = der1 q t (der τ L x) := by
    intro L x hx q t
    have e : der τ L (der1 q t x) = derHom τ L (der1 q t x) := rfl
    rw [e]
    unfold der1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow]
    show der τ L ((t ^ i) x) ^ i = _
    rw [← hcommL L x hx]
  have hconj : ∀ x : Ω, (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation x = 1) →
      ∀ (s : G ℚ Ω) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (s x) = 1 := by
    intro x hx s A hA
    obtain ⟨-, -, -, hlt, heq⟩ := (placeBasic Ω).2.2.2.2.2.2.2.2.2 (s⁻¹ • A) s
    have hsA : s • (s⁻¹ • A) = A := smul_inv_smul s A
    rw [hsA] at hlt heq
    apply (heq x).mpr
    apply hx
    intro hB
    apply hA
    have hr := (hlt (r : Ω)).mpr hB
    show A.valuation (r : Ω) < 1
    simpa using hr
  have hvalL : (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) →
      ∀ (L : List ℕ) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (der τ L u) = 1 := by
    intro hu1 L
    induction L with
    | nil => simpa only [der.eq_1] using hu1
    | cons q L ih =>
      intro A hA
      rw [der.eq_2]
      unfold der1
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i _
      rw [Valuation.map_pow, hconj _ ih _ A hA, one_pow]
  have hzpowL : ∀ (L : List ℕ) (k : ℤ), der τ L (u ^ k) = der τ L u ^ k := by
    intro L k
    induction L with
    | nil => simp only [der.eq_1]
    | cons q L ih => rw [der.eq_2, der.eq_2, ih, derivation_zpow]
  have hperm : ∀ L' : List ℕ, L.Perm L' → der τ L u = der τ L' u := by
    intro L' hp
    induction hp with
    | nil => rfl
    | cons q _ ih => rw [der.eq_2, der.eq_2, ih]
    | swap a b l =>
      rw [der.eq_2, der.eq_2, der.eq_2, der.eq_2]
      have hx := hfixL l u hfix
      have h1 : der1 b (τ b) (der1 a (τ a) (der τ l u)) = der τ [b] (der1 a (τ a) (der τ l u)) := by
        rw [der.eq_2, der.eq_1]
      rw [h1, hder1 [b] _ hx, der.eq_2, der.eq_1]
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
  exact ⟨hneL L, hfixL L u hfix, fun g => hcommL L u hfix g, fun h => hvalL h L, der_mul τ L u, hzpowL L,
    fun q => hder1 L u hfix q (τ q), hperm, fun q _ h => tele q (τ q) u hu h⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω]

private def Cg (A : ValuationSubring Ω) (u v : Ω) : Prop :=
  A.valuation u = 1 ∧ A.valuation v = 1 ∧ A.valuation (u - v) < 1

private theorem cg_of (A : ValuationSubring Ω) {u v : Ω} (hu : A.valuation u = 1) (h : A.valuation (u - v) < 1) :
    Cg A u v := by
  refine ⟨hu, ?_, h⟩
  have h1 : A.valuation (-(u - v)) < A.valuation u := by rw [Valuation.map_neg, hu]; exact h
  have h2 := A.valuation.map_add_eq_of_lt_left h1
  have h3 : u + -(u - v) = v := by ring
  rw [h3, hu] at h2
  exact h2

private theorem cg_mul {A : ValuationSubring Ω} {u v u' v' : Ω} (h : Cg A u v) (h' : Cg A u' v') :
    Cg A (u * u') (v * v') := by
  refine ⟨by rw [map_mul, h.1, h'.1, one_mul], by rw [map_mul, h.2.1, h'.2.1, one_mul], ?_⟩
  have : u * u' - v * v' = u * (u' - v') + (u - v) * v' := by ring
  rw [this]
  refine A.valuation.map_add_lt ?_ ?_
  · rw [map_mul, h.1, one_mul]; exact h'.2.2
  · rw [map_mul, h'.2.1, mul_one]; exact h.2.2

private theorem cg_pow {A : ValuationSubring Ω} {u v : Ω} (h : Cg A u v) (n : ℕ) : Cg A (u ^ n) (v ^ n) := by
  induction n with
  | zero => exact ⟨by simp, by simp, by simp⟩
  | succ n ih => rw [pow_succ, pow_succ]; exact cg_mul ih h

private theorem cg_inv {A : ValuationSubring Ω} {u v : Ω} (h : Cg A u v) : Cg A u⁻¹ v⁻¹ := by
  have hu : u ≠ 0 := fun h0 => by have := h.1; rw [h0, map_zero] at this; exact zero_ne_one this
  have hv : v ≠ 0 := fun h0 => by have := h.2.1; rw [h0, map_zero] at this; exact zero_ne_one this
  refine ⟨by rw [map_inv₀, h.1, inv_one], by rw [map_inv₀, h.2.1, inv_one], ?_⟩
  have : u⁻¹ - v⁻¹ = -((u - v) * u⁻¹ * v⁻¹) := by field_simp; ring
  rw [this, Valuation.map_neg, map_mul, map_mul, map_inv₀, map_inv₀, h.1, h.2.1, inv_one, mul_one, mul_one]
  exact h.2.2

variable [Algebra ℚ Ω]

private theorem opP_mul (δ : G ℚ Ω) (a : ℕ) (u v : Ω) : opP δ a (u * v) = opP δ a u * opP δ a v := by
  simp only [opP, map_mul, mul_pow, mul_div_mul_comm]

private theorem opP_div (δ : G ℚ Ω) (a : ℕ) (u v : Ω) : opP δ a (u / v) = opP δ a u / opP δ a v := by
  simp only [opP, map_div₀, div_pow]
  rw [div_div_div_comm]

private theorem opP_pow (δ : G ℚ Ω) (a : ℕ) (u : Ω) (n : ℕ) : opP δ a (u ^ n) = opP δ a u ^ n := by
  simp only [opP, map_pow, div_pow]
  rw [← pow_mul, ← pow_mul, mul_comm]

private theorem map_opP (δ g : G ℚ Ω) (a : ℕ) (u : Ω) (h : g (δ u) = δ (g u)) :
    g (opP δ a u) = opP δ a (g u) := by
  simp only [opP, map_div₀, map_pow, h]

private theorem opP_root (δ : G ℚ Ω) (a N : ℕ) (hN : N ≠ 0) (hδ : Pows N a δ) (ζ : Ω) (h : ζ ^ N = 1) :
    opP δ a ζ = 1 := by
  have h0 : ζ ≠ 0 := fun h0 => by rw [h0, zero_pow hN] at h; exact zero_ne_one h
  rw [opP, hδ ζ h, div_self (pow_ne_zero _ h0)]

private theorem nrm_opP (δ τ : G ℚ Ω) (a q n : ℕ) (u : Ω) (h : ∀ g : G ℚ Ω, g (δ u) = δ (g u)) :
    nrm q τ (opP δ a u ^ n) = opP δ a (nrm q τ u) ^ n := by
  simp only [nrm, map_pow, opP, map_div₀, h, map_prod]
  rw [Finset.prod_pow, Finset.prod_div_distrib, Finset.prod_pow]

end SlopeTestRemainingChoices

private theorem admissible_of_integral_conj_le {l F r q d : ℕ} (h : ML.admitted l F r (q * d)) : ML.admitted l F r d :=
  ⟨h.1.squarefree_of_dvd (Dvd.intro_left q rfl), fun p hp hd => h.2 p hp (hd.mul_left q)⟩

private theorem admissible_prime_coprime {l F r q : ℕ} (h : AdmP l F r q) : q.Coprime r := by
  have hq := h.1
  rw [Nat.Prime.coprime_iff_not_dvd hq]
  intro hd
  haveI : Fact q.Prime := ⟨hq⟩
  apply h.2.2.2
  have : (r : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff r q).2 hd
  rw [this, orderOf_zero]
  exact dvd_zero l

theorem UpperTheory.V.ML.sysOfLax :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l N₀ m F r a : ℕ), l.Prime → l ≠ 2 → N₀.Coprime l → 1 ≤ m → F = N₀ * l ^ m → ∀ (X : ℕ → Ω) (s : ℕ → ℕ → ℕ), Lax l F r X s →
    ∀ δ : G ℚ Ω, Pows (l ^ m) a δ → Sys l F r (fun d => opP δ a (X d) ^ (2 * N₀ * d)) fun d q => q * s d q := by
  intro Ω _ _ _ l N₀ m F r a hl _ hN hm hF X s hX δ hδ
  have hN0 : N₀ ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hN
    exact hl.one_lt.ne' hN
  have hlm : l ^ m ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hF0 : F ≠ 0 := hF ▸ mul_ne_zero hN0 hlm
  have hFd : ∀ d, ML.admitted l F r d → F * d ≠ 0 := fun d hd => mul_ne_zero hF0 hd.1.ne_zero
  have hcomm : ∀ d, ML.admitted l F r d → ∀ g h : G ℚ Ω, g (h (X d)) = h (g (X d)) := fun d hd =>
    (galBasic Ω (F * d) (hFd d hd)).2.2.2.2.2.1 (X d) (hX.fix d hd)
  obtain ⟨-, -, -, hcop, -, -, -, -, -, hact⟩ := placeBasic Ω
  have hlt : ∀ (A : ValuationSubring Ω) (y : Ω), A.valuation (δ y) < 1 ↔ (δ⁻¹ • A).valuation y < 1 := fun A y => by
    have := (hact (δ⁻¹ • A) δ).2.2.2.1 y
    rwa [smul_inv_smul] at this
  have heq : ∀ (A : ValuationSubring Ω) (y : Ω), A.valuation (δ y) = 1 ↔ (δ⁻¹ • A).valuation y = 1 := fun A y => by
    have := (hact (δ⁻¹ • A) δ).2.2.2.2 y
    rwa [smul_inv_smul] at this
  have hov : ∀ (A : ValuationSubring Ω) (n : ℕ), Over (δ⁻¹ • A) n ↔ Over A n := fun A n => by
    have := hlt A (n : Ω)
    rw [map_natCast] at this
    exact this.symm
  have hδu : ∀ d, ML.admitted l F r d → ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (δ (X d)) = 1 :=
    fun d hd A hA => (heq A _).2 (hX.unit d hd _ fun h => hA ((hov A r).1 h))
  have hζ : ∀ (n : ℕ) (ζ : Ω), ζ ^ (2 * F * n) = 1 → opP δ a ζ ^ (2 * N₀ * n) = 1 := fun n ζ h => by
    rw [← opP_pow]
    refine opP_root δ a (l ^ m) hlm hδ _ ?_
    rw [← pow_mul, ← h, hF]
    congr 1
    ring
  refine ⟨fun d hd => ?_, fun d hd g hg => ?_, fun d hd A hA => ?_, fun d q hq hd => ?_,
    fun d q hq hd τ hτ hgen φ hφ => ?_, fun d q hq hd φ hφ A hA => ?_⟩
  · refine pow_ne_zero _ (div_ne_zero ?_ (pow_ne_zero _ (hX.ne d hd)))
    exact (map_ne_zero δ).2 (hX.ne d hd)
  · rw [map_pow, map_opP δ g a _ (hcomm d hd g δ), hX.fix d hd g hg]
  · rw [map_pow, opP, map_div₀, map_pow, hδu d hd A hA, hX.unit d hd A hA]
    simp
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · have h1 := (hd.2 q hq (Dvd.intro d rfl)).2.1
      have hlF : l ∣ F := hF ▸ Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N₀
      have h2 : l ∣ 1 := ((h1.of_dvd hlF).dvd_iff dvd_rfl).1 h
      exact hl.one_lt.ne' (Nat.dvd_one.1 h2)
    · exact hX.cop d q hq hd h
  · obtain ⟨ζ, h1, h2⟩ := hX.norm d q hq hd τ hτ hgen φ hφ
    rw [nrm_opP δ τ a q _ _ (fun g => hcomm _ hd g δ), h2, opP_mul, mul_pow, hζ _ ζ h1, one_mul, opP_pow, opP_div,
      map_pow, map_opP δ φ⁻¹ a _ (hcomm d (admissible_of_integral_conj_le hd) _ δ), ← div_pow, ← pow_mul, ← pow_mul]
    congr 1
    ring
  · obtain ⟨ζ, h1, h2⟩ := hX.cong d q hq hd φ hφ
    have hr : ¬ Over A r := hcop A q r (admissible_prime_coprime (hd.2 q hq (Dvd.intro d rfl))) hA
    have c1 := cg_of A (hX.unit _ hd A hr) (h2 A hA)
    have h3 := (hlt A _).2 (h2 _ ((hov A q).2 hA))
    rw [map_sub] at h3
    have c2 := cg_of A (hδu _ hd A hr) h3
    have c3 := cg_pow (cg_mul c2 (cg_inv (cg_pow c1 a))) (2 * N₀ * (q * d))
    rw [← div_eq_mul_inv, ← div_eq_mul_inv] at c3
    have c4 : A.valuation (opP δ a (X (q * d)) ^ (2 * N₀ * (q * d)) -
      opP δ a (ζ * φ⁻¹ (X d) ^ s d q) ^ (2 * N₀ * (q * d))) < 1 := c3.2.2
    rw [opP_mul, mul_pow, hζ _ ζ h1, one_mul, opP_pow, ← pow_mul] at c4
    rw [map_pow, map_opP δ φ⁻¹ a _ (hcomm d (admissible_of_integral_conj_le hd) _ δ), ← pow_mul]
    have e : 2 * N₀ * d * (q * s d q) = s d q * (2 * N₀ * (q * d)) := by ring
    rw [e]
    exact c4
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.kolInit :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F r a : ℕ) [NeZero M] [NeZero F] (hM : M ∣ F), r.Prime → r.Coprime F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω F, h y = y) →
    ∀ κ : G ℚ Ω → ZMod M, IsKol M F 1 ζ δ a y κ → ∀ A₀ : ValuationSubring Ω, Over A₀ r → ∀ k : (ZMod F)ˣ → ℤ, HasOrd F r A₀ (opP δ a y) k →
    ∀ ρ : Ω, ρ ^ M = (r : Ω) → ∀ t ∈ Ine (F := ℚ) A₀, t ρ = ζ * ρ → ∀ (c : (ZMod F)ˣ) (σ : G ℚ Ω), Lifts F c σ →
    κ (σ⁻¹ * t * σ) * ZMod.castHom hM (ZMod M) (c : ZMod F) = (k c : ZMod M) := by
  intro Ω _ _ _ M F r a _ _ hM hr hrF ζ hζ δ hδ y hy0 hyfix κ hκ A₀ hA₀ k hk ρ hρ t ht htρ c σ hσ
  have pb := placeBasic Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hM0 : M ≠ 0 := NeZero.ne M
  have hr0 : (r : Ω) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hρ
    exact hr0 hρ.symm
  have hFr : F.Coprime r := hrF.symm
  have hMr : M.Coprime r := (hrF.coprime_dvd_right hM).symm
  have hnotF : ¬ Over A₀ F := fun h => pb.2.2.2.1 A₀ F r hFr h hA₀
  have hnotM : ¬ Over A₀ M := fun h => pb.2.2.2.1 A₀ M r hMr h hA₀
  have hIneF : Ine (F := ℚ) A₀ ≤ fixMu ℚ Ω F := pb.2.2.2.2.1 A₀ F hnotF
  have hconj : ∀ (h τ : G ℚ Ω), h ∈ fixMu ℚ Ω F → τ⁻¹ * h * τ ∈ fixMu ℚ Ω F := by
    intro h τ hh x hx
    have h1 : h (τ x) = τ x := hh _ (by rw [← map_pow, hx, map_one])
    simp [AlgEquiv.mul_apply, h1]
  have htF : t ∈ fixMu ℚ Ω F := hIneF ht
  have hg : σ⁻¹ * t * σ ∈ fixMu ℚ Ω F := hconj t σ htF
  obtain ⟨Y, hYM, hK⟩ := hκ
  obtain ⟨z, -, hzM, hζκ⟩ := hK _ hg
  rw [hyfix _ hg, div_self hy0] at hzM
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hzM
    exact zero_ne_one hzM
  have hPz : opP δ a z = 1 := by
    unfold opP
    rw [hδ z hzM, div_self (pow_ne_zero _ hz0)]
  rw [hPz, div_one] at hζκ
  have hY0 : Y ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hYM
    exact hy0 hYM.symm
  set w := opP δ a Y with hw
  have hw0 : w ≠ 0 := by
    rw [hw]
    unfold opP
    exact div_ne_zero (by simpa using hY0) (pow_ne_zero _ hY0)
  have hζF : ζ ^ F = 1 := (hζ.pow_eq_one_iff_dvd F).mpr hM
  have hσζ : σ ζ = ζ ^ (c : ZMod F).val := hσ ζ hζF
  have h1 : ζ ^ ((c : ZMod F).val * (κ (σ⁻¹ * t * σ)).val) = t (σ w) / σ w := by
    rw [pow_mul, ← hσζ, ← map_pow, hζκ, map_div₀]
    congr 1
    simp [AlgEquiv.mul_apply]
  set W := σ w with hW
  have hW0 : W ≠ 0 := by simpa [hW] using hw0
  have hWM : W ^ M = σ (opP δ a y) := by
    rw [hW, ← map_pow, hw]
    unfold opP
    rw [div_pow, ← map_pow, ← pow_mul, mul_comm a M, pow_mul, hYM]
  have hPfix : ∀ h ∈ fixMu ℚ Ω F, h (opP δ a y) = opP δ a y := by
    intro h hh
    unfold opP
    rw [map_div₀, map_pow, hyfix h hh]
    congr 1
    have h2 := congrArg δ (hyfix _ (hconj h δ hh))
    simpa [AlgEquiv.mul_apply] using h2
  have hXt : t (σ (opP δ a y)) = σ (opP δ a y) := by
    have h2 := congrArg σ (hPfix _ hg)
    simpa [AlgEquiv.mul_apply] using h2
  set e := W / ρ ^ (k c) with he
  have heM : e ^ M = σ (opP δ a y) / (r : Ω) ^ (k c) := by
    rw [he, div_pow, hWM, ← zpow_natCast (ρ ^ k c) M, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρ]
  have hvr0 : A₀.valuation (r : Ω) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  have hveM : A₀.valuation e ^ M = 1 := by
    rw [← map_pow, heM, map_div₀, map_zpow₀, hk c σ hσ, div_self (zpow_ne_zero _ hvr0)]
  have hve : A₀.valuation e = 1 := by
    rcases lt_trichotomy (A₀.valuation e) 1 with hlt | heq | hgt
    · exact absurd hveM (ne_of_lt (pow_lt_one₀ zero_le' hlt hM0))
    · exact heq
    · exact absurd hveM (ne_of_gt (one_lt_pow₀ hgt hM0))
  have he0 : e ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hve
    exact zero_ne_one hve
  have hteM : (t e / e) ^ M = 1 := by
    have hX0 : σ (opP δ a y) / (r : Ω) ^ (k c) ≠ 0 := by
      rw [← heM]
      exact pow_ne_zero M he0
    rw [div_pow, ← map_pow, heM, map_div₀, hXt, map_zpow₀, map_natCast]
    exact div_self hX0
  have hin : A₀.valuation (t e - e) < 1 := ht.2 e hve.le
  have hte1 : A₀.valuation (t e / e - 1) < 1 := by
    rw [div_sub_one he0, map_div₀, hve, div_one]
    exact hin
  have hte : t e = e := by
    have h3 := pb.2.2.2.2.2.1 A₀ M (t e / e) hnotM hteM hte1
    rwa [div_eq_one_iff_eq he0] at h3
  have hWe : W = e * ρ ^ (k c) := by
    rw [he, div_mul_cancel₀ _ (zpow_ne_zero _ hρ0)]
  have htW : t W / W = ζ ^ (k c) := by
    rw [div_eq_iff hW0]
    conv_lhs => rw [hWe]
    rw [map_mul, map_zpow₀, hte, htρ, mul_zpow, hWe]
    ring
  rw [htW, ← zpow_natCast] at h1
  have hdvd : (M : ℤ) ∣ (k c) - (((c : ZMod F).val * (κ (σ⁻¹ * t * σ)).val : ℕ) : ℤ) := by
    rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ (hζ.ne_zero hM0), ← h1, div_self (zpow_ne_zero _ (hζ.ne_zero hM0))]
  have h4 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ M).mpr hdvd
  push_cast at h4
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ← h4, ZMod.natCast_zmod_val, mul_comm]
end
