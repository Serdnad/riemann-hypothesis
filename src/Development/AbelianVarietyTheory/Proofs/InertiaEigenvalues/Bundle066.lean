module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
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
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem finite_quot_span_of_ne_zero (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (c : O) (hc : c ≠ 0) : Finite (O ⧸ Ideal.span {c}) := by
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have h1 : Ideal.span {c} = IsLocalRing.maximalIdeal O ^ n := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow, hu,
      Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [h1]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

theorem finite_between_mulLat (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L)
    (c : K.O) (hc : c ≠ 0) :
    {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite := by
  haveI := finite_quot_span_of_ne_zero K.O c hc
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hL.1
  have hfg : (⊤ : Submodule K.O L).FG := Module.Finite.fg_top
  set S : Submodule K.O L := Ideal.span {c} • (⊤ : Submodule K.O L) with hS
  haveI : Finite (L ⧸ S) := Submodule.finite_quotient_smul _ hfg
  haveI : Finite (Submodule K.O (L ⧸ S)) :=
    Finite.of_injective (fun P : Submodule K.O (L ⧸ S) => (P : Set (L ⧸ S))) SetLike.coe_injective
  let f : Submodule K.O B.A → Submodule K.O (L ⧸ S) := fun M => (M.comap L.subtype).map S.mkQ
  have hSle : ∀ M : Submodule K.O B.A, mulLat K.O (algebraMap K.O B.A c) L ≤ M → S ≤ M.comap L.subtype := by
    intro M hM
    rw [hS, Submodule.smul_le]
    intro r hr x _
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have hx : algebraMap K.O B.A c * (x : B.A) ∈ M := hM ⟨x, x.2, rfl⟩
    have : ((a * c) • x : L) = (a • (algebraMap K.O B.A c * (x : B.A)) : B.A) := by
      rw [Submodule.coe_smul, ← Algebra.smul_def, smul_smul]
    rw [Submodule.mem_comap, Submodule.subtype_apply, this]
    exact M.smul_mem a hx
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M₁ h₁ M₂ h₂ heq
  have e1 : M₁.comap L.subtype = M₂.comap L.subtype := by
    have := congrArg (Submodule.comap S.mkQ) heq
    simp only [f, Submodule.comap_map_mkQ] at this
    rwa [sup_eq_right.2 (hSle M₁ h₁.1), sup_eq_right.2 (hSle M₂ h₂.1)] at this
  have e2 := congrArg (Submodule.map L.subtype) e1
  rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 h₁.2,
    inf_eq_right.2 h₂.2] at e2

end GlobalTheory.UnitLemma
end

section

open GlobalTheory.UnitLemma Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.EtaCompare

open WithZero

theorem norm_le_iff_valuation_le (K : UQ) {E : Type} [NormedField E] (φ : K.E ≃+* E)
    (hball : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (a b : K.E) (hb : b ≠ 0) :
    ‖φ a‖ ≤ ‖φ b‖ ↔ (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E a ≤
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E b := by
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E
  have hint : ∀ y : K.E, v y ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range := by
    intro y
    refine ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one h, ?_⟩
    rintro ⟨a, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one a
  have hφb : φ b ≠ 0 := by simpa using hb
  have hvb : v b ≠ 0 := (Valuation.ne_zero_iff v).2 hb
  rw [← div_le_one₀ (norm_pos_iff.2 hφb), ← norm_div, ← map_div₀, hball, ← hint, map_div₀,
    div_le_one₀ (zero_lt_iff.2 hvb)]

theorem norm_eq_iff_valuation_eq (K : UQ) {E : Type} [NormedField E] (φ : K.E ≃+* E)
    (hball : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (a b : K.E) :
    ‖φ a‖ = ‖φ b‖ ↔ (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E a =
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E b := by
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E
  by_cases hb : b = 0
  · subst hb; simp [v]
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, norm_zero, v]
    constructor
    · intro h; exact absurd (norm_eq_zero.1 h.symm) (by simpa using hb)
    · intro h; exact absurd ((Valuation.zero_iff _).1 h.symm) hb
  rw [le_antisymm_iff, le_antisymm_iff, norm_le_iff_valuation_le K φ hball a b hb,
    norm_le_iff_valuation_le K φ hball b a ha]

end GlobalTheory.EtaCompare

namespace GlobalTheory.EtaCompare

open WithZero

theorem eta_eq_uq_eta : ∀ (K : UQ) (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (φ : K.E ≃+* E),
    (∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) →
    ∀ x : F, GlobalTheory.JR.eta x = ((K.eta (φ.symm (algebraMap F E x)) : ℚ) : ℂ) := by
  intro K F E _ _ _ _ hU φ hball x
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E with hv
  have hn : ∀ t : F, ‖φ (φ.symm (algebraMap F E t))‖ = ‖t‖ := fun t => by
    rw [RingEquiv.apply_symm_apply, norm_algebraMap']
  have key : (∃ y : F, ‖x‖ = ‖y‖ ^ 2) ↔
      ∃ y : F, v (φ.symm (algebraMap F E x)) = v (φ.symm (algebraMap F E y)) ^ 2 := by
    refine exists_congr fun y => ?_
    rw [← hn x, ← hn y, ← norm_pow, ← map_pow φ, norm_eq_iff_valuation_eq K φ hball, map_pow]

  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  obtain ⟨p, hp⟩ := hU.unram (φ π)
  have hvp : v (φ.symm (algebraMap F E p)) = exp (-1) := by
    rw [← hπ]
    refine ((norm_eq_iff_valuation_eq K φ hball _ _).1 ?_)
    rw [hn, hp]
  unfold GlobalTheory.JR.eta UQ.eta val
  rw [key]
  rw [← hv]
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, WithZero.log_zero, neg_zero, zpow_zero, Rat.cast_one]
    rw [if_pos ⟨0, by simp⟩]
  set z := φ.symm (algebraMap F E x) with hz
  have hz0 : z ≠ 0 := by simpa [z] using hx
  have hvz : v z ≠ 0 := (Valuation.ne_zero_iff v).2 hz0
  set m := log (v z) with hm
  have hiff : (∃ y : F, v z = v (φ.symm (algebraMap F E y)) ^ 2) ↔ Even m := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨log (v (φ.symm (algebraMap F E y))), ?_⟩
      rw [hm, hy, log_pow, two_nsmul]
    · rintro ⟨l, hl⟩
      refine ⟨p ^ (-l), ?_⟩
      have hl' : log (v z) = l + l := hl
      rw [map_zpow₀, map_zpow₀, map_zpow₀, hvp, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_log hvz, hl']
      congr 1
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
  split_ifs with h
  · rw [Even.neg_one_zpow ((hiff.1 h).neg)]; simp
  · have ho : Odd (-m) := (Int.not_even_iff_odd.1 (fun he => h (hiff.2 (by simpa using he.neg))))
    rw [Odd.neg_one_zpow ho]; simp

end GlobalTheory.EtaCompare
end
end

section

open GlobalTheory.Prism

namespace GlobalTheory.BSP.LiftProj

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_mem {I J : Ideal A} {x y : Matrix n n A} (hx : ∀ i j, x i j ∈ I) (hy : ∀ i j, y i j ∈ J)
    (i j : n) : (x * y) i j ∈ I * J := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hx i k) (hy k j)

theorem mul_mem_right {I : Ideal A} {x : Matrix n n A} (y : Matrix n n A) (hx : ∀ i j, x i j ∈ I)
    (i j : n) : (x * y) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hx i k)

theorem mul_mem_left {I : Ideal A} {y : Matrix n n A} (x : Matrix n n A) (hy : ∀ i j, y i j ∈ I)
    (i j : n) : (x * y) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy k j)

theorem exists_idem (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (x : Matrix n n A)
    (hx : ∀ i j, (x * x - x) i j ∈ 𝔞) :
    ∃ e : Matrix n n A, e * e = e ∧ ∀ i j, (e - x) i j ∈ 𝔞 := by
  let f : ℕ → Matrix n n A := fun k => Nat.rec x (fun _ y => 3 * (y * y) - 2 * (y * y * y)) k
  have f0 : f 0 = x := rfl
  have fs : ∀ k, f (k + 1) = 3 * (f k * f k) - 2 * (f k * f k * f k) := fun k => rfl
  have h1 : ∀ k i j, (f k * f k - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa [f0] using hx
    | succ k ih =>
      have e : f (k + 1) * f (k + 1) - f (k + 1) =
          ((f k * f k - f k) * (f k * f k - f k)) * (4 * (f k * f k) - 4 * f k - 3) := by
        rw [fs]; noncomm_ring
      intro i j
      rw [e]
      refine mul_mem_right _ (fun i j => ?_) i j
      have := mul_mem ih ih i j
      rw [← pow_add] at this
      exact Ideal.pow_le_pow_right (by omega) this
  have h2 : ∀ k i j, (f (k + 1) - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k i j
    have e : f (k + 1) - f k = (f k * f k - f k) * (1 - 2 * f k) := by
      rw [fs]; noncomm_ring
    rw [e]
    exact mul_mem_right _ (h1 k) i j
  have h3 : ∀ k m, k ≤ m → ∀ i j, (f m - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => intro i j; simp
    | succ m hkm ih =>
      intro i j
      have e : f (m + 1) - f k = (f (m + 1) - f m) + (f m - f k) := by abel
      rw [e, Matrix.add_apply]
      exact add_mem (Ideal.pow_le_pow_right (by omega) (h2 m i j)) (ih i j)
  have h4 : ∀ i j, ∃ L : A, ∀ k, f k i j - L ∈ 𝔞 ^ k := by
    intro i j
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := 𝔞) (fun k => f k i j) (fun {k m} hkm => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
      exact Ideal.pow_le_pow_right (Nat.le_succ k) (h3 k m hkm i j))
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using h4
  let e : Matrix n n A := Matrix.of L
  have hL' : ∀ k i j, (f k - e) i j ∈ 𝔞 ^ k := fun k i j => hL i j k
  refine ⟨e, ?_, fun i j => ?_⟩
  · rw [← sub_eq_zero]
    ext i j
    refine IsHausdorff.haus' (I := 𝔞) _ fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have e1 : e * e - e = (f k * f k - f k) - ((f k - e) * (f k - 1) + e * (f k - e)) := by
      noncomm_ring
    rw [e1, Matrix.sub_apply, Matrix.add_apply]
    exact sub_mem (Ideal.pow_le_pow_right (Nat.le_succ k) (h1 k i j))
      (add_mem (mul_mem_right _ (hL' k) i j) (mul_mem_left _ (hL' k) i j))
  · have e1 : e - x = (f 1 - f 0) - (f 1 - e) := by rw [f0]; abel
    rw [e1, Matrix.sub_apply]
    have a := h2 0 i j
    have b := hL' 1 i j
    rw [zero_add, pow_one] at a
    rw [pow_one] at b
    exact sub_mem a b

theorem exists_idem_lift (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (y : Matrix n n (A ⧸ 𝔞))
    (hy : y * y = y) :
    ∃ e : Matrix n n A, e * e = e ∧ e.map (Ideal.Quotient.mk 𝔞) = y := by
  choose g hg using Ideal.Quotient.mk_surjective (I := 𝔞)
  have hxy : (y.map g).map (Ideal.Quotient.mk 𝔞) = y := by
    ext i j; simp [hg]
  obtain ⟨e, he, hex⟩ := exists_idem 𝔞 (y.map g) fun i j => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : (Ideal.Quotient.mk 𝔞).mapMatrix (y.map g * y.map g - y.map g) = 0 := by
      rw [map_sub, map_mul, RingHom.mapMatrix_apply, hxy, hy, sub_self]
    exact congrFun (congrFun this i) j
  refine ⟨e, he, ?_⟩
  ext i j
  have := (Ideal.Quotient.eq).2 (hex i j)
  simpa [hg] using this

theorem exists_lift : ∀ (A : Type) [CommRing A] (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (N : Type)
    [AddCommGroup N] [Module (A ⧸ 𝔞) N] [Module.Finite (A ⧸ 𝔞) N] [Module.Projective (A ⧸ 𝔞) N],
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module A P) (_ : Module.Finite A P)
      (_ : Module.Projective A P) (u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N), SemiBC u := by
  intro A _ 𝔞 _ N _ _ _ _
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' (A ⧸ 𝔞) N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  have hs' : ∀ z, p (s z) = z := fun z => LinearMap.congr_fun hs z
  obtain ⟨e, he, hey⟩ := exists_idem_lift 𝔞 (LinearMap.toMatrix' (s ∘ₗ p)) (by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    ext1 z
    ext1
    simp [hs'])
  let red : (Fin n → A) →ₛₗ[Ideal.Quotient.mk 𝔞] (Fin n → A ⧸ 𝔞) :=
    { toFun := fun z i => Ideal.Quotient.mk 𝔞 (z i)
      map_add' := fun a b => by ext i; simp
      map_smul' := fun a b => by ext i; simp }
  have red_surj : Function.Surjective red := fun z => by
    choose g hg using Ideal.Quotient.mk_surjective (I := 𝔞)
    exact ⟨fun i => g (z i), funext fun i => hg (z i)⟩
  let E : (Fin n → A) →ₗ[A] (Fin n → A) := Matrix.toLin' e
  have hEE : ∀ z, E (E z) = E z := fun z => by
    simp only [E, Matrix.toLin'_apply, Matrix.mulVec_mulVec, he]
  have hred : ∀ z, red (E z) = s (p (red z)) := fun z => by
    have h1 : s (p (red z)) = Matrix.toLin' (LinearMap.toMatrix' (s ∘ₗ p)) (red z) := by
      rw [Matrix.toLin'_toMatrix']; rfl
    rw [h1, ← hey]
    ext i
    simp [red, E, Matrix.mulVec, dotProduct]
  let P := LinearMap.range E
  let q : (Fin n → A) →ₗ[A] P := E.rangeRestrict
  have hq : ∀ y : P, q y = y := by
    rintro ⟨_, z, rfl⟩
    exact Subtype.ext (hEE z)
  have hproj : Module.Projective A P := Module.Projective.of_split P.subtype q (LinearMap.ext hq)
  let u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N := p.comp (red.comp P.subtype)
  have hu : ∀ y : P, u y = p (red y) := fun y => rfl
  have u_surj : Function.Surjective u := fun z => by
    obtain ⟨t, ht⟩ := red_surj (s z)
    refine ⟨q t, ?_⟩
    rw [hu]
    change p (red (E t)) = z
    rw [hred, ht, hs', hs']
  refine ⟨P, inferInstance, inferInstance, inferInstance, hproj, u, ?_⟩
  intro Q _ _ v
  let w0 : (Fin n → A ⧸ 𝔞) →ₗ[A ⧸ 𝔞] Q :=
    (Pi.basisFun (A ⧸ 𝔞) (Fin n)).constr ℕ fun i => v (q (Pi.single i 1))
  have hw0 : w0.comp red = v.comp q := by
    refine (Pi.basisFun A (Fin n)).ext fun i => ?_
    have : red (Pi.basisFun A (Fin n) i) = Pi.basisFun (A ⧸ 𝔞) (Fin n) i := by
      ext j
      by_cases h : j = i
      · subst h; simp [red]
      · simp [red, h]
    rw [LinearMap.comp_apply, this, LinearMap.comp_apply, Pi.basisFun_apply A]
    exact Module.Basis.constr_basis _ _ _ _
  have key : ∀ y : P, (w0 ∘ₗ s) (u y) = v y := fun y => by
    have h1 : E y = y := congrArg Subtype.val (hq y)
    rw [hu, LinearMap.comp_apply, ← hred, h1]
    have := LinearMap.congr_fun hw0 (y : Fin n → A)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hq] at this
    exact this
  refine ⟨w0 ∘ₗ s, key, fun w hw => ?_⟩
  ext z
  obtain ⟨y, rfl⟩ := u_surj z
  rw [hw, key]

end GlobalTheory.BSP.LiftProj
end

section

noncomputable section

open GlobalTheory.Prism

namespace GlobalTheory.BSP

def fracMap {A : Type} [CommRing A] {N P : Type} [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (S : Submonoid A) (L : P →ₗ[A] N) (s : ↥S) : P →ₗ[A] LocalizedModule S N where
  toFun y := LocalizedModule.mk (L y) s
  map_add' x y := by
    rw [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simp [mul_smul]⟩
  map_smul' c x := by
    rw [map_smul, RingHom.id_apply, LocalizedModule.smul'_mk]

theorem isLocalizedModule_fracMap {A : Type} [CommRing A] (t : A) {N P : Type} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (L : P →ₗ[A] N) (n : ℕ) (hk : ∀ y, L y = 0 → t ^ n • y = 0)
    (hc : ∀ x, ∃ y, L y = t ^ n • x) (s : ↥(Submonoid.powers t)) :
    IsLocalizedModule (Submonoid.powers t) (fracMap (Submonoid.powers t) L s) := by
  refine ⟨IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers t) N), ?_, ?_⟩
  · intro z
    induction z using LocalizedModule.induction_on with
    | _ m r =>
      obtain ⟨y, hy⟩ := hc m
      refine ⟨⟨(s : A) • y, r * ⟨t ^ n, n, rfl⟩⟩, ?_⟩
      change ((r : A) * t ^ n) • LocalizedModule.mk m r = LocalizedModule.mk (L ((s : A) • y)) s
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq, map_smul, hy]
      refine ⟨1, ?_⟩
      simp only [Submonoid.smul_def, smul_smul]
      congr 1
      ring
  · intro x y h
    change LocalizedModule.mk (L x) s = LocalizedModule.mk (L y) s at h
    rw [LocalizedModule.mk_eq] at h
    obtain ⟨c, h⟩ := h
    refine ⟨⟨t ^ n, n, rfl⟩ * (c * s), ?_⟩
    have h1 := hk (((c : A) * s) • (x - y)) (by
      rw [map_smul, map_sub, smul_sub, sub_eq_zero, mul_smul, mul_smul]
      exact h)
    rw [smul_smul, smul_sub, sub_eq_zero] at h1
    exact h1

theorem semiBC_localized (A : Type) [CommRing A] (φ : A →+* A) (t : A) (N : Type) [AddCommGroup N] [Module A N]
    (P : Type) [AddCommGroup P] [Module A P] (u : N →ₛₗ[φ] P) (hu : SemiBC u) (L : P →ₗ[A] N) (n a : ℕ)
    (hk : ∀ y, L y = 0 → t ^ n • y = 0) (hc : ∀ x, ∃ y, L y = t ^ n • x)
    (Φ : N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N)
    (hΦ : ∀ x, IsFrac t (Φ x) (L (u x)) a) : SemiBC Φ := by
  intro Q _ _ v
  letI : Module A Q := Module.compHom Q (algebraMap A (Localization.Away t))
  haveI : IsScalarTower A (Localization.Away t) Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let s : ↥(Submonoid.powers t) := ⟨t ^ a, a, rfl⟩
  haveI := isLocalizedModule_fracMap t L n hk hc s
  have hb := IsLocalizedModule.isBaseChange (Submonoid.powers t) (Localization.Away t)
    (fracMap (Submonoid.powers t) L s)
  have hΦ' : ∀ x, Φ x = fracMap (Submonoid.powers t) L s (u x) := hΦ
  let v' : N →ₛₗ[φ] Q :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun c x => v.map_smulₛₗ c x }
  obtain ⟨w₀, hw₀, hun⟩ := hu Q v'
  refine ⟨hb.lift w₀, fun x => ?_, fun w hw => ?_⟩
  · rw [hΦ', hb.lift_eq]
    exact hw₀ x
  · refine hb.algHom_ext _ _ fun y => ?_
    rw [hb.lift_eq, ← hun ((w.restrictScalars A).comp (fracMap (Submonoid.powers t) L s))
      fun x => (congrArg w (hΦ' x).symm).trans (hw x)]
    rfl

end GlobalTheory.BSP
end
end

section

open GlobalTheory.BK PowerSeries Filter Topology

namespace GlobalTheory.BK

theorem mem_invL_S_iff_tendsto (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] (f : K⟦X⟧) :
    f ∈ invL l (S O K e) ↔ Tendsto (fun n => ‖coeff n f‖ * wS K e n) atTop (𝓝 0) := by
  have h2 : (((l : S O K e) : K⟦X⟧)) = C (l : K) := by simp
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
  have key : ∀ m n : ℕ, ‖coeff n ((((l : S O K e) : K⟦X⟧)) ^ m * f)‖ * wS K e n =
      ‖(l : K)‖ ^ m * (‖coeff n f‖ * wS K e n) := fun m n => by
    rw [h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow, mul_assoc]
  constructor
  · rintro ⟨m, hm⟩
    have h := (mem_S.1 hm).2.const_mul (‖(l : K)‖ ^ m)⁻¹
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [key, inv_mul_cancel_left₀ (pow_pos hl m).ne']
  · intro hf
    obtain ⟨b, hb⟩ := hf.bddAbove_range
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (norm_l_lt_one (K := K) l)).mul_const b
    rw [zero_mul] at h
    obtain ⟨m, hm⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨m, mem_S.2 ⟨fun n => ?_, ?_⟩⟩
    · rw [key]
      exact (mul_le_mul_of_nonneg_left (hb ⟨n, rfl⟩) (pow_pos hl m).le).trans hm.le
    · have h3 := hf.const_mul (‖(l : K)‖ ^ m)
      rw [mul_zero] at h3
      exact h3.congr fun n => (key m n).symm

end GlobalTheory.BK
end
