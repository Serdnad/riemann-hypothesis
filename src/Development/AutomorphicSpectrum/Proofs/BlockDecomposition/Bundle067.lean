module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle033

@[expose] public section

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.NormZero

variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

abbrev Fx (τ : E →+* E) : Type := {a : E // τ a = a}

def zeroFx (τ : E →+* E) : Fx τ := ⟨0, map_zero τ⟩

theorem finite_of_resAlg (h : ResAlg E τ q ε) : Finite E := by
  apply Nat.finite_of_card_ne_zero
  rw [h.card]
  have := h.one_lt
  positivity

theorem nontrivial_of_resAlg (h : ResAlg E τ q ε) : Nontrivial E := by
  haveI := finite_of_resAlg h
  apply Finite.one_lt_card_iff_nontrivial.1
  rw [h.card]
  have := h.one_lt
  nlinarith

theorem card_fx (h : ResAlg E τ q ε) : Nat.card (Fx τ) = q := by
  obtain ⟨u, hu, hb⟩ := h.basis
  let φ : Fx τ × Fx τ → E := fun p => (p.1 : E) + (p.2 : E) * u
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
      have h1 : x + y * u = x' + y' * u := hxy
      have h2 : x + y * τ u = x' + y' * τ u := by
        have := congrArg τ h1
        simpa [hx, hy, hx', hy'] using this
      have h3 : (y - y') * (u - τ u) = 0 := by linear_combination h1 - h2
      have h4 : y = y' := sub_eq_zero.1 (hu.mul_left_eq_zero.1 h3)
      have h5 : x = x' := by
        subst h4
        exact add_right_cancel h1
      subst h4 h5
      rfl
    · intro a
      obtain ⟨x, y, hx, hy, rfl⟩ := hb a
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have h1 : Nat.card (Fx τ × Fx τ) = Nat.card E := Nat.card_congr (Equiv.ofBijective φ hφ)
  rw [Nat.card_prod, h.card] at h1
  have h2 : Nat.card (Fx τ) ^ 2 = q ^ 2 := by rw [← h1]; ring
  exact (Nat.pow_left_inj (by norm_num)).1 h2

theorem exists_idem (h : ResAlg E τ q ε) (hf : ¬ IsField E) :
    ∃ e : E, e * e = e ∧ τ e = 1 - e := by
  haveI := nontrivial_of_resAlg h
  obtain ⟨a, ha0, hau⟩ : ∃ a : E, a ≠ 0 ∧ ¬ IsUnit a := by
    by_contra hc
    push_neg at hc
    refine hf ⟨exists_pair_ne E, mul_comm, fun {a} ha => ?_⟩
    obtain ⟨b, hb⟩ := (hc a ha).exists_right_inv
    exact ⟨b, hb⟩
  obtain ⟨u, hu, -⟩ := h.basis
  have hN : a * τ a = 0 := by
    by_contra hN
    have hfix : τ (a * τ a) = a * τ a := by rw [map_mul, h.inv, mul_comm]
    exact hau (isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hN))
  have htfix : τ (a + τ a) = a + τ a := by rw [map_add (f := _), h.inv, add_comm]
  by_cases ht : a + τ a = 0
  · exfalso
    have hτa : τ a = -a := by linear_combination ht
    have hfix : τ (a * (u - τ u)) = a * (u - τ u) := by
      rw [map_mul, map_sub, h.inv, hτa]
      ring
    have hne : a * (u - τ u) ≠ 0 := fun h0 => ha0 (hu.mul_left_eq_zero.1 h0)
    exact hau (isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hne))
  · obtain ⟨s, hs⟩ := (h.fixedUnit _ htfix ht).exists_right_inv
    have hτs : τ s = s := by
      have h1 : (a + τ a) * τ s = 1 := by
        have := congrArg τ hs
        rwa [map_mul, htfix, map_one] at this
      calc τ s = (s * (a + τ a)) * τ s := by rw [mul_comm s, hs, one_mul]
        _ = s * ((a + τ a) * τ s) := by ring
        _ = s := by rw [h1, mul_one]
    have hτe : τ (a * s) = 1 - a * s := by
      rw [map_mul, hτs]
      linear_combination hs
    refine ⟨a * s, ?_, hτe⟩
    linear_combination (-(s * s)) * hN + (a * s) * hs

theorem card_axes {F : Type} [Finite F] (z : F) :
    Nat.card {p : F × F // p.1 = z ∨ p.2 = z} + 1 = 2 * Nat.card F := by
  classical
  haveI := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : (Finset.univ.filter fun p : F × F => p.1 = z ∨ p.2 = z)
      = (({z} : Finset F) ×ˢ (Finset.univ : Finset F)) ∪ ((Finset.univ : Finset F) ×ˢ ({z} : Finset F)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, and_true, true_and]
  have h2 : (({z} : Finset F) ×ˢ (Finset.univ : Finset F)) ∩ ((Finset.univ : Finset F) ×ˢ ({z} : Finset F))
      = {(z, z)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true,
      true_and, Prod.mk.injEq]
  have h3 := Finset.card_union_add_card_inter (({z} : Finset F) ×ˢ (Finset.univ : Finset F))
    ((Finset.univ : Finset F) ×ˢ ({z} : Finset F))
  rw [h2] at h3
  rw [h1]
  simp only [Finset.card_product, Finset.card_singleton, Finset.card_univ, one_mul, mul_one] at h3
  omega

theorem card_zero_split (h : ResAlg E τ q ε) {e : E} (he : e * e = e) (hτ : τ e = 1 - e) :
    Nat.card {a : E // a * τ a = 0} + 1 = 2 * q := by
  have hτf : τ (1 - e) = e := by rw [map_sub, map_one, hτ]; ring
  let g : Fx τ × Fx τ → E := fun p => (p.1 : E) * e + (p.2 : E) * (1 - e)
  have hnorm : ∀ p, g p * τ (g p) = (p.1 : E) * (p.2 : E) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    show (x * e + y * (1 - e)) * τ (x * e + y * (1 - e)) = x * y
    rw [map_add (f := _), map_mul, map_mul, hx, hy, hτ, hτf]
    linear_combination (2 * x * y - x ^ 2 - y ^ 2) * he
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
      have h1 : x * e + y * (1 - e) = x' * e + y' * (1 - e) := hxy
      have h2 : x * (1 - e) + y * e = x' * (1 - e) + y' * e := by
        have := congrArg τ h1
        simpa only [map_add (f := _), map_mul, hx, hy, hx', hy', hτ, hτf] using this
      have hxe : x * e = x' * e := by
        linear_combination e * h1 + (y - y' - x + x') * he
      have hye : y * e = y' * e := by
        linear_combination e * h2 + (x - x' - y + y') * he
      have h5 : x = x' := by linear_combination h2 + hxe - hye
      have h6 : y = y' := by linear_combination h1 - hxe + hye
      subst h5 h6
      rfl
    · intro a
      refine ⟨(⟨a * e + τ a * (1 - e), ?_⟩, ⟨a * (1 - e) + τ a * e, ?_⟩), ?_⟩
      · rw [map_add (f := _), map_mul, map_mul, h.inv, hτ, hτf]; ring
      · rw [map_add (f := _), map_mul, map_mul, h.inv, hτ, hτf]; ring
      · show (a * e + τ a * (1 - e)) * e + (a * (1 - e) + τ a * e) * (1 - e) = a
        linear_combination (2 * a - 2 * τ a) * he
  have hz : ∀ p : Fx τ × Fx τ, (p.1 = zeroFx τ ∨ p.2 = zeroFx τ) ↔ g p * τ (g p) = 0 := by
    intro p
    rw [hnorm]
    constructor
    · rintro (h0 | h0)
      · rw [h0]; simp [zeroFx]
      · rw [h0]; simp [zeroFx]
    · intro h0
      by_cases hx : (p.1 : E) = 0
      · exact Or.inl (Subtype.ext hx)
      · exact Or.inr (Subtype.ext ((h.fixedUnit _ p.1.2 hx).mul_right_eq_zero.1 h0))
  have hcard : Nat.card {p : Fx τ × Fx τ // p.1 = zeroFx τ ∨ p.2 = zeroFx τ}
      = Nat.card {a : E // a * τ a = 0} :=
    Nat.card_congr ((Equiv.ofBijective g hg).subtypeEquiv hz)
  haveI := finite_of_resAlg h
  rw [← hcard, card_axes, card_fx h]

theorem card_norm_zero : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    (Nat.card {a : E // a * τ a = 0} : ℤ) = q * (1 + ε) - ε := by
  intro E _ τ q ε h
  rcases h.eps with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
  · haveI : IsDomain E := hf.isDomain
    have hu : ∀ a : {a : E // a * τ a = 0}, a = ⟨0, by simp⟩ := by
      rintro ⟨a, ha⟩
      apply Subtype.ext
      rcases mul_eq_zero.1 ha with h0 | h0
      · exact h0
      · have := h.inv a
        rw [h0, map_zero] at this
        exact this.symm
    have h1 : Nat.card {a : E // a * τ a = 0} = 1 := by
      haveI : Unique {a : E // a * τ a = 0} := ⟨⟨⟨0, by simp⟩⟩, hu⟩
      exact Nat.card_unique
    rw [h1]
    simp
  · obtain ⟨e, he, hτ⟩ := exists_idem h hf
    have h1 := card_zero_split h he hτ
    have h2 : (Nat.card {a : E // a * τ a = 0} : ℤ) + 1 = 2 * q := by exact_mod_cast h1
    linarith

end GlobalTheory.CompanionTheory.UnrDens.NormZero
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem exists_trace_ne_zero {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
    (hE : ResAlg E τ q ε) {a : E} (ha : a ≠ 0) : ∃ c : E, c * a + τ (c * a) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, hu, -⟩ := hE.basis
  have h1 := hcon 1
  have h2 := hcon u
  simp only [one_mul, map_mul] at h1 h2
  have hta : τ a = -a := by linear_combination h1
  rw [hta] at h2
  obtain ⟨w', hw'⟩ := hu.exists_left_inv
  apply ha
  linear_combination w' * h2 - a * hw'

theorem exists_unit_norm (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ)
    (hE : ResAlg E τ q ε) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V)
    (hV : Nontrivial V) : ∃ w : V, IsUnit (B.h w w) := by
  have key : ∀ w : V, B.h w w ≠ 0 → IsUnit (B.h w w) := fun w hw =>
    hE.fixedUnit _ (B.self_fixed hE.inv w) hw
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hex : ∃ w, B.h v w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (B.nondeg v hcon)
  obtain ⟨w, hvw⟩ := hex
  obtain ⟨c, hc⟩ := exists_trace_ne_zero hE hvw
  by_cases hww : B.h w w = 0
  · by_cases hvv : B.h v v = 0
    · refine ⟨w + c • v, key _ ?_⟩
      have expand : B.h (w + c • v) (w + c • v) = c * B.h v w + τ (c * B.h v w) := by
        rw [B.add_left, B.add_right, B.add_right, B.smul_left, B.smul_left, B.smul_right,
          B.smul_right, hww, hvv, B.symm v w, map_mul]
        ring
      rw [expand]
      exact hc
    · exact ⟨v, key v hvv⟩
  · exact ⟨w, key w hww⟩

end GlobalTheory.CompanionTheory.UnrDens
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.LevelId

variable {R : Type} [CommRing R]

theorem cT_mul (σ : R →+* R) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    cT σ (x * y) = cT σ y * cT σ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_cT (σ : R →+* R) (h : ∀ a, σ (σ a) = a) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    cT σ (cT σ x) = x := by
  ext i j
  exact h (x i j)

theorem cT_sub (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x - y) = cT σ x - cT σ y := by
  ext i j
  exact map_sub σ (x j i) (y j i)

theorem red_mul (ϖ : R) (k : ℕ) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    red ϖ k (x * y) = red ϖ k x * red ϖ k y := by
  unfold red
  exact Matrix.map_mul

theorem red_sub (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x - y) = red ϖ k x - red ϖ k y := by
  ext i j
  exact map_sub (Ideal.Quotient.mk (lev ϖ k)) (x i j) (y i j)

theorem red_neg (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (-x) = - red ϖ k x := by
  ext i j
  exact map_neg (Ideal.Quotient.mk (lev ϖ k)) (x i j)

theorem red_cT (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (cT σ x) = cT (barσ σ ϖ h k) (red ϖ k x) := by
  ext i j
  exact (barσ_mk σ ϖ h k (x j i)).symm

theorem red_surj (ϖ : R) (k : ℕ) {a b : ℕ} :
    Function.Surjective (red ϖ k : Matrix (Fin a) (Fin b) R → _) := by
  intro y
  refine ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (y i j)).choose, ?_⟩
  ext i j
  exact (Ideal.Quotient.mk_surjective (y i j)).choose_spec

theorem red_gram (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R) :
    red ϖ k (cT σ x * S * x) = cT (barσ σ ϖ h k) (red ϖ k x) * red ϖ k S * red ϖ k x := by
  rw [red_mul, red_mul, red_cT σ ϖ h]

theorem image_sol (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) :
    red ϖ k '' {x : Matrix (Fin m) (Fin n) R | red ϖ k (cT σ x * S * x) = red ϖ k T} =
      {y | cT (barσ σ ϖ h k) y * red ϖ k S * y = red ϖ k T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show cT (barσ σ ϖ h k) (red ϖ k x) * red ϖ k S * red ϖ k x = red ϖ k T
    rw [← red_gram σ ϖ h]
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := red_surj ϖ k y
    refine ⟨x, ?_, rfl⟩
    show red ϖ k (cT σ x * S * x) = red ϖ k T
    rw [red_gram σ ϖ h]
    exact hy

theorem gram_sub_mem (σ : R →+* R) (ϖ : R) (hinv : ∀ a, σ (σ a) = a) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : cT σ S = S) (hT : cT σ T = T)
    (y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) :
    cT (barσ σ ϖ h k) y * red ϖ k S * y - red ϖ k T ∈ hermMod σ ϖ n k := by
  obtain ⟨x, rfl⟩ := red_surj ϖ k y
  unfold hermMod
  refine ⟨cT σ x * S * x - T, ?_, ?_⟩
  · show cT σ (cT σ x * S * x - T) = cT σ x * S * x - T
    rw [cT_sub, cT_mul, cT_mul, cT_cT σ hinv, hS, hT, Matrix.mul_assoc]
  · show red ϖ k (cT σ x * S * x - T) = _
    rw [red_sub, red_gram σ ϖ h]

theorem neg_mem_herm (σ : R →+* R) (ϖ : R) (n k : ℕ) {B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)}
    (hB : B ∈ hermMod σ ϖ n k) : -B ∈ hermMod σ ϖ n k := by
  unfold hermMod at hB ⊢
  obtain ⟨h0, hh, rfl⟩ := hB
  refine ⟨-h0, ?_, red_neg ϖ k h0⟩
  show cT σ (-h0) = -h0
  have hh' : cT σ h0 = h0 := hh
  ext i j
  have e : σ (h0 j i) = h0 i j := congrFun (congrFun hh' i) j
  show σ (-(h0 j i)) = -(h0 i j)
  rw [map_neg, e]

theorem nuAt_neg (ϖ : R) {n k : ℕ} (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :
    nuAt ϖ (-B) = nuAt ϖ B := by
  unfold nuAt
  have hset : (Set.range fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x (-B)) =
      Set.range fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x B := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      show Matrix.vecMul (-x) B = Matrix.vecMul x (-B)
      rw [Matrix.neg_vecMul, Matrix.vecMul_neg]
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      show Matrix.vecMul (-x) (-B) = Matrix.vecMul x B
      rw [Matrix.neg_vecMul, Matrix.vecMul_neg, neg_neg]
  rw [hset]

end GlobalTheory.CompanionTheory.SiegLoc.LevelId


open GlobalTheory.CompanionTheory.SiegLoc.LevelId in
theorem GlobalTheory.CompanionTheory.SiegLoc.level_identity : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (m n k : ℕ) (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), cT σ S = S → cT σ T = T → (∀ Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k), Y ∈ hermMod σ ϖ n k → (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧ (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0)) → (∀ B ∈ hermMod σ ϖ n k, (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) = (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B))) → siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ S T k : ℝ) : ℂ) := by
  intro R _ σ ϖ q ε hR _ ψ hψ m n k S T hS hT horth hgauss
  classical
  have : Fintype ↥(hermMod σ ϖ n k) := Fintype.ofFinite _
  have hx : ∀ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
      (∑' B : hermMod σ ϖ n k,
        ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x - red ϖ k T)))) =
        if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then
          (Nat.card (hermMod σ ϖ n k) : ℂ) else 0 := by
    intro x
    have hmem := gram_sub_mem σ ϖ hR.inv hR.fix_ϖ k S T hS hT x
    by_cases hxe : cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T
    · rw [if_pos hxe]
      exact (horth _ hmem).1 (sub_eq_zero.mpr hxe)
    · rw [if_neg hxe]
      exact (horth _ hmem).2 (sub_ne_zero.mpr hxe)
  have hsplit : ∀ (B : hermMod σ ϖ n k) (x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)),
      ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x - red ϖ k T))) =
        ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
          ψ k (-Matrix.trace (B.1 * red ϖ k T)) := by
    intro B x
    rw [Matrix.mul_sub, Matrix.trace_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hsol : (solCount σ ϖ S T k : ℂ) = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
      if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0 := by
    unfold solCount
    rw [image_sol σ ϖ hR.fix_ϖ k S T, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.natCast_card_filter]
    exact Finset.sum_congr rfl fun x _ => if_congr Iff.rfl rfl rfl
  have h1 : ∀ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), (Nat.card (hermMod σ ϖ n k) : ℂ) *
      (if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0) =
      ∑ B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
        ψ k (-Matrix.trace (B.1 * red ϖ k T)) := by
    intro x
    rw [mul_ite, mul_one, mul_zero, ← hx x, tsum_fintype]
    exact Finset.sum_congr rfl fun B _ => hsplit B x
  have hcount : (Nat.card (hermMod σ ϖ n k) : ℂ) * (solCount σ ϖ S T k : ℂ) =
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) *
        ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
          ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    calc (Nat.card (hermMod σ ϖ n k) : ℂ) * (solCount σ ϖ S T k : ℂ)
        = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), (Nat.card (hermMod σ ϖ n k) : ℂ) *
            (if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0) := by
          rw [hsol, Finset.mul_sum]
      _ = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ∑ B : hermMod σ ϖ n k,
            ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
              ψ k (-Matrix.trace (B.1 * red ϖ k T)) := Finset.sum_congr rfl fun x _ => h1 x
      _ = ∑ B : hermMod σ ϖ n k, ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
            ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
              ψ k (-Matrix.trace (B.1 * red ϖ k T)) := Finset.sum_comm
      _ = ∑ B : hermMod σ ϖ n k, (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) *
            (ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
              ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1)) := by
          refine Finset.sum_congr rfl fun B _ => ?_
          rw [← Finset.sum_mul, hgauss B.1 B.2]
          ring
      _ = _ := by rw [Finset.mul_sum]
  have hneg : ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) =
      ∑ B : hermMod σ ϖ n k, ψ k (Matrix.trace (red ϖ k T * B.1)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    let e : hermMod σ ϖ n k ≃ hermMod σ ϖ n k :=
      { toFun := fun B => ⟨-B.1, neg_mem_herm σ ϖ n k B.2⟩
        invFun := fun B => ⟨-B.1, neg_mem_herm σ ϖ n k B.2⟩
        left_inv := fun B => Subtype.ext (neg_neg _)
        right_inv := fun B => Subtype.ext (neg_neg _) }
    refine Fintype.sum_equiv e _ _ fun B => ?_
    show _ = ψ k (Matrix.trace (red ϖ k T * -B.1)) *
      ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ (-B.1))
    rw [nuAt_neg, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
  have hfin : siegAt ϖ σ ψ q ε m T k = ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    unfold siegAt
    rw [tsum_fintype, hneg]
  have hM : (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcast : ((densAt σ ϖ S T k : ℝ) : ℂ) = (solCount σ ϖ S T k : ℂ) * (Nat.card (hermMod σ ϖ n k) : ℂ) /
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) := by
    unfold densAt
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_natCast,
      Complex.ofReal_natCast]
  rw [hfin, hcast, eq_div_iff hM]
  linear_combination (-1 : ℂ) * hcount
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.power_divisibility_root_extraction : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := by
  first | exact @GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow | exact GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow | (intros; apply GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow <;> assumption)
end
