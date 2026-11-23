module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle090
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle091
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerBlockEmbeddingConj
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle033

@[expose] public section

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.GramDiff

variable {E : Type} [CommRing E] (τ : E →+* E)

theorem cT_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    cT τ (A * B) = cT τ B * cT τ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_add {a b : ℕ} (A B : Matrix (Fin a) (Fin b) E) :
    cT τ (A + B) = cT τ A + cT τ B := by
  ext i j
  simp [cT]

theorem cT_zero {a b : ℕ} : cT τ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
  ext i j
  simp [cT]

theorem cT_neg {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) : cT τ (-A) = -cT τ A := by
  ext i j
  simp [cT]

theorem cT_smul {a b : ℕ} (c : E) (A : Matrix (Fin a) (Fin b) E) :
    cT τ (c • A) = τ c • cT τ A := by
  ext i j
  simp [cT]

theorem cT_cT (hτ : ∀ a, τ (τ a) = a) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    cT τ (cT τ A) = A := by
  ext i j
  simp [cT, hτ]

theorem cT_cross (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} {S : Matrix (Fin m) (Fin m) E} (hS : cT τ S = S)
    (x y : Matrix (Fin m) (Fin n) E) : cT τ (cT τ x * S * y) = cT τ y * S * x := by
  rw [cT_mul, cT_mul, cT_cT τ hτ, hS, Matrix.mul_assoc]

def hermSub (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) E) where
  carrier := {H | cT τ H = H}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [cT_add, ha, hb]
  zero_mem' := cT_zero τ
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [cT_neg, ha]

def diffMap (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E) (hS : cT τ S = S)
    (x : Matrix (Fin m) (Fin n) E) : Matrix (Fin m) (Fin n) E →+ hermSub τ n :=
  AddMonoidHom.mk'
    (fun y => ⟨cT τ y * S * x + cT τ x * S * y, by
      change cT τ (cT τ y * S * x + cT τ x * S * y) = cT τ y * S * x + cT τ x * S * y
      rw [cT_add, cT_cross τ hτ hS, cT_cross τ hτ hS, add_comm]⟩)
    (by
      intro a b
      apply Subtype.ext
      change cT τ (a + b) * S * x + cT τ x * S * (a + b) =
        (cT τ a * S * x + cT τ x * S * a) + (cT τ b * S * x + cT τ x * S * b)
      rw [cT_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add]
      abel)

theorem exists_trace_one {q : ℕ} {ε : ℤ} (h : ResAlg E τ q ε) : ∃ θ : E, θ + τ θ = 1 := by
  obtain ⟨u, hu, -⟩ := h.basis
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : (u - τ u) * τ v = -1 := by
    have := congrArg τ hv
    rw [map_mul, map_sub, h.inv, map_one] at this
    linear_combination -this
  have h2 : τ v = -v := by
    linear_combination (-(τ v)) * hv + v * h1
  refine ⟨u * v, ?_⟩
  rw [map_mul, h2]
  linear_combination hv

theorem diffMap_surjective {q : ℕ} {ε : ℤ} (h : ResAlg E τ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) E) (hS : cT τ S = S) (T : Matrix (Fin n) (Fin n) E)
    (x : Matrix (Fin m) (Fin n) E) (hT : IsUnit T.det) (hx : cT τ x * S * x = T) :
    Function.Surjective (diffMap τ h.inv S hS x) := by
  rintro ⟨H, hH⟩
  have hH' : cT τ H = H := hH
  obtain ⟨θ, hθ⟩ := exists_trace_one τ h
  have hW : cT τ x * S * (x * T⁻¹ * (θ • H)) = θ • H := by
    calc cT τ x * S * (x * T⁻¹ * (θ • H)) = (cT τ x * S * x) * T⁻¹ * (θ • H) := by
          simp only [Matrix.mul_assoc]
      _ = θ • H := by rw [hx, Matrix.mul_nonsing_inv T hT, Matrix.one_mul]
  refine ⟨x * T⁻¹ * (θ • H), ?_⟩
  apply Subtype.ext
  change cT τ (x * T⁻¹ * (θ • H)) * S * x + cT τ x * S * (x * T⁻¹ * (θ • H)) = H
  rw [← cT_cross τ h.inv hS x (x * T⁻¹ * (θ • H)), hW, cT_smul, hH', ← add_smul, add_comm, hθ, one_smul]

theorem card_fibre_mul {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] (f : A →+ B)
    (hf : Function.Surjective f) (b : B) : Nat.card {a // f a = b} * Nat.card B = Nat.card A := by
  obtain ⟨y, rfl⟩ := hf b
  have e : {a // f a = f y} ≃ f.ker :=
    { toFun := fun a => ⟨a.1 - y, by simp [AddMonoidHom.mem_ker, a.2]⟩
      invFun := fun k => ⟨k.1 + y, by
        have : f k.1 = 0 := k.2
        simp [this]⟩
      left_inv := fun a => by simp
      right_inv := fun k => by simp }
  have hi : f.ker.index = Nat.card B := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
  rw [Nat.card_congr e, ← hi]
  exact AddSubgroup.card_mul_index f.ker

theorem card_fibre_gram_differential : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E) (T : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin m) (Fin n) E) (H : Matrix (Fin n) (Fin n) E), cT τ S = S → cT τ T = T → IsUnit T.det → cT τ x * S * x = T → cT τ H = H → Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * x + cT τ x * S * y = H} = q ^ (2 * m * n - n ^ 2) := by
  intro E _ τ q ε h m n hnm S T x H hS _ hT hx hH
  have hq : 0 < q := lt_trans Nat.zero_lt_one h.one_lt
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [h.card]; positivity)
  have hM : Nat.card (Matrix (Fin m) (Fin n) E) = ((q ^ 2) ^ n) ^ m := by
    change Nat.card (Fin m → Fin n → E) = _
    rw [Nat.card_fun, Nat.card_fun, h.card]
    simp
  have hHerm : Nat.card (hermSub τ n) = q ^ (n ^ 2) := GlobalTheory.T.hermitian_matrices_card E τ q ε h n
  have hfib := card_fibre_mul (diffMap τ h.inv S hS x)
    (diffMap_surjective τ h S hS T x hT hx) ⟨H, hH⟩
  have hc : Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * x + cT τ x * S * y = H} =
      Nat.card {y // diffMap τ h.inv S hS x y = ⟨H, hH⟩} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [Subtype.ext_iff]
      rfl)
  have hle : n ^ 2 ≤ 2 * m * n := by nlinarith
  have hpow : ((q ^ 2) ^ n) ^ m = q ^ (n ^ 2) * q ^ (2 * m * n - n ^ 2) := by
    rw [← pow_add, Nat.add_sub_cancel' hle, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hc]
  rw [hHerm, hM, hpow, mul_comm] at hfib
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hq _) hfib

end GlobalTheory.CompanionTheory.UnrDens.GramDiff
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.GaussOne

variable {E : Type} [CommRing E] [Fintype E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

open scoped Classical in
open Classical in
theorem sum_fixed_eq_zero (χ : AddChar E ℂ) (A b : E) (hb : τ b = b) (hχ : χ (A * b) ≠ 1) :
    ∑ t ∈ Finset.univ.filter (fun t : E => τ t = t), χ (A * t) = 0 := by
  set S := ∑ t ∈ Finset.univ.filter (fun t : E => τ t = t), χ (A * t) with hS
  have key : χ (A * b) * S = S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_nbij' (fun t => t + b) (fun t => t - b) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [map_add (f := _), ht, hb]
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [map_sub, ht, hb]
    · intro t _
      simp
    · intro t _
      simp
    · intro t _
      rw [← AddChar.map_add_eq_mul, mul_add, add_comm]
  have h1 : (1 - χ (A * b)) * S = 0 := by rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hχ
  · exact h

open scoped Classical in
open Classical in
theorem card_filter_norm (t : E) :
    (((Finset.univ.filter (fun w : E => τ w * w = t)).card : ℕ) : ℤ) =
      (Nat.card {a : E // a * τ a = t} : ℤ) := by
  have hf : Finset.univ.filter (fun w : E => τ w * w = t) =
      Finset.univ.filter (fun a : E => a * τ a = t) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mul_comm]
  rw [hf, Nat.card_eq_fintype_card, Fintype.card_subtype]

open scoped Classical in
open Classical in
theorem gauss_core (h : ResAlg E τ q ε) (χ : AddChar E ℂ) (A b : E) (hb : τ b = b)
    (hχ : χ (A * b) ≠ 1) :
    ∑ w : E, χ (A * (τ w * w)) = (ε : ℂ) * q := by
  have hmap : ∀ w ∈ (Finset.univ : Finset E),
      τ w * w ∈ Finset.univ.filter (fun t : E => τ t = t) := by
    intro w _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, h.inv]
    exact mul_comm _ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hfib : ∀ t ∈ Finset.univ.filter (fun t : E => τ t = t),
      (∑ w ∈ Finset.univ.filter (fun w : E => τ w * w = t), χ (A * (τ w * w))) =
        (((q : ℂ) - ε) + if t = 0 then (q : ℂ) * ε else 0) * χ (A * t) := by
    intro t ht
    have ht' : τ t = t := (Finset.mem_filter.mp ht).2
    rw [Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2]), Finset.sum_const,
      nsmul_eq_mul]
    congr 1
    have hc := card_filter_norm (τ := τ) t
    have hc' : (((Finset.univ.filter (fun w : E => τ w * w = t)).card : ℕ) : ℂ) =
        ((Nat.card {a : E // a * τ a = t} : ℤ) : ℂ) := by
      rw [← hc]
      push_cast
      rfl
    rw [hc']
    by_cases h0 : t = 0
    · subst h0
      rw [GlobalTheory.T.norm_fibre_card_zero E τ q ε h, if_pos rfl]
      push_cast
      ring
    · rw [GlobalTheory.T.norm_fibre_card_nonzero E τ q ε h t ht' h0, if_neg h0]
      push_cast
      ring
  rw [Finset.sum_congr rfl hfib]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_fixed_eq_zero χ A b hb hχ, mul_zero, zero_add]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and,
    map_zero, if_true, mul_zero, AddChar.map_zero_eq_one, mul_one]
  ring

end GlobalTheory.CompanionTheory.SiegLoc.GaussOne

namespace GlobalTheory.CompanionTheory.SiegLoc

theorem gauss_level_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ)
    (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ),
    IsLevelChars σ ϖ ψ → ∀ (a : R), σ a = a → a ∉ lev ϖ 1 →
    (∑ w : R ⧸ lev ϖ 1, ψ 1 (Ideal.Quotient.mk (lev ϖ 1) a * (barσ σ ϖ hR.fix_ϖ 1 w * w))) =
      (ε : ℂ) * q := by
  intro R _ σ ϖ q ε hR _ ψ hψ a ha hna
  have hex : ∃ b, σ b = b ∧ ψ 1 (Ideal.Quotient.mk _ (a * b)) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hna (hψ.prim a ha hcon)
  obtain ⟨b, hb, hχ⟩ := hex
  refine GaussOne.gauss_core (GlobalTheory.T.residue_algebra_unramified R σ ϖ q ε hR) (ψ 1) _ (Ideal.Quotient.mk _ b) ?_ ?_
  · rw [barσ_mk, hb]
  · rwa [← map_mul]

end GlobalTheory.CompanionTheory.SiegLoc
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.Sphere

theorem card_fibre {E : Type} [CommRing E] {τ : E →+* E} [Fintype E] {V : Type} [AddCommGroup V]
    [Module E V] [Finite V] (B : HermSp E τ V) {w : V} (hw : IsUnit (B.h w w)) (c : E) :
    Nat.card {v : V // B.h v v = c} =
      ∑ a : E, Nat.card {v : B.perp w // (B.perpForm hw).h v v = c - a * τ a * B.h w w} := by
  rw [← Nat.card_sigma]
  refine Nat.card_congr ?_
  have e1 : {x : E × B.perp w // (B.perpForm hw).h x.2 x.2 = c - x.1 * τ x.1 * B.h w w} ≃
      {v : V // B.h v v = c} :=
    Equiv.subtypeEquiv (B.perpEquiv hw) (by
      rintro ⟨a, v⟩
      have hv : B.h (v : V) w = 0 := v.2
      simp only [HermSp.perpEquiv_apply, HermSp.perpForm_h]
      rw [B.norm_perp hv a]
      constructor
      · intro h; rw [h]; ring
      · intro h; rw [← h]; ring)
  exact e1.symm.trans
    ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun s => ⟨(s.1, s.2.1), s.2.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem sum_ite_card {E : Type} [Fintype E] (p : E → Prop) (A B₀ : ℝ) [DecidablePred p] :
    ∑ a, (if p a then B₀ else A) =
      (Nat.card {a // p a} : ℝ) * B₀ + ((Nat.card E : ℝ) - Nat.card {a // p a}) * A := by
  have h : ∀ a, (if p a then B₀ else A) = A + (B₀ - A) * (if p a then 1 else 0) := by
    intro a; split_ifs <;> ring
  simp only [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_univ, nsmul_eq_mul]
  ring

theorem arith_unit (q ε x Q : ℝ) (hq : q ≠ 0) :
    (q - ε) * (Q / q * (1 + (q - 1) * x)) + (q ^ 2 - (q - ε)) * (Q / q * (1 - x)) =
      Q * q ^ 2 / q * (1 - x * (ε / q)) := by
  field_simp
  ring

theorem arith_zero (q ε x Q : ℝ) (hq : q ≠ 0) :
    (q * (1 + ε) - ε) * (Q / q * (1 + (q - 1) * x)) +
        (q ^ 2 - (q * (1 + ε) - ε)) * (Q / q * (1 - x)) =
      Q * q ^ 2 / q * (1 + (q - 1) * (x * (ε / q))) := by
  field_simp
  ring

theorem count : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (∀ c : E, τ c = c → c ≠ 0 → (Nat.card {v : V // B.h v v = c} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m)) ∧ (Nat.card {v : V // B.h v v = 0} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) := by
  intro E _ τ q ε hR m
  have hq1 : 1 < q := hR.one_lt
  have hq0 : (q : ℝ) ≠ 0 := by
    have : 0 < q := by omega
    exact_mod_cast this.ne'
  induction m with
  | zero =>
    intro V _ _ B hc
    have hc1 : Nat.card V = 1 := by simpa using hc
    obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.1 hc1
    refine ⟨?_, ?_⟩
    · intro c _ hc0
      have : IsEmpty {v : V // B.h v v = c} :=
        ⟨fun x => hc0 (by
          have h := x.2
          rw [Subsingleton.elim x.1 0, B.zero_left] at h
          exact h.symm)⟩
      rw [Nat.card_of_isEmpty]
      simp
    · have : Subsingleton {v : V // B.h v v = 0} := inferInstance
      rw [Nat.card_of_subsingleton (⟨0, B.zero_left 0⟩ : {v : V // B.h v v = 0})]
      field_simp
      ring
  | succ m ih =>
    intro V _ _ B hc
    have hpow : 1 < q ^ (2 * (m + 1)) := Nat.one_lt_pow (by omega) hq1
    have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
    have hfinE : Finite E := Nat.finite_of_card_ne_zero (by
      rw [hR.card]; exact pow_ne_zero _ (by omega))
    have hnt : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨w, hw⟩ := GlobalTheory.T.hermitian_space_anisotropic_unit E τ q ε hR V B hnt
    have hP : Nat.card (B.perp w) = q ^ (2 * m) := by
      have h1 : Nat.card E * Nat.card (B.perp w) = Nat.card V := by
        rw [← Nat.card_prod]; exact Nat.card_congr (B.perpEquiv hw)
      rw [hR.card, hc] at h1
      have hq2 : 0 < q ^ 2 := pow_pos (by omega) _
      apply Nat.eq_of_mul_eq_mul_left hq2
      rw [h1]; ring
    obtain ⟨ihc, ihz⟩ := ih (B.perp w) (B.perpForm hw) hP
    classical
    haveI := Fintype.ofFinite E
    have hdfix : τ (B.h w w) = B.h w w := (B.symm w w).symm
    obtain ⟨di, hdi⟩ : ∃ di, B.h w w * di = 1 := hw.exists_right_inv
    have hdifix : τ di = di := by
      have h1 : B.h w w * τ di = 1 := by
        have := congrArg τ hdi
        rwa [map_mul, hdfix, map_one] at this
      calc τ di = (B.h w w * di) * τ di := by rw [hdi, one_mul]
        _ = di * (B.h w w * τ di) := by ring
        _ = di := by rw [h1, mul_one]
    set A : ℝ := (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m) with hA
    set B₀ : ℝ := (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) with hB₀
    have key : ∀ c : E, τ c = c → (Nat.card {v : V // B.h v v = c} : ℝ) =
        (Nat.card {a : E // a * τ a = c * di} : ℝ) * B₀ +
          ((q : ℝ) ^ 2 - Nat.card {a : E // a * τ a = c * di}) * A := by
      intro c hcf
      have hiff : ∀ a : E, a * τ a * B.h w w = c ↔ a * τ a = c * di := by
        intro a
        constructor
        · intro h
          rw [← h, mul_assoc, hdi, mul_one]
        · intro h
          rw [h, mul_assoc, mul_comm di, hdi, mul_one]
      have hterm : ∀ a : E,
          (Nat.card {v : B.perp w // (B.perpForm hw).h v v = c - a * τ a * B.h w w} : ℝ) =
            if a * τ a = c * di then B₀ else A := by
        intro a
        split_ifs with h
        · have h0 : c - a * τ a * B.h w w = 0 := by rw [(hiff a).2 h, sub_self]
          rw [h0]; exact ihz
        · refine ihc _ ?_ ?_
          · rw [map_sub, map_mul, map_mul, hcf, hdfix, hR.inv a]
            ring
          · intro h0
            exact h ((hiff a).1 (sub_eq_zero.1 h0).symm)
      rw [card_fibre B hw c]
      push_cast
      rw [Finset.sum_congr rfl (fun a _ => hterm a), sum_ite_card, hR.card]
      push_cast
      rfl
    have hpw : (q : ℝ) ^ (2 * (m + 1)) = (q : ℝ) ^ (2 * m) * (q : ℝ) ^ 2 := by ring
    refine ⟨?_, ?_⟩
    · intro c hcf hc0
      have hn : (Nat.card {a : E // a * τ a = c * di} : ℝ) = (q : ℝ) - ε := by
        have := GlobalTheory.T.norm_fibre_card_nonzero E τ q ε hR (c * di)
          (by rw [map_mul, hcf, hdifix])
          (by
            intro h0
            apply hc0
            calc c = c * (di * B.h w w) := by rw [mul_comm di, hdi, mul_one]
              _ = (c * di) * B.h w w := by ring
              _ = 0 := by rw [h0, zero_mul])
        exact_mod_cast this
      rw [key c hcf, hn, hpw, pow_succ ((ε : ℝ) / q) m]
      exact arith_unit _ _ _ _ hq0
    · have hn : (Nat.card {a : E // a * τ a = (0 : E) * di} : ℝ) = (q : ℝ) * (1 + ε) - ε := by
        have := GlobalTheory.T.norm_fibre_card_zero E τ q ε hR
        rw [zero_mul]
        exact_mod_cast this
      rw [key 0 (map_zero τ), hn, hpw, pow_succ ((ε : ℝ) / q) m]
      exact arith_zero _ _ _ _ hq0

end GlobalTheory.CompanionTheory.UnrDens.Sphere
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.inverse_transform_holomorphic_lines : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ (g : T) (p v : ℂ × ℂ), Differentiable ℂ (fun τ : ℂ => inv (fun t => φ t g) (p + τ • v)) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line | exact GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line <;> assumption)
end

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.whittaker_column_recursion : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ), j < d →
    (patSet (K := K) (colGe d j)).ncard = Fintype.card K ^ j * (patSet (K := K) (colGe d (j + 1))).ncard →
    (∀ x : Fin j → K, (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0) →
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ χ = ∑ r : Fin j → K, wh (colGe d j) (colGeR K d j r) ψ₀ χ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum <;> assumption)
end

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.whittaker_block_embedding_conj : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) (g : GL (Fin j) K) (h : GL (Fin d) K) (r : Fin j → K),
    j < d → (∀ x y, χ (x * y * x⁻¹) = χ y) →
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) →
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) →
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeR K d j (Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K))) ψ₀ χ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj <;> assumption)
end
