module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle028
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle027
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Transitivity
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

noncomputable section

open scoped UpperHalfPlane
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Sieg.EisQ

theorem ee_int_mul' (n : ℤ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  simp only [ee, ← Complex.exp_int_mul]; congr 1; ring

theorem hasSum_point {M : ℕ} (hM : 0 < M) (a A e : ℤ) (w : ℤ → ℤ → ℂ) :
    HasSum (fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0)
      (if A ≡ a [ZMOD M] then w A e else 0) := by
  have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  split_ifs with h
  · obtain ⟨n, hn⟩ := h.symm.dvd
    have hA : a + M * n = A := by linarith
    have := hasSum_single (f := fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0)
      (n, e) (fun p hp => by
        rw [if_neg]
        rintro ⟨h1, h2⟩
        apply hp
        refine Prod.ext ?_ h1
        apply mul_left_cancel₀ hM'
        simp only
        linarith)
    simpa [hA] using this
  · have : (fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0) = fun _ => 0 := by
      funext p
      rw [if_neg]
      rintro ⟨-, h2⟩
      exact h (Int.ModEq.symm (Int.modEq_iff_dvd.2 ⟨p.1, by linarith⟩))
    rw [this]
    exact hasSum_zero

theorem sum_div_point {m : ℕ} (hm : m ≠ 0) (A e : ℤ) (v : ℂ) :
    ∑ d ∈ m.divisors, ((if e = (d : ℤ) ∧ A = ((m / d : ℕ) : ℤ) then v else 0) +
      (if e = -(d : ℤ) ∧ A = -((m / d : ℕ) : ℤ) then v else 0)) = if A * e = m then v else 0 := by
  have key : ∀ d ∈ m.divisors, (((m / d : ℕ) : ℤ)) * d = m ∧ 0 < (d : ℤ) := fun d hd => by
    refine ⟨?_, by exact_mod_cast Nat.pos_of_mem_divisors hd⟩
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  split_ifs with h
  · have hd : e.natAbs ∈ m.divisors := by
      rw [Nat.mem_divisors]
      refine ⟨?_, hm⟩
      rw [← Int.natCast_dvd_natCast, Int.natAbs_dvd]
      exact ⟨A, by rw [← h, mul_comm]⟩
    rw [Finset.sum_eq_single_of_mem _ hd]
    · obtain ⟨k1, k2⟩ := key _ hd
      generalize ((m / e.natAbs : ℕ) : ℤ) = B at *
      rcases Int.natAbs_eq e with he | he
      · rw [← he] at k1 k2 ⊢
        have : A = B := mul_right_cancel₀ k2.ne' (by rw [h, k1])
        rw [if_pos ⟨rfl, this⟩, if_neg (by omega), add_zero]
      · have he' : (e.natAbs : ℤ) = -e := by omega
        rw [he'] at k1 k2 ⊢
        have : A = -B := mul_right_cancel₀ (b := e) (by omega) (by rw [h, ← k1]; ring)
        rw [if_neg (by omega), if_pos ⟨by ring, this⟩, zero_add]
    · intro d _ hne
      rw [if_neg (by omega), if_neg (by omega), add_zero]
  · refine Finset.sum_eq_zero fun d hd => ?_
    obtain ⟨k1, k2⟩ := key _ hd
    rw [if_neg, if_neg, add_zero]
    · rintro ⟨h1, h2⟩
      exact h (by rw [h1, h2, ← k1]; ring)
    · rintro ⟨h1, h2⟩
      exact h (by rw [h1, h2, ← k1])

theorem fTerm_eq (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) (τ : ℍ) (p : ℤ × ℤ) :
    fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ p =
      if 0 < (a + M * p.1) * p.2 then
        (Int.sign p.2 : ℂ) * (((a + M * p.1 : ℤ) : ℂ) / M) ^ (j - 1) * ee (1 / (M : ℂ)) ^ (b * p.2) *
          ee ((((a + M * p.1) * p.2 : ℤ) : ℂ) * τ / M)
      else 0 := by
  have hQ : (0 : ℚ) < M := by exact_mod_cast hM
  have hC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hc : (0 < ((a : ℚ) / M + p.1) * p.2) ↔ 0 < (a + M * p.1) * p.2 := by
    have : ((a : ℚ) / M + p.1) * p.2 = (((a + M * p.1) * p.2 : ℤ) : ℚ) / M := by
      push_cast; field_simp
    rw [this, div_pos_iff_of_pos_right hQ, Int.cast_pos]
  unfold fTerm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  split_ifs with h
  · rw [← ee_int_mul', mul_right_comm]
    congr 1
    · congr 1
      · congr 2
        push_cast; field_simp
      · congr 1
        push_cast; ring
    · congr 1
      push_cast; field_simp
  · rfl

theorem hasSum_fibre (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) (τ : ℍ) (m : ℕ) :
    HasSum (Set.indicator ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m})
        (fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ))
      ((if m = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b m) *
        Complex.exp (2 * Real.pi * Complex.I * m * τ / M)) := by
  split_ifs with hm
  · have : Set.indicator ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m})
        (fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ) = fun _ => 0 := by
      funext p
      rw [Set.indicator_apply_eq_zero]
      intro hp
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
      rw [fTerm_eq j hM, if_neg (by omega)]
    rw [this, zero_mul]
    exact hasSum_zero
  · set E := Complex.exp (2 * Real.pi * Complex.I * m * τ / M) with hE
    let w : ℤ → ℤ → ℂ := fun A e => (Int.sign e : ℂ) * ((A : ℂ) / M) ^ (j - 1) * ee (1 / (M : ℂ)) ^ (b * e) * E
    have h1 := hasSum_sum (s := m.divisors) fun d _ =>
      (hasSum_point hM a ((m / d : ℕ) : ℤ) (d : ℤ) w).add (hasSum_point hM a (-((m / d : ℕ) : ℤ)) (-(d : ℤ)) w)
    convert (preTransparency := .reducible) h1 using 1
    · funext p
      classical
      rw [sum_div_point hm, Set.indicator_apply, fTerm_eq j hM]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      by_cases h : (a + M * p.1) * p.2 = m
      · rw [if_pos (by omega), if_pos (by omega), if_pos h, h]
        simp only [w, hE, ee]
        congr 2
        push_cast; ring
      · rw [if_neg (by omega), if_neg h]
    · unfold coefPos
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have s1 : Int.sign (d : ℤ) = 1 := Int.sign_eq_one_of_pos hd'
      simp only [w, Int.sign_neg, s1, mul_neg, Int.cast_neg, Int.cast_one, Int.cast_natCast, neg_div]
      split_ifs <;> ring

theorem fract_eq {M : ℕ} (a : ℤ) : Int.fract ((a : ℚ) / M) = frc M a := by
  unfold frc
  exact Int.fract_div_intCast_eq_div_intCast_mod

theorem eisensteinFxConstantTerm_rationalIndex_eq (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    f0 j ![(a : ℚ) / M, (b : ℚ) / M] = const0 j M (ee (1 / (M : ℂ))) a b := by
  have hQ : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have h0 : frc M a = 0 ↔ (M : ℤ) ∣ a := by
    unfold frc
    rw [div_eq_zero_iff, or_iff_left hQ, Int.cast_eq_zero, Int.dvd_iff_emod_eq_zero]
  have he : ee ((((b : ℚ) / M : ℚ)) : ℂ) = ee (1 / (M : ℂ)) ^ b := by
    rw [← ee_int_mul']; congr 1; push_cast; ring
  unfold f0 const0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fract_eq, h0, he]
  split_ifs
  · rfl
  · push_cast; ring
  · push_cast; ring

theorem hasQ_F (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    HasQ M (F j ![(a : ℚ) / M, (b : ℚ) / M]) (eisF j M (ee (1 / (M : ℂ))) a b) := by
  have h1 : HasQ M (fun τ => ∑' p : ℤ × ℤ, fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ p)
      (fun m => if m = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b m) := fun τ => by
    have := (Model.summable_fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ).hasSum.tsum_fiberwise
      (fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat)
    have e : ∀ m : ℕ, ∑' q : ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m}),
        fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ q = _ := fun m => by
      rw [tsum_subtype, (hasSum_fibre j hM a b τ m).tsum_eq]
    simpa only [e] using this
  have h2 := (HasQ.const M (f0 j ![(a : ℚ) / M, (b : ℚ) / M])).add h1
  have e : eisF j M (ee (1 / (M : ℂ))) a b = fun n => (if n = 0 then f0 j ![(a : ℚ) / M, (b : ℚ) / M] else 0) +
      (if n = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b n) := by
    funext n
    unfold eisF
    split_ifs
    · rw [eisensteinFxConstantTerm_rationalIndex_eq j hM, add_zero]
    · rw [zero_add]
  rw [e]
  exact h2

theorem hasQ_cF_weight (c j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    HasQ M (cF c j ![(a : ℚ) / M, (b : ℚ) / M]) (smF (c : ℤ) j M (ee (1 / (M : ℂ))) a b) := by
  have hx : c • ![(a : ℚ) / M, (b : ℚ) / M] = ![(((c : ℤ) * a : ℤ) : ℚ) / M, (((c : ℤ) * b : ℤ) : ℚ) / M] := by
    funext i
    fin_cases i <;> simp [mul_div_assoc]
  have := ((hasQ_F j hM a b).const_mul ((c : ℂ) ^ 2)).sub
    ((hasQ_F j hM (c * a) (c * b)).const_mul ((c : ℂ) ^ (2 - (j : ℤ))))
  rw [← hx] at this
  unfold smF
  simp only [Int.cast_natCast]
  exact this

theorem hasQ_cF_one : ∀ (c M : ℕ) (a b : ℤ), 0 < M → GlobalTheory.QFam.HasQ M (GlobalTheory.Sieg.cF c 1 ![(a : ℚ) / M, (b : ℚ) / M])
    (GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M (GlobalTheory.Sieg.ee (1 / (M : ℂ))) a b) :=
  fun c _ a b hM => hasQ_cF_weight c 1 hM a b

end GlobalTheory.Sieg.EisQ
end
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.fixedFieldAlmostEtale_subgroupOf : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (U H : Subgroup G), AlmostSep v U → AlmostSep v (U.subgroupOf H) := by
  first | exact @GlobalTheory.AlmostEt.almostSep_subgroupOf | exact GlobalTheory.AlmostEt.almostSep_subgroupOf | (intros; apply GlobalTheory.AlmostEt.almostSep_subgroupOf <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.movesIntegersAlmostUnitDistance_fixedSubfield : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) (i : ℝ≥0), i < 1 → (∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i) → ∀ σ : G, Moves v ⊤ σ → Moves v (Fix L N) σ := by
  first | exact @GlobalTheory.AlmostEt.moves_fix_of_moves | exact GlobalTheory.AlmostEt.moves_fix_of_moves | (intros; apply GlobalTheory.AlmostEt.moves_fix_of_moves <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (N : Subgroup G) [Fintype (G ⧸ N)] (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, ∑ i, a i * cosetTrace N (b i * x) = c * x := by
  first | exact @GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq | exact GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq | (intros; apply GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq <;> assumption)
end

section

open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

theorem _root_.GlobalTheory.T.sum_gl2FirstColumnUnitSet_succ_fibre : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (K : Type) [CommRing K] (G : GL (Fin 2) (ZMod (p ^ n)) → K) (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K), 1 ≤ n → ∑ γ ∈ unitSet p (n + 1), G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) = ∑ γ ∈ unitSet p n, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  first | exact @GlobalTheory.KummerEisensteinGalois.sum_unitSet_succ_fibre | exact GlobalTheory.KummerEisensteinGalois.sum_unitSet_succ_fibre | (intros; apply GlobalTheory.KummerEisensteinGalois.sum_unitSet_succ_fibre <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial
open scoped IntermediateField

namespace GlobalTheory.NeedB.NormCob

theorem hom_pow {G : Type*} [Group G] {N : ℕ} (y : G → ZMod N) (hy : ∀ g h, y (g * h) = y g + y h) (σ : G) (q : ℕ) :
    y (σ ^ q) = q * y σ := by
  have h1 : y 1 = 0 := by
    have := hy 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  induction q with
  | zero => simp [h1]
  | succ q ih => rw [pow_succ, hy, ih]; push_cast; ring

theorem exists_generator {G : Type*} [Group G] {N : ℕ} (hN : 0 < N) (y : G → ZMod N)
    (hy : ∀ g h, y (g * h) = y g + y h) :
    ∃ (d m : ℕ) (σ : G), 0 < m ∧ m * d = N ∧ y σ = m ∧ ∀ g, m ∣ (y g).val := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  have h1 : y 1 = 0 := by simpa using hom_pow y hy 1 0
  have hex : ∃ m : ℕ, 0 < m ∧ ∃ g, y g = m := ⟨N, hN, 1, by simp [h1]⟩
  obtain ⟨hm, σ, hσ⟩ := Nat.find_spec hex
  set m := Nat.find hex with hmdef
  have key : ∀ n : ℕ, (∃ g, y g = n) → m ∣ n := by
    rintro n ⟨g, hg⟩
    by_contra hnd
    have hr : 0 < n % m := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    refine Nat.find_min hex (Nat.mod_lt n hm) ⟨hr, g * (σ ^ (n / m))⁻¹, ?_⟩
    have h2 := hy (g * (σ ^ (n / m))⁻¹) (σ ^ (n / m))
    rw [inv_mul_cancel_right, hg, hom_pow y hy, hσ] at h2
    have h3 : (n : ZMod N) = ((n % m : ℕ) : ZMod N) + ((n / m : ℕ) : ZMod N) * m := by
      conv_lhs => rw [← Nat.mod_add_div' n m]
      push_cast; ring
    exact (add_right_cancel (h2.symm.trans h3))
  obtain ⟨d, hd⟩ := key N ⟨1, by simp [h1]⟩
  exact ⟨d, m, σ, hm, hd.symm, hσ, fun g => key _ ⟨g, by simp⟩⟩

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem agree {β : Ω} {g g' : Ω ≃ₐ[K] Ω} (h : g β = g' β) (x : K⟮β⟯) : g x = g' x := by
  have : (g : Ω →ₐ[K] Ω).comp K⟮β⟯.val = (g' : Ω →ₐ[K] Ω).comp K⟮β⟯.val := by
    apply IntermediateField.adjoin_algHom_ext
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact h
  exact DFunLike.congr_fun this x

theorem norm_eq_prod [CharZero K] [IsAlgClosure K Ω] {β : Ω} (σ : Ω ≃ₐ[K] Ω) (d : ℕ)
    (hinj : ∀ i < d, ∀ j < d, (σ ^ i) β = (σ ^ j) β → i = j)
    (hsurj : ∀ g : Ω ≃ₐ[K] Ω, ∃ j < d, g β = (σ ^ j) β) (γ : K⟮β⟯) :
    algebraMap K Ω (Algebra.norm K γ) = ∏ j ∈ Finset.range d, (σ ^ j) γ := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  rw [Algebra.norm_eq_prod_embeddings K Ω γ]
  symm
  refine Finset.prod_bij (fun j _ => ((σ ^ j : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp K⟮β⟯.val) (by simp) ?_ ?_ ?_
  · intro i hi j hj hij
    exact hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
      (DFunLike.congr_fun hij (IntermediateField.AdjoinSimple.gen K β))
  · intro τ _
    obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (F := K) (E := Ω) (K := Ω)
      (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) τ
    let g : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
    obtain ⟨j, hj, hg⟩ := hsurj g
    refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
    rw [← hφ]
    ext x
    exact (agree hg x).symm
  · intro j _
    rfl

theorem carry_coboundary : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w ∧ ∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h) := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb ((map_eq_zero _).mp hβ.symm)
  obtain ⟨hlc, hdef, hhom, -⟩ := GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  set y := kum (N := N) (K := K) ζ β with hydef
  obtain ⟨d, m, σ, hm, hmd, hσ, hdvd⟩ := exists_generator hN y hhom
  have hpow : ∀ j : ℕ, y (σ ^ j) = ((m * j : ℕ) : ZMod N) := fun j => by
    rw [hom_pow y hhom, hσ]; push_cast; ring
  have hval : ∀ g, (y g).val = m * ((y g).val / m) := fun g => (Nat.mul_div_cancel' (hdvd g)).symm
  have hlt : ∀ g, (y g).val / m < d := fun g => by
    apply Nat.div_lt_of_lt_mul
    rw [hmd]; exact ZMod.val_lt _
  have hyk : ∀ g, y g = y (σ ^ ((y g).val / m)) := fun g => by
    rw [hpow, ← hval, ZMod.natCast_zmod_val]
  have hag : ∀ g g', y g = y g' → g β = g' β := fun g g' h => by rw [hdef g, hdef g', h]
  haveI : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  obtain ⟨γ, hγ⟩ := hnorm K⟮β⟯ inferInstance a ha
  have hγ0 : (γ : Ω) ≠ 0 := by
    intro h
    have : γ = 0 := Subtype.ext h
    rw [this, Algebra.norm_zero] at hγ
    exact ha hγ.symm
  have hprod : algebraMap K Ω a = ∏ j ∈ Finset.range d, (σ ^ j) γ := by
    rw [← hγ]
    refine norm_eq_prod σ d ?_ (fun g => ⟨_, hlt g, hag _ _ (hyk g)⟩) γ
    intro i hi j hj hij
    have hi' : m * i < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hi hm
    have hj' : m * j < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hj hm
    rw [hdef, hdef (σ ^ j), hpow, hpow, ZMod.val_cast_of_lt hi', ZMod.val_cast_of_lt hj'] at hij
    exact Nat.eq_of_mul_eq_mul_left hm (hζ.pow_inj hi' hj' (mul_right_cancel₀ hβ0 hij))
  let P : ℕ → Ω := fun n => ∏ j ∈ Finset.range n, (σ ^ j) γ
  have hP0 : ∀ n, P n ≠ 0 := fun n => Finset.prod_ne_zero_iff.mpr fun j _ => (_root_.map_ne_zero _).mpr hγ0
  have hPadd : ∀ (g : Ω ≃ₐ[K] Ω) (i n : ℕ), y g = y (σ ^ i) → P i * g (P n) = P (i + n) := by
    intro g i n hg
    simp only [P]
    rw [Finset.prod_range_add, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    have : y (g * σ ^ j) = y (σ ^ (i + j)) := by rw [pow_add, hhom, hhom, hg]
    exact agree (hag _ _ this) γ
  have hPd : ∀ r, P (d + r) = algebraMap K Ω a * P r := by
    intro r
    have h1 : y 1 = y (σ ^ d) := by
      rw [hpow, hmd, ← pow_zero σ, hpow]; simp
    rw [← hPadd 1 d r h1, hprod]
    rfl
  refine ⟨fun g => Units.mk0 (P ((y g).val / m)) (hP0 _),
    hlc.comp (fun z : ZMod N => Units.mk0 (P (z.val / m)) (hP0 _)), fun g h => ?_⟩
  simp only [Units.val_mk0]
  rw [hPadd g _ _ (hyk g), hhom, ZMod.val_add]
  have hg := hlt g
  have hh := hlt h
  rw [hval g, hval h, ← mul_add, Nat.mul_div_cancel_left _ hm, Nat.mul_div_cancel_left _ hm]
  generalize (y g).val / m = i at *
  generalize (y h).val / m = j at *
  by_cases hij : i + j < d
  · have : m * (i + j) < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hij hm
    rw [Nat.mod_eq_of_lt this, Nat.mul_div_cancel_left _ hm, mul_comm]
  · obtain ⟨r, hr⟩ : ∃ r, i + j = d + r := ⟨i + j - d, by omega⟩
    have hrd : r < d := by omega
    have : m * r < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hrd hm
    rw [hr, mul_add, hmd, Nat.add_mod_left, Nat.mod_eq_of_lt this, Nat.mul_div_cancel_left _ hm, hPd, pow_add, hα]
    ring

end GlobalTheory.NeedB.NormCob
end

section

open GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.primitiveChar_doubleSum_primePow_eval : ∀ (p m : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (ζm : K), 1 ≤ m → ψ.IsPrimitive → IsPrimitiveRoot ζm (p ^ m) → ∀ n₁ n₂ d d' : ℤ, ¬ ((p : ℤ) ∣ n₁ ∧ (p : ℤ) ∣ n₂) → (∀ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) → (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m)) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = (p : K) ^ m * ψ⁻¹ (u : ZMod (p ^ m)) * gaussS p m ψ ζm) ∧ ((¬ ∃ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) ∧ (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m))) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = 0) := by
  first | exact @GlobalTheory.KummerEisensteinGalois.ChSum.charSum | exact GlobalTheory.KummerEisensteinGalois.ChSum.charSum | (intros; apply GlobalTheory.KummerEisensteinGalois.ChSum.charSum <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNHS

theorem hs_props : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (C C' : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), C ≤ C' → HS ε C φ h → HS ε C' φ h) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), HS ε C φ h → HS ε C ψ h' → HS ε C (φ + ψ) (h + h') ∧ HS ε C (φ - ψ) (h - h')) ∧ (∀ (C : ℝ) (r : ℚ) (c : Ω), HS ε C (fun z => ε c * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (HahnSeries.single r c)) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h : HahnSeries ℚ Ω), (∀ z : ℂ, C < z.im → φ z = ψ z) → HS ε C φ h → HS ε C ψ h) := by
  intro Ω _ ε
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C C' φ h hC hs z hz
    exact hs z (lt_of_le_of_lt hC hz)
  · intro C φ ψ h h' hφ hψ
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · have := (hφ z hz).add (hψ z hz)
      simpa [HahnSeries.coeff_add, map_add (f := _), add_mul] using this
    · have := (hφ z hz).sub (hψ z hz)
      simpa [HahnSeries.coeff_sub, map_sub, sub_mul] using this
  · intro C r c z _
    have := hasSum_single (f := fun s : ℚ => ε ((HahnSeries.single r c).coeff s) *
        Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * z)) r (by
      intro b hb
      simp [HahnSeries.coeff_single_of_ne hb])
    simpa [HahnSeries.coeff_single_same] using this
  · intro C φ ψ h hφψ hs z hz
    rw [← hφψ z hz]
    exact hs z hz

end GlobalTheory.FNHS
end
