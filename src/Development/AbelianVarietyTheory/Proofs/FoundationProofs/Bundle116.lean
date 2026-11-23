module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle065
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueLinearDisjointnessCoeffLtOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle095
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
public import Mathlib.RingTheory.AdicCompletion.Completeness
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle096
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.blockDiagonal_principalSeriesCongruenceSubgroup_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → Cut ψ r → Ordered (fun i => ψ (Fin.castAdd t i)) ∧ Ordered (fun i => ψ (Fin.natAdd r i)) ∧ ∀ (a : GL (Fin r) k) (b : GL (Fin t) k), emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ grp ψ ↔ a ∈ grp (fun i => ψ (Fin.castAdd t i)) ∧ b ∈ grp (fun i => ψ (Fin.natAdd r i)) := by
  first | exact @GlobalTheory.PsType.block_diag_mem_grp | exact GlobalTheory.PsType.block_diag_mem_grp | (intros; apply GlobalTheory.PsType.block_diag_mem_grp <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_int_det {I : Type} [Fintype I] [DecidableEq I] {g : GL I k}
    (hM : ∀ i j, valuation k (g.val i j) ≤ 1) (hd : valuation k g.val.det = 1) : g ∈ KO k I := by
  classical
  let M : Matrix I I 𝒪[k] := fun i j => ⟨g.val i j, (Valuation.mem_integer_iff _ _).2 (hM i j)⟩
  have hmap : M.map (algebraMap 𝒪[k] k) = g.val := by
    ext i j
    rfl
  have hdet : IsUnit M.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_of_one' ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, hd]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det M).2 hdet
  refine ⟨u, ?_⟩
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, hu]
  rfl

end GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem strip_off {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ))) : y.val i j = (1 : Matrix (Fin n) (Fin n) k) i j := by
  simp only [strip, Set.mem_ofPred_eq] at hy
  have h0 := hy i j
  rw [if_neg h] at h0
  exact h0

theorem strip_on {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : (i : ℕ) < r ∧ r ≤ (j : ℕ)) :
    valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j) := by
  simp only [strip, Set.mem_ofPred_eq] at hy
  have h0 := hy i j
  rw [if_pos h] at h0
  exact h0

theorem strip_lower {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : j < i) : y.val i j = 0 := by
  have hji : (j : ℕ) < (i : ℕ) := h
  rw [strip_off hy i j (fun hc => by omega), Matrix.one_apply_ne (ne_of_gt h)]

theorem strip_diag {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i : Fin n) : y.val i i = 1 := by
  rw [strip_off hy i i (fun hc => by omega), Matrix.one_apply_eq]

theorem strip_det {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m) :
    y.val.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j h => strip_lower hy i j h)]
  simp [strip_diag hy]

theorem strip_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → Cut ψ r → (∀ y ∈ strip ψ r ϖ 0, y ∈ grp ψ) ∧ (∀ m, ∀ y ∈ strip ψ r ϖ m, theta ψ y = 1) ∧ (∀ y ∈ strip ψ r ϖ 1, y ∈ KO k (Fin n)) ∧ ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ m y, y ∈ strip ψ r ϖ (m + 1) ↔ z * y * z⁻¹ ∈ strip ψ r ϖ m := by
  intro k _ _ _ _ n ψ r ϖ hϖ hϖ1 hunif hcut
  have hent : ∀ (m : ℕ) (y : GL (Fin n) k), y ∈ strip ψ r ϖ m → ∀ i j : Fin n,
      ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → valuation k (y.val i j) ≤ 1 := by
    intro m y hy i j h
    rw [strip_off hy i j h]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  have hdet1 : ∀ (m : ℕ) (y : GL (Fin n) k), y ∈ strip ψ r ϖ m → valuation k y.val.det = 1 := by
    intro m y hy
    rw [strip_det hy, map_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    refine (show y ∈ KO k (Fin n) ∧ ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) (y.val i j) from ⟨?_, ?_⟩)
    · refine mem_KO_of_int_det (fun i j => ?_) (hdet1 0 y hy)
      by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
      · have h0 := (strip_on hy i j h).1
        rwa [pow_zero, one_mul] at h0
      · exact hent 0 y hy i j h
    · intro i j hij
      by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
      · have h0 := (strip_on hy i j h).2
        rwa [pow_zero, one_mul] at h0
      · rw [strip_off hy i j h, Matrix.one_apply_ne (ne_of_lt hij)]
        exact triv_zero _
  · intro m y hy
    rw [GlobalTheory.T.principalSeriesTypeCharacter_triangular k n ψ y (fun _ => 1) (fun _ => by simp) (fun i => by simp [strip_diag hy i])
      (Or.inr fun i j h => strip_lower hy i j h)]
    simp
  · intro y hy
    refine mem_KO_of_int_det (fun i j => ?_) (hdet1 1 y hy)
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · obtain ⟨h1, h2⟩ := strip_on hy i j h
      rw [pow_one] at h1 h2
      have hlt : valuation k (ϖ * y.val i j) < 1 := by
        refine lt_of_le_of_ne h1 fun heq => hcut i j h.1 h.2 ?_
        exact triv_mono _ _ _ (le_of_eq (by rw [heq, map_one])) h2
      have hle := hunif _ hlt
      rw [map_mul] at hle
      have hpos : 0 < valuation k ϖ := zero_lt_iff.2 ((map_ne_zero _).2 hϖ)
      exact le_of_mul_le_mul_left (by rwa [mul_one]) hpos
    · exact hent 1 y hy i j h
  · intro z hz m y
    set d : Fin n → k := fun i : Fin n => if (i : ℕ) < r then ϖ else 1 with hd_def
    have hd : ∀ i, d i ≠ 0 := by
      intro i
      simp only [hd_def]
      split_ifs
      exacts [hϖ, one_ne_zero]
    have hzz : z.val * (z⁻¹).val = 1 := by simp
    have hzinv : (z⁻¹).val = Matrix.diagonal (fun i => (d i)⁻¹) := by
      calc (z⁻¹).val = (Matrix.diagonal (fun i => (d i)⁻¹) * z.val) * (z⁻¹).val := by
            rw [hz, Matrix.diagonal_mul_diagonal]
            rw [show (fun i => (d i)⁻¹ * d i) = fun _ => (1 : k) from funext fun i => inv_mul_cancel₀ (hd i)]
            rw [Matrix.diagonal_one, one_mul]
        _ = Matrix.diagonal (fun i => (d i)⁻¹) := by rw [mul_assoc, hzz, mul_one]
    have hentry : ∀ i j : Fin n, (z * y * z⁻¹).val i j = d i * y.val i j * (d j)⁻¹ := by
      intro i j
      rw [Units.val_mul, Units.val_mul, hz, hzinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [strip, Set.mem_ofPred_eq, hentry]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · rw [if_pos h, if_pos h]
      have hdi : d i = ϖ := by simp only [hd_def]; rw [if_pos h.1]
      have hdj : d j = 1 := by simp only [hd_def]; rw [if_neg (by omega)]
      rw [hdi, hdj, show ϖ ^ m * (ϖ * y.val i j * (1 : k)⁻¹) = ϖ ^ (m + 1) * y.val i j by ring]
    · rw [if_neg h, if_neg h]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply_eq, mul_comm (d i), mul_inv_cancel_right₀ (hd i)]
      · rw [Matrix.one_apply_ne hij]
        simp [hd i, hd j]

end GlobalTheory.PsType
end
end

section

noncomputable section
open Finset
open scoped Classical
open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.KummerEisensteinGalois.LevelT

theorem vp_cmul {K : Type} [Field K] [CharZero K] (p : ℕ) (hp : 0 < p) (f g : ℕ → K) (r : ℕ) :
    vp p (cmul f g) r = cmul (vp p f) (vp p g) r := by
  by_cases h : p ∣ r
  · obtain ⟨r', rfl⟩ := h
    rw [UpSplit.cmul_vp_vp p hp]
    simp [vp, Nat.mul_div_cancel_left _ hp]
  · rw [show vp p (cmul f g) r = 0 by simp [vp, h]]
    unfold cmul
    symm
    apply sum_eq_zero
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
    by_cases hpi : p ∣ i
    · have : ¬ p ∣ r - i := by
        intro h2
        apply h
        have := Nat.dvd_add h2 hpi
        rwa [Nat.sub_add_cancel hi'] at this
      simp [vp, this]
    · simp [vp, hpi]

theorem cauchyProduct_fourfold_finsetSum {K : Type} [Field K] {α : Type} (s₁ s₂ s₃ s₄ : Finset α) (f g : α → α → ℕ → K) (r : ℕ) :
    ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, cmul (f a b) (g c d) r =
      cmul (fun i => ∑ a ∈ s₁, ∑ b ∈ s₂, f a b i) (fun i => ∑ c ∈ s₃, ∑ d ∈ s₄, g c d i) r := by
  unfold cmul
  simp_rw [Finset.sum_comm (s := s₄) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₃) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₂) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₁) (t := range (r + 1))]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]; refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]; refine sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]; refine sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

theorem dvd_castHom_val_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ (n + 1))) :
    p ∣ (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val ↔ p ∣ x.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
    Nat.dvd_mod_iff (dvd_pow_self p (by omega))]

theorem sum_preimage_fibre (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) (K : Type) [CommRing K]
    (X : Finset (GL (Fin 2) (ZMod (p ^ n))))
    (hX : ∀ γ ∈ X, ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val)
    (G : GL (Fin 2) (ZMod (p ^ n)) → K)
    (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K) :
    ∑ γ ∈ (univ.filter fun γ : GL (Fin 2) (ZMod (p ^ (n + 1))) => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X),
      G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) =
    ∑ γ ∈ X, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  set ρ := ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) with hρ
  have hS : (univ.filter fun γ : GL (Fin 2) (ZMod (p ^ (n + 1))) => Matrix.GeneralLinearGroup.map ρ γ ∈ X) =
      (unitSet p (n + 1)).filter (fun γ => Matrix.GeneralLinearGroup.map ρ γ ∈ X) := by
    ext γ
    simp only [mem_filter, mem_univ, true_and, unitSet]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := hX _ h
      have e1 : ((Matrix.GeneralLinearGroup.map ρ γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0 = ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) := rfl
      have e2 : ((Matrix.GeneralLinearGroup.map ρ γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0 = ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) := rfl
      rw [e1, hρ, dvd_castHom_val_iff hn] at h1
      rw [e2, hρ, dvd_castHom_val_iff hn] at h2
      exact ⟨⟨h1, h2⟩, h⟩
    · exact fun h => h.2
  have hX' : (unitSet p n).filter (fun γ => γ ∈ X) = X := by
    ext γ
    simp only [mem_filter, unitSet, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hX γ h, h⟩⟩
  rw [hS, Finset.sum_filter]
  have h1 := GlobalTheory.T.sum_gl2FirstColumnUnitSet_succ_fibre p n K (fun g => if g ∈ X then G g else 0) Φ hn
  simp only [ite_mul, zero_mul] at h1
  rw [h1, ← Finset.sum_filter, hX']

end GlobalTheory.KummerEisensteinGalois.LevelT


open GlobalTheory.KummerEisensteinGalois.LevelT in
theorem GlobalTheory.KummerEisensteinGalois.pieceT_unitSet_level_succ : ∀ (p : ℕ) [Fact p.Prime] (N n m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' v v' : ℤ × ℤ) (ζ : K) (X : Finset (GL (Fin 2) (ZMod (p ^ n)))), IsPrimitiveRoot ζ (N * p ^ (n + 1)) → 0 < N → ¬ p ∣ N → 1 ≤ m → m ≤ n → 3 ≤ k → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → (p : ℤ) * v.1 ≡ w.1 [ZMOD N] → (p : ℤ) * v.2 ≡ w.2 [ZMOD N] → (p : ℤ) * v'.1 ≡ w'.1 [ZMOD N] → (p : ℤ) * v'.2 ≡ w'.2 [ZMOD N] → (∀ γ ∈ X, ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val) → ∀ r : ℕ, pieceT N p (n + 1) m k ψ c d v v' ζ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X) r = vp p (pieceT N p n m k ψ c d w w' (ζ ^ p) X) r := by
  intro p _ N n m k K _ _ ψ c d w w' v v' ζ X hζ hN hpN hm hmn hk hc hd h1 h2 h3 h4 hX r
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hn : 1 ≤ n := le_trans hm hmn
  have hdet : ∀ γ : GL (Fin 2) (ZMod (p ^ (n + 1))),
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).det.val : ℕ) : ZMod (p ^ m)) =
      ((((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) := by
    intro γ
    have hcast : ∀ {a : ℕ} [NeZero a] (y : ZMod a) (h : p ^ m ∣ a),
        ((y.val : ℕ) : ZMod (p ^ m)) = ZMod.castHom h (ZMod (p ^ m)) y := by
      intro a _ y h
      rw [ZMod.castHom_apply, ZMod.natCast_val]
    have e : ((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) =
        ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) := rfl
    rw [hcast _ (pow_dvd_pow p (by omega : m ≤ n + 1)), hcast _ (pow_dvd_pow p hmn), e, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← RingHom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have hRHS : vp p (pieceT N p n m k ψ c d w w' (ζ ^ p) X) r =
      -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
        ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n)))).det.val : ℕ) : ZMod (p ^ m)) *
        vp p (cmul (smF c (k - 1) (N * p ^ n) (ζ ^ p) (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) (ζ ^ p) (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2)) r := by
    unfold vp pieceT
    split_ifs <;> simp
  rw [hRHS]
  unfold pieceT
  have hsum := sum_preimage_fibre p n hn K X hX (fun γ => ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n)))).det.val : ℕ) : ZMod (p ^ m)))
    (fun y₀₀ y₀₁ y₁₀ y₁₁ => cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₀₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (y₀₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
      (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (y₁₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r)
  have hL : ∑ γ ∈ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X), ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ (rowT N p (n + 1) γ 0 v).1 (rowT N p (n + 1) γ 0 v).2)
           (smF d 1 (N * p ^ (n + 1)) ζ (rowT N p (n + 1) γ 1 v').1 (rowT N p (n + 1) γ 1 v').2) r =
      ∑ γ ∈ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X), ψ ((((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0).val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1).val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
      (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0).val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1).val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r := by
    refine sum_congr rfl fun γ _ => ?_
    rw [hdet]
    rfl
  rw [hL, hsum]
  have hp' : (p : K) ≠ 0 := by exact_mod_cast hp0.ne'
  have hj : 1 ≤ k - 1 := by omega
  have hstep : ∀ γ ∈ X,
      (∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)),
        cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₀₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (y₀₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
          (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (y₁₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r) =
      ((p : K) ^ ((2 : ℤ) - ((k - 1 : ℕ) : ℤ)) * (p : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ))) *
        vp p (cmul (smF c (k - 1) (N * p ^ n) (ζ ^ p) (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) (ζ ^ p) (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2)) r := by
    intro γ hγ
    have hu : ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val := by
      exact hX γ hγ
    rw [cauchyProduct_fourfold_finsetSum]
    simp only [GlobalTheory.T.smoothedEisensteinFx_sum_row_lifts_distribution p N n (k - 1) K ζ c ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1) v.1 v.2 w.1 w.2 hζ hN hpN hn hj hc hu.1 h1 h2,
      GlobalTheory.T.smoothedEisensteinFx_sum_row_lifts_distribution p N n 1 K ζ d ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1) v'.1 v'.2 w'.1 w'.2 hζ hN hpN hn le_rfl hd hu.2 h3 h4]
    rw [vp_cmul p hp0]
    unfold cmul
    rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [rowT]
    ring
  rw [Finset.sum_congr rfl (fun γ hγ => by rw [hstep γ hγ])]
  have hsc : -((p : K) ^ (((n + 1 : ℕ) : ℤ) * ((k : ℤ) - 4))) *
      ((p : K) ^ ((2 : ℤ) - ((k - 1 : ℕ) : ℤ)) * (p : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ))) =
      -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) := by
    rw [← zpow_add₀ hp', neg_mul, ← zpow_add₀ hp']
    congr 2
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    ring
  rw [← hsc, Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun γ _ => ?_
  ring
end
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

noncomputable section

namespace GlobalTheory.GeoFix

theorem exists_lau_approx (p : ℕ) [Fact p.Prime] (K : ℕ) (x : O0 p) :
    ∃ (a : Lau p) (c : O0 p), x = algebraMap (Lau p) (O0 p) a + (p : O0 p) ^ K * c := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (pI p) K x)
  have hker : RingHom.ker (AdicCompletion.evalₐ (pI p) K) = (pI p ^ K).map (algebraMap (Lau p) (O0 p)) := by
    ext y
    rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem (Lau p), ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]
    have hle : (pI p ^ K • ⊤ : Ideal (Lau p)) ≤ pI p ^ K := by intro z hz; simpa using hz
    rw [← AdicCompletion.factor_eval_eq_evalₐ (pI p) y hle]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (pI p) (Lau p) K y)
      rw [← hb] at h ⊢
      have : b ∈ pI p ^ K := Ideal.Quotient.eq_zero_iff_mem.mp h
      exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
    · intro h; rw [h, map_zero]
  have hmem : x - algebraMap (Lau p) (O0 p) a ∈ RingHom.ker (AdicCompletion.evalₐ (pI p) K) := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ha, sub_self]
  rw [hker, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow, map_natCast,
    Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨a, c, by rw [mul_comm, hc]; ring⟩

theorem exists_cong_lau :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
      (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ →
      ∀ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p), (∀ t, IsInt (p := p) (e t)) →
      ∀ K : ℕ, ∃ a : Fin d → Lau p,
        Cong (p := p) K (∑ t, e t * ψ (b t))
          (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) := by
  intro p hp Ω _ _ T n ψ h d e b he K
  choose a c hac using fun t => exists_lau_approx p K (b t)
  have hq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (pow_pos hp.out.pos n) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hψ (x : O0 p) : IsIntegral (O0 p) (ψ x) := by
    have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [h.rng] at hx
    exact adjoin_le_integralClosure hq hx
  refine ⟨a, ∑ t, e t * ψ (c t), IsIntegral.sum _ fun t _ => IsIntegral.mul (he t) (hψ (c t)), ?_⟩
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hac t, map_add (f := _), map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.GeoFix
end
end

section

open scoped MatrixGroups NNReal
open Polynomial GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois


theorem _root_.GlobalTheory.T.residue_linear_disjointness_coeff_lt_one :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) →
      v (p : Ω) < 1 → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω),
      IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p),
      (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) →
      v (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) < 1 →
      ∀ r : ℤ, v (∑ t, e t * zp Ω ((a t).coeff r)) < 1 := by
  apply _root_.GlobalTheory.K5.ResDisj.coeff_lt_one <;> assumption
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.heckeNorm_gamma1PrimePow_invariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ∀ g : X.K,
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g →
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) := by
  first | exact @GlobalTheory.normInv_gamma1 | exact GlobalTheory.normInv_gamma1 | (intros; apply GlobalTheory.normInv_gamma1 <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.evalSeriesAndDeriv_unique_of_coefficients : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (c : ℤ → Ω) (x x' y y' : Ω), Ev ψ c x x' → Ev ψ c y y' → x = y ∧ x' = y' := by
  first | exact @GlobalTheory.EvUniq.ev_unique | exact GlobalTheory.EvUniq.ev_unique | (intros; apply GlobalTheory.EvUniq.ev_unique <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss : ∀ {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω), Prim A P → Prim A Q → Prim A (P * Q) := by
  first | exact @GlobalTheory.Glue.Prim.mul | exact GlobalTheory.Glue.Prim.mul | (intros; apply GlobalTheory.Glue.Prim.mul <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (P Q : HahnSeries ℚ Ω), theta s (P * Q) = theta s P * Q + P * theta s Q ∧ theta s (P + Q) = theta s P + theta s Q ∧ ∀ c : Ω, theta s (HahnSeries.C c) = 0 := by
  first | exact @GlobalTheory.Glue.theta_leibniz_add_const | exact GlobalTheory.Glue.theta_leibniz_add_const | (intros; apply GlobalTheory.Glue.theta_leibniz_add_const <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.Glue

theorem _root_.GlobalTheory.T.smul_kaehlerD_reparametrization_eq : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (L : ℕ) (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (b : Lau p) (x y qL : integralClosure (O0 p) Ω), (x : Ω) = ψ (algebraMap (Lau p) (O0 p) b) → (y : Ω) = ψ (algebraMap (Lau p) (O0 p) (thL b)) → (qL : Ω) = T.qq L → qL • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) x = y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qL := by
  first | exact @GlobalTheory.Glue.DPsi.smul_D_psi | exact GlobalTheory.Glue.DPsi.smul_D_psi | (intros; apply GlobalTheory.Glue.DPsi.smul_D_psi <;> assumption)
end
