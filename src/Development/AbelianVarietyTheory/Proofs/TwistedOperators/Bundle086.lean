module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle660
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle656
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle658
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle077
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hU hn g

  set A : Matrix (Fin n) (Fin n) L := ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAdef
  set B : Matrix (Fin n) (Fin n) L := (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    with hBdef
  have hAB : A * B = 1 := (g : GL (Fin n) L).mul_inv
  have hBA : B * A = 1 := (g : GL (Fin n) L).inv_mul

  have hherm : (A.map σ)ᵀ * antiJ L n * A = antiJ L n := g.2

  have key : ∀ i j, Valued.v (A i j) = 1 ∧ Valued.v (B i j) = 1 := by
    intro i j
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · exact i.elim0
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      have h1 : σ (A 0 0) * A 0 0 = 1 := by
        simpa [Matrix.mul_apply, antiJ] using congrFun (congrFun hherm 0) 0
      have h2 : B 0 0 * A 0 0 = 1 := by
        simpa [Matrix.mul_apply] using congrFun (congrFun hBA 0) 0
      have hsq : Valued.v (A 0 0) * Valued.v (A 0 0) = 1 := by
        have := congrArg Valued.v h1
        rwa [map_mul, map_one, hU.2.1] at this
      have hle : Valued.v (A 0 0) ≤ 1 := by
        by_contra hlt
        have hgt : 1 < Valued.v (A 0 0) := not_le.1 hlt
        have : Valued.v (A 0 0) * 1 ≤ Valued.v (A 0 0) * Valued.v (A 0 0) := by gcongr
        rw [mul_one, hsq] at this
        exact hlt this
      have hA1 : Valued.v (A 0 0) = 1 := by
        refine le_antisymm hle ?_
        have : Valued.v (A 0 0) * Valued.v (A 0 0) ≤ Valued.v (A 0 0) * 1 := by gcongr
        rwa [mul_one, hsq] at this
      refine ⟨hA1, ?_⟩
      have := congrArg Valued.v h2
      rwa [map_mul, map_one, hA1, mul_one] at this
  have hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x hx => by
    unfold intL
    exact (Valuation.mem_integer_iff _ _).2 hx.le

  let A' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨A i j, hint _ (key i j).1⟩
  let B' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨B i j, hint _ (key i j).2⟩
  have hinj : Function.Injective
      ((intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (intL L) → Matrix (Fin n) (Fin n) L) :=
    fun X Y h => by
      ext i j
      exact congrFun (congrFun h i) j
  have eA : (intL L).subtype.mapMatrix A' = A := rfl
  have eB : (intL L).subtype.mapMatrix B' = B := rfl
  unfold KU
  rw [Subgroup.mem_subgroupOf]
  unfold intPts
  rw [Subgroup.mem_inf, MonoidHom.mem_range]
  refine ⟨g.2, ⟨A', B', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, eA, eB, map_one, hAB]
  · rw [map_mul, eA, eB, map_one, hBA]
  · unfold bc
    exact Units.ext eA

end GlobalTheory.InertZeta

end
end

section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem rev_zero_eq_last {N : ℕ} : (0 : Fin (N + 2)).rev = Fin.last (N + 1) := by ext; simp [Fin.val_rev]

theorem rev_last_eq_zero {N : ℕ} : (Fin.last (N + 1)).rev = (0 : Fin (N + 2)) := by ext; simp [Fin.val_rev]

theorem blk_rev_of_eq {N : ℕ} (a b : Fin (N + 2)) (h : blk N a = blk N b) : blk N a.rev = blk N b.rev := by
  rcases idx_cases a with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases b with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [rev_zero_eq_last, rev_last_eq_zero, ← mid_rev] at h ⊢

theorem lt_of_blk_lt {N : ℕ} {a b : Fin (N + 2)} (h : blk N a < blk N b) : a < b := by
  rcases idx_cases a with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases b with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Fin.lt_def] at h ⊢

theorem cosetSurj_of_leviExists : LeviExists → CosetSurj := by
  intro _ L _ _ ϖ σ q N hU g
  have hσσ : ∀ x, σ (σ x) = x := hU.1
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨b, k, hb, hk, rfl⟩ := P.fIwasawa_iwasawa σ hσσ hσv g
  have hbT : (mat b).BlockTriangular (blk N) := fun i j h => hb i j (lt_of_blk_lt h)
  obtain ⟨m', hm'L, hm'e, hu'⟩ := leviPart L σ (N + 2) (blk N) blk_rev_of_eq b hbT
  set M₀ : Matrix (Fin N) (Fin N) L := Matrix.of fun i j => mat m' (mid i) (mid j) with hM₀
  have hM₀U : cT σ M₀ * antiJ L N * M₀ = antiJ L N := by
    have h1 : cT σ (mat m') * antiJ L (N + 2) * mat m' = antiJ L (N + 2) := m'.2
    ext i j
    have h2 := congrFun (congrFun h1 (mid i)) (mid j)
    rw [Matrix.mul_apply, sum_idx] at h2
    have e0 : mat m' 0 (mid j) = 0 := hm'L _ _ (by simp)
    have eL : mat m' (Fin.last (N + 1)) (mid j) = 0 := hm'L _ _ (by simp)
    rw [e0, eL, mul_zero, mul_zero, zero_add, add_zero] at h2
    have hJ : antiJ L (N + 2) (mid i) (mid j) = antiJ L N i j := by
      simp only [antiJ]
      exact if_congr (by simp only [val_mid]; omega) rfl rfl
    rw [hJ] at h2
    rw [← h2, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [P.fSatake_cTJ, P.fSatake_cTJ, ← mid_rev]
    rfl
  obtain ⟨g₀, hg₀⟩ := exists_mat M₀ hM₀U
  obtain ⟨⟨k₀, hk₀⟩, hout⟩ := QuotientGroup.mk_out_eq_mul (KU σ N) g₀
  have hxL : σ (mat m' 0 0) * mat m' (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by
    rw [hm'e 0 0 rfl, hm'e _ _ rfl]
    have := P.fSatake_unit_diag hb 0
    rwa [rev_zero_eq_last] at this
  have hx0 : mat m' 0 0 ≠ 0 := by
    intro h; rw [h, map_zero, zero_mul] at hxL; exact zero_ne_one hxL
  have hvx0 : Valued.v (mat m' 0 0) ≠ 0 := by simpa using hx0
  have hvx : Valued.v (mat m' 0 0) = WithZero.exp (-(-(Valued.v (mat m' 0 0)).log)) := by
    rw [neg_neg, WithZero.exp_log hvx0]
  refine ⟨-(Valued.v (mat m' 0 0)).log, (g₀ : GU σ N ⧸ KU σ N), fun m hm => ?_⟩
  obtain ⟨hmL, hm0, hmLL, hmM⟩ := hm
  generalize -(Valued.v (mat m' 0 0)).log = a at hvx hm0 hmLL
  have hmiL : m⁻¹ ∈ leviU σ (blk N) := inv_mem hmL
  have hcL : m⁻¹ * m' ∈ leviU σ (blk N) := mul_mem hmiL hm'L
  have hcK : m⁻¹ * m' ∈ KU σ (N + 2) := by
    rw [mem_KU_iff hσv]
    intro i j
    by_cases hij : blk N i = blk N j
    swap
    · rw [hcL i j hij]; exact zero_mem _
    rw [mat_mul, Matrix.mul_apply, sum_idx]
    rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
      simp at hij
    · rw [Finset.sum_eq_zero (fun l _ => by rw [hmiL 0 (mid l) (by simp), zero_mul]),
        hmiL 0 (Fin.last _) (by simp), zero_mul, add_zero, add_zero, mat_inv_apply, rev_zero_eq_last, hmLL,
        map_zpow₀, hσϖ]
      rw [intL, Valuation.mem_integer_iff]
      rw [map_mul, map_zpow₀, hϖ, hvx, ← WithZero.exp_zsmul, ← WithZero.exp_add,
        show (-a) • (-1 : ℤ) + -a = 0 by rw [smul_eq_mul]; ring, WithZero.exp_zero]
    · rw [hmiL (mid i) 0 (by simp), zero_mul, zero_add, hmiL (mid i) (Fin.last _) (by simp), zero_mul, add_zero]
      have e : ∑ l, mat m⁻¹ (mid i) (mid l) * mat m' (mid l) (mid j) = mat ((g₀ * k₀)⁻¹ * g₀) i j := by
        rw [mat_mul, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [mat_inv_apply, mat_inv_apply, ← mid_rev, ← mid_rev, hmM, hout, hg₀]
        rfl
      rw [e, show (g₀ * k₀)⁻¹ * g₀ = k₀⁻¹ by group]
      exact P.fSatake_K_int (inv_mem hk₀) i j
    · rw [Finset.sum_eq_zero (fun l _ => by rw [hmiL (Fin.last _) (mid l) (by simp), zero_mul]),
        hmiL (Fin.last _) 0 (by simp), zero_mul, zero_add, zero_add, mat_inv_apply, rev_last_eq_zero, hm0,
        map_zpow₀, hσϖ, eq_inv_of_mul_eq_one_right hxL, intL, Valuation.mem_integer_iff, map_mul, map_inv₀, hσv,
        map_zpow₀, hϖ, hvx, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add,
        show a • (-1 : ℤ) + -(-a) = 0 by rw [smul_eq_mul]; ring, WithZero.exp_zero]
  obtain ⟨hr, -⟩ := leviRad L σ (N + 2) (blk N) hσv (m⁻¹ * m') hcL (m'⁻¹ * b) hu'
  exact ⟨(m⁻¹ * m') * (m'⁻¹ * b) * (m⁻¹ * m')⁻¹, hr, (m⁻¹ * m') * k, mul_mem hcK hk, by group⟩

end GlobalTheory.InertZeta
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem _root_.GlobalTheory.InertZeta.leviExists : _root_.GlobalTheory.InertZeta.LeviExists := by
  intro L _ _ ϖ σ q N hq a g₀
  obtain ⟨-, -, hσϖ, hv, -⟩ := hq
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    simp at hv
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.SatakeWeyl.embExists L σ (N + 2) N _root_.GlobalTheory.InertZeta.mid
    _root_.GlobalTheory.InertZeta.mid_injective _root_.GlobalTheory.InertZeta.mid_rev
  obtain ⟨h1, h2⟩ := hι g₀
  set d : Fin (N + 2) → L := fun i => if i = 0 then ϖ ^ a else if i = Fin.last (N + 1) then ϖ ^ (-a) else 1
  have hd : ∀ i, σ (d i) * d i.rev = 1 := by
    intro i
    rcases _root_.GlobalTheory.InertZeta.idx_cases i with rfl | ⟨k, rfl⟩ | rfl
    · simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, mul_inv_cancel₀ (zpow_ne_zero a hϖ)]
    · simp [d, ← _root_.GlobalTheory.InertZeta.mid_rev, _root_.GlobalTheory.InertZeta.mid_ne_zero,
        _root_.GlobalTheory.InertZeta.mid_ne_last]
    · simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, inv_mul_cancel₀ (zpow_ne_zero a hϖ)]
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.SatakeWeyl.exists_mat (σ := σ) (Matrix.diagonal d) (by
    ext i j
    unfold _root_.Formalism.UG.cT
    rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, _root_.Formalism.UG.P.fIwasawa_antiJ]
    split_ifs with h
    · subst h
      simpa using hd i
    · simp)
  have h0 : (0 : Fin (N + 2)) ∉ Set.range _root_.GlobalTheory.InertZeta.mid :=
    fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_zero k hk
  have hl : Fin.last (N + 1) ∉ Set.range _root_.GlobalTheory.InertZeta.mid :=
    fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_last k hk
  have hm : _root_.GlobalTheory.SatakeWeyl.mat (D * ι g₀) =
      Matrix.diagonal d * _root_.GlobalTheory.SatakeWeyl.mat (ι g₀) := by
    rw [← hD]
    rfl
  refine ⟨D * ι g₀, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hm, Matrix.diagonal_mul]
    have hne : i ≠ j := fun h => hij (h ▸ rfl)
    by_cases hi : i ∈ Set.range _root_.GlobalTheory.InertZeta.mid
    · by_cases hj : j ∈ Set.range _root_.GlobalTheory.InertZeta.mid
      · obtain ⟨k, rfl⟩ := hi
        obtain ⟨l, rfl⟩ := hj
        simp [_root_.GlobalTheory.InertZeta.blk_mid] at hij
      · rw [h2 i j (Or.inr hj), Matrix.one_apply_ne hne, mul_zero]
    · rw [h2 i j (Or.inl hi), Matrix.one_apply_ne hne, mul_zero]
  · rw [hm, Matrix.diagonal_mul, h2 0 0 (Or.inl h0), Matrix.one_apply_eq, mul_one]
    simp [d]
  · rw [hm, Matrix.diagonal_mul, h2 _ _ (Or.inl hl), Matrix.one_apply_eq, mul_one]
    simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero]
  · intro i j
    rw [hm, Matrix.diagonal_mul, h1]
    simp [d, _root_.GlobalTheory.InertZeta.mid_ne_zero, _root_.GlobalTheory.InertZeta.mid_ne_last]

end GlobalTheory.InertZeta
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem blk_eq_zero_iff {l : Fin (N + 2)} : blk N l = 0 ↔ l = 0 := by
  rcases idx_cases l with rfl | ⟨j, rfl⟩ | rfl
  · simp
  · simp [mid_ne_zero]
  · simp [last_ne_zero]

theorem blk_eq_two_iff {l : Fin (N + 2)} : blk N l = 2 ↔ l = Fin.last (N + 1) := by
  rcases idx_cases l with rfl | ⟨j, rfl⟩ | rfl
  · simp [(last_ne_zero (N := N)).symm]
  · simp [mid_ne_last]
  · simp

theorem levi_mul_apply_zero {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (j : Fin (N + 2)) : (mat x * M) 0 j = mat x 0 0 * M 0 j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single 0]
  · intro l _ hl
    rw [hx 0 l (by rw [blk_zero]; exact fun h => hl (blk_eq_zero_iff.1 h.symm)), zero_mul]
  · simp

theorem levi_mul_apply_last {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (j : Fin (N + 2)) : (mat x * M) (Fin.last (N + 1)) j = mat x (Fin.last (N + 1)) (Fin.last (N + 1)) * M (Fin.last (N + 1)) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last (N + 1))]
  · intro l _ hl
    rw [hx _ l (by rw [blk_last]; exact fun h => hl (blk_eq_two_iff.1 h.symm)), zero_mul]
  · simp

theorem levi_mul_apply_mid {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (i j : Fin (N + 2)) (k : Fin N) (hi : i = mid k) :
    (mat x * M) i j = ∑ l, mat x i (mid l) * M (mid l) j := by
  subst hi
  rw [Matrix.mul_apply, sum_idx (fun l => mat x (mid k) l * M l j), hx (mid k) 0 (by simp), hx (mid k) _ (by simp)]
  simp

end

theorem cosetInj : CosetInj := by
  intro L _ _ ϖ σ q N hU a a' g₀ g₀' m m' hm hm' u hu u' hu' hK
  have hσ : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hvz : ∀ k : ℤ, Valued.v (ϖ ^ k) = WithZero.exp (-k) := fun k => by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  set n := m⁻¹ * m' with hn_def
  have hnL : n ∈ leviU σ (blk N) := mul_mem (inv_mem hm.1) hm'.1
  have hconj : n⁻¹ * u⁻¹ * n⁻¹⁻¹ ∈ radQ σ N :=
    (leviRad L σ (N + 2) (blk N) hσ n⁻¹ (inv_mem hnL) u⁻¹ (inv_mem hu)).1
  have he : (m * u)⁻¹ * (m' * u') = n * ((n⁻¹ * u⁻¹ * n⁻¹⁻¹) * u') := by
    rw [hn_def]; group
  have hnK : n ∈ KU σ (N + 2) :=
    (leviRad L σ (N + 2) (blk N) hσ n hnL _ (mul_mem hconj hu')).2 (he ▸ hK)
  have hint : ∀ i j, mat n i j ∈ intL L := (mem_KU_iff hσ n).1 hnK
  have hmn : mat m * mat n = mat m' := by rw [← mat_mul, hn_def, mul_inv_cancel_left]
  have h0 : ϖ ^ a * mat n 0 0 = ϖ ^ a' := by
    rw [← hm.2.1, ← hm'.2.1, ← hmn, levi_mul_apply_zero hm.1]
  have hl : ϖ ^ (-a) * mat n (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a') := by
    rw [← hm.2.2.1, ← hm'.2.2.1, ← hmn, levi_mul_apply_last hm.1]
  have hv0 := hint 0 0
  have hvl := hint (Fin.last (N + 1)) (Fin.last (N + 1))
  have e0 : mat n 0 0 = ϖ ^ (a' - a) := by
    rw [zpow_sub₀ hϖ0, ← h0]; field_simp
  have el : mat n (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (a - a') := by
    rw [show a - a' = -a' - -a by ring, zpow_sub₀ hϖ0, ← hl]; field_simp
  change Valued.v (mat n 0 0) ≤ 1 at hv0
  change Valued.v (mat n (Fin.last (N + 1)) (Fin.last (N + 1))) ≤ 1 at hvl
  rw [e0, hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv0
  rw [el, hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at hvl
  refine ⟨by omega, ?_⟩
  rw [mem_KU_iff hσ]
  have hmid : mat g₀ * Matrix.of (fun i j => mat n (mid i) (mid j)) = mat g₀' := by
    ext i j
    rw [← hm'.2.2.2, ← hmn, levi_mul_apply_mid hm.1 _ _ _ i rfl, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [hm.2.2.2]; rfl
  intro i j
  rw [mat_mul, ← hmid, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  exact hint _ _

end GlobalTheory.InertZeta
end

section

noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem traceIndex : TraceIndex := by
  intro L _ _ ϖ σ q f hU
  have hq := traceZeroIndex_of_intIndex intIndex L ϖ σ q hU
  obtain ⟨-, -, hϖ, h4, -, -, -⟩ := hU
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  have hϖO : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [h4, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    omega
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have memT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y + y = 0 := fun y => Iff.rfl
  have hinj : ∀ e : ℕ, Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e)) := fun e =>
    mul_right_injective₀ (pow_ne_zero e h0)
  have hmap : ∀ e : ℕ, (traceZero σ (ϖ ^ e)).map (AddMonoidHom.mulLeft (ϖ ^ e)) = T := fun e => by
    ext x
    rw [AddSubgroup.mem_map, memT]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_traceZero] at hy
      refine ⟨hy.1, ?_⟩
      rw [AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]
      linear_combination ϖ ^ e * hy.2
    · rintro ⟨hx, hx0⟩
      refine ⟨(ϖ ^ e)⁻¹ * x, ?_, ?_⟩
      · rw [mem_traceZero, mul_inv_cancel_left₀ (pow_ne_zero e h0)]
        refine ⟨hx, ?_⟩
        rw [map_mul, map_inv₀, map_pow, hϖ]
        linear_combination (ϖ ^ e)⁻¹ * hx0
      · rw [AddMonoidHom.coe_mulLeft, mul_inv_cancel_left₀ (pow_ne_zero e h0)]
  have h1 : traceZero σ 1 = T := by
    ext x
    rw [mem_traceZero, memT, one_mul]
  have hmulle : ∀ e : ℕ, T.map (AddMonoidHom.mulLeft (ϖ ^ e)) ≤ T := by
    rintro e _ ⟨y, hy, rfl⟩
    have hy : y ∈ T := hy
    rw [memT] at hy ⊢
    refine ⟨(intL L).mul_mem (pow_mem hϖO e) hy.1, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]
    linear_combination ϖ ^ e * hy.2
  rw [← AddSubgroup.relIndex_map_map_of_injective (traceZero σ 1) (traceZero σ (ϖ ^ f)) (hinj f), hmap f, h1]
  induction f with
  | zero =>
    have : T.map (AddMonoidHom.mulLeft (ϖ ^ 0)) = T := by
      ext x
      simp [AddSubgroup.mem_map]
    rw [this]
    simp
  | succ e ih =>
    have hcomp : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) =
        (T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨o, ho, rfl⟩
        exact ⟨ϖ * o, ⟨o, ho, rfl⟩, by rw [pow_succ, mul_assoc]⟩
      · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
        exact ⟨o, ho, by rw [pow_succ, mul_assoc]⟩
    have hstep : (T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1)))).relIndex
        (T.map (AddMonoidHom.mulLeft (ϖ ^ e))) = q := by
      rw [hcomp, AddSubgroup.relIndex_map_map_of_injective _ _ (hinj e)]
      exact hq
    have hle1 : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) ≤ T.map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      rw [hcomp]
      exact AddSubgroup.map_mono (by simpa using hmulle 1)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 (hmulle e), hstep, ih]
    exact (pow_succ' _ _).symm

end GlobalTheory.InertZeta

end
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.cyclicVector_generatedAlgebra_structure : GlobalTheory.RegSS.CyclicAlgebra := by
  first | exact @GlobalTheory.RegSS.CycAlg.cyclicAlgebra | exact GlobalTheory.RegSS.CycAlg.cyclicAlgebra | (intros; apply GlobalTheory.RegSS.CycAlg.cyclicAlgebra <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.hermitianTraceForm_of_traceForm_perfect : GlobalTheory.RegSS.TracePerfect → GlobalTheory.RegSS.TraceClause := by
  first | exact @GlobalTheory.RegSS.traceClause_of_tracePerfect | exact GlobalTheory.RegSS.traceClause_of_tracePerfect | (intros; apply GlobalTheory.RegSS.traceClause_of_tracePerfect <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.regularSemisimple_tensor_commutant : GlobalTheory.RegSS.PointsCommutant := by
  first | exact @GlobalTheory.RegSS.pointsCommutant | exact GlobalTheory.RegSS.pointsCommutant | (intros; apply GlobalTheory.RegSS.pointsCommutant <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.split_subtorus_laurentPolynomial_points : GlobalTheory.RegSS.SubtorusLaurent := by
  first | exact @GlobalTheory.RegSS.subtorusLaurent | exact GlobalTheory.RegSS.subtorusLaurent | (intros; apply GlobalTheory.RegSS.subtorusLaurent <;> assumption)
end
