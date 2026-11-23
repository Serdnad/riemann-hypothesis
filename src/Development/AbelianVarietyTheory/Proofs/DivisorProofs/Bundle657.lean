module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle101
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle616
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014

@[expose] public section

section

noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.Four

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

def unitaryFourUpperLeftBlock (g : GU σ 4) : Matrix (Fin 2) (Fin 2) L := !![mat g 0 0, mat g 0 1; mat g 1 0, mat g 1 1]

theorem unitaryFourUpperLeftBlock_mul_of_mem_levi {g : GU σ 4} (g' : GU σ 4) (hg : g ∈ leviU σ ![0, 0, 1, 1]) :
    unitaryFourUpperLeftBlock (g * g') = unitaryFourUpperLeftBlock g * unitaryFourUpperLeftBlock g' := by
  have h02 := hg 0 2 (by decide)
  have h03 := hg 0 3 (by decide)
  have h12 := hg 1 2 (by decide)
  have h13 := hg 1 3 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryFourUpperLeftBlock, mat_mul, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem unitaryFourUpperLeftBlock_one : unitaryFourUpperLeftBlock (1 : GU σ 4) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitaryFourUpperLeftBlock, mat_one]

theorem unitaryFourUpperLeftBlock_injective_on_levi {g g' : GU σ 4} (hg : g ∈ leviU σ ![0, 0, 1, 1]) (hg' : g' ∈ leviU σ ![0, 0, 1, 1])
    (h : unitaryFourUpperLeftBlock g = unitaryFourUpperLeftBlock g') : g = g' := by
  have h1 : unitaryFourUpperLeftBlock g⁻¹ * unitaryFourUpperLeftBlock g' = 1 := by
    rw [← h, ← unitaryFourUpperLeftBlock_mul_of_mem_levi _ (inv_mem hg), inv_mul_cancel, unitaryFourUpperLeftBlock_one]
  have h2 : unitaryFourUpperLeftBlock g' * unitaryFourUpperLeftBlock g'⁻¹ = 1 := by
    rw [← unitaryFourUpperLeftBlock_mul_of_mem_levi _ hg', mul_inv_cancel, unitaryFourUpperLeftBlock_one]
  have h3 : unitaryFourUpperLeftBlock g⁻¹ = unitaryFourUpperLeftBlock g'⁻¹ := left_inv_eq_right_inv h1 h2
  have low : ∀ i j : Fin 4, mat g⁻¹ j.rev i.rev = mat g'⁻¹ j.rev i.rev → mat g i j = mat g' i j := by
    intro i j e
    have e1 := mat_inv_apply g⁻¹ i j
    have e2 := mat_inv_apply g'⁻¹ i j
    rw [inv_inv] at e1 e2
    rw [e1, e2, e]
  have off : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ ![0, 0, 1, 1] j → mat g i j = mat g' i j :=
    fun i j e => by rw [hg i j e, hg' i j e]
  apply mat_injective
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h 0) 0
  · exact congrFun (congrFun h 0) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact congrFun (congrFun h 1) 0
  · exact congrFun (congrFun h 1) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 1)
  · exact low _ _ (congrFun (congrFun h3 0) 1)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 0)
  · exact low _ _ (congrFun (congrFun h3 0) 0)

theorem exists_lift (h1 : ∀ x, σ (σ x) = x) (h2 : ∀ x, Valued.v (σ x) = Valued.v x) {p r u w : L}
    (hp : p ∈ intL L) (hr : r ∈ intL L) (hu : u ∈ intL L) (hw : w ∈ intL L) (hd : p * w - r * u = -1) :
    ∃ k ∈ KU σ 4 ⊓ leviU σ ![0, 0, 1, 1], unitaryFourUpperLeftBlock k = !![p, r; u, w] := by
  have hd' : σ p * σ w - σ r * σ u = -1 := by simpa using congrArg σ hd
  have hs : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1
    rw [h2]; exact hx
  obtain ⟨k, hk⟩ := exists_mat (σ := σ) !![p, r, 0, 0; u, w, 0, 0; 0, 0, -σ p, σ r; 0, 0, σ u, -σ w] (by
    ext i j
    rw [Matrix.mul_apply]
    simp only [P.fSatake_cTJ]
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, antiJ, h1, Fin.rev] <;>
      first | linear_combination hd | linear_combination -hd | linear_combination hd' | linear_combination -hd' | ring)
  refine ⟨k, ⟨(mem_KU_iff h2 k).2 fun i j => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [hk]
    fin_cases i <;> fin_cases j <;> simp [hp, hr, hu, hw, hs _ hp, hs _ hr, hs _ hu, hs _ hw]
  · rw [hk]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [unitaryFourUpperLeftBlock, hk]

theorem exists_conj {A D ξ : L} (hA : A ≠ 0) (hD : D ≠ 0) :
    ∃ p ∈ intL L, ∃ r ∈ intL L, ∃ u ∈ intL L, ∃ w ∈ intL L, p * w - r * u = -1 ∧
      !![D, -(A * ξ); 0, A] = !![p, r; u, w] * !![A, A * ξ; 0, D] * !![p, r; u, w] := by
  have mem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  by_cases h1 : ξ ∈ intL L
  · refine ⟨-ξ, neg_mem h1, 1, one_mem _, 1, one_mem _, 0, zero_mem _, by ring, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  by_cases h2 : A * ξ / D ∈ intL L
  · refine ⟨0, zero_mem _, 1, one_mem _, 1, one_mem _, -(A * ξ / D), neg_mem h2, by ring, ?_⟩
    obtain ⟨ζ, hζ⟩ : ∃ ζ, A * ξ = D * ζ := ⟨A * ξ / D, by field_simp⟩
    rw [hζ, mul_div_cancel_left₀ _ hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  have hξ : ξ ≠ 0 := fun e => h1 (e ▸ zero_mem _)
  have inv : ∀ x : L, x ∉ intL L → x⁻¹ ∈ intL L := fun x hx => by
    rw [mem] at hx ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (not_le.1 hx).le
  refine ⟨1, one_mem _, 0, zero_mem _, -(ξ⁻¹ - (A * ξ / D)⁻¹), neg_mem (sub_mem (inv _ h1) (inv _ h2)),
    -1, neg_mem (one_mem _), by ring, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem cartanFour : GlobalTheory.SatakeWeyl.CartanFour := by
  intro L _ _ ϖ σ q hU x y s s' hs hs' a ha
  obtain ⟨h1, h2, -, h4, -⟩ := hU
  have hϖ : ϖ ≠ 0 := fun e => by rw [e, map_zero] at h4; exact WithZero.zero_ne_coe h4
  have dl : ∀ (t : GU σ 4) (d : Fin 4 → L), mat t = Matrix.diagonal d → t ∈ leviU σ ![0, 0, 1, 1] :=
    fun t d e i j hij => by rw [e]; exact Matrix.diagonal_apply_ne _ fun e => hij (e ▸ rfl)
  have hsl := dl _ _ hs
  have hsl' := dl _ _ hs'
  have us : unitaryFourUpperLeftBlock s = !![ϖ ^ x, 0; 0, ϖ ^ y] := by simp [unitaryFourUpperLeftBlock, hs]
  have us' : unitaryFourUpperLeftBlock s' = !![ϖ ^ y, 0; 0, ϖ ^ x] := by simp [unitaryFourUpperLeftBlock, hs']
  have ua : unitaryFourUpperLeftBlock a = !![1, mat a 0 1; 0, 1] := by
    simp [unitaryFourUpperLeftBlock, ha.1 0 0 (by decide), ha.1 1 0 (by decide), ha.1 1 1 (by decide)]
  obtain ⟨p, hp, r, hr, u, hu, w, hw, hd, e⟩ :=
    exists_conj (ξ := mat a 0 1) (zpow_ne_zero x hϖ) (zpow_ne_zero y hϖ)
  obtain ⟨k, hk, uk⟩ := exists_lift h1 h2 hp hr hu hw hd
  refine ⟨k, hk.1, k, hk, ?_⟩
  rw [inv_mul_eq_iff_eq_mul]
  refine unitaryFourUpperLeftBlock_injective_on_levi hsl' (mul_mem ha.2 (mul_mem (mul_mem hk.2 (mul_mem hsl ha.2)) hk.2)) ?_
  have usa : unitaryFourUpperLeftBlock (s * a) = !![ϖ ^ x, ϖ ^ x * mat a 0 1; 0, ϖ ^ y] := by
    rw [unitaryFourUpperLeftBlock_mul_of_mem_levi _ hsl, us, ua]; simp
  rw [unitaryFourUpperLeftBlock_mul_of_mem_levi _ ha.2, unitaryFourUpperLeftBlock_mul_of_mem_levi _ (mul_mem hk.2 (mul_mem hsl ha.2)), unitaryFourUpperLeftBlock_mul_of_mem_levi _ hk.2, usa, uk, ← e, us', ua]
  simp [mul_comm]

end GlobalTheory.SatakeWeyl.Four

end
end

section

noncomputable section

open Formalism.UG

namespace GlobalTheory.SatakeWeyl.IdxFour

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

def rootMat (σ : L →+* L) (x : L) : Matrix (Fin 4) (Fin 4) L :=
  !![1, x, 0, 0; 0, 1, 0, 0; 0, 0, 1, -σ x; 0, 0, 0, 1]

theorem rootMat_unitary (hσ : ∀ x, σ (σ x) = x) (x : L) :
    cT σ (rootMat σ x) * antiJ L 4 * rootMat σ x = antiJ L 4 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [P.fSatake_cTJ, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [rootMat, antiJ, Fin.rev, hσ]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem rootMat_add (x y : L) : rootMat σ (x + y) = rootMat σ x * rootMat σ y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, Matrix.mul_apply, Fin.sum_univ_four, add_comm]

theorem exists_hom (hσ : ∀ x, σ (σ x) = x) :
    ∃ φ : Multiplicative L →* GU σ 4, ∀ x, mat (φ x) = rootMat σ x.toAdd := by
  choose f hf using fun x : L => exists_mat (rootMat σ x) (rootMat_unitary hσ x)
  refine ⟨MonoidHom.mk' (fun x => f x.toAdd) fun a b => mat_injective ?_, fun x => hf _⟩
  rw [mat_mul, hf, hf, hf, toAdd_mul, rootMat_add]

theorem mat_of_mem (hσ : ∀ x, σ (σ x) = x) {g : GU σ 4} (hg : g ∈ rootU σ ![0, 0, 1, 1]) :
    mat g = rootMat σ (mat g 0 1) := by
  have h1 : ∀ i j : Fin 4, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 4) (Fin 4) L) i j := hg.1
  have h2 : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ (![0, 0, 1, 1] : Fin 4 → ℕ) j → mat g i j = 0 := hg.2
  have h3 : cT σ (mat g) * antiJ L 4 * mat g = antiJ L 4 := g.2
  have h4 := congrFun (congrFun h3 1) 3
  rw [Matrix.mul_apply] at h4
  simp only [P.fSatake_cTJ, Fin.sum_univ_four] at h4
  have e00 := h1 0 0 (by decide)
  have e11 := h1 1 1 (by decide)
  have e22 := h1 2 2 (by decide)
  have e33 := h1 3 3 (by decide)
  have e10 := h1 1 0 (by decide)
  have e32 := h1 3 2 (by decide)
  have e02 := h2 0 2 (by decide)
  have e03 := h2 0 3 (by decide)
  have e12 := h2 1 2 (by decide)
  have e13 := h2 1 3 (by decide)
  have e20 := h2 2 0 (by decide)
  have e21 := h2 2 1 (by decide)
  have e30 := h2 3 0 (by decide)
  have e31 := h2 3 1 (by decide)
  have r0 : Fin.rev (0 : Fin 4) = 3 := rfl
  have r1 : Fin.rev (1 : Fin 4) = 2 := rfl
  have r2 : Fin.rev (2 : Fin 4) = 1 := rfl
  have r3 : Fin.rev (3 : Fin 4) = 0 := rfl
  rw [r0, r1, r2, r3, e03, e13, e11, e33] at h4
  have e23 : mat g 2 3 = -σ (mat g 0 1) := by
    simp [antiJ] at h4
    exact eq_neg_of_add_eq_zero_left h4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, *]

theorem mem_root {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) : g ∈ rootU σ ![0, 0, 1, 1] := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [hg]
    fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢
  · rw [hg]
    fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢

theorem mem_K_iff (hv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) :
    g ∈ KU σ 4 ↔ x ∈ intL L := by
  rw [mem_KU_iff hv, hg]
  refine ⟨fun h => by simpa [rootMat] using h 0 1, fun h i j => ?_⟩
  have h' : σ x ∈ intL L := by
    show Valued.v (σ x) ≤ 1
    rw [hv]
    exact h
  fin_cases i <;> fin_cases j <;> simp [rootMat, h, h', one_mem, zero_mem]

theorem indexFour (hI : IntIndex) : IndexFour := by
  intro L _ _ ϖ σ q hU s₀ hs
  obtain ⟨φ, hφ⟩ := exists_hom hU.1
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    have := hU.2.2.2.1
    simp at this
  have hinj : Function.Injective φ := fun a b h => by
    have := congrFun (congrFun ((hφ a).symm.trans ((congrArg mat h).trans (hφ b))) 0) 1
    simpa [rootMat] using this
  have hK : KU σ 4 ⊓ rootU σ ![0, 0, 1, 1] = (AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      have e := mat_of_mem hU.1 h2
      exact ⟨Multiplicative.ofAdd (mat g 0 1), (mem_K_iff hU.2.1 e).1 h1, mat_injective ((hφ _).trans e.symm)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(mem_K_iff hU.2.1 (hφ x)).2 hx, mem_root (hφ x)⟩
  have hc : ∀ x : L, s₀ * φ (Multiplicative.ofAdd x) * s₀⁻¹ = φ (Multiplicative.ofAdd (ϖ * x)) := by
    intro x
    rw [mul_inv_eq_iff_eq_mul]
    apply mat_injective
    rw [mat_mul, mat_mul, hφ, hφ, hs]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [rootMat, hU.2.2.1]
    field_simp
  have hK' : ((AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ).map (MulAut.conj s₀).toMonoidHom =
      (AddSubgroup.toSubgroup ((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ))).map φ := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨Multiplicative.ofAdd (ϖ * x.toAdd), ⟨x.toAdd, hx, rfl⟩, (hc x.toAdd).symm⟩
    · rintro ⟨y, ⟨x, hx, e⟩, rfl⟩
      refine ⟨φ (Multiplicative.ofAdd x), ⟨_, hx, rfl⟩, (hc x).trans (congrArg φ ?_)⟩
      exact congrArg Multiplicative.ofAdd e
  rw [hK, hK', Subgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_toSubgroup]
  exact hI L ϖ σ q hU

end GlobalTheory.SatakeWeyl.IdxFour

end
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem antiJ_eq_one_rev {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if i.rev = j then 1 else 0 := by
  have := antiJ_mul_apply (1 : Matrix (Fin n) (Fin n) L) i j
  rw [Matrix.mul_one] at this
  rw [this, Matrix.one_apply]

theorem exists_mat_submatrix {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n r : ℕ}
    (e : Fin r → Fin n) (he : Function.Injective e) (hrev : ∀ i, e i.rev = (e i).rev) (m : GU σ n)
    (hm : ∀ a b, (a ∉ Set.range e ∨ b ∉ Set.range e) → mat m a b = (1 : Matrix (Fin n) (Fin n) L) a b) :
    ∃ a : GU σ r, mat a = (mat m).submatrix e e := by
  apply exists_mat
  ext i j
  have h1 : cT σ (mat m) * antiJ L n * mat m = antiJ L n := m.2
  have h2 := congrFun (congrFun h1 (e i)) (e j)
  rw [Matrix.mul_apply] at h2 ⊢
  simp only [P.fSatake_cTJ] at h2 ⊢
  rw [antiJ_eq_one_rev] at h2 ⊢
  rw [← hrev] at h2
  simp only [he.eq_iff] at h2
  rw [← h2]
  refine Fintype.sum_of_injective e he _ _ ?_ ?_
  · intro l hl
    rw [hm l (e j) (Or.inl hl), Matrix.one_apply_ne (fun h => hl ⟨j, h.symm⟩), mul_zero]
  · intro l
    simp only [Matrix.submatrix_apply, hrev]

theorem unipSplit_of_leviPart (hL : LeviPart) : UnipSplit := by
  intro L _ _ σ n r e β γ ι hB hι u hu
  obtain ⟨hmono, hrev, hβ, hβrev, hβe, hγ⟩ := hB
  have hu' : ∀ i j : Fin n, j.val ≤ i.val → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j := hu
  have htri : (mat u).BlockTriangular β := by
    intro a b hab
    have hba : b < a := hβ.reflect_lt hab
    rw [hu' a b hba.le, Matrix.one_apply_ne hba.ne']
  obtain ⟨m, hmL, hmu, hrad⟩ := hL L σ n β hβrev u htri
  have hmL' : ∀ i j, β i ≠ β j → mat m i j = 0 := hmL
  have hm : ∀ a b, (a ∉ Set.range e ∨ b ∉ Set.range e) → mat m a b = (1 : Matrix (Fin n) (Fin n) L) a b := by
    intro a b hab
    by_cases h : β a = β b
    · rcases hβe a b h with rfl | ⟨h1, h2⟩
      · rw [hmu a a rfl, hu' a a le_rfl]
      · rcases hab with h' | h'
        · exact absurd h1 h'
        · exact absurd h2 h'
    · rw [hmL' a b h, Matrix.one_apply_ne (fun e' : a = b => h (congrArg β e'))]
  obtain ⟨a, ha⟩ := exists_mat_submatrix e hmono.injective hrev m hm
  have hιa : ι a = m := by
    apply mat_injective
    ext x y
    by_cases hxy : x ∉ Set.range e ∨ y ∉ Set.range e
    · rw [(hι a).2 x y hxy, hm x y hxy]
    · push Not at hxy
      obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hxy
      rw [(hι a).1 i j, ha, Matrix.submatrix_apply]
  refine ⟨a, ⟨?_, ?_⟩, m⁻¹ * u, hrad, by rw [hιa, mul_inv_cancel_left]⟩
  · intro i j hij
    have hij' : j ≤ i := hij
    rw [ha, Matrix.submatrix_apply]
    by_cases h : β (e i) = β (e j)
    · rw [hmu _ _ h, hu' _ _ (hmono.monotone hij'), Matrix.one_apply, Matrix.one_apply]
      simp only [hmono.injective.eq_iff]
    · rw [hmL' _ _ h, Matrix.one_apply_ne (fun e' : i = j => h (by rw [e']))]
  · intro i j hij
    rw [ha, Matrix.submatrix_apply]
    exact hmL' _ _ fun h => hij ((hγ i j).1 h)

end GlobalTheory.SatakeWeyl
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem exists_diag_zpow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L}
    (hσ : σ ϖ = ϖ) (h0 : ϖ ≠ 0) {r : ℕ} (b : Fin r → ℤ) (hb : ∀ i, b i.rev = -b i) :
    ∃ s : GU σ r, mat s = Matrix.diagonal (fun i => ϖ ^ b i) := by
  obtain ⟨s, hs, -⟩ := P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by
    rw [map_zpow₀, hσ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  exact ⟨s, hs⟩

theorem leviStep_of_steps (hR : RankOne) (hE : EmbExists) (hM : EmbMem) (hT : EmbTorus) (hL : LeviRad)
    (hS : UnipSplit) (hC : Contract) (hJ : TorusConj) : LeviStep := by
  intro L _ _ ϖ σ q n r e β γ b B B' Q d t t' h hU hD hb hbd hB hB' hBB hd ht ht' hQ hidx hcar hh
  have hv := hU.2.1
  have hϖ : σ ϖ = ϖ := hU.2.2.1
  have h0 : ϖ ≠ 0 := by
    intro h0
    have := hU.2.2.2.1
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hinj : Function.Injective e := hD.1.injective
  obtain ⟨ι, hι⟩ := hE L σ n r e hinj hD.2.1
  obtain ⟨s₀, hs₀⟩ := exists_diag_zpow hϖ h0 b hb
  obtain ⟨s, hs⟩ := exists_diag_zpow hϖ h0 (fun i => B (e i)) (fun i => by rw [hD.2.1, hB])
  obtain ⟨s', hs'⟩ := exists_diag_zpow hϖ h0 (fun i => B' (e i)) (fun i => by rw [hD.2.1, hB'])
  obtain ⟨z, hz, hz', hzc⟩ := hT L σ n r e ι hinj hι (fun a => ϖ ^ B a) (fun a => ϖ ^ B' a) t t' s s' ht ht' hs hs'
    (fun a ha => by simp only [hBB a ha])
  have hMem := hM L σ n r e β γ ι hv hD hι
  have hCon := fun g hg => hC L ϖ σ q r γ b s₀ g hU hbd hs₀ hg
  have hnorm : s₀ ∈ Subgroup.normalizer ((rootU σ γ : Subgroup (GU σ r)) : Set (GU σ r)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => (hCon g hg).1, fun hg => ?_⟩
    have := (hCon _ hg).2.1
    simpa [mul_assoc] using this
  set c : MulAut (rootU σ γ) := (rootU σ γ).normalizerMonoidHom ⟨s₀, hnorm⟩ with hc
  have hc1 : ∀ a, ((c a : rootU σ γ) : GU σ r) = s₀ * a * s₀⁻¹ := fun a => rfl
  have hcz : ∀ (j : ℤ) a, (((c ^ j) a : rootU σ γ) : GU σ r) = s₀ ^ j * a * (s₀ ^ j)⁻¹ := fun j a => by
    rw [hc, ← map_zpow, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hcn : ∀ (j : ℕ) a, (((c ^ j) a : rootU σ γ) : GU σ r) = s₀ ^ j * a * (s₀ ^ j)⁻¹ := fun j a => by
    rw [hc, ← map_pow, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hcomap : (KU σ n).comap (ι.comp (rootU σ γ).subtype) = (KU σ r ⊓ rootU σ γ).subgroupOf (rootU σ γ) := by
    ext a
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun ha => ⟨(hMem a).1.1 ha, a.2⟩, fun ha => (hMem a).1.2 ha.1⟩
  have hLR := hL L σ n β hv
  refine hR (GU σ n) (rootU σ γ) (KU σ n) (radU σ Fin.val) (radU σ β) (ι.comp (rootU σ γ).subtype) c Q d h t t'
    hh.1 (P.finite_supp (KU σ n) (P.isCommensurated_integral_unitary_of_unramified hU n) h hh) ?_ ?_ ?_ ?_ ?_ ?_ hQ ?_ ?_ ?_ ?_
  · intro u hu i j hij
    exact hu i j (hD.2.2.1 hij)
  · intro a
    exact (hMem a).2.2 a.2.1
  · intro u hu
    obtain ⟨a, ha, u', hu', e1⟩ := hS L σ n r e β γ ι hD hι u hu
    exact ⟨⟨a, ha⟩, u', hu', e1⟩
  · intro a u' hu'
    exact (hLR _ ((hMem a).2.1 a.2.2) u' hu').2
  · intro a u' hu'
    exact (hLR _ ((hMem a).2.1 a.2.2) u' hu').1
  · intro a ha
    exact (hMem _).1.2 ((hCon a a.2).2.2.1 ((hMem a).1.1 ha))
  · rw [hcomap, ← Subgroup.relIndex_map_map_of_injective _ _ (rootU σ γ).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_right, ← hidx s₀ hs₀, Subgroup.map_map]
    congr 1
    conv_rhs => rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : KU σ r ⊓ rootU σ γ ≤ _), Subgroup.map_map]
    rfl
  · intro a
    obtain ⟨j, hj⟩ := (hCon a a.2).2.2.2
    refine ⟨j, (hMem _).1.2 ?_⟩
    rw [← hcn] at hj
    exact hj
  · intro a
    have e1 := hJ L ϖ σ r γ b (fun i => B' (e i)) d s₀ s' a h0 hd hs₀ hs' a.2.2
    show t' * ι a * t'⁻¹ = ι ((c ^ d) a : rootU σ γ)
    rw [hcz, ← e1, hz', map_mul, map_mul, map_inv, mul_assoc (ι s'), (hzc a).eq]
    group
  · intro a
    obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hcar s s' hs hs' a a.2
    have hk : ι k₂ ∈ leviU σ β := (hMem _).2.1 hk₂.2
    refine ⟨ι k₁, (hMem _).1.2 hk₁, ι k₂, (hMem _).1.2 hk₂.1, fun u hu => (hLR _ hk u hu).1, fun u hu => ?_, ?_⟩
    · simpa using (hLR _ (inv_mem hk) u hu).1
    · show (ι a)⁻¹ * t' = ι k₁ * (t * ι a) * ι k₂
      have e2 := congrArg ι e1
      simp only [map_mul, map_inv] at e2
      rw [hz, hz', ← mul_assoc, e2, mul_assoc (ι s), (hzc a).eq]
      simp only [mul_assoc]
      rw [(hzc k₂).eq]

end GlobalTheory.SatakeWeyl
end

section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

theorem _root_.GlobalTheory.T.finrank_homO_eq_augmentationQuotient_of_scalar_character : ∀ {k O C W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : C →+* k), (∀ c, τ (algebraMap C O c) = χ c • 1) → finrank k (homO σW τ) = finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := by
  first | exact @GlobalTheory.HTRho.finrank_homO_eq_quot_mSub | exact GlobalTheory.HTRho.finrank_homO_eq_quot_mSub | (intros; apply GlobalTheory.HTRho.finrank_homO_eq_quot_mSub <;> assumption)
end
