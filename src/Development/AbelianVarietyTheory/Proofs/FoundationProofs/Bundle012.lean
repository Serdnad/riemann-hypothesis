module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Tactic.Continuity
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama

@[expose] public section

section

open Module Submodule Function

namespace GlobalTheory

namespace MaximalMinor

section Cramer

variable {A R F ι κ : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup F]
  [Module R F] [Module A F] [IsScalarTower A R F] [Fintype ι] [DecidableEq ι]

theorem det_smul_eq_sum_det_update (b : Basis ι R F) (v : ι → F) (x : F) :
    b.det v • x = ∑ i, b.det (update v i x) • v i := by
  apply b.equivFun.injective
  have h := Matrix.mulVec_cramer (b.toMatrix v) (b.equivFun x)
  rw [map_smul, Basis.det_apply, ← h]
  ext j

  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Basis.equivFun_apply,
  smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.cramer_apply, Basis.det_apply,
  Basis.toMatrix_update, Basis.toMatrix_apply, mul_comm]

theorem mem_span_of_det_update_mem (b : Basis ι R F) {v : ι → F}
    (hv : b.det v ∈ nonZeroDivisors R) {x : F}
    (hx : ∀ i, b.det (update v i x) ∈ span A {b.det v}) : x ∈ span A (Set.range v) := by
  choose a ha using fun i => mem_span_singleton.1 (hx i)
  refine (mem_span_range_iff_exists_fun A).2 ⟨a, ?_⟩
  have h1 : b.det v • (∑ i, a i • v i) = b.det v • x := by
    rw [det_smul_eq_sum_det_update b v x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ha i, smul_assoc, ← algebraMap_smul R (a i), ← algebraMap_smul R (a i), smul_comm]
  apply b.equivFun.injective
  ext j
  have h2 := congrArg (fun y => b.equivFun y j) h1
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h2
  exact (mul_cancel_left_mem_nonZeroDivisors hv).1 h2

theorem span_range_comp_eq (b : Basis ι R F) (G : κ → F) {σ : ι → κ}
    (hσ : b.det (G ∘ σ) ∈ nonZeroDivisors R)
    (h : ∀ τ : ι → κ, b.det (G ∘ τ) ∈ span A {b.det (G ∘ σ)}) :
    span A (Set.range (G ∘ σ)) = span A (Set.range G) := by
  refine le_antisymm (span_mono (Set.range_comp_subset_range _ _)) (span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine mem_span_of_det_update_mem b hσ fun i => ?_
  rw [← comp_update]
  exact h _

end Cramer

end MaximalMinor

end GlobalTheory
end

section

namespace GlobalTheory.IdealPowerMembership

open MvPolynomial

theorem main : ∀ (K L : Type) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : FiniteDimensional K L], ∃ (f : MvPolynomial (Fin (Module.finrank K L)) K), MvPolynomial.IsHomogeneous f (Module.finrank K L) ∧ ∀ (x : L), (Algebra.norm K : L → K) x = (MvPolynomial.eval fun (i : Fin (Module.finrank K L)) ↦ ((Module.Basis.repr (Module.finBasis K L) : L → Fin (Module.finrank K L) →₀ K) x : Fin (Module.finrank K L) → K) i : MvPolynomial (Fin (Module.finrank K L)) K → K) f := by
  intro K L _ _ _ _
  classical
  let b := Module.finBasis K L
  let P : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) (MvPolynomial (Fin (Module.finrank K L)) K) :=
    fun j k => ∑ i, X i * C (Algebra.leftMulMatrix b (b i) j k)
  have hP : ∀ j k, (P j k).IsHomogeneous 1 := by
    intro j k
    apply IsHomogeneous.sum
    intro i _
    simpa using (isHomogeneous_X K i).mul (isHomogeneous_C (Fin (Module.finrank K L)) (Algebra.leftMulMatrix b (b i) j k))
  refine ⟨P.det, ?_, ?_⟩
  · rw [Matrix.det_apply]
    apply IsHomogeneous.sum
    intro σ _
    have h := IsHomogeneous.prod (Finset.univ : Finset (Fin (Module.finrank K L))) (fun i => P (σ i) i) (fun _ => 1) (fun i _ => hP (σ i) i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]; exact h
    · rw [hs, Units.neg_smul, one_smul]; exact h.neg
  · intro x
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext j k
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    have e1 : Algebra.leftMulMatrix b x = ∑ i, b.repr x i • Algebra.leftMulMatrix b (b i) := by
      conv_lhs => rw [hx]

      rw [map_sum]
      simp only [map_smul]
    rw [e1, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply]

    simp only [P, map_sum, eval_mul, eval_X, eval_C, Matrix.smul_apply, smul_eq_mul]
    rfl
end IdealPowerMembership
end GlobalTheory
end

section

noncomputable section

open scoped Matrix

namespace GlobalTheory.Sl2Ad

variable {K : Type*} [Field K]

def coord (X : Matrix (Fin 2) (Fin 2) K) : Fin 3 → K := ![X 0 1, X 1 0, X 0 0]

def ofCoord (v : Fin 3 → K) : Matrix (Fin 2) (Fin 2) K := !![v 2, v 0; v 1, -v 2]

def ad (A : GL (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => coord ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) i

def form : LinearMap.BilinForm K (Fin 3 → K) := Matrix.toBilin' !![0, 1, 0; 1, 0, 0; 0, 0, 2]

theorem trace_ofCoord (v : Fin 3 → K) : (ofCoord v).trace = 0 := by
  simp [ofCoord, Matrix.trace_fin_two]

theorem ofCoord_coord {X : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) : ofCoord (coord X) = X := by
  rw [Matrix.trace_fin_two] at hX
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofCoord, coord] <;> linear_combination -hX

theorem coord_ofCoord (v : Fin 3 → K) : coord (ofCoord v) = v := by
  ext i; fin_cases i <;> simp [ofCoord, coord]

theorem coord_add (X Y : Matrix (Fin 2) (Fin 2) K) : coord (X + Y) = coord X + coord Y := by
  ext i; fin_cases i <;> simp [coord]

theorem coord_smul (c : K) (X : Matrix (Fin 2) (Fin 2) K) : coord (c • X) = c • coord X := by
  ext i; fin_cases i <;> simp [coord]

theorem ofCoord_eq_sum (v : Fin 3 → K) : ofCoord v = ∑ j, v j • ofCoord (Pi.single j 1) := by
  ext i k; fin_cases i <;> fin_cases k <;> simp [ofCoord, Fin.sum_univ_three]

theorem coord_conj_ofCoord (A : GL (Fin 2) K) (v : Fin 3 → K) :
    coord ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord v * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = ad A *ᵥ v := by
  conv_lhs => rw [ofCoord_eq_sum]
  ext i
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mulVec, dotProduct, ad, Matrix.of_apply]
  rw [show ∀ (s : Finset (Fin 3)) (f : Fin 3 → Matrix (Fin 2) (Fin 2) K), coord (∑ j ∈ s, f j) i = ∑ j ∈ s, coord (f j) i from by
    intro s f; induction s using Finset.induction_on with
    | empty => simp [coord]; fin_cases i <;> rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coord_add, Pi.add_apply, ih]]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coord_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem trace_conj (A : GL (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((A : Matrix (Fin 2) (Fin 2) K) * X * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem coord_conj (A : GL (Fin 2) K) {X : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) :
    coord ((A : Matrix (Fin 2) (Fin 2) K) * X * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = ad A *ᵥ coord X := by
  conv_lhs => rw [← ofCoord_coord hX]
  exact coord_conj_ofCoord A _

theorem ad_mul (A B : GL (Fin 2) K) : ad (A * B) = ad A * ad B := by
  ext i j
  have h1 := coord_conj_ofCoord (A * B) (Pi.single j 1)
  have h2 := coord_conj_ofCoord B (Pi.single j 1)
  have h3 := coord_conj A (X := (B : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (by rw [trace_conj, trace_ofCoord])
  rw [h2] at h3
  have : ((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * (((A * B)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (A : Matrix (Fin 2) (Fin 2) K) * ((B : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    simp only [mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  rw [this, h3, Matrix.mulVec_mulVec] at h1
  have := congrFun h1 i
  simpa [Matrix.mulVec_single, Matrix.mul_apply] using this.symm

theorem ad_one : ad (1 : GL (Fin 2) K) = 1 := by
  ext i j
  simp only [ad, Matrix.of_apply, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one, coord_ofCoord]
  fin_cases i <;> fin_cases j <;> rfl

def adHom : GL (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun := ad
  map_one' := ad_one
  map_mul' := ad_mul

theorem form_apply (v w : Fin 3 → K) : form v w = v 0 * w 1 + v 1 * w 0 + 2 * (v 2 * w 2) := by
  simp [form, Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem form_coord {X Y : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) (hY : Y.trace = 0) :
    form (coord X) (coord Y) = (X * Y).trace := by
  rw [Matrix.trace_fin_two] at hX hY
  rw [form_apply]
  simp [coord, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (X 0 0) * hY - (Y 1 1) * hX

end GlobalTheory.Sl2Ad

end
end

section

namespace GlobalTheory.ResidueSpanLift

open IsLocalRing

theorem mem_smul_top_of_entries {O : Type} [CommRing O] {a : ℕ} (I : Ideal O)
    (X : Matrix (Fin a) (Fin a) O) (h : ∀ i j, X i j ∈ I) :
    X ∈ I • (⊤ : Submodule O (Matrix (Fin a) (Fin a) O)) := by
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : O) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (h i j) Submodule.mem_top

theorem exists_lift {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O) (Y : Matrix (Fin a) (Fin a) (ResidueField O))
    (hY : Y ∈ Submodule.span (ResidueField O)
      (Set.range fun g : ι => (M g).map (residue O))) :
    ∃ Z ∈ Submodule.span O (Set.range M), Z.map (residue O) = Y := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨M g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by ext i j; simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Z, hZ, rfl⟩ := hx
    obtain ⟨W, hW, rfl⟩ := hy
    exact ⟨Z + W, Submodule.add_mem _ hZ hW, by ext i j; simp⟩
  | smul c x _ hx =>
    obtain ⟨Z, hZ, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := residue_surjective c
    refine ⟨d • Z, Submodule.smul_mem _ _ hZ, ?_⟩
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem span_eq_top_of_span_residue_eq_top {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O)
    (h : Submodule.span (ResidueField O)
      (Set.range fun g : ι => (M g).map (residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by
  refine top_le_iff.mp ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O)
    Module.Finite.fg_top (maximalIdeal_le_jacobson _) ?_
  intro X _
  obtain ⟨Z, hZ, hZX⟩ := exists_lift M (X.map (residue O)) (h ▸ Submodule.mem_top)
  have hX : X = Z + (X - Z) := by abel
  rw [hX]
  refine Submodule.add_mem_sup hZ (mem_smul_top_of_entries _ _ fun i j => ?_)
  have := congrFun (congrFun hZX i) j
  simp only [Matrix.map_apply] at this
  rw [← residue_eq_zero_iff, Matrix.sub_apply, map_sub, this, sub_self]

end GlobalTheory.ResidueSpanLift
end

section

open Complex Filter Topology

namespace GlobalTheory

theorem lseriesSummable_twist_pow_of_sq_summable :
    ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  intro e ψ g s he hs hψ hg
  have h1 := hg s hs
  have h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + s) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded (h1.add h2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hx : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    simp only [Complex.ofReal_re, norm_mul, norm_pow, Complex.norm_natCast, Nat.add_sub_cancel]
    set x : ℝ := (n : ℝ) with hxdef
    set A : ℝ := ‖g n‖ with hA
    have hA0 : 0 ≤ A := norm_nonneg _
    set p : ℝ := x ^ (-(2 * (k : ℝ) + 3 + s) / 2) with hp
    set q : ℝ := x ^ (-(1 + s) / 2) with hq
    have hp0 : 0 ≤ p := by positivity
    have hq0 : 0 ≤ q := by positivity
    have e1 : A ^ 2 / x ^ (((2 * (k + 1) + 1 : ℕ) : ℝ) + s) = (A * p) ^ 2 := by
      rw [mul_pow, hp, ← Real.rpow_natCast (x ^ _) 2, ← Real.rpow_mul hx.le, div_eq_mul_inv,
        ← Real.rpow_neg hx.le]
      congr 2
      push_cast
      ring
    have e2 : 1 / x ^ (1 + s) = q ^ 2 := by
      rw [hq, ← Real.rpow_natCast (x ^ _) 2, ← Real.rpow_mul hx.le, one_div,
        ← Real.rpow_neg hx.le]
      congr 1
      push_cast
      ring
    have e3 : x ^ k / x ^ (2 * ((k + 1 : ℕ) : ℝ) + s) = p * q := by
      rw [hp, hq, ← Real.rpow_natCast x k, ← Real.rpow_sub hx, ← Real.rpow_add hx]
      congr 1
      push_cast
      ring
    rw [e1, e2]
    have e4 : ‖ψ n‖ * x ^ k * A / x ^ (2 * ((k + 1 : ℕ) : ℝ) + s) = ‖ψ n‖ * (A * p * q) := by
      rw [mul_assoc A, ← e3]; ring
    rw [e4]
    have h3 : ‖ψ n‖ * (A * p * q) ≤ A * p * q :=
      mul_le_of_le_one_left (by positivity) (hψ n)
    have h4 : 0 ≤ A * p * q := by positivity
    nlinarith [sq_nonneg (A * p - q)]

end GlobalTheory
end

section

open Complex Filter Topology

namespace GlobalTheory

theorem lseriesSquares_term (e : ℕ) (c : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) (d : ℕ) :
    LSeries.term (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then
        c (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) (d * d)
      = LSeries.term c ((e + 1 : ℕ) + 2 * s) d := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [LSeries.term_of_ne_zero (mul_ne_zero hd hd), LSeries.term_of_ne_zero hd]
  simp only [Nat.sqrt_eq, if_true]
  rw [Nat.cast_mul, natCast_mul_natCast_cpow, ← cpow_add _ _ hd', ← cpow_natCast, mul_div_assoc,
    ← cpow_sub _ _ hd', div_eq_mul_inv, ← cpow_neg]
  congr 2
  have h3 : 1 ≤ 3 * e := by omega
  push_cast [Nat.cast_sub h3]
  ring

theorem lseriesSquares_eq : ∀ (e : ℕ) (χ ψ θ : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → LSeriesSummable (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) ∧ LSeries (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
  intro e χ ψ θ s he hs hb
  have hinj : Function.Injective (fun d : ℕ => d * d) := fun a b h => Nat.mul_self_inj.mp h
  have hterm := lseriesSquares_term e (fun n => χ n * ψ n * θ n) s he
  set f : ℕ → ℂ := fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then
    χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0 with hf
  have hzero : ∀ n, n ∉ Set.range (fun d : ℕ => d * d) →
      LSeries.term f (((2 * (e : ℝ) + s : ℝ)) : ℂ) n = 0 := by
    intro n hn
    have hn' : ¬ (Nat.sqrt n * Nat.sqrt n = n) := fun h => hn ⟨_, h⟩
    rw [LSeries.term_def]
    split_ifs
    · rfl
    · simp [hf, hn']
  have hsum : LSeriesSummable (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) ?_
    · obtain ⟨h1, h2, h3⟩ := hb n
      rw [norm_mul, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ h1 (norm_nonneg _) h2) (norm_nonneg _) h3
    · have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      simp
      linarith
  constructor
  · refine (hinj.summable_iff hzero).mp ?_
    exact (show Summable _ from hsum).congr fun d => (hterm d).symm
  · unfold LSeries
    rw [← hinj.tsum_eq (fun n hn => by
      by_contra h
      exact hn (hzero n h))]
    exact tsum_congr hterm

end GlobalTheory
end

section

open Complex Filter Topology

namespace GlobalTheory

theorem lSeriesSummable_bounded_mul_of_summable_normSq :
    ∀ (e : ℕ) (θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖θ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => θ n * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  intro e θ g s he hs hθ hg
  have h1 := hg s hs
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ ((2 * (e : ℝ) + s) - 1) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) ?_
  intro n
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have e1 : (((2 * e + 1 : ℕ) : ℝ) + s) = (2 * (e : ℝ) + s) + 1 := by push_cast; ring
    rw [Complex.ofReal_re, e1, Real.rpow_add_one hn'.ne', Real.rpow_sub_one hn'.ne']
    have hN : (0 : ℝ) < (n : ℝ) ^ (2 * (e : ℝ) + s) := Real.rpow_pos_of_pos hn' _
    generalize (n : ℝ) ^ (2 * (e : ℝ) + s) = N at hN ⊢
    have hb : ‖θ n * g n‖ ≤ ‖g n‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hθ n)
    calc ‖θ n * g n‖ / N ≤ ‖g n‖ / N := by gcongr
      _ ≤ (‖g n‖ ^ 2 / (N * n) + 1 / (N / n)) / 2 := by
        have : (‖g n‖ ^ 2 / (N * n) + 1 / (N / n)) / 2 - ‖g n‖ / N
            = (‖g n‖ - n) ^ 2 / (2 * N * n) := by field_simp; ring
        have h3 : 0 ≤ (‖g n‖ - n) ^ 2 / (2 * N * n) := by positivity
        linarith

end GlobalTheory
end

section

namespace GlobalTheory

theorem jacobiSym_neg_eq_of_three_mod_four (q n : ℕ) (hq : q % 4 = 3) (hn : Odd n) :
    jacobiSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q := by
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [jacobiSym.neg _ hn]
  have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h hqo]
  · rw [ZMod.χ₄_nat_three_mod_four h,
      jacobiSym.quadratic_reciprocity_three_mod_four hq h]
    ring

end GlobalTheory
end
