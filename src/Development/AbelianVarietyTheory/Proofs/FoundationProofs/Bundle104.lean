module

public import Formalism.FormalDegreeBessel.Bundle001
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle078
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle081
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
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
public import Mathlib.RingTheory.ZMod.UnitsCyclic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Mathlib.Data.Nat.Totient
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory

namespace BigCellUnitary

def pos (k r : ℕ) : (Fin r ⊕ Fin r) ⊕ Fin (k + 1) → Fin (2 * r + k + 1) :=
  Sum.elim (Sum.elim (eI k r) (esI k r)) (wI k r)

theorem pos_bijective (k r : ℕ) : Function.Bijective (pos k r) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp; omega⟩
  rintro ((a | a) | a) ((b | b) | b) h <;>
    simp only [pos, eI, esI, wI, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    first
      | (exfalso; omega)
      | (have : a = b := Fin.ext (by omega); rw [this])

def posEquiv (k r : ℕ) : (Fin r ⊕ Fin r) ⊕ Fin (k + 1) ≃ Fin (2 * r + k + 1) :=
  Equiv.ofBijective _ (pos_bijective k r)

theorem gram_submatrix (k r : ℕ) :
    (Hpk k r).submatrix (pos k r) (pos k r) =
      fromBlocks (fromBlocks 0 1 1 0) 0 0 (Hb k) := by
  ext ((a | a) | a) ((b | b) | b) <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    simp only [pos, eI, esI, wI, Hpk, Hb, Sum.elim_inl, Sum.elim_inr, submatrix_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.one_apply, diagonal_apply, Fin.ext_iff, Fin.val_last] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | contradiction | (exfalso; simp_all; done) |
      (rename_i h1 h2
       first
        | exact (if_pos h2).trans (by rw [if_pos (by omega), if_pos (by omega)])
        | exact (if_neg h2).trans (by rw [if_pos (by omega), if_neg (by omega)]))

theorem col_e (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (b : Fin r) :
    bigCell k r c μ i (eI k r b) = if i.val = 2 * r + k - b.val then c b else 0 := by
  have hb : (eI k r b).val < r := b.isLt
  unfold bigCell
  rw [dite_eq_left hb]
  exact if_congr Fin.ext_iff rfl rfl

theorem col_w (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (b : Fin (k + 1)) :
    bigCell k r c μ i (wI k r b) =
      if hi : r ≤ i.val ∧ i.val ≤ r + k then μ ⟨i.val - r, by omega⟩ b else 0 := by
  have hb := b.isLt
  have hv : (wI k r b).val = r + b.val := rfl
  unfold bigCell
  rw [dif_neg (by omega), dite_eq_left (by omega)]
  split_ifs
  · congr 1
    apply Fin.ext
    show (wI k r b).val - r = b.val
    omega
  · rfl

theorem col_es (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (b : Fin r) :
    bigCell k r c μ i (esI k r b) = if i.val = b.val then (star (c b))⁻¹ else 0 := by
  have hb := b.isLt
  have hv : (esI k r b).val = 2 * r + k - b.val := rfl
  unfold bigCell
  rw [dif_neg (by omega), dif_neg (by omega)]
  refine if_congr (by omega) ?_ rfl
  congr 3
  apply Fin.ext
  show 2 * r + k - (esI k r b).val = b.val
  omega

theorem bigCell_submatrix (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (bigCell k r c μ).submatrix (pos k r) (pos k r) =
      fromBlocks (fromBlocks 0 (diagonal fun a => (star (c a))⁻¹) (diagonal c) 0) 0 0 μ := by
  ext ((a | a) | a) ((b | b) | b) <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    simp only [pos, Sum.elim_inl, Sum.elim_inr, submatrix_apply, col_e, col_w, col_es,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, diagonal_apply]
  · exact if_neg (by show ¬ a.val = _; omega)
  · have : ((eI k r a).val = b.val) ↔ a = b := (Fin.ext_iff (a := a) (b := b)).symm
    exact (if_congr this rfl rfl).trans (by split_ifs with h <;> simp [h])
  · exact dif_neg (by show ¬ (r ≤ a.val ∧ _); omega)
  · have : ((esI k r a).val = 2 * r + k - b.val) ↔ a = b := by
      rw [Fin.ext_iff]; show 2 * r + k - a.val = _ ↔ _; omega
    exact (if_congr this rfl rfl).trans (by split_ifs with h <;> simp [h])
  · exact if_neg (by show ¬ 2 * r + k - a.val = _; omega)
  · exact dif_neg (by show ¬ (_ ∧ 2 * r + k - a.val ≤ _); omega)
  · exact if_neg (by show ¬ r + a.val = _; omega)
  · exact if_neg (by show ¬ r + a.val = _; omega)
  · rw [dite_eq_left (by show r ≤ r + a.val ∧ r + a.val ≤ _; omega)]
    congr 1
    apply Fin.ext
    show r + a.val - r = a.val
    omega

end BigCellUnitary


open BigCellUnitary in
theorem bigCell_mem_unitary : Formalism.QuantumDeterminants.BigCellMem := by
  intro k r c μ hc hμ
  change (bigCell k r c μ)ᴴ * Hpk k r * bigCell k r c μ = Hpk k r
  let e := BigCellUnitary.posEquiv k r
  have key : ((bigCell k r c μ)ᴴ * Hpk k r * bigCell k r c μ).submatrix e e =
      (Hpk k r).submatrix e e := by
    rw [← submatrix_mul_equiv _ _ _ e, ← submatrix_mul_equiv _ _ _ e,
      ← conjTranspose_submatrix]
    have hp : ⇑e = BigCellUnitary.pos k r := rfl
    rw [hp, BigCellUnitary.gram_submatrix, BigCellUnitary.bigCell_submatrix]
    have h1 : diagonal (fun a => star (c a)) * diagonal (fun a => (star (c a))⁻¹) =
        (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext a
      exact mul_inv_cancel₀ (star_ne_zero.2 (hc a))
    have h2 : diagonal (fun a => star (star (c a))⁻¹) * diagonal c =
        (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext a
      rw [star_inv₀, star_star]
      exact inv_mul_cancel₀ (hc a)
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_zero, diagonal_conjTranspose,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add, hμ]
    rw [show star c = fun a => star (c a) from rfl,
      show star (fun a => (star (c a))⁻¹) = fun a => star (star (c a))⁻¹ from rfl, h1, h2]
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  exact congrFun (congrFun key i) j

end GlobalTheory
end
end

section

open Formalism.BasicNotions MeasureTheory Filter Topology

namespace GlobalTheory

theorem compactSpace_UpqT_zero_right : ∀ N : ℕ, CompactSpace (UpqT N 0) :=
  fun N => (GlobalTheory.compactSpace_UpqT_definite N).1

end GlobalTheory
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_fractionField_extension_of_maps : ∀ (Ω R L M : Type) [Field Ω] [CommRing R] [IsDomain R] [Field L] [Algebra Ω L] [CommRing M] (G S : Type) (c : Ω →+* R) (e : R →+* L) (sl : G → R ≃+* R) (ga : S → R ≃+* R) (A : R →+* M), Function.Injective e → (∀ x, e (c x) = algebraMap Ω L x) → (∀ g x, sl g (c x) = c x) → (∀ a, a ≠ 0 → IsUnit (A a)) → ∃ (K : Type) (_ : Field K) (_ : Algebra Ω K) (io : R →+* K) (e' : K →ₐ[Ω] L) (sl' : G → K ≃ₐ[Ω] K) (ga' : S → K ≃+* K) (A' : K →+* M), Function.Injective io ∧ (∀ f : K, ∃ a b : R, b ≠ 0 ∧ f * io b = io a) ∧ (∀ x, io (c x) = algebraMap Ω K x) ∧ (∀ a, e' (io a) = e a) ∧ (∀ g a, sl' g (io a) = io (sl g a)) ∧ (∀ s a, ga' s (io a) = io (ga s a)) ∧ ∀ a, A' (io a) = A a := by
  first | exact @GlobalTheory.fraction_field_extension | exact GlobalTheory.fraction_field_extension | (intros; apply GlobalTheory.fraction_field_extension <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.isAlgebraic_of_finite_complex_automorphism_orbit : ∀ (E : Subfield ℂ) (x : ℂ), (Set.range fun g : ℂ ≃ₐ[E] ℂ => g x).Finite → IsAlgebraic E x := by
  first | exact @GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit | exact GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit | (intros; apply GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_improved_approx_kummer_generator : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (F : Subfield L) (θ : ℝ≥0), θ ≤ 1 → v (p : L) ≤ 1 → (∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → ∀ α y : L, α ^ p ∈ F → y ∈ F → v (α - y) ≤ v α → ∃ y' ∈ F, v (α - y') ^ p ≤ max (v (p : L) * v (α - y) * v α ^ (p - 1)) (max θ (v (p : L)) * v (α - y) ^ p) := by
  first | exact @GlobalTheory.AlmostEt.exists_approxRoot_step | exact GlobalTheory.AlmostEt.exists_approxRoot_step | (intros; apply GlobalTheory.AlmostEt.exists_approxRoot_step <;> assumption)
end

section

open GlobalTheory.Col PowerSeries

namespace GlobalTheory

theorem sum_units_primePow_teichmuller_reindex :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (m : ℕ) (A : Type) [AddCommMonoid A] (f : ZMod (p ^ (m + 1)) → A),
      ∑ b : (ZMod (p ^ (m + 1)))ˣ, f (b : ZMod (p ^ (m + 1))) =
        ∑ c : (ZMod p)ˣ, ∑ l ∈ Finset.range (p ^ m),
          f ((((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l : ℕ)) : ZMod (p ^ (m + 1))) := by
  intro p hp hp2 m A _ f
  have hpp : p.Prime := hp.out
  haveI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hcop : ∀ (c : (ZMod p)ˣ) (l : ℕ),
      Nat.Coprime ((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l) (p ^ (m + 1)) := by
    intro c l
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.mul_left
    · apply Nat.Coprime.pow_left
      rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
      intro h
      have h0 : (((c : ZMod p).val : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [ZMod.natCast_zmod_val] at h0
      exact c.ne_zero h0
    · apply Nat.Coprime.pow_left
      rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
      intro h
      have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).1 (by rwa [add_comm] at h)
      exact hpp.one_lt.ne' (Nat.dvd_one.1 h1)
  let g : (ZMod p)ˣ × Fin (p ^ m) → (ZMod (p ^ (m + 1)))ˣ :=
    fun x => ZMod.unitOfCoprime _ (hcop x.1 x.2)
  have hg : ∀ x, (g x : ZMod (p ^ (m + 1))) =
      (((x.1 : ZMod p).val ^ (p ^ m) * (1 + p) ^ (x.2 : ℕ) : ℕ) : ZMod (p ^ (m + 1))) := fun x => rfl
  have hinj : Function.Injective g := by
    rintro ⟨c, l⟩ ⟨c', l'⟩ h
    have h' := congrArg (fun u : (ZMod (p ^ (m + 1)))ˣ => (u : ZMod (p ^ (m + 1)))) h
    simp only [hg] at h'
    have hc : c = c' := by
      have h2 := congrArg (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero m)) (ZMod p)) h'
      simp only [map_natCast] at h2
      push_cast at h2
      simp only [ZMod.natCast_val, ZMod.cast_id', id, ZMod.natCast_self, add_zero, one_pow, mul_one,
        ZMod.pow_card_pow] at h2
      exact Units.ext h2
    subst hc
    have hu : IsUnit ((((c : ZMod p).val ^ (p ^ m) : ℕ) : ZMod (p ^ (m + 1)))) :=
      (ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) (hcop c 0))
    have h3 : ((1 + p : ZMod (p ^ (m + 1)))) ^ (l : ℕ) = (1 + p) ^ (l' : ℕ) := by
      rw [Nat.cast_mul, Nat.cast_mul] at h'
      have h4 := hu.mul_left_cancel h'
      push_cast at h4
      exact h4
    have hu1 : IsUnit ((1 + p : ℕ) : ZMod (p ^ (m + 1))) := by
      refine (ZMod.isUnit_iff_coprime _ _).2 ?_
      have h5 := Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) (hcop c 1)
      rwa [pow_one] at h5
    obtain ⟨u, hu⟩ := hu1
    push_cast at hu
    have h6 : u ^ (l : ℕ) = u ^ (l' : ℕ) := Units.ext (by push_cast [hu]; exact h3)
    rw [pow_inj_mod, ← orderOf_units, hu, ZMod.orderOf_one_add_prime hpp hp2, Nat.mod_eq_of_lt l.2,
      Nat.mod_eq_of_lt l'.2] at h6
    exact Prod.ext rfl (Fin.ext h6)
  have hcard : Fintype.card ((ZMod p)ˣ × Fin (p ^ m)) = Fintype.card (ZMod (p ^ (m + 1)))ˣ := by
    rw [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, Fintype.card_fin,
      Nat.totient_prime_pow_succ hpp, Nat.totient_prime hpp]
    ring
  have hbij : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, hcard⟩
  rw [← Fintype.sum_bijective g hbij (fun x => f (g x : ZMod (p ^ (m + 1)))) (fun b => f b)
    (fun _ => rfl), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact Fin.sum_univ_eq_sum_range
    (fun l => f ((((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l : ℕ)) : ZMod (p ^ (m + 1)))) (p ^ m)

end GlobalTheory
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (s : Ω →+* Ω') (l : ℚ) (χ : ℚ → Ω'), 0 < l → χ 0 = 1 → (∀ r r', χ (r + r') = χ r * χ r') → ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω', ∀ h r, (Φ h).coeff (r * l) = χ r * s (h.coeff r) := by
  first | exact @GlobalTheory.FNTwist.exists_scale_twist_ringHom | exact GlobalTheory.FNTwist.exists_scale_twist_ringHom | (intros; apply GlobalTheory.FNTwist.exists_scale_twist_ringHom <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hahnSeries_subring_coeff_mul_inv_mem : ∀ (Ω : Type) [Field Ω] (A : Subring Ω), (∀ h h' : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → (∀ r, h'.coeff r ∈ A) → ∀ r, (h * h').coeff r ∈ A) ∧ ∀ h : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → h.leadingCoeff⁻¹ ∈ A → ∀ r, (h⁻¹).coeff r ∈ A := by
  first | exact @GlobalTheory.HahnSub.coeff_mul_inv_mem | exact GlobalTheory.HahnSub.coeff_mul_inv_mem | (intros; apply GlobalTheory.HahnSub.coeff_mul_inv_mem <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.upperHalfPlane_eq_zero_of_vanish_above_im : ∀ (f : ℍ → ℂ) (C : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, C < τ.im → f τ = 0) → f = 0 := by
  first | exact @GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high | exact GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high | (intros; apply GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff : ∀ f g : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g → (∀ τ, f τ * g τ = 0) → f = 0 ∨ g = 0 := by
  first | exact @GlobalTheory.fn_mul_eq_zero_dom | exact GlobalTheory.fn_mul_eq_zero_dom | (intros; apply GlobalTheory.fn_mul_eq_zero_dom <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.norm_root_le_one_add_sum_norm_coeff : ∀ (n : ℕ) (s : Fin n → ℂ) (y : ℂ), y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0 → ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  first | exact @GlobalTheory.monic_root_norm_le_one_add_sum | exact GlobalTheory.monic_root_norm_le_one_add_sum | (intros; apply GlobalTheory.monic_root_norm_le_one_add_sum <;> assumption)
end

section


theorem _root_.GlobalTheory.T.line_functional_eq_period_mul_alt : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M)
  (g : S → Module.End ℤ_[l] M) (ρ : S → Matrix (Fin 2) (Fin 2) (PadicAlgCl l))
  (L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l]) (F : Finset (PadicAlgCl l)),
  (∀ K : IntermediateField ℚ_[l] (PadicAlgCl l), (∀ a ∈ F, a ∈ K) → ∀ τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l,
    ∃ s, ∀ b ∈ B, L (1 ⊗ₜ[ℤ_[l]] g s b) = τ • L (1 ⊗ₜ[ℤ_[l]] b)) →
  ∀ (m : ℕ) (σ : Fin m → (Fin 2 → PadicAlgCl l) →ₗ[PadicAlgCl l] TensorProduct ℤ_[l] (PadicAlgCl l) M),
  (∀ i v, σ i v ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype)) →
  (∀ i s v, LinearMap.baseChange (PadicAlgCl l) (g s) (σ i v) = σ i (Matrix.mulVec (ρ s) v)) →
  (∀ i, L (σ i ![1, 0]) = 0) →
  ∃ (κ : Fin m → PadicAlgCl l) (per : ℂ_[l]), ‖per‖ = 1 ∧ ∀ i v, L (σ i v) = per * ((κ i * v 1 : PadicAlgCl l) : ℂ_[l]) := by
  first | exact @GlobalTheory.line_functional_eq_period_mul | exact GlobalTheory.line_functional_eq_period_mul | (intros; apply GlobalTheory.line_functional_eq_period_mul <;> assumption)
end
