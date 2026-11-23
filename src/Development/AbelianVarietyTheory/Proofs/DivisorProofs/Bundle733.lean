module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle696
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.SzRules

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem norm_natCast_eq (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  have h : (n : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (n : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_le_one_of_isIntegral {y : ℂ_[l]} (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral ..)

theorem mem_of_natCast_mul {n : ℕ} (hn : n ≠ 0) {x : ℂ} (h : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ) :
    x ∈ algebraicClosure ℚ ℂ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have := div_mem h (natCast_mem (algebraicClosure ℚ ℂ) n)
  rwa [mul_div_cancel_left₀ _ hn'] at this

theorem norm_natCast_mul (n : ℕ) {x : ℂ} (hx : x ∈ algebraicClosure ℚ ℂ) (h : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ) :
    ‖lam ⟨(n : ℂ) * x, h⟩‖ = ‖(n : ℚ_[l])‖ * ‖lam ⟨x, hx⟩‖ := by
  have : (⟨(n : ℂ) * x, h⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) * ⟨x, hx⟩ := rfl
  rw [this, map_mul, map_natCast, norm_mul, norm_natCast_eq]

theorem sz_of_isIntegral (n : ℕ) (x : ℂ) (hn : ¬ l ∣ n) (h : IsIntegral ℤ ((n : ℂ) * x)) : Sz l lam 0 x := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hm : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff'.2 h.tower_top
  have hx := mem_of_natCast_mul hn0 hm
  refine ⟨hx, ?_⟩
  have h1 : IsIntegral ℤ (⟨(n : ℂ) * x, hm⟩ : algebraicClosure ℚ ℂ) :=
    (isIntegral_algHom_iff (algebraicClosure ℚ ℂ).val.toRingHom.toIntAlgHom Subtype.val_injective).1 h
  have h2 : ‖lam ⟨(n : ℂ) * x, hm⟩‖ ≤ 1 :=
    norm_le_one_of_isIntegral (by convert map_isIntegral_int lam h1; exact Subsingleton.elim _ _)
  have h3 : ‖(n : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hn
  have h4 := norm_natCast_mul (lam := lam) n hx hm
  rw [h3, one_mul] at h4
  rw [Real.rpow_zero, ← h4]
  exact h2

theorem sz_add {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x + y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨add_mem hx hy, ?_⟩
  have : (⟨x + y, add_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hy')

theorem sz_mul {r₁ r₂ : ℝ} {x y : ℂ} (hx : Sz l lam r₁ x) (hy : Sz l lam r₂ y) :
    Sz l lam (r₁ + r₂) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r r' : ℝ} {x : ℂ} (h : r ≤ r') (hx : Sz l lam r x) : Sz l lam r' x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

theorem sz_prime_mul (r : ℝ) (x : ℂ) : Sz l lam r ((l : ℂ) * x) ↔ Sz l lam (r + 1) x := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  constructor
  · rintro ⟨h, h'⟩
    have hx := mem_of_natCast_mul hl.out.ne_zero h
    refine ⟨hx, ?_⟩
    rw [norm_natCast_mul l hx h, Padic.norm_p, inv_mul_le_iff₀ hl0] at h'
    rw [Real.rpow_add_one hl0.ne', mul_comm]
    exact h'
  · rintro ⟨hx, h'⟩
    have h : (l : ℂ) * x ∈ algebraicClosure ℚ ℂ := mul_mem (natCast_mem _ l) hx
    refine ⟨h, ?_⟩
    rw [norm_natCast_mul l hx h, Padic.norm_p, inv_mul_le_iff₀ hl0]
    rw [Real.rpow_add_one hl0.ne', mul_comm] at h'
    exact h'

theorem sz_of_sq {r : ℝ} {x : ℂ} (h : Sz l lam r (x ^ 2)) : Sz l lam (r / 2) x := by
  obtain ⟨h, h'⟩ := h
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hx : x ∈ algebraicClosure ℚ ℂ :=
    mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by norm_num : 0 < 2) (mem_algebraicClosure_iff.1 h))
  refine ⟨hx, ?_⟩
  have : (⟨x ^ 2, h⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ ^ 2 := rfl
  rw [this, map_pow, norm_pow] at h'
  have e : (l : ℝ) ^ r = ((l : ℝ) ^ (r / 2)) ^ 2 := by
    rw [sq, ← Real.rpow_add hl0]; congr 1; ring
  rw [e] at h'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ (n : ℕ) (x : ℂ), ¬ l ∣ n → IsIntegral ℤ ((n : ℂ) * x) → Sz l lam 0 x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y)) ∧ (∀ (r r' : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r' y → Sz l lam (r + r') (x * y)) ∧ (∀ (r r' : ℝ) (x : ℂ), r ≤ r' → Sz l lam r x → Sz l lam r' x) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r x → Sz l lam r (-x)) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r ((l : ℂ) * x) ↔ Sz l lam (r + 1) x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r (x ^ 2) → y = x → Sz l lam (r / 2) y) :=
  fun _ _ _ => ⟨sz_of_isIntegral, fun _ _ _ => sz_add, fun _ _ _ _ => sz_mul, fun _ _ _ => sz_mono, fun _ _ => sz_neg,
    sz_prime_mul, fun _ _ _ h e => e ▸ sz_of_sq h⟩

end GlobalTheory.SzRules
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockSwap

variable {p q r s : ℕ}

theorem linePos_swap (l : Ln p q r s) : linePos (l.swap : Ln r s p q) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> rfl

theorem rename_lowB (l : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (lowB l P) = lowB (l.swap : Ln r s p q) (rename Prod.swap P) := by
  unfold lowB
  rw [linePos_swap]
  split_ifs
  · exact (pderiv_rename Prod.swap_injective l P).symm
  · simp

theorem rename_raiB (l : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (raiB l P) = raiB (l.swap : Ln r s p q) (rename Prod.swap P) := by
  unfold raiB
  rw [linePos_swap]
  split_ifs
  · simp
  · simp only [LinearMap.neg_apply, map_neg, neg_inj]
    exact (pderiv_rename Prod.swap_injective l P).symm

theorem rename_omE (l l' : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (omE l l' P) =
      omE (l.swap : Ln r s p q) l'.swap (rename Prod.swap P) := by
  unfold omE
  simp only [LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, rename_raiB, rename_lowB,
    Prod.swap_inj]
  congr 1
  split_ifs <;> simp

theorem rename_omAct (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    rename Prod.swap (omAct p q r s M P) =
      omAct r s p q (M.submatrix Prod.swap Prod.swap) (rename Prod.swap P) := by

  simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
  rename_omE]
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l' => ?_
  simp

theorem rename_fockAct1 (Z : Mat p q) (P : Pol p q r s) :
    rename Prod.swap (fockAct1 p q r s Z P) = fockAct2 r s p q Z (rename Prod.swap P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct]
  congr 2
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, mul_comm]

theorem rename_fockAct2 (Z : Mat r s) (P : Pol p q r s) :
    rename Prod.swap (fockAct2 p q r s Z P) = fockAct1 r s p q Z (rename Prod.swap P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct]
  congr 2
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, mul_comm]

theorem rename_minusPart {σ τ : Type} (e : σ ≃ τ) (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (h : ∀ P, rename e (A P) = B (rename e P))
    (P : MvPolynomial σ ℂ) : rename e (minusPart A P) = minusPart B (rename e P) := by
  unfold minusPart
  have := (renameEquiv ℂ e).toAddEquiv.map_finsum
    (fun d : ℕ => homogeneousComponent d (A (homogeneousComponent (d + 2) P)))
  refine this.trans (finsum_congr fun d => ?_)
  show rename e _ = _
  rw [rename_homogeneousComponent, h, rename_homogeneousComponent]

theorem minusPart_eq_zero_iff {σ τ : Type} (e : σ ≃ τ) (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (h : ∀ P, rename e (A P) = B (rename e P))
    (P : MvPolynomial σ ℂ) : minusPart A P = 0 ↔ minusPart B (rename e P) = 0 := by
  rw [← rename_minusPart e A B h, map_eq_zero_iff _ (rename_injective _ e.injective)]

theorem swap_symmetry : ∀ (p q r s : ℕ), (∀ (Z : Mat p q) (P : Pol p q r s), rename Prod.swap (fockAct1 p q r s Z P) = fockAct2 r s p q Z (rename Prod.swap P)) ∧ (∀ (Z : Mat r s) (P : Pol p q r s), rename Prod.swap (fockAct2 p q r s Z P) = fockAct1 r s p q Z (rename Prod.swap P)) ∧ (∀ P : Pol p q r s, (P ∈ harm1 p q r s ↔ rename Prod.swap P ∈ harm2 r s p q) ∧ (P ∈ harm2 p q r s ↔ rename Prod.swap P ∈ harm1 r s p q)) := by
  intro p q r s
  refine ⟨rename_fockAct1, rename_fockAct2, fun P => ⟨?_, ?_⟩⟩
  · exact forall₂_congr fun Z _ =>
      minusPart_eq_zero_iff (Equiv.prodComm _ _) _ _ (rename_fockAct2 Z) P
  · exact forall₂_congr fun Z _ =>
      minusPart_eq_zero_iff (Equiv.prodComm _ _) _ _ (rename_fockAct1 Z) P

end GlobalTheory.FockSwap
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ]

instance : SemilatticeSup {I : Finset κ // I.Nonempty} :=
  Subtype.semilatticeSup fun _ _ hx _ => hx.mono Finset.subset_union_left

abbrev NE (κ : Type) [LinearOrder κ] : Type := ({I : Finset κ // I.Nonempty})ᵒᵈ

abbrev ne (s : Finset κ) (h : s.Nonempty) : (NE κ)ᵒᵖ := op (OrderDual.toDual ⟨s, h⟩)

abbrev sub (a : (NE κ)ᵒᵖ) : Finset κ := (OrderDual.ofDual a.unop).1

theorem sub_nonempty (a : (NE κ)ᵒᵖ) : (sub a).Nonempty := (OrderDual.ofDual a.unop).2

theorem sub_subset {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) : sub a ⊆ sub b := leOfHom f.unop

def homOf {a b : (NE κ)ᵒᵖ} (h : sub a ⊆ sub b) : a ⟶ b := (homOfLE (show b.unop ≤ a.unop from h)).op

def mn (a : (NE κ)ᵒᵖ) : κ := (sub a).min' (sub_nonempty a)

theorem mn_mem (a : (NE κ)ᵒᵖ) : mn a ∈ sub a := Finset.min'_mem _ _

theorem mn_le_of_hom {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) : mn b ≤ mn a :=
  Finset.min'_le _ _ (sub_subset f (mn_mem a))

theorem card_nonempty {p : ℕ} (s : {s : Finset κ // s.card = p + 1}) : s.1.Nonempty :=
  Finset.card_pos.1 (by rw [s.2]; omega)

theorem card_three {x y z : κ} (h₁ : x < y) (h₂ : y < z) : ({x, y, z} : Finset κ).card = 2 + 1 := by
  rw [Finset.card_insert_of_notMem (by simp [h₁.ne, (h₁.trans h₂).ne]), Finset.card_pair h₂.ne]

section Cech

variable {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

abbrev CC (p : ℕ) : Type := ∀ s : {s : Finset κ // s.card = p + 1}, F.obj (ne s.1 (card_nonempty s))

def δ (p : ℕ) : CC F p →ₗ[R] CC F (p + 1) :=
  LinearMap.pi fun t => ∑ i : t.1, GlobalTheory.cubeSign t.1 i.1 •
    ((mp F (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx t i))) (b := ne _ (card_nonempty t))
      (Finset.erase_subset i.1 t.1))).toLinearMap ∘ₗ LinearMap.proj (GlobalTheory.Cube.eraseIdx t i))

theorem δ_apply (p : ℕ) (x : CC F p) (t : {s : Finset κ // s.card = p + 1 + 1}) :
    δ F p x t = ∑ i : t.1, GlobalTheory.cubeSign t.1 i.1 •
      mp F (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx t i))) (b := ne _ (card_nonempty t))
        (Finset.erase_subset i.1 t.1)) (x (GlobalTheory.Cube.eraseIdx t i)) := by
  simp [δ, LinearMap.sum_apply]

def e0 : CC F 0 →ₗ[R] C0 F :=
  LinearMap.pi fun a => (mp F (homOf (a := ne {mn a} (Finset.singleton_nonempty _)) (b := a)
    (Finset.singleton_subset_iff.2 (mn_mem a)))).toLinearMap ∘ₗ
      LinearMap.proj (⟨{mn a}, Finset.card_singleton _⟩ : {s : Finset κ // s.card = 0 + 1})

theorem pair_subset {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) : ({mn b, mn a} : Finset κ) ⊆ sub b := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact mn_mem b
  · exact sub_subset f (mn_mem a)

theorem triple_subset {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    ({mn d, mn b, mn a} : Finset κ) ⊆ sub d := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact mn_mem d
  · exact sub_subset g (mn_mem b)
  · exact sub_subset g (sub_subset f (mn_mem a))

def e1 : CC F 1 →ₗ[R] C1 F :=
  LinearMap.pi fun a => LinearMap.pi fun b => LinearMap.pi fun f =>
    if h : mn b < mn a then
      -((mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b) (pair_subset f))).toLinearMap ∘ₗ
        LinearMap.proj (⟨{mn b, mn a}, Finset.card_pair h.ne⟩ : {s : Finset κ // s.card = 1 + 1}))
    else 0

def e2 : CC F 2 →ₗ[R] C2 F :=
  LinearMap.pi fun a => LinearMap.pi fun b => LinearMap.pi fun d => LinearMap.pi fun f =>
    LinearMap.pi fun g =>
    if h : mn d < mn b ∧ mn b < mn a then
      -((mp F (homOf (a := ne {mn d, mn b, mn a} (Finset.insert_nonempty _ _)) (b := d)
          (triple_subset f g))).toLinearMap ∘ₗ
        LinearMap.proj (⟨{mn d, mn b, mn a}, card_three h.1 h.2⟩ : {s : Finset κ // s.card = 2 + 1}))
    else 0

end Cech

section Scheme

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def cov (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) (I : NE κ) :
    X.affineOpens :=
  ⟨⨅ i ∈ (OrderDual.ofDual I).1, D i, hD _ (OrderDual.ofDual I).2⟩

theorem cov_mono (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    Monotone (cov D hD) := fun _ _ h => show (⨅ i ∈ _, D i) ≤ ⨅ i ∈ _, D i from biInf_mono fun _ hi => h hi

abbrev covF (s : X ⟶ Sp R) (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R :=
  (cov_mono D hD).functor.op ⋙ OAff s

def res0 (s : X ⟶ Sp R) (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    LinearMap.ker (d0 (OAff s)) →ₗ[R] LinearMap.ker (d0 (covF s D hD)) where
  toFun g := ⟨fun I => g.1 (op (cov D hD I.unop)), by
    funext I J f
    exact congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) _) _) ((cov_mono D hD).functor.map f.unop).op⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem triv_pull_U {X' : Scheme.{0}} (φ : X' ⟶ X) (j : ((LB.triv X).pull φ).ι) :
    ((LB.triv X).pull φ).U j = ⊤ := by
  ext x; simp [LB.pull, LB.LinComb, LB.wchart]

def i0 {X' : Scheme.{0}} (φ : X' ⟶ X) : ((LB.triv X).pull φ).ι := fun _ => PUnit.unit

def trivCoord {X' : Scheme.{0}} {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (V : X'.Opens) :
    GlobalTheory.AbLaw.SecOnR s' ((LB.triv X).pull φ) V →ₗ[R'] Sec s' V where
  toFun x := Sec.res s' (le_inf le_rfl (by rw [triv_pull_U]; exact le_top)) (GlobalTheory.AbLaw.SecOnR.coord x (i0 φ))
  map_add' x y := by simp [GlobalTheory.AbLaw.SecOnR.coord_add]; exact map_add _ _ _
  map_smul' r x := by
    have e : (show Sec s' _ from (r • x).coord (i0 φ)) = r • (show Sec s' _ from x.coord (i0 φ)) := by
      rw [GlobalTheory.AbLaw.SecOnR.coord_base_smul]; rfl
    exact (congrArg (Sec.res s' _) e).trans (map_smul _ _ _)

def Φ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
    {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) (D : κ → X.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) :
    R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p →ₗ[R'] CC (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p :=
  (LinearMap.pi fun t => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) ∘ₗ LinearMap.proj t) ∘ₗ
    GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (p + 1)

def one (s : X ⟶ Sp R) (D : κ → X.Opens) : (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X 0 :=
  fun t => GlobalTheory.AbLaw.SecOnR.of s _ _ ((GlobalTheory.AbLaw.secOnTrivEquiv _).symm 1)

def pr {X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i)
    (I : NE κ) : Pair ψ :=
  ⟨(cov D'' hD'' I, cov D' hD' I), show (⨅ i ∈ _, D'' i) ≤ ψ ⁻¹ᵁ (⨅ i ∈ _, D' i) by
    rw [GlobalTheory.AbLaw.preimage_biInf]; exact iInf₂_mono fun i _ => hle i⟩

def pullCoef {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}} {s' : X' ⟶ Sp R'}
    {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'} (w : ψ ≫ s' = s'' ≫ spMap σ) (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) :
    CoefMap σ (covF s' D' hD') (covF s'' D'' hD'') where
  G := 𝟭 _
  α I := (pairPull w).α (op (pr D' hD' D'' hD'' hle I.unop))
  naturality {I J} f b := by
    have := (pairPull w).naturality (homOfLE (show pr D' hD' D'' hD'' hle J.unop ≤ pr D' hD' D'' hD'' hle I.unop from
      Subtype.mk_le_mk.2 (Prod.mk_le_mk.2 ⟨(cov_mono D'' hD'') (leOfHom f.unop), (cov_mono D' hD') (leOfHom f.unop)⟩))).op b
    exact this
  smul I r b := (pairPull w).smul (op (pr D' hD' D'' hD'' hle I.unop)) r b

end Scheme

end GlobalTheory.CechPoset
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_torsor_model_filtered_colimit : ∀ (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Type) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j),
    (∀ i (h : i ≤ i), f i i h = RingHom.id (R i)) →
    (∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk)) →
    ∀ (B : Type) [CommRing B] (g : ∀ i, R i →+* B),
    (∀ i j (h : i ≤ j), (g j).comp (f i j h) = g i) →
    (∀ b : B, ∃ i x, g i x = b) →
    (∀ i x, g i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) →
    ∀ (q : ℕ), 0 < q →
    ∀ (D : Type) [CommRing D] [Algebra B D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ i, letI : Algebra (R i) B := (g i).toAlgebra
      ∃ (Di : Type) (_ : CommRing Di) (_ : Algebra (R i) Di)
        (acti : Multiplicative (ZMod q) →* (Di ≃ₐ[R i] Di)),
        GlobalTheory.KeyOriginCut.IsZTorsor (R i) Di q acti ∧ Nonempty (TensorProduct (R i) B Di ≃ₐ[B] D) := by
  first | (exact @GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements) | (exact GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements) | (intros; apply GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements  <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_sub_mem_maximalIdeal_etale_over_origin : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsSepClosed (ResidueField A)] (E : Type) [CommRing E] [Algebra (Polynomial A) E] [Algebra.Etale (Polynomial A) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A) E) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ y : Localization.AtPrime Q, ∃ a : Polynomial A, y - algebraMap (Polynomial A) (Localization.AtPrime Q) a ∈ maximalIdeal (Localization.AtPrime Q) := by
  first | (exact @GlobalTheory.OriginResidue.residue_origin) | (exact GlobalTheory.OriginResidue.residue_origin) | (intros; apply GlobalTheory.OriginResidue.residue_origin <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.origin_ideal_unique_prime_over : ∀ (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S] (f : A →+* S), f.IsIntegral →
    (Polynomial.mapRingHom f).IsIntegral ∧ (GlobalTheory.KeyOriginCut.originIdeal S).IsPrime ∧
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    ∀ 𝔔 : Ideal (Polynomial S), 𝔔.IsPrime → 𝔔.comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A → 𝔔 = GlobalTheory.KeyOriginCut.originIdeal S := by
  first | (exact @GlobalTheory.PolyOrigin.polyOrigin) | (exact GlobalTheory.PolyOrigin.polyOrigin) | (intros; apply GlobalTheory.PolyOrigin.polyOrigin  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw


theorem _root_.GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_surjective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Surjective ((etaS q).hom.app (op U)).hom := by
  first | (exact @GlobalTheory.EtC.MuTw.etaS_surjective) | (exact GlobalTheory.EtC.MuTw.etaS_surjective) | (intros; apply GlobalTheory.EtC.MuTw.etaS_surjective  <;> assumption)
end
