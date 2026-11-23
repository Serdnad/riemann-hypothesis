module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqNsmulOfForallDvdOfBijective
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelRankNormBound
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FreeModuleNakayamaDescent
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
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle001
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.separated_of_finite_surjective_quotient : ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q → IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left → IsSeparated Y.hom := by
  first | exact @GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective | exact GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective | (intros; apply GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.fixed_by_automorphisms_mem_field : ∀ (F : IntermediateField ℚ ℂ) (c : ℂ), FiniteDimensional ℚ F → (∀ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) → g c = c) → c ∈ F :=
  @_root_.PositivityTheory.Xgn.mem_of_fixed_by_automorphisms
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem norm_det_le_pow_card_of_ultrametric :
    ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I]
      (M : Matrix I I A) (r : ℝ), 0 ≤ r → (∀ a b, ‖M a b‖ ≤ r) →
      ‖M.det‖ ≤ r ^ Fintype.card I := by
  intro A _ _ I _ _ M r hr hM
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr _) ?_
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul, norm_mul]
  have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h2 : ‖∏ i, M (σ i) i‖ ≤ r ^ Fintype.card I := by
    rw [norm_prod]
    calc ∏ i, ‖M (σ i) i‖ ≤ ∏ _i : I, r :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hM _ _)
      _ = r ^ Fintype.card I := by simp
  calc _ ≤ 1 * r ^ Fintype.card I :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem gp_mat_lattice :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
      v.Integers R → ∀ (g : ℕ) (Ht Bt : Matrix (Fin g) (Fin g ⊕ Fin g) R)
        (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) (cp : R),
        cp ≠ 0 → Eᵀ = -E → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E →
          let φ := algebraMap R C
          let intg : (Fin g → C) → Prop := fun w => ∀ k, v (w k) ≤ 1
          let hb : Matrix (Fin g ⊕ Fin g) (Fin g) C := ((Eᵀ)⁻¹ * Htᵀ).map φ
          v (φ (Matrix.fromRows Ht Bt).det) = v (φ cp) ^ g ∧
            (∀ x : Fin g ⊕ Fin g → C, ((Ht.map φ) *ᵥ x = 0 ∧ intg ((Bt.map φ) *ᵥ x)) ↔
              ∃ w, intg w ∧ x = (φ cp)⁻¹ • (hb *ᵥ w)) ∧
            (∀ w, intg w → ∃ x : Fin g ⊕ Fin g → C,
              (Ht.map φ) *ᵥ x = w ∧ (Bt.map φ) *ᵥ x = 0) ∧
            (∀ l : Fin g ⊕ Fin g → R,
              cp • l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k)) := by
  apply PositivityTheory.HtPt.Rh.gp_mat <;> assumption

end GlobalTheory.CompanionTheory.Ar.GR
end

section

open scoped Matrix TensorProduct
open Matrix

theorem _root_.GlobalTheory.T.teichmuller_character_order_generates : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → orderOf σ = p ^ f - 1 ∧ (∀ χ : MulChar F R, ∃ m, 1 ≤ m ∧ m ≤ p ^ f - 1 ∧ χ = σ ^ m) ∧ (∀ n, (∀ a b, (σ ^ p ^ n) (a + b) - (σ ^ p ^ n) a - (σ ^ p ^ n) b ∈ Ideal.span {(p : R)})) ∧ (∀ τ : MulChar F R, (∀ a b, τ (a + b) - τ a - τ b ∈ Ideal.span {(p : R)}) → ∃ n < f, τ = σ ^ p ^ n) ∧ (∀ a b : F, a ≠ b → v (algebraMap R C (σ a - σ b)) = 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.FundGen.main | exact GlobalTheory.CompanionTheory.Ar.GR.FundGen.main | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.FundGen.main <;> assumption)
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

theorem linearIndependent_span_of_dual_unit :
    ∀ (V : Type) [CommRing V] (L : Type) [AddCommGroup L] [Module V L] (n : ℕ)
      (b : Module.Basis (Fin n) V L) (u : Fin n → L) (f : Fin n → (L →ₗ[V] V)) (N : V),
      IsUnit N → (∀ i j, f j (u i) = if i = j then N else 0) →
      LinearIndependent V u ∧ Submodule.span V (Set.range u) = ⊤ := by
  intro V _ L _ _ n b u f N hN hf
  classical

  let U : Matrix (Fin n) (Fin n) V := Matrix.of fun i k => b.repr (u i) k
  let F : Matrix (Fin n) (Fin n) V := Matrix.of fun k j => f j (b k)
  have hUF : U * F = N • (1 : Matrix (Fin n) (Fin n) V) := by
    ext i j
    have h1 : f j (u i) = ∑ k, b.repr (u i) k * f j (b k) := by
      calc f j (u i) = f j (∑ k, b.repr (u i) k • b k) := by rw [b.sum_repr]
        _ = ∑ k, b.repr (u i) k * f j (b k) := by

          simp only [map_sum, map_smul, smul_eq_mul]
    simp only [Matrix.mul_apply, U, F, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [← h1, hf]
    split_ifs <;> simp
  have hdet : IsUnit U.det := by
    have h2 : U.det * F.det = N ^ n := by
      rw [← Matrix.det_mul, hUF, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact isUnit_of_mul_isUnit_left (h2 ▸ hN.pow n)
  have hb : b.toMatrix u = U.transpose := by
    ext k i
    simp [Module.Basis.toMatrix_apply, U]
  have hdet' : IsUnit (b.toMatrix u).det := by
    rw [hb, Matrix.det_transpose]; exact hdet
  have hdet2 : IsUnit (b.det u) := by
    rw [Module.Basis.det_apply]; exact hdet'
  exact (Module.Basis.is_basis_iff_det b).mpr hdet2

end GlobalTheory.CompanionTheory.CommAlg
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_saturation_torsionFree {Λ : Type*} [AddCommGroup Λ] (W : Submodule ℤ Λ) :
    ∃ S : Submodule ℤ Λ, (∀ x, x ∈ S ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W) ∧
      Module.IsTorsionFree ℤ (Λ ⧸ S) := by
  refine ⟨{ carrier := {x | ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W}
            add_mem' := ?_, zero_mem' := ⟨1, one_ne_zero, by simp⟩, smul_mem' := ?_ },
    fun x => Iff.rfl, ?_⟩
  · rintro a b ⟨k, hk, ha⟩ ⟨l, hl, hb⟩
    refine ⟨k * l, mul_ne_zero hk hl, ?_⟩
    rw [smul_add]
    refine W.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact W.smul_mem _ ha
    · rw [mul_smul]; exact W.smul_mem _ hb
  · rintro c a ⟨k, hk, ha⟩
    exact ⟨k, hk, by rw [smul_comm]; exact W.smul_mem _ ha⟩
  · rw [GlobalTheory.isTorsionFree_quotient_iff]
    rintro r x hr ⟨k, hk, hx⟩
    exact ⟨k * r, mul_ne_zero hk hr, by rw [mul_smul]; exact hx⟩

theorem exists_symplecticBasis_lagrangian_between : ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (B : LinearMap.BilinForm ℤ Λ), (∀ x, B x x = 0) → Function.Bijective B → Module.finrank ℤ Λ = 2 * g → ∀ W : Submodule ℤ Λ, (∀ x, (∀ y ∈ W, B x y = 0) → ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W) → ∃ bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ, (∀ i j, B (bas (.inl i)) (bas (.inl j)) = 0 ∧ B (bas (.inr i)) (bas (.inr j)) = 0 ∧ B (bas (.inl i)) (bas (.inr j)) = if i = j then 1 else 0) ∧ (∀ i, ∃ k : ℤ, k ≠ 0 ∧ k • bas (.inl i) ∈ W) ∧ ∀ x, (∀ y ∈ W, B x y = 0) → x ∈ Submodule.span ℤ (Set.range fun i => bas (.inl i)) := by
  intro g Λ _ _ _ B hB hp hg W hW
  have hA : B.IsAlt := hB
  obtain ⟨S, hS, hSt⟩ := exists_saturation_torsionFree W
  have hmem : ∀ x, x ∈ B.orthogonal S ↔ ∀ y ∈ W, B x y = 0 := by
    intro x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h y hy
      exact hA.isRefl _ _ (h y ((hS y).2 ⟨1, one_ne_zero, by simpa using hy⟩))
    · intro h y hy
      obtain ⟨k, hk, hy⟩ := (hS y).1 hy
      have := h _ hy
      rw [map_smul, smul_eq_mul] at this
      exact hA.isRefl _ _ ((mul_eq_zero.1 this).resolve_left hk)
  have hoo : B.orthogonal (B.orthogonal S) = S :=
    GlobalTheory.orthogonal_orthogonal_of_isTorsionFree_quotient hA hp.2 hSt
  have hiso : B.orthogonal S ≤ B.orthogonal (B.orthogonal S) := by
    rw [hoo]
    intro x hx
    exact (hS x).2 (hW x ((hmem x).1 hx))
  let v := Module.finBasis ℤ (B.orthogonal S)
  obtain ⟨m, b, hb, hv⟩ := GlobalTheory.exists_isSymplecticBasis_extend hA hp
    (GlobalTheory.isTorsionFree_quotient_orthogonal B S) hiso v
  have hc := GlobalTheory.IsSymplecticBasisOfType.finrank_eq b
  have hc' : Fintype.card (Fin (Module.finrank ℤ (B.orthogonal S)) ⊕ Fin m) = g := by omega
  let σ := Fintype.equivFinOfCardEq hc'
  have hb' := hb.reindex σ
  have hl : ∀ i, (b.reindex (σ.sumCongr σ)) (.inl i) = b (.inl (σ.symm i)) := by
    intro i; simp
  refine ⟨b.reindex (σ.sumCongr σ), fun i j => ⟨hb'.left_left i j, hb'.right_right i j,
    hb'.left_right i j⟩, fun i => ?_, fun x hx => ?_⟩
  · refine (hS _).1 (hoo.le ((hb.orthogonal_eq_span hv).ge ?_))
    rw [hl]
    exact Submodule.subset_span (Or.inl ⟨_, rfl⟩)
  · have hx' := (hmem x).2 hx
    have h1 : x = ∑ i, v.repr ⟨x, hx'⟩ i • (v i : Λ) := by
      have := congrArg Subtype.val (v.sum_repr ⟨x, hx'⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [h1]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨σ (.inl i), ?_⟩)
    simp only [hl, Equiv.symm_apply_apply, hv]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_of_forall_exists_sub_eq_nsmul (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (W : Submodule ℤ Λ) (hW : ∀ (k : ℤ) x, k ≠ 0 → k • x ∈ W → x ∈ W) (x : Λ)
    (h : ∀ N : ℕ, 0 < N → ∃ w ∈ W, ∃ b : Λ, x - w = N • b) : x ∈ W := by
  have htf : Module.IsTorsionFree ℤ (Λ ⧸ W) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective W m
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hrm
      exact (Submodule.Quotient.mk_eq_zero W).mpr (hW r y hr hrm)
  have hfree : Module.Free ℤ (Λ ⧸ W) := Module.free_iff_isTorsionFree.mpr htf
  let bs := Module.Free.chooseBasis ℤ (Λ ⧸ W)
  rw [← Submodule.Quotient.mk_eq_zero W]
  refine bs.repr.injective ?_
  rw [map_zero]
  ext i
  rw [Finsupp.zero_apply]
  obtain ⟨w, hw, b, hb⟩ := h ((bs.repr (Submodule.Quotient.mk x) i).natAbs + 1) (by omega)
  generalize hn : (bs.repr (Submodule.Quotient.mk x) i).natAbs = n at hb
  have hq : (Submodule.Quotient.mk x : Λ ⧸ W) = (n + 1) • Submodule.Quotient.mk b := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← hb]
    simpa using hw
  have hc : bs.repr (Submodule.Quotient.mk x) i =
      ((n + 1 : ℕ) : ℤ) * bs.repr (Submodule.Quotient.mk b) i := by
    rw [hq, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  have habs := congrArg Int.natAbs hc
  rw [Int.natAbs_mul, Int.natAbs_natCast, hn] at habs
  rcases Nat.eq_zero_or_pos (bs.repr (Submodule.Quotient.mk b) i).natAbs with ht | ht
  · rw [ht, mul_zero] at habs
    rw [habs] at hn
    exact Int.natAbs_eq_zero.mp hn
  · nlinarith

theorem mem_of_forall_card_mul_eq_pow :
    ∀ (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
      (B : LinearMap.BilinForm ℤ Λ), Function.Bijective B → (∀ x, B x x = 0) →
      ∀ W : Submodule ℤ Λ, (∀ (k : ℤ) x, k ≠ 0 → k • x ∈ W → x ∈ W) →
      (∀ N : ℕ, 0 < N →
        ∃ T : Set (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))),
          Nat.card (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))) * Nat.card T
            = N ^ Module.finrank ℤ Λ ∧
          ∀ x y : W, Submodule.Quotient.mk x ∈ T → (N : ℤ) ∣ B x y) →
      ∀ x, (∀ y ∈ W, B x y = 0) → x ∈ W := by
  intro Λ _ _ _ B hB halt W hW hT x hx
  apply mem_of_forall_exists_sub_eq_nsmul Λ W hW x
  intro N hN
  obtain ⟨T, hcard, hTpair⟩ := hT N hN
  let R : Λ → (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))) → Prop :=
    fun a p => ∃ w : W, Submodule.Quotient.mk w = p ∧ ∃ b : Λ, a - w = N • b
  have h1 : ∀ a b p, R a p → R (a + N • b) p := by
    rintro a b p ⟨w, hw, b0, hb0⟩
    refine ⟨w, hw, b0 + b, ?_⟩
    rw [smul_add, ← hb0]
    abel
  have h2 : ∀ a p p', R a p → R a p' → p = p' := by
    rintro a p p' ⟨w, rfl, b, hb⟩ ⟨w', rfl, b', hb'⟩
    have hdiff : ((w : Λ) - w') = (N : ℤ) • (b' - b) := by
      rw [natCast_zsmul, smul_sub, ← hb, ← hb']
      abel
    have hmem : b' - b ∈ W :=
      hW (N : ℤ) (b' - b) (by exact_mod_cast hN.ne') (by rw [← hdiff]; exact W.sub_mem w.2 w'.2)
    rw [Submodule.Quotient.eq]
    refine ⟨⟨b' - b, hmem⟩, ?_⟩
    apply Subtype.ext
    exact hdiff.symm
  have h3 : ∀ p, ∃ a, R a p := by
    intro p
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    exact ⟨w, w, rfl, 0, by simp⟩
  have h4 : ∀ a p a' p', R a p → p ∈ T → R a' p' → (N : ℤ) ∣ B a a' := by
    rintro a p a' p' ⟨w, rfl, b, hb⟩ hp ⟨w', -, b', hb'⟩
    have ha : a = w + N • b := by rw [← hb]; abel
    have ha' : a' = w' + N • b' := by rw [← hb']; abel
    have hww := hTpair w w' hp
    have hexp : B (↑w + N • b) (↑w' + N • b') = B w w' + N * (B w b' + B b w' + N * B b b') := by
      simp only [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      ring
    rw [ha, ha', hexp]
    exact dvd_add hww (dvd_mul_right _ _)
  have h5 : ∀ a' p', R a' p' → (N : ℤ) ∣ B x a' := by
    rintro a' p' ⟨w', -, b', hb'⟩
    have ha' : a' = w' + N • b' := by rw [← hb']; abel
    rw [ha', map_add (f := _), map_nsmul, hx w' w'.2, zero_add]
    exact ⟨B x b', nsmul_eq_mul _ _⟩
  obtain ⟨p, w, -, b, hwb⟩ :=
    GlobalTheory.exists_rel_of_forall_dvd_of_card_mul Λ B hB N hN _ T R h1 h2 h3 hcard h4 x h5
  exact ⟨w, w.2, b, hwb⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem free_extension_kernel_bound_charpoly : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E), a ≠ 0 → Module.finrank k (LinearMap.ker (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ))) ≤ Module.finrank (𝓞 E) Λ * padicValNat p (Algebra.norm ℤ a).natAbs ∧ (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ Module.finrank (𝓞 E) Λ := by
  exact @PositivityTheory.Xgn.kernel_rank_norm_bound

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_dual_integral_of_saturated_free_part :
    ∀ (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C]
      [IsFractionRing V C] (W : Type) [AddCommGroup W] [Module C W] [Module V W]
      [IsScalarTower V C W] [FiniteDimensional C W] (Lie : Submodule V W) (n : ℕ) (w : Fin n → W),
      Lie.FG → Submodule.span C (Lie : Set W) = ⊤ → LinearIndependent C w →
      (∀ y, y ∈ Submodule.span V (Set.range w) ↔ y ∈ Lie ∧ y ∈ Submodule.span C (Set.range w)) →
      ∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧
        ∀ k, φ (w k) = if k = j then 1 else 0 := by
  intro V C _ _ _ _ _ _ W _ _ _ _ _ Lie n w hfg _ hw hsat j
  classical
  let W' : Submodule C W := Submodule.span C (Set.range w)
  obtain ⟨p, q, u, t, -, hu, ht, -, -, hspan⟩ :=
    exists_basis_split_of_exact_of_fg_valuationRing V C W' W (W ⧸ W') W'.subtype W'.mkQ
      W'.injective_subtype (LinearMap.exact_subtype_mkQ W') Lie hfg
  have hwW : ∀ i, w i ∈ W' := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hli : LinearIndependent C (Sum.elim w t) := by
    rw [Fintype.linearIndependent_iff]
    intro f hf
    rw [Fintype.sum_sum_type] at hf
    simp only [Sum.elim_inl, Sum.elim_inr] at hf
    have h1 : ∀ i, f (Sum.inr i) = 0 := by
      have h := congrArg W'.mkQ hf
      have hz : ∀ i, W'.mkQ (w i) = 0 := fun i => by
        simpa using hwW i

      simp only [map_add (f := _), map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero, zero_add,
      map_zero] at h
      exact Fintype.linearIndependent_iff.mp ht _ h
    have h2 : ∀ i, f (Sum.inl i) = 0 := by
      simp only [h1, zero_smul, Finset.sum_const_zero, add_zero] at hf
      exact Fintype.linearIndependent_iff.mp hw _ hf
    rintro (i | i)
    · exact h2 i
    · exact h1 i
  obtain ⟨g, hg⟩ := (Finsupp.linearCombination C (Sum.elim w t)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hli)
  have hgs : ∀ a, g (Sum.elim w t a) = Finsupp.single a 1 := fun a => by
    have h1 := LinearMap.congr_fun hg (Finsupp.single a 1)
    simpa [Finsupp.linearCombination_single] using h1
  let φ : Module.Dual C W := Finsupp.lapply (Sum.inl j) ∘ₗ g
  have hφw : ∀ k, φ (w k) = if k = j then 1 else 0 := fun k => by
    have h := hgs (Sum.inl k)
    simp only [Sum.elim_inl] at h
    simp [φ, h, Finsupp.single_apply]
  have hφt : ∀ i, φ (t i) = 0 := fun i => by
    have h := hgs (Sum.inr i)
    simp only [Sum.elim_inr] at h
    simp [φ, h, Finsupp.single_apply]
  let R : Submodule V C := LinearMap.range (Algebra.linearMap V C)
  have hone : (1 : C) ∈ R := ⟨1, by simp⟩
  have hzero : (0 : C) ∈ R := R.zero_mem
  have hspw : Submodule.span V (Set.range w) ≤ R.comap (φ.restrictScalars V) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    change φ (w k) ∈ R
    rw [hφw]
    split_ifs
    · exact hone
    · exact hzero
  have hle : Lie ≤ R.comap (φ.restrictScalars V) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · apply hspw
      have hmem : u i ∈ Lie.comap (W'.subtype.restrictScalars V) := by
        rw [← hu]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact (hsat _).mpr ⟨hmem, (u i).2⟩
    · change φ (t i) ∈ R
      rw [hφt]
      exact hzero
  refine ⟨φ, fun y hy => ?_, hφw⟩
  obtain ⟨a, ha⟩ := hle hy
  exact ⟨a, by simpa using ha⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem free_of_free_over_field : ∀ (E : Type) [Field E] [NumberField E] (R k : Type) [CommRing R] [IsLocalRing R] [Field k] (f : R →+* k) [IsLocalHom f] (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) (ρ : 𝓞 E →+* Matrix n n R), (∃ x : Fin r → n → k, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) = ⊤) → ∃ x : Fin r → n → R, LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤ :=
  @PositivityTheory.Xgn.free_module_nakayama_descent

end GlobalTheory.CompanionTheory.Ar.Flat
end
