module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle004
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle015
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReducedBasisOfLinearIndependent
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Filtration
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst

@[expose] public section

section

namespace GlobalTheory

namespace Unipotence

open Polynomial

theorem pow_card_eq_zero {K n : Type} [Field K] [IsAlgClosed K] [Fintype n] [DecidableEq n]
    (Y : Matrix n n K) (h : ∀ μ ∈ spectrum K Y, μ = 0) : IsNilpotent Y := by
  have hm := Y.charpoly_monic
  have hs : Y.charpoly.Splits := IsAlgClosed.splits _
  have hr : Y.charpoly.roots = Multiset.replicate (Multiset.card Y.charpoly.roots) 0 := by
    rw [Multiset.eq_replicate_card]
    intro μ hμ
    exact h μ (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (isRoot_of_mem_roots hμ))
  have he := hs.eq_prod_roots_of_monic hm
  rw [hr] at he
  have hch := Matrix.aeval_self_charpoly Y
  rw [he] at hch
  refine ⟨Multiset.card Y.charpoly.roots, ?_⟩
  simpa using hch

theorem root_of_unity {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hA : IsUnit A) (P : (Matrix n n K)ˣ) (q : ℕ) (hq : 2 ≤ q)
    (h : (P : Matrix n n K) * A = A ^ q * P) (x : K) (hx : x ∈ spectrum K A) :
    ∃ m : ℕ, m ≠ 0 ∧ x ^ m = 1 := by
  have hconj : A ^ q = P * A * (P⁻¹ : (Matrix n n K)ˣ) := by
    rw [h, mul_assoc, Units.mul_inv, mul_one]
  have hstep : ∀ y ∈ spectrum K A, y ^ q ∈ spectrum K A := by
    intro y hy
    have := spectrum.pow_mem_pow A q hy
    rwa [hconj, spectrum.units_conjugate] at this
  have hall : ∀ k : ℕ, x ^ (q ^ k) ∈ spectrum K A := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ, pow_mul]; exact hstep _ ih
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact (spectrum.zero_mem_iff K).mp hx hA
  obtain ⟨i, j, hij, he⟩ := (Matrix.finite_spectrum A).exists_lt_map_eq_of_forall_mem hall
  have hlt : q ^ i < q ^ j := Nat.pow_lt_pow_right (by omega) hij
  refine ⟨q ^ j - q ^ i, by omega, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (q ^ i) hx0)
  rw [← pow_add, mul_one, Nat.add_sub_cancel' hlt.le]
  exact he.symm

theorem eq_zero_of_integral (l : ℕ) [hl : Fact l.Prime] (h3 : 3 ≤ l) {K : Type} [Field K] [CharZero K]
    [Algebra ℤ_[l] K] (μ : K) (hμ : IsIntegral ℤ_[l] μ) (m : ℕ) (hm : m ≠ 0)
    (h : (1 + l • μ) ^ m = 1) : μ = 0 := by
  let E := Algebra.adjoin ℤ_[l] ({μ} : Set K)
  haveI : Module.Finite ℤ_[l] E := Module.Finite.iff_fg.mpr hμ.fg_adjoin_singleton
  let ψ : E := ⟨μ, Algebra.self_mem_adjoin_singleton _ _⟩
  have hl0 : l ≠ 0 := by omega
  have key : (1 : E) + l • ψ = 1 := by
    refine SerreTorsion.eq_one_of_pow (E := E) (q := l) (c := l) ?_ hl.out ?_ hl0 dvd_rfl
      (fun h2 => by omega) m hm ψ ?_
    · intro n x hn hx
      have : (n : K) * (x : K) = 0 := by
        have := congrArg (Subtype.val : E → K) hx
        simpa using this
      exact Subtype.ext ((mul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr hn))
    · intro x hx
      have hk := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := ℤ_[l]) (M := E)
        (IsLocalRing.maximalIdeal ℤ_[l]) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      rw [← Submodule.mem_bot ℤ_[l], ← hk, Submodule.mem_iInf]
      intro k
      obtain ⟨y, hy⟩ := hx k
      rw [hy, ← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]
      refine Submodule.smul_mem_smul (Ideal.pow_mem_pow ?_ k) Submodule.mem_top
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    · apply Subtype.ext
      simpa [ψ] using h
  have := congrArg (Subtype.val : E → K) key
  simpa [ψ, hl0] using this

theorem matrix_nilpotent (l : ℕ) [hl : Fact l.Prime] (h3 : 3 ≤ l) {n : Type} [Fintype n]
    [DecidableEq n] (Y P : Matrix n n ℤ_[l]) (hA : IsUnit (1 + l • Y)) (hP : IsUnit P)
    (q : ℕ) (hq : 2 ≤ q) (h : P * (1 + l • Y) = (1 + l • Y) ^ q * P) : IsNilpotent Y := by
  let K := AlgebraicClosure ℚ_[l]
  have hinj : Function.Injective (algebraMap ℤ_[l] K) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  let f : Matrix n n ℤ_[l] →+* Matrix n n K := (algebraMap ℤ_[l] K).mapMatrix
  have hf : Function.Injective f := Matrix.map_injective hinj
  rw [← IsNilpotent.map_iff hf]
  apply pow_card_eq_zero
  intro μ hμ
  have hint : IsIntegral ℤ_[l] μ := by
    refine ⟨Y.charpoly, Y.charpoly_monic, ?_⟩
    have := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ
    rw [show f Y = Y.map (algebraMap ℤ_[l] K) from rfl, Matrix.charpoly_map] at this
    rw [← Polynomial.eval_map]
    exact this
  have hspec : 1 + l • μ ∈ spectrum K (f (1 + l • Y)) := by
    have := spectrum.subset_polynomial_aeval (f Y) (1 + l • (X : K[X])) ⟨μ, hμ, rfl⟩
    simpa using this
  obtain ⟨m, hm, hx⟩ := root_of_unity (f (1 + l • Y)) (hA.map f) (hP.map f).unit q hq
    (by rw [IsUnit.unit_spec, ← map_mul, h, map_mul, map_pow]) _ hspec
  exact eq_zero_of_integral l h3 μ hint m hm hx

end Unipotence

theorem isNilpotent_sub_one_of_conj_pow :
    ∀ (l : ℕ) [Fact l.Prime], 3 ≤ l → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (S Φ : T ≃ₗ[ℤ_[l]] T) (q : ℕ), 2 ≤ q → Φ * S = S ^ q * Φ → (∀ x, ∃ y, S x - x = l • y) → IsNilpotent ((S : T →ₗ[ℤ_[l]] T) - 1) := by
  intro l _ h3 T _ _ _ _ S Φ q hq h hS
  classical
  let b := Module.Free.chooseBasis ℤ_[l] T
  choose y hy using hS
  let Y : Module.End ℤ_[l] T := b.constr ℤ_[l] (fun i => y (b i))
  have hSY : (S : T →ₗ[ℤ_[l]] T) = 1 + l • Y := by
    apply b.ext
    intro i
    simp only [Y, LinearMap.add_apply, LinearMap.smul_apply, Module.Basis.constr_basis,
      Module.End.one_apply, LinearEquiv.coe_coe, ← hy]
    abel
  let g : (T ≃ₗ[ℤ_[l]] T) →* Module.End ℤ_[l] T := LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hgS : g S = 1 + l • Y := hSY
  let e := LinearMap.toMatrixAlgEquiv b
  have heS : e (g S) = 1 + l • e Y := by rw [hgS, map_add (f := _), map_one, map_nsmul]
  have hN : IsNilpotent (e Y) := by
    refine Unipotence.matrix_nilpotent l h3 (e Y) (e (g Φ)) ?_ (((Group.isUnit Φ).map g).map e) q hq ?_
    · rw [← heS]; exact ((Group.isUnit S).map g).map e
    · rw [← heS, ← map_mul, ← map_mul, h, map_mul, map_mul, map_pow, map_pow]
  rw [IsNilpotent.map_iff (f := e) e.injective] at hN
  rw [hSY, add_sub_cancel_left]
  exact hN.smul l

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.AffineThickening

theorem exists_isAffineOpen_preimage_eq_of_isNilpotent (A A' : Type) [CommRing A] [CommRing A']
    (g : A →+* A') (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g))
    (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A'))
    (β : X' ⟶ X) (h : IsPullback β f' f (Spec.map (CommRingCat.ofHom g)))
    (D' : X'.Opens) (hD' : IsAffineOpen D') :
    ∃ D : X.Opens, IsAffineOpen D ∧ β ⁻¹ᵁ D = D' := by
  have h1 := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg
  have : IsClosedImmersion β := MorphismProperty.of_isPullback h.flip h1
  obtain ⟨O, hO, hO'⟩ := β.isClosedEmbedding.isInducing.isOpen_iff.mp D'.isOpen
  have e : β ⁻¹ᵁ ⟨O, hO⟩ = D' := Opens.ext hO'
  refine ⟨⟨O, hO⟩, ?_, e⟩
  subst e
  exact isAffine_of_isPullback_of_isNilpotent (RingHom.ker g) hn (CommRingCat.ofHom g) hg rfl
    ((isPullback_morphismRestrict β ⟨O, hO⟩).paste_vert h) hD'

end GlobalTheory.AffineThickening
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isDominant_homOfVector_of_quasiFiniteAt' : ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  first | exact @GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt | exact GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt | (intros; apply GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt <;> assumption)
end

section

open Module

namespace GlobalTheory

theorem eq_zero_of_sum_eq_sum_add_nsmul {X : Type*} [AddCommGroup X] {ι : Type*}
    (e : Basis ι ℤ X) {C : ℝ} (hC : 0 ≤ C) {N' D k : ℕ} (hN' : 2 * (D : ℝ) * C < N') (hk : k ≤ D)
    (α β : Fin k → X) (hα : ∀ j i, |(e.repr (α j) i : ℝ)| ≤ C)
    (hβ : ∀ j i, |(e.repr (β j) i : ℝ)| ≤ C) (w : X)
    (h : ∑ j, α j = ∑ j, β j + N' • w) : w = 0 := by
  refine e.repr.injective (Finsupp.ext fun i => ?_)
  have h1 : ∑ j, (e.repr (α j) i : ℝ) = ∑ j, (e.repr (β j) i : ℝ) + N' * (e.repr w i : ℝ) := by
    have := congrArg (fun x => e.repr x i) h

    simp only [map_add (f := _), map_sum, map_nsmul, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul] at this
    exact_mod_cast this
  have bound : ∀ γ : Fin k → X, (∀ j i, |(e.repr (γ j) i : ℝ)| ≤ C) →
      |∑ j, (e.repr (γ j) i : ℝ)| ≤ D * C := fun γ hγ => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => hγ j i).trans ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hC
  have hA := abs_le.1 (bound α hα)
  have hB := abs_le.1 (bound β hβ)
  have hpos : (0 : ℝ) < N' := lt_of_le_of_lt (by positivity) hN'
  have h2 : (e.repr w i : ℝ) < 1 := by
    by_contra hc
    have := mul_le_mul_of_nonneg_left (not_lt.1 hc) hpos.le
    linarith [hA.2, hB.1]
  have h3 : (-1 : ℝ) < (e.repr w i : ℝ) := by
    by_contra hc
    have := mul_le_mul_of_nonneg_left (not_lt.1 hc) hpos.le
    linarith [hA.1, hB.2]
  have h2' : e.repr w i < 1 := by exact_mod_cast h2
  have h3' : -1 < e.repr w i := by exact_mod_cast h3
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  omega

theorem exists_basis_unique_min_and_sums_separated :
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ), Filter.Tendsto q Filter.cofinite Filter.atTop → ∀ (d g N N' D : ℕ), finrank ℤ X = d → d ≤ g → 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N → 2 * (D : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)) * N < N' → ∃ e : Basis (Fin d) ℤ X, (∀ (i : Fin d) (μ : X), μ ≠ 0 → q (e i) < q (e i + N • μ) ∧ q (-e i) < q (-e i + N • μ)) ∧ ∀ (k : ℕ) (α β : Fin k → X), k ≤ D → (∀ j w, q (α j) ≤ q (α j + N • w)) → (∀ j w, q (β j) ≤ q (β j + N • w)) → ∀ w : X, ∑ j, α j = ∑ j, β j + N' • w → w = 0 := by
  intro X _ _ _ q hq d g N N' D hd hg hN hN'
  obtain ⟨e, -, h2, h3⟩ :=
    exists_reduced_basis_unique_min_of_le hd hg q (posDef_realExt_of_tendsto q hq)
  have h0 : (0 : ℝ) ≤ 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) := by positivity
  have hN1 : (1 : ℤ) ≤ (N : ℤ) := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  refine ⟨e, fun i μ hμ => ?_, fun k α β hk hα hβ w h => ?_⟩
  · have := h3 (N : ℤ) (by push_cast; linarith) i μ hμ
    simpa only [natCast_zsmul] using this
  · have key : ∀ γ : Fin k → X, (∀ j w, q (γ j) ≤ q (γ j + N • w)) → ∀ j i,
        |(e.repr (γ j) i : ℝ)| ≤
          (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) * N := fun γ hγ j i => by
      have := h2 (N : ℤ) hN1 (γ j) (fun w => by simpa only [natCast_zsmul] using hγ j w) i
      simpa only [Int.cast_natCast] using this
    exact eq_zero_of_sum_eq_sum_add_nsmul e (by positivity) (by linarith) hk α β
      (key α hα) (key β hβ) w h

end GlobalTheory
end

section

open Module

namespace GlobalTheory

theorem exists_basis_unique_min_pair_sums (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (d g N : ℕ) (hd : finrank ℤ X = d)
    (hg : d ≤ g) (hN : 1 + 4 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N) :
    ∃ e : Basis (Fin d) ℤ X, ∀ (i j : Fin d) (μ : X), μ ≠ 0 →
      q (e i) < q (e i + N • μ) ∧ q (e i + e j) < q (e i + e j + N • μ) := by
  have hq' := posDef_realExt_of_tendsto q hq
  obtain ⟨e, h1, -, -⟩ := exists_reduced_basis_unique_min_of_le hd hg q hq'
  have hp := posDef_of_posDef_realExt hq'
  set c := (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hN' : 1 + 4 * c < ((N : ℤ) : ℝ) := by
    rw [hc, ← mul_assoc]; exact_mod_cast hN
  refine ⟨e, fun i j μ hμ => ?_⟩
  rw [← natCast_zsmul]
  refine ⟨(lt_add_smul_of_abs_polar_le q hc0 (by linarith) (hp μ hμ) (h1 i μ)).1,
    (lt_add_smul_of_abs_polar_le q (c := 2 * c) (by positivity) (by linarith) (hp μ hμ) ?_).1⟩
  rw [QuadraticMap.polar_add_left]
  refine (abs_add_le _ _).trans ?_
  linarith [h1 i μ, h1 j μ]

end GlobalTheory
end
