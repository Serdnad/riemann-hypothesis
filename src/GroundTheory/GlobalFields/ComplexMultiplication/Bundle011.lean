module

public import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityClass
import GroundTheory.GlobalFields.ComplexMultiplication.Bundle003
public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionIso
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialBaseChange
public import GroundTheory.GlobalFields.ComplexMultiplication.WeberFunctionAutomorphisms
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle003
public import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDescent
public import GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphism
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module WeierstrassCurve IntermediateField
open scoped nonZeroDivisors

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

section Extend

variable {K : Type*} [Field K] [Algebra K ℂ]

theorem exists_algEquiv_extend_adjoin {α : ℂ} (hα : IsAlgebraic K α) (φ : K⟮α⟯ →ₐ[K] ℂ) :
    ∃ σ : ℂ ≃ₐ[K] ℂ, ∀ z : K⟮α⟯, σ z = φ z := by
  have hint := hα.isIntegral
  have hroot : Polynomial.aeval (φ (AdjoinSimple.gen K α)) (minpoly K α) = 0 := by
    rw [Polynomial.aeval_algHom_apply, aeval_gen_minpoly, map_zero]
  have heq : minpoly K α = minpoly K (φ (AdjoinSimple.gen K α)) :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hroot (minpoly.monic hint)
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_minpoly_eq hα heq
  refine ⟨σ, fun z ↦ ?_⟩
  have e : (σ.toAlgHom.comp (K⟮α⟯).val) = φ := by
    apply adjoin_algHom_ext
    rintro x rfl
    exact hσ
  exact DFunLike.congr_fun e z

end Extend

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]
include hK

def galClassHom : (ℂ ≃ₐ[K] ℂ) →* ClassGroup (𝓞 K) where
  toFun σ := galClass (algebraMap K ℂ) hK σ.toRingEquiv
  map_one' := galClass_one (algebraMap K ℂ) hK
  map_mul' σ τ := galClass_mul (algebraMap K ℂ) hK σ.toRingEquiv τ.toRingEquiv
    (fun k ↦ σ.commutes k) (fun k ↦ τ.commutes k)

theorem galClassHom_apply_j (σ : ℂ ≃ₐ[K] ℂ) (x : ELL K) :
    σ (ELL.j x) = ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassHom hK σ) x) :=
  apply_j_eq_j_galClass_smul (algebraMap K ℂ) hK σ.toRingEquiv (fun k ↦ σ.commutes k) x

theorem galClassHom_eq_one_iff (σ : ℂ ≃ₐ[K] ℂ) (x : ELL K) :
    galClassHom hK σ = 1 ↔ σ (ELL.j x) = ELL.j x :=
  galClass_eq_one_iff (algebraMap K ℂ) hK σ.toRingEquiv (fun k ↦ σ.commutes k) x

theorem ELL.isAlgebraic_j_over (x : ELL K) : IsAlgebraic K (ELL.j x) := by
  have : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact IsAlgebraic.extendScalars (algebraMap ℚ K).injective (ELL.isAlgebraic_j hK x)

theorem ELL.j_mem_adjoin (x y : ELL K) : ELL.j y ∈ K⟮ELL.j x⟯ := by
  have key : ∀ ρ : ℂ ≃ₐ[K⟮ELL.j x⟯] ℂ, ρ (ELL.j y) = ELL.j y := by
    intro ρ
    have h1 : (ρ.restrictScalars K) (ELL.j x) = ELL.j x :=
      ρ.commutes (AdjoinSimple.gen K (ELL.j x))
    rw [← galClassHom_eq_one_iff hK] at h1
    have h2 := galClassHom_apply_j hK (ρ.restrictScalars K) y
    rw [h1, ellMulAction_one_smul] at h2
    exact h2
  obtain ⟨w, hw⟩ := IntermediateField.mem_bot.1
    ((mem_bot_iff_forall_algEquiv_apply_eq (F := K⟮ELL.j x⟯)).2 key)
  rw [← hw]
  exact w.2

section Field

variable (M : IntermediateField K ℂ) (hM : ∀ y : ELL K, ELL.j y ∈ M)
include hM

omit [NumberField K] hK [_root_.NumberField.IsTotallyComplex K] in
theorem adjoin_j_le (x : ELL K) : K⟮ELL.j x⟯ ≤ M :=
  adjoin_simple_le_iff.2 (hM x)

def extendOf (τ : M ≃ₐ[K] M) : ℂ ≃ₐ[K] ℂ :=
  (exists_algEquiv_extend_adjoin (ELL.isAlgebraic_j_over hK (ellEquiv (algebraMap K ℂ) hK 1))
    (M.val.comp (τ.toAlgHom.comp (inclusion (adjoin_j_le M hM _))))).choose

def galClassOfFun (τ : M ≃ₐ[K] M) : ClassGroup (𝓞 K) :=
  galClassHom hK (extendOf hK M hM τ)

theorem galClassOfFun_apply_j (τ : M ≃ₐ[K] M) (y : ELL K) :
    (τ ⟨ELL.j y, hM y⟩ : ℂ) =
      ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassOfFun hK M hM τ) y) := by
  set x₀ := ellEquiv (algebraMap K ℂ) hK 1
  have hy : ELL.j y ∈ K⟮ELL.j x₀⟯ := ELL.j_mem_adjoin hK x₀ y
  have spec := (exists_algEquiv_extend_adjoin (ELL.isAlgebraic_j_over hK x₀)
    (M.val.comp (τ.toAlgHom.comp (inclusion (adjoin_j_le M hM x₀))))).choose_spec ⟨_, hy⟩
  rw [galClassOfFun, ← galClassHom_apply_j]
  exact spec.symm

theorem galClassOfFun_unique (τ : M ≃ₐ[K] M) (a : ClassGroup (𝓞 K)) (y : ELL K)
    (h : (τ ⟨ELL.j y, hM y⟩ : ℂ) = ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul a y)) :
    galClassOfFun hK M hM τ = a := by
  rw [galClassOfFun_apply_j hK M hM] at h
  exact (existsUnique_smul_eq (algebraMap K ℂ) hK y _).unique (ELL.j_injective h) rfl

def galClassOf : (M ≃ₐ[K] M) →* ClassGroup (𝓞 K) where
  toFun := galClassOfFun hK M hM
  map_one' := by
    apply galClassOfFun_unique hK M hM 1 1 (ellEquiv (algebraMap K ℂ) hK 1)
    rw [ellMulAction_one_smul]
    rfl
  map_mul' τ₁ τ₂ := by
    set y := ellEquiv (algebraMap K ℂ) hK 1
    apply galClassOfFun_unique hK M hM _ _ y
    have h2 : τ₂ ⟨ELL.j y, hM y⟩ = ⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul
        (galClassOfFun hK M hM τ₂) y), hM _⟩ :=
      Subtype.ext (galClassOfFun_apply_j hK M hM τ₂ y)
    rw [ellMulAction_mul_smul, ← galClassOfFun_apply_j hK M hM τ₁, ← h2]
    rfl

theorem galClassOf_apply_j (τ : M ≃ₐ[K] M) (y : ELL K) :
    (τ ⟨ELL.j y, hM y⟩ : ℂ) =
      ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassOf hK M hM τ) y) :=
  galClassOfFun_apply_j hK M hM τ y

end Field

section Adjoin

variable (x : ELL K)

end Adjoin

end Elliptic
end GroundTheory.Global
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

theorem pow_eq_one_of_scale {F : Type*} [Field F] {E : WeierstrassCurve F} [E.IsElliptic]
    (hE : IsShortForm E) {u : F} (h4 : E.a₄ = u ^ 4 * E.a₄) (h6 : E.a₆ = u ^ 6 * E.a₆) :
    u ^ automorphismOrder E = 1 ∧ u ^ 12 = 1 := by
  by_cases hu : u = 0
  · subst hu
    rcases hE.a₄_ne_zero_or_a₆_ne_zero with h | h
    · exact absurd (by simpa using h4) h
    · exact absurd (by simpa using h6) h
  have hn : u ^ automorphismOrder E = 1 := by
    have := (scale_conditions_iff hE u⁻¹).mp ⟨by rw [inv_inv]; exact h4.symm,
      by rw [inv_inv]; exact h6.symm⟩
    rwa [inv_pow, inv_eq_one] at this
  refine ⟨hn, ?_⟩
  unfold automorphismOrder at hn
  split_ifs at hn
  · rw [show 12 = 4 * 3 by rfl, pow_mul, hn, one_pow]
  · rw [show 12 = 6 * 2 by rfl, pow_mul, hn, one_pow]
  · rw [show 12 = 2 * 6 by rfl, pow_mul, hn, one_pow]

section AlgClosed

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]


omit [IsAlgClosed F] [A.IsElliptic] [B.IsElliptic] in
theorem vcPoint_constPoint (C : VariableChange F) (hC : C • A = B) (R : A.toAffine.Point) :
    vcPoint (C.baseChange A.toAffine.FunctionField) (Elliptic.baseChange_smul_eq C _ hC)
        (constPoint A R) = constMap B A.toAffine.FunctionField (vcPoint C hC R) := by
  cases R with
  | zero => rfl
  | some x y h =>
    obtain ⟨h', e⟩ := constPoint_some A h
    rw [e, vcPoint_some, vcPoint_some]
    show Point.some _ _ _ = Point.some _ _ _
    rw [Point.some.injEq]
    exact ⟨(map_vcX C (algebraMap F _) x).symm, (map_vcY C (algebraMap F _) x y).symm⟩

theorem pointMap_eq_vcPoint (C : VariableChange F) (hC : C • A = B) (ψ : Isogeny A B)
    (hψ : ψ.1 = vcPoint (C.baseChange A.toAffine.FunctionField)
      (Elliptic.baseChange_smul_eq C _ hC) (genericPoint A)) (R : A.toAffine.Point) :
    ψ.pointMap R = vcPoint C hC R := by
  apply Isogeny.pointMap_eq_of_map_translate
  rw [hψ, Elliptic.map_vcPoint C (translate A R) hC, map_translate_genericPoint, vcPoint_add,
    vcPoint_constPoint]

theorem pointMap_some_of_scale (hA : IsShortForm A) (hB : IsShortForm B) (u : Fˣ)
    (h4 : B.a₄ = (u : F) ^ 4 * A.a₄) (h6 : B.a₆ = (u : F) ^ 6 * A.a₆) (ψ : Isogeny A B)
    (hx : ψ.x = algebraMap F A.toAffine.FunctionField ((u : F) ^ 2) * genX A)
    (hy : ψ.y = algebraMap F A.toAffine.FunctionField ((u : F) ^ 3) * genY A)
    {x y : F} (h : A.toAffine.Nonsingular x y) :
    ∃ h' : B.toAffine.Nonsingular ((u : F) ^ 2 * x) ((u : F) ^ 3 * y),
      ψ.pointMap (.some x y h) = .some _ _ h' := by
  let C : VariableChange F := ⟨u⁻¹, 0, 0, 0⟩
  have hC : C • A = B := by
    ext
    · simp [C, variableChange_a₁, hA.a₁_eq, hB.a₁_eq]
    · simp [C, variableChange_a₂, hA.a₁_eq, hA.a₂_eq, hB.a₂_eq]
    · simp [C, variableChange_a₃, hA.a₁_eq, hA.a₃_eq, hB.a₃_eq]
    · simp [C, variableChange_a₄, hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, h4]
    · simp [C, variableChange_a₆, hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, h6]
  have hψ : ψ.1 = vcPoint (C.baseChange A.toAffine.FunctionField)
      (Elliptic.baseChange_smul_eq C _ hC) (genericPoint A) := by
    rw [ψ.val_eq_some_x_y]
    simp only [GroundTheory.Arith.Abelian.genericPoint, vcPoint_some, Point.some.injEq]
    constructor
    · rw [hx]
      simp [C, vcX, VariableChange.baseChange, VariableChange.map]
    · rw [hy]
      simp [C, vcY, VariableChange.baseChange, VariableChange.map]
  have ex : vcX C x = (u : F) ^ 2 * x := by simp [C, vcX]
  have ey : vcY C x y = (u : F) ^ 3 * y := by simp [C, vcY]
  have hN : B.toAffine.Nonsingular (vcX C x) (vcY C x y) := hC ▸ (nonsingular_vc C A x y).2 h
  rw [ex, ey] at hN
  refine ⟨hN, ?_⟩
  rw [pointMap_eq_vcPoint C hC ψ hψ, vcPoint_some, Point.some.injEq]
  exact ⟨ex, ey⟩

end AlgClosed

section BaseChange

variable {F : Type u} [Field F] {A B : WeierstrassCurve F} [A.IsElliptic] [B.IsElliptic]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] [DecidableEq Ω]

theorem pointMap_isogBaseChange_some_of_degree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hA : IsShortForm A) (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ u : Fˣ, B.a₄ = (u : F) ^ 4 * A.a₄ ∧ B.a₆ = (u : F) ^ 6 * A.a₆ ∧
      ∀ (x y : Ω) (hxy : (A.baseChange Ω).toAffine.Nonsingular x y),
        ∃ h' : (B.baseChange Ω).toAffine.Nonsingular
            (algebraMap F Ω (u : F) ^ 2 * x) (algebraMap F Ω (u : F) ^ 3 * y),
          (isogBaseChange (F' := Ω) ψ).pointMap (.some x y hxy) = .some _ _ h' := by
  obtain ⟨u, hx, hy, h4, h6⟩ := exists_scale_of_degree_eq_one h2 h3 hA hB ψ h
  refine ⟨u, h4, h6, fun x y hxy => ?_⟩
  let v : Ωˣ := Units.map (algebraMap F Ω) u
  have hv : (v : Ω) = algebraMap F Ω (u : F) := rfl
  have h4' : (B.baseChange Ω).a₄ = (v : Ω) ^ 4 * (A.baseChange Ω).a₄ := by
    show algebraMap F Ω B.a₄ = _ * algebraMap F Ω A.a₄
    rw [h4, hv, map_mul, map_pow]
  have h6' : (B.baseChange Ω).a₆ = (v : Ω) ^ 6 * (A.baseChange Ω).a₆ := by
    show algebraMap F Ω B.a₆ = _ * algebraMap F Ω A.a₆
    rw [h6, hv, map_mul, map_pow]
  have hx' : (isogBaseChange (F' := Ω) ψ).x =
      algebraMap Ω (A.baseChange Ω).toAffine.FunctionField ((v : Ω) ^ 2) *
        genX (A.baseChange Ω) := by
    rw [isogBaseChange_alt, hx, map_mul, AlgHom.commutes, bcEmb_genX, hv, ← map_pow,
      ← IsScalarTower.algebraMap_apply]
  have hy' : (isogBaseChange (F' := Ω) ψ).y =
      algebraMap Ω (A.baseChange Ω).toAffine.FunctionField ((v : Ω) ^ 3) *
        genY (A.baseChange Ω) := by
    rw [isogBaseChange_y, hy, map_mul, AlgHom.commutes, bcEmb_genY, hv, ← map_pow,
      ← IsScalarTower.algebraMap_apply]
  exact pointMap_some_of_scale (hA.baseChange Ω) (hB.baseChange Ω) v h4' h6' _ hx' hy' hxy

end BaseChange

end GroundTheory.Global
end
