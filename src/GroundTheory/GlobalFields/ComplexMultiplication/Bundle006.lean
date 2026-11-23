module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupReduction
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionPoints
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialBaseChange
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstant
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionGauss
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle001
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian

section E0

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [(W.map (algebraMap 𝒪 K)).IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

local notation "ι" => algebraMap 𝒪 K
local notation "ρ" => residue 𝒪

omit [DecidableEq (ResidueField 𝒪)] in
theorem add_notMem_of_notMem_range {X₁ Y₁ X₂ Y₂ : K} (h₁ : (curveK K W).Nonsingular X₁ Y₁)
    (hX₁ : X₁ ∉ Set.range ι) (h₂ : (curveK K W).Nonsingular X₂ Y₂) (hX₂ : X₂ ∉ Set.range ι)
    {x y : 𝒪} (h : (curveK K W).Nonsingular (ι x) (ι y)) :
    WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ ≠
      WeierstrassCurve.Affine.Point.some _ _ h := by
  intro hS
  have hn : (curveK K W).Nonsingular X₂ ((curveK K W).negY X₂ Y₂) :=
    (WeierstrassCurve.Affine.nonsingular_neg _ _).2 h₂
  obtain ⟨x₃, y₃, h₃, e, -, -⟩ := add_of_notMem_range' K W hn hX₂ h
  have hneg : -(WeierstrassCurve.Affine.Point.some _ _ h₂) =
      WeierstrassCurve.Affine.Point.some _ _ hn := WeierstrassCurve.Affine.Point.neg_some h₂
  have e' : WeierstrassCurve.Affine.Point.some _ _ h₁ =
      WeierstrassCurve.Affine.Point.some _ _ h₃ := by
    rw [← e, ← hS, ← hneg]; abel
  rw [WeierstrassCurve.Affine.Point.some.injEq] at e'
  exact hX₁ ⟨x₃, e'.1.symm⟩

theorem add_mem_E0Set_and_reducePoint_add {P Q : (curveK K W).Point} (hP : P ∈ E0Set K W)
    (hQ : Q ∈ E0Set K W) :
    P + Q ∈ E0Set K W ∧ reducePoint K W (P + Q) = reducePoint K W P + reducePoint K W Q := by
  rcases point_cases K W P with rfl | ⟨X₁, Y₁, h₁, rfl, hX₁⟩ | ⟨x₁, y₁, h₁, rfl⟩
  · rw [zero_add, reducePoint_zero, zero_add]; exact ⟨hQ, rfl⟩
  · rcases point_cases K W Q with rfl | ⟨X₂, Y₂, h₂, rfl, hX₂⟩ | ⟨x₂, y₂, h₂, rfl⟩
    · rw [add_zero, reducePoint_zero, add_zero]; exact ⟨hP, rfl⟩
    · rw [reducePoint_some_notMem K W h₁ hX₁, reducePoint_some_notMem K W h₂ hX₂, add_zero]
      rcases point_cases K W (WeierstrassCurve.Affine.Point.some _ _ h₁ +
          WeierstrassCurve.Affine.Point.some _ _ h₂) with h0 | ⟨X, Y, h, hS, hX⟩ | ⟨x, y, h, hS⟩
      · rw [h0]; exact ⟨zero_mem_E0Set K W, rfl⟩
      · rw [hS]; exact ⟨mem_E0Set_some_notMem K W h hX, reducePoint_some_notMem K W h hX⟩
      · exact absurd hS (add_notMem_of_notMem_range K W h₁ hX₁ h₂ hX₂ h)
    · have n₂ := hQ x₂ y₂ h₂ rfl
      obtain ⟨x₃, y₃, h₃, e, hx, hy⟩ := add_of_notMem_range' K W h₁ hX₁ h₂
      refine add_mem_and_reduce_of_exists K W ⟨x₃, y₃, h₃, hx ▸ hy ▸ n₂, e, ?_⟩
      rw [reducePoint_some_notMem K W h₁ hX₁, zero_add, reducePoint_some_integral K W h₂ n₂,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx.symm, hy.symm⟩
  · have n₁ := hP x₁ y₁ h₁ rfl
    rcases point_cases K W Q with rfl | ⟨X₂, Y₂, h₂, rfl, hX₂⟩ | ⟨x₂, y₂, h₂, rfl⟩
    · rw [add_zero, reducePoint_zero, add_zero]; exact ⟨hP, rfl⟩
    · obtain ⟨x₃, y₃, h₃, e, hx, hy⟩ := add_of_notMem_range' K W h₂ hX₂ h₁
      rw [add_comm] at e
      refine add_mem_and_reduce_of_exists K W ⟨x₃, y₃, h₃, hx ▸ hy ▸ n₁, e, ?_⟩
      rw [reducePoint_some_notMem K W h₂ hX₂, add_zero, reducePoint_some_integral K W h₁ n₁,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx.symm, hy.symm⟩
    · have n₂ := hQ x₂ y₂ h₂ rfl
      rw [reducePoint_some_integral K W h₁ n₁, reducePoint_some_integral K W h₂ n₂]
      by_cases hx : ρ x₁ = ρ x₂
      · by_cases hy : ρ y₁ = (curveRed W).negY (ρ x₂) (ρ y₂)
        · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
          rcases add_of_residue_neg K W h₁ h₂ n₁ n₂ hx hy with h0 | ⟨X, Y, h, hS, hX⟩
          · rw [h0]; exact ⟨zero_mem_E0Set K W, rfl⟩
          · rw [hS]; exact ⟨mem_E0Set_some_notMem K W h hX, reducePoint_some_notMem K W h hX⟩
        · have hy' : ρ y₁ = ρ y₂ := by
            rcases WeierstrassCurve.Affine.Y_eq_of_X_eq n₁.1 n₂.1 hx with h | h
            · exact h
            · exact absurd h hy
          have hD : ρ (y₁ + y₂ + W.a₁ * x₁ + W.a₃) ≠ 0 := by
            intro h0; apply hy
            rw [map_add (f := _), map_add (f := _), map_add (f := _), map_mul] at h0
            simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁,
              WeierstrassCurve.map_a₃, ← hx]
            linear_combination h0
          obtain ⟨x₃, y₃, h₃, n₃, e, e'⟩ := add_of_residue_eq K W h₁ h₂ n₁ n₂ hx hy' hD
          rw [e, e', reducePoint_some_integral K W h₃ n₃]
          exact ⟨mem_E0Set_some_integral K W h₃ n₃, rfl⟩
      · obtain ⟨x₃, y₃, h₃, n₃, e, e'⟩ := add_of_residue_X_ne K W h₁ h₂ n₁ n₂ hx
        rw [e, e', reducePoint_some_integral K W h₃ n₃]
        exact ⟨mem_E0Set_some_integral K W h₃ n₃, rfl⟩

def E0Subgroup : AddSubgroup (curveK K W).Point where
  carrier := E0Set K W
  zero_mem' := zero_mem_E0Set K W
  add_mem' hP hQ := (add_mem_E0Set_and_reducePoint_add K W hP hQ).1
  neg_mem' hP := (neg_mem_and_reduce K W hP).1

def reduceE0Hom : E0Subgroup K W →+ (curveRed W).Point where
  toFun P := reducePoint K W P
  map_zero' := reducePoint_zero K W
  map_add' P Q := (add_mem_E0Set_and_reducePoint_add K W P.2 Q.2).2

theorem reduceE0Hom_apply (P : E0Subgroup K W) : reduceE0Hom K W P = reducePoint K W P := rfl

end E0

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

section Descent

variable (E : WeierstrassCurve F) [E.IsElliptic]

theorem exists_eq_add_mul_genY (c : E.toAffine.FunctionField) :
    ∃ r s : E.toAffine.FunctionField, r ∈ F⟮genX E⟯ ∧ s ∈ F⟮genX E⟯ ∧ c = r + s * genY E := by
  set F₁ := F⟮genX E⟯
  have hfin : FiniteDimensional F₁ E.toAffine.FunctionField :=
    Module.finite_of_finrank_pos (by rw [finrank_adjoin_genX E]; norm_num)
  have hint : IsIntegral F₁ (genY E) := Algebra.IsIntegral.isIntegral _
  have htop : F₁⟮genY E⟯ = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := F),
      IntermediateField.adjoin_simple_adjoin_simple]
    exact adjoin_genX_genY E
  have hdeg : (minpoly F₁ (genY E)).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top',
      finrank_adjoin_genX E]
  have hc : c ∈ (F₁⟮genY E⟯).toSubalgebra := by rw [htop]; trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hc
  obtain ⟨p, rfl⟩ := hc
  have hm1 : minpoly F₁ (genY E) ≠ 1 := fun h => by rw [h, natDegree_one] at hdeg; omega
  have hq : (p %ₘ minpoly F₁ (genY E)).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p (minpoly.monic hint) hm1
    omega
  have hval : aeval (genY E) p = aeval (genY E) (p %ₘ minpoly F₁ (genY E)) :=
    (aeval_modByMonic_eq_self_of_root (minpoly.aeval F₁ (genY E))).symm
  obtain ⟨q, hqdef⟩ : ∃ q, q = p %ₘ minpoly F₁ (genY E) := ⟨_, rfl⟩
  rw [← hqdef] at hq hval
  refine ⟨(q.coeff 0 : E.toAffine.FunctionField), (q.coeff 1 : E.toAffine.FunctionField),
    (q.coeff 0).2, (q.coeff 1).2, ?_⟩
  change aeval (genY E) p = _
  rw [hval, eq_X_add_C_of_natDegree_le_one hq]
  simp only [map_add (f := _), map_mul, aeval_C, aeval_X, coeff_add, coeff_C_mul_X, coeff_C]
  simp
  ring

variable {F' : Type u} [Field F'] [Algebra F F']

theorem exists_algebraMap_eq_of_bcEmb {c : E.toAffine.FunctionField} {a : F'}
    (h : bcEmb (F' := F') E c = algebraMap F' (E.baseChange F').toAffine.FunctionField a) :
    ∃ a₀ : F, algebraMap F E.toAffine.FunctionField a₀ = c := by
  set K' := (E.baseChange F').toAffine.FunctionField
  have hinj : Function.Injective (bcEmb (F' := F') E) := (bcEmb (F' := F') E).toRingHom.injective
  have hmap : ∀ w ∈ F⟮genX E⟯, bcEmb (F' := F') E w ∈ F'⟮genX (E.baseChange F')⟯ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx, bcEmb_genX]; exact mem_adjoin_simple_self F' _
    | algebraMap x =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' K']
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨r, s, hr, hs, rfl⟩ := exists_eq_add_mul_genY E c
  rw [map_add (f := _), map_mul, bcEmb_genY] at h
  have hs0 : bcEmb (F' := F') E s = 0 := by
    by_contra hne
    apply genY_not_mem (E.baseChange F')
    have e : genY (E.baseChange F') =
        (algebraMap F' K' a - bcEmb (F' := F') E r) / bcEmb (F' := F') E s := by
      rw [eq_div_iff hne]; linear_combination h
    rw [e]
    exact div_mem (sub_mem (IntermediateField.algebraMap_mem _ a) (hmap r hr)) (hmap s hs)
  have hs00 : s = 0 := hinj (by rw [hs0, map_zero])
  rw [hs0, zero_mul, add_zero] at h
  rw [hs00, zero_mul, add_zero]
  obtain ⟨p, q, rfl⟩ := (mem_adjoin_simple_iff F r).mp hr
  by_cases hq0 : aeval (genX E) q = 0
  · exact ⟨0, by rw [hq0, div_zero, map_zero]⟩
  have hq : q ≠ 0 := fun h0 => hq0 (by rw [h0, map_zero])
  have hq0' : aeval (genX (E.baseChange F')) q ≠ 0 := by
    rw [← bcEmb_genX, aeval_algHom_apply]
    exact fun h0 => hq0 (hinj (by rw [h0, map_zero]))
  rw [map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, bcEmb_genX, div_eq_iff hq0'] at h
  have key : aeval (genX (E.baseChange F'))
      (p.map (algebraMap F F') - C a * q.map (algebraMap F F')) = 0 := by
    rw [map_sub, map_mul, aeval_C, aeval_map_algebraMap, aeval_map_algebraMap]
    linear_combination h
  rw [aeval_genX_eq_zero_iff] at key
  have hcoeff : ∀ j, algebraMap F F' (p.coeff j) = a * algebraMap F F' (q.coeff j) := by
    intro j
    have := congrArg (fun (f : F'[X]) => f.coeff j) key
    simp only [coeff_sub, coeff_map, coeff_C_mul, coeff_zero] at this
    linear_combination this
  have hqi : q.coeff q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hq
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : F, a₀ = p.coeff q.natDegree / q.coeff q.natDegree := ⟨_, rfl⟩
  have ha : a = algebraMap F F' a₀ := by
    rw [ha₀, map_div₀, hcoeff, mul_div_cancel_right₀ _ ((_root_.map_ne_zero _).mpr hqi)]
  have hp : p = C a₀ * q := by
    ext j
    apply (algebraMap F F').injective
    rw [coeff_C_mul, map_mul, hcoeff j, ← ha]
  refine ⟨a₀, ?_⟩
  rw [hp, map_mul, aeval_C, mul_div_cancel_right₀ _ hq0]

end Descent

section Constant

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem exists_algebraMap_eq_isogCoeff (φ : Isogeny E E') :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = isogCoeff φ := by
  classical
  obtain ⟨b, hb⟩ := exists_isogCoeff_eq_algebraMap
    (isogBaseChange (F' := AlgebraicClosure F) φ)
  rw [isogCoeff_isogBaseChange] at hb
  exact exists_algebraMap_eq_of_bcEmb E hb.symm

noncomputable def invConst (φ : Isogeny E E') : F :=
  (exists_algebraMap_eq_isogCoeff φ).choose

theorem algebraMap_invConst (φ : Isogeny E E') :
    algebraMap F E.toAffine.FunctionField (invConst φ) = isogCoeff φ :=
  (exists_algebraMap_eq_isogCoeff φ).choose_spec

theorem isogenyPullback_eq_invConst_smul (φ : Isogeny E E') :
    isogenyPullback φ (invariantDifferential E') = invConst φ • invariantDifferential E := by
  rw [isogenyPullback_invariantDifferential_eq_smul, ← algebraMap_invConst, algebraMap_smul]


variable (E) in
theorem invConst_mulIsogeny (n : ℤ) (hn : n ≠ 0) : invConst (mulIsogeny E n hn) = n :=
  (algebraMap F E.toAffine.FunctionField).injective (by
    rw [algebraMap_invConst, isogCoeff_mulIsogeny, map_intCast])

theorem invConst_isogBaseChange {F' : Type u} [Field F'] [Algebra F F'] [DecidableEq F']
    (φ : Isogeny E E') :
    invConst (isogBaseChange (F' := F') φ) = algebraMap F F' (invConst φ) :=
  (algebraMap F' (E.baseChange F').toAffine.FunctionField).injective (by
    rw [algebraMap_invConst, isogCoeff_isogBaseChange, ← algebraMap_invConst, AlgHom.commutes,
      IsScalarTower.algebraMap_apply F F' (E.baseChange F').toAffine.FunctionField])

end Constant

end GroundTheory.Global
end

section

namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian WeierstrassCurve.Affine

section PointMap

variable {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L] (f : F →+* L)
  (V : WeierstrassCurve F)

def pointMapRing : V.toAffine.Point →+ (V.map f).toAffine.Point :=
  letI := f.toAlgebra
  Point.map (W' := V) (Algebra.ofId F L)

theorem pointMapRing_some {x y : F} (h : V.toAffine.Nonsingular x y) :
    ∃ h' : (V.map f).toAffine.Nonsingular (f x) (f y),
      pointMapRing f V (.some x y h) = .some _ _ h' :=
  ⟨_, rfl⟩

end PointMap

section Functorial

variable {𝒪₁ 𝒪₂ : Type*} [CommRing 𝒪₁] [IsDomain 𝒪₁] [IsDiscreteValuationRing 𝒪₁]
  [CommRing 𝒪₂] [IsDomain 𝒪₂] [IsDiscreteValuationRing 𝒪₂]
  (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra 𝒪₁ K₁] [IsFractionRing 𝒪₁ K₁] [Algebra 𝒪₂ K₂]
  [IsFractionRing 𝒪₂ K₂] {f : 𝒪₁ →+* 𝒪₂} [IsLocalHom f] {σ : K₁ →+* K₂}
  (hσ : σ.comp (algebraMap 𝒪₁ K₁) = (algebraMap 𝒪₂ K₂).comp f) (W : WeierstrassCurve 𝒪₁)

include hσ in
theorem map_curveK_eq :
    (W.map (algebraMap 𝒪₁ K₁)).map σ = (W.map f).map (algebraMap 𝒪₂ K₂) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, hσ]

theorem map_curveRed_eq :
    (W.map (residue 𝒪₁)).map (ResidueField.map f) = (W.map f).map (residue 𝒪₂) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, ResidueField.map_comp_residue]


include hσ in
theorem map_notMem_range {X : K₁} (hX : X ∉ Set.range (algebraMap 𝒪₁ K₁)) :
    σ X ∉ Set.range (algebraMap 𝒪₂ K₂) := by
  rintro ⟨s, hs⟩
  obtain ⟨t, htm, ht⟩ := exists_inv_mem_of_notMem_range K₁ hX
  have hX0 : X ≠ 0 := fun h => hX ⟨0, by rw [h, map_zero]⟩
  have h1 : algebraMap 𝒪₂ K₂ (s * f t) = 1 := by
    rw [map_mul, hs, ← RingHom.comp_apply, ← hσ, RingHom.comp_apply, ht, ← map_mul,
      mul_inv_cancel₀ hX0, map_one]
  have hu : IsUnit (f t) := isUnit_iff_exists_inv.mpr ⟨s,
    IsFractionRing.injective 𝒪₂ K₂ (by rw [mul_comm, h1, map_one])⟩
  exact (mem_maximalIdeal _).1 htm (isUnit_of_map_unit f t hu)

variable [W.IsElliptic] [DecidableEq K₁] [DecidableEq K₂] [DecidableEq (ResidueField 𝒪₁)]
  [DecidableEq (ResidueField 𝒪₂)]

theorem reducePoint_pointMapRing (P : (curveK K₁ W).Point) :
    reducePoint K₂ (W.map f) (pointCongr (map_curveK_eq K₁ K₂ hσ W)
        (pointMapRing σ (W.map (algebraMap 𝒪₁ K₁)) P)) =
      pointCongr (map_curveRed_eq W)
        (pointMapRing (ResidueField.map f) (W.map (residue 𝒪₁)) (reducePoint K₁ W P)) := by
  rcases point_cases K₁ W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · rw [reducePoint_zero, map_zero, map_zero, map_zero, map_zero, reducePoint_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some σ (W.map (algebraMap 𝒪₁ K₁)) h
    rw [e, pointCongr_some, reducePoint_some_notMem K₂ (W.map f) _ (map_notMem_range K₁ K₂ hσ hX),
      reducePoint_some_notMem K₁ W h hX, map_zero, map_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some σ (W.map (algebraMap 𝒪₁ K₁)) h
    have hx : σ (algebraMap 𝒪₁ K₁ x) = algebraMap 𝒪₂ K₂ (f x) := by
      rw [← RingHom.comp_apply, hσ, RingHom.comp_apply]
    have hy : σ (algebraMap 𝒪₁ K₁ y) = algebraMap 𝒪₂ K₂ (f y) := by
      rw [← RingHom.comp_apply, hσ, RingHom.comp_apply]
    have h₂ : (curveK K₂ (W.map f)).Nonsingular (algebraMap 𝒪₂ K₂ (f x))
        (algebraMap 𝒪₂ K₂ (f y)) := by
      have := (map_curveK_eq K₁ K₂ hσ W) ▸ h'
      rwa [hx, hy] at this
    have n₁ := nonsingular_residue_of_isElliptic K₁ W h.1
    have n₂ := nonsingular_residue_of_isElliptic K₂ (W.map f) h₂.1
    obtain ⟨n₁', e₁⟩ := pointMapRing_some (ResidueField.map f) (W.map (residue 𝒪₁)) n₁
    have e₂ : pointCongr (map_curveK_eq K₁ K₂ hσ W) (.some _ _ h') = .some _ _ h₂ := by
      rw [pointCongr_some, Point.some.injEq]
      exact ⟨hx, hy⟩
    rw [e, e₂, reducePoint_some_integral K₂ (W.map f) h₂ n₂, reducePoint_some_integral K₁ W h n₁,
      e₁, pointCongr_some, Point.some.injEq, ResidueField.map_residue, ResidueField.map_residue]
    exact ⟨rfl, rfl⟩

end Functorial

section FF

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

abbrev gaussCurve : WeierstrassCurve (gaussRing W) := W'.map (algebraMap 𝒪 (gaussRing W))

theorem gaussCurve_map_functionField :
    (gaussCurve W W').map (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField) =
      (W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField := by
  show W'.map ((algebraMap (gaussRing W) _).comp (algebraMap 𝒪 (gaussRing W))) =
    W'.map ((algebraMap K _).comp (algebraMap 𝒪 K))
  rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

theorem gaussCurve_map_residue :
    ((gaussCurve W W').map (residue (gaussRing W))).map (gaussResidue W) =
      (W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField := by
  simp only [gaussCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  ext c
  simp [gaussResidue_residue_algebraMap]

variable [W'.IsElliptic]

def reduceFF : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point →+
    ((W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField).toAffine.Point :=
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  (pointCongr (gaussCurve_map_residue W W')).toAddMonoidHom.comp
    ((pointMapRing (gaussResidue W) _).comp
      ((reductionHom (W.baseChange K).toAffine.FunctionField (gaussCurve W W')).comp
        (pointCongr (gaussCurve_map_functionField K W W').symm).toAddMonoidHom))

end FF

end

end GroundTheory.Global
end
