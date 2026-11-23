module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate
public import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicIsogeny
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle005
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionPoints
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeron
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle002
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle006
public import GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddUniversal
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
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialBaseChange
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation

@[expose] public section

section

namespace GroundTheory.Global

noncomputable section

open Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

theorem exists_algebraMap_eq_of_isAlgebraic_ff (E : WeierstrassCurve F) [E.IsElliptic]
    {u : E.toAffine.FunctionField} (hu : IsAlgebraic F u) :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = u := by
  classical
  have hu' : IsAlgebraic (AlgebraicClosure F) (bcEmb (F' := AlgebraicClosure F) E u) :=
    (hu.algHom (bcEmb (F' := AlgebraicClosure F) E)).tower_top (AlgebraicClosure F)
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic (E.baseChange (AlgebraicClosure F)) hu'
  exact exists_algebraMap_eq_of_bcEmb E hc.symm

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem isGenPt_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsGenPt E' Q := by
  classical
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl h0
  · by_contra hx
    have hx' : IsAlgebraic F x := not_not.mp hx
    obtain ⟨a, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hx'
    have hy' : IsAlgebraic F y := by
      have := isIntegral_y E' F h.1 (mem_algebraicClosure_iff.2 (isAlgebraic_algebraMap a))
      exact mem_algebraicClosure_iff.1 this
    obtain ⟨b, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hy'
    have hc : (E'.baseChange F).toAffine.Nonsingular a b :=
      (E'.toAffine.baseChange_nonsingular (f := Algebra.ofId F E.toAffine.FunctionField)
        (algebraMap F _).injective a b).mp h
    have hQc : (Point.some _ _ h : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) =
        Point.map (Algebra.ofId F E.toAffine.FunctionField) (Point.some _ _ hc) := by
      rw [Point.map_some, Point.some.injEq]; exact ⟨rfl, rfl⟩
    have key := (respectsAdd_iff _).mp hQ (univField E) (univPt₁ E) (univPt₂ E)
      (isGenPt_univPt₁ E) (isGenPt_univPt₂ E) (isGenPt_univPt₁₂ E)
    have hconst : ∀ (σ : E.toAffine.FunctionField →ₐ[F] univField E),
        Point.map σ (Point.some _ _ h) =
          Point.map (Algebra.ofId F (univField E)) (Point.some _ _ hc) := fun σ => by
      rw [hQc, Point.map_map]
      have e : σ.comp (Algebra.ofId F E.toAffine.FunctionField) = Algebra.ofId F (univField E) :=
        AlgHom.ext fun z => by
          rw [AlgHom.comp_apply, Algebra.ofId_apply, Algebra.ofId_apply, σ.commutes]
      rw [e]
    rw [hconst, hconst, hconst, left_eq_add] at key
    have := Point.map_injective (W' := E') (Algebra.ofId F (univField E))
      (key.trans (map_zero _).symm)
    exact Point.some_ne_zero hc this

theorem isIsogeny_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsIsogeny E E' Q :=
  (isIsogeny_iff Q).mpr ⟨isGenPt_of_respectsAdd hQ h0, hQ⟩

end

end GroundTheory.Global
end

section

open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian KaehlerDifferential
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L₁ L₂ : PeriodPair}

theorem homConst_ne_zero {Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)} (hQ : Q ≠ 0) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q ≠ 0 := by
  set φ := isogOfHom Q hQ
  have hsep : φ.IsSeparable := by
    have := φ.finiteDimensional
    exact Algebra.IsSeparable.of_integral _ _
  have h1 := (isSeparable_iff_isogConst_ne_zero φ).1 hsep
  have h2 : isogConst φ = homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q := by
    apply (algebraMap ℂ (weierstrassCurve L₁).toAffine.FunctionField).injective
    rw [algebraMap_isogConst, algebraMap_homConst]
    rfl
  rwa [← h2]

theorem homConst_injective :
    Function.Injective (homConst (weierstrassCurve L₁) (weierstrassCurve L₂)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro Q h
  by_contra hQ
  exact homConst_ne_zero hQ h

theorem exists_eq_constMap_of_omegaDeriv {W : WeierstrassCurve ℂ}
    (P : (W.baseChange MeroField).toAffine.Point) (h : omegaDeriv (omegaAt W P) = 0) :
    ∃ R : W.toAffine.Point, P = constMap W MeroField R := by
  rcases P with _ | ⟨u, v, hP⟩
  · exact ⟨0, (map_zero _).symm⟩
  obtain ⟨s₁, s₂⟩ := omegaAt_some_spec W hP
  have e₁ := congrArg omegaDeriv s₁
  have e₂ := congrArg omegaDeriv s₂
  rw [LinearMap.map_smul, h, smul_eq_mul, mul_zero, omegaDeriv_D, eq_comm] at e₁ e₂
  obtain ⟨c, rfl⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero e₁
  obtain ⟨d, rfl⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero e₂
  have hcd : W.toAffine.Nonsingular c d :=
    (W.toAffine.baseChange_nonsingular (f := Algebra.ofId ℂ MeroField)
      (algebraMap ℂ MeroField).injective c d).1 hP
  exact ⟨.some c d hcd, rfl⟩

theorem exists_map_ellEval_eq {Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)}
    (hQ : Q ≠ 0) :
    ∃ c : ℂ, Point.map (ellEval L₁) Q.1 =
      affinePoint L₂ (homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q) c
        (homConst_ne_zero hQ) := by
  set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q
  have h0 : α ≠ 0 := homConst_ne_zero hQ
  have e := omegaAt_eq_homConst_smul Q
  have e' := congrArg (kpush (ellEval L₁)) e
  rw [kpush_omegaAt, kpush_const_smul, invariantDifferential, kpush_omegaAt,
    map_ellEval_genericPoint, basePoint_eq] at e'
  have hω : omegaDeriv (omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1)) =
      algebraMap ℂ MeroField α := by
    rw [e', ← algebraMap_smul MeroField, LinearMap.map_smul, omegaDeriv_affinePoint, smul_eq_mul,
      map_one, mul_one]
  have hD : omegaDeriv (omegaAt (weierstrassCurve L₂)
      (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0)) = 0 := by
    have h1 : omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0) =
        omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1) -
          omegaAt (weierstrassCurve L₂) (affinePoint L₂ α 0 h0) :=
      map_sub (omegaHom (weierstrassCurve L₂)) _ _
    rw [h1, map_sub, hω, omegaDeriv_affinePoint, sub_self]
  obtain ⟨R, hR⟩ := exists_eq_constMap_of_omegaDeriv _ hD
  obtain ⟨c, rfl⟩ := toPoint_surjective (L := L₂) R
  refine ⟨0 + c, ?_⟩
  rw [← affinePoint_add_constMap, ← hR]
  abel

theorem homConst_mem_latticeHom (Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q ∈ latticeHom L₁ L₂ := by
  by_cases hQ : Q = 0
  · rw [hQ, map_zero]
    exact zero_mem _
  set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q
  have h0 : α ≠ 0 := homConst_ne_zero hQ
  obtain ⟨c, hc⟩ := exists_map_ellEval_eq hQ
  have hg : IsGenPt (weierstrassCurve L₂) Q.1 := isGenPt_of_mem_isogHom Q.2 (fun h ↦ hQ (Subtype.ext h))
  obtain ⟨hne, hQs⟩ := eq_some_xOf_yOf _ (isGenPt_ne_zero _ hg)
  rw [hQs, Point.map_some, affinePoint, Point.some.injEq] at hc
  obtain ⟨f, hf, hfe⟩ := exists_isEllipticFunction_ellEval_eq L₁ (xOf _ Q.1)
  obtain ⟨g, hg', hge⟩ := exists_isEllipticFunction_ellEval_eq L₁ (yOf _ Q.1)
  rw [hfe, germ_eq_germ_iff hf.1 (meromorphic_weierstrassP_affine L₂ α c)] at hc
  rw [hge, germ_eq_germ_iff hg'.1 (meromorphic_derivWeierstrassP_half_affine L₂ α c)] at hc
  obtain ⟨hcx, hcy⟩ := hc
  intro l hl
  obtain ⟨z, h1, h2, h3, h4, h5, h6⟩ := nonempty_of_mem_codiscrete (hcx.and (hcy.and
    ((eventually_affine hcx one_ne_zero l).and ((eventually_affine hcy one_ne_zero l).and
    ((eventually_affine (eventually_notMem_lattice L₂) h0 c).and
    (eventually_affine (eventually_notMem_lattice L₂) h0 (α * l + c)))))))
  beta_reduce at h1 h2
  simp only [one_mul] at h3 h4
  rw [hf.2 z l hl] at h3
  rw [hg'.2 z l hl] at h4
  have e₁ : ℘[L₂] (α * z + (α * l + c)) = ℘[L₂] (α * z + c) := by
    rw [← h1, h3, show α * (z + l) + c = α * z + (α * l + c) by ring]
  have e₂ : ℘'[L₂] (α * z + (α * l + c)) = ℘'[L₂] (α * z + c) := by
    have := h2.symm.trans h4
    rw [show α * (z + l) + c = α * z + (α * l + c) by ring] at this
    linear_combination 2 * this.symm
  have hpt : toPoint L₂ (α * z + (α * l + c)) = toPoint L₂ (α * z + c) := by
    rw [toPoint_of_notMem h6, toPoint_of_notMem h5]
    exact point_some_congr e₁ (by rw [e₂])
  have := torusToPoint_injective (L := L₂) (a₁ := Torus.mk L₂ _) (a₂ := Torus.mk L₂ _) hpt
  rw [Torus.mk_eq_mk_iff] at this
  simpa using this

theorem latticeToHom_homConst (Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)) :
    latticeToHom ⟨_, homConst_mem_latticeHom Q⟩ = Q :=
  homConst_injective (by rw [homConst_latticeToHom])

theorem latticeToHom_add (α β : latticeHom L₁ L₂) :
    latticeToHom (α + β) = latticeToHom α + latticeToHom β :=
  homConst_injective (by
    rw [map_add (f := _), homConst_latticeToHom, homConst_latticeToHom, homConst_latticeToHom]
    rfl)

theorem ellEval_comp_translate (L : PeriodPair) (z : ℂ) :
    (ellEval L).comp (translate (weierstrassCurve L) (toPoint L z)) =
      (affineComp 1 z one_ne_zero).comp (ellEval L) := by
  apply algHom_eq_of_map_genericPoint' (E := weierstrassCurve L)
  rw [← Point.map_map, map_translate_genericPoint, map_add (f := _), map_ellEval_genericPoint,
    show constPoint (weierstrassCurve L) (toPoint L z) =
      constMap (weierstrassCurve L) _ (toPoint L z) from rfl, map_constMap, basePoint_eq,
    affinePoint_add_constMap, ← Point.map_map, map_ellEval_genericPoint, basePoint_eq,
    map_affineComp_affinePoint]
  exact affinePoint_congr L _ _ (by ring) (by ring)

theorem homPt_latticeToHom (α : latticeHom L₁ L₂) (z : ℂ) :
    homPt (latticeToHom α) (toPoint L₁ z) = toPoint L₂ (α * z) := by
  by_cases h0 : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α h0, homPt_zero, AddMonoidHom.zero_apply, h0, zero_mul,
      toPoint_zero]
  apply homPt_eq_of
  apply Point.map_injective (ellEval L₁)
  rw [Point.map_map, ellEval_comp_translate, ← Point.map_map, latticeToHom_of_ne_zero α h0,
    map_ellEval_isogPt, map_affineComp_affinePoint, map_add, map_ellEval_isogPt, map_constMap,
    affinePoint_add_constMap]
  exact affinePoint_congr L₂ _ _ (by ring) (by ring)

section End

variable {L : PeriodPair}

theorem latticeToHom_mul (α β : latticeHom L L) (h : (α : ℂ) * β ∈ latticeHom L L) :
    latticeToHom ⟨_, h⟩ = latticeToHom α * latticeToHom β := by
  by_cases hα : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α hα, zero_mul, latticeToHom_of_eq_zero _ (by simp [hα])]
  by_cases hβ : (β : ℂ) = 0
  · rw [latticeToHom_of_eq_zero β hβ, mul_zero, latticeToHom_of_eq_zero _ (by simp [hβ])]
  have hg : IsGenPt (weierstrassCurve L) (latticeToHom β).1 := by
    rw [latticeToHom_of_ne_zero β hβ]
    exact isGenPt_isogPt _ _
  apply Subtype.ext
  apply Point.map_injective (ellEval L)
  have e : Point.map (ellEval L) (latticeToHom β).1 = affinePoint L β 0 hβ := by
    rw [latticeToHom_of_ne_zero β hβ, map_ellEval_isogPt]
  rw [isogEnd_mul_def, homComp_of_isGenPt _ _ hg, Point.map_map, ← genEval_map _ (ellEval L) hg,
    genEval_congr _ e _ (isGenPt_affinePoint L β 0 hβ), genEval_affinePoint, ← Point.map_map,
    latticeToHom_of_ne_zero α hα, map_ellEval_isogPt, map_affineComp_affinePoint,
    latticeToHom_of_ne_zero _ (mul_ne_zero hα hβ), map_ellEval_isogPt]
  exact affinePoint_congr L _ _ rfl (by ring)

end End

end Elliptic
end GroundTheory.Global
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian

section Scale

variable {R : Type*} [CommRing R]

def scaleCoeffs (W : WeierstrassCurve R) (a : R) : WeierstrassCurve R :=
  ⟨a * W.a₁, a ^ 2 * W.a₂, a ^ 3 * W.a₃, a ^ 4 * W.a₄, a ^ 6 * W.a₆⟩

theorem map_scaleCoeffs {S : Type*} [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) (a : R) :
    (scaleCoeffs W a).map f = scaleCoeffs (W.map f) (f a) := by
  ext <;> simp [scaleCoeffs]

def scaleVariableChange {F : Type*} [Field F] {c : F} (hc : c ≠ 0) :
    WeierstrassCurve.VariableChange F :=
  ⟨(Units.mk0 c hc)⁻¹, 0, 0, 0⟩

theorem scaleVariableChange_smul {F : Type*} [Field F] (W : WeierstrassCurve F) {c : F}
    (hc : c ≠ 0) : scaleVariableChange hc • W = scaleCoeffs W c := by
  ext <;> simp [scaleVariableChange, scaleCoeffs, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆]

end Scale

section Torsion

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [(W.map (algebraMap 𝒪 K)).IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

local notation "ι" => algebraMap 𝒪 K
local notation "ρ" => residue 𝒪

theorem nsmul_ne_zero_of_notMem_range {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0) {X Y : K}
    (h : (curveK K W).Nonsingular X Y) (hX : X ∉ Set.range ι) :
    n • WeierstrassCurve.Affine.Point.some _ _ h ≠ 0 := by
  intro hnP
  have hι := IsFractionRing.injective 𝒪 K
  obtain ⟨z, w, v, hzm, hz0, -, -, hwv, hvu, hρv, hXz, hYw⟩ :=
    exists_zw_of_notMem_range K W h.1 hX
  have hzK : ι z ≠ 0 := (map_ne_zero_iff _ hι).2 hz0
  set W' := scaleCoeffs W z with hW'
  have hC : scaleVariableChange hzK • W.map ι = W'.map ι := by
    rw [scaleVariableChange_smul, hW', map_scaleCoeffs]
  have : (W'.map ι).IsElliptic := hC ▸ inferInstance
  set v' : 𝒪 := ↑hvu.unit⁻¹ with hv'
  have hvv : v * v' = 1 := hvu.mul_val_inv
  have hvK : ι v * ι v' = 1 := by rw [← map_mul, hvv, map_one]
  have hwK : ι w = ι z ^ 3 * ι v := by rw [hwv, map_mul, map_pow]
  have hvK0 : ι v ≠ 0 := left_ne_zero_of_mul_eq_one hvK
  have hv'K : ι v' = (ι v)⁻¹ := eq_inv_of_mul_eq_one_right hvK
  have hx' : vcX (scaleVariableChange hzK) X = ι v' := by
    simp only [vcX, scaleVariableChange, inv_inv, Units.val_mk0, sub_zero]
    rw [← hXz, hwK, hv'K]
    field_simp
  have hy' : vcY (scaleVariableChange hzK) X Y = ι (-v') := by
    simp only [vcY, scaleVariableChange, inv_inv, Units.val_mk0, sub_zero, zero_mul]
    rw [← hYw, hwK, map_neg, hv'K]
    field_simp
  have h' : (curveK K W').Nonsingular (ι v') (ι (-v')) := by
    have := (nonsingular_vc (scaleVariableChange hzK) (W.map ι) X Y).2 h
    rw [hC, hx', hy'] at this
    exact this
  set φ := vcPointEquiv (scaleVariableChange hzK) hC
  have hφ : φ (.some _ _ h) = .some _ _ h' := by
    rw [vcPointEquiv_apply, vcPoint_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx', hy'⟩

  have hρz : ρ z = 0 := residue_eq_zero_of_mem hzm
  have h1 : (W'.map ρ).a₁ = -2 * 0 := by simp [hW', scaleCoeffs, hρz]
  have h2 : (W'.map ρ).a₂ = -0 ^ 2 := by simp [hW', scaleCoeffs, hρz]
  have h3 : (W'.map ρ).a₃ = 0 := by simp [hW', scaleCoeffs, hρz]
  have h4 : (W'.map ρ).a₄ = 0 := by simp [hW', scaleCoeffs, hρz]
  have h6 : (W'.map ρ).a₆ = 0 := by simp [hW', scaleCoeffs, hρz]
  have hρv' : ρ v' = 1 := by
    have := congrArg ρ hvv
    rwa [map_mul, hρv, one_mul, map_one] at this
  have n' : (curveRed W').Nonsingular (ρ v') (ρ (-v')) :=
    origin_nonsingular (W'.map ρ) h3 h4 h6 (equation_residue W' (equation_of_map K W' h'.1))
      (by rw [hρv']; exact one_ne_zero)
  have hE0 : φ (.some _ _ h) ∈ E0Subgroup K W' := by
    rw [hφ]; exact mem_E0Set_some_integral K W' h' n'
  set Q : E0Subgroup K W' := ⟨_, hE0⟩
  have hnQ : n • Q = 0 := by
    apply Subtype.ext
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
    change n • φ _ = 0
    rw [← map_nsmul, hnP, map_zero]
  have hred : reduceE0Hom K W' Q = .some _ _ n' := by
    rw [reduceE0Hom_apply]
    change reducePoint K W' (φ _) = _
    rw [hφ, reducePoint_some_integral K W' h' n']
  have key : n • cuspHom (W'.map ρ) h3 h4 h6 0 h1 h2 (reduceE0Hom K W' Q) = 0 := by
    rw [← map_nsmul, ← map_nsmul, hnQ, map_zero, map_zero]
  rw [hred] at key
  change n • (ρ v' / (ρ (-v') - 0 * ρ v')) = 0 at key
  rw [map_neg, hρv'] at key
  apply hn
  simpa using key

end Torsion

section Good

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [W.IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

theorem eq_zero_of_nsmul_eq_zero_of_reducePoint_eq_zero {n : ℕ}
    (hn : (n : ResidueField 𝒪) ≠ 0) {P : (curveK K W).Point} (hnP : n • P = 0)
    (hP : reducePoint K W P = 0) : P = 0 := by
  rcases point_cases K W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · rfl
  · exact absurd hnP (nsmul_ne_zero_of_notMem_range K W hn h hX)
  · rw [reducePoint_some_integral K W h (nonsingular_residue_of_isElliptic K W h.1)] at hP
    exact absurd hP (WeierstrassCurve.Affine.Point.some_ne_zero _)

theorem eq_of_reductionHom_eq_of_nsmul {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0)
    {P Q : (curveK K W).Point} (hP : n • P = 0) (hQ : n • Q = 0)
    (h : reductionHom K W P = reductionHom K W Q) : P = Q :=
  sub_eq_zero.1 (eq_zero_of_nsmul_eq_zero_of_reducePoint_eq_zero K W hn
    (by rw [nsmul_sub, hP, hQ, sub_zero])
    (by rw [← reductionHom_apply, map_sub, h, sub_self]))

end Good

section Localization

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] (v : HeightOneSpectrum R)

end Localization

section NumberField

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F] (𝔮 : HeightOneSpectrum (𝓞 F))
  (W : WeierstrassCurve (𝔮.valuationSubringAtPrime F)) [W.IsElliptic] [DecidableEq F]
  [DecidableEq (ResidueField (𝔮.valuationSubringAtPrime F))]

end NumberField

end

end GroundTheory.Global
end
