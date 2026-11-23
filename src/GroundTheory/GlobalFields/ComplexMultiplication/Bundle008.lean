module

public import GroundTheory.GlobalFields.ComplexMultiplication.BaseChange
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle006
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionLift
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
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
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Relrank
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

namespace GroundTheory.Global

open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)
open scoped Polynomial.Bivariate

universe u

section Neg

variable {F : Type u} [Field F] (E : WeierstrassCurve F)

theorem xOf_neg {K : Type*} [Field K] {W : WeierstrassCurve K} (P : W.toAffine.Point) :
    xOf W (-P) = xOf W P := by
  cases P with
  | zero => rfl
  | some x y h => rfl

theorem xOf_map {K L : Type*} [Field K] [Field L] [Algebra F K] [Algebra F L] [DecidableEq K]
    [DecidableEq L] (f : K →ₐ[F] L) (P : (E.baseChange K).toAffine.Point) :
    xOf _ (Point.map f P) = f (xOf _ P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

theorem two_genY_add_ne_zero [E.IsElliptic] :
    (2 : E.toAffine.FunctionField) * genY E + algebraMap F _ E.a₁ * genX E +
      algebraMap F _ E.a₃ ≠ 0 := by
  intro h
  set A := E.toAffine.CoordinateRing
  set K := E.toAffine.FunctionField
  have key : (C E.a₁ * X + C E.a₃ : F[X]) • (1 : A) +
      (2 : F[X]) • WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine Y = 0 := by
    apply IsFractionRing.injective A K
    rw [map_zero, ← h]
    simp only [Algebra.smul_def, mul_one, map_add (f := _), map_mul, ← IsScalarTower.algebraMap_apply,
      genX_eq, genY, map_ofNat]
    rw [IsScalarTower.algebraMap_apply F F[X] K, IsScalarTower.algebraMap_apply F F[X] K,
      Polynomial.algebraMap_apply, Polynomial.algebraMap_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    ring
  obtain ⟨h1, h2⟩ := WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero key
  have h2F : (2 : F) = 0 := by
    have := congrArg (AddMonoidAlgebra.coeff · 0) h2
    simpa using this
  have ha₁ : E.a₁ = 0 := by
    have := congrArg (AddMonoidAlgebra.coeff · 1) h1
    simpa using this
  have ha₃ : E.a₃ = 0 := by
    have := congrArg (AddMonoidAlgebra.coeff · 0) h1
    simpa using this
  have hΔ : E.Δ = 0 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, ha₁, ha₃]
    linear_combination (-8 * E.a₂ ^ 2 * (4 * E.a₂ * E.a₆ - E.a₄ ^ 2) - 32 * E.a₄ ^ 3 -
      216 * E.a₆ ^ 2 + 144 * E.a₂ * E.a₄ * E.a₆) * h2F
  exact not_isUnit_zero (hΔ ▸ E.isUnit_Δ)

end Neg

section Even

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem isGenPt_neg_genericPoint : IsGenPt E (-genericPoint E) :=
  isGenPt_neg (show IsGenPt E (genericPoint E) from transcendental_genX E)


variable (E) in
noncomputable def negFF : E.toAffine.FunctionField →ₐ[F] E.toAffine.FunctionField :=
  genEval E (-genericPoint E) isGenPt_neg_genericPoint

theorem negFF_genX : negFF E (genX E) = genX E := by
  rw [negFF, genEval_genX, xOf_neg]
  rfl

theorem negFF_genY :
    negFF E (genY E) = -genY E - algebraMap F _ E.a₁ * genX E - algebraMap F _ E.a₃ := by
  rw [negFF, genEval_genY]
  rfl

theorem negFF_of_mem {w : E.toAffine.FunctionField} (hw : w ∈ F⟮genX E⟯) : negFF E w = w := by
  induction hw using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx, negFF_genX]
  | algebraMap x => exact AlgHom.commutes _ x
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem mem_adjoin_genX_of_negFF {c : E.toAffine.FunctionField} (h : negFF E c = c) :
    c ∈ F⟮genX E⟯ := by
  obtain ⟨r, s, hr, hs, rfl⟩ := exists_eq_add_mul_genY E c
  rw [map_add (f := _), map_mul, negFF_of_mem hr, negFF_of_mem hs, negFF_genY] at h
  have hs0 : s = 0 := by
    have : s * ((2 : E.toAffine.FunctionField) * genY E + algebraMap F _ E.a₁ * genX E +
        algebraMap F _ E.a₃) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_right (two_genY_add_ne_zero E)
  rw [hs0, zero_mul, add_zero]
  exact hr

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.negFF_alt (φ : Isogeny E E') : negFF E φ.x = φ.x := by
  have hG : IsGenPt E (genericPoint E) := transcendental_genX E
  have e := map_genEval_neg φ.respectsAdd hG
  have e2 : Point.map (genEval E (genericPoint E) hG) φ.1 = φ.1 := φ.app_genericPoint hG
  rw [e2] at e
  have := congrArg (xOf _) e
  rw [xOf_neg, xOf_map] at this
  exact this

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.x_mem_adjoin_genX (φ : Isogeny E E') :
    φ.x ∈ F⟮genX E⟯ :=
  mem_adjoin_genX_of_negFF φ.negFF_alt

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_ratEmb_eq_x (φ : Isogeny E E') :
    ∃ r : RatFunc F, ratEmb E r = φ.x := by
  have h := φ.x_mem_adjoin_genX
  rw [← fieldRange_ratEmb] at h
  exact h

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.degree_eq_max_natDegree (φ : Isogeny E E')
    {r : RatFunc F} (hr : ratEmb E r = φ.x) :
    φ.degree = max r.num.natDegree r.denom.natDegree := by
  set α := φ.comap
  set E1 : IntermediateField F E.toAffine.FunctionField := F⟮genX E⟯
  set M := α.fieldRange
  set E0 : IntermediateField F E.toAffine.FunctionField := F⟮φ.x⟯
  have hxE1 : φ.x ∈ E1 := φ.x_mem_adjoin_genX
  have hxM : φ.x ∈ M := ⟨genX E', φ.comap_genX⟩
  have h01 : E0 ≤ E1 := adjoin_simple_le_iff.mpr hxE1
  have h0M : E0 ≤ M := adjoin_simple_le_iff.mpr hxM
  have e1 : relfinrank E1 ⊤ = 2 := by rw [relfinrank_top_right, finrank_adjoin_genX]
  have e2 : relfinrank E0 M = 2 := by
    have hE0 : E0 = (F⟮genX E'⟯).map α := by
      rw [adjoin_map, Set.image_singleton, φ.comap_genX]
    have hM : M = (⊤ : IntermediateField F _).map α := (map_top_eq_fieldRange α).symm
    rw [hE0, hM, relfinrank_map_map, relfinrank_top_right, finrank_adjoin_genX]
  have e3 : relfinrank E0 E1 = max r.num.natDegree r.denom.natDegree := by
    have hE0 : E0 = (F⟮r⟯).map (ratEmb E) := by
      rw [adjoin_map, Set.image_singleton, hr]
    have hE1 : E1 = (⊤ : IntermediateField F (RatFunc F)).map (ratEmb E) := by
      rw [map_top_eq_fieldRange, fieldRange_ratEmb]
    rw [hE0, hE1, relfinrank_map_map, relfinrank_top_right, RatFunc.finrank_eq_max_natDegree]
  have t1 := relfinrank_mul_relfinrank h01 (le_top : E1 ≤ ⊤)
  have t2 := relfinrank_mul_relfinrank h0M (le_top : M ≤ ⊤)
  rw [e1, e3] at t1
  rw [e2, ← t1] at t2
  have hdeg : φ.degree = relfinrank M ⊤ := by rw [Isogeny.degree, relfinrank_top_right]
  rw [hdeg]
  omega

end Even

section RatFunc

variable {F : Type u} [Field F]

theorem num_denom_div_of_isCoprime {p q : F[X]} (hq : q.Monic) (h : IsCoprime p q) :
    (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).num = p ∧
      (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).denom = q := by
  set r := algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q
  have hq0 : q ≠ 0 := hq.ne_zero
  have hinj := RatFunc.algebraMap_injective F
  have hcross : r.num * q = p * r.denom := by
    have e : algebraMap F[X] (RatFunc F) r.num / algebraMap F[X] (RatFunc F) r.denom =
        algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q := RatFunc.num_div_denom r
    rw [div_eq_div_iff ((map_ne_zero_iff _ hinj).mpr r.denom_ne_zero)
      ((map_ne_zero_iff _ hinj).mpr hq0), ← map_mul, ← map_mul] at e
    exact hinj e
  have hd1 : q ∣ r.denom :=
    h.symm.dvd_of_dvd_mul_left ⟨r.num, by linear_combination -hcross⟩
  have hd2 : r.denom ∣ q :=
    r.isCoprime_num_denom.symm.dvd_of_dvd_mul_left ⟨p, by linear_combination hcross⟩
  have hden : r.denom = q :=
    Polynomial.eq_of_monic_of_associated r.monic_denom hq (associated_of_dvd_dvd hd2 hd1)
  refine ⟨?_, hden⟩
  rw [hden] at hcross
  exact mul_right_cancel₀ hq0 hcross

end RatFunc

section Degree

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [E.IsElliptic] in
theorem ffMap_aeval (p : F[X]) (z : E.toAffine.FunctionField) :
    ffMap σ E (aeval z p) = aeval (ffMap σ E z) (p.map σ) := by
  rw [aeval_def, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a
  simp [ffMap_algebraMap]

end Degree

end GroundTheory.Global
end

section

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

section Transport

theorem pointCongr_pointCongr {F : Type*} [Field F] [DecidableEq F]
    {V₁ V₂ V₃ : WeierstrassCurve F} (h₁ : V₁ = V₂) (h₂ : V₂ = V₃) (P : V₁.toAffine.Point) :
    pointCongr h₂ (pointCongr h₁ P) = pointCongr (h₁.trans h₂) P := by
  subst h₁; subst h₂; rfl

theorem pointMapRing_pointCongr {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    (f : F →+* L) {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) (P : V₁.toAffine.Point) :
    pointMapRing f V₂ (pointCongr h P) =
      pointCongr (congrArg (fun V => V.map f) h) (pointMapRing f V₁ P) := by
  subst h; rfl

theorem pointMapRing_congr {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    {f g : F →+* L} (h : f = g) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    pointMapRing f V P = pointCongr (by rw [h]) (pointMapRing g V P) := by
  subst h; rfl

theorem pointMapRing_pointMapRing {F L L' : Type*} [Field F] [Field L] [Field L'] [DecidableEq F]
    [DecidableEq L] [DecidableEq L'] (f : F →+* L) (g : L →+* L') (V : WeierstrassCurve F)
    (P : V.toAffine.Point) :
    pointMapRing g (V.map f) (pointMapRing f V P) = pointMapRing (g.comp f) V P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

theorem map_eq_pointCongr_pointMapRing {R F₁ F₂ : Type*} [CommRing R] [Field F₁] [Field F₂]
    [Algebra R F₁] [Algebra R F₂] [DecidableEq F₁] [DecidableEq F₂] (V : WeierstrassCurve R)
    (σ : F₁ →ₐ[R] F₂) (P : (V.baseChange F₁).toAffine.Point) :
    Point.map σ P = pointCongr (by
        show V.map (σ.toRingHom.comp (algebraMap R F₁)) = V.map (algebraMap R F₂)
        exact congrArg V.map σ.comp_algebraMap) (pointMapRing σ.toRingHom (V.baseChange F₁) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero (pointCongr _)).symm
  · rw [Point.map_some]
    obtain ⟨h', e⟩ := pointMapRing_some σ.toRingHom (V.baseChange F₁) h
    rw [e, pointCongr_some, Point.some.injEq]
    exact ⟨rfl, rfl⟩

theorem reducePoint_pointCongr {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (K : Type*) [Field K] [Algebra 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
    {V₁ V₂ : WeierstrassCurve 𝒪} (h : V₁ = V₂) (P : (curveK K V₁).Point) :
    reducePoint K V₂ (pointCongr (congrArg (fun V => V.map (algebraMap 𝒪 K)) h) P) =
      pointCongr (congrArg (fun V => V.map (residue 𝒪)) h) (reducePoint K V₁ P) := by
  subst h; rfl

end Transport

section Eval

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  (M : Type*) [Field M] [Algebra Λ M] [IsFractionRing Λ M] [Algebra K M] [DecidableEq M]
  [DecidableEq (ResidueField Λ)]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] [IsDomain Λ]
  [IsDiscreteValuationRing Λ] [IsLocalHom j] [IsFractionRing Λ M] [DecidableEq M]
  [DecidableEq (ResidueField Λ)] in
theorem map_baseChange_eq_map_of
    (hjM : ∀ c : 𝒪, algebraMap K M (algebraMap 𝒪 K c) = algebraMap Λ M (j c)) :
    (W'.baseChange K).baseChange M = (W'.map j).map (algebraMap Λ M) := by
  show W'.map ((algebraMap K M).comp (algebraMap 𝒪 K)) = W'.map ((algebraMap Λ M).comp j)
  congr 1
  exact RingHom.ext hjM

variable {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)
  (hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x)))

theorem map_fieldEvalRed_eq :
    ((W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField).map
      (fieldEvalRed W j hxy hx) = (W'.map j).map (residue Λ) := by
  show W'.map (((fieldEvalRed W j hxy hx).comp (algebraMap (ResidueField 𝒪) _)).comp
    (residue 𝒪)) = W'.map ((residue Λ).comp j)
  congr 1
  refine RingHom.ext fun c => ?_
  simp [fieldEvalRed_algebraMap, ResidueField.map_residue]

variable [W'.IsElliptic]

theorem reducePoint_genEval
    (hjM : ∀ c : 𝒪, algebraMap K M (algebraMap 𝒪 K c) = algebraMap Λ M (j c))
    (hR : ((W.baseChange K).baseChange M).toAffine.Nonsingular (algebraMap Λ M x)
      (algebraMap Λ M y))
    (hRg : IsGenPt (W.baseChange K) (Point.some _ _ hR))
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point) :
    reducePoint M (W'.map j) (pointCongr (map_baseChange_eq_map_of K W' j M hjM)
        (Point.map (genEval (W.baseChange K) _ hRg) Q)) =
      pointCongr (map_fieldEvalRed_eq W W' j hxy hx)
        (pointMapRing (fieldEvalRed W j hxy hx) _ (reduceFF K W W' Q)) := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  set σ := genEval (W.baseChange K) _ hRg
  have hσ : σ.toRingHom.comp (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField) =
      (algebraMap Λ M).comp (gaussLift W j hxy hx) := by
    apply comp_algebraMap_gaussLift
    · intro c
      show σ (algebraMap 𝒪 _ c) = _
      rw [IsScalarTower.algebraMap_apply 𝒪 K, σ.commutes, hjM]
    · exact genEval_genX _ _ hRg
    · exact genEval_genY _ _ hRg
  have c0 : (gaussCurve W W').map (gaussLift W j hxy hx) = W'.map j := by
    show W'.map ((gaussLift W j hxy hx).comp (algebraMap 𝒪 (gaussRing W))) = W'.map j
    exact congrArg W'.map (RingHom.ext (gaussLift_algebraMap_base W j hxy hx))
  set Q₀ := pointCongr (gaussCurve_map_functionField K W W').symm Q with hQ₀
  have hQ : Q = pointCongr (gaussCurve_map_functionField K W W') Q₀ := by
    rw [hQ₀, pointCongr_pointCongr]; rfl
  have key := reducePoint_pointMapRing (W.baseChange K).toAffine.FunctionField M hσ
    (gaussCurve W W') Q₀
  have lhs : pointCongr (map_baseChange_eq_map_of K W' j M hjM) (Point.map σ Q) =
      pointCongr (congrArg (fun V => V.map (algebraMap Λ M)) c0)
        (pointCongr (map_curveK_eq _ M hσ (gaussCurve W W')) (pointMapRing σ.toRingHom _ Q₀)) := by
    rw [map_eq_pointCongr_pointMapRing, hQ, pointMapRing_pointCongr, pointCongr_pointCongr,
      pointCongr_pointCongr, pointCongr_pointCongr]
  rw [lhs, reducePoint_pointCongr, key, pointMapRing_congr (residueField_map_gaussLift W j hxy hx),
    ← pointMapRing_pointMapRing]
  simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
  rw [pointMapRing_pointCongr]
  erw [pointCongr_pointCongr, pointCongr_pointCongr, pointCongr_pointCongr]
  · rfl
  · exact c0

end Eval

end

end GroundTheory.Global
end
