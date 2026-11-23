module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LetterEigen

theorem prod_ofFn_eq_single {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (u : Fin n → M) (i : Fin n), (∀ j, j ≠ i → u j = 1) → (List.ofFn u).prod = u i
  | 0, _, i, _ => i.elim0
  | n + 1, u, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases (motive := fun i => (∀ j, j ≠ i → u j = 1) →
      u 0 * (List.ofFn fun k : Fin n => u k.succ).prod = u i) (fun h => ?_) (fun i h => ?_) i h
    · have hprod : (List.ofFn fun k : Fin n => u k.succ).prod = 1 :=
        List.prod_eq_one (List.forall_mem_ofFn_iff.mpr fun k => h _ (Fin.succ_ne_zero k))
      rw [hprod, _root_.mul_one]
    · rw [h 0 (Fin.succ_ne_zero i).symm, _root_.one_mul]
      exact prod_ofFn_eq_single (fun k : Fin n => u k.succ) i
        (fun j hj => h _ (fun e => hj (Fin.succ_injective _ e)))

theorem left_eq_of_isLieComb_single {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
    {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (i : Fin n) (t : R) {w : epsR R ⟶ G}
    (hw : IsLieComb (Pi.single i t) v w) : w.left = spMap (epsScaleR t) ≫ (v i).left := by
  obtain ⟨u, hu, rfl⟩ := hw
  rw [prod_ofFn_eq_single u i, hu i, Pi.single_eq_same]
  intro j hj
  have h0 := (LieMultiple.isLieComb_one_iff (0 : R) (v j) 1).1
    ((LieMultiple.lieMultiple_calculus R G G (v j) 1 1 0 0).2.2.2.2.2 (hv j))
  apply Over.OverMorphism.ext
  rw [hu j, Pi.single_eq_of_ne hj, h0]

theorem exists_scale_of_eigen {K : Type} [Field K] [NumberField K] {A B : Over (Sp (𝓞 K))} {A' B' : Over (Sp K)}
    [GrpObj A'] [GrpObj B'] {n : ℕ} {v : Fin n → (epsR K ⟶ A')} (hv : ∀ i, IsTangent (v i)) (i : Fin n) (t : K)
    (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (α : A ⟶ A) (β : B ⟶ B) (F : A ⟶ B) (hF : α ≫ F = F ≫ β)
    {w₁ : epsR K ⟶ A'} (hw₁ : IsLieComb (Pi.single i t) v w₁) (he : (v i).left ≫ φA ≫ α.left = w₁.left ≫ φA)
    {w : epsR K ⟶ B'} (hw : w.left ≫ φB = (v i).left ≫ φA ≫ F.left) :
    ∃ w' : epsR K ⟶ B', IsLieComb ![t] ![w] w' ∧ w.left ≫ φB ≫ β.left = w'.left ≫ φB := by
  have hc : IsLieComb ![t] ![w] (Chart.spMap (Chart.scaleD t) ≫ w) :=
    (LieMultiple.isLieComb_one_iff_comp t w _).2 rfl
  refine ⟨_, hc, ?_⟩
  have hF' : α.left ≫ F.left = F.left ≫ β.left := by
    rw [← Over.comp_left, hF, Over.comp_left]
  rw [(LieMultiple.isLieComb_one_iff t w _).1 hc, Category.assoc, hw, reassoc_of% hw, ← hF', reassoc_of% he,
    left_eq_of_isLieComb_single hv i t hw₁, Category.assoc]

theorem letter_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (b : E →+* ℂ) (i : Fin (L.m b)) (w : epsR o.K₁ ⟶ o.xB.P.A), L.IsLetter (L.e ⟨b, i⟩) w → ∀ a : 𝓞 E, ∃ w' : epsR o.K₁ ⟶ o.xB.P.A, IsLieComb ![labK c o.K₁ b (a : E)] ![w] w' ∧ w.left ≫ o.φB ≫ (o.oa.act a).left = w'.left ≫ o.φB := by
  intro E _ _ _ _ H l c nΨ n' f o La ho L hL b i w hw a
  obtain ⟨-, -, -, -, -, -, -, -, -, hΨ, h', eΨ, e', -⟩ := ho
  have hb := hL.2.1 b i
  unfold LamLetters.IsLetter at hw
  generalize L.src (L.e ⟨b, i⟩) = s at hb hw
  rcases s with q | q
  · obtain ⟨w₁, h₁, h₂⟩ := hΨ a q.2
    obtain ⟨rfl, -⟩ := hb
    exact exists_scale_of_eigen o.xΨ.basis.1 q.2 _ _ _ _ _ _ (eΨ q.1 a) h₁ h₂ hw
  · obtain ⟨w₁, h₁, h₂⟩ := h' a q.2
    obtain ⟨rfl, -⟩ := hb
    exact exists_scale_of_eigen o.x'.basis.1 q.2 _ _ _ _ _ _ (e' q.1 a) h₁ h₂ hw

end GlobalTheory.LamF.LetterEigen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem points_sums_eq_products : (∀ (S : Scheme.{0}) (G T : Over S) [GrpObj G], (toUnit T ≫ η[G] = (1 : T ⟶ G)) ∧ (∀ a b : T ⟶ G, padd G a b = a * b) ∧ (∀ (n : ℕ) (a : T ⟶ G), pnsmulPt n a = a ^ n) ∧ ∀ (n : ℕ) (f : Fin n → (T ⟶ G)), psumPt f = (List.ofFn f).prod) ∧ ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R'), Formalism.L2.Pj.dualMap f = Chart.dualMapR f := by
  refine ⟨fun S G T _ => ⟨rfl, fun _ _ => rfl, fun n a => ?_, fun n f => ?_⟩, fun _ _ _ _ _ => rfl⟩
  · induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih =>
      rw [pow_succ, ← ih]; rfl
  · rw [List.prod_eq_foldr]; rfl

end GlobalTheory.LamF
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem traceForm_integral_perfect_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ k, (∀ x ∈ (U.X k).Λ, ∀ y ∈ (U.X k).Λ, ∃ n : ℤ, EFf (U.X k).ξ0 (U.X k).Gm x y = n) ∧ ∀ φ : (U.X k).Λ →+ ℤ, ∃ x ∈ (U.X k).Λ, ∀ y : (U.X k).Λ, (φ y : ℚ) = EFf (U.X k).ξ0 (U.X k).Gm x y := by
  intro E _ _ _ H Dw l Xo c σ r U hU k
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hφ, -⟩ := hU
  refine ⟨fun x hx y hy => ?_, fun ψ => ?_⟩
  · refine ⟨(F.Di (ik k)).EF ((φ k).symm ⟨x, hx⟩) ((φ k).symm ⟨y, hy⟩), ?_⟩
    rw [hφ k]
    simp only [LinearEquiv.apply_symm_apply, EFf]
  · obtain ⟨a, ha⟩ := (F.Di (ik k)).unimod.2
      (ψ.comp (φ k).toLinearMap.toAddMonoidHom).toIntLinearMap
    refine ⟨φ k a, (φ k a).2, fun y => ?_⟩
    have h := hφ k a ((φ k).symm y)
    rw [ha] at h
    simpa [EFf] using h

end GlobalTheory
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HomLinear

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}


omit [GrpObj A] [GrpObj A'] in
theorem valAt'_comp_left (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (f : A ⟶ A') (U : A'.left.Opens) (s : Γ(A'.left, U)) :
    valAt' (x ≫ f).left U s = valAt' x.left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) :=
  (valAt'_comp x.left f.left U s).symm


omit [GrpObj A'] in
theorem isHolTo_ex_comp (u : HolUnif A L g) (f : A ⟶ A') :
    IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (u.ex z ≫ f).left) := by
  intro U s
  have hset : {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (u.ex w ≫ f).left ⁻¹ᵁ U} =
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (f.left ⁻¹ᵁ U)} := by
    ext w
    simp
  have hfun : (fun w => valAt' (u.ex w ≫ f).left U s) =
      fun w => valAt' (u.ex w).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) :=
    funext fun w => valAt'_comp_left _ f U s
  rw [hset, hfun]
  exact u.hol _ _

theorem isTangent_comp {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f]
    {v : epsR R ⟶ G} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem top_le_ex_zero (u : HolUnif A L g) {v : epsR ℂ ⟶ A} (hv : IsTangent v) (U : A.left.Opens)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
  have h0 : u.ex 0 = η[A] := by
    rw [(u.ker 0).mpr u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  rw [h0, ← hv]
  intro a _
  exact h (Set.mem_univ _)

theorem isDiff_comp (u : HolUnif A L g) (u' : HolUnif A' L' g') (f : A ⟶ A') [IsMonHom f]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z ≫ f) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hd : u.IsDiff w v) : u'.IsDiff (F w) (v ≫ f) := by
  intro U h s
  have h1 := hd (f.left ⁻¹ᵁ U) h ((f.left.app U).hom s)
  have e : ((v ≫ f).left.appLE U ⊤ h).hom s =
      (v.left.appLE (f.left ⁻¹ᵁ U) ⊤ h).hom ((f.left.app U).hom s) := by
    have := Scheme.Hom.comp_appLE v.left f.left U ⊤ h
    exact congrArg (fun φ => φ.hom s) this
  have hdiff : DifferentiableAt ℂ (fun z => valAt' (u'.ex z).left U s) 0 :=
    (u'.hol U s).2.differentiableAt ((u'.hol U s).1.mem_nhds (top_le_ex_zero u' (isTangent_comp f hv) U h))
  have hfun : (fun z => valAt' (u.ex z).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)) =
      (fun z => valAt' (u'.ex z).left U s) ∘ LinearMap.toContinuousLinearMap F := by
    funext z
    rw [← valAt'_comp_left, ← hF]
    rfl
  have hch := (HasFDerivAt.comp (0 : Fin g → ℂ) (f := LinearMap.toContinuousLinearMap F)
    (by rw [map_zero]; exact hdiff.hasFDerivAt) (LinearMap.toContinuousLinearMap F).hasFDerivAt).fderiv
  rw [hfun, hch] at h1
  rw [e]
  exact h1

theorem exists_linear_of_isMonHom :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' →
  ∀ (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g'),
  (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u'.IsDiff w v) →
  ∀ f : A ⟶ A', IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), (∀ z, u'.ex (F z) = u.ex z ≫ f) ∧
    (∀ l ∈ u.Λ, F l ∈ u'.Λ) ∧ (∀ w v, IsTangent v → u.IsDiff w v → IsTangent (v ≫ f) ∧ u'.IsDiff (F w) (v ≫ f)) ∧
    ∀ f' : A ⟶ A', (∀ z, u'.ex (F z) = u.ex z ≫ f') → f' = f := by
  intro A A' _ _ hA hA' L L' g g' u u' h1 h2 f hf
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.existsUnique_linearLift_of_holomorphic_abelianVariety A' hA' L' g' g u' h1 h2 (fun z => u.ex z ≫ f)
    (fun z w => by simp only [u.ex_add]; exact MonObj.mul_comp _ _ f) (isHolTo_ex_comp u f)
  refine ⟨F, hF, fun l hl => ?_, fun w v hv hd => ⟨isTangent_comp f hv, isDiff_comp u u' f F hF hv hd⟩,
    fun f' hf' => ?_⟩
  · rw [← u'.ker, hF, (u.ker l).mpr hl]
    exact MonObj.one_comp f
  · have hs : Smooth A.hom := hA.smooth
    have hp : IsProper A'.hom := hA'.proper
    have hr : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hs
    refine ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨z, rfl⟩ := u.ex_onto x
    rw [← hf', hF]

end GlobalTheory.HomLinear
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem appLE_top_eq_zero_iff_gs {X Z : Scheme.{0}} (r : Z ⟶ X) (U : X.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (a : Γ(X, U)) :
    (r.appLE U ⊤ h).hom a = 0 ↔ ∀ z, gs r z U a = 0 := by
  have e : ∀ z, gs (𝟙 Z) z ⊤ ((r.appLE U ⊤ h).hom a) = gs r z U a := fun z =>
    (gs_appLE r U ⊤ h (𝟙 Z) z trivial a).trans (by rw [Category.id_comp])
  have e0 : ∀ z : Z, gs (𝟙 Z) z ⊤ 0 = 0 := fun z => by
    rw [gs_eq (𝟙 Z) z ⊤ trivial, map_zero, map_zero]
  exact ⟨fun H z => by rw [← e z, H, e0], fun H => fn_ext fun z _ => by rw [e z, H z, e0]⟩

theorem exists_pull_sec_sval {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (F : Y ⟶ X) :
    ∃ s : (L.pull F).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s r z J = gs (r ≫ F) z (L.U (J (r ≫ F))) (θ.f (J (r ≫ F))) := by
  have le : ∀ J, (L.pull F).U J ≤ F ⁻¹ᵁ L.U (J PUnit.unit) := fun J => LB.wchart_le L _ J PUnit.unit
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) z J, r z ∈ (L.pull F).U J →
      gs r z _ ((F.appLE _ _ (le J)).hom (θ.f _)) = gs (r ≫ F) z _ (θ.f (J PUnit.unit)) :=
    fun Z r z J h => gs_appLE F _ _ (le J) r z h _
  refine ⟨⟨fun J => (F.appLE _ _ (le J)).hom (θ.f _), fun J J' => fn_ext fun y hy => ?_⟩,
    fun Z r z J hJ => ev Z r z _ (hJ.mem _ r)⟩
  have hm : (𝟙 Y ≫ F) y ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨le J hy.1, le J' hy.2⟩
  have e := congrArg (gs (𝟙 Y ≫ F) y _) (θ.compat (J PUnit.unit) (J' PUnit.unit))
  rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm] at e
  refine ((gs_res (𝟙 Y) y _ hy _).trans ((ev _ _ y J hy.1).trans e)).trans
    (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y J J' hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans (ev _ _ y J' hy.2)))).symm)
  simp

theorem exists_sec_of_gen_diff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (θ : L.Sec) (ψ φ : Y ⟶ X)
    (d : LB.Gen (LB.LinComb L (K := Fin 2) ![ψ, φ] ![1, -1])) (hd : d.IsGen) :
    ∃ s : (L.pull φ).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s r z J = 0 → gs (r ≫ ψ) z (L.U (J (r ≫ ψ))) (θ.f (J (r ≫ ψ))) = 0 := by
  obtain ⟨s₀, hs₀⟩ := exists_pull_sec_sval θ ψ
  have hF : FormEq (Sum.elim (fun _ : PUnit => 𝟙 Y ≫ ψ) ![ψ, φ])
      (Sum.elim (fun _ => 1) (fun k => -(![1, -1] : Fin 2 → ℤ) k)) (fun _ : PUnit => φ) (fun _ => 1) := by
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two]
  obtain ⟨s, hs⟩ := exists_sec hL hF (pullMulSec s₀ (𝟙 Y) (LB.invGen L _ _ d) (LB.isGen_invGen L _ _ d hd))
  refine ⟨s, fun Z r z J hJ H => ?_⟩
  rw [hs Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, Category.comp_id, hs₀ Z r z J hJ] at H
  exact (Units.mul_left_eq_zero _).1 H

theorem kTriv_of_sections_vanish_on_zero : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ eSec A) → (∀ (R' : Type) [CommRing R'] (f : Sp R' ⟶ S) (Y : Scheme.{0}) (φ : Y ⟶ A.left) (q : Y ⟶ Sp R'), IsPullback φ q A.hom f → ∀ (s : (L.pull φ).Sec) (T : Scheme.{0}) (t : T ⟶ Y) (j : (L.pull φ).ι) (h : ⊤ ≤ t ⁻¹ᵁ (L.pull φ).U j), t ≫ φ = t ≫ φ ≫ A.hom ≫ eSec A → (t.appLE ((L.pull φ).U j) ⊤ h).hom (s.f j) = 0) → Out.KTriv A L := by
  intro S A _ L θ hL hθ hs R _ t x hx
  have one : ∀ (T : Over S) (y : T ⟶ A), y.left ≫ A.hom ≫ eSec A = (1 : T ⟶ A).left := fun T y => by
    rw [← Category.assoc, Over.w y]; rfl
  have H' : ∀ (R' : CommRingCat.{0}) (t' : Spec R' ⟶ S) (y : Over.mk t' ⟶ A) (i i₀ : L.ι),
      ⊤ ≤ y.left ⁻¹ᵁ L.U i → ⊤ ≤ (1 : Over.mk t' ⟶ A).left ⁻¹ᵁ L.U i₀ →
      (∃ c : LB.Gen (Out.translDiff A L y), c.IsGen) → y = 1 := by
    rintro R' t' y i i₀ hi hi₀ ⟨c, hc⟩
    by_contra hne
    have hne' : y.left ≠ (1 : Over.mk t' ⟶ A).left := fun e => hne (Over.OverMorphism.ext e)
    obtain ⟨s, hs'⟩ := exists_sec_of_gen_diff hL θ _ _ c hc
    let r : Over.mk t' ⟶ Over.mk t' ⊗ A := lift (𝟙 _) 1
    have r₁ : r.left ≫ (lift (fst _ A ≫ y) (snd _ A) ≫ μ[A]).left = y.left := by
      rw [← Over.comp_left, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp]
      exact congrArg (fun q : Over.mk t' ⟶ A => q.left) (_root_.mul_one y)
    have r₂ : r.left ≫ (snd _ A).left = (1 : Over.mk t' ⟶ A).left := by
      rw [← Over.comp_left, lift_snd]
    have hj : ⊤ ≤ r.left ⁻¹ᵁ (L.pull (snd (Over.mk t') A).left).U (fun _ => i₀) := fun z _ =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q z ∈ L.U i₀) r₂).mpr (hi₀ trivial)
    have hz := hs R' t' _ (snd (Over.mk t') A).left (fst (Over.mk t') A).left
      (IsPullback.of_hasPullback t' A.hom).flip s _ r.left (fun _ => i₀) hj
      (by rw [← Category.assoc, r₂, one])
    refine hne' (((hθ _ y.left i hi).1 ((appLE_top_eq_zero_iff_gs _ _ hi _).2 fun z => ?_)).trans (one _ y))
    obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Bool)
      (fun b => cond b y.left (1 : Over.mk t' ⟶ A).left) (fun b => cond b i i₀) (by
        rintro (_ | _) (_ | _) e
        exacts [rfl, absurd e.symm hne', absurd e hne', rfl]) (by
        rintro (_ | _)
        exacts [hi₀ trivial, hi trivial])
    have := hs' _ r.left z J hJ ((sval_of s r.left z J (fun _ => i₀) (fun _ => by rw [r₂]; exact e false)).trans
      ((appLE_top_eq_zero_iff_gs _ _ hj _).1 hz z))
    rw [r₁] at this
    obtain rfl : J y.left = i := e true
    exact this
  change x = 1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨V, hp, c, hc⟩ := hx p
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((1 : Over.mk t ⟶ A).left p)
  obtain ⟨U, hU, hpU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (U := V ⊓ x.left ⁻¹ᵁ L.U i ⊓ (1 : Over.mk t ⟶ A).left ⁻¹ᵁ L.U i₀) (x := p) ⟨⟨hp, hi⟩, hi₀⟩
  refine ⟨U, hpU, ?_⟩
  let g : Over.mk (hU.fromSpec ≫ t) ⟶ Over.mk t := Over.homMk hU.fromSpec rfl
  have hq := fun q => hUV (hU.range_fromSpec.le ⟨q, rfl⟩)
  have h1 : g ≫ x = g ≫ 1 := by
    rw [MonObj.comp_one]
    refine H' _ _ _ i i₀ (fun q _ => (hq q).1.2) ?_ (exists_isGen_translDiff_comp A L x g V
      (fun q => (hq q).1.1) c hc)
    rw [← MonObj.comp_one g]
    exact fun q _ => (hq q).2
  have h2 : hU.fromSpec ≫ x.left = hU.fromSpec ≫ (1 : Over.mk t ⟶ A).left :=
    congrArg (·.left) h1
  rw [IsAffineOpen.fromSpec, Category.assoc, Category.assoc, cancel_epi] at h2
  exact h2

end GlobalTheory
end
