module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle632
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle513
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle633
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_holUnif_pull_along_groupHom : ∀ (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B] (φ : A ⟶ B) (L : LB B.left) (g : ℕ) (u' : HolUnif B L g)
    (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ' : u'.Λ → ℂ),
    (∀ z w, ex (z + w) = ex z * ex w) → Function.Surjective ex → (∀ z, ex z = 1 ↔ z ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (ex z).left U f) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U}) →
    (∀ z, ex z ≫ φ = u'.ex z) → Λ ≤ u'.Λ → u'.IsAH Hm χ' →
    ∃ (u : HolUnif A (L.pull φ.left) g) (χ : u.Λ → ℂ), (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  first | exact @GlobalTheory.PullUnifHom.exists_holUnif_pull_hom | exact GlobalTheory.PullUnifHom.exists_holUnif_pull_hom | (intros; apply GlobalTheory.PullUnifHom.exists_holUnif_pull_hom <;> assumption)
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProdUnifSq

variable {g : ℕ}

def halfL (g : ℕ) : (Fin (g + g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (Fin.castAdd g k)

def halfR (g : ℕ) : (Fin (g + g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (Fin.natAdd g k)

theorem halfL_apply (v : Fin (g + g) → ℂ) : halfL g v = fun k => v (Fin.castAdd g k) := rfl
theorem halfR_apply (v : Fin (g + g) → ℂ) : halfR g v = fun k => v (Fin.natAdd g k) := rfl

theorem halfL_append (x y : Fin g → ℂ) : halfL g (Fin.append x y) = x := by
  funext k; simp [halfL_apply]
theorem halfR_append (x y : Fin g → ℂ) : halfR g (Fin.append x y) = y := by
  funext k; exact Fin.append_right x y k

theorem append_halves (v : Fin (g + g) → ℂ) : Fin.append (halfL g v) (halfR g v) = v := by
  funext q
  refine Fin.addCases (fun k => ?_) (fun k => ?_) q
  · rw [Fin.append_left, halfL_apply]
  · rw [Fin.append_right, halfR_apply]

def sqLat (Λ : Submodule ℤ (Fin g → ℂ)) : Submodule ℤ (Fin (g + g) → ℂ) :=
  Λ.comap ((halfL g).toLinearMap.restrictScalars ℤ) ⊓ Λ.comap ((halfR g).toLinearMap.restrictScalars ℤ)

theorem mem_sqLat (Λ : Submodule ℤ (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    v ∈ sqLat Λ ↔ halfL g v ∈ Λ ∧ halfR g v ∈ Λ := Iff.rfl

theorem sqLat_discrete (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] : DiscreteTopology (sqLat Λ) := by
  refine DiscreteTopology.of_continuous_injective (β := Λ × Λ)
    (f := fun z => (⟨halfL g z.1, z.2.1⟩, ⟨halfR g z.1, z.2.2⟩))
    (Continuous.prodMk (((halfL g).continuous.comp continuous_subtype_val).subtype_mk _)
      (((halfR g).continuous.comp continuous_subtype_val).subtype_mk _)) fun z z' h => ?_
  refine Subtype.ext ?_
  rw [← append_halves z.1, ← append_halves z'.1]
  simp only [Prod.mk.injEq] at h
  have h1 : halfL g z.1 = halfL g z'.1 := congrArg Subtype.val h.1
  have h2 : halfR g z.1 = halfR g z'.1 := congrArg Subtype.val h.2
  rw [h1, h2]

def appendL (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin (g + g) → ℂ) where
  toFun x := Fin.append x 0
  map_add' x y := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]
  map_smul' c x := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]

def appendR (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin (g + g) → ℂ) where
  toFun y := Fin.append 0 y
  map_add' x y := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]
  map_smul' c x := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]

theorem sqLat_full (Λ : Submodule ℤ (Fin g → ℂ)) (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) = ⊤ := by
  have hL : Set.range (appendL g) ⊆ Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) := by
    have : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map (appendL g) ≤ Submodule.span ℝ (sqLat Λ : Set _) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · change halfL g (Fin.append x 0) ∈ Λ
        rw [halfL_append]; exact hx
      · change halfR g (Fin.append x 0) ∈ Λ
        rw [halfR_append]; exact Λ.zero_mem
    rintro _ ⟨x, rfl⟩
    exact this ⟨x, by rw [h]; trivial, rfl⟩
  have hR : Set.range (appendR g) ⊆ Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) := by
    have : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map (appendR g) ≤ Submodule.span ℝ (sqLat Λ : Set _) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · change halfL g (Fin.append 0 x) ∈ Λ
        rw [halfL_append]; exact Λ.zero_mem
      · change halfR g (Fin.append 0 x) ∈ Λ
        rw [halfR_append]; exact hx
    rintro _ ⟨x, rfl⟩
    exact this ⟨x, by rw [h]; trivial, rfl⟩
  refine eq_top_iff.2 fun v _ => ?_
  have hv : v = appendL g (halfL g v) + appendR g (halfR g v) := by
    conv_lhs => rw [← append_halves v]
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [appendL, appendR, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Fin.append_left, Fin.append_right,
        Pi.zero_apply, add_zero, zero_add]
  rw [hv]
  exact Submodule.add_mem _ (hL ⟨_, rfl⟩) (hR ⟨_, rfl⟩)

variable (A : Over (Sp ℂ)) [GrpObj A]

abbrev trivLB (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

def sqUnif {L : LB A.left} (u : HolUnif A L g) : HolUnif (A ⊗ A) (trivLB (A ⊗ A).left) (g + g) where
  ex v := lift (u.ex (halfL g v)) (u.ex (halfR g v))
  ex_add z w := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [MonObj.mul_comp, lift_fst, lift_fst, lift_fst, map_add (f := _), u.ex_add]
    · rw [MonObj.mul_comp, lift_snd, lift_snd, lift_snd, map_add (f := _), u.ex_add]
  ex_onto p := by
    obtain ⟨x, hx⟩ := u.ex_onto (p ≫ fst _ _)
    obtain ⟨y, hy⟩ := u.ex_onto (p ≫ snd _ _)
    refine ⟨Fin.append x y, ?_⟩
    show lift (u.ex (halfL g (Fin.append x y))) (u.ex (halfR g (Fin.append x y))) = p
    rw [halfL_append, halfR_append, hx, hy]
    exact (CartesianMonoidalCategory.hom_ext _ _ (lift_fst _ _) (lift_snd _ _))
  Λ := sqLat u.Λ
  ker z := by
    rw [mem_sqLat, ← u.ker, ← u.ker]
    constructor
    · intro h
      constructor
      · have := congrArg (· ≫ fst A A) h
        simpa only [lift_fst, MonObj.one_comp] using this
      · have := congrArg (· ≫ snd A A) h
        simpa only [lift_snd, MonObj.one_comp] using this
    · rintro ⟨h1, h2⟩
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [lift_fst, MonObj.one_comp, h1]
      · rw [lift_snd, MonObj.one_comp, h2]
  discrete := by
    have := u.discrete
    exact sqLat_discrete u.Λ
  full := sqLat_full u.Λ u.full
  hol := by
    have hd : GlobalTheory.PowUnif.IsHolFamily (fun z => (u.ex z).left) := u.hol
    refine GlobalTheory.PowUnif.isHolFamily_tensor A A _ ?_ ?_
    · simp only [lift_fst]
      exact hd.precomp (halfL g).differentiable
    · simp only [lift_snd]
      exact hd.precomp (halfR g).differentiable
  fr _ _ := 1
  fr_hol _ := differentiableOn_const _
  fr_ne _ _ _ := one_ne_zero
  fr_compat i j z h := by
    rw [Units.val_one, valAt'_one _ h, _root_.one_mul]

end GlobalTheory.ProdUnifSq

end
end

section

open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

theorem _root_.GlobalTheory.T.riemann_relation_converse_conjAffine : ∀ {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ), M₀ᴴ = M₀ → M₀.det ≠ 0 → (Cᵀ * M₀)ᵀ = Cᵀ * M₀ → (1 - C.map star * C).det ≠ 0 → (M₀ * (1 - C.map star * C)⁻¹)ᴴ = M₀ * (1 - C.map star * C)⁻¹ ∧ ∀ z w : Fin g → ℂ, (hermForm (M₀ * (1 - C.map star * C)⁻¹) (z + C *ᵥ star z) (w + C *ᵥ star w)).im = (hermForm M₀ z w).im := by
  first | exact @GlobalTheory.PeriodCoord.riemann_converse | exact GlobalTheory.PeriodCoord.riemann_converse | (intros; apply GlobalTheory.PeriodCoord.riemann_converse; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

theorem _root_.GlobalTheory.T.exists_symplectic_basis_congr_level_mod : ∀ (h k : ℕ) (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (Ef : LinearMap.BilinForm ℤ M) (l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] M), 0 < k → Module.finrank ℤ M = 2 * h → (∀ x, Ef x x = 0) → Function.Bijective Ef → (∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b) → ∃ B : (Fin h ⊕ Fin h → ℤ) ≃ₗ[ℤ] M, (∀ a b, Ef (B a) (B b) = omegaStd a b) ∧ ∀ a, ∃ m : M, l a - B a = (k : ℤ) • m := by
  first | exact @GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr | exact GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr | (intros; apply GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TauNeg

theorem val_tau_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (D.tau (-a) (-b)) (𝟙 _) z J * cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c (-a)) (toUnit (TK R) ≫ D.c b) * (cubV D.cub z J (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c (-b)) (toUnit (TK R) ≫ D.c (-a)))⁻¹ := by
  intro R _ _ D hB a b z J hJ
  have xadd : ∀ u v : D.X, toUnit (TK R) ≫ D.c (u + v) = (toUnit (TK R) ≫ D.c u) * (toUnit (TK R) ≫ D.c v) := by
    intro u v; rw [D.c_add]; exact MonObj.comp_mul _ _ _
  have x0 : toUnit (TK R) ≫ D.c 0 = 1 := by
    have h := xadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have face (x y : TK R ⟶ D.P.A) : cubV D.cub z J 1 x y = 1 := by
    have h := val_corr hJ (D.cub.face 0) (lift x y).left
    rw [val_one] at h
    refine Eq.trans ?_ h
    refine Eq.trans ?_ (val_cub D.cub (lift x y) hJ (pzero D.P.A _) (x2 D.P.A 0) (x2 D.P.A 1)).symm
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have B : ∀ u u' w v : D.X, u + u' = w → val (D.tau w v) (𝟙 _) z J *
      cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v) =
      val (D.tau u v) (𝟙 _) z J * val (D.tau u' v) (𝟙 _) z J := by
    rintro u u' w v rfl
    have h := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB u u' v) (𝟙 _)).trans (val_mul hJ _ _ _))
    have hc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 u u' v)) (𝟙 _) z J =
        cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v) := by
      refine (val_cub D.cub (𝟙 (TK R)) hJ _ _ _).trans ?_
      rw [Category.id_comp, Category.id_comp, Category.id_comp]
    rw [← hc]
    exact h
  have sym : ∀ u v : D.X, val (D.tau u v) (𝟙 _) z J = val (D.tau v u) (𝟙 _) z J := by
    intro u v
    simp only [DegPre.tau, val_mul hJ, val_inv]
    rw [add_comm u v, mul_right_comm (val (D.psi (v + u)) (𝟙 _) z J)]
  have T0 : ∀ v : D.X, val (D.tau 0 v) (𝟙 _) z J = 1 := by
    intro v
    have h := B 0 v v v (zero_add v)
    rw [x0, face, _root_.mul_one] at h
    exact (mul_eq_right.1 h.symm)
  have e1 := B a (-a) 0 b (add_neg_cancel a)
  have e2 := B b (-b) 0 (-a) (add_neg_cancel b)
  rw [T0, _root_.one_mul] at e1 e2
  rw [e1, e2, sym b (-a), sym (-b) (-a)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TauNeg
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RegCoverExists

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
private theorem isSeparated_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c) := by
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
    show IsAffine (Spec (CommRingCat.of R)); infer_instance
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R') := by
    show IsAffine (Spec (CommRingCat.of R')); infer_instance
  infer_instance


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
theorem _root_.GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    {Y : Scheme.{0}} {f : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (f ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f := by
  obtain ⟨N, i, hi, hif⟩ := h
  have hP := _root_.GlobalTheory.ProjSpace.isPullback_baseChange N c
  haveI := isSeparated_spMap c
  haveI : IsSeparated (_root_.GlobalTheory.ProjSpace.baseChange N c) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  refine ⟨N, hP.lift i f hif, ?_, hP.lift_snd _ _ _⟩
  haveI : IsClosedImmersion (hP.lift i f hif ≫ _root_.GlobalTheory.ProjSpace.baseChange N c) := by
    rw [hP.lift_fst]; exact hi
  exact IsClosedImmersion.of_comp _ (_root_.GlobalTheory.ProjSpace.baseChange N c)

end GlobalTheory.RegCoverExists

end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

namespace GlobalTheory.FieldDimCoheight

theorem coheight_add_dim_closure_eq (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp F) [LocallyOfFiniteType p] (z : X) :
    (Order.coheight z : WithBot ℕ∞) + topologicalKrullDim (closure ({z} : Set X)) =
      topologicalKrullDim X := by
  refine le_antisymm ?_ ?_
  · rw [add_comm]
    haveI : QuasiSober (closure ({z} : Set X)) :=
      isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
    exact DimCodim.dim_add_le_of_le_coheight continuous_subtype_val Subtype.val_injective _
      fun w => Order.coheight_anti (specializes_iff_mem_closure.2 w.2)
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hne : Nonempty U := ⟨⟨z, hzU⟩⟩
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(X, U), hU.fromSpec P = z := by
    have : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hzU
    exact this
  let φ := Spec.preimage (hU.fromSpec ≫ p)
  have hφ : Spec.map φ = hU.fromSpec ≫ p := Spec.map_preimage _
  let _ : Algebra F Γ(X, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have : Nonempty (Spec Γ(X, U)) := ⟨P⟩
  have hA : ringKrullDim Γ(X, U) = topologicalKrullDim X := by
    rw [← OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion F X _ p hU.fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
  have h2 := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F) P.asIdeal
  let x : Spec Γ(X, U) := P
  have eS := (asIso (hU.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(X, U) x).commRingCatIsoToRingEquiv
  have hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight z := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight]
    rw [← hP]
  have h3 : ringKrullDim (Γ(X, U) ⧸ P.asIdeal) ≤ topologicalKrullDim (closure ({z} : Set X)) := by
    rw [← topologicalKrullDim_range_inter_closure_eq (B := Γ(X, U)) hU.fromSpec P, hP]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [← hA, ← h2, hPh]
  exact add_le_add le_rfl h3

theorem eq_one_iff_of_add_eq {c : ℕ∞} {t : WithBot ℕ∞} {e : ℕ}
    (h : (c : WithBot ℕ∞) + t = (e + 1 : ℕ)) : c = 1 ↔ t = e := by
  induction t using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at h; exact absurd h.symm (WithBot.natCast_ne_bot _)
  | coe t =>
    have h' : c + t = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
    have hc : c ≠ ⊤ := by rintro rfl; rw [top_add] at h'; exact ENat.natCast_ne_top _ h'.symm
    have ht : t ≠ ⊤ := by rintro rfl; rw [add_top] at h'; exact ENat.natCast_ne_top _ h'.symm
    lift c to ℕ using hc
    lift t to ℕ using ht
    have h'' : c + t = e + 1 := by exact_mod_cast h'
    constructor
    · intro h1
      have : c = 1 := by exact_mod_cast h1
      have : t = e := by omega
      exact_mod_cast this
    · intro h1
      have : t = e := by exact_mod_cast h1
      have : c = 1 := by omega
      exact_mod_cast this

theorem coheight_eq_one_iff : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F)
    (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ z : X,
    Order.coheight z = 1 ↔ topologicalKrullDim (closure ({z} : Set X)) = e := by
  intro F _ X _ p e hp hd z
  have : IsProper p := by
    obtain ⟨N, c, hc, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  exact eq_one_iff_of_add_eq ((coheight_add_dim_closure_eq F X p z).trans hd)

end GlobalTheory.FieldDimCoheight
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U := by
  first | exact @GlobalTheory.SqZeroBC.preimage_surj | exact GlobalTheory.SqZeroBC.preimage_surj | (intros; apply GlobalTheory.SqZeroBC.preimage_surj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_endomorphism_finite_of_geometric_fibres : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (φ : A ⟶ A),
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), IsFinite ((Over.pullback t).map φ).left) →
    IsFinite φ.left := by
  first | (exact @GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres) | (exact GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres) | (intros; apply GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_baseUnit_rigidifiedGenericGenerator : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → ∀ (eA : Sp K ⟶ pullback X.hom (spMap (algebraMap R K))), eA ≫ pullback.fst X.hom (spMap (algebraMap R K)) = spMap (algebraMap R K) ≫ e → ∀ (M : LB X.left) (rig : LB.Gen (M.pull e)) (c : LB.Gen (M.pull (pullback.fst X.hom (spMap (algebraMap R K))))), M.IsLB → rig.IsGen → LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ c eA) (LB.pullGen M _ _ rig (spMap (algebraMap R K))) → ∀ (a : Kˣ) (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ pullback X.hom (spMap (algebraMap R K))) (z : Z), pullback.fst X.hom (spMap (algebraMap R K)) (r z) ∈ M.U i → (gm (r ≫ pullback.fst X.hom (spMap (algebraMap R K))) z (M.U i) (u.s i)).val = gs (r ≫ pullback.snd X.hom (spMap (algebraMap R K))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull (pullback.fst X.hom (spMap (algebraMap R K)))).U fun _ => i) (c.s fun _ => i)).val) → ∃ b : Rˣ, algebraMap R K (b : R) = (a : K) := by
  first | exact @GlobalTheory.rigUnit_exists | exact GlobalTheory.rigUnit_exists | (intros; apply GlobalTheory.rigUnit_exists <;> assumption)
end
