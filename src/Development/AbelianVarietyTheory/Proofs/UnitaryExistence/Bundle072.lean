module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle070
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle066
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle016
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle050
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase

@[expose] public section

section

set_option autoImplicit false

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.ArithImage

open GlobalTheory.PeterssonCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem frameOf_one : frameOf X 1 = baseFr X := by
  funext τ
  show mat (frameOf X 1) τ = mat (baseFr X) τ
  rw [mat_frameOf]
  simp

theorem lact_one_fr (y : Frame X.Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y τ
  simp

theorem lact_mul_fr (a b : GL (Fin r) E) (y : Frame X.Ψ r) : lact (a * b) y = lact a (lact b y) := by
  funext τ
  show ((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ =
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

def image : Subgroup (RealGrp X) where
  carrier := {s | ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s}
  one_mem' := ⟨1, X.Γ.one_mem, by rw [lact_one_fr, frameOf_one]⟩
  mul_mem' := by
    rintro s t ⟨γ, hγ, e⟩ ⟨δ, hδ, f⟩
    exact ⟨γ * δ, X.Γ.mul_mem hγ hδ, by rw [lact_mul_fr, f, lact_frameOf X e]⟩
  inv_mem' := by
    rintro s ⟨γ, hγ, e⟩
    refine ⟨γ⁻¹, X.Γ.inv_mem hγ, ?_⟩
    have h := lact_frameOf X e s⁻¹
    rw [mul_inv_cancel, frameOf_one] at h
    rw [← h, ← lact_mul_fr, inv_mul_cancel, lact_one_fr]

def smallSet : Set (RealGrp X) :=
  {s | ∀ (τ : X.Ψ) (a b : Fin r), ‖(mat (frameOf X s) τ * (mat (baseFr X) τ)⁻¹) a b‖ < 2}

theorem isOpen_smallSet : IsOpen (smallSet X) := by
  unfold smallSet
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
  refine isOpen_lt (Continuous.norm ?_) continuous_const
  have h : Continuous fun s : RealGrp X =>
      mat (baseFr X) τ * ((s τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat (baseFr X) τ)⁻¹ :=
    (continuous_const.matrix_mul (Units.continuous_val.comp
      (continuous_subtype_val.comp (continuous_apply τ)))).matrix_mul continuous_const
  exact h.matrix_elem a b

theorem one_mem_smallSet : (1 : RealGrp X) ∈ smallSet X := by
  intro τ a b
  rw [frameOf_one, Matrix.mul_nonsing_inv _ (det_baseFr X τ).isUnit, Matrix.one_apply]
  split_ifs <;> simp

theorem finite_image_inter : ((image X : Set (RealGrp X)) ∩ smallSet X).Finite := by
  refine Set.Finite.of_finite_image (f := frameOf X) ?_ (frameOf_injective X).injOn
  refine (((GlobalTheory.LatFin.latFin (E := E)).2 r X 2).image fun γ => lact γ (baseFr X)).subset ?_
  rintro _ ⟨s, ⟨⟨γ, hγ, e⟩, hs⟩, rfl⟩
  refine ⟨γ, ⟨X.Γ_stab γ hγ, fun τ a b => ?_⟩, e⟩
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (baseFr X) τ = mat (frameOf X s) τ := congrFun e τ
  have h2 := hs τ a b
  rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ (det_baseFr X τ).isUnit] at h2
  exact h2.le

theorem exists_discrete_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∃ Λ : Subgroup (RealGrp X), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) ∧ ∃ W ∈ 𝓝 (1 : RealGrp X), ∀ w ∈ Λ, w ∈ W → w = 1 := by
  intro E _ _ _ r X
  refine ⟨image X, fun _ => Iff.rfl, smallSet X \ (((image X : Set (RealGrp X)) ∩ smallSet X) \ {1}), ?_, ?_⟩
  · exact ((isOpen_smallSet X).sdiff ((finite_image_inter X).subset Set.diff_subset).isClosed).mem_nhds
      ⟨one_mem_smallSet X, fun h => h.2 rfl⟩
  · intro w hw hW
    by_contra hne
    exact hW.2 ⟨⟨hw, hW.1⟩, hne⟩

end GlobalTheory.ArithImage
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.CubeGlue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem triv_of_triv_pull_id {P : Scheme.{0}} {M : LB P} (h : Triv (M.pull (𝟙 P))) : Triv M := by
  obtain ⟨u, hu⟩ := h
  have le : ∀ i, M.U i ≤ (M.pull (𝟙 P)).U (fun _ => i) := fun i y hy => mem_pull.2 hy
  refine ⟨⟨fun i => res (le i) (u.s fun _ => i)⟩, fun i j => unit_ext fun y hy => ?_⟩
  have c := gen_trans hu (𝟙 P) y (le i hy.1) (le j hy.2)
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp] at c
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (c.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))

theorem exists_section {P Z : Scheme.{0}} (p : P ⟶ Z) (e : Z ⟶ P) (he : e ≫ p = 𝟙 Z) (V : Z.Opens) :
    ∃ s : V.toScheme ⟶ (p ⁻¹ᵁ V).toScheme, s ≫ (p ⁻¹ᵁ V).ι = V.ι ≫ e ∧ s ≫ (p ∣_ V) = 𝟙 _ := by
  obtain ⟨s, hs⟩ : ∃ s : V.toScheme ⟶ (p ⁻¹ᵁ V).toScheme, s ≫ (p ⁻¹ᵁ V).ι = V.ι ≫ e :=
    ⟨IsOpenImmersion.lift _ (V.ι ≫ e) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (· ∈ V) (congrArg (fun m => m q.1) he)).mpr q.2), IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨s, hs, ?_⟩
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hs, Category.assoc, he,
    Category.id_comp, Category.comp_id]

theorem exists_normalised {P Z : Scheme.{0}} {M : LB P} (hM : M.IsLB) (p : P ⟶ Z) (e : Z ⟶ P) (he : e ≫ p = 𝟙 Z)
    (g : LB.Gen (M.pull e)) (hg : g.IsGen) (V : Z.Opens) (h : Triv (M.pull (p ⁻¹ᵁ V).ι)) :
    ∃ t : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => (p ⁻¹ᵁ V).ι ≫ 𝟙 P) (fun _ => 1)), t.IsGen ∧
      ∀ (T : Scheme.{0}) (r : T ⟶ (p ⁻¹ᵁ V).toScheme) (b : T ⟶ Z) (z : T) (J), Good M z J →
        r ≫ (p ⁻¹ᵁ V).ι = b ≫ e → val t r z J = val g b z J := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨s, hs, -⟩ := exists_section p e he V
  have n₁ : ((p ∣_ V) ≫ s) ≫ (p ⁻¹ᵁ V).ι = ((p ⁻¹ᵁ V).ι ≫ p) ≫ e := by
    rw [Category.assoc, hs, ← Category.assoc, morphismRestrict_ι]
  obtain ⟨t', ht', hv⟩ := exists_gen hM (K' := PUnit) (φ' := fun _ => (p ⁻¹ᵁ V).ι ≫ 𝟙 P) (ε' := fun _ => 1)
    (fun U _ k => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, n₁, Category.comp_id]
      simp)
    (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ t (LB.invGen M _ _ (LB.pullGen M _ _ t ((p ∣_ V) ≫ s))))
      (LB.pullGen M _ _ g ((p ⁻¹ᵁ V).ι ≫ p)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hg _))
  refine ⟨t', ht', fun T r b z J hJ hr => ?_⟩
  have hb : r ≫ (p ⁻¹ᵁ V).ι ≫ p = b := by
    rw [← Category.assoc, hr, Category.assoc, he, Category.comp_id]
  have : r ≫ (p ∣_ V) ≫ s = r := by
    rw [← cancel_mono (p ⁻¹ᵁ V).ι, Category.assoc, n₁, ← Category.assoc, hb, hr]
  rw [hv T r z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, this, mul_inv_cancel, hb,
    _root_.one_mul]

theorem triv_of_locally_triv {P Z : Scheme.{0}} {M : LB P} (hM : M.IsLB) (p : P ⟶ Z) (e : Z ⟶ P)
    (he : e ≫ p = 𝟙 Z) (hp : ∀ V : Z.Opens, Function.Surjective (p ∣_ V).appTop.hom) (h₀ : Triv (M.pull e))
    (loc : ∀ z : Z, ∃ V : Z.Opens, z ∈ V ∧ Triv (M.pull (p ⁻¹ᵁ V).ι)) : Triv M := by
  obtain ⟨g, hg⟩ := h₀
  choose U hU hT using loc
  choose t ht hn using fun z => exists_normalised hM p e he g hg (U z) (hT z)
  obtain ⟨u, hu, -⟩ := glue_gen hM (K := PUnit) (fun _ => 𝟙 P) (fun _ => 1) (fun s => p ⁻¹ᵁ U s)
    (fun y => ⟨p y, hU _⟩) t ht (by
      intro s s' T r r' z J hJ hr
      obtain ⟨σ, hσ, hσ'⟩ := exists_section p e he (U s ⊓ U s')
      let m := P.homOfLE (show p ⁻¹ᵁ (U s ⊓ U s') ≤ p ⁻¹ᵁ U s from fun _ hy => hy.1)
      let m' := P.homOfLE (show p ⁻¹ᵁ (U s ⊓ U s') ≤ p ⁻¹ᵁ U s' from fun _ hy => hy.2)
      have hm : m ≫ (p ⁻¹ᵁ U s).ι = (p ⁻¹ᵁ (U s ⊓ U s')).ι := P.homOfLE_ι _
      have hm' : m' ≫ (p ⁻¹ᵁ U s').ι = (p ⁻¹ᵁ (U s ⊓ U s')).ι := P.homOfLE_ι _
      obtain ⟨ρ, hρ⟩ : ∃ ρ : T ⟶ (p ⁻¹ᵁ (U s ⊓ U s')).toScheme, ρ ≫ (p ⁻¹ᵁ (U s ⊓ U s')).ι = r ≫ (p ⁻¹ᵁ U s).ι :=
        ⟨IsOpenImmersion.lift _ (r ≫ (p ⁻¹ᵁ U s).ι) (by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          exact ⟨(r y).2, (congrArg (fun q => p (q y) ∈ U s') hr).mpr (r' y).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
      have r₁ : ρ ≫ m = r := by rw [← cancel_mono (p ⁻¹ᵁ U s).ι, Category.assoc, hm, hρ]
      have r₂ : ρ ≫ m' = r' := by rw [← cancel_mono (p ⁻¹ᵁ U s').ι, Category.assoc, hm', hρ, hr]
      have key := gen_unique' hM (K := PUnit) (K' := PUnit) (φ := fun _ => m ≫ (p ⁻¹ᵁ U s).ι ≫ 𝟙 P) (ε := fun _ => 1)
        (φ' := fun _ => m' ≫ (p ⁻¹ᵁ U s').ι ≫ 𝟙 P) (ε' := fun _ => 1)
        (fun W _ k => Finset.prod_congr rfl fun i _ => by
          show k (m' ≫ _ ≫ _) ^ _ = k (m ≫ _ ≫ _) ^ _
          rw [← Category.assoc, ← Category.assoc m, hm, hm'])
        (p ∣_ (U s ⊓ U s')) σ hσ' (hp _) (DVR.pullGen_isGen _ _ _ _ (ht s) m)
        (DVR.pullGen_isGen _ _ _ _ (ht s') m') (fun y I hI => by
          rw [val_pull hI, val_pull hI, hn s _ _ (U s ⊓ U s').ι y I hI (by rw [Category.assoc, hm, hσ]),
            hn s' _ _ (U s ⊓ U s').ι y I hI (by rw [Category.assoc, hm', hσ])]) T ρ z J hJ
      rwa [val_pull hJ, val_pull hJ, r₁, r₂] at key)
  exact triv_of_triv_pull_id ⟨u, hu⟩

theorem surjective_restrict {P Z : Scheme.{0}} (p : P ⟶ Z) (h : ∀ V : Z.Opens, IsIso (p.app V)) (V : Z.Opens) :
    Function.Surjective (p ∣_ V).appTop.hom := by
  have : IsIso (p ∣_ V).appTop := by
    rw [morphismRestrict_appTop]
    have := h (V.ι ''ᵁ ⊤)
    refine IsIso.comp_isIso' this ?_
    rw [eqToHom_op]; exact Functor.map_isIso _ _
  exact (ConcreteCategory.bijective_of_isIso (p ∣_ V).appTop).2

theorem triv_of_triv_faces : ∀ (k : Type) [Field k] (X Y Z : Over (Sp k)) (x₀ : 𝟙_ (Over (Sp k)) ⟶ X) (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (z₀ : 𝟙_ (Over (Sp k)) ⟶ Z), Smooth X.hom → Smooth Y.hom → IsProper X.hom → IsProper Y.hom → IsProjBy X.hom → IsProjBy Y.hom → GeometricallyIntegral X.hom → GeometricallyIntegral Y.hom → ConnectedSpace Z.left → ∀ M : LB (X ⊗ Y ⊗ Z).left, M.IsLB → Triv (M.pull (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left) → Triv (M.pull (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z))).left) → Triv (M.pull (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀))).left) → Triv M := by
  intro k _ X Y Z x₀ y₀ z₀ sX sY pX pY jX jY gX gY cZ M hM h₁ h₂ h₃
  have loc := GlobalTheory.T.theorem_of_cube_locally_two_projective_factors k X Y Z x₀ y₀ z₀ sX sY pX pY jX jY gX gY cZ M hM h₁ h₂ h₃
  have iX : ∀ V, IsIso ((snd X (Y ⊗ Z)).left.app V) := fun V =>
    GlobalTheory.ProperFunctions.isIso_app_baseChange_of_field (IsPullback.of_hasPullback X.hom (Y ⊗ Z).hom) V
  have iY : ∀ V, IsIso ((snd Y Z).left.app V) := fun V =>
    GlobalTheory.ProperFunctions.isIso_app_baseChange_of_field (IsPullback.of_hasPullback Y.hom Z.hom) V
  let σ : Z ⟶ Y ⊗ Z := lift (toUnit Z ≫ y₀) (𝟙 Z)
  obtain ⟨g, hg⟩ := h₁
  refine triv_of_locally_triv hM (snd X (Y ⊗ Z) ≫ snd Y Z).left
    (σ.left ≫ (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left) ?_ (surjective_restrict _ fun V => ?_)
    ⟨_, DVR.pullGen_isGen _ _ _ _ hg σ.left⟩ loc
  · rw [← Over.comp_left, ← Over.comp_left]
    exact congrArg (fun q => q.left)
      (show (σ ≫ lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))) ≫ snd X (Y ⊗ Z) ≫ snd Y Z = 𝟙 Z by simp [σ])
  · rw [Over.comp_left, Scheme.Hom.comp_app]
    exact IsIso.comp_isIso' (iY V) (iX _)

end GlobalTheory.CubeGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem isTypeFn_of_enum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => (e j).1) := by
  intro τ
  have hcard : Nat.card {i // (e i).1 = τ} = Dw.mult τ := by
    have e2 : {i // (e i).1 = τ} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} ≃ Fin (Dw.mult τ) := Equiv.sigmaSubtype τ
    rw [Nat.card_congr (e2.trans e3), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_pos h]
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_neg h]

theorem exists_openChart_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (z : Xo.XF c), ∃ (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R), OpenChart j y₀ ∧ z ∈ Set.range j := by
  intro hS E _ _ _ H Dw l Xo c z
  classical
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  obtain ⟨R, _, _, jR, o, v, th, hft, hred, hjR, ⟨q, hq⟩, hs, ⟨m⟩, hv, hev, hth, -⟩ :=
    GlobalTheory.ModuliChart.exists_chart_eigenframe hS E H Dw l Xo c _ _ (isTypeFn_of_enum Dw e) z
  let x : Sp R ⟶ Xo.X := jR ≫ pullback.fst _ _
  have hb : TanBasis x (fun i => (v i).left ≫ m.cm.F) :=
    ((GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal E H Dw l Xo R x o.t.G m.cm.F m.cart).2 _ v).1 hv
  let u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left) :=
    fun τ i => (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
  have htan : ∀ τ i, IsTanAt x (u τ i) := fun τ i => hb.1 _
  have heig : ∀ τ i, IsEigAt c τ (u τ i) := by
    intro τ i a
    have h := hev (e.symm ⟨τ, i⟩) a
    simp only [Equiv.apply_symm_apply] at h
    have h' : (v (e.symm ⟨τ, i⟩)).left ≫ (o.t.act.act a).left =
      spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ (v (e.symm ⟨τ, i⟩)).left := h
    show ((v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F) ≫ _ = _ ≫ (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
    rw [Category.assoc, ← m.act a, ← Category.assoc, h', Category.assoc]
  have hb' : TanBasis x (fun j => u (e j).1 (e j).2) := by
    have : (fun j => u (e j).1 (e j).2) = fun i => (v i).left ≫ m.cm.F := by
      funext j
      show (v (e.symm (e j))).left ≫ m.cm.F = _
      rw [Equiv.symm_apply_apply]
    rw [this]; exact hb
  have hbasis := (GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l Xo c R x u _ e htan heig).2 hb'
  obtain ⟨s, hsn⟩ := GlobalTheory.T.exists_fibreSection_nowhereZero_of_pullbackTriple E H Dw l Xo R x o.t m.toSABMap th hth
  have hgen := GlobalTheory.T.fibreSectionGenerates_of_nowhereZero hS E H Dw l Xo R x s hsn
  have hx : x ≫ Xo.s = sOf c R := by
    have h1 : x ≫ Xo.s = (jR ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (jR ≫ ·) pullback.condition
    rw [h1, hs, sOf]
    exact (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm
  let y : FrPt Xo c R := ⟨x, hx, u, htan, heig, hbasis, s, hgen⟩
  obtain ⟨p, ⟨f⟩⟩ := (GlobalTheory.reduced_finiteType_iff_testRing c.F).1 R hft hred
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c R p.R f.symm.toAlgHom y
  have hiso : IsIso (spMap f.symm.toAlgHom.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map f.symm.toRingEquiv.toCommRingCatIso.hom))
  refine ⟨p, spMap f.symm.toAlgHom.toRingHom ≫ jR, y₀, ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · rw [hy₀.1, Category.assoc]
  · rw [Category.assoc, hs]
    refine (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm.trans (congrArg Spec.map ?_)
    ext a
    exact f.symm.commutes a
  · obtain ⟨q', hq'⟩ := (spMap f.symm.toAlgHom.toRingHom).surjective q
    exact ⟨q', by rw [Scheme.Hom.comp_apply, hq', hq]⟩

end GlobalTheory.Frames
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_universalFrame_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : TRing c.F) (y₀ : FrPt Xo c p.R), ∃ (A : TRing c.F) (π : p.R →ₐ[c.F] A.R) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ) (u : FrPt Xo c A.R), UnivFrame y₀ π X s u := by
  first | exact @GlobalTheory.Frames.exists_univFrame_testRing | exact GlobalTheory.Frames.exists_univFrame_testRing | (intros; apply GlobalTheory.Frames.exists_univFrame_testRing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompRat

open GlobalTheory.CompIdem ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem exists_coeff_idempotents_any_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo σ₀ g ty F _ _ _ hA c
  obtain rfl : σ₀ = (KA l).val.toRingHom := RingHom.ext hA
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨S, hS, hrat⟩ := exists_rational_components (c.le.trans (coeff_le_algebraicClosure c)) Xo.s
  have := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c', hc'⟩ := exists_coeff_containing E H l (S ∪ Finset.univ.image fun j => (b j : ℂ)) (by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact mem_algebraicClosure_iff.1 (hS z h)
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
      exact mem_algebraicClosure_iff.1 (coeff_le_algebraicClosure c (b j).2))
  refine ⟨c', fun z hz => ?_, fun i => ?_⟩
  · have e := congrArg c.F.val (b.sum_repr ⟨z, hz⟩)

    rw [map_sum] at e
    have e' : z = _ := e.symm
    rw [e']
    refine sum_mem fun j _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _
      (hc' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have hr := hrat c'.F c'.le (coeff_le_algebraicClosure c') fun z hz => hc' z (Finset.mem_union_left _ hz)
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c'
  let σ : c'.F →+* ℂ := c'.F.val.toRingHom
  let s : Xo.XF c' ⟶ Sp c'.F := pullback.snd _ _
  let pr : Xo.XF c' ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → (p ≫ pr) ≫ Xo.s = spMap (KA l).val.toRingHom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, GlobalTheory.CompIdem.spMap_comp]
    rfl
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    intro p q hp hq hpq
    obtain ⟨r, hr1, hr2⟩ := hr (q (IsLocalRing.closedPoint ℂ))
    exact const_on_component σ s r hr1 (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
      p q hp hq ((connectedComponent_eq hr2) ▸ hpq) hr2
  let U : Set (Xo.XF c') := {z | ∃ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ ∧
    p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i}
  have hUc : ∀ z w, w ∈ connectedComponent z → (w ∈ U ↔ z ∈ U) := by
    intro z w h
    simp only [U, Set.mem_setOf_eq, connectedComponent_eq h]
  have hU : IsClopen U := by
    refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hUc z w hw).1 h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hUc z w hw).2 hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  obtain ⟨e, h1, h2⟩ := exists_indicator_function U hU
  refine ⟨e, h1, fun i' P hP p hp1 hp => ?_⟩
  have hp' : t (p ≫ pr) = i' := by
    have : p ≫ pr = F.u i' P := hp1
    rw [this]
    exact ht i' P hP
  split_ifs with h
  · subst h
    exact (h2 p).1 ⟨p, hp, mem_connectedComponent, hp'⟩
  · refine (h2 p).2 ?_
    rintro ⟨q, hq, hqp, hqi⟩
    exact h (Fin.ext (hp'.symm.trans ((hconst q p hq hp hqp).symm.trans hqi)))

end GlobalTheory.CompRat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_coeffField_idempotent_cutting_periodSpaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  first | exact @GlobalTheory.CompRat.exists_coeff_idempotent_functions | exact GlobalTheory.CompRat.exists_coeff_idempotent_functions | (intros; apply GlobalTheory.CompRat.exists_coeff_idempotent_functions <;> assumption)
end
