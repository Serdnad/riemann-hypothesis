module

public import Development.EtaleCohomology.TateTwists.Bundle005
public import Development.EtaleCohomology.TateTwists.Bundle002
public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle019
public import Development.EtaleCohomology.TateTwists.Bundle012
import Development.EtaleCohomology.TateTwists.Bundle011
public import Development.EtaleCohomology.TateTwists.Bundle013
public import Development.EtaleCohomology.TateTwists.Bundle029
public import Development.EtaleCohomology.TateTwists.Bundle028
import Development.EtaleCohomology.TateTwists.Bundle020
public import Development.EtaleCohomology.TateTwists.Bundle017
public import Development.EtaleCohomology.TateTwists.KumMulCocPf
public import Development.EtaleCohomology.TateTwists.Bundle016
public import Development.EtaleCohomology.TateTwists.Bundle025
public import Development.EtaleCohomology.TateTwists.Bundle027
import Development.EtaleCohomology.TateTwists.Bundle006
public import Development.EtaleCohomology.TateTwists.Bundle031
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.EtaleCohomology.TateTwists.Bundle007
import Mathlib.Tactic.TypeStar

@[expose] public section

section

namespace LateralTheory.Fix.EtaleKummerClassExplicitCocycle
open LateralTheory.EtaleFoundations

theorem primLoc : EtalePrimitiveRootsExistLocally := etale_locally_roots_of_unity_structure_of_exists_and_kummer etale_locally_exists_primitive_root_of_unity_of_invertible_order etale_locally_kummer_roots_of_units_of_invertible_order
theorem resSec : EtaleInjectiveResolutionSectionsLocallyExact := etaleSheaf_injectiveResolution_sections_exact_of_local_exactness LateralTheory.EtaleFoundations.ResSecPf.exact_loc_of

theorem holds_of (hK : EtaleKummerTriangleExists) : EtaleKummerClassExplicitCocycle := by
  have he : kum_exists := kum_exists_of hK primLoc etale_sheaf_sections_glue_of_forget_isSheaf LateralTheory.Fix.EtaleSchemeGlobalSectionCohomologyClass.intersectionNumber_baseChange resSec
  exact etale_kummer_class_specification_of_existence_naturality_additivity he
    (kum_nat_of he etale_chain_cochain_eval_basic_properties_hold primLoc etale_sheaf_sections_glue_of_forget_isSheaf)
    (kum_add_of he (kum_uniq_of primLoc etale_sheaf_sections_glue_of_forget_isSheaf etale_chain_cochain_eval_basic_properties_hold)
      (kum_mul_coc_of hK primLoc etale_sheaf_sections_glue_of_forget_isSheaf etale_chain_cochain_exists_of_eval_data etale_chain_cochain_eval_differential_formula_holds etale_chain_cochain_eval_basic_properties_hold)
      (kum_pow_coc_of hK etale_chain_cochain_exists_of_eval_data etale_chain_cochain_eval_differential_formula_holds he))

end LateralTheory.Fix.EtaleKummerClassExplicitCocycle
end

section

namespace LateralTheory.Fin.EtalePrimitiveRootsExistLocally
theorem etale_locally_exists_primitive_root_of_unity : LateralTheory.EtaleFoundations.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder := by
  apply LateralTheory.EtaleFoundations.etale_locally_exists_primitive_root_of_unity_of_invertible_order
theorem etale_torsion_cohomology_primary_localization_kummer : LateralTheory.EtaleFoundations.EtaleLocallyKummerRootsOfUnits := by
  apply LateralTheory.EtaleFoundations.etale_locally_kummer_roots_of_units_of_invertible_order
theorem etale_torsion_cohomology_primary_localization : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally := by
  apply LateralTheory.EtaleFoundations.etale_locally_roots_of_unity_structure_of_exists_and_kummer <;> first | exact etale_locally_exists_primitive_root_of_unity | exact etale_torsion_cohomology_primary_localization_kummer
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally := etale_torsion_cohomology_primary_localization
end LateralTheory.Fin.EtalePrimitiveRootsExistLocally
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExDeg

variable {R : Type} [CommRing R]

noncomputable def tmap {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) :
    Tens I J V w →ₗ[ULift.{1} R] Tens I' J' V w :=
  DirectSum.lmap fun p => TensorProduct.map ((f.f p.1.1).hom.app (op V)).hom ((g.f p.1.2).hom.app (op V)).hom

theorem lift_res {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (k : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    τ.lift V w (Tens.res k w x) = Sec.res k (τ.lift U w x) := by
  classical
  have key : τ.lift V w ∘ₗ Tens.res k w = ((K.X w).obj.map k.op).hom ∘ₗ τ.lift U w := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift,
      DirectSum.toModule_lof, TensorProduct.lift.tmul]
    exact (τ.nat k p.1.1 p.1.2 w p.2 a b).symm
  exact congrArg (fun m => m x) key

theorem lam_res {I J I' J' K : Cx R} (ν : Pair I' J' K) (f : I ⟶ I') (g : J ⟶ J') {V U : Scheme.{0}} (k : V ⟶ U)
    (w : ℤ) (x : Tens I J U w) :
    ν.lift V w (tmap f g V w (Tens.res k w x)) = Sec.res k (ν.lift U w (tmap f g U w x)) := by
  classical
  have key : (ν.lift V w ∘ₗ tmap f g V w) ∘ₗ Tens.res k w =
      ((K.X w).obj.map k.op).hom ∘ₗ (ν.lift U w ∘ₗ tmap f g U w) := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Tens.res, tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift,
      DirectSum.toModule_lof, TensorProduct.lift.tmul]
    have e := ν.nat k p.1.1 p.1.2 w p.2 (Sec.map (f.f p.1.1) a) (Sec.map (g.f p.1.2) b)
    rw [secmap_res, secmap_res] at e
    exact e.symm
  exact congrArg (fun m => m x) key

theorem lam_zero {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) (x : Tens I J V w) (hx : τ.lift V w x = 0) :
    ν.lift V w (tmap f g V w x) = 0 := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) V
  refine TensLocbij.loc_mono (hτ.2 V w x hx) ?_
  intro W k hk
  rw [← lam_res, hk, map_zero, map_zero]
  exact (map_zero _).symm

theorem lam_eq {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) (x x' : Tens I J V w) (hx : τ.lift V w x = τ.lift V w x') :
    ν.lift V w (tmap f g V w x) = ν.lift V w (tmap f g V w x') := by
  have := lam_zero τ hτ ν f g V w (x - x') (by rw [map_sub, hx, sub_self])
  rw [map_sub, map_sub, sub_eq_zero] at this
  exact this

end LateralTheory.EtaleFoundations.ExDeg

namespace LateralTheory.EtaleFoundations.ExDeg
variable {R : Type} [CommRing R]

theorem sheafT (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property)

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y :=
  (TensLocbij.map_comp_apply' R F.obj k g y).symm

def sv {I J K : Cx R} (τ : Pair I J K) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) : Sieve U where
  arrows V g := ∃ x, τ.lift V w x = Sec.res g y
  downward_closed := by
    rintro V W g ⟨x, hx⟩ k
    exact ⟨Tens.res k w x, by rw [lift_res, hx, res_comp]⟩

theorem sv_cov {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    sv τ w y ∈ Scheme.etaleTopology.{0} U := by
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  exact Scheme.etaleTopology.superset_covering (fun V g hg => hP V g hg) hS

noncomputable def fam {I J K I' J' K' : Cx R} (τ : Pair I J K) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    Presieve.FamilyOfElements ((K'.X w).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (sv τ w y).arrows :=
  fun V _ hk => (ν.lift V w (tmap f g V w hk.choose) : Sec (K'.X w) V)

theorem fam_compat {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    (fam τ ν f g w y).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ heq
  show Sec.res g₁ (ν.lift Y₁ w (tmap f g Y₁ w h₁.choose)) = Sec.res g₂ (ν.lift Y₂ w (tmap f g Y₂ w h₂.choose))
  rw [← lam_res, ← lam_res]
  apply lam_eq τ hτ
  rw [lift_res, lift_res, h₁.choose_spec, h₂.choose_spec, res_comp, res_comp, heq]

noncomputable def glue {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) : Sec (K'.X w) U :=
  (sheafT (K'.X w) _ (sv_cov τ hτ w y)).amalgamate _ (fam_compat τ hτ ν f g w y)

theorem glue_spec {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) {V : Scheme.{0}} (k : V ⟶ U)
    (x : Tens I J V w) (hx : τ.lift V w x = Sec.res k y) :
    Sec.res k (glue τ hτ ν f g w y) = ν.lift V w (tmap f g V w x) := by
  have hk : (sv τ w y).arrows k := ⟨x, hx⟩
  have := (sheafT (K'.X w) _ (sv_cov τ hτ w y)).valid_glue (fam_compat τ hτ ν f g w y) k hk
  refine this.trans ?_
  show ν.lift V w (tmap f g V w hk.choose) = _
  exact lam_eq τ hτ ν f g V w _ _ (hk.choose_spec.trans hx.symm)

end LateralTheory.EtaleFoundations.ExDeg

namespace LateralTheory.EtaleFoundations.ExDeg
variable {R : Type} [CommRing R]

theorem sv_loc {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    Loc U fun V k => (sv τ w y).arrows k :=
  ⟨sv τ w y, sv_cov τ hτ w y, fun _ _ h => h⟩

theorem glue_add {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y₁ y₂ : Sec (K.X w) U) :
    glue τ hτ ν f g w (y₁ + y₂) = glue τ hτ ν f g w y₁ + glue τ hτ ν f g w y₂ := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U
  refine TensLocbij.loc_mono (TensLocbij.loc_and (sv_loc τ hτ w y₁) (sv_loc τ hτ w y₂)) ?_
  rintro V k ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  rw [glue_spec τ hτ ν f g w _ k (x₁ + x₂) (by rw [map_add (f := _), hx₁, hx₂]; exact (map_add _ _ _).symm)]
  have e : Sec.res k (glue τ hτ ν f g w y₁ + glue τ hτ ν f g w y₂) =
      Sec.res k (glue τ hτ ν f g w y₁) + Sec.res k (glue τ hτ ν f g w y₂) := map_add _ _ _
  rw [e, glue_spec τ hτ ν f g w _ k x₁ hx₁, glue_spec τ hτ ν f g w _ k x₂ hx₂, map_add (f := _), map_add (f := _)]

theorem glue_smul {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (c : ULift.{1} R) (y : Sec (K.X w) U) :
    glue τ hτ ν f g w (c • y) = c • glue τ hτ ν f g w y := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U
  refine TensLocbij.loc_mono (sv_loc τ hτ w y) ?_
  rintro V k ⟨x, hx⟩
  rw [glue_spec τ hτ ν f g w _ k (c • x) (by rw [map_smul, hx]; exact (map_smul _ _ _).symm)]
  have e : Sec.res k (c • glue τ hτ ν f g w y) = c • Sec.res k (glue τ hτ ν f g w y) := map_smul _ _ _
  rw [e, glue_spec τ hτ ν f g w _ k x hx, map_smul, map_smul]

theorem glue_res {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U U' : Scheme.{0}} (w : ℤ) (h : U' ⟶ U) (y : Sec (K.X w) U) :
    glue τ hτ ν f g w (Sec.res h y) = Sec.res h (glue τ hτ ν f g w y) := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U'
  refine TensLocbij.loc_mono (sv_loc τ hτ w (Sec.res h y)) ?_
  rintro _ k ⟨x, hx⟩
  rw [glue_spec τ hτ ν f g w _ k x hx, res_comp]
  rw [res_comp] at hx
  rw [glue_spec τ hτ ν f g w _ (k ≫ h) x hx]

noncomputable def phi {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (w : ℤ) : K.X w ⟶ K'.X w :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun y => glue τ hτ ν f g w (U := U.unop) y
          map_add' := fun y₁ y₂ => glue_add τ hτ ν f g w y₁ y₂
          map_smul' := fun c y => glue_smul τ hτ ν f g w c y }
     naturality := by
       intro U U' h
       ext y
       exact glue_res τ hτ ν f g w h.unop y }⟩

theorem res_id {F : Shv R} {U : Scheme.{0}} (y : Sec F U) : Sec.res (𝟙 U) y = y := by
  simp [Sec.res]

end LateralTheory.EtaleFoundations.ExDeg

open LateralTheory.EtaleFoundations.ExDeg in
theorem LateralTheory.EtaleFoundations.twpair_tens_univ_exdeg_of : LateralTheory.EtaleFoundations.twpair_tens_univ_exdeg := by
  intro R _ I J K τ hτ I' J' K' ν f g w
  refine ⟨_root_.LateralTheory.EtaleFoundations.ExDeg.phi τ hτ ν f g w, ?_⟩
  intro U s t h a b
  classical
  have hx : τ.lift U w (DirectSum.lof (ULift.{1} R) _ _ ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      Sec.res (𝟙 U) (τ.mul U s t w h a b) := by
    rw [res_id]
    simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
  have e := glue_spec τ hτ ν f g w _ (𝟙 U) _ hx
  rw [res_id] at e
  refine e.trans ?_
  simp only [tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift, DirectSum.toModule_lof,
    TensorProduct.lift.tmul]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.columnPf

def kerLoc : Prop :=
  ∀ (R : Type) [CommRing R] (M : Shv R) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ M.obj),
    (∀ (U : Scheme.{0}) (y : Sec M U), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = Sec.res g y) →
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) →
    ∀ (G : Shv R) (V : Scheme.{0}) (u : Sec G V ⊗[ULift.{1} R] P.obj (op V)),
      TensorProduct.map LinearMap.id (φ.app (op V)).hom u = 0 →
      Loc V fun _ k => TensorProduct.map (G.obj.map k.op).hom (P.map k.op).hom u = 0

theorem map_map_eq {S : Type*} [CommRing S] {A B C D A' B' C' D' : Type*} [AddCommGroup A] [Module S A]
    [AddCommGroup B] [Module S B] [AddCommGroup C] [Module S C] [AddCommGroup D] [Module S D]
    [AddCommGroup A'] [Module S A'] [AddCommGroup B'] [Module S B'] [AddCommGroup C'] [Module S C']
    [AddCommGroup D'] [Module S D']
    (f1 : A →ₗ[S] A') (f2 : A' →ₗ[S] C) (f1' : A →ₗ[S] C') (f2' : C' →ₗ[S] C)
    (g1 : B →ₗ[S] B') (g2 : B' →ₗ[S] D) (g1' : B →ₗ[S] D') (g2' : D' →ₗ[S] D)
    (hf : f2 ∘ₗ f1 = f2' ∘ₗ f1') (hg : g2 ∘ₗ g1 = g2' ∘ₗ g1') (x : A ⊗[S] B) :
    TensorProduct.map f2 g2 (TensorProduct.map f1 g1 x) = TensorProduct.map f2' g2' (TensorProduct.map f1' g1' x) := by
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hf, hg, TensorProduct.map_comp, LinearMap.comp_apply]

end LateralTheory.EtaleFoundations.columnPf

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.lift_of (hK : kerLoc) : lift := by
  classical
  intro R _ M P φ hsurj hker F G δ U x hx
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  refine loc_bind (loc_finset S fun i _ => hsurj U i.2) ?_
  intro V g hV
  choose p hp using hV
  let x' : Sec F V ⊗[ULift.{1} R] P.obj (op V) := ∑ i ∈ S.attach, (F.obj.map g.op).hom i.1.1 ⊗ₜ p i.1 i.2
  have h1 : TensorProduct.map LinearMap.id (φ.app (op V)).hom x' =
      TensorProduct.map (F.obj.map g.op).hom (M.obj.map g.op).hom x := by

    rw [hS, map_sum, map_sum, ← Finset.sum_attach S]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [hp i.1 i.2]
  have nat : ∀ {V' V : Scheme.{0}} (k : V' ⟶ V), (G.obj.map k.op).hom ∘ₗ (δ.hom.app (op V)).hom =
      (δ.hom.app (op V')).hom ∘ₗ (F.obj.map k.op).hom := fun k => by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, δ.hom.naturality]
  have h2 : TensorProduct.map LinearMap.id (φ.app (op V)).hom
      (TensorProduct.map (δ.hom.app (op V)).hom LinearMap.id x') = 0 := by
    rw [map_map_eq (f1 := (δ.hom.app (op V)).hom) (f2 := LinearMap.id) (g1 := LinearMap.id) (g2 := (φ.app (op V)).hom)
      (f1' := LinearMap.id) (f2' := (δ.hom.app (op V)).hom) (g1' := (φ.app (op V)).hom) (g2' := LinearMap.id)
      (by simp) (by simp), h1,
      map_map_eq (f1 := (F.obj.map g.op).hom) (f2 := (δ.hom.app (op V)).hom) (g1 := (M.obj.map g.op).hom)
      (g2 := LinearMap.id) (f1' := (δ.hom.app (op U)).hom) (f2' := (G.obj.map g.op).hom) (g1' := LinearMap.id)
      (g2' := (M.obj.map g.op).hom) (nat g).symm (by simp), hx, map_zero]
  refine loc_mono (hK R M P φ hsurj hker G V _ h2) ?_
  intro W k hk
  refine ⟨TensorProduct.map (F.obj.map k.op).hom (P.map k.op).hom x', ?_, ?_⟩
  · rw [map_map_eq (f1 := (F.obj.map k.op).hom) (f2 := (δ.hom.app (op W)).hom) (g1 := (P.map k.op).hom)
      (g2 := LinearMap.id) (f1' := (δ.hom.app (op V)).hom) (f2' := (G.obj.map k.op).hom) (g1' := LinearMap.id)
      (g2' := (P.map k.op).hom) (nat k).symm (by simp), hk]
  · have hφ : (φ.app (op W)).hom ∘ₗ (P.map k.op).hom = (M.obj.map k.op).hom ∘ₗ (φ.app (op V)).hom := by
      rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, φ.naturality]
    rw [map_map_eq (f1 := (F.obj.map k.op).hom) (f2 := LinearMap.id) (g1 := (P.map k.op).hom)
      (g2 := (φ.app (op W)).hom) (f1' := LinearMap.id) (f2' := (F.obj.map k.op).hom) (g1' := (φ.app (op V)).hom)
      (g2' := (M.obj.map k.op).hom) (by simp) hφ, h1, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp]

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.column_of' (hK : kerLoc) : LateralTheory.EtaleFoundations.acyc.column :=
  LateralTheory.EtaleFoundations.acyc.column_of_cut (lift_of hK) kill_of
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.StepPf
open LateralTheory.EtaleFoundations.stairPf
variable {R : Type} [CommRing R] {C J T : Cx R}

theorem tens_res_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (w : ℤ) (x : Tens C J U w) :
    Tens.res (k ≫ g) w x = Tens.res k w (Tens.res g w x) := by
  ext p
  rw [res_apply, res_apply, res_apply]
  generalize x p = v
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem ix_eq {w : ℤ} (p : Ix w) (a b : ℤ) (h : p.1.2 = b) (ha : a + b = w) : p = ⟨(a, b), ha⟩ :=
  Subtype.ext (Prod.ext (show p.1.1 = a by have := p.2; omega) h)

theorem lof_back {U : Scheme.{0}} {w : ℤ} (i j : Ix w) (h : i = j) (v : Cmp C J U w i) :
    DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) j ((DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) i v) j) =
      DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) i v := by
  subst h; rw [lof_same]

theorem ev_zsmul {U : Scheme.{0}} {w : ℤ} (c : ℤ) (f : Tens C J U w) (q : Ix w) : (c • f) q = c • f q := rfl

theorem Dm_comp (U : Scheme.{0}) (n t0 : ℤ) (y : Tens C J U n) :
    (Dm U n (n + 1) rfl y) ⟨(n - t0 + 1, t0), by omega⟩ =
      TensorProduct.map ((C.d (n - t0) (n - t0 + 1)).hom.app (op U)).hom LinearMap.id (y ⟨(n - t0, t0), by omega⟩) +
      (Dm U n (n + 1) rfl (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(n - t0 + 1, t0 - 1), by omega⟩
        (y ⟨(n - t0 + 1, t0 - 1), by omega⟩))) ⟨(n - t0 + 1, t0), by omega⟩ := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add (f := _), DirectSum.add_apply] at ha hb ⊢
    rw [ha, hb]; abel
  | of p v =>
    rw [← DirectSum.lof_eq_of (ULift.{1} R)]
    by_cases h0 : p.1.2 = t0
    · obtain ⟨⟨a, b⟩, hab⟩ := p
      simp only at h0; subst h0
      obtain rfl : a = n - b := by omega
      rw [Dm_lof, DirectSum.add_apply, ev_zsmul]
      dsimp only
      rw [lof_same, lof_ne _ _ _ _ (by simp), smul_zero, add_zero,
        lof_same, lof_ne _ _ _ _ (by simp; omega), map_zero, map_zero, DirectSum.zero_apply, add_zero]
    by_cases h1 : p.1.2 = t0 - 1
    · rw [lof_back p _ (ix_eq p (n - t0 + 1) (t0 - 1) h1 (by omega)), lof_ne _ _ _ _ h0, map_zero, zero_add]
    · rw [Dm_lof, DirectSum.add_apply, ev_zsmul, lof_ne _ _ _ _ h0, lof_ne _ _ _ _ (by simp; omega),
        smul_zero, add_zero, lof_ne _ _ _ _ h0, lof_ne _ _ _ _ h1, map_zero, map_zero, map_zero,
        DirectSum.zero_apply, add_zero]

theorem Step_of : LateralTheory.EtaleFoundations.stairPf.Step := by
  intro R _ C J T τ hτ hc n t0 V x hx hd
  have hD : τ.lift V (n + 1) (Dm V n (n + 1) rfl x) = 0 := by rw [lift_Dm, hd]
  refine loc_bind (hτ.2 V (n + 1) _ hD) fun W g hW => ?_
  have hc0 : TensorProduct.map ((C.d (n - t0) (n - t0 + 1)).hom.app (op W)).hom LinearMap.id
      (Tens.res g n x ⟨(n - t0, t0), by omega⟩) = 0 := by
    rw [res_apply, nat_tens]
    have h1 := congrArg (fun z => z ⟨(n - t0 + 1, t0), by omega⟩) hW
    simp only at h1
    rw [res_apply, Dm_comp, hx ⟨(n - t0 + 1, t0 - 1), by omega⟩ (by simp)] at h1
    simp only [map_zero, DirectSum.zero_apply, add_zero] at h1
    exact h1
  refine loc_mono (hc W (n - t0) t0 _ hc0) fun W' k hk => ?_
  obtain ⟨y0, hy0⟩ := hk
  refine ⟨Tens.res (k ≫ g) n x - Dm W' (n - 1) n (by ring)
      (DirectSum.lof (ULift.{1} R) (Ix (n - 1)) (Cmp C J W' (n - 1)) ⟨(n - t0 - 1, t0), by omega⟩ y0),
    DirectSum.lof (ULift.{1} R) (Ix (n - 1)) (Cmp C J W' (n - 1)) ⟨(n - t0 - 1, t0), by omega⟩ y0, ?_,
    (sub_add_cancel _ _).symm⟩
  intro p hp
  rw [DirectSum.sub_apply, Dm_lof, DirectSum.add_apply, ev_zsmul]
  rcases lt_or_eq_of_le (show p.1.2 ≤ t0 by omega) with h | h
  · rw [res_apply, hx p h, map_zero, lof_ne _ _ _ _ (by simp; omega), lof_ne _ _ _ _ (by simp; omega),
      smul_zero, add_zero, sub_zero]
  · obtain ⟨⟨a, b⟩, hab⟩ := p
    simp only at h; subst h
    obtain rfl : a = n - b := by omega
    dsimp only
    rw [lof_shift W' n (n - b - 1) (n - b) b (by ring) (by omega) (by omega), lof_same,
      lof_ne _ _ _ _ (by simp), smul_zero, add_zero, hy0, tens_res_comp, res_apply k, sub_self]

end LateralTheory.EtaleFoundations.StepPf
end
end
