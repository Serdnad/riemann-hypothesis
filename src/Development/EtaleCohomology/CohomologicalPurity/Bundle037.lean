module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle004
public import Development.EtaleCohomology.EtaleSheaves.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle030
public import Development.EtaleCohomology.TateTwists.Bundle006
public import Development.EtaleCohomology.EtaleSheaves.Bundle014
public import Development.EtaleCohomology.EtaleSheaves.Bundle013
public import Development.EtaleCohomology.KummerTheory.Bundle016
public import Development.EtaleCohomology.TateTwists.Bundle034
public import Development.EtaleCohomology.TateTwists.Bundle019
public import Development.EtaleCohomology.TateTwists.Bundle011
public import Development.EtaleCohomology.TateTwists.Bundle023
public import Development.EtaleCohomology.TateTwists.Bundle029
public import Development.EtaleCohomology.TateTwists.Bundle032
public import Development.EtaleCohomology.TateTwists.Bundle021
public import Development.EtaleCohomology.TateTwists.Bundle027
public import Development.EtaleCohomology.TateTwists.Bundle020
public import Development.EtaleCohomology.TateTwists.Bundle028
public import Development.EtaleCohomology.TateTwists.conePf
public import Development.EtaleCohomology.CohomologicalPurity.Bundle012
public import Development.EtaleCohomology.CohomologicalPurity.Bundle019
public import Development.EtaleCohomology.CohomologicalPurity.Bundle021
public import Development.EtaleCohomology.CohomologicalPurity.Bundle020
public import Development.EtaleCohomology.CohomologicalPurity.Bundle034
import Development.EtaleCohomology.CohomologicalPurity.Bundle031
public import Development.EtaleCohomology.CohomologicalPurity.Bundle018
public import Development.EtaleCohomology.CohomologicalPurity.Bundle033
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Limits.Types.Pushouts
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
public import Development.EtaleCohomology.TateTwists.Bundle010
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.EtaleFoundations

namespace LateralTheory.CohomologicalPurity.LeafAWCut

def LeafTwSec : Prop := EtaleTateTwistSectionsLocallyGenerated

theorem of_pair (h : LateralTheory.E.CupProductRingLaws.LeafTwPairExists) : LateralTheory.CohomologicalPurity.LeafAW := by
  intro q _ i j
  exact ⟨pick_spec (h q i j), fun E n m α β => LateralTheory.KummerTheory.CupAW_of (ZMod q) (twPair q i j) E rfl α β⟩

theorem row : EtaleTensorWithFlatPreservesLocalExactness := by
  intro R _ C J hJ hC s t V x hx
  have hA : C.Acyclic := fun n => (etale_short_complex_exact_iff_locally_surjective_on_kernel R (C.sc n)).2 (hC n)
  exact acyc.column_of R C J hJ ((acyc.acycIff_of R C).1 hA) V s t x hx

theorem tensAcyc : EtaleTensorAcyclicOfFlatBounded :=
  etale_tensor_complex_acyclic_of_locally_exact_flat etale_short_complex_exact_iff_locally_surjective_on_kernel (etale_tensor_complex_locally_exact_of_lifted_sections
    (etale_tensor_cycles_locally_lift_of_row_exact_and_descent row etale_tensor_cycle_locally_lowers_top_degree_of_row_exact))

theorem tensQis : EtaleTensorPairQuasiIsoOfFlatQuasiIso := etale_tensor_preserves_quasiIso_of_acyclic_and_cone tensAcyc tqis.cone_of

theorem pair_of (hq : EtaleTensorPairQuasiIsoOfFlatQuasiIso) (hm : EtaleTateTwistSingletonTensorGenMul) : LateralTheory.E.CupProductRingLaws.LeafTwPairExists :=
  LateralTheory.E.LeafTwPairExistsPf.LeafTwPairExists_of' LateralTheory.E.LeafTwTensExPf.LeafTwTensEx_of
    (LateralTheory.E.LeafTwTensResPf.leafTwTensRes_of
      (etale_tensor_twisted_resolution_of_existence_bound_and_sides LateralTheory.Fin.EtaleComplexTensorPairingExists.intersectionNumber_baseChange
        (fun R _ _ _ _ μ hI hJ hμ => (LateralTheory.Fin.EtaleTensorPairUniversalProperty.intersectionNumber_baseChange R μ hμ).2.1 hI hJ)
        (tt_twist_side_of hm LateralTheory.Fin.EtaleTateTwistSheafFlat.intersectionNumber_baseChange LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange hq)
        (tt_res_side_of LateralTheory.Fin.EtaleTensorPairUniversalProperty.intersectionNumber_baseChange hq))
      (fun q _ j t => (LateralTheory.Fin.EtaleTwistResolutionUniversalExtension.intersectionNumber_baseChange q j).2.1 t))

theorem twMul (hT : LeafTwSec) : EtaleTateTwistSingletonTensorGenMul :=
  etale_tate_twist_tensor_iso_of_generator_map_iso (etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists LateralTheory.Fin.EtaleComplexTensorPairingExists.intersectionNumber_baseChange) (etale_tate_twist_multiplication_generator_map_of_section_description hT)
    (etale_tate_twist_generator_map_isIso_of_inj_surj etale_sheaf_mono_epi_iff_sections_of_separation
      (etale_tate_twist_generator_map_surjective_of_local_and_root (fun q _ i => (hT q i).1)
        (fun q _ j => ⟨(hT q j).2.2.2.1, fun U ζ ξ => (hT q j).2.1 U ζ (twGen j ξ)⟩))
      (etale_tate_twist_generator_map_injective_of_sections_glue hT LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange))

theorem goal_of (h2 : LeafTwSec) : LateralTheory.CohomologicalPurity.LeafAW :=
  of_pair (pair_of tensQis (twMul h2))

end LateralTheory.CohomologicalPurity.LeafAWCut
end

section

namespace LateralTheory.Fin.LeafExc
theorem etale_excision_identification_of_excision : LateralTheory.CohomologicalPurity.LeafExcIdent := by
  apply LateralTheory.CohomologicalPurity.EtaleExcIdent
theorem etale_excision_cohomological_degree_of_excision : LateralTheory.CohomologicalPurity.LeafExcDeg := by
  apply LateralTheory.CohomologicalPurity.LeafExcDeg_of
theorem etale_excision_formal_reduction_of_excision : LateralTheory.CohomologicalPurity.LeafExcFormal := by
  apply LateralTheory.CohomologicalPurity.LeafExcFormal_of <;> first | exact etale_excision_identification_of_excision | exact etale_excision_cohomological_degree_of_excision
theorem etale_excision_free_cokernel_injective_of_excision : LateralTheory.CohomologicalPurity.LeafFreeCokInj := by
  apply LateralTheory.CohomologicalPurity.LeafFreeCokInj_of
theorem etale_excision_cokernel_free_of_excision : LateralTheory.CohomologicalPurity.LeafFreeCok := by
  apply LateralTheory.CohomologicalPurity.LeafFreeCok_of_inj <;> first | exact etale_excision_free_cokernel_injective_of_excision
theorem etale_excision_surjective_geometric_points_of_excision : LateralTheory.CohomologicalPurity.LeafSurjGeo := by
  apply LateralTheory.CohomologicalPurity.LeafSurjGeo_of
theorem etale_excision_injective_geometric_points_of_excision : LateralTheory.CohomologicalPurity.LeafInjGeo := by
  apply LateralTheory.CohomologicalPurity.LeafInjGeo_of
theorem etale_excision_sheaf_level_of_excision : LateralTheory.CohomologicalPurity.LeafExcSheaf := by
  apply LateralTheory.CohomologicalPurity.LeafExcSheaf_of <;> first | exact etale_excision_cokernel_free_of_excision | exact etale_excision_surjective_geometric_points_of_excision | exact etale_excision_injective_geometric_points_of_excision
theorem etale_excision_isomorphism_of_excision : LateralTheory.CohomologicalPurity.LeafExc := by
  apply LateralTheory.CohomologicalPurity.LeafExc_of <;> first | exact etale_excision_formal_reduction_of_excision | exact etale_excision_sheaf_level_of_excision
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafExc := etale_excision_isomorphism_of_excision
end LateralTheory.Fin.LeafExc
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem psh_limit_ext {J : Type} [SmallCategory J] (F : J ⥤ PSh) (U : Scheme.{0}ᵒᵖ) (w w' : (limit F).obj U)
    (h : ∀ j, (limit.π F j).app U w = (limit.π F j).app U w') : w = w' := by
  apply (mono_iff_injective (limitObjIsoLimitCompEvaluation F U).hom).1 inferInstance
  apply Types.limit_ext
  intro j
  have e := limitObjIsoLimitCompEvaluation_hom_π F j (k := U)
  have e1 := congrArg (fun f => f w) (congrArg ConcreteCategory.hom e)
  have e2 := congrArg (fun f => f w') (congrArg ConcreteCategory.hom e)
  simp only [types_comp_apply] at e1 e2
  rw [e1, e2]; exact h j

theorem wpb_ext {B : PSh} {n : ℕ} {P : PSh} (φ : P ⟶ B) (U : Scheme.{0}ᵒᵖ)
    (w w' : (widePullback B (fun _ : Fin (n + 1) => P) fun _ => φ).obj U)
    (h : ∀ i, NatTrans.app (WidePullback.π (fun _ : Fin (n + 1) => φ) i) U w =
      NatTrans.app (WidePullback.π (fun _ : Fin (n + 1) => φ) i) U w') : w = w' := by
  apply psh_limit_ext _ U
  rintro (_ | i)
  · have e := WidePullback.π_arrow (fun _ : Fin (n + 1) => φ) 0
    have e1 := congrArg (fun f => (f.app U) w) e
    have e2 := congrArg (fun f => (f.app U) w') e
    simp only [NatTrans.comp_app, types_comp_apply] at e1 e2
    change NatTrans.app (WidePullback.base (fun _ : Fin (n + 1) => φ)) U w =
      NatTrans.app (WidePullback.base (fun _ : Fin (n + 1) => φ)) U w'
    rw [← e1, ← e2, h 0]
  · exact h i

theorem leafCechRec : LeafCechRec := by
  intro X P Z φ r g hg hinj hsurj
  let Xa : SimplicialObject.Augmented PSh := { left := X, right := Z, hom := r }
  let G : SimplicialObject.Augmented.toArrow.obj Xa ⟶ Arrow.mk φ :=
    Arrow.homMk g (𝟙 Z) (by change g ≫ φ = r.app _ ≫ 𝟙 Z; exact hg.trans (Category.comp_id _).symm)
  let Ψ := SimplicialObject.equivalenceLeftToRight Xa (Arrow.mk φ) G
  have hπ : ∀ (m : ℕ) (U : Scheme.{0}ᵒᵖ) x (i : Fin (m + 1)),
      NatTrans.app (WidePullback.π (fun _ : Fin (m + 1) => φ) i) U
        (NatTrans.app (Ψ.left.app (op (SimplexCategory.mk m))) U x) = g.app U ((X.map (vtx m i).op).app U x) := by
    intro m U x i
    have e : Ψ.left.app (op (SimplexCategory.mk m)) ≫ WidePullback.π (fun _ : Fin (m + 1) => φ) i =
        X.map (vtx m i).op ≫ g := WidePullback.lift_π _ _ _ _ _
    have := ConcreteCategory.congr_hom (NatTrans.congr_app e U) x
    exact this
  refine ⟨Ψ.left, ?_, ?_⟩
  · have : ∀ n, IsIso (Ψ.left.app n) := by
      intro n
      induction n using Opposite.rec with | op n => ?_
      induction n using SimplexCategory.rec with | _ m => ?_
      have : ∀ U, IsIso ((Ψ.left.app (op (SimplexCategory.mk m))).app U) := by
        intro U
        rw [isIso_iff_bijective]
        constructor
        · intro x x' hx
          apply hinj m U x x'
          intro i
          rw [← hπ, ← hπ]
          exact congrArg _ hx
        · intro w
          obtain ⟨x, hx⟩ := hsurj m U (fun i => NatTrans.app (WidePullback.π (fun _ : Fin (m + 1) => φ) i) U w)
            (NatTrans.app (WidePullback.base (fun _ : Fin (m + 1) => φ)) U w) (fun i => by
              have e := WidePullback.π_arrow (fun _ : Fin (m + 1) => φ) i
              have := ConcreteCategory.congr_hom (NatTrans.congr_app e U) w
              exact this)
          refine ⟨x, wpb_ext φ U _ _ fun i => ?_⟩
          rw [hπ]; exact hx i
      exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ Ψ.left this
  · refine (Ψ.w : _).trans ?_
    change r ≫ (SimplicialObject.const PSh).map (𝟙 Z) = r
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

theorem LeafWCech_of_data (hD : LeafWData) : LeafWCech := LeafWCech_of leafCechRec hD

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem chainsXIso_nat (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p))) =
      ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom := by
  have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
  change _ = (HomologicalComplex.extendMap ((chainsN R).map f) _).f _ ≫ _
  rw [HomologicalComplex.extendMap_f _ _ h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

instance freePresSpan (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (free R) := by
  have : PreservesColimitsOfShape WalkingSpan (ModuleCat.free.{1} (ULift.{1} R)) :=
    (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape WalkingSpan (freeP R) := by
    unfold freeP; infer_instance
  unfold free; infer_instance

theorem free_isPushout (R : Type) [CommRing R] (P : Arrow Spc) (p : ℕ) :
    IsPushout ((free R).map (P.hom.app (op (SimplexCategory.mk p))))
      ((free R).map (P.hom.app (op (SimplexCategory.mk p))))
      ((free R).map ((dbl.inl P).app (op (SimplexCategory.mk p))))
      ((free R).map ((dbl.inr P).app (op (SimplexCategory.mk p)))) := by
  have h0 : IsPushout P.hom P.hom (dbl.inl P) (dbl.inr P) := IsPushout.of_hasPushout P.hom P.hom
  have h1 := h0.map ((evaluation _ PSh).obj (op (SimplexCategory.mk p)))
  exact h1.map (free R)

theorem chains_isPushout (R : Type) [CommRing R] (P : Arrow Spc) (p : ℕ) :
    IsPushout (((chains R).map P.hom).f (-(p : ℤ))) (((chains R).map P.hom).f (-(p : ℤ)))
      (((chains R).map (dbl.inl P)).f (-(p : ℤ))) (((chains R).map (dbl.inr P)).f (-(p : ℤ))) :=
  (free_isPushout R P p).of_iso' (chainsXIso R _ p) (chainsXIso R _ p) (chainsXIso R _ p)
    (chainsXIso R _ p) (chainsXIso_nat R _ p) (chainsXIso_nat R _ p)
    (chainsXIso_nat R _ p) (chainsXIso_nat R _ p)

theorem leafDblCok_of : LeafDblCok := by
  intro R _ P _ n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    exact isIso_cokernel_map_of_isPushout (chains_isPushout R P p)
  · push Not at hn
    have hz : ∀ E : Spc, IsZero (((chains R).obj E).X n) := fun E =>
      HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)
    have hc : ∀ {E E' : Spc} (f : E ⟶ E'), IsZero (cokernel (((chains R).map f).f n)) := fun f => by
      rw [IsZero.iff_id_eq_zero]
      exact coequalizer.hom_ext ((hz _).eq_of_src _ _)
    exact ⟨⟨0, (hc _).eq_of_src _ _, (hc _).eq_of_src _ _⟩⟩

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

section gen
variable {C : Type*} [Category C] {S : Type*} [Ring S] {F G : Cᵒᵖ ⥤ ModuleCat.{1} S} (φ : F ⟶ G) {X : C}

theorem pl_imageSieve_add (s s' : G.obj (op X)) :
    Presheaf.imageSieve φ s ⊓ Presheaf.imageSieve φ s' ≤ Presheaf.imageSieve φ (s + s') := by
  rintro Y i ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
  exact ⟨t + t', by rw [map_add (f := _), map_add (f := _), ht, ht']⟩

theorem pl_imageSieve_smul (r : S) (s : G.obj (op X)) :
    Presheaf.imageSieve φ s ≤ Presheaf.imageSieve φ (r • s) := by
  rintro Y i ⟨t, ht⟩
  exact ⟨r • t, by rw [map_smul, map_smul, ht]⟩

theorem pl_imageSieve_zero : Presheaf.imageSieve φ (0 : G.obj (op X)) = ⊤ := by
  ext Y i
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩
end gen

theorem pl_hit (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (n : SimplexCategoryᵒᵖ)
    {X Z : Scheme.{0}} (x : (E.obj n).obj (op X)) (h : Z ⟶ X)
    (H : (∃ y, (f.app n).app (op Z) y = (E.obj n).map h.op x) ∨ (∃ y, (g.app n).app (op Z) y = (E.obj n).map h.op x)) :
    Presheaf.imageSieve (biprod.desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)) h := by
  rcases H with ⟨y, hy⟩ | ⟨y, hy⟩
  · refine ⟨NatTrans.app (biprod.inl : (freeP R).obj (U.obj n) ⟶ (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)) _
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)), ?_⟩
    have key := congrArg (fun (k : (freeP R).obj (U.obj n) ⟶ (freeP R).obj (E.obj n)) => ConcreteCategory.hom (NatTrans.app k (op Z))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)))
      (biprod.inl_desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
    refine Eq.trans key ?_
    change (ModuleCat.free _).map _ (ModuleCat.freeMk _) = (ModuleCat.free _).map _ (ModuleCat.freeMk _)
    refine (ModuleCat.free_map_apply _ _).trans (Eq.trans ?_ (ModuleCat.free_map_apply _ _).symm)
    exact congrArg ModuleCat.freeMk (congrArg ULift.up hy)
  · refine ⟨NatTrans.app (biprod.inr : (freeP R).obj (V.obj n) ⟶ (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)) _
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)), ?_⟩
    have key := congrArg (fun (k : (freeP R).obj (V.obj n) ⟶ (freeP R).obj (E.obj n)) => ConcreteCategory.hom (NatTrans.app k (op Z))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)))
      (biprod.inr_desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
    refine Eq.trans key ?_
    change (ModuleCat.free _).map _ (ModuleCat.freeMk _) = (ModuleCat.free _).map _ (ModuleCat.freeMk _)
    refine (ModuleCat.free_map_apply _ _).trans (Eq.trans ?_ (ModuleCat.free_map_apply _ _).symm)
    exact congrArg ModuleCat.freeMk (congrArg ULift.up hy)

theorem pl_gen (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hL : LocCov f g) (n : SimplexCategoryᵒᵖ)
    (X : Scheme.{0}) (x : (E.obj n).obj (op X)) :
    Presheaf.imageSieve (biprod.desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)) ∈ Scheme.etaleTopology.{0} X := by
  obtain ⟨ι, O, hO, hi⟩ := hL n X x
  have hO' : TopologicalSpace.IsOpenCover O := hO
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_ (X.openCoverOfIsOpenCover O hO').mem_grothendieckTopology
  refine (Sieve.generate_le_iff _ _).2 ?_
  rintro Y _ ⟨i⟩
  exact pl_hit R f g n x (O i).ι (hi i)

theorem LeafPLoc_of : LeafPLoc := by
  intro R _ U V E f g hL n
  constructor
  intro X s
  change (ULift.{1} ((E.obj n).obj (op X)) →₀ ULift.{1} R) at s
  induction s using Finsupp.induction_linear with
  | zero =>
    exact GrothendieckTopology.superset_covering _ (pl_imageSieve_zero _).ge (GrothendieckTopology.top_mem _ _)
  | add a b ha hb =>
    exact GrothendieckTopology.superset_covering _ (pl_imageSieve_add _ _ _)
      (GrothendieckTopology.intersection_covering _ ha hb)
  | single a r =>
    have e : (Finsupp.single a r : ULift.{1} ((E.obj n).obj (op X)) →₀ ULift.{1} R) =
        r • ModuleCat.freeMk (R := ULift.{1} R) a := by
      exact (Finsupp.smul_single_one a r).symm
    have h := GrothendieckTopology.superset_covering _ (pl_imageSieve_smul _ r _) (pl_gen R f g hL n X a.down)
    convert h using 2
    exact congrArg (Presheaf.imageSieve _) e

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end
