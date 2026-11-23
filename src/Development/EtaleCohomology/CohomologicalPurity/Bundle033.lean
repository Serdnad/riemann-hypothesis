module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle019
public import Development.EtaleCohomology.CohomologicalPurity.Bundle028
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.CohomologicalPurity.Bundle029
import Development.EtaleCohomology.CohomologicalPurity.Bundle026
public import Development.EtaleCohomology.CohomologicalPurity.Bundle020
public import Development.EtaleCohomology.CohomologicalPurity.Bundle031
public import Development.EtaleCohomology.CohomologicalPurity.OffContStepPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Development.EtaleCohomology.CohomologicalPurity.Bundle012

@[expose] public section

section

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex Pretriangulated

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem toHom_pull (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n) :
    CohomologyClass.toHom (HK.pull R f F n x) =
      (HomotopyCategory.quotient _ _).map f ≫ CohomologyClass.toHom x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.toHom (CohomologyClass.mk (zcomp (Cocycle.ofHom f) x (zero_add n))) = _
  rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, ← Functor.map_comp]
  congr 1
  ext p : 1
  simp [zcomp, Cocycle.equivHomShift_symm_apply, Cochain.rightShift_v _ n 0 (zero_add n) p p (add_zero p) (p + n) rfl]

theorem leafConeSplit : LeafConeSplit := by
  intro R _ K L g r hgr F n
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished g
  let Q := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)
  have z12 : Q.map g ≫ Q.map (mappingCone.inr g) = 0 := comp_distTriang_mor_zero₁₂ _ hT
  let m3 : Q.obj (mappingCone g) ⟶ (Q.obj K)⟦(1 : ℤ)⟧ := (mappingCone.triangleh g).mor₃
  have z31 : m3 ≫ (Q.map g)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have ex2 : ∀ {X} (f : Q.obj L ⟶ X), Q.map g ≫ f = 0 → ∃ w : Q.obj (mappingCone g) ⟶ X,
      f = Q.map (mappingCone.inr g) ≫ w := fun f hf => Triangle.yoneda_exact₂ _ hT f hf
  have ex3 : ∀ {X} (f : Q.obj (mappingCone g) ⟶ X), Q.map (mappingCone.inr g) ≫ f = 0 →
      ∃ w : (Q.obj K)⟦(1 : ℤ)⟧ ⟶ X, f = m3 ≫ w :=
    fun f hf => Triangle.yoneda_exact₃ _ hT f hf
  have hinj : ∀ {M : Cx R} (a b : HK R M F n), CohomologyClass.toHom a = CohomologyClass.toHom b → a = b :=
    fun a b h => (CohomologyClass.toHom_bijective _ _ _).1 h
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · apply hinj
    have h0 : Q.map (mappingCone.inr g) ≫ CohomologyClass.toHom x = 0 := by
      rw [← toHom_pull, hx, map_zero]
    obtain ⟨w, hw⟩ := ex3 _ h0
    rw [hw, map_zero]
    have : w = (Q.map g)⟦(1 : ℤ)⟧' ≫ (Q.map r)⟦(1 : ℤ)⟧' ≫ w := by
      rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hgr, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    rw [this, ← Category.assoc, z31, zero_comp]
  · have h0 : Q.map g ≫ CohomologyClass.toHom y = 0 := by
      rw [← toHom_pull, hy, map_zero]
    obtain ⟨w, hw⟩ := ex2 _ h0
    obtain ⟨x, hx⟩ := (CohomologyClass.toHom_bijective (mappingCone g) _ _).2 w
    refine ⟨x, hinj _ _ ?_⟩
    rw [toHom_pull, hx, hw]
  · rintro ⟨x, rfl⟩
    apply hinj
    rw [toHom_pull, toHom_pull, map_zero, ← Category.assoc, z12, zero_comp]

def LeafDblCok : Prop := ∀ (R : Type) [CommRing R] (P : Arrow Spc), Mono P.hom → ∀ n : ℤ,
  IsIso (cokernel.map _ _ _ _ (sqw (dbl_sq R P) n).symm)

theorem leafDblConeQI_of (hC : LeafConeCok) (hK : LeafDblCok) : LeafDblConeQI := by
  intro R _ P h
  have hi : Mono (dbl.inr P) := ⟨fun a b e => by
    have := congrArg (· ≫ dbl.fold P) e
    simpa [Category.assoc, dbl.inr_fold] using this⟩
  exact hC R _ _ _ _ (dbl_sq R P) (leafChainsMono R _ h) (leafChainsMono R _ hi) (hK R P h)

theorem etale_relative_cohomology_iso_of_cone_and_double_cokernel_isos (hC : LeafConeCok) (hK : LeafDblCok) : LeafHsRel :=
  leafHsRel_of (leafDblConeQI_of hC hK) leafConeSplit

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

def LeafPLoc : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), LocCov f g →
  ∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0}
    (biprod.desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))

theorem LeafCovLoc_of (hP : LeafPLoc) : LeafCovLoc := by
  intro R _ U V E f g hf hg hL
  refine ⟨hf, hg, fun n => ?_⟩
  let S := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  let a := (freeP R).map (f.app n)
  let b := (freeP R).map (g.app n)
  have h1 : Epi (S.map (biprod.desc a b)) := by
    have : Sheaf.IsLocallySurjective (S.map (biprod.desc a b)) :=
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).2 (hP R f g hL n)
    infer_instance
  change Epi (biprod.desc (S.map a) (S.map b))
  let P := (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)
  let k : S.obj P ⟶ S.obj ((freeP R).obj (U.obj n)) ⊞ S.obj ((freeP R).obj (V.obj n)) :=
    biprod.lift (S.map (biprod.fst : P ⟶ _)) (S.map (biprod.snd : P ⟶ _))
  have h2 : k ≫ biprod.desc (S.map a) (S.map b) = S.map (biprod.desc a b) := by
    simp only [k]
    rw [biprod.lift_desc, ← S.map_comp, ← S.map_comp, ← S.map_add (f := _), biprod.desc_eq]
  rw [← h2] at h1
  exact epi_of_epi k _

theorem LeafWCov_of' (hG : LeafGeo) (hP : LeafPLoc) (hW : LeafWLoc) : LeafWCov :=
  LeafWCov_of hG (LeafCovLoc_of hP) hW

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

abbrev vtx (n : ℕ) (i : Fin (n + 1)) : SimplexCategory.mk 0 ⟶ SimplexCategory.mk n :=
  SimplexCategory.const _ _ i

def LeafCechRec : Prop := ∀ (X : Spc) (P Z : PSh) (φ : P ⟶ Z) (r : X ⟶ disc.obj Z)
  (g : X.obj (op (SimplexCategory.mk 0)) ⟶ P), g ≫ φ = r.app (op (SimplexCategory.mk 0)) →
  (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (x x' : (X.obj (op (SimplexCategory.mk n))).obj U),
    (∀ i, g.app U ((X.map (vtx n i).op).app U x) = g.app U ((X.map (vtx n i).op).app U x')) → x = x') →
  (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (y : Fin (n + 1) → P.obj U) (z : Z.obj U), (∀ i, φ.app U (y i) = z) →
    ∃ x, ∀ i, g.app U ((X.map (vtx n i).op).app U x) = y i) →
  ∃ ψ : X ⟶ (Arrow.mk φ).cechNerve, IsIso ψ ∧ ψ ≫ (Arrow.mk φ).augmentedCechNerve.hom = r

def LeafWData : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (r : W d R ⟶ disc.obj (yoneda.obj (Spec (CommRingCat.of (MvPolynomial (Fin d) R)))))
    (g : (W d R).obj (op (SimplexCategory.mk 0)) ⟶
      yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (MvPolynomial (Fin d) R))))),
    wa d R ≫ r = 𝟙 _ ∧ g ≫ yoneda.map (fW d R) = r.app (op (SimplexCategory.mk 0)) ∧
    (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (x x' : ((W d R).obj (op (SimplexCategory.mk n))).obj U),
      (∀ i, g.app U (((W d R).map (vtx n i).op).app U x) = g.app U (((W d R).map (vtx n i).op).app U x')) →
        x = x') ∧
    (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (y : Fin (n + 1) → (yoneda.obj (Spec (CommRingCat.of
        (LaurentPolynomial (MvPolynomial (Fin d) R))))).obj U) (z : (yoneda.obj (Spec (CommRingCat.of
        (MvPolynomial (Fin d) R)))).obj U), (∀ i, (yoneda.map (fW d R)).app U (y i) = z) →
      ∃ x, ∀ i, g.app U (((W d R).map (vtx n i).op).app U x) = y i)

theorem LeafWCech_of (hC : LeafCechRec) (hD : LeafWData) : LeafWCech := by
  intro d R _
  obtain ⟨r, g, hr, hg, hi, hs⟩ := hD d R
  obtain ⟨ψ, hψ, he⟩ := hC (W d R) _ _ (yoneda.map (fW d R)) r g hg hi hs
  refine ⟨ψ, hψ, ?_⟩
  change wa d R ≫ ψ ≫ (Arrow.mk (yoneda.map (fW d R))).augmentedCechNerve.hom = 𝟙 _
  subst he
  exact hr

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut
variable {P' P : Arrow Spc} (φ : P' ⟶ P)

private theorem inl_sig : dbl.inl (QQ φ) ≫ sig φ = 𝟙 _ :=
  pushout.inl_desc (f := jj φ) (g := jj φ) _ _ _

private theorem inr_sig : dbl.inr (QQ φ) ≫ sig φ = rr φ ≫ jj φ :=
  pushout.inr_desc (f := jj φ) (g := jj φ) _ _ _

theorem etale_double_inl_sigma_inl_eq_inl : dbl.inl (QQ φ) ≫ sig φ ≫ dbl.inl (QQ φ) = dbl.inl (QQ φ) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ dbl.inl (QQ φ)) (inl_sig φ)).trans (Category.id_comp _))

theorem etale_double_inr_sigma_inl_eq_retraction_jj_inr : dbl.inr (QQ φ) ≫ sig φ ≫ dbl.inl (QQ φ) = (rr φ ≫ jj φ) ≫ dbl.inr (QQ φ) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ dbl.inl (QQ φ)) (inr_sig φ)).trans
    ((Category.assoc (rr φ) (jj φ) (dbl.inl (QQ φ))).trans ((congrArg (rr φ ≫ ·) (jj_inl φ)).trans
      (Category.assoc (rr φ) (jj φ) (dbl.inr (QQ φ))).symm)))

theorem fix_key (q : ℕ) :
    (chains (ZMod q)).map (sig φ ≫ dbl.inl (QQ φ)) ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))) =
      cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))) := by
  have h := (chains (ZMod q)).map_isPushout (IsPushout.of_hasPushout (QQ φ).hom (QQ φ).hom)
  apply h.hom_ext
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))))
      ((chains (ZMod q)).map_comp (dbl.inl (QQ φ)) (sig φ ≫ dbl.inl (QQ φ))).symm).trans
      (congrArg (fun f => (chains (ZMod q)).map f ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) (etale_double_inl_sigma_inl_eq_inl φ)))
  · have c0 : (chains (ZMod q)).map (dbl.inr (QQ φ)) ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))) = 0 :=
      cokernel.condition _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))))
      ((chains (ZMod q)).map_comp (dbl.inr (QQ φ)) (sig φ ≫ dbl.inl (QQ φ))).symm).trans
      ((congrArg (fun f => (chains (ZMod q)).map f ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) (etale_double_inr_sigma_inl_eq_retraction_jj_inr φ)).trans
      ((congrArg (· ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) ((chains (ZMod q)).map_comp (rr φ ≫ jj φ) (dbl.inr (QQ φ)))).trans
      ((Category.assoc _ _ _).trans ((congrArg ((chains (ZMod q)).map (rr φ ≫ jj φ) ≫ ·) c0).trans
      (Limits.comp_zero.trans c0.symm))))))

theorem LeafFix_of : LeafFix := by
  intro q n i P' P φ z hz
  have hr := (LateralTheory.CohomologicalPurity.eEquiv q n i (QQ φ)).right_inv ⟨z, hz⟩
  have hz1 : HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) (tw q i) n
      (HK.pull (ZMod q) (LateralTheory.CohomologicalPurity.secC q (QQ φ)) (tw q i) n z) = z := congrArg Subtype.val hr
  change HK.pull (ZMod q) ((chains (ZMod q)).map (sig φ ≫ dbl.inl (QQ φ))) (tw q i) n z = z
  conv_lhs => rw [← hz1]
  rw [← LateralTheory.CohomologicalPurity.HK.pull_comp', fix_key, hz1]

end LateralTheory.CohomologicalPurity.TubeCut

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafChiSq : Prop := ∀ {P' P : Arrow Spc} (φ : P' ⟶ P),
  IsPushout (dbl.inr P') (chi φ).right (dbl.map (chi φ)) (dbl.inr (QQ φ))

def LeafCokPush : Prop := ∀ (q : ℕ) {A B C D : Cx (ZMod q)} (f : A ⟶ B) (g : A ⟶ C) (a : B ⟶ D) (b : C ⟶ D)
  (h : IsPushout f g a b), IsIso (cokernel.map f b g a h.w.symm)

theorem LeafCokPush_of : LeafCokPush := by
  intro q A B C D f g a b h
  refine ⟨⟨cokernel.desc b (h.desc (cokernel.π f) 0 (by simp)) (by simp), ?_, ?_⟩⟩
  · refine coequalizer.hom_ext ?_
    simp
  · refine coequalizer.hom_ext ?_
    simp only [cokernel.π_desc_assoc, Category.comp_id]
    apply h.hom_ext <;> simp

theorem LeafChiExc_of (hS : LeafChiSq) : LeafChiExc := by
  intro q P' P φ
  exact LateralTheory.CohomologicalPurity.LeafExcCx_of LateralTheory.CohomologicalPurity.EtaleExcIdent q (chi φ)
    (LeafCokPush_of q _ _ _ _ ((chains (ZMod q)).map_isPushout (hS φ)))

theorem LeafExcOfEqv_of_sq (hS : LeafChiSq) : LeafExcOfEqv := LeafExcOfEqv_of LeafFix_of (LeafChiExc_of hS)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.TubeCut
namespace HomLocPf

variable {R : Type} [CommRing R]

lemma exact_cyc (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) :
    ((ShortComplex.mk (K.iCycles n) (K.d n ((ComplexShape.down ℕ).next n)) (K.iCycles_d _ _)).map
      ((evaluation _ _).obj T)).Exact :=
  (ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel n _ rfl)).map _

lemma exact_bdy (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) :
    ((ShortComplex.mk (K.toCycles (n + 1) n) (K.homologyπ n)
      (K.toCycles_comp_homologyπ _ _)).map ((evaluation _ _).obj T)).Exact :=
  (ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel _ n (ChainComplex.prev ℕ n))).map _

lemma iCyc_inj (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) : Function.Injective ((K.iCycles n).app T).hom := by
  rw [← ModuleCat.mono_iff_injective]
  exact (inferInstance : Mono (((evaluation _ _).obj T).map (K.iCycles n)))

lemma π_surj (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) : Function.Surjective ((K.homologyπ n).app T).hom := by
  rw [← ModuleCat.epi_iff_surjective]
  exact (inferInstance : Epi (((evaluation _ _).obj T).map (K.homologyπ n)))

lemma lift_cyc (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) (hx : Cyc K n T x) :
    ∃ y, ((K.iCycles n).app T).hom y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (exact_cyc K n T) x (hx _)

lemma cyc_i (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) : Cyc K n T (((K.iCycles n).app T).hom y) := by
  intro m
  change ((K.iCycles n ≫ K.d n m).app T).hom y = 0
  rw [K.iCycles_d]; rfl

lemma π_zero_iff (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((K.homologyπ n).app T).hom y = 0 ↔ Bdy K n T (((K.iCycles n).app T).hom y) := by
  have ti : ∀ z, ((K.iCycles n).app T).hom (((K.toCycles (n + 1) n).app T).hom z) = ((K.d (n + 1) n).app T).hom z := by
    intro z
    change ((K.toCycles (n + 1) n ≫ K.iCycles n).app T).hom z = _
    rw [K.toCycles_i]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (exact_bdy K n T) y h
    exact ⟨z, (ti z).symm.trans (congrArg _ hz)⟩
  · rintro ⟨z, hz⟩
    rw [← ti] at hz
    rw [← iCyc_inj K n T hz]
    change ((K.toCycles (n + 1) n ≫ K.homologyπ n).app T).hom z = 0
    rw [K.toCycles_comp_homologyπ]; rfl

lemma nat_i (K : PCx R) (n : ℕ) {T U : Scheme.{0}ᵒᵖ} (g : T ⟶ U) (y) :
    ((K.X n).map g).hom (((K.iCycles n).app T).hom y) = ((K.iCycles n).app U).hom (((K.cycles n).map g).hom y) := by
  change (((K.iCycles n).app T ≫ (K.X n).map g)).hom y = (((K.cycles n).map g ≫ (K.iCycles n).app U)).hom y
  rw [(K.iCycles n).naturality]

lemma nat_π (K : PCx R) (n : ℕ) {T U : Scheme.{0}ᵒᵖ} (g : T ⟶ U) (y) :
    ((K.homology n).map g).hom (((K.homologyπ n).app T).hom y) = ((K.homologyπ n).app U).hom (((K.cycles n).map g).hom y) := by
  change (((K.homologyπ n).app T ≫ (K.homology n).map g)).hom y = (((K.cycles n).map g ≫ (K.homologyπ n).app U)).hom y
  rw [(K.homologyπ n).naturality]

lemma cm_i {K L : PCx R} (φ : K ⟶ L) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((L.iCycles n).app T).hom (((HomologicalComplex.cyclesMap φ n).app T).hom y) =
      ((φ.f n).app T).hom (((K.iCycles n).app T).hom y) := by
  change ((HomologicalComplex.cyclesMap φ n ≫ L.iCycles n).app T).hom y = ((K.iCycles n ≫ φ.f n).app T).hom y
  rw [HomologicalComplex.cyclesMap_i]

lemma hm_π {K L : PCx R} (φ : K ⟶ L) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((HomologicalComplex.homologyMap φ n).app T).hom (((K.homologyπ n).app T).hom y) =
      ((L.homologyπ n).app T).hom (((HomologicalComplex.cyclesMap φ n).app T).hom y) := by
  change ((K.homologyπ n ≫ HomologicalComplex.homologyMap φ n).app T).hom y =
    ((HomologicalComplex.cyclesMap φ n ≫ L.homologyπ n).app T).hom y
  rw [HomologicalComplex.homologyπ_naturality]

end HomLocPf

open HomLocPf in
theorem LeafHomLoc_of : LeafHomLoc := by
  intro R _ K L φ n hinj hsurj
  refine ⟨⟨fun {X} a b h => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · change ((HomologicalComplex.homologyMap φ n).app X).hom a = ((HomologicalComplex.homologyMap φ n).app X).hom b at h
    obtain ⟨y, hy⟩ := π_surj K n X (a - b)
    have hb : Bdy L n X (((φ.f n).app X).hom (((K.iCycles n).app X).hom y)) := by
      rw [← cm_i, ← π_zero_iff, ← hm_π, hy, map_sub, h, sub_self]
    obtain ⟨S, hS, hSx⟩ := hinj X _ (cyc_i K n X y) hb
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V f hf
    rw [Presheaf.equalizerSieve_apply]
    change ((K.homology n).map f.op).hom a = ((K.homology n).map f.op).hom b
    rw [← sub_eq_zero, ← map_sub, ← hy, nat_π, π_zero_iff, ← nat_i]
    exact hSx f hf
  · obtain ⟨y, rfl⟩ := π_surj L n _ s
    obtain ⟨S, hS, hSx⟩ := hsurj (op U) _ (cyc_i L n _ y)
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V f hf
    obtain ⟨x', hx', hb⟩ := hSx f hf
    obtain ⟨y', rfl⟩ := lift_cyc K n _ x' hx'
    refine ⟨((K.homologyπ n).app (op V)).hom y', ?_⟩
    change ((HomologicalComplex.homologyMap φ n).app (op V)).hom (((K.homologyπ n).app (op V)).hom y') =
      ((L.homology n).map f.op).hom (((L.homologyπ n).app (op U)).hom y)
    rw [hm_π, nat_π, ← sub_eq_zero, ← map_sub, π_zero_iff, map_sub, cm_i, ← nat_i]
    exact hb

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def EtaleOpenCovSieve : Prop := ∀ (T : Scheme.{0}) (S : Sieve T),
  (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ S V.ι) → S ∈ Scheme.etaleTopology.{0} T

def EtaleAugInjAt : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ)
    (T : Scheme.{0}ᵒᵖ) (x : ((((chainsP R).obj (hoc (D ⋙ yoneda))).X n).obj T)),
    Cyc _ n T x → Bdy _ n T ((((chainsP R).map (aug _ hc)).f n).app T |>.hom x) →
    ∀ t : T.unop, ∃ V : T.unop.Opens, t ∈ V ∧
      Bdy _ n (op (V : Scheme.{0})) (((((chainsP R).obj (hoc (D ⋙ yoneda))).X n).map V.ι.op).hom x)

theorem bdy_res {R : Type} [CommRing R] (K : PCx R) (n : ℕ) {U V : Scheme.{0}} (g : V ⟶ U) (x : (K.X n).obj (op U))
    (h : Bdy K n (op U) x) : Bdy K n (op V) (((K.X n).map g.op).hom x) := by
  obtain ⟨y, rfl⟩ := h
  refine ⟨((K.X (n + 1)).map g.op).hom y, ?_⟩
  have := (K.d (n + 1) n).naturality g.op
  exact (ConcreteCategory.congr_hom this y).symm.trans rfl |>.symm ▸ rfl

def bdySieve {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}) (x : (K.X n).obj (op T)) : Sieve T where
  arrows U f := Bdy K n (op U) (((K.X n).map f.op).hom x)
  downward_closed {U V} f hf g := by
    have e : ((K.X n).map (g ≫ f).op).hom x = ((K.X n).map g.op).hom (((K.X n).map f.op).hom x) := by
      rw [op_comp, Functor.map_comp]; rfl
    rw [e]; exact bdy_res K n g _ hf

theorem EtaleAugInj_of_openCovSieve (hc0 : EtaleOpenCovSieve) (ha : EtaleAugInjAt) : LeafAugInj := by
  intro J _ D X c ho hcov hdir hc R _ n T x hx hb
  refine ⟨bdySieve _ n T.unop x, hc0 _ _ fun t => ?_, fun U f hf => hf⟩
  obtain ⟨V, hV, h⟩ := ha J D X c ho hcov hdir hc R n T x hx hb t
  exact ⟨V, hV, h⟩

theorem etaleOpenCovSieve : EtaleOpenCovSieve := by
  intro T S h
  choose V hV hS using h
  apply Scheme.zariskiTopology_le_etaleTopology
  rw [Scheme.zariskiTopology, Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers T (fun t => (V t : Scheme.{0})) (fun t => (V t).ι)
    (fun x => ⟨x, ⟨x, hV x⟩, by simp⟩), ?_⟩
  rintro Y g ⟨i⟩
  exact hS i

theorem EtaleAugInj_of_augInjAt (ha : EtaleAugInjAt) : LeafAugInj := EtaleAugInj_of_openCovSieve etaleOpenCovSieve ha

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem span_range_mul_span_singleton {A : Type} [CommRing A] {r : ℕ} (x : Fin r → A) (f : A) :
    Ideal.span (Set.range x) * Ideal.span {f} = Ideal.span (Set.range (fun k => x k * f)) := by
  rw [Ideal.span_mul_span', Set.mul_singleton, ← Set.range_comp]
  rfl

theorem OffContLoc_of : OffContLoc := by
  intro _ r hN q A B _ _ φ x f hq J _ _ D s t hc he n i
  rw [span_range_mul_span_singleton]
  exact hN q φ (fun k => x k * f) hq J D s t hc he n i

end LateralTheory.CohomologicalPurity
end
end
