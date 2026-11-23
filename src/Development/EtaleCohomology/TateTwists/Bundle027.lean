module

import Development.EtaleCohomology.EtaleSheaves.KummerSequence.TwLocGenPfSec
public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle006
public import Development.EtaleCohomology.TateTwists.Bundle024
public import Development.EtaleCohomology.TateTwists.Bundle013
public import Development.EtaleCohomology.TateTwists.Bundle022
public import Development.EtaleCohomology.TateTwists.Bundle020
public import Development.EtaleCohomology.TateTwists.Bundle007
public import Development.EtaleCohomology.TateTwists.Bundle019
public import Development.EtaleCohomology.TateTwists.Bundle010
public import Development.EtaleCohomology.TateTwists.Bundle014
public import Development.EtaleCohomology.TateTwists.Bundle023
public import Development.EtaleCohomology.TateTwists.Bundle016
public import Development.EtaleCohomology.TateTwists.Bundle025
public import Development.EtaleCohomology.TateTwists.Bundle003
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

theorem ZarPow_of (hA : AlgPow) : ZarPow := by
  apply LateralTheory.E.H2CurveOrder.TwLocGenPfSec.ZarPow_of <;> assumption

theorem TwSecLoc_of_alg (hA : AlgPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := TwSecLoc_of (ZarPow_of hA)

end LateralTheory.EtaleFoundations.TwSecLocPf
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.cupflip_ev_ext_pf : LateralTheory.EtaleFoundations.cupflip_ev_ext := by
  intro R _ E I n α β hab
  refine Cochain.ext _ _ fun p q hpq => ?_
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    have key : (chainsXIso R E N).inv ≫ α.v _ q hpq = (chainsXIso R E N).inv ≫ β.v _ q hpq := by
      refine (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R _ _).2.1 _ _ fun U x => ?_
      exact hab N q hpq U x
    simpa using congrArg (fun f => (chainsXIso R E N).hom ≫ f) key
  · have := (LateralTheory.Fin.EtaleSimplicialChainsFreeDescription.intersectionNumber_baseChange R).1 E
    have hz : IsZero (((chains R).obj E).X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    exact hz.eq_of_src _ _

namespace LateralTheory.EtaleFoundations

theorem ev_res' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  have h3 := (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R (E.obj (op (SimplexCategory.mk p))) (I.X s)).2.2.1 V U g x
  unfold ev
  rw [show Sx.res g x = (E.obj (op (SimplexCategory.mk p))).map g.op x from rfl, ← h3]
  have := congrArg (fun f => (ModuleCat.Hom.hom f) (freeGen R (E.obj (op (SimplexCategory.mk p))) U x))
    (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)
  simpa using this.symm

theorem along_res' {E : Spc} {p N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.along θ).res g = (x.res g).along θ := by
  unfold Sx.along Sx.res
  exact (NatTrans.naturality_apply (E.map θ.op) g.op x).symm

theorem cupflip_eta_mk_pf : cupflip_eta_mk := by
  intro h _ R _ I J K μ E n m k hk α β
  obtain ⟨η, hη⟩ := LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation.intersectionNumber_baseChange R (E := E) (I := K) (n := k - 1)
    (fun N s _ U x => phi μ hk α β x s (h N)) (by
      intro N s hs V U g x

      simp only [phi, Finsupp.sum, Sec.res, map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      unfold phiT
      split_ifs with hw
      · rw [map_zsmul]
        have := μ.nat g _ _ _ (by omega : -(z.1 : ℤ) + n + (-(z.2.1 : ℤ) + m) = s)
          (ev α z.1 _ rfl U (x.along z.2.2.1)) (ev β z.2.1 _ rfl U (x.along z.2.2.2))
        simp only [Sec.res] at this
        have ea := ev_res' α _ _ rfl g (x.along z.2.2.1)
        have eb := ev_res' β _ _ rfl g (x.along z.2.2.2)
        rw [along_res'] at ea eb
        simp only [Sec.res] at ea eb
        rw [this, ea, eb]
      · simp)
  exact ⟨η, fun N s hs U x => hη N s hs U x⟩

end LateralTheory.EtaleFoundations

theorem LateralTheory.EtaleFoundations.cc_aw_flip_of (hst : LateralTheory.EtaleFoundations.cupflip_steen) (hdl : LateralTheory.EtaleFoundations.cupflip_eta_delta) :
    LateralTheory.EtaleFoundations.cc_aw_flip :=
  LateralTheory.EtaleFoundations.cupflip_aw_flip_of hst (LateralTheory.EtaleFoundations.cupflip_homotopy_of LateralTheory.EtaleFoundations.cupflip_ev_ext_pf
    LateralTheory.EtaleFoundations.cupflip_eta_mk_pf hdl)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem secmap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := rfl

theorem secmap_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun k => k.hom x) (φ.hom.naturality g.op)
  exact this.symm

noncomputable def pairPost {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    rw [← μ.nat g s t w h a b]
    exact secmap_res (u.f w) g _
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    have hc : Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) =
        Sec.map (u.f (w + 1)) (Sec.map (K.d w (w + 1)) (μ.mul U s t w h a b)) := by
      rw [secmap_comp, secmap_comp, u.comm]
    show Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = _
    rw [hc, μ.leibniz U s t w h a b]
    show Sec.map (u.f (w + 1)) _ = Sec.map (u.f (w + 1)) _ + _ • Sec.map (u.f (w + 1)) _
    rw [Sec.map, map_add (f := _), map_zsmul_unit]

def twpair_tens_univ_uniq : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u u' : K ⟶ K'), τ.Compat ν f g u → τ.Compat ν f g u' → u = u'

def twpair_tens_univ_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃ u : K ⟶ K', τ.Compat ν f g u

def twpair_tens_univ_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0

theorem pairPost_compat {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') :
    μ.Compat (pairPost μ u) (𝟙 I) (𝟙 J) u := by
  intro U s t w h a b
  rfl

theorem lift_comp_eq {R : Type} [CommRing R] {I J K I' J' K' : Cx R} (τ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u u' : K ⟶ K')
    (hu : τ.Compat ν f g u) (hu' : τ.Compat ν f g u') (V : Scheme.{0}) (w : ℤ) (x : Tens I J V w) :
    Sec.map (u.f w) (τ.lift V w x) = Sec.map (u'.f w) (τ.lift V w x) := by
  classical
  have key : ((u.f w).hom.app (op V)).hom ∘ₗ τ.lift V w = ((u'.f w).hom.app (op V)).hom ∘ₗ τ.lift V w := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    exact (hu V _ _ _ p.2 a b).trans (hu' V _ _ _ p.2 a b).symm
  exact congrArg (fun k => k x) key

theorem tens_univ_uniq_of (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) : twpair_tens_univ_uniq := by
  intro R _ I J K τ hτ I' J' K' ν f g u u' hu hu'
  ext w U y
  apply hsep R (K'.X w) U.unop
  refine TensLocbij.loc_mono (hτ.1 U.unop w y) ?_
  rintro V r ⟨x, hx⟩
  rw [secmap_res, secmap_res, ← hx]
  exact lift_comp_eq τ ν f g u u' hu hu' V w x

theorem sec_zero_of_isZero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have : Sec.map (𝟙 F) x = Sec.map (0 : F ⟶ F) x := by rw [h]
  exact this

theorem isZero_of_sec {R : Type} [CommRing R] {F : Shv R} (h : ∀ (U : Scheme.{0}) (x : Sec F U), x = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U y
  exact (h U.unop y).trans (h U.unop _).symm

theorem tens_univ_ge_of (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) : twpair_tens_univ_ge := by
  intro R _ I J K τ hτ hI hJ
  have hK : ∀ w : ℤ, w < 0 → IsZero (K.X w) := by
    intro w hw
    apply isZero_of_sec
    intro U y
    apply hsep R (K.X w) U
    refine TensLocbij.loc_mono (hτ.1 U w y) ?_
    rintro V r ⟨x, hx⟩
    rw [← hx]
    classical
    have hl : τ.lift V w = 0 := by
      apply DirectSum.linearMap_ext
      intro p
      apply TensorProduct.ext'
      intro a b
      simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.zero_apply]
      rcases lt_or_ge p.1.1 0 with hs | hs
      · rw [sec_zero_of_isZero (CochainComplex.isZero_of_isStrictlyGE I 0 p.1.1 hs) a, map_zero, LinearMap.zero_apply]
      · have ht : p.1.2 < 0 := by have := p.2; omega
        rw [sec_zero_of_isZero (CochainComplex.isZero_of_isStrictlyGE J 0 p.1.2 ht) b, map_zero]
    rw [hl, LinearMap.zero_apply]
    exact (map_zero _).symm
  exact ⟨fun i hi => hK i ((ComplexShape.notMem_range_embeddingUpIntGE_iff (p := 0) i).1 hi)⟩

theorem etale_sheaf_sections_separated_holds : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep := by
  intro R _ F U a b hab
  obtain ⟨S, hS, hP⟩ := hab
  have h1 : Presheaf.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property
  have h2 := (isSheaf_iff_isSheaf_of_type _ _).1 h1
  exact (h2 S hS).isSeparatedFor.ext fun V g hg => hP V g hg

def twpair_tens_univ_exdeg : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ), ∃ φ : K.X w ⟶ K'.X w, ∀ (U : Scheme.{0}) (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map φ (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

theorem tens_univ_ex_of (hdeg : twpair_tens_univ_exdeg) : twpair_tens_univ_ex := by
  intro R _ I J K τ hτ I' J' K' ν f g
  choose φ hφ using hdeg R τ hτ ν f g
  have hsep := etale_sheaf_sections_separated_holds
  refine ⟨⟨φ, ?_⟩, fun U s t w h a b => hφ w U s t h a b⟩
  rintro i j (hij : i + 1 = j)
  subst hij
  ext U y
  apply hsep R (K'.X (i + 1)) U.unop
  refine TensLocbij.loc_mono (hτ.1 U.unop i y) ?_
  rintro V r ⟨x, hx⟩
  show Sec.res r (Sec.map (φ i ≫ K'.d i (i + 1)) y) = Sec.res r (Sec.map (K.d i (i + 1) ≫ φ (i + 1)) y)
  rw [secmap_res, secmap_res, ← hx]
  classical
  have key : ((K.d i (i + 1) ≫ φ (i + 1)).hom.app (op V)).hom ∘ₗ τ.lift V i =
      ((φ i ≫ K'.d i (i + 1)).hom.app (op V)).hom ∘ₗ τ.lift V i := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    have e1 : Sec.map (K.d i (i + 1) ≫ φ (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) =
        Sec.map (φ (i + 1)) (Sec.map (K.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b)) := rfl
    have e2 : Sec.map (φ i ≫ K'.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) =
        Sec.map (K'.d i (i + 1)) (Sec.map (φ i) (τ.mul V p.1.1 p.1.2 i p.2 a b)) := rfl
    change Sec.map (K.d i (i + 1) ≫ φ (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) = Sec.map (φ i ≫ K'.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b)
    have h1 := hφ (i + 1) V (p.1.1 + 1) p.1.2 (by have := p.2; omega) (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) b
    have h2 := hφ (i + 1) V p.1.1 (p.1.2 + 1) (by have := p.2; omega) a (Sec.map (J.d p.1.2 (p.1.2 + 1)) b)
    have hf : Sec.map (I'.d p.1.1 (p.1.1 + 1)) (Sec.map (f.f p.1.1) a) = Sec.map (f.f (p.1.1 + 1)) (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) := by
      rw [secmap_comp, secmap_comp, f.comm]
    have hg : Sec.map (J'.d p.1.2 (p.1.2 + 1)) (Sec.map (g.f p.1.2) b) = Sec.map (g.f (p.1.2 + 1)) (Sec.map (J.d p.1.2 (p.1.2 + 1)) b) := by
      rw [secmap_comp, secmap_comp, g.comm]
    rw [e1, e2, τ.leibniz, hφ i, ν.leibniz, hf, hg]
    simp only [Sec.map, map_add (f := _), map_zsmul_unit] at h1 h2 ⊢
    rw [h1, h2]
  exact (congrArg (fun k => k x) key).symm

theorem twpair_tens_univ_of (hdeg : twpair_tens_univ_exdeg) :
    LateralTheory.EtaleFoundations.twpair_tens_univ := by
  have hsep := etale_sheaf_sections_separated_holds
  have hex := tens_univ_ex_of hdeg
  intro R _ I J K τ hτ
  refine ⟨?_, tens_univ_ge_of hsep R τ hτ, fun u => ⟨pairPost τ u, pairPost_compat τ u⟩⟩
  intro I' J' K' ν f g
  obtain ⟨u, hu⟩ := hex R τ hτ ν f g
  exact ⟨u, hu, fun u' hu' => tens_univ_uniq_of hsep R τ hτ ν f g u' u hu' hu⟩

end LateralTheory.EtaleFoundations
end

section

namespace LateralTheory.Fin.EtaleComplexTensorPairingExists
theorem etale_tensor_product_sheaf_exists_of_components : LateralTheory.EtaleFoundations.EtaleSheafTensorComplexExists := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_tensor_complex_exists
theorem etale_tensor_product_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_complex_exists_of_sheaf_tensor_complex <;> first | exact etale_tensor_product_sheaf_exists_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := etale_tensor_product_exists_of_components
end LateralTheory.Fin.EtaleComplexTensorPairingExists
end

section

namespace LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
theorem etale_evaluation_map_basic_of_components : LateralTheory.EtaleFoundations.pp_ev_basic := by
  apply LateralTheory.EtaleFoundations.pp_ev_basic_of
theorem etale_cohomology_evaluation_mk : LateralTheory.EtaleFoundations.pp_ev_mk := by
  apply LateralTheory.EtaleFoundations.pp_ev_mk_of
theorem etale_cohomology_evaluation_connecting_hom : LateralTheory.EtaleFoundations.pp_ev_delta := by
  apply LateralTheory.EtaleFoundations.pp_ev_delta_of
theorem etale_torsion_cohomology_operation_spec : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  apply LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation <;> first | exact etale_evaluation_map_basic_of_components | exact etale_cohomology_evaluation_mk | exact etale_cohomology_evaluation_connecting_hom
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := etale_torsion_cohomology_operation_spec
end LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
end

section


open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.etale_steenrod_prism_homotopy_of_acyclic_alexander_whitney (hA : leaf_acyc) (hAW : leaf_aw) (hWA : leaf_wa) :
    LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy :=
  LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations hA steenrod_prism_chain_differential_squared_eq_zero_of_etale prism_boundary_map_square_zero_holds hAW hWA
end

section

namespace LateralTheory.Fin.EtaleTensorPairUniversalProperty
theorem etale_tensor_complex_degreewise_universal : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_pairing_degreewise_universal_of_sheafification
theorem etale_tensor_complex_universal_of_degreewise : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_tensor_universal_property_of_degreewise <;> first | exact etale_tensor_complex_degreewise_universal
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := etale_tensor_complex_universal_of_degreewise
end LateralTheory.Fin.EtaleTensorPairUniversalProperty
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations
namespace TTP

variable {R : Type} [CommRing R]

noncomputable section

abbrev dI (I : Cx R) (U : Scheme.{0}) (s : ℤ) : Sec (I.X s) U →ₗ[ULift.{1} R] Sec (I.X (s + 1)) U :=
  ((I.d s (s + 1)).hom.app (op U)).hom

theorem dI_dI (I : Cx R) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) : dI I U (s + 1) (dI I U s a) = 0 := by
  have h := congrArg (fun f => ((f.hom.app (op U)).hom a)) (I.d_comp_d s (s + 1) (s + 1 + 1))
  exact h.trans (by simp)

theorem dI_res (I : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s : ℤ) (a : Sec (I.X s) U) :
    dI I V s (((I.X s).obj.map g.op).hom a) = ((I.X (s + 1)).obj.map g.op).hom (dI I U s a) := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f a) ((I.d s (s + 1)).hom.naturality g.op)
  exact h

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) {q : ℤ × ℤ // q.1 + q.2 = w + 1}
        (fun q => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map (dI I U p.1.1) LinearMap.id) +
    ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) {q : ℤ × ℤ // q.1 + q.2 = w + 1}
        (fun q => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id (dI J U p.1.2)))

theorem dT_of (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s + 1, t), by omega⟩ (dI I U s a ⊗ₜ b) +
    (s.negOnePow : ℤ) • DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t + 1), by omega⟩ (a ⊗ₜ dI J U t b) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R), dT, DirectSum.toModule_lof]
  simp [DirectSum.lof_eq_of]

theorem dT_dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : (dT I J U (w + 1)).comp (dT I J U w) = 0 := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, LinearMap.zero_apply]
  rw [dT_of, map_add (f := _), map_zsmul, dT_of, dT_of]
  simp [dI_dI, Int.negOnePow_succ]

theorem res_of (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Tens.res (I := I) (J := J) g w (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) V ⊗[ULift.{1} R] Sec (J.X q.1.2) V)
      ⟨(s, t), h⟩ (((I.X s).obj.map g.op).hom a ⊗ₜ ((J.X t).obj.map g.op).hom b) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R), Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, DirectSum.lof_eq_of]

theorem res_id (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens.res (I := I) (J := J) (𝟙 U) w = LinearMap.id := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, LinearMap.id_apply]
  rw [res_of]
  simp

theorem res_comp (I J : Cx R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (w : ℤ) :
    Tens.res (I := I) (J := J) (f ≫ g) w = Tens.res f w ∘ₗ Tens.res g w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [res_of, res_of, res_of]
  simp

theorem dT_res (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [res_of, dT_of, dT_of, map_add (f := _), map_zsmul, res_of, res_of, dI_res, dI_res]

def PF (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    apply ModuleCat.hom_ext
    simp only [unop_id, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact res_id I J U.unop w
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [unop_comp, ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact res_comp I J g.unop f.unop w

def dN (I J : Cx R) (w : ℤ) : PF I J w ⟶ PF I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := by
    apply ModuleCat.hom_ext
    simp only [PF, ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact dT_res I J g.unop w

theorem dN_dN (I J : Cx R) (w : ℤ) : dN I J w ≫ dN I J (w + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext
  simp only [NatTrans.comp_app, dN, NatTrans.app_zero, ModuleCat.hom_zero]
  exact dT_dT I J U.unop w

def PC (I J : Cx R) : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ :=
  CochainComplex.of (fun w => PF I J w) (fun w => dN I J w) (fun w => dN_dN I J w)

def tensPre (I J : Cx R) : TensPre I J where
  P := PC I J
  e U w := LinearEquiv.refl (ULift.{1} R) (Tens I J U w)
  nat g w x := rfl
  leibniz U s t w h a b := by
    simp only [PC]
    rw [CochainComplex.of_d]
    exact (dT_of I J U s t w h a b).trans (congrArg (HAdd.hAdd _) (Units.smul_def _ _).symm)

end

end TTP

theorem tt_tens_pre_of : tt_tens_pre := fun _ _ I J => ⟨TTP.tensPre I J⟩

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_cup_alexanderWhitney_uniqueness_holds : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupCochainUnique := by
  intro R _ I J K μ E n m k hk α β γ γ' h h'
  exact LateralTheory.EtaleFoundations.AwExPf.ev_ext _ _ fun N w hw U x => (h N w hw U x).trans (h' N w hw U x).symm
end
