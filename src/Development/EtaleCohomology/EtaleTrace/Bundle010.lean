module

public import Development.EtaleCohomology.EtaleTrace.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

variable {k : Type} [Field k] {N : ℕ}

instance isIso_stalkMap_ι (X : Scheme.{0}) (U : X.Opens) (x : U) : IsIso (U.ι.stalkMap x) :=
  (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _

lemma pn_cover (y : PN (k := k) N) : ∃ i : Fin (N + 1), y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (X i) := by
  have htop := Proj.iSup_basicOpen_eq_top' (homogeneousSubmodule (Fin (N + 1)) k) (fun i : Fin (N + 1) => (X i : MvPolynomial (Fin (N + 1)) k))
    (fun i => ⟨1, (isHomogeneous_X k i)⟩) (by
      rw [eq_top_iff]
      rintro p -
      induction p using MvPolynomial.induction_on with
      | C c =>
        exact Subalgebra.algebraMap_mem _ (⟨C c, isHomogeneous_C _ c⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add p q hp hq => exact add_mem hp hq
      | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩))
  have : y ∈ (⊤ : (PN (k := k) N).Opens) := trivial
  rw [← htop] at this
  exact TopologicalSpace.Opens.mem_iSup.1 this

lemma pn_nbhd (y : PN (k := k) N) (W : (PN (k := k) N).Opens) (hy : y ∈ W) :
    ∃ n, 0 < n ∧ ∃ F ∈ homogeneousSubmodule (Fin (N + 1)) k n,
      y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) F ∧
      Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) F ≤ W := by
  obtain ⟨_, ⟨f, rfl⟩, hyf, hfW⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Proj.isBasis_basicOpen (homogeneousSubmodule (Fin (N + 1)) k))) hy
  rw [Proj.basicOpen_eq_iSup_proj] at hyf
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hyf
  obtain ⟨i, hi⟩ := pn_cover y
  refine ⟨1 + j, by omega, X i * GradedRing.proj (homogeneousSubmodule (Fin (N + 1)) k) j f,
    SetLike.mul_mem_graded (isHomogeneous_X k i) ?_, ?_, ?_⟩
  · rw [GradedRing.proj_apply]; exact Submodule.coe_mem _
  · rw [Proj.basicOpen_mul]; exact ⟨hi, hj⟩
  · refine le_trans ?_ hfW
    rw [Proj.basicOpen_mul, Proj.basicOpen_eq_iSup_proj _ f]
    exact inf_le_right.trans (le_iSup (fun i => Proj.basicOpen _ (GradedRing.proj _ i f)) j)

lemma genOn_value {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (w : Fin (N + 1) → X.functionField)
    (U : X.Opens) (πU : U.toScheme ⟶ PN (k := k) N) (hG : GenOn p w U πU) (hη : genericPoint X ∈ U)
    {n : ℕ} (hn : 0 < n) (F : MvPolynomial (Fin (N + 1)) k) (hF : F ∈ homogeneousSubmodule (Fin (N + 1)) k n)
    (hy : πU ⟨genericPoint X, hη⟩ ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) F)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n)) :
    (πU.stalkMap ⟨genericPoint X, hη⟩ ≫ inv (U.ι.stalkMap ⟨genericPoint X, hη⟩)).hom
      ((PN (k := k) N).presheaf.germ _ _ hy (Proj.awayToSection _ F (HomogeneousLocalization.Away.mk _ hF m g hg))) =
      eval₂ (kHom p) w g / eval₂ (kHom p) w F ^ m := by
  have hy' : (⟨genericPoint X, hη⟩ : U) ∈ πU ⁻¹ᵁ Proj.basicOpen _ F := hy
  obtain ⟨h1, h2⟩ := hG hη n hn F hF
  have hF0 : eval₂ (kHom p) w F ≠ 0 := h1.1 hy'
  have e := h2 m g hg hy'
  set ψ := U.ι.stalkMap ⟨genericPoint X, hη⟩
  have hinv : ∀ z, (inv ψ).hom (ψ.hom z) = z := fun z => by
    show (ψ ≫ inv ψ).hom z = z
    rw [IsIso.hom_inv_id]; rfl
  have key := Scheme.Hom.germ_stalkMap_apply πU (Proj.basicOpen _ F) ⟨genericPoint X, hη⟩ hy
    (Proj.awayToSection _ F (HomogeneousLocalization.Away.mk _ hF m g hg))
  rw [CommRingCat.hom_comp, RingHom.comp_apply, key]
  refine (eq_div_iff (G₀ := X.functionField) (pow_ne_zero _ hF0)).2 ?_
  calc _ = (inv ψ).hom (U.toScheme.presheaf.germ _ ⟨genericPoint X, hη⟩ hy' (πU.app _
          (Proj.awayToSection _ F (HomogeneousLocalization.Away.mk _ hF m g hg))) *
        ψ.hom (eval₂ (kHom p) w F) ^ m) := by rw [map_mul, map_pow, hinv]; rfl
    _ = (inv ψ).hom (ψ.hom (eval₂ (kHom p) w g)) := congrArg _ e
    _ = _ := hinv _

lemma spec_ext {Y : Scheme.{0}} {R : CommRingCat.{0}} (y y' : Y) (hyy : y = y')
    (φ : Y.presheaf.stalk y ⟶ R) (φ' : Y.presheaf.stalk y' ⟶ R)
    (h : ∀ (W : Y.Opens) (hy : y ∈ W) (hy' : y' ∈ W) (s : Γ(Y, W)),
      φ.hom (Y.presheaf.germ W y hy s) = φ'.hom (Y.presheaf.germ W y' hy' s)) :
    Spec.map φ ≫ Y.fromSpecStalk y = Spec.map φ' ≫ Y.fromSpecStalk y' := by
  subst hyy
  congr 2
  apply TopCat.Presheaf.stalk_hom_ext
  intro W hy
  ext s
  exact h W hy hy s

lemma gU_eq {X : Scheme.{0}} (U : X.Opens) (Y : Scheme.{0}) (πU : U.toScheme ⟶ Y) (x : X) (hx : x ∈ U) :
    U.fromSpecStalkOfMem x hx ≫ πU =
      Spec.map (πU.stalkMap ⟨x, hx⟩ ≫ inv (U.ι.stalkMap ⟨x, hx⟩)) ≫ Y.fromSpecStalk (πU ⟨x, hx⟩) := by
  rw [Scheme.Opens.fromSpecStalkOfMem, Spec.map_comp]
  simp only [Category.assoc]
  have := Scheme.SpecMap_stalkMap_fromSpecStalk πU (x := (⟨x, hx⟩ : U.toScheme))
  erw [this]
  rfl

lemma transfer {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (w : Fin (N + 1) → X.functionField)
    (U U' : X.Opens) (πU : U.toScheme ⟶ PN (k := k) N) (πU' : U'.toScheme ⟶ PN (k := k) N)
    (hG : GenOn p w U πU) (hG' : GenOn p w U' πU') (hη : genericPoint X ∈ U) (hη' : genericPoint X ∈ U')
    {n : ℕ} (hn : 0 < n) (F : MvPolynomial (Fin (N + 1)) k) (hF : F ∈ homogeneousSubmodule (Fin (N + 1)) k n)
    (hy : πU ⟨genericPoint X, hη⟩ ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) F) :
    πU' ⟨genericPoint X, hη'⟩ ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) F :=
  (hG' hη' n hn F hF).1.2 ((hG hη n hn F hF).1.1 hy)

lemma pt_eq {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (w : Fin (N + 1) → X.functionField)
    (U U' : X.Opens) (πU : U.toScheme ⟶ PN (k := k) N) (πU' : U'.toScheme ⟶ PN (k := k) N)
    (hG : GenOn p w U πU) (hG' : GenOn p w U' πU') (hη : genericPoint X ∈ U) (hη' : genericPoint X ∈ U') :
    πU ⟨genericPoint X, hη⟩ = πU' ⟨genericPoint X, hη'⟩ := by
  refine Inseparable.eq (inseparable_iff_forall_isOpen.2 fun s hs => ⟨fun h => ?_, fun h => ?_⟩)
  · obtain ⟨n, hn, F, hF, hyF, hFW⟩ := pn_nbhd _ ⟨s, hs⟩ h
    exact hFW (transfer p w U U' πU πU' hG hG' hη hη' hn F hF hyF)
  · obtain ⟨n, hn, F, hF, hyF, hFW⟩ := pn_nbhd _ ⟨s, hs⟩ h
    exact hFW (transfer p w U' U πU' πU hG' hG hη' hη hn F hF hyF)

lemma germ_agree {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (w : Fin (N + 1) → X.functionField)
    (U U' : X.Opens) (πU : U.toScheme ⟶ PN (k := k) N) (πU' : U'.toScheme ⟶ PN (k := k) N)
    (hG : GenOn p w U πU) (hG' : GenOn p w U' πU') (hη : genericPoint X ∈ U) (hη' : genericPoint X ∈ U')
    (W : (PN (k := k) N).Opens) (hy : πU ⟨genericPoint X, hη⟩ ∈ W) (hy' : πU' ⟨genericPoint X, hη'⟩ ∈ W) (s : Γ(PN (k := k) N, W)) :
    (πU.stalkMap ⟨genericPoint X, hη⟩ ≫ inv (U.ι.stalkMap ⟨genericPoint X, hη⟩)).hom ((PN (k := k) N).presheaf.germ W _ hy s) =
    (πU'.stalkMap ⟨genericPoint X, hη'⟩ ≫ inv (U'.ι.stalkMap ⟨genericPoint X, hη'⟩)).hom
      ((PN (k := k) N).presheaf.germ W _ hy' s) := by
  obtain ⟨n, hn, F, hF, hyF, hFW⟩ := pn_nbhd _ W hy
  have hyF' := transfer p w U U' πU πU' hG hG' hη hη' hn F hF hyF
  rw [← (PN (k := k) N).presheaf.germ_res_apply (homOfLE hFW) _ hyF s,
    ← (PN (k := k) N).presheaf.germ_res_apply (homOfLE hFW) _ hyF' s]
  set t := (PN (k := k) N).presheaf.map (homOfLE hFW).op s
  have ht : Proj.awayToSection _ F ((Proj.basicOpenIsoAway _ F hF hn).inv t) = t := by
    show ((Proj.basicOpenIsoAway _ F hF hn).inv ≫ (Proj.basicOpenIsoAway _ F hF hn).hom) t = t
    rw [Iso.inv_hom_id]; rfl
  obtain ⟨m, g, hg, hmk⟩ := HomogeneousLocalization.Away.mk_surjective _ hF ((Proj.basicOpenIsoAway _ F hF hn).inv t)
  rw [← ht, ← hmk, genOn_value p w U πU hG hη hn F hF hyF m g hg, genOn_value p w U' πU' hG' hη' hn F hF hyF' m g hg]

theorem GenOnAgree_of : GenOnAgree := by
  intro k _ X _ p N w U U' πU πU' hG hG'
  by_cases hE : IsEmpty ↥(pullback U.ι U'.ι : Scheme.{0})
  · exact isInitialOfIsEmpty.hom_ext _ _
  rw [not_isEmpty_iff] at hE
  obtain ⟨z⟩ := hE
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨_, trivial, (pullback.fst U.ι U'.ι z).2⟩
  have hη' : genericPoint X ∈ U' :=
    ((genericPoint_spec X).mem_open_set_iff U'.isOpen).2 ⟨_, trivial, (pullback.snd U.ι U'.ι z).2⟩
  let ι := pullback.lift (U.fromSpecStalkOfMem _ hη) (U'.fromSpecStalkOfMem _ hη')
    (by rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι])
  have : IsReduced (pullback U.ι U'.ι : Scheme.{0}) := isReduced_of_isOpenImmersion (pullback.fst U.ι U'.ι ≫ U.ι)
  have : IsDominant ι := by
    constructor
    let e := pullback.fst U.ι U'.ι ≫ U.ι
    have he : Topology.IsEmbedding e.base := e.isOpenEmbedding.isEmbedding
    let c : Spec (X.presheaf.stalk (genericPoint X)) := IsLocalRing.closedPoint _
    have hc : e (ι c) = genericPoint X := by
      have : ι ≫ e = X.fromSpecStalk (genericPoint X) := by
        show ι ≫ pullback.fst _ _ ≫ U.ι = _
        rw [pullback.lift_fst_assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
      rw [show e (ι c) = (ι ≫ e) c from rfl, this]
      exact Scheme.fromSpecStalk_closedPoint
    refine Dense.mono (Set.singleton_subset_iff.2 (Set.mem_range_self c)) ?_
    rw [dense_iff_closure_eq, he.closure_eq_preimage_closure_image, Set.image_singleton]
    erw [hc, (genericPoint_spec X).def]
    rfl
  refine ext_of_isDominant ι ?_
  rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, gU_eq, gU_eq]
  exact spec_ext _ _ (pt_eq p w U U' πU πU' hG hG' hη hη') _ _
    (fun W hy hy' s => germ_agree p w U U' πU πU' hG hG' hη hη' W hy hy' s)

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem homog_div_mem {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K)
    (i : Fin (N + 1)) (_hi : w i ≠ 0) (R : Subring K) (hκ : ∀ c, κ c ∈ R) (hw : ∀ j, w j / w i ∈ R)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g.IsHomogeneous m) : eval₂ κ w g / w i ^ m ∈ R := by
  rw [eval₂_eq, Finset.sum_div]
  refine Subring.sum_mem _ fun d hd => ?_
  have hdeg : ∑ j, d j = m := by
    rw [← hg (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have : (κ (AddMonoidAlgebra.coeff g d) * ∏ j, w j ^ d j) / w i ^ m = κ (AddMonoidAlgebra.coeff g d) * ∏ j, (w j / w i) ^ d j := by
    rw [mul_div_assoc]; congr 1
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  have hsupp : ∏ j ∈ d.support, w j ^ d j = ∏ j, w j ^ d j :=
    Finset.prod_subset (Finset.subset_univ _) (fun j _ hj => by simp [Finsupp.notMem_support_iff.mp hj])
  rw [hsupp, this]
  exact Subring.mul_mem _ (hκ _) (Subring.prod_mem _ fun j _ => Subring.pow_mem _ (hw j) _)

def chartVal {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K) (i : Fin (N + 1))
    (hi : w i ≠ 0) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* K :=
  (IsLocalization.Away.lift (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) (g := eval₂Hom κ w)
    (by simpa using hi.isUnit)).comp
    (algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)))

theorem chartVal_mk {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K)
    (i : Fin (N + 1)) (hi : w i ≠ 0)
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)) :
    chartVal κ w i hi (HomogeneousLocalization.Away.mk _ hx m g hg) = eval₂ κ w g / w i ^ m := by
  simp only [chartVal, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [coe_eval₂Hom, eval₂_pow, eval₂_X]
  rw [mul_div_cancel₀ _ (pow_ne_zero _ hi)]

def SectOfLoc : Prop := ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (R : Subring X.functionField),
  (∀ z ∈ R, ∀ y ∈ U, z ∈ loc X y) →
  ∃ φ : R →+* Γ(X, U), ∀ (z : R) (y : X) (hy : y ∈ U),
    algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy (φ z)) = z

theorem ChartRing_of (h : SectOfLoc) : ChartRing := by
  intro k _ X _ p N w i hi U hU hx
  let ψ := chartVal (kHom p) w i hi
  have hR : ∀ z ∈ ψ.range, ∀ y ∈ U, z ∈ loc X y := by
    rintro _ ⟨a, rfl⟩ y hy
    obtain ⟨m, g, hg, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hx a
    rw [chartVal_mk]
    have hg' : g.IsHomogeneous m := by
      simpa using (mem_homogeneousSubmodule _ _).1 hg
    exact homog_div_mem (kHom p) w i hi (loc X y) (fun c => kHom_mem_loc p y c) (fun j => hU y hy j) m g hg'
  obtain ⟨φ, hφ⟩ := h X U ψ.range hR
  refine ⟨φ.comp ψ.rangeRestrict, fun y hy m g hg => ?_⟩
  rw [RingHom.comp_apply, hφ]
  exact chartVal_mk (kHom p) w i hi hx m g hg

theorem GenOutChart_of_sect (h1 : SectOfLoc) (h2 : ChartGen) : GenOutChart :=
  GenOutChart_of (ChartRing_of h1) h2

end LateralTheory.EtaleTrace.Cov
end
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem etaleOverBasic : EtaleOverBasic := by
  intro X P π U hU hU' a H
  have hle : π ⁻¹ᵁ P.basicOpen a ≤ π ⁻¹ᵁ U := π.preimage_mono (P.basicOpen_le a)
  have key : RingHom.Etale (π.app (P.basicOpen a)).hom := by
    letI := (π.app U).hom.toAlgebra
    letI : Algebra Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    letI : Algebra Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app _).hom.toAlgebra
    letI : Algebra Γ(P, U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    haveI : IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(P, U) Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      show (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom =
        (P.presheaf.map (homOfLE (P.basicOpen_le a)).op ≫ π.app (P.basicOpen a)).hom
      rw [π.naturality]; rfl
    have hA : IsLocalization.Away a Γ(P, P.basicOpen a) := hU.isLocalization_basicOpen a
    have gen : ∀ (W : X.Opens) (e : W ≤ π ⁻¹ᵁ U), W = X.basicOpen (π.app U a) →
        @IsLocalization.Away _ _ (π.app U a) Γ(X, W) _ (X.presheaf.map (homOfLE e).op).hom.toAlgebra := by
      rintro W e rfl; exact hU'.isLocalization_basicOpen _
    exact H _ _ hA (gen _ hle (π.preimage_basicOpen a))
  haveI : IsAffine (P.basicOpen a).toScheme := hU.basicOpen a
  haveI : IsAffine (π ⁻¹ᵁ P.basicOpen a).toScheme := by
    have := hU'.basicOpen (π.app U a); rw [← π.preimage_basicOpen a] at this; exact this
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
  have hW : (P.basicOpen a).ι ''ᵁ ⊤ = P.basicOpen a := by simp
  have gen2 : ∀ (W : P.Opens) (T : X.Opens) (h : T = π ⁻¹ᵁ W), W = P.basicOpen a →
      RingHom.Etale (π.app W ≫ X.presheaf.map (eqToHom h).op).hom := by
    rintro W T h rfl
    subst h
    simpa using key
  exact gen2 _ _ _ hW

end LateralTheory.EtaleTrace.Cov
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

theorem tz_isUnit_ι (X : Scheme.{0}) (f : Γ(X, ⊤)) : IsUnit ((X.basicOpen f).ι.appTop.hom f) := by
  have h := RingedSpace.isUnit_res_basicOpen X.toRingedSpace f
  rw [Scheme.Opens.ι_appTop]
  have e1 : (X.basicOpen f).ι ''ᵁ ⊤ = X.basicOpen f := by simp
  have key : ∀ (W : X.Opens) (_ : W = X.basicOpen f) (hle : W ≤ ⊤), IsUnit ((X.presheaf.map (homOfLE hle).op).hom f) := by
    rintro W rfl hle
    exact h
  exact key _ e1 _

theorem tz_idem_one {A : Type} [CommRing A] {x : A} (h : IsIdempotentElem x) (hu : IsUnit x) : x = 1 := by
  obtain ⟨u, rfl⟩ := hu
  have := congrArg (· * ((u⁻¹ : Aˣ) : A)) h.eq
  simpa [mul_assoc] using this

theorem splitLoc : SplitLoc := by
  intro U n e he hs
  let W : Fin n → U.Opens := fun i => U.basicOpen (e i)
  have hW : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)
    rw [TopologicalSpace.Opens.mem_iSup]
    by_contra hx
    push Not at hx
    have hm : ∀ i, U.presheaf.germ ⊤ x trivial (e i) ∈ IsLocalRing.maximalIdeal (U.presheaf.stalk x) := fun i =>
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 ((Scheme.mem_basicOpen_top _ _ x).not.1 (hx i)))
    have hsum := Ideal.sum_mem (IsLocalRing.maximalIdeal _) (t := Finset.univ) (fun i _ => hm i)

    rw [← map_sum, hs, map_one] at hsum
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 hsum)
  let 𝒰 := U.openCoverOfIsOpenCover W hW
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, ?_, ?_⟩
  · exact Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰)
  · rintro V g ⟨Y, h, f, ⟨i⟩, rfl⟩
    let j : Fin n := i
    refine ⟨j, ?_⟩
    have h1 : (W j).ι.appTop.hom (e i) = 1 := tz_idem_one ((he j).map _) (tz_isUnit_ι U (e j))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    change h.appTop.hom ((W j).ι.appTop.hom (e j)) = 1
    rw [h1]; exact map_one _

theorem TwZero_of_split (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hS : PrimSplit) : TwZero :=
  TwZero_of hTw hS splitLoc

end LateralTheory.EtaleTrace
end
end
