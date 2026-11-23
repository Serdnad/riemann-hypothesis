module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

section

namespace GlobalTheory

open MvPolynomial Finset

theorem clearDenominators {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K)
    (P D : ι → MvPolynomial τ K) :
    ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) →
      MvPolynomial.eval y M ≠ 0 ∧
      MvPolynomial.eval y G = MvPolynomial.eval y M *
        MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by
  classical
  set N := F.totalDegree
  refine ⟨∑ m ∈ F.support, C (F.coeff m) * ∏ i ∈ F.vars, (P i) ^ (m i) * (D i) ^ (N - m i),
    ∏ i ∈ F.vars, (D i) ^ N, fun y hy => ⟨?_, ?_⟩⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by rw [map_pow]; exact pow_ne_zero _ (hy i)
  · have hle : ∀ m ∈ F.support, ∀ i, m i ≤ N := fun m hm i =>
      (monomial_le_degreeOf i hm).trans (degreeOf_le_totalDegree F i)
    have hsub : ∀ m ∈ F.support, m.support ⊆ F.vars := fun m hm i hi =>
      (MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨m, hm, hi⟩

    rw [MvPolynomial.eval_eq (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F,
    map_prod, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [map_mul, eval_C, map_prod]
    rw [Finset.prod_subset (hsub m hm) (fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero])]
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow]
    have hd := hy i
    have hk := hle m hm i
    rw [div_pow, ← pow_sub_mul_pow (MvPolynomial.eval y (D i)) hk]
    field_simp

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem exists_eval₂_approx_maximalIdeal_pow_succ {A R : Type} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (hm : (maximalIdeal A).map φ = maximalIdeal R) (θ : R)
    (h1 : ∀ r : R, ∃ P : Polynomial A, r - Polynomial.eval₂ φ θ P ∈ maximalIdeal R)
    (n : ℕ) (x : R) (hx : x ∈ maximalIdeal R ^ n) :
    ∃ P : Polynomial A, Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ n ∧
      x - Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ (n + 1) := by
  have hpow : maximalIdeal R ^ n = (maximalIdeal A ^ n).map φ := by
    rw [Ideal.map_pow, hm]
  rw [hpow] at hx
  unfold Ideal.map at hx
  refine Submodule.span_induction (p := fun x _ => ∃ P : Polynomial A,
      Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ n ∧
      x - Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ (n + 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨Polynomial.C a, ?_, ?_⟩
    · rw [Polynomial.eval₂_C, hpow]; exact Ideal.mem_map_of_mem φ ha
    · simp
  · exact ⟨0, by simp, by simp⟩
  · rintro x y _ _ ⟨P, hP, hxP⟩ ⟨Q, hQ, hyQ⟩
    refine ⟨P + Q, ?_, ?_⟩
    · rw [Polynomial.eval₂_add]; exact add_mem hP hQ
    · have : x + y - Polynomial.eval₂ φ θ (P + Q) =
          (x - Polynomial.eval₂ φ θ P) + (y - Polynomial.eval₂ φ θ Q) := by
        rw [Polynomial.eval₂_add]; ring
      rw [this]; exact add_mem hxP hyQ
  · rintro r x _ ⟨P, hP, hxP⟩
    obtain ⟨Q, hQ⟩ := h1 r
    refine ⟨Q * P, ?_, ?_⟩
    · rw [Polynomial.eval₂_mul]; exact Ideal.mul_mem_left _ _ hP
    · have : r • x - Polynomial.eval₂ φ θ (Q * P) =
          r * (x - Polynomial.eval₂ φ θ P) +
            (r - Polynomial.eval₂ φ θ Q) * Polynomial.eval₂ φ θ P := by
        rw [Polynomial.eval₂_mul, smul_eq_mul]; ring
      rw [this]
      refine add_mem (Ideal.mul_mem_left _ _ hxP) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hQ hP

theorem exists_poly_sub_mem_maximalIdeal_pow : ∀ {A R : Type} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (φ : A →+* R), (maximalIdeal A).map φ = maximalIdeal R →
    ∀ θ : R, (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) →
    ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n := by
  intro A R _ _ _ _ φ hm θ h1 n r
  simp only [Polynomial.eval_map] at h1 ⊢
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨Q, -, hQ⟩ := exists_eval₂_approx_maximalIdeal_pow_succ φ hm θ h1 n _ hP
    refine ⟨P + Q, ?_⟩
    have : r - Polynomial.eval₂ φ θ (P + Q) =
        r - Polynomial.eval₂ φ θ P - Polynomial.eval₂ φ θ Q := by
      rw [Polynomial.eval₂_add]; ring
    rw [this]; exact hQ

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace GlobalTheory.LocalRingGeneralisation

theorem flat_fromSpecStalk (X : Scheme.{0}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have h₃ : Flat (IsAffineOpen.fromSpec hU) := inferInstance
  exact MorphismProperty.comp_mem @Flat _ _ this h₃

theorem isIso_stalkMap_fromSpecStalk (X : Scheme.{0}) (x : X) (y : Spec (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap y) := by
  have := flat_fromSpecStalk X x
  have hs : SurjectiveOnStalks (X.fromSpecStalk x) := inferInstance
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, (X.fromSpecStalk x).stalkMap_surjective y⟩
  have hl : IsLocalHom ((X.fromSpecStalk x).stalkMap y).hom := inferInstance
  have h := Flat.stalkMap (X.fromSpecStalk x) y
  algebraize [((X.fromSpecStalk x).stalkMap y).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk ((X.fromSpecStalk x) y))
    ((Spec (X.presheaf.stalk x)).presheaf.stalk y)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk ((X.fromSpecStalk x) y)) (B := (Spec (X.presheaf.stalk x)).presheaf.stalk y)
  exact FaithfulSMul.algebraMap_injective _ _

end GlobalTheory.LocalRingGeneralisation
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem residueField_map_finite_of_quasiFinite {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (h : f.QuasiFinite) :
    (IsLocalRing.ResidueField.map f).Finite := by
  algebraize [f]
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Algebra.QuasiFinite R (IsLocalRing.ResidueField S) :=
    Algebra.QuasiFinite.of_surjective_algHom (IsScalarTower.toAlgHom R S _)
      IsLocalRing.residue_surjective
  have : Algebra.QuasiFinite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    .of_restrictScalars R _ _
  have hfin : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Algebra.QuasiFinite.iff_of_isArtinianRing.mp this
  have heq : IsLocalRing.ResidueField.map f =
      algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  rw [heq]
  exact RingHom.finite_algebraMap.mpr hfin

theorem residueFieldMap_finite_of_locallyQuasiFinite {Y Z : Scheme.{0}} (g : Y ⟶ Z)
    [LocallyQuasiFinite g] (y : Y) : (g.residueFieldMap y).hom.Finite := by
  have hq : (g.stalkMap y).hom.QuasiFinite := g.quasiFiniteAt y
  exact residueField_map_finite_of_quasiFinite _ hq

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem app_injective_of_dense_range {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (W : Z.Opens) : Function.Injective (j.app W).hom := by
  intro a b hab
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  have h0 : j ⁻¹ᵁ Z.basicOpen (a - b) = ⊥ := by
    rw [Scheme.preimage_basicOpen, map_sub, hab, sub_self, Scheme.basicOpen_zero]
  by_contra hne
  obtain ⟨z, hz⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
  obtain ⟨x, hx1, ⟨y, rfl⟩⟩ := hj.inter_open_nonempty _ (Z.basicOpen (a - b)).isOpen ⟨z, hz⟩
  have : y ∈ j ⁻¹ᵁ Z.basicOpen (a - b) := hx1
  rw [h0] at this
  exact this

theorem app_res_eq {T Z : Scheme.{0}} (j : T ⟶ Z) {V W : Z.Opens} (i : V ⟶ W)
    (i' : j ⁻¹ᵁ V ⟶ j ⁻¹ᵁ W) (a : Γ(Z, W)) :
    j.app V (Z.presheaf.map i.op a) = T.presheaf.map i'.op (j.app W a) := by
  obtain rfl : i' = (Opens.map j.base).map i := Subsingleton.elim _ _
  have := congrArg (fun f => f.hom a) (j.naturality i.op)
  simpa using this

theorem glue_of_dense_openImmersion : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  intro T Z _ j _ hj U s hloc
  choose W hWU hmem h hh using hloc
  let Wf : U → Z.Opens := fun u => W u.1 u.2
  have hcover : U ≤ iSup Wf := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hmem x hx⟩
  obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' Wf U (fun u => homOfLE (hWU u.1 u.2)) hcover
    (fun u => h u.1 u.2) (by
      intro u v
      apply app_injective_of_dense_range j hj
      change j.app _ (Z.presheaf.map _ (h u.1 u.2)) = j.app _ (Z.presheaf.map _ (h v.1 v.2))
      rw [app_res_eq j _ (homOfLE (j.preimage_mono inf_le_left)),
        app_res_eq j _ (homOfLE (j.preimage_mono inf_le_right)), hh, hh]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  let g' : Γ(Z, U) := g
  have hg' : ∀ u : U, Z.presheaf.map (homOfLE (hWU u.1 u.2)).op g' = h u.1 u.2 := hg
  refine ⟨g', ?_⟩
  refine T.sheaf.eq_of_locally_eq' (fun u : U => j ⁻¹ᵁ Wf u) (j ⁻¹ᵁ U)
    (fun u => homOfLE (j.preimage_mono (hWU u.1 u.2))) ?_ _ _ ?_
  · intro x hx
    exact Opens.mem_iSup.2 ⟨⟨j x, hx⟩, hmem _ hx⟩
  · intro u
    have key : T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op (j.app U g') =
        T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op s := by
      rw [← app_res_eq j (homOfLE (hWU u.1 u.2)), hg' u, hh]
    exact key

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.RelDimFibCrit

end GlobalTheory.RelDimFibCrit

namespace GlobalTheory.RelDimFibCrit

open AlgebraicGeometry CategoryTheory Limits in
private lemma specMap_residueFieldMap_conj_eq_ofHom_map {R S : CommRingCat.{0}} (φ : R ⟶ S)
    (p : PrimeSpectrum S) :
    (Scheme.Spec.residueFieldIso R ((Spec.map φ) p)).inv ≫ (Spec.map φ).residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso S p).hom =
      CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) := by
  haveI : ((Spec.map φ) p).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have key : CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R ((Spec.map φ) p)).inv ≫ (Spec.map φ).residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso S p).hom =
      CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫
      CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) := by
    rw [reassoc_of% Scheme.Spec.algebraMap_residueFieldIso_inv]
    erw [Scheme.residue_residueFieldMap_assoc (Spec.map φ) p]
    erw [Scheme.Spec.residue_residueFieldIso_hom]
    erw [Scheme.Hom.germ_stalkMap_assoc]
    erw [Spec.germ_stalkMapIso_hom_assoc]
    erw [Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    erw [Ideal.ResidueField.map_algebraMap]
    rw [← IsScalarTower.algebraMap_apply]
  ext1
  apply Ideal.ResidueField.ringHom_ext
  exact congr_arg CommRingCat.Hom.hom key

open AlgebraicGeometry CategoryTheory Limits in
private lemma residueFieldCongr_hom_hom_comp {Y : Scheme.{0}} {a b : Y} {Z : CommRingCat.{0}}
    (h : a = b) (h' : b = a) (g : Y.residueField a ⟶ Z) :
    (Y.residueFieldCongr h).hom ≫ (Y.residueFieldCongr h').hom ≫ g = g := by
  subst h
  simp [Scheme.residueFieldCongr_refl]

open AlgebraicGeometry CategoryTheory Limits in
private lemma trdeg_le_of_ringEquiv {K L K' L' : Type} [CommRing K] [CommRing L] [CommRing K']
    [CommRing L'] [Nontrivial K'] [Algebra K L] [Algebra K' L'] (e₁ : K ≃+* K') (e₂ : L ≃+* L')
    (h : (algebraMap K' L').comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K L)) :
    Algebra.trdeg K L ≤ Algebra.trdeg K' L' :=
  ciSup_le' fun s ↦ (s.2.ringHom_of_comp_eq e₁ e₂ e₁.surjective e₂.injective h).cardinalMk_le_trdeg

open AlgebraicGeometry CategoryTheory Limits in
private lemma trdeg_eq_of_ringEquiv {K L K' L' : Type} [Field K] [CommRing L] [Field K']
    [CommRing L'] [Algebra K L] [Algebra K' L'] (e₁ : K ≃+* K') (e₂ : L ≃+* L')
    (h : (algebraMap K' L').comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K L)) :
    Algebra.trdeg K L = Algebra.trdeg K' L' := by
  refine le_antisymm (trdeg_le_of_ringEquiv e₁ e₂ h) (trdeg_le_of_ringEquiv e₁.symm e₂.symm ?_)
  ext a
  have := congr($h (e₁.symm a))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply] at this
  simp [this]


open AlgebraicGeometry CategoryTheory Limits in
theorem _root_.GlobalTheory.RelDimFibCrit.trdeg_affine {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (p : PrimeSpectrum Γ(X, V)) :
    @Algebra.trdeg (Y.residueField (f (hV.fromSpec p))) (X.residueField (hV.fromSpec p)) _ _
      (f.residueFieldMap (hV.fromSpec p)).hom.toAlgebra =
    @Algebra.trdeg (p.asIdeal.comap (f.appLE U V e).hom).ResidueField p.asIdeal.ResidueField _ _
      (Ideal.ResidueField.map _ p.asIdeal (f.appLE U V e).hom rfl).toAlgebra := by
  obtain ⟨p, rfl⟩ : ∃ p' : Spec Γ(X, V), p' = p := ⟨p, rfl⟩
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime (p : PrimeSpectrum Γ(X, V))
  set φ := f.appLE U V e
  haveI := hU.isOpenImmersion_fromSpec
  haveI := hV.isOpenImmersion_fromSpec
  have h₁ : hU.fromSpec ((Spec.map φ) p) = f (hV.fromSpec p) :=
    congr($(hU.SpecMap_appLE_fromSpec f hV e) p)
  set q : Spec Γ(Y, U) := (Spec.map φ) p
  let eL := (asIso (hV.fromSpec.residueFieldMap p) ≪≫
    Scheme.Spec.residueFieldIso _ p).commRingCatIsoToRingEquiv
  let eK := (Y.residueFieldCongr h₁.symm ≪≫ asIso (hU.fromSpec.residueFieldMap q) ≪≫
    Scheme.Spec.residueFieldIso _ q).commRingCatIsoToRingEquiv
  have hsq : (Y.residueFieldCongr h₁.symm).hom ≫ hU.fromSpec.residueFieldMap q ≫
      (Scheme.Spec.residueFieldIso _ q).hom ≫
        CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) =
      f.residueFieldMap (hV.fromSpec p) ≫ hV.fromSpec.residueFieldMap p ≫
        (Scheme.Spec.residueFieldIso _ p).hom := by
    erw [← specMap_residueFieldMap_conj_eq_ofHom_map]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc (hU.fromSpec.residueFieldMap q),
      ← Scheme.residueFieldMap_comp, ← Category.assoc (f.residueFieldMap _),
      ← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr (hU.SpecMap_appLE_fromSpec f hV e)]
    exact (congrArg _ (Category.assoc _ _ _)).trans (residueFieldCongr_hom_hom_comp _ _ _)
  refine @trdeg_eq_of_ringEquiv _ _ _ _ _ _ _ _ (RingHom.toAlgebra _) (RingHom.toAlgebra _) eK eL ?_
  ext a
  exact congr((CommRingCat.Hom.hom $hsq) a)

end GlobalTheory.RelDimFibCrit
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem integral_intervalIntegral_mul_right_curve {K : Type} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsMulRightInvariant] [IsProbabilityMeasure μ]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E]
    (c : ℝ → K) (hc : Continuous c) (g : K → E) (hg : Continuous g) :
    ∫ x, (∫ t in (0:ℝ)..1, g (x * c t)) ∂μ = ∫ x, g x ∂μ := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hg).isBounded.exists_norm_le
  have hcont : Continuous (Function.uncurry fun (x : K) (t : ℝ) => g (x * c t)) := by
    unfold Function.uncurry
    fun_prop
  have hint : Integrable (Function.uncurry fun (x : K) (t : ℝ) => g (x * c t))
      (μ.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Eventually.of_forall fun p => ?_)
    exact hC _ ⟨_, Set.mem_univ _, rfl⟩
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  rw [integral_integral_swap hint]
  simp_rw [integral_mul_right_eq_self g]
  simp

theorem norm_intervalIntegral_unit_sq_le (h : ℝ → ℂ) (hh : Continuous h) :
    ‖∫ t in (0:ℝ)..1, h t‖ ^ 2 ≤ ∫ t in (0:ℝ)..1, ‖h t‖ ^ 2 := by
  set a : ℝ := ∫ t in (0:ℝ)..1, ‖h t‖ with ha
  have h1 : ‖∫ t in (0:ℝ)..1, h t‖ ≤ a :=
    intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have h2 : 0 ≤ ∫ t in (0:ℝ)..1, (‖h t‖ - a) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
  have hn : Continuous fun t => ‖h t‖ := hh.norm
  have h3 : ∫ t in (0:ℝ)..1, (‖h t‖ - a) ^ 2
      = (∫ t in (0:ℝ)..1, ‖h t‖ ^ 2) - a ^ 2 := by
    have e : ∀ t, (‖h t‖ - a) ^ 2 = (‖h t‖ ^ 2 - 2 * a * ‖h t‖) + a ^ 2 := fun t => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, ← ha]
    · simp; ring
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  have h4 : ‖∫ t in (0:ℝ)..1, h t‖ ^ 2 ≤ a ^ 2 := by
    gcongr
  linarith

theorem right_translation_curve_sq_le_and_integral_deriv_eq_zero :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (c : ℝ → K), Continuous c → c 0 = 1 →
      ∀ f f' : K → ℂ, Continuous f → Continuous f' →
      (∀ x t, HasDerivAt (fun t : ℝ => f (x * c t)) (f' (x * c t)) t) →
      (∫ x, ‖f (x * c 1) - f x‖ ^ 2 ∂μ ≤ ∫ x, ‖f' x‖ ^ 2 ∂μ) ∧ ∫ x, f' x ∂μ = 0 := by
  intro K _ _ _ _ _ _ _ μ _ _ _ c hc h0 f f' hf hf' hd
  have key : ∀ x, f (x * c 1) - f x = ∫ t in (0:ℝ)..1, f' (x * c t) := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd x t)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp [h0]
  have hI : ∀ {E : Type} [NormedAddCommGroup E] [SecondCountableTopology E] (g : K → E),
      Continuous g → Integrable g μ :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  constructor
  · rw [← integral_intervalIntegral_mul_right_curve μ c hc (fun x => ‖f' x‖ ^ 2) (by fun_prop)]
    refine integral_mono (hI _ (by fun_prop)) (hI _ ?_) fun x => ?_
    · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun (x : K) (t : ℝ) => ‖f' (x * c t)‖ ^ 2)
        (by unfold Function.uncurry; fun_prop) 0 1
    · simp only [key]
      exact norm_intervalIntegral_unit_sq_le _ (by fun_prop)
  · rw [← integral_intervalIntegral_mul_right_curve μ c hc f' hf']
    simp_rw [← key]
    rw [integral_sub (hI _ (by fun_prop)) (hI _ hf), integral_mul_right_eq_self f, sub_self]

end GlobalTheory
end
