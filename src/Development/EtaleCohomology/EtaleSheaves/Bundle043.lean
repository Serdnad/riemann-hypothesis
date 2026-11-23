module

public import Development.EtaleCohomology.EtaleSheaves.Bundle028
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Development.EtaleCohomology.EtaleSheaves.Bundle029
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Development.EtaleCohomology.EtaleSheaves.Bundle026
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
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.ChartAcycPf

theorem acyc_of_iso {q : ℕ} {E E' : Spc} (e : E ≅ E') (h : Acyc q E') : Acyc q E := by
  intro n i hn
  have := h n i hn
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : Ht q E n i, z = pull _ e.hom (tw q i) n (pull _ e.inv (tw q i) n z) := by
    intro z
    rw [← pull_comp, e.hom_inv_id, pull_id]
  rw [key x, key y, Subsingleton.elim (pull _ e.inv (tw q i) n x) (pull _ e.inv (tw q i) n y)]

theorem aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have h2 : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    rw [Polynomial.map_map]; ext n; simp
  rw [← h2]
  change Polynomial.eval (e.toRingHom a) _ = 0
  rw [Polynomial.eval_map_apply, ha, map_zero]

theorem fib_iso_quot {A : Type} [CommRing A] [IsLocalRing A] {U : Scheme.{0}} [IsAffine U]
    (f : U ⟶ Spec (CommRingCat.of A)) :
    ∃ (φ : A →+* Γ(U, ⊤)), Nonempty (fib f ≅ Spec (CommRingCat.of
      (Γ(U, ⊤) ⧸ (IsLocalRing.maximalIdeal A).map φ))) := by
  let e := U.isoSpec
  let φ := Spec.preimage (e.inv ≫ f)
  have hf : f = e.hom ≫ Spec.map φ := by
    rw [Spec.map_preimage]; simp
  letI : Algebra A Γ(U, ⊤) := φ.hom.toAlgebra
  refine ⟨φ.hom, ⟨?_⟩⟩
  refine (pullback.congrHom hf rfl) ≪≫
    (asIso (pullback.map (e.hom ≫ Spec.map φ) (cpt A) (Spec.map φ) (cpt A) e.hom (𝟙 _) (𝟙 _) (by simp) (by simp))) ≪≫ ?_
  refine (pullbackSpecIso A Γ(U, ⊤) (IsLocalRing.ResidueField A)) ≪≫ ?_
  let i := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := A) Γ(U, ⊤)
    (IsLocalRing.maximalIdeal A)).toRingEquiv.toCommRingCatIso
  exact Scheme.Spec.mapIso i.op

theorem ChartAcyc_of (hQ : QuotAcyc) : ChartAcyc := by
  intro H q A _ _ Z U p ι hι hU hZ hq
  have : IsIntegral Z := hZ.1
  by_cases hne : Nonempty U
  · have : IsIntegral U := isIntegral_of_isOpenImmersion ι
    obtain ⟨φ, ⟨e⟩⟩ := fib_iso_quot (ι ≫ p)
    have hdom : IsDomain Γ(U, ⊤) := inferInstance
    have haff : IsAffineOpen (ι ''ᵁ (⊤ : U.Opens)) := (isAffineOpen_top U).image_of_isOpenImmersion ι
    have hnV : ((ι ''ᵁ (⊤ : U.Opens) : Z.Opens) : Set Z).Nonempty := by
      obtain ⟨x⟩ := hne
      exact ⟨ι x, x, trivial, rfl⟩
    have haic : AIC Γ(U, ⊤) :=
      aic_of_equiv (ι.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ haff hnV)
    have hqB : IsUnit (q : Γ(U, ⊤)) := by
      simpa using hq.map φ
    exact acyc_of_iso (sch.mapIso e) (hQ H q Γ(U, ⊤) _ haic hqB)
  · rw [not_nonempty_iff] at hne
    obtain ⟨x⟩ : Nonempty Z := inferInstance
    obtain ⟨V, ⟨W, hW, rfl⟩, hxW, -⟩ := (Z.isBasis_affineOpens).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hWne : Nonempty W := ⟨⟨x, hxW⟩⟩
    have hdom : IsDomain Γ(Z, W) := inferInstance
    have haic : AIC Γ(Z, W) := hZ.2 W hW ⟨x, hxW⟩
    let ψ : CommRingCat.of A ⟶ Γ(Z, W) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top).op
    have hqC : IsUnit (q : Γ(Z, W)) := by
      simpa using hq.map ψ.hom
    have h1 := hQ H q Γ(Z, W) ⊤ haic hqC
    have : IsEmpty (fib (ι ≫ p)) := ⟨fun y => hne.elim ((pullback.fst (ι ≫ p) (cpt A)) y)⟩
    have : Subsingleton (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))) := Ideal.Quotient.subsingleton_iff.mpr rfl
    have : IsEmpty (Spec (CommRingCat.of (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))))) :=
      ⟨fun y => (show PrimeSpectrum (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))) from y).isPrime.ne_top (Subsingleton.elim _ _)⟩
    exact acyc_of_iso (sch.mapIso (isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty)) h1

end LateralTheory.E.ChartAcycPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.FibCovPf

open LateralTheory.E.t_E2Cut LateralTheory.E.LineHighPf

theorem qaic_of_iso {q : ℕ} {W W' : Scheme.{0}} (e : W ≅ W') (h : QAIC q W') : QAIC q W := by
  obtain ⟨B, i1, i2, I, hB, hq, ⟨e'⟩⟩ := h
  exact ⟨B, i1, i2, I, hB, hq, ⟨e ≪≫ e'⟩⟩

theorem qaic_empty (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (hB : AIC B) (hq : IsUnit (q : B))
    {W : Scheme.{0}} [IsEmpty W] : QAIC q W := by
  have : Subsingleton (B ⧸ (⊤ : Ideal B)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have : IsEmpty (Spec (CommRingCat.of (B ⧸ (⊤ : Ideal B)))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (B ⧸ (⊤ : Ideal B))))
  exact ⟨B, inferInstance, inferInstance, ⊤, hB, hq, ⟨isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty⟩⟩

theorem qaic_good (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A)) (B0 : Type) [CommRing B0]
    [IsDomain B0] (hB0 : AIC B0) (hq0 : IsUnit (q : B0)) {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A))
    (hw : Good w) : QAIC q (pullback w (cpt A)) := by
  rcases hw with hE | ⟨B, i1, i2, i3, hB, e, he⟩
  · have : IsEmpty ↥(pullback w (cpt A) : Scheme.{0}) := ⟨fun x => hE.elim ((pullback.fst w (cpt A)).base x)⟩
    exact qaic_empty q B0 hB0 hq0
  · subst he
    refine ⟨B, i1, i2, (IsLocalRing.maximalIdeal A).map (algebraMap A B), hB, ?_, ?_⟩
    · simpa using hq.map (algebraMap A B)
    · obtain ⟨e2⟩ := fibre_affine A B
      exact ⟨(pullbackRightPullbackFstIso _ (cpt A) e.hom).symm ≪≫ asIso (pullback.snd e.hom _) ≪≫ e2⟩

theorem exists_absolutely_integrally_closed_domain_with_q_unit (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A)) {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of A)) (hZ : AICSch Z) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B), AIC B ∧ IsUnit (q : B) := by
  obtain ⟨hI, hA⟩ := hZ
  obtain ⟨x⟩ : Nonempty Z := hI.nonempty
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : Z.Opens) from trivial)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨Γ(Z, U), inferInstance, IsIntegral.component_integral U, hA U hU ⟨x, hxU⟩, ?_⟩
  have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appLE ⊤ U le_top).hom
  simpa using this

theorem FibCov_of : FibCov := by
  intro q A _ _ hq Z p hZ U V f g _ _ hc hU hV hW
  obtain ⟨B0, _, _, hB0, hq0⟩ := exists_absolutely_integrally_closed_domain_with_q_unit q A hq p hZ
  refine ⟨pullback f (pullback.fst p (cpt A)), pullback g (pullback.fst p (cpt A)),
    pullback.snd f (pullback.fst p (cpt A)), pullback.snd g (pullback.fst p (cpt A)),
    inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_union, hc, Set.preimage_univ]
  · exact qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) f) (qaic_good q A hq B0 hB0 hq0 _ hU)
  · exact qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) g) (qaic_good q A hq B0 hB0 hq0 _ hV)
  · refine qaic_of_iso ?_ (qaic_good q A hq B0 hB0 hq0 _ hW)
    exact pullbackLeftPullbackSndIso f (pullback.fst p (cpt A)) (pullback.snd g (pullback.fst p (cpt A))) ≪≫
      pullback.congrHom rfl pullback.condition.symm ≪≫
      (pullbackLeftPullbackSndIso f g (pullback.fst g (pullback.fst p (cpt A)))).symm ≪≫
      pullbackRightPullbackFstIso g (pullback.fst p (cpt A)) (pullback.snd f g) ≪≫
      pullback.congrHom pullback.condition.symm rfl ≪≫
      pullbackRightPullbackFstIso p (cpt A) (pullback.fst f g ≫ f) ≪≫
      pullback.congrHom (Category.assoc _ _ _) rfl

end LateralTheory.E.FibCovPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ProdAcycPf

theorem zero_acyc (H : LateralTheory.E.t_E2Cut.Hyp) (q : ℕ) (A : Type) [CommRing A] [Subsingleton A] : Acyc q (sp A) := by
  intro n i hn
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : Ht q (sp A) n i, x = 0 := by
    intro x
    obtain ⟨Y, f, -, -, hx⟩ := H.a5 (ZMod q) (Spec (CommRingCat.of A)) (tw q i) n hn x
    have : IsEmpty (Spec (CommRingCat.of A)) := inferInstanceAs (IsEmpty (PrimeSpectrum A))
    have : IsIso (sch.map f) := inferInstance
    have hy : pull _ (inv (sch.map f)) _ _ (pull _ (sch.map f) _ _ x) = x := by
      rw [← pull_comp, IsIso.inv_hom_id, pull_id]
    rw [← hy, hx, map_zero]
  rw [h0 x, h0 y]

def Bin : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A R0 R1 : Type) [CommRing A] [CommRing R0] [CommRing R1],
  Nonempty (A ≃+* R0 × R1) → Acyc q (sp R0) → Acyc q (sp R1) → Acyc q (sp A)

def splitFirst (n : ℕ) (R : Fin (n + 1) → Type) [∀ k, CommRing (R k)] :
    (∀ k, R k) ≃+* R 0 × ∀ k : Fin n, R k.succ where
  toFun f := (f 0, fun k => f k.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' f g := rfl
  map_add' f g := rfl

theorem prod_of (hB : Bin) : LateralTheory.E.QuotAcycCut.ProdAcyc := by
  intro H q A _ n
  induction n generalizing A with
  | zero =>
    intro R _ ⟨e⟩ _
    have : Subsingleton A := e.injective.subsingleton
    exact zero_acyc H q A
  | succ n ih =>
    intro R _ ⟨e⟩ hR
    refine hB H q A (R 0) (∀ k : Fin n, R k.succ) ⟨e.trans (splitFirst n R)⟩ (hR 0) ?_
    exact ih (∀ k : Fin n, R k.succ) (fun k => R k.succ) ⟨RingEquiv.refl _⟩ fun k => hR k.succ

end LateralTheory.E.ProdAcycPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineHighPf

namespace LateralTheory.E.ZCovPf
set_option linter.style.haveILetI false

theorem aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hc : (e : R →+* S).comp e.symm.toRingHom = RingHom.id S := by ext x; simp
  have hq : p = (p.map e.symm.toRingHom).map (e : R →+* S) := by
    rw [Polynomial.map_map, hc, Polynomial.map_id]
  rw [hq, show e a = (e : R →+* S) a from rfl, Polynomial.eval_map_apply, ha, map_zero]

theorem good_of_affine {A : Type} [CommRing A] {Z W : Scheme.{0}} (hZ : AICSch Z) (j : W ⟶ Z) [IsOpenImmersion j]
    [IsAffine W] (p : Z ⟶ Spec (CommRingCat.of A)) : Good (j ≫ p) := by
  by_cases hW : IsEmpty W
  · exact Or.inl hW
  right
  obtain ⟨x⟩ : Nonempty W := not_isEmpty_iff.mp hW
  have hO : IsAffineOpen (j ''ᵁ ⊤) := (isAffineOpen_top W).image_of_isOpenImmersion j
  have hne : ((j ''ᵁ ⊤ : Z.Opens) : Set Z).Nonempty := ⟨j x, x, trivial, rfl⟩
  have hA : AIC Γ(W, ⊤) := aic_of_equiv (j.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ hO hne)
  haveI : IsIntegral Z := hZ.1
  haveI : Nonempty W := ⟨x⟩
  haveI : IsIntegral W := isIntegral_of_isOpenImmersion j
  haveI : Nonempty (⊤ : W.Opens) := ⟨⟨x, trivial⟩⟩
  let φ : A →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (j ≫ p).appTop).hom
  letI : Algebra A Γ(W, ⊤) := φ.toAlgebra
  refine ⟨Γ(W, ⊤), inferInstance, inferInstance, inferInstance, hA, W.isoSpec, ?_⟩
  have hφ : CommRingCat.ofHom (algebraMap A Γ(W, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (j ≫ p).appTop := rfl
  rw [hφ, Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

attribute [local instance] MvPolynomial.gradedAlgebra

def D (i : Fin 2) : P1.Opens := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

theorem D_affine (i : Fin 2) : IsAffineOpen (D i) :=
  Proj.isAffineOpen_basicOpen _ _ (f_deg := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_X ℤ i)) (hm := Nat.one_pos)

theorem D_inf : IsAffineOpen (D 0 ⊓ D 1) := by
  have h := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (MvPolynomial.X 0 * MvPolynomial.X 1) (f_deg := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    ((MvPolynomial.isHomogeneous_X ℤ 0).mul (MvPolynomial.isHomogeneous_X ℤ 1))) (hm := Nat.two_pos)
  rw [Proj.basicOpen_mul] at h
  exact h

theorem D_cover : D 0 ⊔ D 1 = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ)) ?_
  · refine eq_top_iff.mpr (le_trans (le_of_eq h.symm) (iSup_le fun i => ?_))
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · intro x hx
    have h0 := (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx
    have hc : AddMonoidAlgebra.coeff x 0 = 0 := by
      rw [GradedRing.proj_apply] at h0
      have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) x) 0 : MvPolynomial (Fin 2) ℤ) =
          MvPolynomial.homogeneousComponent 0 x := MvPolynomial.decomposition.decompose'_apply x 0
      rw [e] at h0
      have := congrArg (AddMonoidAlgebra.coeff · 0) h0
      rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_zero] at this
      simpa using this
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hne
    push Not at hne
    have hm0 : m = 0 := Finsupp.ext fun i => hne i trivial
    subst hm0
    exact (MvPolynomial.mem_support_iff.mp hm) hc

theorem projectiveLine_integers_affine_cover_absolutely_integrally_closed : ZCov := by
  intro A _ Z p hp hZ
  obtain ⟨L, u, l, hu, ⟨-, f0, hpb⟩, rfl⟩ := hp
  have hf0 : IsAffineHom f0 :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  let φ : Z ⟶ P1 := u ≫ f0
  let U : Z.Opens := φ ⁻¹ᵁ D 0
  let V : Z.Opens := φ ⁻¹ᵁ D 1
  have hU : IsAffineOpen U := (D_affine 0).preimage φ
  have hV : IsAffineOpen V := (D_affine 1).preimage φ
  have hUV : IsAffineOpen (U ⊓ V) := D_inf.preimage φ
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  haveI : IsAffine (U ⊓ V : Z.Opens) := hUV
  haveI : IsAffine (pullback U.ι V.ι) := IsAffine.of_isIso (isPullback_opens_inf U V).isoPullback.inv
  refine ⟨U, V, U.ι, V.ι, inferInstance, inferInstance, ?_, good_of_affine hZ U.ι _, good_of_affine hZ V.ι _, ?_⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have h := congrArg (fun O : P1.Opens => ((φ ⁻¹ᵁ O : Z.Opens) : Set Z)) D_cover
    simpa [U, V] using h
  · rw [← Category.assoc]
    exact good_of_affine hZ (pullback.fst U.ι V.ι ≫ U.ι) _

end LateralTheory.E.ZCovPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.E.ChernClassEvaluation

variable {R : Type} [CommRing R]

theorem chains_d (E : Spc) (p : ℕ) :
    ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  refine (HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl).trans ?_
  unfold chainsXIso
  congr 2
  simp [chainsN]

theorem freeGen_nat {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map f).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  unfold freeGen
  change ((((toSheafify _ ((freeP R).obj P)) ≫ sheafifyMap _ ((freeP R).map f)).app (op U)).hom _) = _
  rw [← toSheafify_naturality, NatTrans.comp_app, ModuleCat.hom_comp]
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom y)
    (by erw [ModuleCat.free_map_apply]; rfl)

def evH {A B : Shv R} (U : Scheme.{0}) (y : Sec A U) : (A ⟶ B) →+ Sec B U where
  toFun f := (f.hom.app (op U)).hom y
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evH_apply {A B : Shv R} (U : Scheme.{0}) (y : Sec A U) (f : A ⟶ B) :
    (f.hom.app (op U)).hom y = evH U y f := rfl

theorem evDelta_pf : ChernClassExistence.LeafEvDelta := by
  intro R _ E I n m hm α U
  constructor
  · intro x
    unfold ev
    rw [δ_v n m hm α (-((0 : ℕ) : ℤ)) m (by simp) n 1 (by omega) (by simp)]
    have hz : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) 1 = 0 :=
      (HomologicalComplex.isZero_extend_X _ _ 1 (fun i => by show -(i : ℤ) ≠ 1; omega)).eq_of_tgt _ _
    rw [hz]
    simp [Sec.map]
  · intro p s t hs ht x
    unfold ev
    rw [δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by push_cast; omega), chains_d]
    simp only [Preadditive.comp_add, Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id_assoc]
    simp [Sec.map, Units.smul_def, Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul, freeGen_nat, Sx.face]

    rw [evH_apply, map_zsmul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← evH_apply]
    simp [freeGen_nat]

theorem etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness (hmk : ChernClassExistence.LeafEvMk) (h1 : ChernClassExistence.EtaleKummerChernEdgeValuesExistNatural) (h2 : ChernClassExistence.EtaleKummerChernTriangleValuesExistNatural)
    (c1 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnEdges) (c2 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTriangles) (c3 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra) :
    LateralTheory.E.ChernCocycleExistenceAndUniqueness.EtaleKummerChernCocycleExists :=
  ChernClassExistence.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness hmk evDelta_pf h1 h2 c1 c2 c3

end LateralTheory.E.ChernClassEvaluation
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StandardEtaleChartsIdempotentGluing

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def mS (S : Subalgebra A K) : Submodule A K := IsLocalRing.maximalIdeal A • Subalgebra.toSubmodule S

def AdjoinInv (B : Subalgebra A K) (t : K) : Subalgebra A K := Algebra.adjoin A ((B : Set K) ∪ {t⁻¹})

structure Charts (B C : Subalgebra A K) (t : K) : Prop where
  ne : t ≠ 0
  tB : t ∈ B
  tC : t⁻¹ ∈ C
  intB : ∀ b ∈ B, IsIntegral (Algebra.adjoin A {t}) b
  intC : ∀ c ∈ C, IsIntegral (Algebra.adjoin A {t⁻¹}) c
  glue : AdjoinInv B t = Algebra.adjoin A ((C : Set K) ∪ {t})

def IdemPair (B C : Subalgebra A K) (t e f : K) : Prop :=
  e ∈ B ∧ f ∈ C ∧ e * e - e ∈ mS B ∧ f * f - f ∈ mS C ∧ e - f ∈ mS (AdjoinInv B t)

def StdCharts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧
    ∀ W : Set ↑(pullback p (cpt A)), IsClopen W → ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ)

def IdemLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f →
  ∃ g ∈ B, g ∈ C ∧ g - e ∈ mS B ∧ g - f ∈ mS C

def AlgGlue : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → (∀ x ∈ B, x ∈ C → IsIntegral A x) → ∀ e f : K, IdemPair B C t e f →
  (e ∈ mS B ∧ f ∈ mS C) ∨ (e - 1 ∈ mS B ∧ f - 1 ∈ mS C)

theorem goal_of (hS : StdCharts) (hG : AlgGlue) : LateralTheory.E.t_E2Cut.LineZero := by
  intro A _ _ hSH Z p hIL hZ
  obtain ⟨hH, -⟩ := hSH
  have hne : Nonempty ↑(pullback p (cpt A)) := by
    obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
    have := hl.1
    have := hZ.1
    exact LateralTheory.E.LineZeroCut.lzNonempty A (u ≫ l) inferInstance inferInstance
  obtain ⟨K, _, _, B, C, t, hc, hint, hW⟩ := hS A p hIL hZ
  have hpre : PreconnectedSpace ↑(pullback p (cpt A)) := by
    rw [preconnectedSpace_iff_clopen]
    intro W hW'
    obtain ⟨e, f, hef, h0, h1⟩ := hW W hW'
    rcases hG A K B C t hc hint e f hef with h | h
    · exact Or.inl (h0 h)
    · exact Or.inr (h1 h)
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

end LateralTheory.E.StandardEtaleChartsIdempotentGluing
end
end
