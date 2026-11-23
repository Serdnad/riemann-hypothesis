module

public import Development.EtaleCohomology.EtaleSheaves.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import GroundTheory.FunctionField.PlaceDefs
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Basic

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.PullbackAlongInclusion

section
variable (A K L : Type) [CommRing A] [Field K] [Algebra A K] [Field L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L]

private abbrev Idx : Type := {E : IntermediateField K L // FiniteDimensional K E}

omit [Algebra A K] in
private theorem idx_directed : IsDirected (Idx K L) (· ≤ ·) :=
  ⟨fun a b => by
    haveI := a.2
    haveI := b.2
    exact ⟨⟨a.1 ⊔ b.1, inferInstance⟩, le_sup_left (a := a.1), le_sup_right (b := b.1)⟩⟩

private noncomputable def incl {E F : IntermediateField K L} (h : E ≤ F) :
    integralClosure A E →ₐ[A] integralClosure A F :=
  ((IntermediateField.inclusion h).restrictScalars A).mapIntegralClosure

private noncomputable def toL (E : IntermediateField K L) :
    integralClosure A E →ₐ[A] integralClosure A L :=
  (E.val.restrictScalars A).mapIntegralClosure

private noncomputable def ringD : Idx K L ⥤ CommRingCat.{0} where
  obj E := CommRingCat.of (integralClosure A E.1)
  map f := CommRingCat.ofHom (incl A K L (leOfHom f)).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private noncomputable def ringC : Cocone (ringD A K L) where
  pt := CommRingCat.of (integralClosure A L)
  ι := { app := fun E => CommRingCat.ofHom (toL A K L E.1).toRingHom
         naturality := fun _ _ _ => by ext; rfl }

private theorem ringC_isColimit [Algebra.IsAlgebraic K L] : Nonempty (IsColimit (ringC A K L)) := by
  haveI := idx_directed K L
  haveI : Nonempty (Idx K L) := ⟨⟨⊥, inferInstance⟩⟩
  haveI : IsFiltered (Idx K L) := inferInstance
  haveI : ReflectsColimitsOfShape (Idx K L) (forget CommRingCat) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    have hx : IsIntegral K (x.1 : L) := Algebra.IsIntegral.isIntegral _
    let E : Idx K L := ⟨IntermediateField.adjoin K {x.1}, IntermediateField.adjoin.finiteDimensional hx⟩
    have hm : x.1 ∈ E.1 := IntermediateField.mem_adjoin_simple_self K x.1
    have hi : IsIntegral A (⟨x.1, hm⟩ : E.1) :=
      (isIntegral_algHom_iff (E.1.val.restrictScalars A) E.1.val.toRingHom.injective).1 x.2
    exact ⟨E, ⟨⟨x.1, hm⟩, hi⟩, rfl⟩
  · intro a b xa xb h
    haveI := a.2
    haveI := b.2
    refine ⟨⟨a.1 ⊔ b.1, inferInstance⟩, homOfLE (le_sup_left (a := a.1)),
      homOfLE (le_sup_right (b := b.1)), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : integralClosure A L => (z : L)) h

omit [Algebra A K] [IsScalarTower A K L] [Field K] [Algebra K L] in
private theorem aic [IsAlgClosed L] : AIC (integralClosure A L) := by
  intro p hp hdeg
  have hd : (p.map (algebraMap (integralClosure A L) L)).degree ≠ 0 := by
    rw [hp.degree_map]
    exact (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral (integralClosure A L) a := ⟨p, hp, by rw [← Polynomial.eval_map]; exact ha⟩
  have hA : IsIntegral A a := isIntegral_trans a hint
  refine ⟨⟨a, hA⟩, ?_⟩
  have h2 : algebraMap (integralClosure A L) L (Polynomial.eval ⟨a, hA⟩ p) = 0 := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact ha
  exact Subtype.ext h2

end

private theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

private theorem pull_of_comp (q : ℕ) (m i : ℤ) {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (e : g.comp f = h) (x : Ht q (sp R) m i) :
    pull _ (spMap g) _ m (pull _ (spMap f) _ m x) = pull _ (spMap h) _ m x := by
  rw [← pull_comp, spMap_comp, e]

end UpperTheory.PullbackAlongInclusion

open UpperTheory.PullbackAlongInclusion in
theorem UpperTheory.exists_finite_ext_pullback_integralClosure_eq_zero :
    Hyps → ∀ (q : ℕ) [NeZero q] (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
        [IsFractionRing A K], IsUnit (q : A) → ∀ (m i : ℤ), 0 < m → ∀ x : Ht q (sp A) m i,
        ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F) (_ : IsScalarTower A K F) (_ : FiniteDimensional K F),
          pull _ (spMap (algebraMap A (integralClosure A F))) _ m x = 0 := by
  intro h q _ A K _ _ _ _ _ hq m i hm x
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hB1, -, -, -, hB5, -⟩ := h
  let L := AlgebraicClosure K
  haveI : IsDirected (Idx K L) (· ≤ ·) := idx_directed K L
  haveI : Nonempty (Idx K L) := ⟨⟨⊥, inferInstance⟩⟩
  haveI : IsFiltered (Idx K L) := isFiltered_of_directed_le_nonempty _
  obtain ⟨hc⟩ := ringC_isColimit A K L
  let j0 : Idx K L := ⟨⊥, inferInstance⟩
  have hqE : ∀ E : IntermediateField K L, IsUnit ((q : integralClosure A E)) := fun E => by
    simpa using hq.map (algebraMap A (integralClosure A E))
  have hqL : IsUnit ((q : integralClosure A L)) := by
    simpa using hq.map (algebraMap A (integralClosure A L))
  have e1 := pull_of_comp q m i (algebraMap A (integralClosure A j0.1)) (toL A K L j0.1).toRingHom
    (algebraMap A (integralClosure A L)) (toL A K L j0.1).comp_algebraMap x
  haveI := hB5 q (integralClosure A L) (aic A L) hqL m i hm
  have hzero : pull _ (spMap ((ringC A K L).ι.app j0).hom) _ m
      (pull _ (spMap (algebraMap A (integralClosure A j0.1))) _ m x) = 0 :=
    e1.trans (Subsingleton.elim _ _)
  obtain ⟨k, f, hk⟩ := (hB1 q (ringD A K L) (ringC A K L) hc m i).2 j0 _ (hqE _) hzero
  refine ⟨k.1, inferInstance, inferInstance, inferInstance, inferInstance, k.2, ?_⟩
  have e2 := pull_of_comp q m i (algebraMap A (integralClosure A j0.1))
    (incl A K L (leOfHom f)).toRingHom (algebraMap A (integralClosure A k.1))
    (incl A K L (leOfHom f)).comp_algebraMap x
  exact e2.symm.trans hk
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

private lemma aux {W S T U : Scheme.{0}} (w : W ⟶ S) (i : T ⟶ S) (j : U ⟶ T) (g : U ⟶ S)
    (hg : j ≫ i = g) [Flat j] [IsPreimmersion i] (y' : ↑(pullback w g)) (x : W)
    (hx : x ⤳ (pullback.fst w g) y') (hxr : x ∈ Set.range (pullback.fst w i)) :
    ∃ x' : ↑(pullback w g), x' ⤳ y' ∧ (pullback.fst w g) x' = x := by
  subst hg
  have hfst : ∀ p, (pullback.fst w (j ≫ i)) ((pullbackLeftPullbackSndIso w i j).hom p) =
      (pullback.fst w i) ((pullback.fst (pullback.snd w i) j) p) := by
    intro p
    show ((pullbackLeftPullbackSndIso w i j).hom ≫ pullback.fst w (j ≫ i)).base p =
      (pullback.fst (pullback.snd w i) j ≫ pullback.fst w i).base p
    rw [pullbackLeftPullbackSndIso_hom_fst]
  have hy : (pullbackLeftPullbackSndIso w i j).hom ((pullbackLeftPullbackSndIso w i j).inv y') = y' := by
    show ((pullbackLeftPullbackSndIso w i j).inv ≫ (pullbackLeftPullbackSndIso w i j).hom).base y' = y'
    rw [Iso.inv_hom_id]
    rfl
  obtain ⟨z, hz⟩ := hxr
  have hxz : z ⤳ (pullback.fst (pullback.snd w i) j) ((pullbackLeftPullbackSndIso w i j).inv y') := by
    rw [← (IsPreimmersion.isEmbedding (pullback.fst w i)).isInducing.specializes_iff, hz, ← hfst, hy]
    exact hx
  obtain ⟨x'', hx'', hx''z⟩ := Flat.generalizingMap (pullback.fst (pullback.snd w i) j) hxz
  refine ⟨(pullbackLeftPullbackSndIso w i j).hom x'', ?_, ?_⟩
  · rw [← hy]
    exact hx''.map (Scheme.Hom.continuous _)
  · rw [hfst, hx''z, hz]

private lemma spec_bot {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f) :
    Spec.map (CommRingCat.ofHom f) (⊥ : PrimeSpectrum B) = (⊥ : PrimeSpectrum A) := by
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective f hf

private lemma spec_field {F : Type} [Field F] (z : PrimeSpectrum F) : z = ⊥ :=
  PrimeSpectrum.ext (Ideal.eq_bot_of_prime _)

private lemma spec_gen {A : Type} [CommRing A] [IsDomain A] (a : PrimeSpectrum A)
    (h : a ⤳ (⊥ : PrimeSpectrum A)) : a = ⊥ :=
  le_bot_iff.1 ((PrimeSpectrum.le_iff_specializes _ _).2 h)

theorem UpperTheory.exists_specializes_lift_generic_base_change :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω], Function.Injective (algebraMap R Ω) → ∀ {W : Scheme.{0}} (w : W ⟶ Sp R) (y' : ↑(pullback w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) (x : W), x ⤳ (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) y' → ∃ x' : ↑(pullback w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))), x' ⤳ y' ∧ (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) x' = x := by
  intro R Ω _ _ _ _ hinj W w y' x hx
  have hRK : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  letI : Algebra (FractionRing R) Ω := (IsFractionRing.lift hinj : FractionRing R →+* Ω).toAlgebra
  haveI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hcomp : (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) =
      algebraMap R Ω := IsLocalization.lift_comp _
  have hg : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  apply aux w (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) Ω))) _ hg y' x hx
  have hwx : (show PrimeSpectrum R from w x) = ⊥ := by
    apply spec_gen
    have h1 := hx.map w.continuous
    have h2 : w (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y') =
        Spec.map (CommRingCat.ofHom (algebraMap R Ω))
          (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y') := by
      show (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ w).base y' =
        (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R Ω))).base y'
      rw [pullback.condition]
    rw [h2, spec_field (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y'),
      spec_bot _ hinj] at h1
    exact h1
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := w)
    (g := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) x
    (⊥ : PrimeSpectrum (FractionRing R)) (by
      show (show PrimeSpectrum R from w x) = _
      rw [hwx, spec_bot _ hRK])
  exact ⟨z, hz⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem exists_point {k R : Type} [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal] :
    ∃ φ : R →ₐ[k] k, ∀ r, φ r = 0 → r ∈ m := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) := inferInstance
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := inferInstance
  let e : k ≃ₐ[k] (R ⧸ m) :=
    AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), fun r hr => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : e.symm (Ideal.Quotient.mk m r) = 0 := hr
  exact (map_eq_zero_iff e.symm e.symm.injective).mp h0

private theorem dom_fg {k R A ι : Type} [Field k] [IsAlgClosed k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing A] [IsDomain A] [Algebra k A] (e : Module.Basis ι k A)
    (s t : Finset ι) (a b : ι → R)
    (h : (∑ i ∈ s, a i ⊗ₜ[k] e i) * (∑ j ∈ t, b j ⊗ₜ[k] e j) = 0) :
    (∀ i ∈ s, a i = 0) ∨ (∀ j ∈ t, b j = 0) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨i0, hi0, ha⟩, ⟨j0, hj0, hb⟩⟩ := hcon
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hab : a i0 * b j0 ≠ 0 := mul_ne_zero ha hb
  have hjac : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance Ideal.isRadical_bot_of_noZeroDivisors
  have hnot : a i0 * b j0 ∉ (⊥ : Ideal R).jacobson := by
    rw [hjac]
    simpa using hab
  obtain ⟨m, hm, hnm⟩ : ∃ m : Ideal R, m.IsMaximal ∧ a i0 * b j0 ∉ m := by
    by_contra hne
    push_neg at hne
    apply hnot
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro J ⟨-, hJ⟩
    exact hne J hJ
  haveI := hm
  obtain ⟨φ, hφ⟩ := exists_point (k := k) m
  have hφa : φ (a i0) ≠ 0 := fun h0 => hnm (m.mul_mem_right _ (hφ _ h0))
  have hφb : φ (b j0) ≠ 0 := fun h0 => hnm (m.mul_mem_left _ (hφ _ h0))
  let ψ : R ⊗[k] A →ₐ[k] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId k A).comp φ) (AlgHom.id k A) (fun _ _ => Commute.all _ _)
  have hψ : ∀ (c : ι → R) (u : Finset ι),
      ψ (∑ i ∈ u, c i ⊗ₜ[k] e i) = ∑ i ∈ u, φ (c i) • e i := by
    intro c u

    simp [ψ, map_sum, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  have h2 := congrArg ψ h
  rw [map_mul, hψ, hψ, map_zero] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hφa ((linearIndependent_iff'.mp e.linearIndependent) s (fun i => φ (a i)) h3 i0 hi0)
  · exact hφb ((linearIndependent_iff'.mp e.linearIndependent) t (fun j => φ (b j)) h3 j0 hj0)

private theorem dom_tensor (k K L : Type) [Field k] [IsAlgClosed k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] : IsDomain (L ⊗[k] K) := by
  classical
  let e := Module.Basis.ofVectorSpace k K
  haveI : Nontrivial (L ⊗[k] K) := inferInstance
  suffices hnz : NoZeroDivisors (L ⊗[k] K) from NoZeroDivisors.to_isDomain _
  refine ⟨fun {x y} hxy => ?_⟩
  let E := TensorProduct.equivFinsuppOfBasisRight (M := L) e
  have hrep : ∀ z : L ⊗[k] K, z = ∑ i ∈ (E z).support, (E z) i ⊗ₜ[k] e i := by
    intro z
    conv_lhs => rw [← E.symm_apply_apply z]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum]
  let S : Finset L := (E x).support.image (E x) ∪ (E y).support.image (E y)
  let R := Algebra.adjoin k (S : Set L)
  haveI : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp (Subalgebra.fg_adjoin_finset S)
  have hmem : ∀ (z : L ⊗[k] K), (z = x ∨ z = y) → ∀ i, (E z) i ∈ R := by
    rintro z hz i
    by_cases hi : i ∈ (E z).support
    · apply Algebra.subset_adjoin
      rcases hz with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact R.zero_mem
  let a : Module.Basis.ofVectorSpaceIndex k K → R := fun i => ⟨(E x) i, hmem x (Or.inl rfl) i⟩
  let b : Module.Basis.ofVectorSpaceIndex k K → R := fun i => ⟨(E y) i, hmem y (Or.inr rfl) i⟩
  let j : R ⊗[k] K →ₐ[k] L ⊗[k] K := Algebra.TensorProduct.map R.val (AlgHom.id k K)
  have hj : Function.Injective j := by
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := K) R.val.toLinearMap Subtype.val_injective
    exact this
  have hja : j (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) = x := by

    rw [map_sum]
    conv_rhs => rw [hrep x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [j, a]
  have hjb : j (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = y := by

    rw [map_sum]
    conv_rhs => rw [hrep y]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [j, b]
  have hprod : (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) * (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = 0 := by
    apply hj
    rw [map_mul, hja, hjb, hxy, map_zero]
  rcases dom_fg (k := k) e _ _ a b hprod with h0 | h0
  · left
    rw [hrep x]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := congrArg Subtype.val (h0 i hi)
    simp only [a, ZeroMemClass.coe_zero] at this
    rw [this, TensorProduct.zero_tmul]
  · right
    rw [hrep y]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := congrArg Subtype.val (h0 i hi)
    simp only [b, ZeroMemClass.coe_zero] at this
    rw [this, TensorProduct.zero_tmul]

private theorem gi (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  haveI := dom_tensor k K L
  let e : Y ≅ Spec (CommRingCat.of (L ⊗[k] K)) := h.isoPullback ≪≫ pullbackSpecIso k L K
  haveI : Nonempty Y := ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

theorem UpperTheory.isCurve_pullback_of_isCurve_baseChange :
    ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] {C : Scheme.{0}} (c : C ⟶ Sp k), IsCurve c → IsCurve (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  intro k L _ _ _ _ C c hc
  obtain ⟨h1, h2, h3⟩ := hc
  haveI := gi k L
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L)) with hg
  set p := pullback.fst c g with hp
  haveI : GeometricallyIrreducible p := inferInstance
  haveI : GeometricallyReduced p := inferInstance
  haveI : Flat p := inferInstance
  haveI : Finite (irreducibleComponents C) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  haveI hred : IsReduced (pullback c g) :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents p
  have hgen : GeneralizingMap p := Flat.generalizingMap p
  set η := genericPoint C
  let ξ : ↥(pullback c g) := p.fiberι η (genericPoint (p.fiber η))
  have hall : ∀ q : ↥(pullback c g), ξ ⤳ q := by
    intro q
    have h0 : η ⤳ p q := genericPoint_specializes _
    obtain ⟨q', hq', hpq'⟩ := hgen h0
    have hmem : q' ∈ Set.range (p.fiberι η) := by
      rw [p.range_fiberι]
      exact hpq'
    obtain ⟨r, rfl⟩ := hmem
    exact ((genericPoint_specializes r).map (p.fiberι η).continuous).trans hq'
  haveI hirr : IrreducibleSpace ↥(pullback c g) := by
    rw [irreducibleSpace_def]
    have hcl : closure ({ξ} : Set ↥(pullback c g)) = Set.univ :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)
    rw [Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, inferInstance, ?_⟩
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) (IsPullback.of_hasPullback c g) h3
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

private theorem UpperTheory.affine_opens_same_krullDim (k : Type) [Field k] {Y : Scheme.{0}} [IsIntegral Y]
    (t : Y ⟶ Sp k) [LocallyOfFiniteType t] :
    ∃ c : WithBot ℕ∞, ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → ringKrullDim Γ(Y, U) = c := by
  classical
  let iso : k →+* Γ(Sp k, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hiso : Function.Surjective iso := by
    intro y
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom y, ?_⟩
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom y = y
    simp
  have eT : (⊤ : Y.Opens) ≤ t ⁻¹ᵁ ⊤ := le_top
  haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨Nonempty.some (inferInstance : Nonempty Y), trivial⟩⟩
  let φ : k →+* Y.functionField := (Y.germToFunctionField ⊤).hom.comp ((t.appLE ⊤ ⊤ eT).hom.comp iso)
  letI : Algebra k Y.functionField := φ.toAlgebra
  refine ⟨((Algebra.trdeg k Y.functionField).toENat : WithBot ℕ∞), ?_⟩
  intro U hU hne
  have eU : U ≤ t ⁻¹ᵁ ⊤ := le_top
  letI : Algebra k Γ(Y, U) := ((t.appLE ⊤ U eU).hom.comp iso).toAlgebra
  haveI : Algebra.FiniteType k Γ(Y, U) := by
    have h1 : (t.appLE ⊤ U eU).hom.FiniteType :=
      t.finiteType_appLE (isAffineOpen_top _) hU eU
    exact h1.comp (RingHom.FiniteType.of_surjective _ hiso)
  haveI : IsFractionRing Γ(Y, U) Y.functionField := functionField_isFractionRing_of_isAffineOpen Y U hU
  haveI : IsScalarTower k Γ(Y, U) Y.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change φ x = (Y.germToFunctionField U).hom ((t.appLE ⊤ U eU).hom (iso x))
    simp only [φ, RingHom.comp_apply]
    rw [← Scheme.Hom.appLE_map t eT (homOfLE (le_top : U ≤ ⊤)).op]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.germToFunctionField]
    exact (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (le_top : U ≤ ⊤)) _ _ _).symm
  exact GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing k Y.functionField

theorem UpperTheory.topologicalKrullDim_le_of_isOpenImmersion_integral :
    ∀ (k : Type) [Field k] {Y D : Scheme.{0}} [IsIntegral Y] (t : Y ⟶ Sp k) [LocallyOfFiniteType t] (j : D ⟶ Y) [IsOpenImmersion j] [Nonempty D], topologicalKrullDim Y ≤ topologicalKrullDim D := by
  intro k _ Y D _ t _ j _ _
  obtain ⟨c, hc⟩ := UpperTheory.affine_opens_same_krullDim k t
  have hdim : ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → topologicalKrullDim U = c := by
    intro U hU hne
    rw [← hc U hU hne, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
  have hup : topologicalKrullDim Y ≤ c := by
    apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
    intro x
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨A, A.isOpen, hxA, (hdim A hA ⟨⟨x, hxA⟩⟩).le⟩
  have hemb := j.isOpenEmbedding
  obtain ⟨d⟩ := ‹Nonempty D›
  obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAsub⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_range_self d) hemb.isOpen_range
  have hZ := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb.isEmbedding rfl
  have hAZ := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding (Topology.IsEmbedding.inclusion hAsub) rfl
  have hle := topologicalKrullDim_subspace_le (Set.range _) (Set.range (Set.inclusion hAsub))
  rw [hAZ, hZ] at hle
  exact hup.trans ((hdim A hA ⟨⟨_, hyA⟩⟩).symm.le.trans hle)
end
