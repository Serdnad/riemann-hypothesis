module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle870
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle005

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finrank_homology_one_two_dualResolution : ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g → ∀ (f : Fin g → O), Ideal.span (Set.range f) ≠ ⊤ → IsArtinianRing (O ⧸ Ideal.span (Set.range f)) → ∀ (C : CochainComplex (ModuleCat.{0} O) ℕ), (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap) → Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O] (O ⧸ Ideal.span (Set.range f))) → ∀ (K : Type) [Field K] (φ : O →+* K), RingHom.ker φ = IsLocalRing.maximalIdeal O → Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1) = g ∧ Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2) ≤ g.choose 2 := by
  first | exact @GlobalTheory.finrank_homology_one_two_of_dual_resolution | exact GlobalTheory.finrank_homology_one_two_of_dual_resolution | (intros; apply GlobalTheory.finrank_homology_one_two_of_dual_resolution <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem isCls_zero (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    IsCls (0 : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F) (0 : H R E F ((1 : ℕ) : ℤ)) := by
  have hc0 : ∀ {n : ℕ}, cobd (0 : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) = 0 := by
    intro n; simp [cobd]
  obtain ⟨x, hx⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F E 1).1 0 hc0
  have h4 := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F E 0).2.2.2.1 0 x (by rw [hc0]; exact hx)
  rw [h4] at hx
  exact hx

theorem mul_inv_mul_cancel_comm {M : Type*} [AddCommGroup M] {a b c : M} (h : a - b + c = 0) : b = c + a := by
  rw [sub_add_eq_add_sub, sub_eq_zero] at h
  rw [← h, add_comm]

theorem sub_add_eq_zero_of_eq_add {M : Type*} [AddCommGroup M] {a b c : M} (h : b = c + a) : a - b + c = 0 := by
  rw [h]
  abel

theorem mem_Z1_iff_cocycle (R : Type) [CommRing R] (F : Shv R) (w : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) :
    w ∈ Z1 F A B ↔
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom w =
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom w +
      ((onRings F).map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom w := Iff.rfl

theorem cobd_eq_zero_iff (R : Type) [CommRing R] (F : Shv R) (s : (free R).obj ((GlobalTheory.EtC.cech (fB A B)).obj (op ⦋1⦌)) ⟶ F) :
    cobd s = 0 ↔
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) =
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) +
      ((onRings F).map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) := by
  have hinj := (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 2 _ _ (y2 A B) (hy2 A B) (GlobalTheory.T.triple_tensor_wide_pullback_limit A B).some).1
  constructor
  · intro h
    have h2 := (val_coboundary_second_level A B R F s).symm.trans
      ((congrArg (fun t => val t (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B)) h).trans (val_zero R _ _))
    exact mul_inv_mul_cancel_comm h2
  · intro h
    apply hinj
    change val (cobd s) (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B) = val 0 (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B)
    rw [val_zero]
    exact (val_coboundary_second_level A B R F s).trans (sub_add_eq_zero_of_eq_add h)

def Rel (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) (x : H R (sp A) F 1) : Prop :=
  ∃ s : (free R).obj ((GlobalTheory.EtC.cech (fB A B)).obj (op ⦋1⦌)) ⟶ F,
    val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) ∧
      IsCls s (pull R (GlobalTheory.EtC.cechAug (fB A B)) F ((1 : ℕ) : ℤ) x)

theorem rel_unique [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B)
    (x x' : H R (sp A) F 1) (h : Rel A B R F u x) (h' : Rel A B R F u x') : x = x' := by
  obtain ⟨s, hs, hx⟩ := h
  obtain ⟨s', hs', hx'⟩ := h'
  have hss : s = s' :=
    (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 1 _ _ (y1 A B) (hy1 A B) (GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare A B).some).1 (hs.trans hs'.symm)
  subst hss
  have := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F (GlobalTheory.EtC.cech (fB A B)) 1).2.2.1 s _ _ hx hx'
  obtain ⟨h1, h2⟩ := smooth_surj A B
  exact (GlobalTheory.T.etC_a2 R (fB A B) F ((1 : ℕ) : ℤ)).1 this

theorem rel_exists [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) :
    ∃ x, Rel A B R F u x := by
  obtain ⟨s, hs⟩ := (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 1 _ _ (y1 A B) (hy1 A B) (GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare A B).some).2
    (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B)))
  have hs' : val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) := hs
  have hc : cobd s = 0 := (cobd_eq_zero_iff A B R F s).2 (by rw [hs']; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)
  obtain ⟨y, hy⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F (GlobalTheory.EtC.cech (fB A B)) 1).1 s hc
  obtain ⟨h1, h2⟩ := smooth_surj A B
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etC_a2 R (fB A B) F ((1 : ℕ) : ℤ)).2 y
  exact ⟨x, s, hs', hx ▸ hy⟩

variable {A B} in
theorem rel_add (R : Type) [CommRing R] (F : Shv R) (u u' : Z1 F A B) (x x' : H R (sp A) F 1)
    (h : Rel A B R F u x) (h' : Rel A B R F u' x') : Rel A B R F (u + u') (x + x') := by
  obtain ⟨s, hs, hx⟩ := h
  obtain ⟨s', hs', hx'⟩ := h'
  refine ⟨s + s', ?_, ?_⟩
  · rw [val_add, hs, hs']
    rfl
  · rw [map_add (f := _)]
    exact (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).2.1 s s' _ _ hx hx'

theorem rel_zero (R : Type) [CommRing R] (F : Shv R) : Rel A B R F 0 0 := by
  refine ⟨0, ?_, ?_⟩
  · rw [val_zero]
    rfl
  · rw [map_zero]
    exact isCls_zero R F _


open Classical in
def gam (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) : H R (sp A) F 1 :=
  if Algebra.Etale A B ∧ Module.FaithfullyFlat A B then Classical.epsilon (Rel A B R F u) else 0

theorem gam_spec [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) :
    Rel A B R F u (gam A B R F u) := by
  unfold gam
  rw [if_pos ⟨inferInstance, inferInstance⟩]
  exact Classical.epsilon_spec (rel_exists A B R F u)

theorem gam_eq [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B)
    (x : H R (sp A) F 1) : gam A B R F u = x ↔ Rel A B R F u x :=
  ⟨fun h => h ▸ gam_spec A B R F u, fun h => rel_unique A B R F u _ _ (gam_spec A B R F u) h⟩

def gamHom (R : Type) [CommRing R] (F : Shv R) : Z1 F A B →+ H R (sp A) F 1 where
  toFun := gam A B R F
  map_zero' := by
    by_cases h : Algebra.Etale A B ∧ Module.FaithfullyFlat A B
    · haveI := h.1
      haveI := h.2
      exact (gam_eq A B R F 0 0).2 (rel_zero A B R F)
    · unfold gam
      rw [if_neg h]
  map_add' u u' := by
    by_cases h : Algebra.Etale A B ∧ Module.FaithfullyFlat A B
    · haveI := h.1
      haveI := h.2
      exact (gam_eq A B R F _ _).2 (rel_add R F _ _ _ _ (gam_spec A B R F u) (gam_spec A B R F u'))
    · unfold gam
      rw [if_neg h, if_neg h, if_neg h, add_zero]

theorem cech1 : ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) [CommRing A], ∃ γ : ∀ (B : Type) [CommRing B] [Algebra A B], Z1 F A B →+ H R (sp A) F 1, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.FaithfullyFlat A B], (∀ u : Z1 F A B, γ B u = 0 ↔ ∃ v : (onRings F).obj (CommRingCat.of B), (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v - ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v) ∧ (∀ x : H R (sp A) F 1, pull R (spMap (algebraMap A B)) F 1 x = 0 → ∃ u, γ B u = x) ∧ (∀ u, pull R (spMap (algebraMap A B)) F 1 (γ B u) = 0) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Algebra.Etale A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : Z1 F A B) (u' : Z1 F A B'), (u' : (onRings F).obj (CommRingCat.of (B' ⊗[A] B'))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map φ φ).toRingHom)).hom u → γ B' u' = γ B u := by
  intro R _ F A _
  refine ⟨fun B => gamHom A B R F, ?_⟩
  intro B _ _ _ _
  have bij0 := GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 0 _ _ _ _ (GlobalTheory.T.isLimit_widePullbackCone_spec_single A B).some
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    change gam A B R F u = 0 ↔ _
    rw [gam_eq]
    constructor
    · rintro ⟨s, hs, hx⟩
      rw [map_zero] at hx
      obtain ⟨t, rfl⟩ := GlobalTheory.T.simplicialCochain_coboundary_of_class_zero R F _ s hx
      exact ⟨val t (Spec (CommRingCat.of B)) (P0 A B), by rw [← hs, val_coboundary_first_level]⟩
    · rintro ⟨v, hv⟩
      obtain ⟨t, ht⟩ := bij0.2 v
      have ht' : val t (Spec (CommRingCat.of B)) (P0 A B) = v := ht
      have hval : val (cobd t) (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) := by
        rw [val_coboundary_first_level, ht', hv]
      have hc : cobd (cobd t) = 0 := (cobd_eq_zero_iff A B R F _).2 (by rw [hval]; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)
      refine ⟨cobd t, hval, ?_⟩
      rw [map_zero]
      obtain ⟨x, hx⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).1 (cobd t) hc
      have h4 := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 0).2.2.2.1 t x hx
      rw [h4] at hx
      exact hx
  · intro x hx
    obtain ⟨s, hs, hcls⟩ := GlobalTheory.T.etaleCohomology_one_cechCocycle_of_pullback_zero R F _ _ (fB A B) x hx
    exact ⟨⟨val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B), (mem_Z1_iff_cocycle A B R F _).2 ((cobd_eq_zero_iff A B R F s).1 hs)⟩, (gam_eq A B R F _ x).2 ⟨s, rfl, hcls⟩⟩
  · intro u
    obtain ⟨s, hs, hcls⟩ := gam_spec A B R F u
    exact GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle R F (fB A B) s ((cobd_eq_zero_iff A B R F s).2 (by rw [hs]; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)) _ hcls
  · intro B' _ _ _ _ φ u u' hu
    change gam A B' R F u' = gam A B R F u
    rw [gam_eq]
    obtain ⟨s, hs, hcls⟩ := gam_spec A B R F u
    refine ⟨(free R).map ((cechMap (fB A B) (fB A B') _ (spec_algHom φ)).app (op ⦋1⦌)) ≫ s, ?_, ?_⟩
    · rw [val_cech_map_first_level, hs, hu]
    · have := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).2.2.2.2 _ (cechMap (fB A B) (fB A B') _ (spec_algHom φ)) s _ hcls
      rw [← pull_comp, cechMap_aug] at this
      exact this

end GlobalTheory.CechOne
end
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnitsNoeth

theorem exists_unit_of_mem_map_comap {A' B' : Type} [CommRing A'] [CommRing B'] [IsDomain B']
    [IsLocalRing B'] (f : A' →+* B') (b : B')
    (h : b ∈ ((Ideal.span {b}).comap f).map f) : ∃ (d : A') (w : B'ˣ), b = f d * w := by
  by_cases hb : b = 0
  · exact ⟨0, 1, by simp [hb]⟩
  by_contra hne
  push_neg at hne
  have hle : ((Ideal.span {b}).comap f).map f ≤ Ideal.span {b} * maximalIdeal B' := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hd
    obtain ⟨z, hz⟩ := hd
    rw [Ideal.mem_comap, hz]
    by_cases hzu : IsUnit z
    · exact absurd (by rw [hz]; exact (Units.mul_inv_cancel_right b hzu.unit).symm) (hne d hzu.unit⁻¹)
    · exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self b) ((mem_maximalIdeal z).2 hzu)
  obtain ⟨m, hm, hbm⟩ := (Ideal.mem_span_singleton_mul).1 (hle h)
  have h1 : m = 1 := by
    have : b * (m - 1) = 0 := by rw [mul_sub, hbm, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hb
    · exact sub_eq_zero.1 h0
  exact (mem_maximalIdeal m).1 hm (h1 ▸ isUnit_one)

theorem divConst_origin_noeth : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 →
      bA * cA = algebraMap A (Localization.AtPrime QA) sA →
    ∃ (a : T) (w : Oˣ), jA bA = algebraMap T O a * (w : O) := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ QA _ hQA jA hjA
    bA cA sA hs hbc
  obtain ⟨A', _, _, _, _, B', _, _, _, _, _, _, _, ι, α, β, γ, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.T.divisorsOfConstants_flat_normal_stage_at_origin T O hT P φ hφ hsh hP A i hi hil EA QA hQA jA hjA sA hs
  have hbc' : β bA * β cA = algebraMap A' B' (ι sA) := by
    have e := congrArg (fun g => g sA) h1
    simp only [RingHom.comp_apply] at e
    rw [e, ← hbc, map_mul]
  have hmem := GlobalTheory.T.divisor_descent_flat_normal_domains A' B' (ι sA) h4 h5 (β bA) (β cA) hbc'
  obtain ⟨d, w, hdw⟩ := exists_unit_of_mem_map_comap (algebraMap A' B') (β bA) hmem
  have e3 := congrArg (fun g => g d) h3
  simp only [RingHom.comp_apply] at e3
  refine ⟨α d, Units.map γ.toMonoidHom w, ?_⟩
  rw [← h2, RingHom.comp_apply, hdw, map_mul, e3]
  rfl

end GlobalTheory.VertUnitsNoeth
end

section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.LocAcyc

private theorem spread_torsor : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (DE : Type) (_ : CommRing DE)
      (_ : Algebra (GlobalTheory.LocAcyc.GenFib T E) DE)
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE ∧
      ∀ s : DE →+* GlobalTheory.LocAcyc.GenFib T O,
        (∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap O (GlobalTheory.LocAcyc.GenFib T O) (ψ e)) →
        Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := GlobalTheory.T.spread_torsor_to_etale_algebra
private theorem exists_maximal_over_closedPt : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := GlobalTheory.T.exists_maximal_over_closedPoint_closedFibre
private theorem section_at_closedPt : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := GlobalTheory.T.exists_section_strictHenselisation_closedFibre_point
private theorem specialisation_map : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := GlobalTheory.T.exists_specialisation_to_strictlyHenselian

theorem keyGeneric_of_keyClosedPts : KeyClosedPts → KeyGeneric := by
  intro hC T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hP hPeq q hq hqu
  rw [torsorsTrivial_iff]
  intro D _ _ act hD
  obtain ⟨E, _, _, _, _, _, ψ, DE, _, _, actE, hDE, hred⟩ := spread_torsor T O P φ hφ hSH.2.2.2 q hq D act hD

  set Q : Ideal E := (maximalIdeal O).comap ψ.toRingHom with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : (maximalIdeal O).comap φ = maximalIdeal (Localization.AtPrime P) := by
    haveI := hSH.2.2.1
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
    · intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x hu)
  have hQP : Q.comap (algebraMap (Polynomial T) E) = P := by
    rw [hQdef, Ideal.comap_comap]
    have h1 : ψ.toRingHom.comp (algebraMap (Polynomial T) E) = φ.comp (algebraMap (Polynomial T) _) := by
      rw [hφ]; exact ψ.comp_algebraMap
    rw [h1, ← Ideal.comap_comap, hloc]
    exact Localization.AtPrime.under_maximalIdeal (R := Polynomial T) (I := P)
  obtain ⟨y, hymax, hQy, hyne, hyT⟩ := exists_maximal_over_closedPt T E Q (hQP.trans hPeq)
  haveI : y.IsPrime := hymax.isPrime
  obtain ⟨S, _, _, _, _, _, hSy, hSflat, hSpieces, s, hs⟩ :=
    section_at_closedPt hC T E hAIC y hyT hyne q hq hqu DE actE hDE
  letI : Algebra E O := ψ.toRingHom.toAlgebra
  haveI : HenselianLocalRing O := hSH.1
  haveI : IsSepClosed (ResidueField O) := hSH.2.1
  obtain ⟨σ⟩ := specialisation_map E S O Q y hQy hSy rfl hSflat hSpieces
  have hσT : ∀ t : T, σ (algebraMap T S t) = algebraMap T O t := by
    intro t
    rw [IsScalarTower.algebraMap_apply T E S, σ.commutes, IsScalarTower.algebraMap_apply T (Polynomial T) E]
    change ψ (algebraMap (Polynomial T) E _) = _
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  have hM : Algebra.algebraMapSubmonoid S (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)).comap σ.toRingHom := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (hσT t).symm⟩
  let m : GenFib T S →+* GenFib T O := IsLocalization.map (GenFib T O) σ.toRingHom hM
  refine hred (m.comp s) fun e => ?_
  rw [RingHom.comp_apply, hs e]
  simp only [m, IsLocalization.map_eq]
  change algebraMap O (GenFib T O) (σ (algebraMap E S e)) = _
  rw [σ.commutes]
  rfl

end GlobalTheory.LocAcyc
end
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.lintegral_frame_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → ∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A E U z β hE hβ a w ha hw hw0
  classical
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hc := api_nsq_contOn A hE.isOpen hβ.1
  have hm := ContinuousOn.measurable_piecewise hc
    (continuousOn_const (c := (0 : ℝ)) (s := Uᶜ)) hUm
  set N : Y → ℝ := U.piecewise (A.nsq (A.kap + E) β) (fun _ => 0) with hN
  have hNU : ∀ y ∈ U, N y = A.nsq (A.kap + E) β y := fun y hy => by simp [hN, hy]
  have hΦ : Measurable fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y) :=
    ENNReal.measurable_ofReal.comp ((hm.mul (ha.norm.pow_const 2)).mul hw)
  rw [setLIntegral_congr_fun hUm
    (g := fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y)) (fun y hy => by simp only [hNU y hy]),
    GlobalTheory.T.lintegral_atlasMeasure_etale_pullback_lebesgue n Y ι La A U z hE _ hΦ]
  refine lintegral_congr fun x => ?_
  have hJ : 0 < A.nsq A.kap (jdet A z) x := by
    have := hE.det_ne (A.pick (x : Y)) x x.2 (A.mem_pick _)
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hB : 0 < A.nsq (A.kap + E) β x := by
    have : β (A.pick (x : Y)) x ≠ 0 := by
      exact hβ.2 _ x.2
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hwx := hw0 x x.2
  rw [hNU x x.2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold GlobalTheory.OTY.TwEst.wt
  rw [neg_add, neg_neg, Real.exp_add, Real.exp_neg, Real.exp_log hB, Real.exp_log hJ]
  ring
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.blockVacuumLattice_eq_comap_standardLattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ), StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') = (stdLat B.L (Ix D n n')).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  first | exact @GlobalTheory.BaseVacuum.laB_eq_comap | exact GlobalTheory.BaseVacuum.laB_eq_comap | (intros; apply GlobalTheory.BaseVacuum.laB_eq_comap <;> assumption)
end
