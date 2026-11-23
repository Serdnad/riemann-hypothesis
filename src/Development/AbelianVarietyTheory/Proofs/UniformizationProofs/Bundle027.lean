module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle066
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilProper

theorem isSeparated_of_comp_surjective {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.SemiAbelianDescent.isSeparated_of_comp <;> assumption

theorem surjective_specMap_mk (A : Type) [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) :
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
  obtain ⟨n, hn⟩ := hJ
  have hle : J ≤ nilradical A := fun x hx ↦ by
    rw [mem_nilradical]
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hle).2⟩

theorem isProper_and_geometricallyConnected_of_isNilpotent :
    ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (Y : Over (Spec (CommRingCat.of A))) [LocallyOfFiniteType Y.hom], (IsProper (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → IsProper Y.hom) ∧ (GeometricallyConnected (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → GeometricallyConnected Y.hom) := by
  intro A _ J hJ Y _
  have hsq : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap_mk A J hJ
  have hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨fun hP ↦ ?_, fun hG ↦ ?_⟩
  · have hcomp : IsProper (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
        ≫ Y.hom) := by
      rw [pullback.condition]
      infer_instance
    have : IsSeparated Y.hom :=
      isSeparated_of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom
    have : UniversallyClosed Y.hom :=
      UniversallyClosed.of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom
    exact { toIsSeparated := ‹_›, toUniversallyClosed := ‹_›, toLocallyOfFiniteType := ‹_› }
  · rw [geometricallyConnected_iff] at hG ⊢
    intro K _ y Z fst snd h
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    have hker : ∀ x ∈ J, φ.hom x = 0 := by
      obtain ⟨n, hn⟩ := hJ
      intro x hx
      have hx' : x ^ n = 0 := by
        have := Ideal.pow_mem_pow hx n
        rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      exact (IsNilpotent.map ⟨n, hx'⟩ φ.hom).eq_zero
    let ψ := Ideal.Quotient.lift J φ.hom hker
    have hφ : φ = CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom ψ := by
      ext x
      simp [ψ]
    rw [hφ, Spec.map_comp] at h
    let p : Z ⟶ pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
      pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [h.w, Category.assoc])
    apply hG (Spec.map (CommRingCat.ofHom ψ)) p snd
    have e : p ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) = fst :=
      pullback.lift_fst _ _ _
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [e]
    exact h

end GlobalTheory.NilProper
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.AdicValSum

theorem nullV_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) : NullV v x := by
  classical
  intro q
  obtain ⟨S, hS⟩ := h q
  refine S.finite_toSet.subset fun i hi => ?_
  by_contra hiS
  have h1 := hS S subset_rfl
  have h2 := hS (insert i S) (Finset.subset_insert i S)
  have hx : x i = (s - ∑ j ∈ S, x j) - (s - ∑ j ∈ insert i S, x j) := by
    rw [Finset.sum_insert hiS]
    ring
  have h3 : (q : WithTop ℚ) ≤ v (x i) := by
    rw [hx]
    exact le_trans (le_min h1 h2) (AddValuation.map_sub v _ _)
  exact absurd hi (not_lt.mpr h3)

theorem exists_le_on_finset {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (t : Finset F) :
    ∃ c : ℚ, ∀ y ∈ t, (c : WithTop ℚ) ≤ v y := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ : ∃ d : ℚ, (d : WithTop ℚ) ≤ v a := by
      by_cases htop : v a = ⊤
      · exact ⟨0, htop ▸ le_top⟩
      · exact ⟨(v a).untop htop, by rw [WithTop.coe_untop]⟩
    refine ⟨min c d, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact le_trans (WithTop.coe_le_coe.mpr (min_le_right c d)) hd
    · exact le_trans (WithTop.coe_le_coe.mpr (min_le_left c d)) (hc y hy)

theorem sumV_of_sumI {V : Type} [CommRing V] (I : Ideal V) {F : Type} [Field F] [Module V F] (φ : V → F)
    (hφ : ∀ (a : V) (y : F), a • y = φ a * y) (v : AddValuation F (WithTop ℚ))
    (hv : ∀ (n : ℕ) (a : V), a ∈ I ^ n → ((n : ℚ) : WithTop ℚ) ≤ v (φ a))
    {Ix : Type} {x : Ix → F} {s : F} (h : SumI I x s) : SumV v x s := by
  obtain ⟨N, hNfg, -, -, hconv⟩ := h
  obtain ⟨G, rfl⟩ := hNfg
  obtain ⟨c, hc⟩ := exists_le_on_finset v G
  have h0 : ∀ a : V, (0 : WithTop ℚ) ≤ v (φ a) := by
    intro a
    have := hv 0 a (by simp)
    simpa using this
  have hN : ∀ y ∈ Submodule.span V (G : Set F), (c : WithTop ℚ) ≤ v y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simp
    | add y z _ _ hy hz => exact le_trans (le_min hy hz) (AddValuation.map_add v y z)
    | smul a y _ hy =>
      rw [hφ, AddValuation.map_mul]
      simpa using add_le_add (h0 a) hy
  have hIN : ∀ n : ℕ, ∀ z ∈ I ^ n • Submodule.span V (G : Set F), (((n : ℚ) + c : ℚ) : WithTop ℚ) ≤ v z := by
    intro n z hz
    refine Submodule.smul_induction_on hz (fun r hr y hy => ?_) (fun y z hy hz => ?_)
    · rw [hφ, AddValuation.map_mul, WithTop.coe_add]
      exact add_le_add (hv n r hr) (hN y hy)
    · exact le_trans (le_min hy hz) (AddValuation.map_add v y z)
  intro q
  obtain ⟨S, hS⟩ := hconv ⌈q - c⌉₊
  refine ⟨S, fun T hT => le_trans ?_ (hIN _ _ (hS T hT))⟩
  have : q ≤ (⌈q - c⌉₊ : ℚ) + c := by linarith [Nat.le_ceil (q - c)]
  exact WithTop.coe_le_coe.mpr this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (Ix : Type) (x : Ix → F) (s : F), SumF (maximalIdeal V) F x s → SumV v x s ∧ NullV v x := by
  intro V _ _ _ ϖ hϖ F _ _ v hval Ix x s hsum
  letI : Module V F := Module.compHom F (algebraMap V (FractionRing V))
  have hI : SumI (maximalIdeal V) x s := hsum
  have hV : SumV v x s := by
    refine sumV_of_sumI (maximalIdeal V) (fun a => algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a))
      (fun a y => Algebra.smul_def _ _) v ?_ hI
    intro n a ha
    by_cases ha0 : a = 0
    · subst ha0
      simp
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hdvd : ϖ ^ n ∣ ϖ ^ k := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
      exact (Units.dvd_mul_left).mp ha
    have hnk : n ≤ k := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hdvd
    have hhv : HasVal ϖ (algebraMap V (FractionRing V) (↑u * ϖ ^ k)) (k : ℤ) :=
      ⟨u, by rw [map_mul, map_pow, zpow_natCast, mul_comm]⟩
    rw [hval _ _ hhv, WithTop.coe_le_coe]
    exact_mod_cast hnk
  exact ⟨hV, nullV_of_sumV hV⟩

end GlobalTheory.UT.AdicValSum
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

namespace EndTorus

theorem idempotent_trivial {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) [IsAdicComplete I R]
    (e : ℕ) (x : R ⧸ I ^ (e + 1)) (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hle : I ^ (e + 1) ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero e)
  have h0 : a₀ * a₀ - a₀ ∈ I := hle (Ideal.Quotient.eq.1 hx)
  have hm : (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic := by monicity!
  obtain ⟨a, ha, hI⟩ := HenselianRing.is_henselian (I := I) _ hm a₀ (by simpa [sq] using h0) (by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (2 * a₀ - 1)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    convert I.mul_mem_left 4 h0 using 1
    simp
    ring)
  have hnil : ∀ y ∈ I, IsNilpotent (Ideal.Quotient.mk (I ^ (e + 1)) y) := fun y hy =>
    ⟨e + 1, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hy _)⟩
  have ha' : a * (a - 1) = 0 := by
    have := ha.eq_zero
    simp at this
    linear_combination this
  rcases mul_eq_zero.1 ha' with h | h
  · left
    refine hx.eq_zero_of_isNilpotent (hnil _ ?_)
    simpa [h] using hI
  · right
    have h1 : a = 1 := sub_eq_zero.1 h
    have := hx.one_sub.eq_zero_of_isNilpotent (by simpa [h1] using hnil _ hI)
    exact (sub_eq_zero.1 this).symm

theorem connectedSpace_thickening {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)
    [hC : IsAdicComplete I R] (e : ℕ) : ConnectedSpace (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := by
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : PreconnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))) := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    obtain ⟨x, hx, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hU
    rcases idempotent_trivial I e x hx with rfl | rfl <;> simp
  exact ({ toNonempty := inferInstance } : ConnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))))

theorem torusEndOf_iff_appTop {S : Scheme.{0}} {X : Type} [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) : TorusEndOf X h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem isMonHom_of_mono {S : Scheme.{0}} {A B C : Over S} [MonObj A] [MonObj B] [MonObj C]
    (t : A ⟶ B) (i : B ⟶ C) [Mono i] [IsMonHom i] [IsMonHom (t ≫ i)] : IsMonHom t := by
  constructor
  · rw [← cancel_mono i, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

end EndTorus


open EndTorus in
theorem gtCoord_end_torus_abelian : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G), IsMonHom a → (∃! h : D.X →+ D.X, ∃ t, TorusEndOf D.X h t ∧ g.i ≫ a = t ≫ g.i) ∧ ∃! b : thickObj R I e D.P.A ⟶ thickObj R I e D.P.A, IsMonHom b ∧ a ≫ g.q = g.q ≫ b := by
  intro _ R _ _ I hR D e G _ _ g a ha
  obtain ⟨hN, -, -, hC⟩ := hR
  have := connectedSpace_thickening I e
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hk := g.isKernel
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D.P.A) :=
    { comm := inferInstance
      smooth := by have := D.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g.i ≫ a ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D.X _ hB (g.i ≫ a ≫ g.q) inferInstance).trans (Hom.one_def)
  have : Mono g.i := by
    have : Mono (η[thickObj R I e D.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback hk.flip (.infer_property _)
  constructor
  · let t := hk.lift (g.i ≫ a) (toUnit _) (by rw [Category.assoc, h1])
    have ht : t ≫ g.i = g.i ≫ a := hk.lift_fst _ _ _
    have : IsMonHom (t ≫ g.i) := ht ▸ inferInstance
    have : IsMonHom t := isMonHom_of_mono t g.i
    obtain ⟨h, hh⟩ := SplitTorusHom.exists_addMonoidHom t
    refine ⟨h, ⟨t, (torusEndOf_iff_appTop _ _).2 hh, ht.symm⟩, ?_⟩
    rintro h' ⟨t', h₁, h₂⟩
    obtain rfl : t' = t := by rw [← cancel_mono g.i, ht, h₂]
    ext χ
    exact SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
      (((torusEndOf_iff_appTop _ _).1 h₁ χ).symm.trans (hh χ))
  · obtain ⟨b, hb, hq⟩ := FlatQuotient.exists_desc g.q g.i (a ≫ g.q) hk h1
    have := FlatQuotient.epi_of_flat_surjective g.q
    refine ⟨b, ⟨hb, hq.symm⟩, ?_⟩
    rintro b' ⟨-, h⟩
    rw [← cancel_epi g.q, ← h, hq]

end GlobalTheory
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem weilIs_comp_iff_of_rosatiAdj : LL → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → RosatiAdj P.A P.L a a' → ∀ (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) (x y : Over.mk p ⟶ P.A), x ^ k = 1 → y ^ k = 1 → ∀ c, WeilIs P.A P.L k (x ≫ a) y c ↔ WeilIs P.A P.L k x (y ≫ a') c := by
  intro h S _ P a a' ha ha' hR F _ p k x y hx hy c
  exact GlobalTheory.weilIs_rosati_iff h.1.globalFns h.1.cube P a a' hR k x y hx hy c

end GlobalTheory.UT
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.exists_uniformizationEndomorphism_of_linear : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → ∀ a : O, ∃ E : EndU U.toUnifPre, E.aG = ιG.act a ∧ E.aA = ιA.act a ∧ E.aB = ιD.onB.act a ∧ (∀ χ, E.h χ = star a • χ) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), E.Act g g' ↔ GtAct ιD a g g' := by
  first | exact @GlobalTheory.UT.OLinEnd.main | exact GlobalTheory.UT.OLinEnd.main | (intros; apply GlobalTheory.UT.OLinEnd.main <;> assumption)
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem gs_res_global_scal_eq_cst {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (q : Z ⟶ Y) (z : Z) (V : Y.Opens) (hz : q z ∈ V) (c : R) :
    gs q z V (resTop V (scal p c)) = cst (q ≫ p) z c := by
  unfold resTop
  rw [gs_res q z le_top hz]
  unfold scal cst
  exact gs_pull q p z ⊤ trivial _

theorem gs_of_eq_sum_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (q : Z ⟶ Y) (z : Z) (V : Y.Opens) (hz : q z ∈ V) {n : ℕ} (c : Fin n → R) {a : Γ(Y, V)} {b : Fin n → Γ(Y, V)}
    (h : a = ∑ i, resTop V (scal p (c i)) * b i) :
    gs q z V a = ∑ i, cst (q ≫ p) z (c i) * gs q z V (b i) := by
  subst h
  rw [gs_fsum q z V hz]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul q z V hz, gs_res_global_scal_eq_cst p q z V hz]

theorem expandsAt_iff_stalks {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) :
    U.ExpandsAt e k σ f ↔ ∃ S : Finset D.toPre.X, ∀ (y : (thickObj R I e G).left) (J), Good D.toPre.P.L y J →
      (∀ α ∉ S, sval (f α) (pGl U e) y J = 0) ∧ ∀ jL, (fGl I G e) y ∈ U.LG.L.U jL →
        (wv U e (𝟙 _) y (J (pGl U e)) jL ^ k).val * sv U k σ (fGl I G e) y jL =
          ∑ α ∈ S, sval (f α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
    refine ⟨S, fun y J hJ => ?_⟩
    have hy := hS _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at hy
    exact hy
  · rintro ⟨S, hS⟩
    exact expandsAt_of_val U e k σ f S hS

theorem expandsAt_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k e n : ℕ) (c : Fin n → R) (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f : Fin n → ∀ α, D.toPre.SecB k α) (σ₀ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ : ∀ α, D.toPre.SecB k α), (∀ i, U.ExpandsAt e k (σ i) (f i)) → (∀ j, σ₀.f j = ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j) → (∀ α j, (f₀ α).f j = ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j) → U.ExpandsAt e k σ₀ f₀ := by
  intro R _ _ I D A G _ _ U k e n c σ f σ₀ f₀ hE hσ hf
  classical
  have hE' := fun i => (expandsAt_iff_stalks U e k (σ i) (f i)).1 (hE i)
  choose S hS using hE'
  refine (expandsAt_iff_stalks U e k σ₀ f₀).2 ⟨Finset.univ.biUnion S, fun y J hJ => ?_⟩
  have hc : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom := (Over.w _).trans (Over.w _).symm
  have key₀ : ∀ α, sval (f₀ α) (pGl U e) y J =
      ∑ i, cst (pGl U e ≫ D.toPre.P.A.hom) y (c i) * sval (f i α) (pGl U e) y J := fun α =>
    gs_of_eq_sum_scal D.toPre.P.A.hom (pGl U e) y _ (Good.mem hJ _ _) c (hf α _)
  refine ⟨fun α hα => ?_, fun jL hjL => ?_⟩
  · rw [key₀ α]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hS i y J hJ).1 α (fun h => hα (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩)), mul_zero]
  · have hmem : fGl I G e y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL) :=
      Set.mem_iInter.2 fun _ => hjL
    have keyσ : sv U k σ₀ (fGl I G e) y jL =
        ∑ i, cst (fGl I G e ≫ G.hom) y (c i) * sv U k (σ i) (fGl I G e) y jL :=
      gs_of_eq_sum_scal G.hom (fGl I G e) y _ hmem c (hσ _)
    have hR : ∑ α ∈ Finset.univ.biUnion S, sval (f₀ α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val =
        ∑ i, ∑ α ∈ Finset.univ.biUnion S,
          cst (fGl I G e ≫ G.hom) y (c i) * sval (f i α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [key₀ α, Finset.sum_mul, hc]
    rw [hR, keyσ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, (hS i y J hJ).2 jL hjL,
      Finset.sum_subset (Finset.subset_biUnion_of_mem S (Finset.mem_univ i))
        (fun α _ hα => by rw [(hS i y J hJ).1 α hα, zero_mul]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [_root_.mul_assoc]

end GlobalTheory
end
end
