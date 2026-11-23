module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorOrdersAllTraitsOverModuli
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndependentMember
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle633
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3238
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.HtpyLine

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]

theorem pull_bijective_of_ringEquiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (F : Shv R) (n : ℤ) : Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp, ← spMap_id]
    congr 1
    ext x
    simp
  have h2 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp, ← spMap_id]
    congr 1
    ext x
    simp
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h1, pull_id]
  · rw [← pull_comp, h2, pull_id]

theorem bijective_of_subsingleton {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Subsingleton M] [Subsingleton N]
    (f : M →+ N) : Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end GlobalTheory.EtC.HtpyLine

namespace GlobalTheory.EtC.HtpyLine

open Polynomial

theorem exists_cyclotomic_root_of_AIC (q : ℕ) [NeZero q] (T : Type) [CommRing T] [Nontrivial T] (hA : AIC T) :
    ∃ ζ : T, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨a, ha⟩ := hA (cyclotomic q T) (cyclotomic.monic q T)
    (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
  refine ⟨a, ?_⟩
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  exact ha

theorem htpy_AIC : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : T →+* Polynomial T)) (tw q i) := by
  intro q _ T _ _ _ hA hq i n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have hneg : ∀ E : Spc, Subsingleton (H (ZMod q) E (tw q i) n) := by
      intro E
      have hz : ∀ α : CochainComplex.HomComplex.Cochain ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i)) n, α = 0 := by
        intro α
        apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 α 0
        intro p s h U x
        have hs : s < 0 := by omega
        haveI := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q i) U).2.2.2 s hs)
        exact Subsingleton.elim _ _
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := a.mk_surjective
      obtain ⟨b, rfl⟩ := b.mk_surjective
      have : a = b := CochainComplex.HomComplex.Cocycle.ext (by rw [hz a.1, hz b.1])
      rw [this]
    haveI := hneg (sp T)
    haveI := hneg (sp (Polynomial T))
    exact bijective_of_subsingleton _
  · exact GlobalTheory.T.h_zero_pullback_twist_bijective q T (Polynomial T) Polynomial.C hq (exists_cyclotomic_root_of_AIC q T hA) inferInstance
      (fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he) (fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he) i
  · haveI hT : Subsingleton (Ht q (sp T) n i) := GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic q T hA hq n i hn
    haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
    have hqK : IsUnit (q : FractionRing T) := by simpa using hq.map (algebraMap T (FractionRing T))
    haveI hKt : Subsingleton (Ht q (sp (Polynomial (FractionRing T))) n i) := GlobalTheory.T.tateTwistAcyclic_spectrum_polynomial_of_isAlgClosed q (FractionRing T) hqK n i hn
    let e : TensorProduct T (FractionRing T) (Polynomial T) ≃+* Polynomial (FractionRing T) :=
      (polyEquivTensor T (FractionRing T)).symm.toRingEquiv
    haveI hTens : Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) (Polynomial T))) n i) :=
      (pull_bijective_of_ringEquiv e (tw q i) n).1.subsingleton
    have hC3 := GlobalTheory.T.etale_cohomology_ind_etale_base_change q T hA hq (Polynomial T) i n
    haveI : Subsingleton (Ht q (sp (Polynomial T)) n i) := hC3.1.subsingleton
    exact bijective_of_subsingleton _

end GlobalTheory.EtC.HtpyLine
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_local_heatOperators_abelianLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) ⇑DV Θ₁ → ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) ∧ (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) := by
  first | exact @GlobalTheory.HeatV.exists_heat_abLocus | exact GlobalTheory.HeatV.exists_heat_abLocus | (intros; apply GlobalTheory.HeatV.exists_heat_abLocus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.ideal_descent_to_component_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ UValThru Xo c C.i (𝟙 C.Z) A φ J d := by
  first | exact @GlobalTheory.UPoincDown.idealDescent | exact GlobalTheory.UPoincDown.idealDescent | (intros; apply GlobalTheory.UPoincDown.idealDescent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.divisor_orders_all_traits_over_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (ι : ℕ) (D : GlobalTheory.EffCartierData Y.Z), (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι := by
  first | exact @GlobalTheory.UPoinc.AllTraits.orders_all | exact GlobalTheory.UPoinc.AllTraits.orders_all | (intros; apply GlobalTheory.UPoinc.AllTraits.orders_all <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GalTrans

section Cong
variable {X : Type} [AddCommGroup X]

theorem cm_symm {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, hw⟩ := h
  exact ⟨-w, by rw [hw, smul_neg]; abel⟩

theorem cm_trans {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  exact ⟨w' + w, by rw [hw, hw', smul_add]; abel⟩

theorem cm_map {Y : Type} [AddCommGroup Y] (f : X →+ Y) {N : ℕ} {x y : X} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨f w, by rw [hw, map_add (f := _), map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : X}
    (h : (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.mp h
  change N • w = -x + y at hw
  refine ⟨-w, ?_⟩
  rw [smul_neg, hw]
  abel

theorem cm_mk {N : ℕ} {x y : X} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y := by
  obtain ⟨w, hw⟩ := h
  refine QuotientAddGroup.eq.mpr ⟨-w, ?_⟩
  change N • (-w) = -x + y
  rw [hw, smul_neg]
  abel
private theorem charZero_uTest_V {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) : CharZero u.V :=
  ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero

def matAct (E : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun v a := ∑ b, E a b • v b
  map_zero' := by ext a; simp
  map_add' v w := by ext a; simp [smul_add, Finset.sum_add_distrib]

end Cong


open MonObj in
theorem compare {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {p : ℕ} [Fact p.Prime]
    {y₀ : S.R →+* PadicAlgCl p} {y₁ : S'.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (u' : ρ'.UTest p y₁) (l : u.Lab)
    (l' : u'.Lab) (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left)
    (ha : IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a)
    (ha' : IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a')
    (hL : LBIso P₀.L (u.A.L.pull a)) (hL' : LBIso P₀.L (u'.A.L.pull a')) :
    ∃ e : u.D.toPre.X ≃+ u'.D.toPre.X, (∀ χ, l'.q (e χ) = l.q χ) ∧
      (∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A)
        (w : Sp (PadicAlgCl p) ⟶ P₀.A.left), 1 ≤ m → x ^ m = 1 → x' ^ m = 1 → w ≫ P₀.A.hom = 𝟙 _ → w ≫ a = x.left →
        w ≫ a' = x'.left → ∃ pk pk', QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x ∧
          QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' ∧ CongMod m pk'.y (e pk.y)) ∧
      ∀ (m : ℕ) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), 1 ≤ m →
        QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) m)
          (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w : Sp (PadicAlgCl p) ⟶ P₀.A.left),
          QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x ∧ x ^ m = 1 ∧ w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧
          w ≫ a' = x'.left ∧ CongMod m pk'.y (e pk.y) := by
  obtain ⟨e, hps, hcg⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations S S' ρ ρ' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI := charZero_uTest_V u
  haveI := charZero_uTest_V u'
  refine ⟨e, fun χ => ?_, fun m x x' w hm hx hx' hw hwa hwa' => ?_, fun m pk' x' hm hpk' => ?_⟩
  · have h1 := (hps χ _).1 (l.q_eq χ)
    have h2 := l'.q_eq (e χ)
    have h3 := Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 h1)
    linarith
  · obtain ⟨f, hf1, hf2, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨f', hf1', hf2', -⟩ := GlobalTheory.ZH.uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    obtain ⟨pk, rfl⟩ := hf2 x hx
    obtain ⟨pk', rfl⟩ := hf2' x' hx'
    have q1 := (hf1 pk (f pk)).2 rfl
    have q2 := (hf1' pk' (f' pk')).2 rfl
    exact ⟨pk, pk', q1, q2, hcg m pk pk' _ _ w hm q1 q2 hw hwa hwa'⟩
  · have hx' : x' ^ m = 1 := by
      have h0 := hpk'
      unfold QkToAkU at h0
      obtain ⟨w0, hw0⟩ := u'.U.ext
      have h1 := h0 w0 hw0
      unfold QkToAk at h1
      exact h1.1
    obtain ⟨w, x, hw, hwa', hwa, hx⟩ :=
      GlobalTheory.PtTrans.ptTrans (PadicAlgCl p) u'.A u.A P₀ a' a ha' ha m x' hx'
    obtain ⟨f, hf1, hf2, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨pk, rfl⟩ := hf2 x hx
    have q1 := (hf1 pk (f pk)).2 rfl
    exact ⟨pk, f pk, w, q1, hx, hw, hwa, hwa', hcg m pk pk' _ _ w hm q1 hpk' hw hwa hwa'⟩


theorem isLab_conj : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∀ (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro g n F W Z i X₁ hg hn hodd hi hE8 hth hpr ε₁ hdiag D σ s hs a hga p _ z₁ c y h h' yy hlab
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', hsame', hi₀', hR', y₀, hy₀, u, l, j, hq, hlabl, hmat⟩ := hlab
  obtain ⟨yy₂, hlab₂⟩ := exists_isLab g n F W Z i D.X hg hn hodd hi hE8 hth D.proj D.ε D.diag p
    ((y ≫ s) (cPt p)) (D.lift c (y ≫ s) h')
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hsame₂, hi₀₂, hR₂, y₁, hy₁, u₂, l₂, j₂, hq₂, -, -⟩ := hlab₂
  obtain ⟨P₀, b, t, ε₀, hb, ht, lb, lt, hε, hp⟩ := hga
  obtain ⟨Q, b', b'', hb', hb'', lb', lb'', hpts, hend⟩ :=
    exists_generic D.X.ρ D.ε ρ' ε' ρ₂ ε₂ (fun x => x) (fun x => x) hsame' hsame₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) a P₀ b t ε₀
      hb ht lb lt hε hp
  haveI : IsDedekindDomain D.X.o₁ := ArithBase.ded (Ω := D.X.Ω₁)
  have hR₂' : R₂ ≤ D.X.M.O (((gPt p ≫ y) ≫ s) (closedPoint (PadicAlgCl p))) := by
    rw [Category.assoc]; exact hR₂
  have hy₁' : ∀ r : R₂, y₁ r = D.X.M.val ((gPt p ≫ y) ≫ s) r := by
    intro r; rw [Category.assoc]; exact hy₁ r
  have hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := by
    have hn := D.X.normal
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme
    obtain ⟨h1, h2⟩ := hn
    exact fun x => ⟨h1 x, h2 x⟩
  obtain ⟨P₁, a₁, a₂, ha₁, ha₂, la₁, la₂, hpt, hen⟩ :=
    spread D.X.M hM ρ' ρ₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) s hs (gPt p ≫ y) hR' hR₂' y₀ y₁ hy₀ hy₁' u u₂ Q hb' hb''
      lb' lb''
  obtain ⟨e, heq, hfw, hbk⟩ := compare u u₂ l l₂ P₁ a₁ a₂ ha₁ ha₂ la₁ la₂
  have hN : 1 ≤ D.X.S.r * D.X.S.N := by
    obtain ⟨jj, -, hr⟩ := D.X.ρ.r_eq
    rw [hr, D.X.ρ.N_eq]
    have hnp := D.X.ρ.n_prime.pos
    exact Nat.mul_pos (pow_pos hnp _) (pow_pos (pow_pos hnp _) _)
  refine ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hsame₂, hi₀₂, hR₂, y₁, hy₁, u₂, l₂, e.symm.trans j, ?_, ?_, ?_⟩
  · intro χ
    have h1 := heq (e.symm χ)
    rw [AddEquiv.apply_symm_apply] at h1
    rw [h1]
    exact hq (e.symm χ)
  · intro bb χ hb2
    obtain ⟨wg, hwg, hwg1, hwg2⟩ := hpts bb
    obtain ⟨w1, x1, x2, hw1, hw1a, hw1b, hx1, hx2⟩ := hpt (a bb) bb wg hwg hwg1 hwg2
    have hx1p := GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u (a bb) x1 hx1
    have hx2p := GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ₂ p y₁ u₂ bb x2 hx2
    obtain ⟨pk, pk2, hq1, hq2, hc12⟩ := hfw (D.X.S.r * D.X.S.N) x1 x2 w1 hN hx1p hx2p hw1 hw1a hw1b
    have e1 := l.yy_eq (a bb) pk x1 hq1 hx1
    have e2 := l₂.yy_eq bb pk2 x2 hq2 hx2
    have c1 : CongMod (D.X.S.r * D.X.S.N) χ pk2.y := cm_of_mk (hb2.symm.trans e2)
    have c2 := cm_trans c1 hc12
    have c3 : CongMod (D.X.S.r * D.X.S.N) (e.symm χ) pk.y := by
      have c4 := cm_map e.symm.toAddMonoidHom c2
      simpa using c4
    have e3 : l.yy (a bb) = QuotientAddGroup.mk (e.symm χ) := e1.trans (cm_mk (cm_symm c3))
    exact hlabl (a bb) (e.symm χ) e3
  · intro m pk pk' x x' E hm hq hq' hxx
    obtain ⟨pk0, x0, w0, hq0, hx0, hw0, hw0a, hw0b, hc0⟩ := hbk m pk x hm hq
    obtain ⟨pk0', x0', w0', hq0', hx0', hw0', hw0a', hw0b', hc0'⟩ := hbk m pk' x' hm hq'
    obtain ⟨η, hη1, hη2⟩ := hend E
    have hyp : w0' ≫ a₂ ≫ u₂.φ = w0 ≫ a₂ ≫ u₂.φ ≫ (ε₂ E).left := by
      rw [← hw0b', ← hw0b] at hxx
      simpa only [Category.assoc] using hxx
    have key : x0'.left ≫ u.φ = x0.left ≫ u.φ ≫ (ε' E).left := by
      have k1 := hen (ε' E) (ε₂ E) η hη1 hη2 w0 w0' hw0 hw0' hyp
      rw [← hw0a', ← hw0a]
      simpa only [Category.assoc] using k1
    have hm0 := hmat m pk0 pk0' x0 x0' E hm hq0 hq0' key
    have A : CongMod m (j (e.symm pk'.y)) (j pk0'.y) := by
      have A1 := cm_map (e.symm.trans j).toAddMonoidHom hc0'
      simpa using A1
    have B : CongMod m (j (e.symm pk.y)) (j pk0.y) := by
      have B1 := cm_map (e.symm.trans j).toAddMonoidHom hc0
      simpa using B1
    have B2 := cm_map (matAct E) B
    exact cm_trans A (cm_trans hm0 (cm_symm B2))

end GlobalTheory.Poinc.GalTrans
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumAdj

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D₁ D₂ : DegData R (maximalIdeal R)}
  {A A₁ A₂ : PolAV (Sp (FractionRing R))} {G G₁ G₂ : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G₁] [IsCommMonObj G₁]
  [GrpObj G₂] [IsCommMonObj G₂]

theorem exists_linHom_end (hR : Base R) (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) {a a' h h'}
    (H : Adj (pol D) (pol D) a a' h h') : ∃ g, LinHom U.toUnifPre U.toUnifPre a h' g := by
  have hE := GlobalTheory.MumFam.AdjEnd.endData_of_adj R hR D a a' h h' H
  obtain ⟨b, hb⟩ := GlobalTheory.Mum.EndThick.formalEnd_exists R hR.1 D A G hG U a a' h h' hE
  obtain ⟨g, hg, e⟩ := GlobalTheory.T.mumford_formalEndomorphism_algebraic R hR D A G hG U a a' h h' hE b hb
  exact ⟨g, linHom_iff_linEnd.2 ⟨hg, (funext e : _ = b).symm ▸ hb⟩⟩

theorem exists_linHom (hR : Base R) (hG₁ : IsSemiAbelian G₁) (hG₂ : IsSemiAbelian G₂) (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁)
    (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) {a : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A}
    {h : D₁.toPre.X →+ D₂.toPre.X} {h' : D₂.toPre.X →+ D₁.toPre.X} (H : Adj (pol D₁) (pol D₂) a a' h h') :
    ∃ u u', LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧
      GAdj U₁.LG.L U₂.LG.L u u' := by
  obtain ⟨D, A, U, i₁, p₁, i₂, p₂, j₁, q₁, j₂, q₂, hG, ip₁, ip₂, jq₁, jq₂, ad₁, ad₂, l₁, r₁, l₂, r₂, g₁, g₂⟩ :=
    GlobalTheory.T.product_uniformised_groups_sum_data R hR D₁ A₁ G₁ hG₁ U₁ D₂ A₂ G₂ hG₂ U₂
  have H' := GlobalTheory.MumFam.Adj.comp R _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.MumFam.Adj.comp R _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.MumFam.adj_symm R _ _ _ _ _ _ ad₁) H) ad₂
  obtain ⟨g, hg⟩ := exists_linHom_end hR hG U H'
  obtain ⟨g', hg'⟩ := exists_linHom_end hR hG U (GlobalTheory.MumFam.adj_symm R _ _ _ _ _ _ H')
  have ros : GAdj U.LG.L U.LG.L g g' := GlobalTheory.Mum.linEnd_adjoint_lbIso R hR D A _ hG U _ _ _ _ (GlobalTheory.MumFam.AdjEnd.endData_of_adj R hR D _ _ _ _ H') g g'
    (linHom_iff_linEnd.1 hg) (linHom_iff_linEnd.1 hg')
  refine ⟨_, _, ?_, ?_, GlobalTheory.MumFam.gAdj_swap_comp.2 _ _ _ _ _ _ _ U₁.LG.isLB U.LG.isLB U₂.LG.isLB _ _ _ _
    (GlobalTheory.MumFam.gAdj_swap_comp.2 _ _ _ _ _ _ _ U₁.LG.isLB U.LG.isLB U.LG.isLB _ _ _ _ g₁ ros)
    (GlobalTheory.MumFam.gAdj_swap_comp.1 _ _ _ _ _ U₂.LG.isLB U.LG.isLB _ _ g₂)⟩
  · have := (l₁.comp hg).comp r₂
    convert this using 1
    · change a = (i₁ ≫ (p₁ ≫ a) ≫ i₂) ≫ p₂
      simp only [Category.assoc, ip₂, Category.comp_id, reassoc_of% ip₁]
    · ext y
      change h' y = q₁ (j₁ (h' (q₂ (j₂ y))))
      rw [jq₁, jq₂]
  · have := l₂.comp (hg'.comp r₁)
    convert this using 1
    · change a' = i₂ ≫ (p₂ ≫ a' ≫ i₁) ≫ p₁
      simp only [Category.assoc, ip₁, Category.comp_id, reassoc_of% ip₂]
    · ext y
      change h y = q₂ (j₂ (h (q₁ (j₁ y))))
      rw [jq₁, jq₂]

end

theorem adj_groups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A) (h : D₁.toPre.X →+ D₂.toPre.X) (h' : D₂.toPre.X →+ D₁.toPre.X), Adj (pol D₁) (pol D₂) a a' h h' → ∃ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧ GAdj U₁.LG.L U₂.LG.L u u' := fun R _ _ _ hR D₁ A₁ G₁ _ _ hG₁ U₁ D₂ A₂ G₂ _ _ hG₂ U₂ _ _ _ _ H =>
  exists_linHom hR hG₁ hG₂ U₁ U₂ H

end GlobalTheory.MumAdj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.twistedThetaSum_zeta_exponent_independent_member : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ Y₁) (𝔪₁ : UMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : (Fin 8 → Y₁) → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ Y₂) (𝔪₂ : UMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : (Fin 8 → Y₂) → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  first | exact @GlobalTheory.Poinc.Sep.twistSum_indep | exact GlobalTheory.Poinc.Sep.twistSum_indep | (intros; apply GlobalTheory.Poinc.Sep.twistSum_indep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.GenericEnd.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
  intro R _ _ _ hB D A G _ _ hG U O _ _ _ o a
  have hE := (GlobalTheory.Mum.endData_symm_and_ofOAct R D.toPre).2 O o a
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_adjointEndomorphisms_action_uniformisedThickenings R hB.1 D A G hG U _ _ _ _ hE
  obtain ⟨g, hg, hgb⟩ := GlobalTheory.T.mumford_formalEndomorphism_algebraic R hB D A G hG U _ _ _ _ hE b hb
  obtain ⟨f, hf, hact⟩ := GlobalTheory.Mum.GenericEnd.exists_generic_of_formal U.toUnifPre (o.onB.act a)
    (DistribSMul.toAddMonoidHom D.toPre.X (star a)) b hb g hg hgb
  have hfun : (⇑(DistribSMul.toAddMonoidHom D.toPre.X (star a)) : D.toPre.X → D.toPre.X) = fun χ => star a • χ :=
    funext fun χ => DistribSMul.toAddMonoidHom_apply _ _ χ
  rw [hfun] at hact
  exact ⟨f, hf, hact⟩
end
