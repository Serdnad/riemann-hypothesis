module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

private theorem isLocalHom_constantCoeff_ps (O : Type) [CommRing O] [IsLocalRing O] :
    IsLocalHom (PowerSeries.constantCoeff (R := O)) :=
  ⟨fun _ ha => PowerSeries.isUnit_iff_constantCoeff.2 ha⟩

private theorem constantCoeff_comp_sc {k E : Type} [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) :
    (PowerSeries.constantCoeff (R := E)).comp (sc p u) = p.O.subtype.comp (PowerSeries.constantCoeff (R := p.O)) := by
  refine RingHom.ext fun a => ?_
  show PowerSeries.constantCoeff (PowerSeries.rescale u (PowerSeries.map p.O.subtype a)) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, _root_.one_mul,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rfl

private theorem spMap_comp_spMap {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]

private theorem evAt_eq_of_eq {R : Type} [CommRing R] {X : Scheme.{0}} {a b : Sp R ⟶ X} (e : a = b) {U : X.Opens}
    (h : ⊤ ≤ a ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U) : evAt a h = evAt b h' := by
  subst e; rfl

theorem isRatPath_of_integral_at_places : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G] (ξ : Sp (PowerSeries E) ⟶ G.left) (u : Place k E → E), (∀ p, u p ≠ 0) → {p | ord p (u p) ≠ 0}.Finite → 0 < ∑ᶠ p, ord p (u p) → (∀ p : Place k E, ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p (u p)) ≫ ζ) → IsRatPath ξ := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx G _ ξ u hu0 hfin hpos hloc
  choose b ζ hb hpath hξ using hloc
  have hFF : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx)).2 E
  obtain ⟨p₀, -⟩ : ∃ p, ord p (u p) ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [finsum_eq_zero_of_forall_eq_zero hc] at hpos
    exact lt_irrefl _ hpos
  apply GlobalTheory.T.isRationalFormalPath_of_rationalExpansions E G.left ξ
  intro U _ h f
  set V : C.Opens := unitSec G ⁻¹ᵁ U with hV
  have hVne : (V : Set C).Nonempty := by
    let q : Sp E := IsLocalRing.closedPoint E
    refine ⟨(spMap p₀.O.subtype ≫ b p₀) q, ?_⟩
    have h2 : spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ = spMap p₀.O.subtype ≫ b p₀ ≫ unitSec G := by
      rw [hξ p₀, ← Category.assoc, spMap_comp_spMap, constantCoeff_comp_sc, ← spMap_comp_spMap, Category.assoc,
        (hpath p₀).zero]
    have h3 : (spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ) q ∈ U := h trivial
    rw [h2] at h3
    exact h3
  have hfinb := GlobalTheory.T.finite_places_centre_outside_open k K E C x hx V hVne
  have hUp : ∀ p, ⊤ ≤ (spMap (sc p (u p)) ≫ ζ p) ⁻¹ᵁ U := fun p => hξ p ▸ h
  choose e ψ he0 he1 heq using fun p => GlobalTheory.T.exists_bounded_denominator_along_valuationPath k E p (u p) G.left (ζ p) U (hUp p) f
  have key : ∀ p, ⊤ ≤ (b p) ⁻¹ᵁ V → ⊤ ≤ (ζ p) ⁻¹ᵁ U := by
    intro p hp
    haveI := isLocalHom_constantCoeff_ps p.O
    rw [GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 (PowerSeries p.O) G.left (ζ p) U]
    rw [← (IsLocalRing.comap_closedPoint (PowerSeries.constantCoeff (R := p.O)) :
      spMap (PowerSeries.constantCoeff (R := p.O)) (IsLocalRing.closedPoint p.O) = _)]
    show (spMap (PowerSeries.constantCoeff (R := p.O)) ≫ ζ p) (IsLocalRing.closedPoint p.O) ∈ U
    rw [(hpath p).zero]
    exact hp trivial
  refine GlobalTheory.T.isRational_powerSeries_of_adelicIntegral_positiveRadius k E hFF (evAt ξ h f) u e ψ hu0 hfin hpos he0 ?_ ?_
  · refine hfinb.subset fun p hp => ⟨b p, hb p, fun hbV => hp ?_⟩
    rw [he1 p (key p hbV), map_one]
    exact isUnit_one
  · intro p
    rw [evAt_eq_of_eq (hξ p) h (hUp p)]
    exact heq p

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem top_le_preimage_of_isDominant {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) [IsDominant x]
    (V : C.Opens) (hV : (V : Set C).Nonempty) : ⊤ ≤ x ⁻¹ᵁ V := by
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open V.isOpen hV
  intro z _
  have : z = y := Subsingleton.elim _ _
  subst this
  exact hy

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {C : Scheme.{0}} (b : Sp R ⟶ C)
    (V : C.Opens) (h : b (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ b ⁻¹ᵁ V := by
  intro z _
  have hs : z ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal z.2.ne_top)
  exact (hs.map b.continuous).mem_open V.isOpen h

theorem locFrame_of_frames {k K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} (x : Sp K ⟶ C)
    {W : C.Modules} {r : ℕ} {V₀ V : C.Opens} {s : Fin r → Γ(W, V₀)} {t : Fin r → Γ(W, V)}
    (hs : IsFrame s) (ht : IsFrame t) (v : Place k K) (b : Sp v.O ⟶ C) (hb : spMap v.O.subtype ≫ b = x)
    (hbV : ⊤ ≤ b ⁻¹ᵁ V) (hx : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V)) :
    LocFrame x s v (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)) ∧
      (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)).det ≠ 0 := by
  set M := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀)) with hM
  refine ⟨⟨b, V, t, V₀ ⊓ V, inf_le_left, inf_le_right, hx, M, hb, hbV, ht, fun j => ?_, rfl⟩, ?_⟩
  · have := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).sum_repr (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀) j)
    simp only [IsFrame.basis_apply] at this
    rw [hM]
    simp only [Module.Basis.toMatrix_apply, IsFrame.basis_apply]
    exact this.symm
  · have hu : IsUnit M.det := by
      have := Module.Basis.toMatrix_mul_toMatrix_flip (ht.basis (inf_le_right : V₀ ⊓ V ≤ V))
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, this, Matrix.det_one]⟩
    have := (hu.map (evAt x hx)).ne_zero
    rwa [RingHom.map_det] at this

theorem unimod_one' {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v : Place k F) :
    Unimod v (1 : Matrix (Fin n) (Fin n) F) :=
  ⟨fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h], by simp⟩

theorem exists_frame_locFrames : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  intro k K _ _ _ _ _ C _ x hx W r hW
  haveI : IsDominant x := hx.2.1.1
  have hxx : spMap (algebraMap K K) ≫ x = x := by
    change spMap (RingHom.id K) ≫ x = x
    exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp x)
  obtain ⟨V₀, s, hη, hs⟩ := hW (x (IsLocalRing.closedPoint K))
  have hV₀ : (V₀ : Set C).Nonempty := ⟨_, hη⟩
  have hcen : ∀ v : Place k K, ∃ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x := fun v => by
    obtain ⟨b, hb, -⟩ := GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K K C x hx v
    exact ⟨b, hb.trans hxx⟩
  choose b hb using hcen
  have key : ∀ v, ∃ gv : Matrix (Fin r) (Fin r) K,
      LocFrame x s v gv ∧ gv.det ≠ 0 ∧ (⊤ ≤ b v ⁻¹ᵁ V₀ → gv = 1) := by
    intro v
    by_cases hv : ⊤ ≤ b v ⁻¹ᵁ V₀
    · have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V₀) := by
        rw [inf_idem]; exact top_le_preimage_of_isDominant x V₀ hV₀
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs hs v (b v) (hb v) hv hx'
      refine ⟨_, h1, h2, fun _ => ?_⟩
      rw [Module.Basis.toMatrix_self]
      simp
    · obtain ⟨V, t, hc, ht⟩ := hW (b v (IsLocalRing.closedPoint v.O))
      have hbV := top_le_preimage_of_closedPoint (b v) V hc
      have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V) := fun z hz =>
        ⟨top_le_preimage_of_isDominant x V₀ hV₀ hz, top_le_preimage_of_isDominant x V ⟨_, hc⟩ hz⟩
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs ht v (b v) (hb v) hbV hx'
      exact ⟨_, h1, h2, fun h => absurd h hv⟩
  choose g hg1 hg2 hg3 using key
  refine ⟨V₀, s, g, hV₀, hs, ⟨hg2, ?_⟩, hg1⟩
  refine (GlobalTheory.T.finite_places_centre_outside_open k K K C x hx V₀ hV₀).subset fun v hv => ⟨b v, (hb v).trans hxx.symm, fun h => hv ?_⟩
  rw [hg3 v h]
  exact unimod_one' v

end GlobalTheory.Nef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_spMap_fromSpecStalk {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (x : X)
    (hx : f (IsLocalRing.closedPoint (CommRingCat.of A)) = x) :
    ∃ g0 : X.presheaf.stalk x →+* A, spMap g0 ≫ X.fromSpecStalk x = f := by
  subst hx
  exact ⟨(Scheme.stalkClosedPointTo f).hom, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem ringHom_eq_of_fromSpecStalk {X : Scheme.{0}} (x : X) {B : Type} [CommRing B]
    (f f' : X.presheaf.stalk x →+* B) (h : spMap f ≫ X.fromSpecStalk x = spMap f' ≫ X.fromSpecStalk x) : f = f' := by
  have h' : spMap f = spMap f' := (cancel_mono (X.fromSpecStalk x)).mp h
  have := Spec.map_injective h'
  exact congrArg CommRingCat.Hom.hom this

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_constantCoeff_closedPoint (R : Type) [CommRing R] [IsLocalRing R] : (spMap (PowerSeries.constantCoeff (R := R))) (IsLocalRing.closedPoint (CommRingCat.of R)) = IsLocalRing.closedPoint (CommRingCat.of (PowerSeries R)) := by
  haveI : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (PowerSeries.constantCoeff (R := R)))) :=
    ⟨fun _ h => PowerSeries.isUnit_iff_constantCoeff.mpr h⟩
  exact Spec_closedPoint

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem path_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R) (n : ℕ), 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ ξ' : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G c b ξ' → (∀ (U : G.left.Opens) (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(G.left, U)) (j : ℕ), 0 < j → j < n → PowerSeries.coeff j (evAt ξ h f) = PowerSeries.coeff j (evAt ξ' h' f)) → ξ = ξ' := by
  intro S G _ R _ _ hqs c n hn hc b ξ ξ' hξ hξ' hlow
  set s : S := b (IsLocalRing.closedPoint (CommRingCat.of R)) with hs
  set x : G.left := unitSec G s with hx
  have hpt : ∀ q0 : Sp (PowerSeries R) ⟶ G.left, IsPath G c b q0 →
      q0 (IsLocalRing.closedPoint (CommRingCat.of (PowerSeries R))) = x := by
    intro q0 hq0
    have e := congrArg (fun q : Sp R ⟶ G.left => q (IsLocalRing.closedPoint (CommRingCat.of R))) hq0.zero
    change q0 (spMap PowerSeries.constantCoeff (IsLocalRing.closedPoint (CommRingCat.of R))) = unitSec G s at e
    rw [spMap_constantCoeff_closedPoint] at e
    exact e
  obtain ⟨π, ε, m, hSD, h1, h2, h3⟩ := GlobalTheory.T.exists_groupSchemeUnitStalkData S G s
  have hm := GlobalTheory.T.groupSchemeSquaring_cotangent_eq_two S G hqs s π ε m hSD
  obtain ⟨β, hβ⟩ := exists_spMap_fromSpecStalk b s rfl
  obtain ⟨g, hg⟩ := exists_spMap_fromSpecStalk ξ x (hpt ξ hξ)
  obtain ⟨g', hg'⟩ := exists_spMap_fromSpecStalk ξ' x (hpt ξ' hξ')
  have E1 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      k.comp π = PowerSeries.C.comp β := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk s
    rw [spMap_comp' π k, spMap_comp' β PowerSeries.C, Category.assoc, Category.assoc, hβ, hSD.str, ← Category.assoc, hk.base]
  have E2 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      PowerSeries.constantCoeff.comp k = β.comp ε := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk x
    rw [spMap_comp' k PowerSeries.constantCoeff, spMap_comp' ε β, Category.assoc, Category.assoc, hSD.unit, ← Category.assoc (spMap β), hβ, hk.zero]
  have E3 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      (PowerSeries.rescale c).comp k = k.comp m := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk x
    rw [spMap_comp' k (PowerSeries.rescale c), spMap_comp' m k, Category.assoc, Category.assoc, hSD.sq, hk.scale, Category.assoc]
  subst hg hg'
  have hlow' : ∀ j < n, ∀ f, PowerSeries.coeff j (g f) = PowerSeries.coeff j (g' f) := by
    intro j hj f
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have a := RingHom.congr_fun (E2 g hξ) f
      have a' := RingHom.congr_fun (E2 g' hξ') f
      simp only [RingHom.comp_apply] at a a'
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply, a, a']
    · obtain ⟨U, hxU, f0, rfl⟩ := TopCat.Presheaf.germ_exist _ f
      obtain ⟨hh, hev⟩ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.2.2.2.2 (PowerSeries R) G.left x g U hxU
      obtain ⟨hh', hev'⟩ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.2.2.2.2 (PowerSeries R) G.left x g' U hxU
      have := hlow U hh hh' f0 j hj0 hj
      rw [hev, hev'] at this
      exact this
  have := ringHom_powerSeries_eq_of_rescale _ _ R π ε m β c n h1 h2 h3 hm hn hc g g' (E1 g hξ) (E1 g' hξ')
    (E2 g hξ) (E2 g' hξ') (E3 g hξ) (E3 g' hξ') hlow'
  rw [this]

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_path_tan : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R] [Algebra ℚ R], Smooth G.hom → QuasiSeparated G.hom → ∀ (b : Sp R ⟶ S) (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∃ ξ, IsPath G 2 b ξ ∧ HasTan G b ξ τ w := by
  intro S G _ R _ _ _ hsm hqs b n V τ w hbV
  set s : S := b (IsLocalRing.closedPoint R)
  set β : S.presheaf.stalk s →+* R := (Scheme.stalkClosedPointTo b).hom
  have hβ : Spec.map (CommRingCat.ofHom β) ≫ S.fromSpecStalk s = b :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk b
  obtain ⟨-, -, -, hev4, -, -, hev7⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  have hsV : s ∈ V := (hev4 R S b V).1 hbV
  obtain ⟨π, ε, m, hSD, hεπ, hmπ, hεm⟩ := GlobalTheory.T.exists_groupSchemeUnitStalkData S G s
  have hfs := GlobalTheory.T.formallySmooth_stalk_unit_smooth_groupScheme S G hsm s π ε m hSD
  have hm2 := GlobalTheory.T.groupSchemeSquaring_cotangent_eq_two S G hqs s π ε m hSD
  obtain ⟨δ, hδ, hδπ, hδτ⟩ := GlobalTheory.T.exists_stalkDerivation_of_lieSheafSections S G R s π ε m β n V hsV τ w hSD
  obtain ⟨ψ, hψπ, hψ0, hψ1, hψ2⟩ := GlobalTheory.T.exists_path_formallySmooth_ring _ _ R π ε m β δ hfs hεπ hmπ hεm hm2 hδ hδπ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ G.left.fromSpecStalk (unitSec G s), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← hSD.str, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψπ,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hβ]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ0, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, hSD.unit, ← Category.assoc, hβ]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ2, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, hSD.sq, Category.assoc]
  · intro U hU V' hV he hb f
    have hs' : s ∈ V' := (hev4 R S b V').1 hb
    have hp : unitSec G s ∈ U := he hs'
    obtain ⟨h₁, e₁⟩ := hev7 (PowerSeries R) G.left (unitSec G s) ψ U hp
    rw [show evAt _ hU f = evAt _ h₁ f from rfl, e₁, hψ1, hδτ U hp V' hV he hs' f]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    obtain ⟨h₂, e₂⟩ := hev7 R S s β V' hs'
    rw [← e₂]
    have key : ∀ {b₁ b₂ : Sp R ⟶ S} (_ : b₁ = b₂) (k₁ : ⊤ ≤ b₁ ⁻¹ᵁ V') (k₂ : ⊤ ≤ b₂ ⁻¹ᵁ V') (g : Γ(S, V')),
        evAt b₁ k₁ g = evAt b₂ k₂ g := by
      rintro _ _ rfl _ _ _; rfl
    exact key hβ h₂ hb _

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

theorem GlobalTheory.Nef.RatRigidField.spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

namespace GlobalTheory.Nef

theorem isRatPath_map {F Ω : Type} [Field F] [Field Ω] (φ : F →+* Ω) {Y : Scheme.{0}}
    (ξ : Sp (PowerSeries F) ⟶ Y) (h : IsRatPath ξ) : IsRatPath (spMap (PowerSeries.map φ) ≫ ξ) := by
  obtain ⟨β, hβ⟩ := h
  have hinjP : Function.Injective
      ((algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp (PowerSeries.map φ)) :=
    (IsFractionRing.injective (PowerSeries Ω) (LaurentSeries Ω)).comp
      (PowerSeries.map_injective φ φ.injective)
  have hinjR : Function.Injective
      ((algebraMap (Polynomial Ω) (RatFunc Ω)).comp (Polynomial.mapRingHom φ)) :=
    (IsFractionRing.injective (Polynomial Ω) (RatFunc Ω)).comp
      (Polynomial.map_injective φ φ.injective)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : LaurentSeries F →+* LaurentSeries Ω, ψ.comp (algebraMap (PowerSeries F) (LaurentSeries F)) =
      (algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp (PowerSeries.map φ) :=
    by
    refine ⟨IsFractionRing.lift hinjP, ?_⟩
    ext1 x
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  obtain ⟨ρ, hρ0⟩ : ∃ ρ : RatFunc F →+* RatFunc Ω, ρ.comp (algebraMap (Polynomial F) (RatFunc F)) =
      (algebraMap (Polynomial Ω) (RatFunc Ω)).comp (Polynomial.mapRingHom φ) :=
    by
    refine ⟨IsFractionRing.lift hinjR, RingHom.ext fun x => ?_⟩
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  have hpol : ((algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp ρ).comp (algebraMap (Polynomial F) (RatFunc F)) =
      (ψ.comp (algebraMap (RatFunc F) (LaurentSeries F))).comp (algebraMap (Polynomial F) (RatFunc F)) := by
    refine RingHom.ext fun p => ?_
    have h1 : ρ (algebraMap (Polynomial F) (RatFunc F) p) =
        algebraMap (Polynomial Ω) (RatFunc Ω) (p.map φ) := by
      have := congrArg (fun f => f p) hρ0
      simpa using this
    have h2 : ψ (algebraMap (PowerSeries F) (LaurentSeries F) (p : PowerSeries F)) =
        algebraMap (PowerSeries Ω) (LaurentSeries Ω) (PowerSeries.map φ (p : PowerSeries F)) :=
      congrArg (fun f => f (p : PowerSeries F)) hψ
    have h3 : PowerSeries.map φ (p : PowerSeries F) = ((p.map φ : Polynomial Ω) : PowerSeries Ω) := by
      ext n; simp [Polynomial.coeff_map]
    have hc : ∀ (K : Type) [Field K] (q : Polynomial K),
        algebraMap (RatFunc K) (LaurentSeries K) (algebraMap (Polynomial K) (RatFunc K) q) =
          algebraMap (PowerSeries K) (LaurentSeries K) (q : PowerSeries K) :=
      fun K _ q => (RatFunc.coe_coe q).symm
    simp only [RingHom.comp_apply]
    rw [h1, hc, hc, h2, h3]
  have hρ : (algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp ρ =
      ψ.comp (algebraMap (RatFunc F) (LaurentSeries F)) :=
    IsLocalization.ringHom_ext (M := nonZeroDivisors (Polynomial F)) (S := RatFunc F) hpol
  refine ⟨spMap ρ ≫ β, ?_⟩
  have e1 : spMap (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ≫ spMap ρ =
      spMap ψ ≫ spMap (algebraMap (RatFunc F) (LaurentSeries F)) := by
    rw [← RatRigidField.spMap_comp, ← RatRigidField.spMap_comp, hρ]
  have e2 : spMap ψ ≫ spMap (algebraMap (PowerSeries F) (LaurentSeries F)) =
      spMap (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) ≫ spMap (PowerSeries.map φ) := by
    rw [← RatRigidField.spMap_comp, ← RatRigidField.spMap_comp, hψ]
  rw [← Category.assoc, e1, Category.assoc, hβ, ← Category.assoc, e2, Category.assoc]

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem ratRigid_of_field_map (S : Scheme.{0}) (G : Over S) [GrpObj G] (F Ω : Type) [Field F] [Field Ω]
    (φ : F →+* Ω) (b : Sp F ⟶ S) (h : RatRigid G (spMap φ ≫ b)) : RatRigid G b := by
  intro ξ hξ hr
  have hp := ((GlobalTheory.T.formalSquaringPaths_baseChange_and_hom).1 S G F Ω φ 2 1 b ξ hξ).1
  rw [PowerSeries.rescale_one, RingHom.id_comp, map_ofNat] at hp
  have e := h _ hp (isRatPath_map φ ξ hr)
  have hC : (PowerSeries.map φ).comp (PowerSeries.C (R := F)) = (PowerSeries.C (R := Ω)).comp φ := by
    ext1 x; simp
  have ht : spMap (PowerSeries.map φ) ≫ triv G b = triv G (spMap φ ≫ b) := by
    simp only [triv]
    rw [← Category.assoc, ← RatRigidField.spMap_comp, hC, RatRigidField.spMap_comp]
    simp only [Category.assoc]
  exact (GlobalTheory.T.spec_injectiveRingMap_cancellation).1 _ _ (PowerSeries.map φ) (PowerSeries.map_injective φ φ.injective) _ _ _
    (e.trans ht.symm)

end GlobalTheory.Nef
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.archimedeanExistence_of_complex_isomorphic_field : ∀ κ : Rule, Funct κ → Arch κ → ArchF κ := by
  first | exact @GlobalTheory.MBLow.archF_of_arch | exact GlobalTheory.MBLow.archF_of_arch | (intros; apply GlobalTheory.MBLow.archF_of_arch <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.cube_value_eq_first_jet_alternating_product : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (G : Geo ν d),
    (∀ (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
      (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
      valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    ∀ (W : Fin g → ℂ) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    IsD ν d W gm.b → ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      1 + TrivSqZeroExt.inr
        (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex (x + y))).left)) (x + y) W / G.frG (ν.J (ν.eA (d.ex (x + y))).left) (x + y) +
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / G.frG (ν.J (ν.eA (d.ex 0)).left) 0 -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x W / G.frG (ν.J (ν.eA (d.ex x)).left) x -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex y)).left)) y W / G.frG (ν.J (ν.eA (d.ex y)).left) y) := by
  first | exact @GlobalTheory.MBLow.Cl.CubeJet.cube_jet | exact GlobalTheory.MBLow.Cl.CubeJet.cube_jet | (intros; apply GlobalTheory.MBLow.Cl.CubeJet.cube_jet <;> assumption)
end
