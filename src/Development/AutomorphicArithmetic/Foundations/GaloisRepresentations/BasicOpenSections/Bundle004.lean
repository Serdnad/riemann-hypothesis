module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma clopen_basicOpen {X : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    IsClopen (X.basicOpen e : Set X) := by
  have hsum : X.basicOpen e ⊔ X.basicOpen (1 - e) = ⊤ := by
    apply le_antisymm le_top
    have h := X.basicOpen_add_le e (1 - e)
    rwa [add_sub_cancel, Scheme.basicOpen_one] at h
  have hprod : X.basicOpen e ⊓ X.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, mul_sub, mul_one, he.eq, sub_self, Scheme.basicOpen_zero]
  have hc : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    constructor
    · intro hx hx'
      have hin : x ∈ X.basicOpen e ⊓ X.basicOpen (1 - e) := TopologicalSpace.Opens.mem_inf.mpr ⟨hx, hx'⟩
      rw [hprod] at hin
      simpa using hin
    · intro hx
      have hin : x ∈ X.basicOpen e ⊔ X.basicOpen (1 - e) := by
        rw [hsum]
        trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hin with h | h
      · exact h
      · exact absurd h hx
  refine ⟨?_, (X.basicOpen e).isOpen⟩
  rw [hc]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

private noncomputable def rho {κ : Type} [Field κ] {W : Scheme.{0}} (z : gp κ ⟶ W) : Γ(W, ⊤) →+* κ :=
  (z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom

private lemma mem_basicOpen_iff {κ : Type} [Field κ] {W : Scheme.{0}} (z : gp κ ⟶ W) (e : Γ(W, ⊤)) :
    pt z ∈ W.basicOpen e ↔ rho z e ≠ 0 := by
  have h1 : pt z ∈ W.basicOpen e ↔ IsLocalRing.closedPoint κ ∈ (gp κ).basicOpen (z.appTop e) := by
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  rw [h1, basicOpen_eq_of_affine']
  refine (PrimeSpectrum.mem_basicOpen _ _).trans ?_
  change _ ∉ IsLocalRing.maximalIdeal κ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, isUnit_iff_ne_zero]
  rfl

private lemma rho_inj {κ : Type} [Field κ] {W : Scheme.{0}} [IsAffine W] {z z' : gp κ ⟶ W}
    (h : rho z = rho z') : z = z' := by
  apply ext_of_isAffine
  have : z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom = z'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom :=
    CommRingCat.hom_ext h
  exact (cancel_mono _).mp this

private lemma rho_comp (V : Type) [CommRing V] [IsLocalRing V] {W : Scheme.{0}}
    (g : W ⟶ Spec (CommRingCat.of V)) (z : gp (IsLocalRing.ResidueField V) ⟶ W) (hz : z ≫ g = resPt V) :
    (rho z).comp ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ g.appTop).hom = IsLocalRing.residue V := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ (z ≫ g).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField V))).hom =
      CommRingCat.ofHom (IsLocalRing.residue V) := by
    rw [hz, resPt, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have h2 := congrArg CommRingCat.Hom.hom key
  exact h2

theorem UpperTheory.Gal.Mod.clopenAt :
    ResClosed → HensSplit → ClopenAt := by
  intro _ hHS V _ _ _ _ W g _ z₀ hz₀
  haveI : IsAffine W := isAffine_of_isAffineHom g
  set φ : V →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ g.appTop).hom with hφ
  have hfin : φ.Finite := by
    have h1 := g.finite_appTop
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (fun a => ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom a, by simp⟩)
    exact h1.comp h2
  letI : Algebra V Γ(W, ⊤) := φ.toAlgebra
  haveI : Module.Finite V Γ(W, ⊤) := hfin
  have hc : ∀ z : gp (IsLocalRing.ResidueField V) ⟶ W, z ≫ g = resPt V →
      ∀ v : V, rho z (φ v) = IsLocalRing.residue V v := by
    intro z hz v
    exact RingHom.congr_fun (rho_comp V g z hz) v
  have hsurj : ∀ z : gp (IsLocalRing.ResidueField V) ⟶ W, z ≫ g = resPt V →
      Function.Surjective (rho z) := by
    intro z hz r
    obtain ⟨v, hv⟩ := IsLocalRing.residue_surjective r
    exact ⟨φ v, by rw [hc z hz v, hv]⟩
  have hmax : (RingHom.ker (rho z₀)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (hsurj z₀ hz₀)
  obtain ⟨e, he, hem, hoth⟩ := hHS V Γ(W, ⊤) (RingHom.ker (rho z₀)) hmax
  refine ⟨W.basicOpen e, clopen_basicOpen he, ?_⟩
  intro z hz
  rw [SetLike.mem_coe, mem_basicOpen_iff]
  constructor
  · intro hne
    have hk : RingHom.ker (rho z) = RingHom.ker (rho z₀) := by
      by_contra hk
      exact hne (RingHom.mem_ker.mp
        (hoth _ (RingHom.ker_isMaximal_of_surjective _ (hsurj z hz)) hk))
    apply rho_inj
    ext a
    obtain ⟨v, hv⟩ := IsLocalRing.residue_surjective (rho z₀ a)
    have hmem : a - φ v ∈ RingHom.ker (rho z₀) := by
      rw [RingHom.mem_ker, map_sub, hc z₀ hz₀ v, hv, sub_self]
    rw [← hk, RingHom.mem_ker, map_sub, sub_eq_zero, hc z hz v, hv] at hmem
    exact hmem
  · rintro rfl
    exact fun h => hem (RingHom.mem_ker.mpr h)
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma natCast_eq_zero_of_pt {p : ℕ} {Y : Scheme.{0}} {Ω : Type} [Field Ω] (x : gp Ω ⟶ Y)
    (h : pt x ∉ Y.basicOpen (p : Γ(Y, ⊤))) : (p : Ω) = 0 := by
  by_contra hne
  apply h
  have hu : IsUnit ((ConcreteCategory.hom (Scheme.Hom.app x ⊤)) (p : Γ(Y, ⊤))) := by
    rw [map_natCast]
    have e : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (p : Ω) = (p : Γ(gp Ω, ⊤)) := map_natCast _ p
    have hu0 := (IsUnit.mk0 _ hne).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    rw [e] at hu0
    exact hu0
  have hpre := Scheme.preimage_basicOpen x (p : Γ(Y, ⊤))
  rw [Scheme.basicOpen_of_isUnit _ hu] at hpre
  have hm : IsLocalRing.closedPoint Ω ∈ x ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤)) := by
    rw [hpre]
    trivial
  exact hm

private lemma sp_closedPoint {K L : Type} [Field K] [Field L] (a : K →+* L) :
    (sp a) (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint K := by
  exact IsLocalRing.comap_closedPoint a

private lemma resPt_closedPoint (V : Type) [CommRing V] [IsLocalRing V] :
    (resPt V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint V := by
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue V)

private lemma exists_frob (p f : ℕ) (hp : p.Prime) (F : Type) [Field F] (h : (p : F) = 0) :
    ∃ φ : F →+* F, ∀ a, φ a = a ^ p ^ f := by
  haveI : CharP F p := (CharP.charP_iff_prime_eq_zero hp).2 h
  haveI : ExpChar F p := ExpChar.prime hp
  exact ⟨iterateFrobenius F p f, fun a => iterateFrobenius_def p f a⟩

theorem UpperTheory.Gal.Mod.cycAll :
    ResClosed → ValLift → CycRes → CycExt → CycAll := by
  intro hRC hVL hCR hCE p f n hp Y π T w hOne hPt hdense hbasic Ω _ _ x hgen
  obtain ⟨η, hη, hsp⟩ := hdense (pt x)
  obtain ⟨V, _, _, _, _, y, Ω', _, _, a, b, hpV, hsq⟩ := hVL p Y Ω x η hsp hη
  haveI := hRC V
  have hx0 : pt x ∉ Y.basicOpen (p : Γ(Y, ⊤)) := fun h => hgen.1 (hbasic _ h)
  have hptA : pt (sp a ≫ x) = pt x := by
    change x (sp a (IsLocalRing.closedPoint Ω')) = _
    rw [sp_closedPoint]
    rfl
  have hptB : pt (sp b ≫ resPt V ≫ y) = y (IsLocalRing.closedPoint V) := by
    change y (resPt V (sp b (IsLocalRing.closedPoint Ω'))) = _
    rw [sp_closedPoint, resPt_closedPoint]
  have hyx : y (IsLocalRing.closedPoint V) = pt x := by
    rw [← hptB, ← hsq, hptA]
  have hpΩ := natCast_eq_zero_of_pt x hx0
  have hpΩ' := natCast_eq_zero_of_pt (sp a ≫ x) (by rw [hptA]; exact hx0)
  have hpR := natCast_eq_zero_of_pt (resPt V ≫ y) (by
    change y (resPt V (IsLocalRing.closedPoint _)) ∉ _
    rw [resPt_closedPoint, hyx]
    exact hx0)
  obtain ⟨φ, hφ⟩ := exists_frob p f hp Ω hpΩ
  obtain ⟨φ', hφ'⟩ := exists_frob p f hp Ω' hpΩ'
  obtain ⟨ψ, hψ⟩ := exists_frob p f hp (IsLocalRing.ResidueField V) hpR
  refine ⟨φ, hφ, ?_⟩
  have hW : ∀ j, IsWt (T j).p (w j) := fun j => (hOne j).1
  have h1 := hCR p (p ^ f) n Y π T w hOne hPt V hpV y (by rw [hyx]; exact hgen) ψ hψ
  have h2 := (hCE p (p ^ f) n Y T w hW _ Ω' b ψ φ'
    (RingHom.ext fun z => by simp [hψ, hφ', map_pow]) (resPt V ≫ y)).mp h1
  rw [← hsq] at h2
  exact (hCE p (p ^ f) n Y T w hW Ω Ω' a φ φ'
    (RingHom.ext fun z => by simp [hφ, hφ', map_pow]) x).mpr h2
end

section

open CategoryTheory Limits AlgebraicGeometry
open UpperTheory.Gal.TranscendenceTraces (gp pt)
open UpperTheory.Gal.crystallineComparison (resPt)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem exists_common_algClosed_embedding {k A B : Type} [Field k] [Field A] [Field B] [Algebra k A]
    [Algebra k B] :
    ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (f : A →+* C) (g : B →+* C),
      f.comp (algebraMap k A) = g.comp (algebraMap k B) := by
  haveI : Nontrivial (TensorProduct k A B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k A B
      (algebraMap k B).injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct k A B)
  letI := Ideal.Quotient.field M
  let q : TensorProduct k A B →+* TensorProduct k A B ⧸ M := Ideal.Quotient.mk M
  let iA : A →ₐ[k] TensorProduct k A B := Algebra.TensorProduct.includeLeft
  let iB : B →ₐ[k] TensorProduct k A B := Algebra.TensorProduct.includeRight
  refine ⟨AlgebraicClosure (TensorProduct k A B ⧸ M), inferInstance, inferInstance,
    (algebraMap _ _).comp (q.comp iA.toRingHom), (algebraMap _ _).comp (q.comp iB.toRingHom), ?_⟩
  ext c
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgHom.commutes, iA, iB]

theorem UpperTheory.Gal.Mod.valLiftB :
    ValLift := by
  intro p Y Ω _ x η hsp hp
  let O := Y.presheaf.stalk (pt x)
  let sx : O ⟶ CommRingCat.of Ω := Scheme.stalkClosedPointTo x
  haveI : IsLocalHom sx.hom := Scheme.isLocalHom_stalkClosedPointTo' x
  have hx : Spec.map sx ≫ Y.fromSpecStalk (pt x) = x :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  let K := AlgebraicClosure (Y.residueField η)
  let f : O →+* K := (algebraMap (Y.residueField η) K).comp
    ((Y.residue η).hom.comp (Y.presheaf.stalkSpecializes hsp).hom)
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let g : O →+* A := f.codRestrict A.toSubring hA
  haveI : IsLocalHom g := hloc
  haveI : IsAlgClosed (FractionRing A) :=
    IsAlgClosed.of_ringEquiv K _ (FractionRing.algEquiv A K).symm.toRingEquiv
  let φ : IsLocalRing.ResidueField O →+* Ω := IsLocalRing.ResidueField.lift sx.hom
  let ψ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField A :=
    IsLocalRing.ResidueField.map g
  letI : Algebra (IsLocalRing.ResidueField O) Ω := φ.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField A) := ψ.toAlgebra
  obtain ⟨C, _, _, fa, fb, hab⟩ := exists_common_algClosed_embedding (k := IsLocalRing.ResidueField O) (A := Ω)
    (B := IsLocalRing.ResidueField A)
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom g) ≫ Y.fromSpecStalk (pt x), C, inferInstance, inferInstance,
    fa, fb, ?_, ?_⟩
  · intro h0
    have hu := ((Y.mem_basicOpen (p : Γ(Y, ⊤)) η trivial).mp hp).map (Y.residue η).hom
    simp only [map_natCast] at hu
    have h1 := congrArg A.subtype h0
    simp only [map_natCast, map_zero] at h1
    have h2 : (p : Y.residueField η) = 0 :=
      (algebraMap (Y.residueField η) K).injective (by rw [map_natCast, map_zero]; exact h1)
    exact hu.ne_zero h2
  · conv_lhs => rw [← hx]
    simp only [sp, resPt, ← Spec.map_comp_assoc]
    congr 2
    ext z
    have hz := congrArg (fun h => h (IsLocalRing.residue O z)) hab
    simpa [φ, ψ, RingHom.algebraMap_toAlgebra, IsLocalRing.ResidueField.map_residue] using hz
end

section

open Polynomial

namespace UpperTheory.Gal.Mod

theorem resClosed : ResClosed := by
  intro V _ _ _ _
  refine IsAlgClosed.of_exists_root _ ?_
  intro P hmon hirr
  have hl : P ∈ Polynomial.lifts (IsLocalRing.residue V) := by
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ IsLocalRing.residue_surjective P
  obtain ⟨Q, hQ, hdeg, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hmon
  have hpos : 0 < P.degree := Polynomial.degree_pos_of_irreducible hirr
  have hdeg' : (Q.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
    rw [hQm.degree_map, hdeg]
    exact hpos.ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Q.map (algebraMap V (FractionRing V))) hdeg'
  have hint : IsIntegral V x := ⟨Q, hQm, by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hx
    exact hx⟩
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (K := FractionRing V)).1 hint
  have hy : Q.eval y = 0 := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [map_zero, ← hx.eq_zero, Polynomial.eval_map, Polynomial.eval₂_hom]
  refine ⟨IsLocalRing.residue V y, ?_⟩
  rw [← hQ, Polynomial.eval_map, Polynomial.eval₂_hom, hy, map_zero]

end UpperTheory.Gal.Mod
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma finsum_fib {A P : Type*} [Finite A] (f : A → P) (S : Set P) (g : P → ℤ)
    (hg : ∀ z ∈ S, g z = (Nat.card {a // f a = z} : ℤ)) :
    ∑ᶠ z ∈ S, g z = (Nat.card {a // f a ∈ S} : ℤ) := by
  classical
  haveI := Fintype.ofFinite A
  have h1 : ∑ᶠ z ∈ S, g z = ∑ᶠ z ∈ S, (Nat.card {a // f a = z} : ℤ) :=
    finsum_mem_congr rfl hg
  set s : Finset A := Finset.univ.filter fun a => f a ∈ S with hs
  have h2 : ∑ᶠ z ∈ S, (Nat.card {a // f a = z} : ℤ) =
      ∑ z ∈ s.image f, (Nat.card {a // f a = z} : ℤ) := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext z
    simp only [Set.mem_inter_iff, Finset.coe_image, Set.mem_image, Finset.mem_coe, hs,
      Finset.mem_filter, Finset.mem_univ, true_and, Function.mem_support, ne_eq]
    constructor
    · rintro ⟨hz, h⟩
      refine ⟨?_, h⟩
      have : Nonempty {a // f a = z} := by
        by_contra hne
        rw [not_nonempty_iff] at hne
        exact h (by simp)
      obtain ⟨⟨a, rfl⟩⟩ := this
      exact ⟨a, hz, rfl⟩
    · rintro ⟨⟨a, ha, rfl⟩, h⟩
      exact ⟨ha, h⟩
  rw [h1, h2, Nat.card_eq_fintype_card, Fintype.card_subtype, ← hs,
    Finset.card_eq_sum_card_image f s, Nat.cast_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 2
  ext a
  simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro rfl
    obtain ⟨b, hb, hbz⟩ := Finset.mem_image.1 hz
    refine ⟨?_, rfl⟩
    rw [← hbz]
    exact (Finset.mem_filter.1 hb).2
  · exact fun h => h.2

private lemma co_eq (q : ℕ) {n : ℕ} (j : Fin (n + 1)) :
    co q j = (crystallineComparison.wEv q j : ℤ) - (crystallineComparison.wOd q j : ℤ) := by
  unfold co crystallineComparison.wEv crystallineComparison.wOd
  by_cases h : Even (j : ℕ)
  · simp [h, h.neg_one_pow]
  · have h' : Odd (j : ℕ) := Nat.not_even_iff_odd.1 h
    simp [h, h'.neg_one_pow]

theorem UpperTheory.Gal.Mod.cycRes :
    WtVal → CycRes := by
  intro hW p q n Y π T w hOne hPt V _ _ _ _ _ hp y hgen φ hφ y₀
  classical
  have hv := fun j => hW p Y (T j) (w j) (hOne j) V hp y
  haveI : ∀ j, Finite ((T j).Sec y) := fun j => (hv j).1
  letI : ∀ j, Fintype ((T j).Sec y) := fun j => Fintype.ofFinite _
  have hA := hPt V hp y hgen φ hφ (fun j => (T j).Sec y) (fun j => id)
    (fun j => Function.bijective_id)
  have hc := congrArg (Multiset.count y₀) hA
  simp only [crystallineComparison.pts, Multiset.count_sum', Multiset.count_nsmul, id] at hc
  have key : ∀ j : Fin (n + 1),
      ∑ᶠ z ∈ {z : gp (IsLocalRing.ResidueField V) ⟶ (T j).Z | z ≫ (T j).p = resPt V ≫ y ∧
        (twist φ Y)^[n - j] (z ≫ (T j).r) = y₀}, w j _ z =
      (Multiset.count y₀ (Finset.univ.val.map fun i : (T j).Sec y =>
        (twist φ Y)^[n - j] (resPt V ≫ i.1 ≫ (T j).r)) : ℤ) := by
    intro j
    rw [finsum_fib (fun i : (T j).Sec y => resPt V ≫ i.1)
      {z : gp (IsLocalRing.ResidueField V) ⟶ (T j).Z | z ≫ (T j).p = resPt V ≫ y ∧
        (twist φ Y)^[n - j] (z ≫ (T j).r) = y₀} (w j _)
      (fun z hz => (hv j).2 z hz.1)]
    congr 1
    rw [Multiset.count_map, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_def,
      Finset.filter_val]
    refine congrArg Multiset.card (Multiset.filter_congr fun i _ => ?_)
    have h1 : (resPt V ≫ i.1) ≫ (T j).p = resPt V ≫ y := by
      rw [Category.assoc, i.2]
    simp only [Set.mem_setOf_eq, h1, true_and, Category.assoc]
    exact eq_comm
  simp only [key, co_eq, sub_mul, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  exact_mod_cast hc
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.secGen :
    SecGen := by
  intro Z Y g _ V _ _ _ y
  have hP : IsProper g := inferInstance
  have hV : ValuativeCriterion g := by
    rw [IsProper.eq_valuativeCriterion] at hP
    exact hP.1.1.1
  let e : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of V) :=
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    show (e ≫ z) ≫ g = e ≫ y
    rw [Category.assoc, show z ≫ g = y from hz]
  · intro z₁ hz₁ z₂ hz₂ h
    have h₁ : z₁ ≫ g = y := hz₁
    have h₂ : z₂ ≫ g = y := hz₂
    have h' : e ≫ z₁ = e ≫ z₂ := h
    let S : ValuativeCommSq g :=
      ⟨V, FractionRing V, e ≫ z₁, y, ⟨by rw [Category.assoc, h₁]⟩⟩
    have hu := ValuativeCriterion.uniqueness hV S
    have := @Subsingleton.elim _ hu
      ⟨z₁, rfl, h₁⟩ ⟨z₂, h'.symm, h₂⟩
    exact congrArg CommSq.LiftStruct.l this
  · intro x hx
    have hx' : x ≫ g = e ≫ y := hx
    let S : ValuativeCommSq g := ⟨V, FractionRing V, x, y, ⟨hx'⟩⟩
    obtain ⟨⟨l⟩⟩ := ValuativeCriterion.existence hV S
    exact ⟨l.l, l.fac_right, l.fac_left⟩
end
