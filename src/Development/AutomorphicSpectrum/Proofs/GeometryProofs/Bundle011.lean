module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_stalk_closed {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (U : X.Opens) (hp : p.1 ∈ U)
    (hη : genPt ξ ∈ U) (r : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp r) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη r) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := U) hp p.2
  have h2 := congr(($h).hom r)
  have e : ∀ x, genMap ξ p x =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes p.2).hom x) := fun _ => rfl
  rw [e]
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom h2

theorem stalk_eq_germ_div_of_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (b : X.presheaf.stalk x.1) :
    ∃ r t : Γ(X, U), b * X.presheaf.germ U x.1 x.2 t = X.presheaf.germ U x.1 x.2 r ∧
      IsUnit (X.presheaf.germ U x.1 x.2 t) := by
  have hl := hU.isLocalization_stalk x
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj (hU.primeIdealOf x).asIdeal.primeCompl b
  exact ⟨r, t.1, hrt, IsLocalization.map_units (X.presheaf.stalk x.1)
    (M := (hU.primeIdealOf x).asIdeal.primeCompl) t⟩

theorem regAt_isLocalRing_isFractionRing_stalk :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ →
      ∀ p : Cpt ξ, IsLocalRing (regAt ξ p) ∧ IsFractionRing (regAt ξ p) Ω ∧
        Nonempty (X.presheaf.stalk p.1 ≃+* regAt ξ p) := by
  intro X Ω _ ξ hξ p
  have hsurj : Function.Surjective (genMap ξ p).rangeRestrict := (genMap ξ p).rangeRestrict_surjective
  have hinj : Function.Injective (genMap ξ p).rangeRestrict := fun a b h =>
    hξ.inj p (congrArg Subtype.val h)
  have e : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
    RingEquiv.ofBijective (genMap ξ p).rangeRestrict ⟨hinj, hsurj⟩
  have hloc : IsLocalRing (regAt ξ p) :=
    IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict hsurj
  refine ⟨hloc, ?_, ⟨e⟩⟩
  apply IsFractionRing.of_field
  intro a
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := p.1) trivial
  have hη : genPt ξ ∈ U := p.2.mem_open U.2 hpU
  obtain ⟨b, rfl⟩ : ∃ b : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom b = a :=
    hξ.bij.2 a
  obtain ⟨r, t, hrt, hunit⟩ := stalk_eq_germ_div_of_affine hU ⟨genPt ξ, hη⟩ b
  replace hrt : b * X.presheaf.germ U (genPt ξ) hη t = X.presheaf.germ U (genPt ξ) hη r := hrt
  replace hunit : IsUnit (X.presheaf.germ U (genPt ξ) hη t) := hunit
  have hne : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη t) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨⟨_, X.presheaf.germ U p.1 hpU r, rfl⟩, ⟨_, X.presheaf.germ U p.1 hpU t, rfl⟩, ?_⟩
  show _ = genMap ξ p (X.presheaf.germ U p.1 hpU r) / genMap ξ p (X.presheaf.germ U p.1 hpU t)
  rw [genMap_germ_eq_stalk_closed ξ p U hpU hη, genMap_germ_eq_stalk_closed ξ p U hpU hη, eq_div_iff hne]
  exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans
    (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)

end GlobalTheory.CompanionTheory.Ar
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.RegDenom

theorem exists_denom_of_injective {R K B S : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Finite S]
    (ρ : R →+* B) (v : S → B →+* K) (hv : Function.Injective v)
    (hρ : ∀ i r, v i (ρ r) = algebraMap R K r) (f : S → K) :
    ∃ d : R, d ≠ 0 ∧ ∃ b : B, ∀ i, v i b = algebraMap R K d * f i := by
  classical
  cases nonempty_fintype S
  have inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  let W : Submodule K (S → K) := Submodule.span K (Set.range fun b : B => fun i => v i b)
  have hW : W = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)
    have hm : Function.Injective (fun i : S => ((v i : B →+* K) : B →* K)) := by
      intro i j hij
      apply hv
      ext b
      exact DFunLike.congr_fun hij b
    have hli : LinearIndependent K (fun i : S => (fun b => v i b : B → K)) :=
      (linearIndependent_monoidHom B K).comp _ hm
    have hc : ∀ i, φ (Pi.single i 1) = 0 := by
      have h0 := Fintype.linearIndependent_iff.mp hli (fun i => φ (Pi.single i 1)) (by
        funext b
        have hb : φ (fun i => v i b) = 0 := hle (Submodule.subset_span ⟨b, rfl⟩)
        have hx : (fun i => v i b) = ∑ i, (v i b) • (Pi.single i (1 : K) : S → K) := by
          funext j
          simp [Finset.sum_apply, Pi.single_apply]

        rw [hx, map_sum] at hb
        simp only [map_smul, smul_eq_mul] at hb
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hb]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
      exact h0
    apply hφ
    ext i
    simpa using hc i

  have key : ∀ x ∈ W, ∃ d : R, d ≠ 0 ∧ ∃ b : B, ∀ i, v i b = algebraMap R K d * x i := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨b, rfl⟩ := h
      exact ⟨1, one_ne_zero, b, fun i => by simp⟩
    | zero => exact ⟨1, one_ne_zero, 0, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, b, hb⟩ := hx
      obtain ⟨e, he, c, hc⟩ := hy
      refine ⟨d * e, mul_ne_zero hd he, ρ e * b + ρ d * c, fun i => ?_⟩
      simp only [map_add (f := _), map_mul, hρ, hb, hc, Pi.add_apply]
      ring
    | smul k x _ hx =>
      obtain ⟨d, hd, b, hb⟩ := hx
      obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) k
      have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
      have hcK : algebraMap R K c ≠ 0 := fun h => hc0 (inj (by simpa using h))
      refine ⟨c * d, mul_ne_zero hc0 hd, ρ a * b, fun i => ?_⟩
      simp only [map_mul, hρ, hb, Pi.smul_apply, smul_eq_mul]
      field_simp
  exact key f (hW ▸ Submodule.mem_top)

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

def valHom {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valHom_apply {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : valHom x U h s = valAt x U h s := rfl

theorem eq_of_valHom_eq {B : Type} [CommRing B] {X : Scheme.{0}} {x y : Spec (CommRingCat.of B) ⟶ X} {U : X.Opens}
    (hU : IsAffineOpen U) (hx : ⊤ ≤ x ⁻¹ᵁ U) (hy : ⊤ ≤ y ⁻¹ᵁ U) (e : valHom x U hx = valHom y U hy) : x = y := by
  have ha : x.appLE U ⊤ hx = y.appLE U ⊤ hy := by
    ext s
    have := DFunLike.congr_fun e s
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom).1 this
  have htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of B)).Opens) := isAffineOpen_top _
  have h1 := hU.SpecMap_appLE_fromSpec x htop hx
  have h2 := hU.SpecMap_appLE_fromSpec y htop hy
  rw [ha, h2] at h1
  have : IsIso htop.fromSpec := by
    rw [show htop = isAffineOpen_top _ from rfl, IsAffineOpen.fromSpec_top]
    infer_instance
  exact (cancel_epi htop.fromSpec).mp h1.symm

theorem le_preimage_top {X Y : Scheme.{0}} (p : X ⟶ Y) (U : X.Opens) : U ≤ p ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

def structHom {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (le_preimage_top p U)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem valHom_structHom {B : Type} [CommRing B] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R))
    (i : R →+* B) (x : Spec (CommRingCat.of B) ⟶ X) (hx : x ≫ p = Spec.map (CommRingCat.ofHom i))
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (r : R) : valHom x U h (structHom p U r) = i r := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U (le_preimage_top p U) ≫ x.appLE U ⊤ h ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom = CommRingCat.ofHom i := by
    have e1 : p.appLE ⊤ U (le_preimage_top p U) ≫ x.appLE U ⊤ h = (x ≫ p).appTop := by
      rw [Scheme.Hom.appLE_comp_appLE]
      simp only [Scheme.Hom.appLE, Scheme.Hom.comp_appTop, Scheme.Hom.appTop]
      refine Eq.trans (congrArg _ ?_) (Category.comp_id _)
      exact (Spec (CommRingCat.of B)).presheaf.map_id _
    rw [reassoc_of% e1, hx, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congr($(e).hom r)

theorem exists_denom_regularAt : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left),
    ∃ d : R, d ≠ 0 ∧ Γ.RegularAt (fun t => algebraMap R _ d * f t) g := by
  intro R _ _ T _ _ Γ f g
  obtain ⟨U, hU, hg, -⟩ := exists_isAffineOpen_mem_and_subset (x := g) (U := ⊤) trivial
  let S := {t : T // ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U}
  let v : S → Γ(Γ.G.left, U) →+* FractionRing R := fun t => valHom (Γ.pt t.1).left U t.2
  have hv : Function.Injective v := by
    intro s t e
    have hst := eq_of_valHom_eq hU s.2 t.2 e
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := inferInstance
    exact Subtype.ext (Γ.pt_inj s.1 t.1 x x (by rw [hst]))
  have hρ : ∀ t r, v t (structHom Γ.G.hom U r) = algebraMap R _ r := fun t r =>
    valHom_structHom Γ.G.hom _ _ (Over.w (Γ.pt t.1)) U t.2 r
  obtain ⟨d, hd, b, hb⟩ := exists_denom_of_injective (structHom Γ.G.hom U) v hv hρ (fun t => f t.1)
  exact ⟨d, hd, U, hg, b, fun t h => hb ⟨t, h⟩⟩

end GlobalTheory.CompanionTheory.Ar.BT.RegDenom
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegSec

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

noncomputable def val (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (U : X.Opens) (h : genPt ξ ∈ U) {q : X} (hq : genPt ξ ⤳ q) (hqU : q ∈ U)
    (s : Γ(X, U)) :
    genMap ξ ⟨q, hq⟩ ((X.presheaf.germ U q hqU).hom s) = val ξ U h s := by
  have key : ∀ {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g).hom x = g.hom (f.hom x) :=
    fun _ _ _ => rfl
  unfold genMap val
  rw [← X.presheaf.germ_stalkSpecializes hqU hq]
  exact (key (X.presheaf.stalkSpecializes hq) (Scheme.stalkClosedPointTo ξ) _).trans
    ((congrArg (fun y => (Scheme.stalkClosedPointTo ξ).hom y)
      (key (X.presheaf.germ U q hqU) (X.presheaf.stalkSpecializes hq) s).symm).trans
      (key (X.presheaf.germ U q hqU ≫ X.presheaf.stalkSpecializes hq)
        (Scheme.stalkClosedPointTo ξ) s).symm)

theorem val_res {V U : X.Opens} (i : V ⟶ U) (hV : genPt ξ ∈ V) (hU : genPt ξ ∈ U) (s : Γ(X, U)) :
    val ξ V hV ((X.presheaf.map i.op).hom s) = val ξ U hU s := by
  have key : ∀ {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g).hom x = g.hom (f.hom x) :=
    fun _ _ _ => rfl
  unfold val
  rw [← X.presheaf.germ_res i (genPt ξ) hV]
  exact (key (X.presheaf.germ V (genPt ξ) hV) (Scheme.stalkClosedPointTo ξ) _).trans
    ((congrArg (fun y => (Scheme.stalkClosedPointTo ξ).hom y)
      (key (X.presheaf.map i.op) (X.presheaf.germ V (genPt ξ) hV) s).symm).trans
      (key (X.presheaf.map i.op ≫ X.presheaf.germ V (genPt ξ) hV)
        (Scheme.stalkClosedPointTo ξ) s).symm)

theorem val_injective (hξ : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U)
    (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) : Function.Injective (val ξ U h) := by
  intro s t hst
  refine TopCat.Presheaf.section_ext X.sheaf U s t (fun q hq => ?_)
  have hq' := hU q hq
  apply hξ.inj ⟨q, hq'⟩
  exact (genMap_germ ξ U h hq' hq s).trans (hst.trans (genMap_germ ξ U h hq' hq t).symm)

theorem mem_range_val_iff (hξ : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U)
    (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) (a : Ω) :
    a ∈ (val ξ U h).range ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  constructor
  · intro ha q hqU
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    exact RingHom.mem_range.mpr ⟨(X.presheaf.germ U q.1 hqU).hom s, genMap_germ ξ U h q.2 hqU s⟩
  · intro H
    have loc : ∀ q : U, ∃ (W : X.Opens) (t : Γ(X, W)) (_ : (q : X) ∈ W) (hg : genPt ξ ∈ W),
        val ξ W hg t = a := by
      rintro ⟨q, hq⟩
      have hq' : genPt ξ ⤳ q := hU q hq
      obtain ⟨x, hx⟩ := RingHom.mem_range.mp (H ⟨q, hq'⟩ hq)
      obtain ⟨W, hqW, t, ht⟩ := TopCat.Presheaf.germ_exist X.presheaf x
      have hg : genPt ξ ∈ W := hq'.mem_open W.isOpen hqW
      refine ⟨W, t, hqW, hg, ?_⟩
      rw [← genMap_germ ξ W hg hq' hqW t]
      exact (congrArg (genMap ξ ⟨q, hq'⟩) ht).trans hx
    choose W t hqW hg hval using loc
    let V : U → X.Opens := fun q => W q ⊓ U
    have hgV : ∀ q, genPt ξ ∈ V q := fun q => ⟨hg q, h⟩
    let sf : ∀ q : U, Γ(X, V q) := fun q =>
      (X.presheaf.map (homOfLE inf_le_left : V q ⟶ W q).op).hom (t q)
    have hsf : ∀ q, val ξ (V q) (hgV q) (sf q) = a := fun q =>
      (val_res ξ (homOfLE inf_le_left : V q ⟶ W q) (hgV q) (hg q) (t q)).trans (hval q)
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V sf := by
      intro i j
      apply val_injective ξ hξ (V i ⊓ V j) ⟨hgV i, hgV j⟩ (fun q hq => hU q hq.1.2)
      exact ((val_res ξ (TopologicalSpace.Opens.infLELeft (V i) (V j)) ⟨hgV i, hgV j⟩
        (hgV i) (sf i)).trans (hsf i)).trans
        ((val_res ξ (TopologicalSpace.Opens.infLERight (V i) (V j)) ⟨hgV i, hgV j⟩
        (hgV j) (sf j)).trans (hsf j)).symm
    have hcover : U ≤ iSup V := by
      intro q hq
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hq⟩, hqW ⟨q, hq⟩, hq⟩
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := X.sheaf) (U := V) U
      (fun q => homOfLE inf_le_right) hcover sf hcompat
    refine RingHom.mem_range.mpr ⟨s, ?_⟩
    have i0 : U := ⟨genPt ξ, h⟩
    exact (val_res ξ (homOfLE inf_le_right : V i0 ⟶ U) (hgV i0) h s).symm.trans
      ((congrArg (val ξ (V i0) (hgV i0)) (hs i0)).trans (hsf i0))

end GlobalTheory.CompanionTheory.Ar.RegSec

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_sections : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X),
    IsCptGen ξ → ∀ (U : X.Opens) (h : genPt ξ ∈ U), (∀ q : X, q ∈ U → genPt ξ ⤳ q) →
      Function.Injective (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom ∧
      ∀ a : Ω, a ∈ (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom.range ↔
        ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  intro X Ω _ ξ hξ U h hU
  exact ⟨RegSec.val_injective ξ hξ U h hU, RegSec.mem_range_val_iff ξ hξ U h hU⟩

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegAtMono

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_stalkSpecializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ) (h : q.1 ⤳ p.1)
    (x : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes h).hom x) = genMap ξ p x := by
  have e := X.presheaf.stalkSpecializes_comp q.2 h
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (congrArg (fun φ => φ.hom x) e)

theorem genMap_germ_eq (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ) (h : q.1 ⤳ p.1)
    (U : X.Opens) (hp : p.1 ∈ U) (hq : q.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom t) = genMap ξ p ((X.presheaf.germ U p.1 hp).hom t) := by
  rw [← genMap_stalkSpecializes ξ p q h, ← CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes]

theorem unitAt_of_isUnit (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) {x : X.presheaf.stalk q.1}
    (hx : IsUnit x) : unitAt ξ q (genMap ξ q x) := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨(u.isUnit.map (genMap ξ q)).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ), ?_⟩⟩
  exact map_units_inv (genMap ξ q) u

theorem regAt_mono :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ), q.1 ⤳ p.1 →
      regAt ξ p ≤ regAt ξ q ∧
        (IsCptGen ξ → ∀ a ∈ regAt ξ q, ∃ s ∈ regAt ξ p, unitAt ξ q s ∧ s * a ∈ regAt ξ p) := by
  intro X Ω _ ξ p q h
  refine ⟨?_, fun _ => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, genMap_stalkSpecializes ξ p q h x⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hp, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p.1) isOpen_univ
    have hU : IsAffineOpen U := hU
    have hq : q.1 ∈ U := h.mem_open U.2 hp
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨q.1, hq⟩ : U)
    have hloc := hU.isLocalization_stalk ⟨q.1, hq⟩
    obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) x
    have hu : IsUnit ((X.presheaf.germ U q.1 hq).hom t.1) :=
      IsLocalization.map_units (X.presheaf.stalk q.1) t
    have e' : x * (X.presheaf.germ U q.1 hq).hom t.1 = (X.presheaf.germ U q.1 hq).hom r := e
    refine ⟨genMap ξ q ((X.presheaf.germ U q.1 hq).hom t.1), ?_, unitAt_of_isUnit ξ q hu, ?_⟩
    · exact ⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩
    · rw [mul_comm, ← map_mul, e']
      exact ⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩

end GlobalTheory.CompanionTheory.Ar.RegAtMono
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_closedPointTo {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (V : X.Opens) (hy : p.1 ∈ V) (hx : genPt ξ ∈ V) (b : Γ(X, V)) :
    genMap ξ p (X.presheaf.germ V p.1 hy b) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hx b) := by
  have h : X.presheaf.germ V (genPt ξ) hx = X.presheaf.germ V p.1 hy ≫ X.presheaf.stalkSpecializes p.2 :=
    (X.presheaf.germ_stalkSpecializes hy p.2).symm
  rw [h]
  rfl

theorem exists_frac_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    ∃ b c : X.presheaf.stalk p.1, genMap ξ p c ≠ 0 ∧ a * genMap ξ p c = genMap ξ p b := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (genPt ξ)) := (X.presheaf.germ U (genPt ξ) hgU).hom.toAlgebra
  have _ : IsLocalization.AtPrime (X.presheaf.stalk (genPt ξ)) (hU.primeIdealOf ⟨genPt ξ, hgU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨genPt ξ, hgU⟩
  obtain ⟨s, rfl⟩ : ∃ s : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom s = a := hξ.bij.2 a
  obtain ⟨⟨r, d⟩, rfl⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf ⟨genPt ξ, hgU⟩).asIdeal.primeCompl s
  refine ⟨X.presheaf.germ U p.1 hpU r, X.presheaf.germ U p.1 hpU d, ?_, ?_⟩
  · rw [genMap_germ_eq_closedPointTo ξ p U hpU hgU]
    have hu := IsLocalization.map_units (X.presheaf.stalk (genPt ξ)) d
    exact (hu.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  · rw [genMap_germ_eq_closedPointTo ξ p U hpU hgU, genMap_germ_eq_closedPointTo ξ p U hpU hgU]
    have h := congrArg (Scheme.stalkClosedPointTo ξ).hom (IsLocalization.mk'_spec (X.presheaf.stalk (genPt ξ)) r d)
    exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans h

end GlobalTheory.CompanionTheory.Ar
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.Funct

theorem valAt_pullback {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (a : X ⟶ Y)
    (y : Spec (CommRingCat.of B) ⟶ Y) (hy : x ≫ a = y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (h' : ⊤ ≤ x ⁻¹ᵁ (a ⁻¹ᵁ U)) (s : Γ(Y, U)) :
    valAt x (a ⁻¹ᵁ U) h' ((a.app U).hom s) = valAt y U h s := by
  subst hy
  simp only [valAt]
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem regularAt_pullback {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ₁ : QFGroup R T)
    {T' : Type} [CommGroup T'] (Γ₂ : QFGroup R T') (a : Γ₁.G ⟶ Γ₂.G) (α : T →* T')
    (ha : ∀ t, Γ₁.pt t ≫ a = Γ₂.pt (α t)) (φ : T' → FractionRing R) (g : Γ₁.G.left)
    (hg : Γ₂.RegularAt φ (a.left g)) : Γ₁.RegularAt (fun t => φ (α t)) g := by
  obtain ⟨U, hU, s, hs⟩ := hg
  refine ⟨a.left ⁻¹ᵁ U, hU, (a.left.app U).hom s, fun t h => ?_⟩
  have hy : (Γ₁.pt t).left ≫ a.left = (Γ₂.pt (α t)).left := by
    rw [← ha t, Over.comp_left]
  have h₂ : ⊤ ≤ (Γ₂.pt (α t)).left ⁻¹ᵁ U := by
    rw [← hy]
    exact h
  rw [valAt_pullback _ _ _ hy U h₂ h s]
  exact hs (α t) h₂

theorem comp_mem_btOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (T' : Type) [CommGroup T'] [Finite T'] (Γ' : QFGroup R T') (a : Γ.G ⟶ Γ'.G) (α : T →* T'), (∀ t, Γ.pt t ≫ a = Γ'.pt (α t)) → ∀ f ∈ Γ'.btOrder ⊤, (fun t => f (α t)) ∈ Γ.btOrder ⊤ := by
  intro R _ _ T _ _ Γ T' _ _ Γ' a α ha f hf
  let Φ : (T' → R) →ₐ[R] (T → R) :=
    { toFun := fun f t => f (α t)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hle : Γ'.btOrder ⊤ ≤ (Γ.btOrder ⊤).comap Φ := by
    refine Algebra.adjoin_le fun f hf => ?_
    refine Algebra.subset_adjoin fun t g _ => ?_
    have h := regularAt_pullback Γ Γ' a α ha _ g (hf (α t) (a.left g) trivial)
    change Γ.RegularAt (fun x => algebraMap R (FractionRing R) (f (α (t * x)))) g
    simpa only [map_mul] using h
  exact hle hf

end GlobalTheory.CompanionTheory.Ar.BT.Funct
end
