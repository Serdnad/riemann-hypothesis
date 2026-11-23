module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle918
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle923
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys.OfLift

theorem sec_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Smooth s] (U : X.affineOpens) :
    Algebra.Smooth R (Sec s U.1) := by
  have h := HasRingHomProperty.appLE @Smooth s ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h' : RingHom.Smooth ((s.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact RingHom.smooth_algebraMap.mp h'

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {X₀ X : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

theorem surjective_spMap (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (hπ : Function.Surjective π) :
    Surjective (spMap π) := by
  constructor
  intro x
  have hx : (show PrimeSpectrum R from x) ∈ Set.range (PrimeSpectrum.comap π) := by
    refine (range_comap_of_surjective R₀ π hπ).ge ?_
    rw [hk]
    intro a ha
    have h2 : a ^ 2 = 0 := by
      have := Ideal.pow_mem_pow ha 2
      rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact (show PrimeSpectrum R from x).2.mem_of_pow_mem 2 (by rw [h2]; exact zero_mem _)
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

variable (hpb : IsPullback i s₀ s (spMap π)) (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π))

def liftOpen (U : X₀.affineOpens) : X.affineOpens :=
  ⟨(GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose,
    (GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose_spec.1⟩

theorem preimage_liftOpen (U : X₀.affineOpens) : i ⁻¹ᵁ (liftOpen hpb hπ hn U).1 = U.1 :=
  (GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose_spec.2

theorem liftOpen_mono (hi : Function.Surjective i.base) {U V : X₀.affineOpens} (h : V ≤ U) :
    liftOpen hpb hπ hn V ≤ liftOpen hpb hπ hn U := by
  intro x hx
  obtain ⟨y, rfl⟩ := hi x
  have hy : y ∈ i ⁻¹ᵁ (liftOpen hpb hπ hn V).1 := hx
  rw [preimage_liftOpen] at hy
  have hy' : y ∈ i ⁻¹ᵁ (liftOpen hpb hπ hn U).1 := by
    rw [preimage_liftOpen]; exact h hy
  exact hy'

def pr (U : X₀.affineOpens) : GlobalTheory.CechDR.Pair i := ⟨(U, liftOpen hpb hπ hn U), (preimage_liftOpen hpb hπ hn U).ge⟩

end GlobalTheory.LiftSys.OfLift


open GlobalTheory.LiftSys.OfLift in
theorem GlobalTheory.LiftSys.exists_sys_presents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsPullback i s₀ s (spMap π) → Smooth s → ∃ S : Sys I π s₀, Nonempty (S.Presents s i) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ X s i hpb hsm
  have hn : IsNilpotent (RingHom.ker π) := ⟨2, hk ▸ hI⟩
  haveI := surjective_spMap hI hk hπ
  have hi : Function.Surjective i.base :=
    (MorphismProperty.of_isPullback (P := @Surjective) hpb.flip ‹_›).surj
  let G : AffOp X₀ ⥤ AffOp X :=
    (Monotone.functor (f := liftOpen hpb hπ hn) fun _ _ h ↦ liftOpen_mono hpb hπ hn hi h).op
  let S : Sys I π s₀ :=
    { F := G ⋙ OAff s
      p := fun U ↦ GlobalTheory.CechDR.secPull s s₀ (pr hpb hπ hn U.unop)
      semi := fun U ↦ GlobalTheory.CechDR.semiHom_secPull hpb.w _
      nat := fun {U V} a b ↦ (congrArg (fun t ↦ t.hom b) (i.map_appLE (pr hpb hπ hn V.unop).2
          (homOfLE (liftOpen_mono hpb hπ hn hi (leOfHom a.unop))).op)).trans
        (congrArg (fun t ↦ t.hom b) (i.appLE_map (pr hpb hπ hn U.unop).2 (homOfLE (show V.unop.1 ≤ U.unop.1 from leOfHom a.unop)).op)).symm
      surj := fun U ↦ (GlobalTheory.CechDR.secPull_surjective_and_ker R R₀ I π hπ hk X₀ X s₀ s i hpb (pr hpb hπ hn U.unop) (preimage_liftOpen hpb hπ hn U.unop)).1
      ker := fun U b ↦ (GlobalTheory.CechDR.secPull_surjective_and_ker R R₀ I π hπ hk X₀ X s₀ s i hpb (pr hpb hπ hn U.unop) (preimage_liftOpen hpb hπ hn U.unop)).2 b
      smooth := fun U ↦ sec_smooth s _ }
  exact ⟨S, ⟨⟨fun U ↦ affPt s (liftOpen hpb hπ hn U.unop), fun U ↦ (liftOpen hpb hπ hn U.unop).2.isOpenImmersion_fromSpec, fun U ↦ affPt_w s _,
    fun U V a ↦ affPt_res s _, fun U ↦ GlobalTheory.CechDR.secPull_affPt s s₀ (pr hpb hπ hn U.unop),
    S.cover_of_surjective ⟨hi⟩ _ fun U ↦ GlobalTheory.CechDR.secPull_affPt s s₀ (pr hpb hπ hn U.unop)⟩⟩⟩
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

namespace Sys

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {X₀ : Scheme.{0}} {π : R →+* R₀}
  {s₀ : X₀ ⟶ Sp R₀}

def viaDR (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (s₀ : X₀ ⟶ Sp R₀) :
    CoefMap (((RingHom.id R₀).comp (RingHom.id R₀)).comp π) (O (divided₂ hI) (s₀ ≫ spMap π)) (OAff s₀) :=
  ((redMor hI hk s₀).coef.comp (CoefMap.restrict (O (dp0 R₀) s₀) (IsTriv s₀).ι)).comp
    (ptCoef (F := OAff s₀) (fun U ↦ affPt s₀ U.unop) (fun U ↦ affPt_w s₀ U.unop)
      fun _ _ a ↦ affPt_res s₀ (leOfHom a.unop))

variable (S : Sys I π s₀) (hI : I ^ 2 = 0) (hk : RingHom.ker π = I)

def redTrans : ((S.coef hI).comp S.redO).G ⟶ (viaDR hI hk s₀).G where
  app U :=
    { φ := { (S.p U : S.F.obj U →+* Sec s₀ U.unop.1) with
        commutes' := fun r ↦ (S.semi U).map_algebraMap r }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := by
        refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_, fun n hn a ha ↦ ?_⟩
        · exact Ideal.mem_comap.2 (Ideal.mem_bot.2 ((S.ker U a).2 ha))
        · change (dp0 _).dpow n (S.p U a) = S.p U _
          rw [(S.ker U a).2 ha, dpow_eval_zero _ hn]
          exact ((S.ker U _).2 ((divided₂ (map_sq hI _)).dpow_mem hn ha)).symm
      pt := by
        change spMap (RingHom.id _) ≫ affPt s₀ U.unop = affPt s₀ U.unop ≫ 𝟙 X₀
        rw [Cris.spMap_id, Category.id_comp, Category.comp_id] }
  naturality U V a := Thick.hom_ext fun b ↦ S.nat a b

theorem redO_r (c : Cr hI π s₀) :
    S.redO.pull1 (S.r hI c) = cmpO s₀ (toH1O s₀ (rho hI hk s₀ c)) := by
  refine (CoefMap.pullCohomologyOne_comp _ _ c).symm.trans
    ((CoefMap.pullCohomologyOne_eq_of_natTrans _ (viaDR hI hk s₀) (S.redTrans hI hk) (fun _ _ ↦ rfl) c).trans ?_)
  rw [viaDR, CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_comp]
  rfl

end Sys

end GlobalTheory.LiftSys

namespace GlobalTheory.LiftSys

theorem Sys.mem_K_sup_iff : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀),
    ∀ S : Sys I π s₀, RhoBC hI hk s₀ → S.Full hI → ∀ c : Cr hI π s₀,
      c ∈ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) ↔ rho hI hk s₀ c ∈ F1 s₀ := by
  intro R R₀ _ _ I hI π _ hk X₀ s₀ S hBC hF c
  have key : ∀ c, rho hI hk s₀ c ∈ F1 s₀ ↔ S.redO.pull1 (S.r hI c) = 0 := fun c ↦ by
    rw [Sys.redO_r S hI hk c]
    change toH1O s₀ (rho hI hk s₀ c) = 0 ↔ _
    exact ⟨fun h ↦ by rw [h, map_zero],
      fun h ↦ GlobalTheory.CechDR.cmpO_injective R₀ X₀ s₀ (h.trans (map_zero _).symm)⟩
  rw [key]
  constructor
  · intro h
    obtain ⟨k, hk', i, hi, rfl⟩ := Submodule.mem_sup.1 h
    have h0 : S.r hI k = 0 := hk'
    rw [map_add (f := _), h0, zero_add]
    refine (key i).1 ?_
    rw [(hBC.2 i).2 hi]
    exact Submodule.zero_mem _
  · intro h
    obtain ⟨z, hz⟩ := H1.mk_surjective _ (S.r hI c)
    rw [← hz, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at h
    obtain ⟨g₀, hg₀⟩ := h
    choose g hg using fun U ↦ S.surj U (g₀ U)
    let z' : Z1 S.F := z - ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩
    have hz' : S.IsIdealValuedLiftSystemCocycle z' := by
      intro U V a
      rw [← S.ker]
      have e := congrFun (congrFun (congrFun hg₀ U) V) a
      rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
      change g₀ V - mp (OAff s₀) a (g₀ U) = S.p V (z.1 U V a) at e
      change S.p V (z.1 U V a - (g V - mp S.F a (g U))) = 0
      rw [map_sub, map_sub, S.nat, hg, hg, ← e, sub_self]
    obtain ⟨c', hc', hrc'⟩ := hF z' hz'
    have hr : S.r hI (c - c') = 0 := by
      rw [map_sub, hrc', ← hz, map_sub, sub_sub_cancel]
      exact H1.mk_eq_zero.2 ⟨g, rfl⟩
    exact Submodule.mem_sup.2 ⟨c - c', hr, c', hc', sub_add_cancel c c'⟩

end GlobalTheory.LiftSys
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LiftSys.Glue

open Opposite Limits

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_surjective {A B : Type} [CommRing A] [CommRing B] (q : A →+* B)
    (hq : Function.Surjective q) (hn : ∀ a, q a = 0 → a * a = 0) : Function.Surjective (spMap q) := by
  intro p
  have hker : RingHom.ker q ≤ p.asIdeal := by
    intro x hx
    have hx2 := hn x (RingHom.mem_ker.1 hx)
    exact (p.isPrime.mem_or_mem (by rw [hx2]; exact p.asIdeal.zero_mem)).elim id id
  haveI := p.isPrime
  haveI : (Ideal.map q p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  refine ⟨⟨Ideal.map q p.asIdeal, this⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap q (Ideal.map q p.asIdeal) = p.asIdeal
  rw [Ideal.comap_map_of_surjective _ hq, sup_eq_left]
  intro x hx
  exact hker (by simpa [RingHom.mem_ker] using hx)

theorem exists_affine {X₀ : Scheme.{0}} {x : X₀} {U : X₀.Opens} (hx : x ∈ U) :
    ∃ W : X₀.affineOpens, x ∈ W.1 ∧ W.1 ≤ U := by
  obtain ⟨W, hW, hxW, hWU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₀.isBasis_affineOpens) hx
  exact ⟨⟨W, hW⟩, hxW, hWU⟩

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

abbrev cov {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : S.Presents s i)
    (hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S.F.obj (op U))), h.y (op U) z = x) :
    X.OpenCover where
  I₀ := X₀.affineOpens
  X U := Sp (S.F.obj (op U))
  f U := h.y (op U)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x ↦ by obtain ⟨U, z, hz⟩ := hc x; exact ⟨U, z, hz⟩, fun U ↦ h.isOpen _⟩

def dir {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : S.Presents s i)
    (hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S.F.obj (op U))), h.y (op U) z = x)
    (hd : ∀ (U V : X₀.affineOpens) (a : Sp (S.F.obj (op U))) (b : Sp (S.F.obj (op V))),
      h.y (op U) a = h.y (op V) b → ∃ (W : X₀.affineOpens) (_ : W ≤ U) (_ : W ≤ V)
        (c : Sp (S.F.obj (op W))), h.y (op W) c = h.y (op U) a) :
    (cov h hc).LocallyDirected where
  trans {U V} a := spMap (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U))
  trans_id U := by
    haveI := h.isOpen (op U)
    rw [← cancel_mono (h.y (op U))]
    exact (h.nat _).trans (Category.id_comp _).symm
  trans_comp {U V W} a b := by
    haveI := h.isOpen (op W)
    rw [← cancel_mono (h.y (op W))]
    rw [Category.assoc, h.nat, h.nat, h.nat]
  w {U V} a := h.nat a.op
  directed {U V} x := by
    haveI := h.isOpen (op U)
    haveI := h.isOpen (op V)
    obtain ⟨W, hWU, hWV, c, hcW⟩ := hd U V (pullback.fst (h.y (op U)) (h.y (op V)) x)
      (pullback.snd (h.y (op U)) (h.y (op V)) x)
      (by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply])
    refine ⟨W, homOfLE hWU, homOfLE hWV, c, ?_⟩
    apply (pullback.fst (h.y (op U)) (h.y (op V)) ≫ h.y (op U)).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    change (spMap _ ≫ h.y (op U)) c = _
    rw [h.nat, hcW, Scheme.Hom.comp_apply]
  property_trans {U V} a := by
    haveI := h.isOpen (op V)
    haveI : IsOpenImmersion (spMap (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U)) ≫ h.y (op V)) := by
      rw [h.nat]; exact h.isOpen _
    exact IsOpenImmersion.of_comp _ (h.y (op V))

theorem presents_hom : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (Y : Scheme.{0}) (t : Y ⟶ Sp R) (j : X₀ ⟶ Y), IsPullback i s₀ s (spMap π) → S.Presents t j → S'.Presents s i → (∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b)) → ∃ f : X ⟶ Y, f ≫ t = s ∧ i ≫ f = j := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S S' X s i Y t j hpb hY hX hψ
  obtain ⟨ψ, hψp, hψn⟩ := hψ

  have hsurU : ∀ U, Function.Surjective (spMap (S'.p U)) := fun U ↦
    spMap_surjective _ (S'.surj U) fun b hb ↦ by
      have hb' := (S'.ker U b).1 hb
      have : b * b ∈ (I.map (algebraMap R (S'.F.obj U))) ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul hb' hb'
      rwa [map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hπs : Function.Surjective (spMap π) := spMap_surjective π hπ fun a ha ↦ by
    have ha' : a ∈ I := hk ▸ RingHom.mem_ker.2 ha
    have : a * a ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha' ha'
    rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this

  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom π) hπ
  haveI hic : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip inferInstance
  have hinj : Function.Injective i := i.isClosedEmbedding.injective
  have hisurj : Function.Surjective i :=
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hpb.flip ⟨hπs⟩).surj

  have hrng : ∀ (U : X₀.affineOpens) (z : Sp (S'.F.obj (op U))), ∃ x₀ ∈ U.1, hX.y (op U) z = i x₀ := by
    intro U z
    obtain ⟨w, rfl⟩ := hsurU (op U) z
    refine ⟨affPt s₀ U w, U.2.range_fromSpec.le ⟨w, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, hX.red (op U), Scheme.Hom.comp_apply]
  have hcov : ∀ (U : X₀.affineOpens) (x₀ : X₀), x₀ ∈ U.1 → ∃ z : Sp (S'.F.obj (op U)), hX.y (op U) z = i x₀ := by
    intro U x₀ hx
    obtain ⟨w, hw⟩ : x₀ ∈ Set.range (affPt s₀ U) := U.2.range_fromSpec.ge hx
    refine ⟨spMap (S'.p (op U)) w, ?_⟩
    change (spMap (S'.p (op U)) ≫ hX.y (op U)) w = i x₀
    rw [hX.red (op U), Scheme.Hom.comp_apply]
    exact congrArg i hw
  have hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S'.F.obj (op U))), hX.y (op U) z = x := by
    intro x
    obtain ⟨x₀, rfl⟩ := hisurj x
    obtain ⟨U, hxU, -⟩ := exists_affine (show x₀ ∈ (⊤ : X₀.Opens) from trivial)
    obtain ⟨z, hz⟩ := hcov U x₀ hxU
    exact ⟨U, z, hz⟩
  have hd : ∀ (U V : X₀.affineOpens) (a : Sp (S'.F.obj (op U))) (b : Sp (S'.F.obj (op V))),
      hX.y (op U) a = hX.y (op V) b → ∃ (W : X₀.affineOpens) (_ : W ≤ U) (_ : W ≤ V)
        (c : Sp (S'.F.obj (op W))), hX.y (op W) c = hX.y (op U) a := by
    intro U V a b hab
    obtain ⟨x₀, hxU, ha⟩ := hrng U a
    obtain ⟨x₁, hxV, hb⟩ := hrng V b
    have e : x₀ = x₁ := hinj (ha.symm.trans (hab.trans hb))
    subst e
    obtain ⟨W, hxW, hWle⟩ := exists_affine (show x₀ ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩)
    obtain ⟨c, hc'⟩ := hcov W x₀ hxW
    exact ⟨W, le_inf_iff.1 hWle |>.1, le_inf_iff.1 hWle |>.2, c, hc'.trans ha.symm⟩
  letI := dir hX hc hd
  let 𝒰 := cov hX hc
  let g : ∀ U : 𝒰.I₀, 𝒰.X U ⟶ Y := fun U ↦
    spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U)
  have hg : ∀ {U V : 𝒰.I₀} (a : U ⟶ V), 𝒰.trans a ≫ g V = g U := by
    intro U V a
    change spMap (mp S'.F a.op : S'.F.obj (op V) →+* S'.F.obj (op U)) ≫
      spMap (ψ (op V) : S.F.obj (op V) →+* S'.F.obj (op V)) ≫ hY.y (op V) = _
    rw [← Category.assoc, ← spMap_comp₂]
    have e : (mp S'.F a.op : S'.F.obj (op V) →+* S'.F.obj (op U)).comp
        (ψ (op V) : S.F.obj (op V) →+* S'.F.obj (op V)) =
        (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)).comp
          (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U)) :=
      RingHom.ext fun b ↦ hψn (op V) (op U) a.op b
    rw [e, spMap_comp₂, Category.assoc, hY.nat a.op]
  refine ⟨𝒰.glueMorphismsOfLocallyDirected g hg, 𝒰.hom_ext _ _ fun U ↦ ?_, ?_⟩
  · rw [𝒰.map_glueMorphismsOfLocallyDirected_assoc g hg U]
    change (spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U)) ≫ t = hX.y (op U) ≫ s
    rw [Category.assoc, hY.base, hX.base, ← spMap_comp₂]
    exact congrArg spMap (RingHom.ext fun r ↦ (ψ (op U)).commutes r)
  · let 𝒱 : X₀.OpenCover := Scheme.Cover.mkOfCovers X₀.affineOpens (fun U ↦ Sp (Sec s₀ U.1))
      (fun U ↦ affPt s₀ U)
      (fun x ↦ by
        obtain ⟨U, hxU, -⟩ := exists_affine (show x ∈ (⊤ : X₀.Opens) from trivial)
        obtain ⟨w, hw⟩ : x ∈ Set.range (affPt s₀ U) := U.2.range_fromSpec.ge hxU
        exact ⟨U, w, hw⟩)
      (fun U ↦ IsAffineOpen.isOpenImmersion_fromSpec U.2)
    refine 𝒱.hom_ext _ _ fun U ↦ ?_
    change affPt s₀ U ≫ i ≫ _ = affPt s₀ U ≫ j
    rw [← Category.assoc, show affPt s₀ U ≫ i = _ from (hX.red (op U)).symm,
      show affPt s₀ U ≫ j = _ from (hY.red (op U)).symm, Category.assoc]
    change spMap (S'.p (op U)) ≫ 𝒰.f U ≫ _ = _
    rw [𝒰.map_glueMorphismsOfLocallyDirected g hg U]
    change spMap (S'.p (op U)) ≫ spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U) = _
    rw [← Category.assoc, ← spMap_comp₂]
    exact congrArg (· ≫ hY.y (op U)) (congrArg spMap (RingHom.ext fun b ↦ hψp (op U) b))

end GlobalTheory.LiftSys.Glue
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.LatticeUp

theorem exists_mul_integral : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ), l.Prime →
    OneOver l y → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x ∈ lattice c y, IsIntegral ℤ ((M : E) * x) := by
  intro E _ _ l c y hl hy
  obtain ⟨M, hM, hMv⟩ := GlobalTheory.T.exists_denominator_prime_to_l_finiteAdele E l (y : Af E) hl fun w hw => by rw [hy w hw, map_one]
  refine ⟨M, hM, fun x hx => ?_⟩
  have hx' : algebraMap E (Af E) x * (↑y⁻¹ : Af E) ∈ hatO c := hx
  have key : algebraMap E (Af E) ((M : E) * x) =
      (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * (algebraMap E (Af E) (M : E) * (y : Af E)) := by
    have hyy : (↑y⁻¹ : Af E) * (y : Af E) = 1 := y.inv_mul
    rw [map_mul]
    calc algebraMap E (Af E) (M : E) * algebraMap E (Af E) x
        = algebraMap E (Af E) (M : E) * algebraMap E (Af E) x * ((↑y⁻¹ : Af E) * (y : Af E)) := by rw [hyy, mul_one]
      _ = _ := by ring
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((M : E) * x) fun v => by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((M : E) * x)]
    have h1 := GlobalTheory.CMVal.ObjModel.hatO_integral hx' v
    have h2 := hMv v
    have : (algebraMap E (Af E) ((M : E) * x)) v =
        (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) v * (algebraMap E (Af E) (M : E) * (y : Af E)) v := by
      rw [key]; rfl
    rw [show ((((M : E) * x : E)) : v.adicCompletion E) = (algebraMap E (Af E) ((M : E) * x)) v from rfl, this, map_mul]
    exact mul_le_one' h1 h2
  rw [← hb]
  exact (b.isIntegral_coe)

end GlobalTheory.HilbFam.LatticeUp
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

theorem _root_.GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D M : ℕ) (x : ℂ), 0 < D → IsIntegral ℤ ((D : ℂ) * x ^ 2) → Sz l lam (-(padicValNat l D : ℝ) / 2) ((D : ℂ) * x) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M * l ^ padicValNat l D : ℕ) : ℂ) := by
  first | exact @GlobalTheory.SizeSqIntegral.main | exact GlobalTheory.SizeSqIntegral.main | (intros; apply GlobalTheory.SizeSqIntegral.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

theorem _root_.GlobalTheory.T.exists_glued_lineBundleSection_cover : ∀ {X : Scheme.{0}} (M : LB X), M.IsLB → ∀ (V : X.Opens) {J : Type} (W : J → X.Opens) (j : J → M.ι) (F : ∀ i, Γ(X, W i)), ⨆ i, W i = V → (∀ i, W i ≤ M.U (j i)) → (∀ i i', rsT (F i) (W i ⊓ W i') = rsT (M.g (j i) (j i')).val (W i ⊓ W i') * rsT (F i') (W i ⊓ W i')) → ∃ t : ∀ c, Γ(X, M.U c ⊓ V), (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ V) = rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ V) * rsT (t c') (M.U c ⊓ M.U c' ⊓ V)) ∧ ∀ i, rsT (t (j i)) (W i) = F i := by
  first | exact @GlobalTheory.GlueOver.exists_glue | exact GlobalTheory.GlueOver.exists_glue | (intros; apply GlobalTheory.GlueOver.exists_glue <;> assumption)
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

theorem _root_.GlobalTheory.T.cuspidalLeviDatum_perm_blocks_match : ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b b' : Fin r → ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ (blockTri (κ := F) b) V) (σ' : Representation ℂ (blockTri (κ := F) b') V'), IsCuspDatum b σ → IsCuspDatum b' σ' → ∀ (w : Equiv.Perm (Fin r)) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : blockTri (κ := F) b) (p' : blockTri (κ := F) b'), (p' : GL (Fin r) F) * permGL F w = permGL F w * (p : GL (Fin r) F) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  first | exact @GlobalTheory.FinGL.BlockMatch.blocks_match | exact GlobalTheory.FinGL.BlockMatch.blocks_match | (intros; apply GlobalTheory.FinGL.BlockMatch.blocks_match <;> assumption)
end
