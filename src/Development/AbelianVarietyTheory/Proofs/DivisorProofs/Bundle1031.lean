module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle309
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyTrivialOfIsoPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisLiftPdThickening
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem frobLift_stalk (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (U : Y.Opens) (hU : IsAffineOpen U)
    (F₀ : Γ(Y, U) →+* Γ(Y, U)) (hp2 : (p : Γ(Y, U)) ^ 2 = 0) (hF₀ : ∀ z, ∃ w, F₀ z = z ^ p + p * w)
    (y : Y) (hy : y ∈ U) :
    ∃ F : Y.presheaf.stalk y →+* Y.presheaf.stalk y,
      (∀ b, F ((Y.presheaf.germ U y hy).hom b) = (Y.presheaf.germ U y hy).hom (F₀ b)) ∧
        ∀ z, ∃ w, F z = z ^ p + p * w := by
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  exact frobLift_localization p (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl F₀ hp2 hF₀

theorem stalk_ringHom_ext {Y : Scheme.{0}} (U : Y.Opens) (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U)
    {C : Type} [CommRing C] (f f' : Y.presheaf.stalk y →+* C)
    (h : ∀ b, f ((Y.presheaf.germ U y hy).hom b) = f' ((Y.presheaf.germ U y hy).hom b)) : f = f' := by
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  exact IsLocalization.ringHom_ext (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (RingHom.ext h)

theorem exists_frobLift_stalk_of_etCoord :
    ∀ (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (g : Y ⟶ Sp (ZMod (p ^ 2))) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ (η : Y) (hη : η ∈ U), ∃ F : Y.presheaf.stalk η →+* Y.presheaf.stalk η, (∀ z, ∃ w, F z = z ^ p + p * w) ∧ (∀ l, F ((Y.presheaf.germ U η hη).hom (t l)) = (Y.presheaf.germ U η hη).hom (t l) ^ p) ∧ ∀ (y : Y), y ∈ U → ∀ (h : η ⤳ y), ∀ z ∈ stalkIm h, ∃ w ∈ stalkIm h, F z = z ^ p + p * w := by
  intro p _ Y g U n t hU ht η hη
  obtain ⟨F₀, hF₀, hFt⟩ := frob_lift_etale_chart p _ ht
  have hp2 : (p : Γ(Y, U)) ^ 2 = 0 := by
    have h := map_natCast (cstOn g U) (p ^ 2)
    rw [ZMod.natCast_self, map_zero] at h
    rw [← Nat.cast_pow, ← h]
  obtain ⟨F, hFg, hF⟩ := frobLift_stalk p U hU F₀ hp2 hF₀ η hη
  refine ⟨F, hF, fun l => ?_, fun y hy h z hz => ?_⟩
  · have := hFt l
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    rw [hFg, this, map_pow]
  · obtain ⟨F', hFg', hF'⟩ := frobLift_stalk p U hU F₀ hp2 hF₀ y hy
    have hs : ∀ b, (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.germ U y hy).hom b) =
        (Y.presheaf.germ U η hη).hom b := fun b =>
      congrArg (fun k => k.hom b) (Y.presheaf.germ_stalkSpecializes hy h)
    have hc : F.comp (Y.presheaf.stalkSpecializes h).hom =
        (Y.presheaf.stalkSpecializes h).hom.comp F' := by
      apply stalk_ringHom_ext U hU y hy
      intro b
      rw [RingHom.comp_apply, RingHom.comp_apply, hs, hFg, hFg', hs]
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨w, hw⟩ := hF' a
    refine ⟨_, ⟨w, rfl⟩, ?_⟩
    have := congrArg (· a) hc
    simp only [RingHom.comp_apply] at this
    rw [this, hw, map_add (f := _), map_mul, map_pow, map_natCast]

end GlobalTheory.DI
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.FinAffAmple

variable {X : Scheme.{0}} {M : LB X}

theorem mem_secAdd_iff_right {s t : M.Sec} {x : X} (ht : x ∉ nonzeroLocus t) :
    x ∈ nonzeroLocus (DVR.SecOps.secAdd s t) ↔ x ∈ nonzeroLocus s := by
  by_cases hc : ∃ k, x ∈ M.U k
  · obtain ⟨k, hk⟩ := hc
    rw [GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk, GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk] at *
    change x ∈ X.basicOpen (s.f k + t.f k) ↔ _
    rw [Scheme.mem_basicOpen _ _ _ hk, Scheme.mem_basicOpen _ _ _ hk] at *
    rw [map_add (f := _)]
    have hm : (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (t.f k) ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).2 ht
    have := Ideal.add_mem_iff_left (IsLocalRing.maximalIdeal _)
      (a := (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (s.f k)) hm
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff] at this
    exact not_iff_not.1 this
  · push_neg at hc
    exact ⟨fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc),
      fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc)⟩

theorem mem_secAdd_iff_left {s t : M.Sec} {x : X} (hs : x ∉ nonzeroLocus s) :
    x ∈ nonzeroLocus (DVR.SecOps.secAdd s t) ↔ x ∈ nonzeroLocus t := by
  have e : DVR.SecOps.secAdd s t = DVR.SecOps.secAdd t s := DVR.SecOps.sec_ext fun i => add_comm (s.f i) (t.f i)
  rw [e]
  exact mem_secAdd_iff_right hs

theorem exists_sec_forall_mem (T : Finset X) (t : X → M.Sec) (ht : ∀ x ∈ T, x ∈ nonzeroLocus (t x))
    (ht' : ∀ x ∈ T, ∀ y ∈ T, y ≠ x → y ∉ nonzeroLocus (t x)) :
    ∃ g : M.Sec, ∀ x ∈ T, x ∈ nonzeroLocus g := by
  classical
  suffices H : ∀ T' : Finset X, T' ⊆ T → ∃ g : M.Sec, ∀ x ∈ T, (x ∈ nonzeroLocus g ↔ x ∈ T') by
    obtain ⟨g, hg⟩ := H T subset_rfl
    exact ⟨g, fun x hx => (hg x hx).2 hx⟩
  intro T'
  induction T' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨DVR.SecOps.secZero, fun x _ => ?_⟩
    rw [GlobalTheory.nonzeroLocus_secZero]
    simp
  | insert a T' ha ih =>
    intro hsub
    obtain ⟨g, hg⟩ := ih ((Finset.subset_insert a T').trans hsub)
    have haT : a ∈ T := hsub (Finset.mem_insert_self a T')
    refine ⟨DVR.SecOps.secAdd g (t a), fun x hx => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      rw [mem_secAdd_iff_left (fun h => ha ((hg x hx).1 h))]
      simpa using ht x haT
    · rw [mem_secAdd_iff_right (ht' a haT x hx hxa), hg x hx, Finset.mem_insert]
      simp [hxa]

theorem exists_specializes_minimal {Z : Type*} [TopologicalSpace Z] [T0Space Z] (F : Finset Z) {x : Z}
    (hx : x ∈ F) : ∃ y ∈ F, x ⤳ y ∧ ∀ z ∈ F, y ⤳ z → z = y := by
  classical
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image (F.filter (x ⤳ ·)) (fun y => (F.filter (y ⤳ ·)).card)
    ⟨x, Finset.mem_filter.2 ⟨hx, specializes_refl x⟩⟩
  obtain ⟨hyF, hxy⟩ := Finset.mem_filter.1 hy
  refine ⟨y, hyF, hxy, fun z hz hyz => ?_⟩
  have hsub : F.filter (z ⤳ ·) ⊆ F.filter (y ⤳ ·) := fun w hw => by
    obtain ⟨hwF, hzw⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hwF, hyz.trans hzw⟩
  have hle := hmin z (Finset.mem_filter.2 ⟨hz, hxy.trans hyz⟩)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hzy : z ⤳ y := (Finset.mem_filter.1 (heq ▸ Finset.mem_filter.2 ⟨hyF, specializes_refl y⟩ :
    y ∈ F.filter (z ⤳ ·))).2
  exact (hyz.antisymm hzy).eq.symm

theorem finAff_of_isAmpleLB {Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y] [UniversallyClosed f] {L : LB X}
    (h : IsAmpleLB L) : FinAff X := by
  classical
  intro F
  let F' := F.filter (fun x => ∀ z ∈ F, x ⤳ z → z = x)
  let V : X → X.Opens := fun x =>
    ⟨(⋃ y ∈ F'.erase x, closure ({y} : Set X))ᶜ, (isClosed_biUnion_finset fun _ _ => isClosed_closure).isOpen_compl⟩
  have hV : ∀ x ∈ F', x ∈ V x := by
    intro x hx hmem
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hmem
    obtain ⟨hyx, hyF'⟩ := Finset.mem_erase.1 hy
    have hyx' : y ⤳ x := specializes_iff_mem_closure.2 hxy
    exact hyx ((Finset.mem_filter.1 hyF').2 x (Finset.mem_filter.1 hx).1 hyx').symm
  have hV' : ∀ x ∈ F', ∀ y ∈ F', y ≠ x → y ∉ V x := fun x _ y hy hyx hmem =>
    hmem (Set.mem_iUnion₂.2 ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, subset_closure rfl⟩)
  choose n hn s hs hsV _ using fun x : F' => h.exists_affine_le (hV x.1 x.2)
  obtain ⟨N, hN, t, ht⟩ := exists_common_pow n hn s
  let tt : X → (lbPow L N).Sec := fun x => if hx : x ∈ F' then t ⟨x, hx⟩ else DVR.SecOps.secZero
  have htt : ∀ x (hx : x ∈ F'), nonzeroLocus (tt x) = nonzeroLocus (s ⟨x, hx⟩) := fun x hx => by
    simp only [tt, dif_pos hx, ht]
  obtain ⟨g, hg⟩ := exists_sec_forall_mem F' tt (fun x hx => (htt x hx).symm ▸ hs ⟨x, hx⟩)
    (fun x hx y hy hyx hmem => hV' x hx y hy hyx (hsV ⟨x, hx⟩ ((htt x hx) ▸ hmem)))
  refine ⟨nonzeroLocus g, h.isAffineOpen_nonzeroLocus f hN g, fun x hx => ?_⟩
  obtain ⟨y, hyF, hxy, hmin⟩ := exists_specializes_minimal F hx
  exact hxy.mem_open (nonzeroLocus g).isOpen (hg y (Finset.mem_filter.2 ⟨hyF, hmin⟩))

theorem finAff_of_relAmple : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B →
    ∀ L : LB B.left, L.IsLB → Out.RelAmple B L → FinAff B.left := by
  intro R _ B _ hB L hL hA
  have := hB.proper
  exact finAff_of_isAmpleLB B.hom (isAmpleLB_of_relAmple_of_isAffine B hL hA)

end GlobalTheory.DualCon.FinAffAmple
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.SameLocal

theorem injective_app_of_section {X Y : Scheme.{0}} (p : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y)
    (V : Y.Opens) : Function.Injective (p.app V).hom := by
  have hi : IsIso ((e ≫ p).app V) := by
    rw [Scheme.Hom.congr_app he V]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (Functor.map_isIso _ _)
  have k : ∀ z, ((e ≫ p).app V).hom z = (e.app (p ⁻¹ᵁ V)).hom ((p.app V).hom z) := fun z => rfl
  intro x x' hx
  apply (ConcreteCategory.bijective_of_isIso ((e ≫ p).app V)).1
  change ((e ≫ p).app V).hom x = ((e ≫ p).app V).hom x'
  rw [k, k, hx]

theorem same_of_local : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ Same A M N (Over.homMk W.ι rfl ≫ u : Over.mk (W.ι ≫ Y.hom) ⟶ U) (Over.homMk W.ι rfl ≫ t)) → Same A M N u t := by
  intro R _ _ A _ hA U T M N hM hN hMr hNr Y u t hloc
  let p := (snd A Y).left
  let e := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  have he : e ≫ p = 𝟙 Y.left := by
    simp only [p, e, ← Over.comp_left, lift_snd, Over.id_left]
  have hp : ∀ V : Y.left.Opens, Function.Bijective (p.app V).hom := fun V =>
    ⟨injective_app_of_section p e he V,
      GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns _ (Out.TLinPf.isAb_pullback Y.hom A hA) V⟩
  rw [same_iff hM hN, ← sub_eq_zero]
  obtain ⟨L, hL, hLc⟩ := cls_surj (evc hM (fst A Y) (snd A Y ≫ u) - evc hN (fst A Y) (snd A Y ≫ t))
  have hloc' : ∀ y : Y.left, ∃ V : Y.left.Opens, y ∈ V ∧ ∃ g : LB.Gen (L.pull (p ⁻¹ᵁ V).ι), g.IsGen := by
    intro y
    obtain ⟨W, hyW, hW⟩ := hloc y
    refine ⟨W, hyW, (cls_eq_zero_iff (pull_isLB hL _)).1 ?_⟩
    rw [cls_pull hL, hLc]
    let j : Over.mk (W.ι ≫ Y.hom) ⟶ Y := Over.homMk W.ι rfl
    have h0 : CechPic.pull (A ◁ j).left
        (evc hM (fst A Y) (snd A Y ≫ u) - evc hN (fst A Y) (snd A Y ≫ t)) = 0 := by
      rw [map_sub, pull_evc, pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd_assoc, sub_eq_zero]
      exact (same_iff hM hN _ _).1 hW
    let P : Over (Sp R) := Over.mk ((p ⁻¹ᵁ W).ι ≫ (A ⊗ Y).hom)
    let k : P ⟶ A ⊗ Y := Over.homMk (p ⁻¹ᵁ W).ι rfl
    have hr : Set.range ((p ⁻¹ᵁ W).ι ≫ p) ⊆ Set.range W.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.2
    let w : P ⟶ Over.mk (W.ι ≫ Y.hom) := Over.homMk (IsOpenImmersion.lift W.ι ((p ⁻¹ᵁ W).ι ≫ p) hr) (by
      simp only [Over.mk_hom, P]
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, Over.w (snd A Y)])
    let φ : P ⟶ A ⊗ Over.mk (W.ι ≫ Y.hom) := lift (k ≫ fst A Y) w
    have hφ : φ ≫ (A ◁ j) = k := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      · rw [Category.assoc, whiskerLeft_snd, lift_snd_assoc]
        exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    have e2 : (p ⁻¹ᵁ W).ι = φ.left ≫ (A ◁ j).left := by rw [← Over.comp_left, hφ]; rfl
    rw [e2, pull_comp, h0, map_zero]
  obtain ⟨N', hN', w, hw⟩ := GlobalTheory.CubeLawCompare.iso_pull_of_locally_trivial p hp hL hloc'
  have h1 : CechPic.pull p (cls N' hN') = cls L hL := by
    rw [← cls_pull hN' p (pull_isLB hN' p)]
    exact (cls_eq_iff _ hL).2 ⟨w, hw⟩
  have h2 : CechPic.pull e (cls L hL) = 0 := by
    rw [hLc, map_sub, pull_evc, pull_evc, lift_fst, lift_snd_assoc, Category.id_comp, hMr, hNr, sub_zero]
  have h3 : cls N' hN' = 0 := by
    rw [← h2, ← h1, ← pull_comp, he, pull_id]
  rw [← hLc, ← h1, h3, map_zero]

end GlobalTheory.DualCon.SameLocal
end
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.KernelHalf

open GlobalTheory.ColNorms GlobalTheory.ColNorms.NumMean

theorem exists_le_wtSum {α : Type} [Fintype α] (w f : α → ℝ) (h0 : ∀ a, 0 ≤ w a) (h1 : ∑ a, w a = 1) :
    ∃ a, w a ≠ 0 ∧ f a ≤ ∑ b, w b * f b := by
  by_contra hc
  push_neg at hc
  have h2 : ∑ a, w a * (∑ b, w b * f b) < ∑ a, w a * f a := by
    obtain ⟨a, ha⟩ : ∃ a, w a ≠ 0 := by
      by_contra h
      push_neg at h
      simp [h] at h1
    refine Finset.sum_lt_sum (fun b _ => ?_) ⟨a, Finset.mem_univ _, ?_⟩
    · by_cases hb : w b = 0
      · simp [hb]
      · exact mul_le_mul_of_nonneg_left (hc b hb).le (h0 b)
    · exact mul_lt_mul_of_pos_left (hc a ha) (lt_of_le_of_ne (h0 a) (Ne.symm ha))
  rw [← Finset.sum_mul, h1, one_mul] at h2
  exact lt_irrefl _ h2

theorem wt_affine {α Z : Type} [Fintype α] [Fintype Z] (w : α → ℝ) (hw : ∑ a, w a = 1) (p q : Z → ℝ) (o : α → Z → ℝ) (t : α → ℝ)
    (c₁ c₂ : ℝ) :
    ∑ a, w a * ((∑ z, (p z - q z * o a z)) + t a + c₁ + c₂) =
      (∑ z, (p z - q z * ∑ a, w a * o a z)) + (∑ a, w a * t a) + c₁ + c₂ := by
  have h1 : ∑ a, w a * ∑ z, (p z - q z * o a z) = ∑ z, (p z - q z * ∑ a, w a * o a z) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    have : ∑ a, w a * (p z - q z * o a z) = (∑ a, w a) * p z - ∑ a, q z * (w a * o a z) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, hw, one_mul]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul, h1]

theorem kernelBound_wt (N : NumDatum) (δ : Code N) (T : ℕ) (CK : ℝ) (j : ℕ) {α : Type} [Fintype α] (w : α → ℝ) (hw : ∑ a, w a = 1)
    (lo : α → RPl N.R → ℝ) (lt : α → ℝ) (h h' n n' : ℕ) :
    ∑ a, w a * kernelBound_sq N δ T CK j (lo a) (lt a) h h' n n' =
      kernelBound_sq N δ T CK j (fun z => ∑ a, w a * lo a z) (∑ a, w a * lt a) h h' n n' := by
  unfold kernelBound_sq
  exact wt_affine w hw _ _ lo lt _ _

theorem wt_mean {α Emb : Type} [Fintype α] [Fintype Emb] (wt : Emb → α → ℝ) (c d : ℝ) (h : ∀ a, (∑ v, wt v a) / c = 1 / d) (x : α → ℝ) :
    (∑ v, ∑ a, wt v a * x a) / c = (∑ a, x a) / d := by
  rw [Finset.sum_comm, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_mul, mul_div_right_comm, h a]
  ring

theorem sum_filter_eq {J : Type} [Fintype J] {m : ℕ} (eJ : J ≃ Fin m) (t : J → ℝ) {i : ℕ} (hi : i < m) :
    ∑ l ∈ Finset.univ.filter (fun l => (eJ l).1 = i), t l = t (eJ.symm ⟨i, hi⟩) := by
  have : Finset.univ.filter (fun l => (eJ l).1 = i) = {eJ.symm ⟨i, hi⟩} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      rw [Equiv.eq_symm_apply]
      exact Fin.ext h
    · rintro rfl
      simp
  rw [this, Finset.sum_singleton]

theorem sum_filter_ge {J : Type} [Fintype J] {m : ℕ} (hm : 2 ≤ m) (eJ : J ≃ Fin m) (t : J → ℝ) :
    ∑ l ∈ Finset.univ.filter (fun l => m - 2 ≤ (eJ l).1), t l =
      t (eJ.symm ⟨m - 2, by omega⟩) + t (eJ.symm ⟨m - 1, by omega⟩) := by
  classical
  have hne : eJ.symm ⟨m - 2, by omega⟩ ≠ eJ.symm ⟨m - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val (eJ.symm.injective h)
    simp only at this
    omega
  have : Finset.univ.filter (fun l => m - 2 ≤ (eJ l).1) = {eJ.symm ⟨m - 2, by omega⟩, eJ.symm ⟨m - 1, by omega⟩} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have h2 := (eJ l).2
      rcases (by omega : (eJ l).1 = m - 2 ∨ (eJ l).1 = m - 1) with h3 | h3
      · left
        rw [Equiv.eq_symm_apply]
        exact Fin.ext h3
      · right
        rw [Equiv.eq_symm_apply]
        exact Fin.ext h3
    · rintro (rfl | rfl) <;> simp <;> omega
  rw [this, Finset.sum_pair hne]

theorem factorBounds_of_weights {K : Type} [Field K] [NumberField K] [StarRing K] (Q : KerChain K) {α J : Type} [Fintype α] [Fintype J]
    {m : ℕ} (hm : 2 ≤ m) (hn : Q.n = m - 2) (eJ : J ≃ Fin m) (pu : α → InfinitePlace K) (wt : InfinitePlace K → α → ℝ)
    (h0 : ∀ v a, 0 ≤ wt v a) (h1 : ∀ v, ∑ a, wt v a = 1) (hup : ∀ v a, wt v a ≠ 0 → pu a = v) (lb : α → ℕ → ℝ)
    (hpos : ∀ i v φ, 0 ≤ (famIpAt (Q.F i) (Q.hF i) v φ φ).re)
    (hS : ∀ a i, i + 2 < m → StepBound_sq Q i (pu a) (lb a (i + 1)))
    (hC : ∀ a, CplBound_sq Q (pu a) (lb a (m - 1) + lb a m))
    (t : J → InfinitePlace K → ℝ) (ht : ∀ l v, t l v = ∑ a, wt v a * lb a ((eJ l).1 + 1)) :
    FactorBounds Q (fun l => (eJ l).1) t := by
  refine ⟨fun i hi v => ?_, fun v => ?_⟩
  · have hi' : i + 2 < m := by omega
    have hi1 : i < m := by omega
    rw [sum_filter_eq eJ (fun l => t l v) hi1, ht]
    obtain ⟨a, ha, hle⟩ := exists_le_wtSum (wt v) (fun a => lb a (i + 1)) (h0 v) (h1 v)
    have h2 := hS a i hi'
    rw [hup v a ha] at h2
    simp only [Equiv.apply_symm_apply]
    exact h2.mono hle (hpos i v)
  · rw [hn, sum_filter_ge hm eJ (fun l => t l v), ht, ht]
    obtain ⟨a, ha, hle⟩ := exists_le_wtSum (wt v) (fun a => lb a (m - 1) + lb a m) (h0 v) (h1 v)
    have h2 := hC a
    rw [hup v a ha] at h2
    simp only [Equiv.apply_symm_apply]
    have e1 : m - 2 + 1 = m - 1 := by omega
    have e2 : m - 1 + 1 = m := by omega
    rw [e1, e2, ← Finset.sum_add_distrib]
    simp only [mul_add] at hle
    intro φ
    refine (h2 φ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hle) (hpos _ v φ))

theorem one_le_f (R : Ranks) : (1 : ℝ) ≤ R.f := by
  have : 1 ≤ R.f := by
    unfold Ranks.f Ranks.n
    have := And.intro (Nat.one_le_two_pow (n := R.e)) (show 0 < R.ord from R.ord_pos)
    omega
  exact_mod_cast this

theorem one_le_Nm (N : NumDatum) : (1 : ℝ) ≤ N.Nm := by
  have : 1 ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    have := N.R.m_add_three_le_k
    omega
  exact_mod_cast this

theorem L_le_La (N : NumDatum) : N.sc.L ≤ N.La := by
  have hb := two_le_b N.sc
  have hx := N.sc.one_lt_alt
  have hrd := one_le_rd N
  have h1 : N.sc.b ≤ N.sc.a := by
    unfold Scale.a
    exact le_mul_of_one_le_left (by linarith) hx.le
  have h2 : N.sc.a ≤ N.sc.a * N.rd := le_mul_of_one_le_right (by linarith) hrd
  calc N.sc.L = Real.log (Real.exp N.sc.L) := (Real.log_exp _).symm
    _ ≤ Real.log (N.sc.a * N.rd) := Real.log_le_log (Real.exp_pos _) (h1.trans h2)
    _ = N.La := rfl



end GlobalTheory.KernelHalf
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLogarithm_basis_lift_pdThickening : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ (Ideal.span {(p : B)}) → IsBasis μ e := by
  first | exact @GlobalTheory.basis_lift | exact GlobalTheory.basis_lift | (intros; apply GlobalTheory.basis_lift <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_formalSeries_of_coboundary_dvd_p : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 ∧ (∀ α, (p : O) ∣ coeff α (cob2 c.μ κ)) ∧ (∀ α, (p : O) ∣ coeff α (Katz.swap κ - κ)) ∧ (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) ∧ c.ev 1 B = b + (p : O) • y := by
  first | exact @GlobalTheory.QLog.exists_series_of_cobOne_dvd | exact GlobalTheory.QLog.exists_series_of_cobOne_dvd | (intros; apply GlobalTheory.QLog.exists_series_of_cobOne_dvd <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundle_iso_tangent_pull_constant_deformation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x₀ : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G x₀ π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) := by
  first | exact @GlobalTheory.TangentConstLB.lbIso_tangent_const | exact GlobalTheory.TangentConstLB.lbIso_tangent_const | (intros; apply GlobalTheory.TangentConstLB.lbIso_tangent_const <;> assumption)
end
