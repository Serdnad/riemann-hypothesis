module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.ClosedFibreDvd

theorem mem_span_of_forall_pow {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] (a s : O)
    (h : ∀ n : ℕ, s ∈ Ideal.span {a} ⊔ maximalIdeal O ^ (n + 1)) : s ∈ Ideal.span {a} := by
  by_cases ht : Ideal.span {a} = ⊤
  · rw [ht]; trivial
  haveI : Nontrivial (O ⧸ Ideal.span {a}) := Ideal.Quotient.nontrivial_iff.2 ht
  haveI : IsLocalRing (O ⧸ Ideal.span {a}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk (Ideal.span {a})) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing
    (maximalIdeal (O ⧸ Ideal.span {a})) (maximalIdeal.isMaximal _).ne_top, Ideal.mem_iInf]
  intro n
  have hle : Ideal.map (Ideal.Quotient.mk (Ideal.span {a})) (Ideal.span {a} ⊔ maximalIdeal O ^ (n + 1)) ≤
      maximalIdeal (O ⧸ Ideal.span {a}) ^ n := by
    rw [Ideal.map_sup, Ideal.map_pow]
    refine sup_le ?_ ?_
    · rw [Ideal.map_quotient_self]; exact bot_le
    · refine le_trans ?_ (Ideal.pow_le_pow_right (Nat.le_succ n))
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit _ r hr) _
  exact hle (Ideal.mem_map_of_mem _ (h n))

theorem ker_stalkMap_le {X H : Scheme.{0}} (j : H ⟶ X) [IsClosedImmersion j] (z : H)
    (I : Ideal (X.presheaf.stalk (j z))) (hI : I ≠ ⊤)
    (ℓ : Spec (CommRingCat.of (X.presheaf.stalk (j z) ⧸ I)) ⟶ H)
    (hℓ : ℓ ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk (j z)) :
    RingHom.ker (j.stalkMap z).hom ≤ I := by
  intro a ha
  haveI : Nontrivial (X.presheaf.stalk (j z) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : IsLocalRing (X.presheaf.stalk (j z) ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have e : ℓ (IsLocalRing.closedPoint _) = z := by
    apply j.isEmbedding.injective
    refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hℓ).trans ?_
    exact (congrArg (X.fromSpecStalk (j z)) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
      Scheme.fromSpecStalk_closedPoint
  let ψ := H.presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo ℓ
  have hψ : j.stalkMap z ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (j z)), ← hℓ, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
  have hψ' := congrArg (fun q => q.hom a) hψ
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hψ'
  rw [RingHom.mem_ker.1 ha, map_zero] at hψ'
  exact Ideal.Quotient.eq_zero_iff_mem.1 hψ'.symm

def cstHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) : R →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p x) trivial ≫ p.stalkMap x).hom

theorem cstHom_apply {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) (c : R) :
    cstHom p x c = cst p x c := by
  rw [cst, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl

theorem fromSpecStalk_comp {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) :
    X.fromSpecStalk x ≫ p = Spec.map (CommRingCat.ofHom (cstHom p x)) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, ← Spec.map_comp]; rfl

theorem exists_lift {R : Type} [CommRing R] (J : Ideal R) {X Y P : Scheme.{0}} (π : Y ⟶ Sp R) (p : X ⟶ Sp R)
    (fs : P ⟶ Y) (sn : P ⟶ Spec (CommRingCat.of (R ⧸ J)))
    (hP : IsPullback fs sn π (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (k : Y ⟶ X) (h : X ⟶ Y) (hh : h ≫ π = p) (hk : h ≫ k = 𝟙 X) (z : P)
    (I : Ideal (X.presheaf.stalk ((fs ≫ k) z))) (hJ : Ideal.map (cstHom p _) J ≤ I) :
    ∃ ℓ : Spec (CommRingCat.of (X.presheaf.stalk ((fs ≫ k) z) ⧸ I)) ⟶ P,
      ℓ ≫ (fs ≫ k) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk _ := by
  let L : R ⧸ J →+* X.presheaf.stalk ((fs ≫ k) z) ⧸ I := Ideal.Quotient.lift J ((Ideal.Quotient.mk I).comp (cstHom p _))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hJ (Ideal.mem_map_of_mem _ ha)))
  have w : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk _) ≫ h) ≫ π =
      Spec.map (CommRingCat.ofHom L) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    rw [Category.assoc, Category.assoc, hh, fromSpecStalk_comp, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  refine ⟨hP.lift _ _ w, ?_⟩
  rw [← Category.assoc, hP.lift_fst, Category.assoc, hk, Category.comp_id]

theorem cst_stalkMap' {V : Type} [CommRing V] {X Z : Scheme.{0}} (r : Z ⟶ X) (p : X ⟶ Sp V) (z : Z) (a : V) :
    (r.stalkMap z).hom (cst p (r z) a) = cst (r ≫ p) z a := by
  have e := gs_pull (𝟙 X) p (r z) ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  rw [Category.id_comp] at e
  exact (congrArg (r.stalkMap z).hom e.symm).trans ((gs_stalkMap r z (p ⁻¹ᵁ ⊤) trivial _).symm.trans
    (gs_pull r p z ⊤ trivial _))

theorem germ_dvd_of_expT_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∀ (x : (𝟙_ (Over (Sp R)) ⊗ G).left), (𝟙_ (Over (Sp R)) ⊗ G).hom x = closedPoint R → ∀ (j : Fin 1 → U.P.L.L.ι), x ∈ LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j → ∃ t, gs (𝟙 _) x (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j) = cst (𝟙_ (Over (Sp R)) ⊗ G).hom x q * t := by
  intro R _ _ _ hR D A G _ _ U σ f g q hE hM x hx j hxj
  haveI : IsNoetherianRing R := hR.1.1
  haveI : Smooth G.hom := U.semi.smooth
  have lam : (snd (𝟙_ (Over (Sp R))) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ G).inv.left ≫ (snd (𝟙_ (Over (Sp R))) G).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]
  have lamA' : (λ_ D.P.A).inv.left ≫ (snd (𝟙_ (Over (Sp R))) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]
  have toU : ∀ {Y : Over (Sp R)} (h : Y ⟶ 𝟙_ (Over (Sp R))), h.left = Y.hom := fun h => by simpa using Over.w h
  have hpG : (snd (𝟙_ (Over (Sp R))) G).left ≫ G.hom = (𝟙_ (Over (Sp R)) ⊗ G).hom := Over.w _
  haveI : IsIso (snd (𝟙_ (Over (Sp R))) G).left := ⟨⟨(λ_ G).inv.left, lam, lam'⟩⟩
  haveI : LocallyOfFiniteType (𝟙_ (Over (Sp R)) ⊗ G).hom := by rw [← hpG]; infer_instance
  haveI : IsLocallyNoetherian (𝟙_ (Over (Sp R)) ⊗ G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (𝟙_ (Over (Sp R)) ⊗ G).hom
  suffices H : gs (𝟙 _) x (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j) ∈
      Ideal.span {cst (𝟙_ (Over (Sp R)) ⊗ G).hom x q} by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 H
    exact ⟨t, by rw [← ht, mul_comm]⟩
  refine mem_span_of_forall_pow _ _ fun e => ?_
  have hxg : G.hom ((snd (𝟙_ (Over (Sp R))) G).left x) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, hpG]; exact hx
  haveI : Nontrivial (R ⧸ maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  haveI : IsLocalRing (R ⧸ maximalIdeal R ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hw : thick R (maximalIdeal R) e (closedPoint _) = closedPoint R := by
    have := IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))
    exact this
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := thick R (maximalIdeal R) e) _ _
    (hxg.trans hw.symm)
  have hzx : (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z = x := by
    rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, lam]; rfl
  subst hzx

  have hc : IsClosedImmersion (thick R (maximalIdeal R) e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

  haveI : IsIso (λ_ G).inv.left := ⟨⟨(snd (𝟙_ (Over (Sp R))) G).left, lam', lam⟩⟩
  haveI : IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e)) := inferInstance
  haveI : IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) := inferInstance

  have hmap : Ideal.map (cstHom (𝟙_ (Over (Sp R)) ⊗ G).hom
      ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)) (maximalIdeal R ^ (e + 1)) ≤
      maximalIdeal _ ^ (e + 1) := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun c hc' => ?_) _
    rw [Ideal.mem_comap, cstHom_apply]
    exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (cst_not_isUnit _ _ hx hc'))
  have hker : RingHom.ker ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap z).hom ≤
      maximalIdeal _ ^ (e + 1) := by
    have hI : Ideal.map (cstHom (𝟙_ (Over (Sp R)) ⊗ G).hom
        ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)) (maximalIdeal R ^ (e + 1)) ≠ ⊤ :=
      ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top (hmap.trans (Ideal.pow_le_self (Nat.succ_ne_zero e)))
    obtain ⟨ℓ, hℓ⟩ := exists_lift (maximalIdeal R ^ (e + 1)) G.hom (𝟙_ (Over (Sp R)) ⊗ G).hom
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _) (λ_ G).inv.left
      (snd (𝟙_ (Over (Sp R))) G).left hpG lam z _ le_rfl
    exact (ker_stalkMap_le _ z _ hI ℓ hℓ).trans hmap

  obtain ⟨S, hS⟩ := hE e
  obtain ⟨JG, hJG⟩ := GlobalTheory.UU.exists_good_pt U.P.L.isLB z
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  have h3 : ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (fst (𝟙_ (Over (Sp R))) D.P.A).left =
      (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫ (fst (𝟙_ (Over (Sp R))) G).left := by
    rw [toU, toU, Category.assoc, Category.assoc, Over.w (λ_ D.P.A).inv, Over.w (λ_ G).inv, Over.w (U.gt e).pG,
      pullback.condition]
    rfl
  have key := (hS _ (𝟙 _) (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left)
    ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left)
    (by rw [Category.assoc, lam', Category.comp_id, Category.id_comp]; rfl)
    (by rw [Category.assoc, lamA', Category.comp_id, Category.id_comp]) h3 z JG J hJG hJ).2

  have aux : ∀ {O : Type} [CommRing O] (u : Oˣ) (a b : O) (I : Ideal O), (u : O) ^ 1 * a = b → b ∈ I → a ∈ I :=
    fun u a b I h hb => by
      rw [pow_one] at h
      rw [← u.inv_mul_cancel_left a, h]
      exact I.mul_mem_left _ hb
  have hq : ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom =
      (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    rw [Category.assoc, Category.assoc, Over.w (λ_ D.P.A).inv, Over.w (λ_ G).inv, Over.w (U.gt e).pG,
      pullback.condition]
    rfl
  have hmem : sval σ (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z JG ∈
      Ideal.span {cst ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫
        (𝟙_ (Over (Sp R)) ⊗ G).hom) z q} := by
    refine aux _ _ _ _ key (Ideal.sum_mem _ fun α _ => ?_)
    have hF : sval (f α) ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) z J =
        cst (((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom) z q *
          sval (g α) ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) z J :=
      secIsMul_gs (hM α) _ z _ (hJ.mem _ _)
    rw [hF, hq, _root_.mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hπ : ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap z).hom
      (gs (𝟙 _) ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)
        (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j)) ∈
      Ideal.span {cst ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫
        (𝟙_ (Over (Sp R)) ⊗ G).hom) z q} := by
    have e1 := gs_stalkMap (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z _ hxj (σ.f j)
    erw [← e1, sec_trans σ _ z hxj (hJG.mem _ _)]
    exact Ideal.mul_mem_left _ _ hmem
  obtain ⟨t', ht'⟩ := Ideal.mem_span_singleton'.1 hπ
  obtain ⟨t, rfl⟩ := (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap_surjective z t'
  refine Submodule.mem_sup.2 ⟨t * cst (𝟙_ (Over (Sp R)) ⊗ G).hom
    ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z) q,
    Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), _, hker ?_, add_sub_cancel _ _⟩
  rw [RingHom.mem_ker, map_sub, map_mul, cst_stalkMap', ht', sub_self]

end GlobalTheory.ClosedFibreDvd

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.FibreAmple

noncomputable section

namespace GlobalTheory.DiagAmpleLocus

theorem diag_relAmple_locus : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → Set.range g.base ⊆ (U : Set S') := by
  intro S' _ G _ _ P hG hP
  have := hG.proper
  have : Flat G.hom := by have := hG.smooth; infer_instance
  have hD : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  let good : Set S' := {s | ∃ (Y X : Scheme.{0}) (j : Y ⟶ S') (_ : IsOpenImmersion j) (π : X ⟶ G.left)
      (f : X ⟶ Y), IsPullback π f G.hom j ∧ s ∈ Set.range j.base ∧
        RelAmple (Over.mk f) ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull π)}
  have hopen : IsOpen good := by
    rw [isOpen_iff_forall_mem_open]
    rintro s ⟨Y, X, j, hj, π, f, h, hs, hA⟩
    exact ⟨Set.range j.base, fun x hx => ⟨Y, X, j, hj, π, f, h, hx, hA⟩,
      j.isOpenEmbedding.isOpen_range, hs⟩
  refine ⟨⟨good, hopen⟩, fun V hV => ?_, ?_⟩
  · let AV := (Over.pullback V.ι).obj G
    have : IsProper AV.hom := inferInstanceAs (IsProper (pullback.snd G.hom V.ι))
    have key : RelAmple AV ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (pullback.fst G.hom V.ι)) := by
      refine GlobalTheory.AmpleLocal.relAmple_of_locally V AV _ (pull_isLB hD _) inferInstance inferInstance
        fun v => ?_
      obtain ⟨Y, X, j, hj, π, f, h, ⟨y, hy⟩, hA⟩ := hV v.2
      let V' : V.toScheme.Opens := V.ι ⁻¹ᵁ j.opensRange
      have hv : v ∈ V' := ⟨y, hy⟩
      have hrange : Set.range (V'.ι ≫ V.ι).base ⊆ Set.range j.base := by
        rintro _ ⟨w, rfl⟩
        exact w.2
      have sq : IsPullback ((AV.hom ⁻¹ᵁ V').ι ≫ pullback.fst G.hom V.ι) (AV.hom ∣_ V') G.hom (V'.ι ≫ V.ι) :=
        (isPullback_morphismRestrict AV.hom V').flip.paste_horiz (IsPullback.of_hasPullback G.hom V.ι)
      have h₁ := relAmple_of_factor hD h sq (IsOpenImmersion.lift j _ hrange)
        (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hD π) (GlobalTheory.lbIso_refl (pull_isLB hD π)) hA
      have : IsProper (Over.mk (AV.hom ∣_ V')).hom := inferInstanceAs (IsProper (AV.hom ∣_ V'))
      exact ⟨V', hv, GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _)
        (pull_isLB (pull_isLB hD _) _) (lbIso_pull_pull hD _ _) h₁⟩
    have e₁ : LBIso ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 AV) (𝟙 AV)).left)
        (P.pull ((lift (𝟙 AV) (𝟙 AV)).left ≫ Pdiv.PullbackComparison.pφ₂ V.ι G)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    rw [GlobalTheory.DiagAmpleBC.diag_comp G AV _ _ (Pdiv.PullbackComparison.isSquare V.ι G)] at e₁
    have e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (Pdiv.PullbackComparison.pφ V.ι G))
        (P.pull (Pdiv.PullbackComparison.pφ V.ι G ≫ (lift (𝟙 G) (𝟙 G)).left)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    exact GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _) (pull_isLB (pull_isLB hP _) _)
      (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hD _) e₁ e₂.symm) key
  · rintro T g A' _ φ φ₂ P' hpb hsq hP' e hA _ ⟨t, rfl⟩
    have h₀ : IsPullback φ A'.hom G.hom g := hpb.1
    have : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) h₀ ‹_›
    have e₁ : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) (P.pull ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp e _
    rw [GlobalTheory.DiagAmpleBC.diag_comp G A' φ φ₂ hsq] at e₁
    have e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) (P.pull (φ ≫ (lift (𝟙 G) (𝟙 G)).left)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    have hA' : RelAmple A' ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) :=
      GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hP' _) (pull_isLB hD _)
        (LBIso.trans (pull_isLB hD _) (pull_isLB hP _) (pull_isLB hP' _) e₂ e₁.symm) hA
    obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S') (U := ⊤) (x := g.base t) trivial
    have : IsNoetherianRing Γ(S', V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    obtain ⟨VT, hVT, ht, hle⟩ := exists_isAffineOpen_mem_and_subset (X := T) (U := g ⁻¹ᵁ V) (x := t) hs
    obtain ⟨q, hq⟩ : t ∈ Set.range hVT.fromSpec.base := by rw [hVT.range_fromSpec]; exact ht
    let tV : Sp Γ(S', V) ⟶ S' := hV.fromSpec
    let φR := g.appLE V VT hle
    have sqR : Spec.map φR ≫ hV.fromSpec = hVT.fromSpec ≫ g := IsAffineOpen.SpecMap_appLE_fromSpec g hV hVT hle
    let p : PrimeSpectrum Γ(S', V) := (Spec.map φR).base q
    have hp : tV.base p = g.base t := by
      have := congrArg (fun f : Spec Γ(T, VT) ⟶ S' => f.base q) sqR
      simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at this
      rw [← hq]
      exact this
    have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime (q : PrimeSpectrum Γ(T, VT))
    have : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    let k := p.asIdeal.ResidueField
    let kq := q.asIdeal.ResidueField
    let gR := algebraMap Γ(S', V) k
    let i : k →+* kq := Ideal.ResidueField.map p.asIdeal q.asIdeal φR.hom rfl
    have hi : spMap (algebraMap Γ(T, VT) kq) ≫ Spec.map φR = spMap i ≫ spMap gR := by
      show Spec.map (CommRingCat.ofHom _) ≫ Spec.map φR = Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom gR)
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (Ideal.ResidueField.map_algebraMap _ _ _ _ x).symm
    let y : Sp kq ⟶ S' := spMap i ≫ spMap gR ≫ tV
    have hu : (spMap (algebraMap Γ(T, VT) kq) ≫ hVT.fromSpec) ≫ g = y := by
      rw [Category.assoc, ← sqR, ← Category.assoc, hi, Category.assoc]
    have hfib := relAmple_of_factor hD h₀ (IsPullback.of_hasPullback G.hom y) _ hu (pull_isLB hD φ)
      (GlobalTheory.lbIso_refl (pull_isLB hD φ)) hA'
    let B : Over (Sp Γ(S', V)) := Over.mk (pullback.snd G.hom tV)
    have : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd G.hom tV))
    have : Flat B.hom := inferInstanceAs (Flat (pullback.snd G.hom tV))
    have hB := IsPullback.of_hasPullback G.hom tV
    have hL := pull_isLB hD (pullback.fst G.hom tV)
    obtain ⟨r, hr, hAr⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hL gR (residueField_fraction p.asIdeal)
      (relAmple_of_fieldExtension hD i ((IsPullback.of_hasPullback B.hom (spMap gR)).paste_horiz hB)
        (IsPullback.of_hasPullback G.hom _) (pull_isLB hL _) (lbIso_pull_pull hD _ _) hfib)
    let Dr : (Sp Γ(S', V)).Opens := PrimeSpectrum.basicOpen r
    have hpD : p ∈ Dr := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
    have : IsProper (Over.mk (pullback.snd B.hom Dr.ι)).hom := inferInstanceAs (IsProper (pullback.snd B.hom Dr.ι))
    exact ⟨Dr.toScheme, _, Dr.ι ≫ tV, inferInstance, pullback.fst B.hom Dr.ι ≫ pullback.fst G.hom tV,
      pullback.snd B.hom Dr.ι, (IsPullback.of_hasPullback B.hom Dr.ι).paste_horiz hB, ⟨⟨p, hpD⟩, hp⟩,
      GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hL _) (pull_isLB hD _) (lbIso_pull_pull hD _ _).symm hAr⟩

end GlobalTheory.DiagAmpleLocus
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.basis_tangentModule_abelianScheme_of_relDim : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (d : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension d G.hom → Nonempty (Module.Basis (Fin d) R (TanM (𝟙 (Sp R)) G)) := by
  first | exact @GlobalTheory.TanBasisDim.basis_tanM_abelian | exact GlobalTheory.TanBasisDim.basis_tanM_abelian | (intros; apply GlobalTheory.TanBasisDim.basis_tanM_abelian <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_basis_tangentModule_smooth_commGroupScheme : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) := by
  first | exact @GlobalTheory.TanBasis.exists_basis_tanM | exact GlobalTheory.TanBasis.exists_basis_tanM | (intros; apply GlobalTheory.TanBasis.exists_basis_tanM <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smooth_commGroupSchemeHom_tangentAtOrigin_surjective : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G B : Over (Sp R)) [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B] (q : G ⟶ B) [IsMonHom q], Smooth q.left → ∀ u : TanM (𝟙 (Sp R)) B, ∃ v : TanM (𝟙 (Sp R)) G, tv v ≫ q = tv u := by
  first | exact @GlobalTheory.LieSurjLocal.map_surjective | exact GlobalTheory.LieSurjLocal.map_surjective | (intros; apply GlobalTheory.LieSurjLocal.map_surjective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_rescaled_iso_preserving_rigidification : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L₁ L₂ : RigLB G)
    (e : LB.Iso L₁.L L₂.L), e.IsGen → ∃ e' : LB.Iso L₁.L L₂.L, e'.IsGen ∧
      LB.Gen.Maps (LB.linCombIso e' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  first | exact @GlobalTheory.RigRescale.exists_isGen_maps_rig | exact GlobalTheory.RigRescale.exists_isGen_maps_rig | (intros; apply GlobalTheory.RigRescale.exists_isGen_maps_rig <;> assumption)
end
