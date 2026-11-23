module

public import Development.EtaleCohomology.EtaleSheaves.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle012
public import Development.EtaleCohomology.EtaleSheaves.Bundle076
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.EtaleCohomology.EtaleSheaves.Bundle079
public import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf
public import Development.EtaleCohomology.EtaleSheaves.Bundle066
public import Development.EtaleCohomology.EtaleSheaves.Bundle082
public import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutQuasiFinitenessBaseChange

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    toR R' ≫ incl hR = toR R := by
  rw [← Spec.map_comp]; rfl

theorem sq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {q : D ⟶ Sp R} {v : C ⟶ D} (hv : IsPullback v c q (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hv.w)) c
      (pullback.snd q (incl hR)) (toR R') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl hR))
  rw [pullback.lift_fst, toR_incl]; exact hv

theorem spread_chain_base_change_to_larger_subalgebra : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafBaseChangePreR := by
  intro k _ Ω _ _ R R' hR C0 C1 C2 c0 γ1 γ2 D0 D1 D2 q d1 d2 v0 v1 v2 hpre
  obtain ⟨-, -, -, p0, p1, p2, m1, m2⟩ := hpre
  let e1 : pullback (d1 ≫ q) (incl hR) ⟶ pullback q (incl hR) :=
    pullback.lift (pullback.fst _ _ ≫ d1) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  let e2 : pullback (d2 ≫ d1 ≫ q) (incl hR) ⟶ pullback (d1 ≫ q) (incl hR) :=
    pullback.lift (pullback.fst _ _ ≫ d2) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  have t1 : e1 ≫ pullback.snd q (incl hR) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have t2 : e2 ≫ pullback.snd (d1 ≫ q) (incl hR) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have t12 : e2 ≫ e1 ≫ pullback.snd q (incl hR) = pullback.snd _ _ := by rw [t1, t2]
  have P0 := sq hR p0
  have P1 := sq hR p1
  have P2 := sq hR p2
  refine ⟨_, _, _, pullback.snd q (incl hR), e1, e2, _, pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact p1.w), pullback.lift v2 ((γ2 ≫ γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact p2.w), pullback.fst _ _, pullback.fst _ _, pullback.fst _ _,
    ⟨P0, ?_, ?_, ?_, ?_⟩, IsPullback.of_hasPullback _ _, ?_, ?_, pullback.lift_fst _ _ _,
    pullback.lift_fst _ _ _, pullback.lift_fst _ _ _⟩
  · rw [t1]; exact P1
  · rw [t12]; exact P2
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, e1, pullback.lift_fst_assoc]; exact m1
    · simp only [Category.assoc, pullback.lift_snd, e1]
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, e2, pullback.lift_fst_assoc]; exact m2
    · simp only [Category.assoc, pullback.lift_snd, e2]
  · rw [t1]; exact IsPullback.of_hasPullback _ _
  · rw [t12]; exact IsPullback.of_hasPullback _ _

theorem LeafSpreadQF_of (hSep : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated)
    (hSm : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1) (hG : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph)
    (hM : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap) : LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF :=
  LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadQF_of hSep hSm hG hM spread_chain_base_change_to_larger_subalgebra

end LateralTheory.E.SpreadingOutQuasiFinitenessBaseChange

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutLocallyQuasiFinite

def LeafQFAtBaseChange : Prop := ∀ {EA EB A B : Scheme.{0}} (h : EA ⟶ EB) (g : A ⟶ B) (rA : EA ⟶ A) (rB : EB ⟶ B),
    IsPullback rA h g rB → LocallyOfFiniteType g → ∀ x : EA, g.QuasiFiniteAt (rA x) → h.QuasiFiniteAt x

def LeafQFAtDescend : Prop := ∀ {CA CB A B : Scheme.{0}} (γ : CA ⟶ CB) (g : A ⟶ B) (vA : CA ⟶ A) (vB : CB ⟶ B),
    IsPullback vA γ g vB → LocallyOfFiniteType g → ∀ x : CA, γ.QuasiFiniteAt x → g.QuasiFiniteAt (vA x)

def LeafOpenSpread : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C A : Scheme.{0}} (c : C ⟶ Sp Ω) (p : A ⟶ Sp R) (v : C ⟶ A) (U : A.Opens),
    (LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p) → IsPullback v c p (toR R) →
    (∀ x : C, v x ∈ U) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ A), IsPullback r q' p (incl hR) → ∀ z : E, r z ∈ U

theorem quasi_finite_at_base_change_of_finite_type : LeafQFAtBaseChange := by
  intro EA EB A B h g rA rB sq hg x hx
  let U := g.quasiFiniteLocus
  have sq2 : IsPullback (rA ∣_ U) ((rA ⁻¹ᵁ U).ι ≫ h) (U.ι ≫ g) rB :=
    (isPullback_morphismRestrict rA U).paste_vert sq
  have : LocallyQuasiFinite ((rA ⁻¹ᵁ U).ι ≫ h) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq2 inferInstance
  have hxV : x ∈ rA ⁻¹ᵁ U := hx
  have := ((rA ⁻¹ᵁ U).ι ≫ h).quasiFiniteAt ⟨x, hxV⟩
  have h2 := (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion (f := (rA ⁻¹ᵁ U).ι) (g := h)
    (x := ⟨x, hxV⟩)).mp this
  simpa using h2

theorem LeafSpreadLQFMap_of (hBC : LeafQFAtBaseChange) (hD : LeafQFAtDescend) (hO : LeafOpenSpread) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap := by
  intro k _ Ω _ _ R hR CA CB A B cB γ qB g vA vB hB hA pB pA hw hγ
  have : LocallyOfFinitePresentation (g ≫ qB) := hA.1
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g qB
  have sqC : IsPullback vA γ g vB := IsPullback.of_bot pA hw.symm pB
  have hU : ∀ x : CA, vA x ∈ g.quasiFiniteLocus := fun x =>
    hD γ g vA vB sqC inferInstance x (γ.quasiFiniteAt x)
  obtain ⟨S, hRS, hS, H⟩ := hO k Ω R hR (γ ≫ cB) (g ≫ qB) vA g.quasiFiniteLocus hA pA hU
  refine ⟨S, hRS, hS, ?_⟩
  intro R' hSR' hRR' EA EB qB' h rA rB QB QA hc
  have sqE : IsPullback rA h g rB := IsPullback.of_bot QA hc.symm QB
  have : LocallyOfFiniteType h :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sqE inferInstance
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  refine top_le_iff.mp fun z _ => ?_
  exact hBC h g rA rB sqE inferInstance z (H R' hSR' hRR' EA (h ≫ qB') rA QA z)

end LateralTheory.E.SpreadingOutLocallyQuasiFinite

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf GlobalTheory.GlueModels

namespace LateralTheory.E.LeafGlueTwoPf

def LeafPushoutFP : Prop := ∀ {DW DU DV S : Scheme.{0}} (φU : DW ⟶ DU) (φV : DW ⟶ DV) [IsOpenImmersion φU]
    [IsOpenImmersion φV] (qU : DU ⟶ S) (qV : DV ⟶ S) (h : φU ≫ qU = φV ≫ qV), IsAffine S →
    FP qU → FP qV → FP (φU ≫ qU) → FP (pushout.desc qU qV h)

set_option backward.isDefEq.respectTransparency false in
theorem LeafGlueTwo_of (hF : LeafPushoutFP) : LeafGlueTwo := by
  intro k _ Ω _ _ X f U V R hUV ⟨DU, DV, DW, qU, qV, qW, vU, vV, vW, φU, φV, hqU, hqV, hqW, hφU, hφV, eU, eV,
    pU, pV, pW, cU, cV⟩
  have hc : ∀ x : X, x ∈ Set.range U.ι ∨ x ∈ Set.range V.ι := by
    intro x
    have hx : x ∈ (U ⊔ V : X.Opens) := by rw [hUV]; trivial
    rcases hx with hx | hx
    · exact Or.inl (by simpa using hx)
    · exact Or.inr (by simpa using hx)
  have hsq : IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) U.ι V.ι := isPullback_opens_inf U V
  have hab : X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ vU ≫ pushout.inl φU φV =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ vV ≫ pushout.inr φU φV := by
    rw [← Category.assoc, ← Category.assoc, ← cU, ← cV, Category.assoc, Category.assoc, pushout.condition]
  obtain ⟨v, h1, h2⟩ := exists_glue hsq hc _ _ hab
  have hh : φU ≫ qU = φV ≫ qV := eU.trans eV.symm
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV

  have HV : IsPullback vW (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) φV vV := by
    refine IsPullback.of_bot ?_ cV pV
    rw [← Category.assoc, Scheme.homOfLE_ι, eV]; exact pW
  have HU : IsPullback vW (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) φU vU := by
    refine IsPullback.of_bot ?_ cU pU
    rw [← Category.assoc, Scheme.homOfLE_ι, eU]; exact pW
  have e1 (x : U.toScheme) : v (U.ι x) = pushout.inl φU φV (vU x) := congrArg (fun g => g x) h1
  have e2 (x : V.toScheme) : v (V.ι x) = pushout.inr φU φV (vV x) := congrArg (fun g => g x) h2
  refine ⟨pushout φU φV, pushout.desc qU qV hh, v, hF φU φV qU qV hh inferInstance hqU hqV (eU ▸ hqW), ?_⟩
  refine isPullback_of_two (pushout_cover φU φV) (u' := U.ι) (v' := V.ι) (aU := vU) (aV := vV) ?_ ?_ ?_ ?_
  · refine IsOpenImmersion.isPullback _ _ _ _ h1 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e2 x))
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback HV w x hw
        refine ⟨X.homOfLE inf_le_left z, ?_⟩
        exact congrArg (fun g => g z) hsq.w
    · rintro ⟨y, rfl⟩
      exact ⟨vU y, (e1 y).symm⟩
  · refine IsOpenImmersion.isPullback _ _ _ _ h2 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e1 x)).symm
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback HU w x hw
        refine ⟨X.homOfLE inf_le_right z, ?_⟩
        exact (congrArg (fun g => g z) hsq.w).symm
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨vV y, (e2 y).symm⟩
  · simpa only [pushout.inl_desc] using pU
  · simpa only [pushout.inr_desc] using pV

end LateralTheory.E.LeafGlueTwoPf
end
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.LeafClosedSH0PfQuot
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

theorem hensQuot {A C : Type} [CommRing A] [HenselianLocalRing A] [CommRing C] [IsLocalRing C] (g : A →+* C)
    (hg : Function.Surjective g) : HenselianLocalRing C := by
  have hloc : IsLocalHom g := IsLocalHom.of_surjective g hg
  refine { is_henselian := ?_ }
  intro p hp a0 h0 h1
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.mpr (fun n => hg _)) hp
  obtain ⟨b0, rfl⟩ := hg a0
  have e : ∀ (Q : A[X]) (x : A), g (Q.eval x) = (Q.map g).eval (g x) := fun Q x => by
    rw [Polynomial.eval_map, eval₂_at_apply]
  have hb0 : P.eval b0 ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
    have := hu.map g
    rw [e, hPmap] at this
    exact (mem_maximalIdeal _).mp h0 this
  have hb1 : IsUnit ((derivative P).eval b0) := by
    apply (isUnit_map_iff g _).mp
    rw [e, ← derivative_map, hPmap]; exact h1
  obtain ⟨b, hb, hbm⟩ := HenselianLocalRing.is_henselian P hPm b0 hb0 hb1
  refine ⟨g b, ?_, ?_⟩
  · change p.eval (g b) = 0
    rw [← hPmap, ← e, hb.eq_zero, map_zero]
  · rw [← map_sub, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    exact (mem_maximalIdeal _).mp hbm

theorem sepQuot {A C : Type} [CommRing A] [IsLocalRing A] [CommRing C] [IsLocalRing C] (g : A →+* C)
    (hg : Function.Surjective g) [IsLocalHom g] [IsSepClosed (ResidueField A)] : IsSepClosed (ResidueField C) := by
  have hbij : Function.Bijective (ResidueField.map g) := by
    refine ⟨(ResidueField.map g).injective, ?_⟩
    intro y
    obtain ⟨c, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hg c
    exact ⟨residue A a, by simp⟩
  let e := RingEquiv.ofBijective _ hbij
  refine IsSepClosed.of_exists_root _ (fun p _ hirr hsep => ?_)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_eval₂_eq_zero_of_injective (e.symm : ResidueField C →+* ResidueField A)
    e.symm.injective p (degree_pos_of_irreducible hirr).ne' hsep
  refine ⟨e x, ?_⟩
  have h2 := congrArg e hx
  rw [map_zero] at h2
  rw [show (e : ResidueField A → ResidueField C) = (e : ResidueField A →+* ResidueField C) from rfl,
    Polynomial.hom_eval₂, RingEquiv.comp_symm] at h2
  exact h2

theorem shQuot : LeafSHQuot := by
  intro A _ hA W' ι' _
  obtain ⟨hH, hS⟩ := hA
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  let g : CommRingCat.of A ⟶ Γ(W', ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ι'.appTop
  have hg : Function.Surjective g :=
    hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective
  by_cases hC : Nontrivial Γ(W', ⊤)
  · right
    have hLC : IsLocalRing Γ(W', ⊤) := IsLocalRing.of_surjective' g.hom hg
    have hHC := hensQuot g.hom hg
    have : IsLocalHom g.hom := IsLocalHom.of_surjective g.hom hg
    exact ⟨hHC, sepQuot g.hom hg⟩
  · left
    rw [not_nontrivial_iff_subsingleton] at hC
    refine ⟨fun x => ?_⟩
    have h10 : (1 : Γ(W', ⊤)) = 0 := Subsingleton.elim _ _
    have := congrArg (W'.presheaf.germ ⊤ x trivial).hom h10
    rw [map_one, map_zero] at this
    exact one_ne_zero this

end LateralTheory.E.LeafClosedSH0PfQuot
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafClosedSH0PfEmpty
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

theorem emptySec : LeafEmptySec := by
  intro R _ F X hX
  have hb : (⊥ : Sieve X) ∈ Scheme.etaleTopology X := by
    exact Scheme.bot_mem_grothendieckTopology X
  have hT := Sheaf.isTerminalOfBotCover F X hb
  have hZ : IsZero (F.obj.obj (op X)) := hT.isZero
  exact (ModuleCat.isZero_iff_subsingleton.mp hZ)

end LateralTheory.E.LeafClosedSH0PfEmpty
end
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.LeafClosedSH0PfPrim
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

theorem derivUnit {C : Type} [CommRing C] [Nontrivial C] (q : ℕ) (z : C) (hq : IsUnit (q : C))
    (hz : (cyclotomic q C).eval z = 0) : IsUnit ((derivative (cyclotomic q C)).eval z) := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q C
  have hzq : z ^ q = 1 := by
    have := congrArg (eval z) hg
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, hz, zero_mul] at this
    exact sub_eq_zero.mp this
  have hzu : IsUnit z := IsUnit.of_pow_eq_one hzq hq0
  have hd := congrArg (fun p => (derivative p).eval z) hg
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_add, eval_mul,
    eval_C, eval_pow, eval_X, hz, zero_mul, add_zero] at hd
  have hu : IsUnit ((q : C) * z ^ (q - 1)) := hq.mul (hzu.pow _)
  have hu' : IsUnit ((derivative (cyclotomic q C)).eval z * g.eval z) := by
    rw [← hd]; simpa using hu
  exact isUnit_of_mul_isUnit_left hu'

theorem evalHom {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (p : B[X]) (x : B) :
    f (p.eval x) = (p.map f).eval (f x) := by
  rw [Polynomial.eval_map, eval₂_at_apply]

theorem primLift : LeafPrimLift := by
  intro q B C _ _ _ _ f hf ζ
  have hloc : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨z, hqC, hz⟩ := ζ
  have hz' : (cyclotomic q C).eval z = 0 := by
    rw [aeval_def, ← Polynomial.eval_map, map_cyclotomic] at hz; exact hz
  have hqB : IsUnit (q : B) := by
    have : IsUnit (f (q : B)) := by simpa using hqC
    exact (isUnit_map_iff f _).mp this
  obtain ⟨a0, rfl⟩ := hf z
  have hker : (cyclotomic q B).eval a0 ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
    have := hu.map f
    rw [evalHom, map_cyclotomic, hz'] at this
    exact not_isUnit_zero this
  have hder : IsUnit ((derivative (cyclotomic q B)).eval a0) := by
    apply (isUnit_map_iff f _).mp
    rw [evalHom, ← derivative_map, map_cyclotomic]
    exact derivUnit q (f a0) hqC hz'
  have : IsLocalRing C := IsLocalRing.of_surjective' f hf
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian (cyclotomic q B) (cyclotomic.monic q B) a0 hker hder
  have hfa : (cyclotomic q C).eval (f a) = 0 := by
    rw [← map_cyclotomic q f, ← evalHom, ha.eq_zero, map_zero]
  refine ⟨⟨a, hqB, ?_⟩, ?_⟩
  · rw [aeval_def, ← Polynomial.eval_map, map_cyclotomic]; exact ha.eq_zero
  · apply Subtype.ext
    change f a = f a0
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hfa hz' ?_ (derivUnit q (f a) hqC hfa)
    rw [← map_sub, isUnit_map_iff]
    exact (mem_maximalIdeal _).mp ham

end LateralTheory.E.LeafClosedSH0PfPrim
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHSievePf

theorem LeafSHSieve_of : LateralTheory.E.LeafClosedSH0Pf.LeafSHSieve := by
  intro X _ hSH S hS
  obtain ⟨hHens, hSep⟩ := hSH
  let A : Type := Γ(X, ⊤)
  let K : Type := IsLocalRing.ResidueField A
  let π : A →+* K := IsLocalRing.residue A
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  let x : Spec (.of K) ⟶ X := Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber K).jointly_surjective _
    (Scheme.Cover.mem_grothendieckTopology 𝒰) x
  obtain ⟨Z, h, _, ⟨i⟩, rfl⟩ := hg
  have hy' : (y ≫ h) ≫ 𝒰.f i = Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv := by
    exact (Category.assoc _ _ _).trans hy
  obtain ⟨l, ⟨-, hl⟩, -⟩ := GlobalTheory.existsUnique_lift_of_etale_of_henselian (𝒰.f i) π
    IsLocalRing.residue_surjective (y ≫ h) X.isoSpec.inv hy'
  have hmem : S (𝒰.f i) := hle _ _ (Presieve.ofArrows.mk i)
  have := S.downward_closed hmem (X.isoSpec.hom ≫ l)
  have e : (X.isoSpec.hom ≫ l) ≫ 𝒰.f i = 𝟙 X := by rw [Category.assoc, hl, Iso.hom_inv_id]
  rwa [e] at this

end LateralTheory.E.LeafSHSievePf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocSplitPfM

theorem iso_inv_mono' {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) : Mono e.inv := inferInstance

theorem resι_mono {R : Type} [CommRing R] (F : Shv R) : Mono (resι R F) := by
  unfold resι
  rw [InjectiveResolution.ι'_f_zero]
  have h0 : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  exact @mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ h0 _ (iso_inv_mono' _)))

theorem sec_inj {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (fun x : Sec F U => Sec.map φ x) := by
  have h1 : Mono ((sheafToPresheaf _ _).map φ) := inferInstance
  have h2 : Mono (((sheafToPresheaf _ _).map φ).app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 h2

def LeafTw0TwFree : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)),
  twGen 0 ζ = 0 ∨ ∀ c : ULift.{1} (ZMod q), c • twGen 0 ζ = 0 → c = 0

theorem LeafTw0GenFree_of (h : LeafTw0TwFree) : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0GenFree := by
  intro q _ V ζ
  rcases h q V ζ with h0 | h1
  · exact Or.inl h0
  · right
    intro c hc
    apply h1 c
    have : Mono (resι (ZMod q) (tw q 0)) := resι_mono _
    apply sec_inj (resι (ZMod q) (tw q 0)) V
    show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = Sec.map (resι (ZMod q) (tw q 0)) 0
    rw [show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = c • resGen 0 ζ from
      map_smul ((resι (ZMod q) (tw q 0)).hom.app (op V)).hom c _, hc]
    simp [Sec.map]

end LateralTheory.E.LeafTw0LocSplitPfM
end
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut
theorem LateralTheory.E.TruncationCokernelLevelRelations.TruncCok_of (hD : LateralTheory.E.TruncationKernel.RelDesc) : LateralTheory.E.DescLocPf.Fine.TruncCok := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' m hm y ⟨x, hx⟩
  have hinj := hD hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo'
  refine LateralTheory.E.KernelLocalization.range_of_bd _ _ _ m n (by omega) y ((injective_iff_map_eq_zero _).1 hinj _ ?_)
  refine (LateralTheory.E.KernelLocalization.rpull_bd ..).trans ?_
  rw [← hx]
  exact LateralTheory.E.KernelLocalization.bd_pull ..
theorem LateralTheory.E.TruncationCokernelLevelRelations.LvlRel_of : LateralTheory.E.FiltrationLevelInjectivity.LvlRel := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' p _ m hm
  have h := LateralTheory.E.LevelsPf.Tp.Levels_of' LateralTheory.E.CechLevelIsoPf.CechLevelIso_of hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE p m hm
  exact ⟨h.2, h.1 (m - 1) (by omega)⟩
end
