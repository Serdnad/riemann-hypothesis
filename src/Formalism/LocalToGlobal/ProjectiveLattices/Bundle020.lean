module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle019
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cjFin (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
  Units.map (Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.conjF).toRingHom.toMonoidHom

def XiTilde (xi δ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop := ∀ x, xi (x / cjFin D x) = δ x

end Formalism.L2.Pj
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem gfp_chart_iso {R : Type} [CommRing R] {G₁ G₂ : Over (Spec (CommRingCat.of R))} [GrpObj G₁] [GrpObj G₂]
    (e : G₁ ≅ G₂) [IsMonHom e.hom] {n : ℕ}
    {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R)
      (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ G₁} (hx : IsUnivChart G₁ n xc) :
    IsUnivChart G₂ n (fun m => xc m ≫ e.hom) := by
  have h1 : ∀ X : Over (Spec (CommRingCat.of R)), (1 : X ⟶ G₁) ≫ e.hom = 1 := by
    intro X
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  refine ⟨fun m => ?_, fun m => ?_, ?_⟩
  · rw [← Category.assoc, hx.1 m]
  · rw [← Category.assoc, hx.2.1 m, h1]
  · intro A _ _ aug m hker y hy
    have hy' : ReciprocityTheory.ChartRestriction.G.Chart.spMap aug ≫ (y ≫ e.inv) = 1 := by
      rw [← Category.assoc, hy, ← h1, Category.assoc, e.hom_inv_id, Category.comp_id]
    obtain ⟨ψ, hψ, huniq⟩ := hx.2.2 A aug m hker (y ≫ e.inv) hy'
    refine ⟨ψ, ⟨hψ.1, ?_⟩, fun ψ' hψ' => huniq ψ' ⟨hψ'.1, ?_⟩⟩
    · rw [← Category.assoc, ← Iso.comp_inv_eq, hψ.2]
    · rw [Iso.comp_inv_eq, hψ'.2, Category.assoc]

def gfpEig {L : Type} [Field L] [Algebra c.F L] {x : Sp L ⟶ Xo.X} {n : ℕ}
    {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L)
      (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
    (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) : Submodule L (Fin n → L) :=
  eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) (fun a => algebraMap c.F L (embK c τ a))

section BC

variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L)
      (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}

theorem gfpVec_tmap (hx : IsUnivChart _ n xc) (a : 𝓞 E) (cc : Fin n → L) :
    gfpVec x xc (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      gfpVec x xc cc ≫ (Xo.univ.t.act.act a).left := by
  have ht : tvec (x := xc) (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      tvec (x := xc) cc ≫ (Over.pullback x).map (Xo.univ.t.act.act a) := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx _ cc
    | exact (ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx _ cc).symm
    | exact (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx
        (tvec (x := xc) cc ≫ (Over.pullback x).map (Xo.univ.t.act.act a)) _).symm
  have e1 : ((Over.pullback x).map (Xo.univ.t.act.act a)).left ≫ pullback.fst Xo.univ.t.G.hom x =
      pullback.fst Xo.univ.t.G.hom x ≫ (Xo.univ.t.act.act a).left := by
    simp
    all_goals first
    | exact pullback.lift_fst _ _ _
    | erw [pullback.lift_fst]
    | (rw [limit.lift_π]; rfl)
  simp only [gfpVec, ht, Over.comp_left, Category.assoc, e1]

theorem gfp_bc {L' : Type} [Field L'] [Algebra L L'] (hx : IsUnivChart _ n xc) :
    ∃ (xc' : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L')
      (ReciprocityTheory.ChartRestriction.G.Chart.JetR L' (Fin n) m) ⟶
        (Over.pullback (spMap (algebraMap L L') ≫ x)).obj Xo.univ.t.G) (hx' : IsUnivChart _ n xc'),
      (∀ cc : Fin n → L, gfpVec (spMap (algebraMap L L') ≫ x) xc' (algebraMap L L' ∘ cc) =
        spMap (dualMap (algebraMap L L')) ≫ gfpVec x xc cc) ∧
      ∀ (a : 𝓞 E) (cc : Fin n → L),
        tmap hx' ((Over.pullback (spMap (algebraMap L L') ≫ x)).map (Xo.univ.t.act.act a)) (algebraMap L L' ∘ cc) =
          algebraMap L L' ∘ tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc := by
  obtain ⟨x₁, hx₁, hcomp⟩ := ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := L) (R' := L') _ n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj Xo.univ.t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB L L'))
    (isGrpPullback_pullback Xo.univ.t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback Xo.univ.t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB L L' ≫ x))
  have hv : ∀ cc : Fin n → L, gfpVec (spMap (algebraMap L L') ≫ x) (fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc) =
      spMap (dualMap (algebraMap L L')) ≫ gfpVec x xc cc := by
    intro cc
    have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left =
        (tvec (x := x₁) (algebraMap L L' ∘ cc)).left ≫ e.hom.left := by
      show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
      rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
    show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left ≫ pullback.fst _ _ = _
    rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
    rfl
  have hx' := gfp_chart_iso e hx₁
  refine ⟨fun m => x₁ m ≫ e.hom, hx', hv, fun a cc => gfp_inj hx' ?_⟩
  rw [gfpVec_tmap hx', hv, hv, gfpVec_tmap hx, Category.assoc]

variable [Algebra c.F L]

theorem gfp_finrank (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) :
    Module.finrank L (gfpEig (c := c) hx τ) = Dw.mult τ := by
  classical
  obtain ⟨xc', hx', -, htm⟩ := gfp_bc (L' := AlgebraicClosure L) hx
  have hrank := ReciprocityTheory.ChartRestriction.G.Chart.finrank_eig_bc (V := L) (k := AlgebraicClosure L)
    (fun a => tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)))
    (fun a => tmap hx' ((Over.pullback (spMap (algebraMap L (AlgebraicClosure L)) ≫ x)).map (Xo.univ.t.act.act a)))
    htm (fun a => algebraMap c.F L (embK c τ a))
  let β : KA l →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp
    ((algebraMap c.F L).comp (IntermediateField.inclusion c.le).toRingHom)
  have hβ : (spMap (algebraMap L (AlgebraicClosure L)) ≫ x) ≫ Xo.s = spMap β := by
    rw [Category.assoc, hx0]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hd := (Xo.univ.geom (AlgebraicClosure L) _ β hβ).1
  let τ' : 𝓞 E →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp ((algebraMap c.F L).comp (embK c τ))
  have key : ∀ N, LieMult Xo.univ.t.act (spMap (algebraMap L (AlgebraicClosure L)) ≫ x) τ' N →
      Module.finrank (AlgebraicClosure L) (eigLat hx'
        (fun a => (Over.pullback (spMap (algebraMap L (AlgebraicClosure L)) ≫ x)).map (Xo.univ.t.act.act a))
        (fun a => τ' a)) = N :=
    fun N h => ReciprocityTheory.ChartRestriction.G.Chart.finrank_of_lieMult gfp_hcId (Category.comp_id _) hx' Xo.univ.t.act
      Xo.univ.t.act.act (fun a => by rw [Category.comp_id, Category.id_comp]) _ (fun a => rfl) τ' h
  have hinj : Function.Injective ((algebraMap L (AlgebraicClosure L)).comp (algebraMap c.F L)) := RingHom.injective _
  have e0 : τ' H.rt = β (baseKA l).ρ ↔ τ (H.rt : E) = H.rt0 := by
    constructor
    · intro h
      have h' := @hinj (embK c τ H.rt) (IntermediateField.inclusion c.le (baseKA l).ρ) h
      exact congrArg (fun z : c.F => (z : ℂ)) h'
    · intro h
      have h' : embK c τ H.rt = IntermediateField.inclusion c.le (baseKA l).ρ := Subtype.ext h
      exact congrArg ((algebraMap L (AlgebraicClosure L)).comp (algebraMap c.F L)) h'
  refine hrank.trans ?_
  unfold Datum.mult
  split_ifs with h
  · exact key _ ((hd τ').1 (e0.2 h))
  · exact key _ ((hd τ').2 (fun h' => h (e0.1 h')))

theorem gfp_basis (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ)
    (d : Fin (Dw.mult τ) → Fin n → L) (hd : LinearIndependent L d) (hdW : ∀ i, d i ∈ gfpEig (c := c) hx τ)
    (w : Sp (DualNumber L) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) (he : IsEigAt c τ w) :
    ∃! a : Fin (Dw.mult τ) → L, IsCombAt x (fun i => gfpVec x xc (d i)) a w := by
  obtain ⟨cc, rfl⟩ := gfp_exists hx w hw
  have hcc : cc ∈ gfpEig (c := c) hx τ := (gfp_eig_iff hx τ cc).1 he
  have hle : Submodule.span L (Set.range d) ≤ gfpEig (c := c) hx τ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hdW i
  have hfr : Module.finrank L (Submodule.span L (Set.range d)) =
      Module.finrank L (gfpEig (c := c) hx τ) := by
    rw [finrank_span_eq_card hd, Fintype.card_fin, gfp_finrank hx0 hx τ]
  have heq : Submodule.span L (Set.range d) = gfpEig (c := c) hx τ :=
    Submodule.eq_of_le_of_finrank_eq hle hfr
  have hspan : cc ∈ Submodule.span L (Set.range d) := heq ▸ hcc
  obtain ⟨a, ha⟩ : ∃ a : Fin (Dw.mult τ) → L, ∑ i, a i • d i = cc := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun L).1 hspan
    | exact Submodule.mem_span_range_iff_exists_fun.1 hspan
  refine ⟨a, (gfp_comb_iff hx d a cc).2 ha.symm, ?_⟩
  intro a' ha'
  have h2 : cc = ∑ j, a' j • d j := (gfp_comb_iff hx d a' cc).1 ha'
  have h3 : ∑ j, a' j • d j = ∑ j, a j • d j := h2.symm.trans ha.symm
  funext i
  have h4 := Fintype.linearIndependent_iff.1 hd (a' - a) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h3, sub_self]) i
  simpa [sub_eq_zero] using h4

end BC

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def KapFG : Prop := ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (kap Z)).FG

def KapTrdeg (d : ℕ) : Prop := ∀ Z : Comp Xo c, Algebra.trdeg c.F (kap Z) = d

theorem fnFG_of (h : KapFG Xo c) : FnFG Xo c := by
  intro Z
  classical
  obtain ⟨s, hs⟩ := h Z
  have hfin : (Set.range fun i : FlagVar Dw =>
      algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) (MvPolynomial.X i)).Finite := Set.finite_range _
  refine ⟨s.image (algebraMap (kap Z) (Om Z)) ∪ hfin.toFinset, ?_⟩
  set K := IntermediateField.adjoin c.F
    ((s.image (algebraMap (kap Z) (Om Z)) ∪ hfin.toFinset : Finset (Om Z)) : Set (Om Z)) with hK
  have hC : ∀ a : kap Z, algebraMap (kap Z) (Om Z) a ∈ K := by
    intro a
    have ha : a ∈ IntermediateField.adjoin c.F (s : Set (kap Z)) := by
      rw [hs]
      exact IntermediateField.mem_top
    have h1 : IsScalarTower.toAlgHom c.F (kap Z) (Om Z) a ∈
        (IntermediateField.adjoin c.F (s : Set (kap Z))).map (IsScalarTower.toAlgHom c.F (kap Z) (Om Z)) :=
      by
        first
          | exact ⟨a, ha, rfl⟩
          | (rw [← SetLike.mem_coe, IntermediateField.coe_map]; exact Set.mem_image_of_mem _ ha)
    rw [IntermediateField.adjoin_map] at h1
    refine IntermediateField.adjoin.mono _ _ _ ?_ h1
    rintro _ ⟨b, hb, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
  have hP : ∀ q : MvPolynomial (FlagVar Dw) (kap Z),
      algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) q ∈ K := by
    intro q
    induction q using MvPolynomial.induction_on
    next a =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hC a
    next p₁ p₂ h₁ h₂ =>
      rw [map_add (f := _)]
      exact K.add_mem h₁ h₂
    next p₁ i h₁ =>
      rw [map_mul]
      refine K.mul_mem h₁ (IntermediateField.subset_adjoin c.F _ ?_)
      exact Finset.mem_coe.mpr (Finset.mem_union_right _ (hfin.mem_toFinset.mpr ⟨i, rfl⟩))
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨p₁, p₂⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (MvPolynomial (FlagVar Dw) (kap Z))) x
  dsimp only
  rw [IsFractionRing.mk'_eq_div]
  exact K.div_mem (hP p₁) (hP p₂)

private lemma isAlgebraic_frac_lemma {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (x : K) : IsAlgebraic A x := by
  obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) x
  dsimp only
  have hq : algebraMap A K (q : A) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors q.2
  refine ⟨Polynomial.C (q : A) * Polynomial.X - Polynomial.C p, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun f : Polynomial A => f.coeff 1) h0
    simp at h1
    try exact nonZeroDivisors.ne_zero q.2 h1
  · rw [IsFractionRing.mk'_eq_div]
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [mul_div_cancel₀ _ hq, sub_self]

theorem fnTrdeg_of (d : ℕ) (h : KapTrdeg Xo c d) : FnTrdeg Xo c (d + Nat.card (FlagVar Dw)) := by
  intro Z
  haveI h1 : FaithfulSMul (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (kap Z) (MvPolynomial (FlagVar Dw) (kap Z))).injective
  haveI h2 : FaithfulSMul (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z))
  haveI h3 : FaithfulSMul c.F (kap Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap c.F (kap Z)).injective
  haveI h4 : FaithfulSMul (kap Z) (Om Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap (kap Z) (Om Z)).injective
  have e1 : Algebra.trdeg (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) = Cardinal.mk (FlagVar Dw) := by
    first
      | (rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id])
      | (rw [Algebra.trdeg_mvPolynomial, Cardinal.lift_id])
      | (rw [MvPolynomial.trdeg_eq, Cardinal.lift_id])
      | (rw [MvPolynomial.lift_trdeg, Cardinal.lift_id])
      | (rw [Algebra.trdeg_MvPolynomial, Cardinal.lift_id])
      | (rw [MvPolynomial.trdeg_eq_cardinalMk, Cardinal.lift_id])
  have e2 : Algebra.trdeg (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) = 0 := by
    unfold Algebra.trdeg
    refine le_antisymm (ciSup_le' fun s => ?_) zero_le
    refine (Cardinal.mk_eq_zero_iff.mpr ⟨fun x => ?_⟩).le
    exact s.2.transcendental x (isAlgebraic_frac_lemma _)
  have hcard : Cardinal.mk (FlagVar Dw) = ((Nat.card (FlagVar Dw) : ℕ) : Cardinal) := by
    first
      | exact Nat.cast_card.symm
      | simp [Cardinal.mk_fintype, Nat.card_eq_fintype_card]
  have T1 := lift_trdeg_add_eq (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z)
  have T2 := lift_trdeg_add_eq c.F (kap Z) (Om Z)
  simp only [Cardinal.lift_id] at T1 T2
  show Algebra.trdeg c.F (Om Z) = ((d + Nat.card (FlagVar Dw) : ℕ) : Cardinal)
  rw [← T2, h Z, ← T1, e1, e2, add_zero, hcard, Nat.cast_add]

end Formalism.L2.Pj

end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]


variable (Xo c) in
def supR (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : Rul Xo c) : ℝ :=
  supAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f


variable (Xo c) in
def SupBdd (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    Prop :=
  ∀ σ, BddAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f


variable (Xo c) in
def PTNe : Prop := ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), (PT (Ω := Om Z) σ).Nonempty

theorem ptNe_of_fnFG (hfg : FnFG Xo c) : PTNe Xo c := fun Z σ => exists_embedding_over (hfg Z) σ

def ValAtCx (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ‖P (evC h Z f)‖ = cabs (evR Xo c f (yP Z P))

def NZSome (h : GenFrEx Xo c) (f : Rul Xo c) : Prop := ∃ Z, evC h Z f ≠ 0

section Pf

variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

theorem meanK_mono' {K : Type} [Field K] [NumberField K] {F G : (K →+* ℂ) → ℝ} (hFG : ∀ sg, F sg ≤ G sg) :
    meanK F ≤ meanK G := by
  unfold meanK
  gcongr with sg _
  exact hFG sg

theorem exZ_wtZ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (i : Ix Dw) : exZ Dw (wtZ a n) i = (ex Dw a n i : ℤ) := by
  cases i <;> rfl

theorem nrmC_valC_le (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (Z : Comp Xo c) (P : Om Z →+* ℂ) :
    nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P ≤ supR Xo c fn (sgOf P) a n f := by
  have hb := hB (sgOf P)
  unfold BddAt at hb
  have hle := le_ciSup hb (yP Z P)
  have hc : (valC h a n f Z).coeff (wtZ a n) = evC h Z f := by
    unfold valC
    simp
  have heq : nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P =
      ptNorm (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
    unfold nrmC ptNorm
    rw [hc, hcx Z P a n f hS]
    simp only [exZ_wtZ, zpow_neg, zpow_natCast, inv_pow] <;> rfl
  rw [heq]
  exact hle

theorem log_supN_le (hfn : FnNe Xo c fn) (hPT : PTNe Xo c) (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (hN : NZSome h f) (σ : c.F →+* ℂ) :
    Real.log (⨆ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ), nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) ≤
      Real.log (supR Xo c fn σ a n f) := by
  have hbd : ∀ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ),
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2 ≤ supR Xo c fn σ a n f := by
    rintro ⟨Z, P, hP⟩
    have hσ : sgOf P = σ := hP
    have key := nrmC_valC_le (h := h) (yP := yP) hcx hS hB Z P
    rw [hσ] at key
    exact key
  obtain ⟨Z0, hZ0⟩ := hN
  obtain ⟨P0, hP0⟩ := hPT Z0 σ
  have hpos : 0 < nrmC fn (yP Z0) (wtZ a n) (valC h a n f Z0) P0 := by
    have hc : (valC h a n f Z0).coeff (wtZ a n) = evC h Z0 f := by
      unfold valC
      simp
    unfold nrmC
    rw [hc]
    apply mul_pos
    · exact norm_pos_iff.mpr ((map_ne_zero P0).mpr hZ0)
    · apply Finset.prod_pos
      intro i _
      exact zpow_pos (abs_pos.mpr (hfn _ _ i)) _
  have hne : Nonempty (Σ Z : Comp Xo c, PT (Ω := Om Z) σ) := ⟨⟨Z0, P0, hP0⟩⟩
  have hB' : BddAbove (Set.range fun p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ) =>
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) := ⟨_, Set.forall_mem_range.mpr hbd⟩
  apply Real.log_le_log
  · exact lt_of_lt_of_le hpos (le_ciSup hB' ⟨Z0, P0, hP0⟩)
  · exact ciSup_le hbd

end Pf

end Formalism.L2.Pj
end
end
