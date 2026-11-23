module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenDiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenRank
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

theorem appTop_specMap {R S : CommRingCat} (g : R ⟶ S) (r : Γ(Spec R, ⊤)) :
    (Spec.map g).appTop.hom r = (Scheme.ΓSpecIso S).inv.hom (g.hom ((Scheme.ΓSpecIso R).hom.hom r)) := by
  have e := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_naturality g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [← e]
  simp

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

abbrev TO : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (fO v hϖ hv)))

abbrev ιS : TF (R := V) F ⟶ TO hϖ hv :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ Spec.map (CommRingCat.ofHom (fO v hϖ hv)) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫ Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fO_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

abbrev jO : DegPre.BF D.toPre F ⟶ TO hϖ hv ⊗ D.toPre.P.A := ιS hϖ hv ▷ D.toPre.P.A

theorem jO_snd : (jO hϖ hv (D := D)).left ≫ (snd (TO hϖ hv) D.toPre.P.A).left = (DegPre.prB D.toPre F).left := by
  rw [← Over.comp_left, whiskerRight_snd]

theorem jO_fst : (jO hϖ hv (D := D)).left ≫ (fst (TO hϖ hv) D.toPre.P.A).left =
    (fst (TF (R := V) F) D.toPre.P.A).left ≫ (ιS hϖ hv).left := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

abbrev ιr (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) : F :=
  algebraMap (Ov v) F ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom r)

theorem v_ιr (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) : (0 : WithTop ℚ) ≤ v (ιr (v := v) r) := v_nonneg v _

theorem gs_jO {Z : Scheme.{0}} (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) :
    gs (ρ ≫ (jO hϖ hv (D := D)).left) z ⊤ ((fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom r) =
      gs ρ z ⊤ (gF D.toPre F (ιr (v := v) r)) := by
  have e1 : gs (ρ ≫ (jO hϖ hv (D := D)).left) z ⊤ ((fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom r) =
      gs ((ρ ≫ (jO hϖ hv (D := D)).left) ≫ (fst (TO hϖ hv) D.toPre.P.A).left) z ⊤ r := gs_pull _ _ z ⊤ trivial r
  rw [e1, Category.assoc, jO_fst, ← Category.assoc]
  have e2 : gs ((ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ (ιS hϖ hv).left) z ⊤ r =
      gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤ ((ιS hϖ hv).left.appTop.hom r) := (gs_pull _ _ z ⊤ trivial r).symm
  have e3 : gs ρ z ⊤ (gF D.toPre F (ιr (v := v) r)) = gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (ιr (v := v) r)) := gs_pull _ _ z ⊤ trivial _
  rw [e2, e3, show (ιS hϖ hv).left = Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) from rfl, appTop_specMap]
  rfl

theorem vge_moveO (hTW : TwistBCSpanStatement) {k : ℕ} (hk : 1 ≤ k) {α χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    {s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))}
    {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hfst : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    {H : (TO hϖ hv ⊗ D.toPre.P.A).left ⟶ (TO hϖ hv ⊗ D.toPre.P.A).left}
    (hh : h ≫ (jO hϖ hv (D := D)).left = (jO hϖ hv).left ≫ H)
    {K₃ K₄ : Type} [Fintype K₃] [Fintype K₄]
    {φ₃ : K₃ → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb D.toPre.P.L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s'
      (DegPre.famφ D.toPre F α) (DegPre.famε k) s h φ₃ ε₃ u)
    {ψ : K₄ → ((TO hϖ hv ⊗ D.toPre.P.A).left ⟶ D.toPre.P.A.left)} {δ : K₄ → ℤ}
    (eO : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)) (heO : eO.IsGen)
    (hform : FormEq (Sum.elim (fun i => (H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) ≫ D.toPre.famφB α i) ψ)
      (Sum.elim (DegPre.famε k) δ) (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB χ i) (DegPre.famε k))
    (c : F)
    (hc : ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) * (val eO (jO hϖ hv).left y J).val)
    {r q : ℚ} (hq : ((q : ℚ) : WithTop ℚ) ≤ v c) (hs : VGe D F v k α s r) : VGe D F v k χ s' (r + q) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  have e1 : ∀ i, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L
      (fun j => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB χ j) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (TO hϖ hv ⊗ D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (σ i) (ρ ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) z J * (val eO ρ z J).val := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hform (pullMulSec (σ i) (H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) eO heO)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ heO ρ z hJ)⟩
  choose S hS using e1
  have e2 := fun i => hTW V D.toPre k hk χ (Ov v) (fO v hϖ hv) inferInstance (S i)
  choose m rr σ' hsp using e2
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F χ) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  have e3 : ∀ (i : Fin n) (l : Fin (m i)), ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (σ' i l) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun i l => by
    obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ (σ' i l) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullSec _ _ _ _ ρ z hJ)⟩
  choose σ'F hσ'F using e3
  let eqv := (finSigmaFinEquiv (n := m)).symm
  let co : Fin (∑ i, m i) → F := fun t => c * a (eqv t).1 * ιr (v := v) (rr (eqv t).1 (eqv t).2)
  have hprB : h ≫ (DegPre.prB D.toPre F).left = (jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left := by
    rw [← jO_snd hϖ hv, ← Category.assoc, hh, Category.assoc]

  have CORE : ∀ (y : (DegPre.BF D.toPre F).left) (I), Good D.toPre.P.L y I →
      sval s' (𝟙 _) y I = ∑ t, gs (𝟙 _) y ⊤ (gF D.toPre F (co t)) * sval (σ'F (eqv t).1 (eqv t).2) (𝟙 _) y I := by
    intro y I hIy
    have H1 := (secRel_iff hL _ _ s' _ _ s h _ _ u).1 hrel _ (𝟙 _) y I hIy
    have H2 := sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) (𝟙 _ ≫ h) y hIy
    rw [H1, H2, hc y I hIy, Finset.sum_mul]
    rw [← (Equiv.sum_comp eqv.symm _), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have A1 : gs (𝟙 _ ≫ h) y ⊤ (gF D.toPre F (a i)) = gs (𝟙 _) y ⊤ (gF D.toPre F (a i)) := by
      rw [Category.id_comp]; exact gs_gF_comp hfst y (a i)
    have A2 : sval (σF i) (𝟙 _ ≫ h) y I = sval (σ i) ((jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) y I := by
      rw [← secScal_sval (hscal i) (𝟙 _ ≫ h) y hIy, Category.assoc, hprB, Category.id_comp]
    have A3 := hS i _ (jO hϖ hv).left y I hIy
    have A4 := sval_lin (fun l => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (rr i l))
      (fun l => pullSec D.toPre.P.L _ _ (σ' i l) (snd (TO hϖ hv) D.toPre.P.A).left) (fun j => hsp i j)
      (jO hϖ hv).left y hIy
    rw [A1, A2]
    have A5 : sval (σ i) ((jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) y I *
        (val eO (jO hϖ hv).left y I).val = ∑ l, gs (𝟙 _) y ⊤ (gF D.toPre F (ιr (v := v) (rr i l))) *
          sval (σ'F i l) (𝟙 _) y I := by
      rw [← A3, A4]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [sval_pullSec _ _ _ _ _ y hIy, jO_snd, hσ'F i l _ (𝟙 _) y I hIy, Category.id_comp]
      congr 1
      have := gs_jO hϖ hv (D := D) (𝟙 _) y (rr i l)
      rwa [Category.id_comp] at this
    calc _ = gs (𝟙 _) y ⊤ (gF D.toPre F (a i)) * gs (𝟙 _) y ⊤ (gF D.toPre F c) *
          (sval (σ i) ((jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) y I *
            (val eO (jO hϖ hv).left y I).val) := by ring
      _ = _ := by
        rw [A5, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [co, eqv, Equiv.symm_symm, map_mul]
        rw [show finSigmaFinEquiv.symm (finSigmaFinEquiv (⟨i, l⟩ : (i : Fin n) × Fin (m i))) = ⟨i, l⟩ from
          Equiv.symm_apply_apply _ _, gs_mul _ y ⊤ trivial, gs_mul _ y ⊤ trivial]
        ring
  refine ⟨∑ i, m i, co, fun t => σ' (eqv t).1 (eqv t).2, fun t => σ'F (eqv t).1 (eqv t).2, fun t => ?_, fun t => ?_,
    fun j => ?_⟩
  · exact secScal_of_sval hL fun y J hJ => (hσ'F _ _ _ (𝟙 _) y J hJ).symm
  · show ((r + q : ℚ) : WithTop ℚ) ≤ v (c * a (eqv t).1 * ιr (v := v) (rr (eqv t).1 (eqv t).2))
    rw [AddValuation.map_mul, AddValuation.map_mul, WithTop.coe_add]
    calc ((r : ℚ) : WithTop ℚ) + (q : WithTop ℚ) = (q : WithTop ℚ) + (r : WithTop ℚ) + 0 := by
          rw [add_zero, add_comm]
      _ ≤ _ := add_le_add (add_le_add hq (hva _)) (v_ιr _)
  · show s'.f j = ∑ t, resTop _ (gF D.toPre F (co t)) * (σ'F (eqv t).1 (eqv t).2).f j
    refine fn_ext fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart hL (ψ y)
    have hIy : Good D.toPre.P.L y I := hI
    have mm := hIy.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    have hy' : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j := hy
    have T0 := sec_trans s' (𝟙 _) y hy' mm
    set τ := (Geo.Tor.trF (DegPre.famφ D.toPre F χ) (DegPre.famε k) (𝟙 _) y j
      (fun k => I (𝟙 _ ≫ DegPre.famφ D.toPre F χ k))).val with hτ
    have RHS : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (∑ t, resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (co t)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from
            (σ'F (eqv t).1 (eqv t).2).f j)) =
        τ * ∑ t, gs (𝟙 _) y ⊤ (gF D.toPre F (co t)) * sval (σ'F (eqv t).1 (eqv t).2) (𝟙 _) y I := by
      rw [gs_sum _ y _ hy', Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have S1 : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
          (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (co t))) =
          gs (𝟙 _) y ⊤ (gF D.toPre F (co t)) := gs_res _ y le_top hy' _
      rw [gs_mul _ y _ hy', S1, sec_trans (σ'F (eqv t).1 (eqv t).2) (𝟙 _) y hy' mm, hτ]
      exact mul_left_comm _ _ _
    exact T0.trans ((congrArg (fun x => τ * x) (CORE y I hIy)).trans RHS.symm)

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section FamPr

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D' D : DegPre R}

theorem famφB_pr (pD : IsPowDeg D' D j) (α' : D'.X) (i : Fin j) (a : Fin 4) :
    D'.famφB α' a ≫ (pD.pw.pr i).left = (pD.pw.pr i).left ≫ D.famφB (pD.xe α' i) a := by
  haveI := pD.pw.hom i
  have hc := pD.c_pr α' i
  fin_cases a <;>
    simp [DegPre.famφB, ← Over.comp_left, padd, hc, IsMonHom.mul_hom, IsMonHom.one_hom]
  all_goals
    first
    | (rw [← Over.comp_left]; congr 1;
        simp [CartesianMonoidalCategory.comp_lift_assoc, CartesianMonoidalCategory.comp_lift, hc,
          IsMonHom.mul_hom, CartesianMonoidalCategory.comp_toUnit_assoc])
    | (congr 1; simp [CartesianMonoidalCategory.comp_lift_assoc, CartesianMonoidalCategory.comp_lift, hc,
          IsMonHom.mul_hom, CartesianMonoidalCategory.comp_toUnit_assoc])

def boxFamB (pD : IsPowDeg D' D j) (k : ℕ) (f : Fin j → ∀ α : D.X, D.SecB k α) (α' : D'.X) : D'.SecB k α' :=
  secOfIso (u := LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i)))
    (linCombIso_isGen pD.w pD.w_gen _ _) (linComb_isLB _ D'.P.isLB _ _)
    (linComb_isLB _ (linComb_isLB _ D.P.isLB _ _) _ _)

theorem isBoxFamB_boxFamB (pD : IsPowDeg D' D j) (k : ℕ) (f : Fin j → ∀ α : D.X, D.SecB k α) :
    IsBoxFamB pD k (boxFamB pD k f) f := by
  intro α'
  refine ⟨famφB_pr pD α', fun jN jM => ?_⟩
  set V := LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN ⊓ LB.wchart D'.P.L (D'.famφB α') jM with hVdef
  have hVab : V ≤ LB.wchart D'.P.L (D'.famφB α') jM ⊓ LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN :=
    fun _ hy => ⟨hy.2, hy.1⟩
  have hspec := congrArg (rs hVab) (secOfIso_spec (u := LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i)))
    (linCombIso_isGen pD.w pD.w_gen _ _) (linComb_isLB _ D'.P.isLB _ _)
    (linComb_isLB _ (linComb_isLB _ D.P.isLB _ _) _ _) jM jN)
  erw [rs_rs] at hspec
  have hspec2 := hspec.trans (isoCand_rs (LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i))) jM jN hVab)
  have hVd : V ≤ (LB.div (LB.LinComb (boxLB D.P.L pD.pw.pr) (D'.famφB α') (DegPre.famε k))
      (LB.LinComb D'.P.L (D'.famφB α') (DegPre.famε k))).U (jN, jM) := fun _ hy => ⟨hy.1, hy.2⟩
  have hu : res hVd ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM)) =
      @id (Γ(D'.P.A.left, V)ˣ) ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM)) :=
    res_refl' _
  have key := unit_cancel _ _ _ _ hspec2 hu
  refine key.trans ?_
  simp only [boxSecGen, boxSecGenF]
  refine (map_prod ((D'.P.A.left.presheaf.map (homOfLE _).op).hom) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact rs_rs _ _ _

end FamPr

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]



theorem leading_expansion_term_ne_zero [IsDiscreteValuationRing R] (hI : I = maximalIdeal R) (U : Unif I D A G) (s : H0 U.LG.L 1)
    (hs : NonzeroOnSpecial U s) (g : ∀ α, D.toPre.SecB 1 α) (hexp : U.ExpandsAt 0 1 s g)
    (hv : ∀ mu, mu ≠ 0 → ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((g mu).f j) = 0) :
    ¬ ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((g 0).f j) = 0 := by
  intro h0
  subst hI

  have hloc : ∀ {X : Scheme.{0}} {W : X.Opens} (y : Γ(X, W)),
      (∀ x ∈ W, ∃ V : X.Opens, ∃ hV : V ≤ W, x ∈ V ∧ (X.presheaf.map (homOfLE hV).op).hom y = 0) →
        y = 0 := by
    intro X W y h
    choose V hV hxV hy using h
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun p : W => V p.1 p.2) W
      (fun p => homOfLE (hV p.1 p.2)) ?_ y 0 ?_
    · intro x hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩
    · intro p
      exact (hy p.1 p.2).trans (map_zero _).symm

  have hvan : ∀ (α : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι),
      ((U.gt 0).pG.left.app (D.toPre.P.L.wchart (D.toPre.famφB α) j)).hom ((g α).f j) = 0 := by
    intro α j
    have hz : ((pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).app
        ((D.toPre.P.L.LinComb (D.toPre.famφB α) (DegPre.famε 1)).U j)).hom ((g α).f j) = 0 := by
      by_cases hα : α = 0
      · subst hα
        exact h0 j
      · exact hv α hα j
    show (((U.gt 0).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).app
        ((D.toPre.P.L.LinComb (D.toPre.famφB α) (DegPre.famε 1)).U j)).hom ((g α).f j) = 0
    try rw [Scheme.comp_app]
    exact (congrArg (fun z => ((U.gt 0).q.left.app _).hom z) hz).trans (map_zero _)
  unfold NonzeroOnSpecial at hs
  obtain ⟨j, hj⟩ := hs
  obtain ⟨S, -, hS⟩ := hexp
  choose ch hch using fun y : D.toPre.P.A.left => WeightPf.exists_chart D.toPre.P.L D.toPre.P.isLB y
  apply hj
  refine hloc _ fun x hx => ?_
  refine ⟨U.expW 0 (fun _ => ch ((U.gt 0).pG.left.base x), fun _ => j 0) j S
      (fun α i => ch (((U.gt 0).pG.left ≫ D.toPre.famφB α i).base x))
      (fun α i => ch ((D.toPre.Oφ (U.gt 0).pG α i).base x)),
    inf_le_left.trans inf_le_right, ?_, ?_⟩
  · refine TopologicalSpace.Opens.mem_inf.mpr ⟨TopologicalSpace.Opens.mem_inf.mpr
      ⟨TopologicalSpace.Opens.mem_inf.mpr ⟨?_, ?_⟩, hx⟩, ?_⟩
    · exact Set.mem_iInter.mpr fun _ => hch _
    · exact Set.mem_iInter.mpr fun _ => Set.mem_iInter.mp hx 0
    · exact WeightPf.mem_finset_inf S _ x fun α _ => TopologicalSpace.Opens.mem_inf.mpr
        ⟨Set.mem_iInter.mpr fun i => hch _, Set.mem_iInter.mpr fun i => hch _⟩
  · have e := hS (fun _ => ch ((U.gt 0).pG.left.base x), fun _ => j 0) j
      (fun α i => ch (((U.gt 0).pG.left ≫ D.toPre.famφB α i).base x))
      (fun α i => ch ((D.toPre.Oφ (U.gt 0).pG α i).base x)) rfl (by
        intro a b hab
        rcases a with _ | a | a <;> rcases b with _ | b | b <;>
          exact congrArg (fun f => ch (f.base x)) hab)
    rw [Finset.sum_eq_zero (fun α _ => by rw [hvan, map_zero, zero_mul]), ← Units.val_pow_eq_pow_val] at e
    exact (Units.mul_right_eq_zero _).mp e

theorem generates_of_ne (hLaws : Laws) [IsDiscreteValuationRing R] (hI : I = maximalIdeal R)
    (t : D.toPre.SecB 1 0) (ht : ¬ ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ (t.f j) = 0) :
    SecBGenerates 1 0 t := by
  unfold SecBGenerates
  intro s'
  obtain ⟨c₀, c', h, h0⟩ := secB_rank_one (hLaws := hLaws) (t := t) (s' := s')
  haveI : Flat D.toPre.P.A.hom := flat_B

  have hc₀ : c₀ ≠ 0 := by
    intro hz
    apply ht
    intro j
    rw [h0 hz j, map_zero]

  have hdiv : ∃ a : R, c' = c₀ * a := by
    obtain ⟨m, hm | hm⟩ := ValuationRing.cond c₀ c'
    · exact ⟨m, hm.symm⟩
    · by_cases hmu : IsUnit m
      · obtain ⟨u, rfl⟩ := hmu
        refine ⟨↑u⁻¹, ?_⟩
        rw [← hm, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
      · exfalso
        have hmI : m ∈ I ^ (0 + 1) := by
          rw [zero_add, pow_one, hI]
          exact (IsLocalRing.mem_maximalIdeal m).mpr hmu
        have hc' : c' ≠ 0 := by
          rintro rfl
          exact hc₀ (by rw [← hm, zero_mul])
        apply ht
        intro j
        have hj : t.f j = toW D.toPre.P.A.hom _ m * s'.f j := by
          refine (sub_eq_zero.mp (toW_mul_eq_zero D.toPre.P.A.hom _ hc' ?_)).symm
          rw [mul_sub, ← _root_.mul_assoc, ← map_mul, hm, h j, sub_self]
        rw [hj, map_mul, app_toW_of_mem D.toPre.P.A.hom (I ^ (0 + 1)) _ hmI, zero_mul]
  obtain ⟨a, rfl⟩ := hdiv
  have hSa : SecIsMul D.toPre.P.A.hom a s' t := by
    intro j
    rw [resTop_scal]
    refine sub_eq_zero.mp (toW_mul_eq_zero D.toPre.P.A.hom _ hc₀ ?_)
    rw [mul_sub, h j, map_mul, _root_.mul_assoc, sub_self]
  refine ⟨a, hSa, fun b hb => ?_⟩
  by_contra hne
  apply ht
  intro j
  have e1 := hb j
  have e2 := hSa j
  rw [resTop_scal] at e1 e2
  have hz : t.f j = 0 := by
    refine toW_mul_eq_zero D.toPre.P.A.hom _ (sub_ne_zero.mpr hne) ?_
    rw [map_sub, sub_mul, ← e1, ← e2, sub_self]
  rw [hz, map_zero]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end
