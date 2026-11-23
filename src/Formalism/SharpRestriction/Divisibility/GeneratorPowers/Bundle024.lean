module

import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSecondPartialLaw
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBFr
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle009
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

section Base

variable {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

def divLinB (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Gen (LB.div (LB.LinComb L φ ε) L)) :
    LB.Gen (LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)) :=
  ⟨fun j => res (fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k),
      Set.mem_iInter.1 hy (Sum.inl 0)⟩ :
    LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j ≤ (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)))
    (w.s (j ∘ Sum.inr, j (Sum.inl 0)))⁻¹⟩

theorem divLinB_isGen (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Gen (LB.div (LB.LinComb L φ ε) L)) (hw : w.IsGen) :
    (divLinB L φ ε w).IsGen := fun i j => unit_ext fun y hy => by
  have le : ∀ j : Fin 1 ⊕ K → L.ι, LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j ≤
      (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)) := fun _ _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k), Set.mem_iInter.1 hy (Sum.inl 0)⟩
  have hi := le i hy.1
  have hj := le j hy.2
  have hij : (𝟙 X : X ⟶ X) y ∈ (LB.div (LB.LinComb L φ ε) L).U (i ∘ Sum.inr, i (Sum.inl 0)) ⊓
      (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)) := ⟨hi, hj⟩
  have hw' := (gm_res (𝟙 X) y _ hij _).symm.trans ((congrArg (gm (𝟙 X) y _) (hw (i ∘ Sum.inr, i (Sum.inl 0))
    (j ∘ Sum.inr, j (Sum.inl 0)))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 X) y _ hij _))))
  have hg : gm (𝟙 X) y _ ((LB.div (LB.LinComb L φ ε) L).g (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0))) =
      (gm (𝟙 X) y _ ((LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)).g i j))⁻¹ := by
    refine (map_mul _ _ _).trans ?_
    refine Eq.trans (congrArg₂ (· * ·) ((gm_res _ y _ hij _).trans (gm_linComb L φ ε (𝟙 _) y _ _ hi.1 hj.1))
      ((map_inv _ _).trans (congrArg _ (gm_res _ y _ hij _)))) ?_
    refine Eq.trans ?_ (congrArg _ (gm_linComb L _ _ (𝟙 _) y i j hy.1 hy.2)).symm
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Fin.prod_univ_one, zpow_one,
      Category.comp_id, Category.id_comp, mul_inv_rev, inv_inv]
    rfl
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans ((map_inv _ _).trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans
    ((gm_res _ y _ hy.2 _).trans (map_inv _ _))))).symm
  exact (congrArg (·⁻¹) (hw'.trans (congrArg (· * _) hg))).trans
    (by simp only [mul_inv_rev, inv_inv]; exact _root_.mul_comm _ _)

end Base

section Tools

theorem prod_cube3 {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] [IsCommMonObj G] {T : Over X0} {M : Type} [CommGroup M]
    (h : (T ⟶ G) → M) (xs : Fin 3 → (T ⟶ G)) :
    ∏ I : thK, h (psum G xs I.down) ^ thε I =
      (h 1)⁻¹ * h (xs 0 * 1) * h (xs 1 * 1) * h (xs 2 * 1) * (h (xs 0 * (xs 1 * 1)))⁻¹ * (h (xs 0 * (xs 2 * 1)))⁻¹ *
        (h (xs 1 * (xs 2 * 1)))⁻¹ * h (xs 0 * (xs 1 * (xs 2 * 1))) := by
  apply GlobalTheory.SecondPartialLaw.prod_cube3 <;> assumption

theorem eta_one {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] : (η[G] : 𝟙_ (Over X0) ⟶ G) = 1 := by
  show η[G] = toUnit _ ≫ η[G]
  rw [toUnit_unique (toUnit (𝟙_ (Over X0))) (𝟙 _), Category.id_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem scale_isGen {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (hg : g.IsGen) : (scaleGenG t φ ε u g).IsGen := fun i j =>
  unit_ext fun y hy => by
    have e := (gm_res (𝟙 Y) y _ hy _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hg i j)).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))))
    refine (gm_res _ y _ hy _).trans ((map_mul _ _ _).trans ?_)
    refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (map_mul _ _ _)))).symm
    refine (congrArg₂ (· * ·) (gm_res _ y le_top hy.1 u) e).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (gm_res _ y le_top hy.2 u).symm rfl))
    exact _root_.mul_left_comm _ _ _

theorem val_rigT {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (rig : LB.Gen (L.pull (eSec A)))
    (T : Over S0) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J : (Z ⟶ A.left) → L.ι) (hJ : Good L z J) :
    val (rigT A L rig T 1) r z J = val rig (r ≫ T.hom) z J := by
  rw [val_of rig (r ≫ T.hom) z J (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans ((zpow_one _).trans ((gm_res r z _ hm _).trans ?_))
  exact gm_pull r T.hom z _ (show T.hom (r z) ∈ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)) from
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _

end Tools

section Prim

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

abbrev zz : 𝟙_ (Over X0) ⟶ t.G ⊗ t.G := lift (η[t.G] : 𝟙_ (Over X0) ⟶ t.G) (η[t.G] : 𝟙_ (Over X0) ⟶ t.G)

theorem cube_one_left {T : Over X0} {M : Type} [CommGroup M] (h : (T ⟶ t.G) → M) (b : T ⟶ t.G) :
    ∏ I : ULift (Finset (Fin 2)), h (psum t.G ![1, b] I.down) ^ cε 2 I = 1 := by
  rw [prod_cube2]
  simp

theorem cube_one_right {T : Over X0} {M : Type} [CommGroup M] (h : (T ⟶ t.G) → M) (b : T ⟶ t.G) :
    ∏ I : ULift (Finset (Fin 2)), h (psum t.G ![b, 1] I.down) ^ cε 2 I = 1 := by
  rw [prod_cube2]
  simp

theorem exists_wP : ∃ wP : PrimTyG t, IsPrimG t wP := by
  have hL := t.PP.isLB
  obtain ⟨w, hw⟩ := t.prim
  let w1 : PrimTyG t := divLinB t.PP.L _ _ w
  have hw1 : w1.IsGen := divLinB_isGen t.PP.L _ _ w hw
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), eSec t.G ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, eSec, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact (Category.comp_id _).trans (eta_one t.G)
    · rfl
  obtain ⟨u, hu⟩ := exists_ratio t.PP.L hL (φ' := fun _ : PUnit => eSec t.G) (ε' := fun _ => 1)
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg, Finset.prod_inv_distrib,
        hpt, Fintype.prod_unique]
      rw [cube_one_left t (fun p => h p.left), inv_one, _root_.mul_one])
    (LB.pullGen t.PP.L _ _ w1 (eSec t.G)) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hw1 _) t.PP.rig t.PP.rigGen
  have hes : eSec t.G ≫ t.G.hom = 𝟙 _ := Over.w η[t.G]
  refine ⟨scaleGenG t _ _ (pullU t.G.hom ⊤ u⁻¹) w1, scale_isGen t _ _ _ w1 hw1, corr_of_val hL fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans ((val_scale t _ _ _ _ _ y J hJ).trans ?_)
  refine (congrArg₂ (· * ·) ((gm_pull (𝟙 _ ≫ eSec t.G) t.G.hom y ⊤ trivial u⁻¹).trans
    (congrArg (fun r => gm r y ⊤ u⁻¹) (by rw [Category.assoc, hes, Category.comp_id])))
    ((val_pull hJ w1 _ _).symm.trans (hu _ (𝟙 _) y J hJ))).trans ?_
  rw [map_inv, inv_mul_cancel_left]

theorem exists_wL (a : 𝓞 E) : ∃ wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over X0)).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val wL (r ≫ (zz t).left) z J = 1 := by
  have hL := t.PP.isLB
  obtain ⟨w, hw⟩ := t.adj a
  let w2 := divLin t.PP.L (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cε 2)
    (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) (cε 2) w
  have hw2 : w2.IsGen := divLin_isGen t.PP.L _ _ _ _ w hw
  have hp1 : ∀ I : ULift.{0} (Finset (Fin 2)), (zz t).left ≫ cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act (H.bar a)] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · show zz t ≫ fst t.G t.G = 1
      exact (lift_fst _ _).trans (eta_one t.G)
    · show zz t ≫ (snd t.G t.G ≫ t.act.act (H.bar a)) = η[t.G] ≫ t.act.act (H.bar a)
      exact lift_snd_assoc _ _ _
  have hp2 : ∀ I : ULift.{0} (Finset (Fin 2)), (zz t).left ≫ cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] I =
      (psum t.G ![η[t.G] ≫ t.act.act a, 1] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · show zz t ≫ (fst t.G t.G ≫ t.act.act a) = η[t.G] ≫ t.act.act a
      exact lift_fst_assoc _ _ _
    · show zz t ≫ snd t.G t.G = 1
      exact (lift_snd _ _).trans (eta_one t.G)
  obtain ⟨s, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hp1, hp2, Fintype.prod_empty]
      rw [cube_one_left t (fun p => h p.left), cube_one_right t (fun p => h p.left), inv_one, _root_.mul_one])
    (LB.pullGen t.PP.L _ _ w2 (zz t).left) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hw2 _)
  have le : (⊤ : ((𝟙_ (Over X0)).left).Opens) ≤ LB.wchart t.PP.L (PEmpty.elim : PEmpty → (_ ⟶ t.G.left)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  let u := res le (s.s PEmpty.elim)
  have hz : (zz t).left ≫ (t.G ⊗ t.G).hom = 𝟙 _ := Over.w (zz t)
  refine ⟨scaleGenG t _ _ (pullU (t.G ⊗ t.G).hom ⊤ u⁻¹) w2, scale_isGen t _ _ _ w2 hw2, fun Z r z J hJ => ?_⟩
  refine (val_scale t _ _ _ _ _ z J hJ).trans ?_
  have e1 : val w2 (r ≫ (zz t).left) z J = gm r z ⊤ u := by
    refine (val_pull hJ w2 _ _).symm.trans ((hv Z r z J hJ).symm.trans ?_)
    rw [val_of s r z J PEmpty.elim (fun k => k.elim)]
    exact (gm_res r z le trivial _).symm
  refine (congrArg₂ (· * ·) ((gm_pull (r ≫ (zz t).left) (t.G ⊗ t.G).hom z ⊤ trivial u⁻¹).trans
    (congrArg (fun q => gm q z ⊤ u⁻¹) (by rw [Category.assoc, hz, Category.comp_id]))) e1).trans ?_
  rw [map_inv, inv_mul_cancel]

end Prim

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

attribute [local instance] Over.cartesianMonoidalCategory

theorem jet_zero_hom_ext {S : Type} [CommRing S] {κ κ' : Type} (f g : Jet S κ 0 →ₐ[S] Jet S κ' 0) : f = g := by
  apply jet_hom_ext
  intro i
  have h0 : (Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (MvPolynomial.X i) : Jet S κ 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact X_mem_orig i)
  rw [h0, map_zero, map_zero]

theorem comp_one' {X0 : Scheme.{0}} {G : Over X0} [GrpObj G] {T T' : Over X0} (f : T' ⟶ T) :
    f ≫ (1 : T ⟶ G) = 1 := by
  show f ≫ (toUnit T ≫ η[G]) = toUnit T' ≫ η[G]
  rw [← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem val_scale' {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (scaleGen φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  GermB.val_scale Xo.univ.t φ ε u g r z J hJ

theorem chart_at_zero_eq_one (C : ChartAt Xo c y) : C.x 0 = 1 := by
  have hz := C.chart.zero 0
  have hid : homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫
      homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S) = 𝟙 _ := by
    rw [homAt_comp, jet_zero_hom_ext ((Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)).comp jetAug) (AlgHom.id S _), homAt_id]
  calc C.x 0 = 𝟙 _ ≫ C.x 0 := (Category.id_comp _).symm
    _ = (homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫
          homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)) ≫ C.x 0 := by rw [hid]
    _ = homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫ 1 := by rw [Category.assoc, hz]
    _ = 1 := comp_one' _

theorem jet_point_zero_eq_one (C : ChartAt Xo c y) {n : ℕ} (i : Fin n) : jpt y C.d C.x 0 i = 1 := by
  unfold jpt
  rw [chart_at_zero_eq_one C]
  exact comp_one' _

theorem const_ad (C : ChartAt Xo c y) (a : 𝓞 E) : MvPowerSeries.constantCoeff (C.B.ad a) = 1 := by
  have e := Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev (n := 1) ![0, Germ.pt S (n := 1) C.d 0]
    (by intro p q; fin_cases p <;> simp [Germ.pt]) (C.B.ad a)
  rw [C.B.adjoint_zero_fst a, map_one] at e
  exact e.symm

def AdRel (C : ChartAt Xo c y) (a : 𝓞 E) (wL : ExpGC.AdTy Xo a) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ, (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (C.B.ad a) ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y C.d C.x m (0 : Fin 2)) (jpt y C.d C.x m (1 : Fin 2))).left)
        (pe y C.d C.x C.e m ![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
      (scaleGen _ _ (unitΓ u)
        (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)]))

theorem exists_adRel (C : ChartAt Xo c y) (a : 𝓞 E) : ∃ wL : ExpGC.AdTy Xo a, wL.IsGen ∧ AdRel C a wL :=
  C.frame.ad a

theorem wL_zero (C : ChartAt Xo c y) (a : 𝓞 E) (wL : ExpGC.AdTy Xo a) (hrel : AdRel C a wL) {Z : Scheme.{0}}
    (r : Z ⟶ (overAt y.x S).left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι)
    (hJ : Good Xo.univ.t.PP.L z J) :
    val wL (r ≫ (lift (1 : overAt y.x S ⟶ Xo.univ.t.G) (1 : overAt y.x S ⟶ Xo.univ.t.G)).left) z J = 1 := by
  obtain ⟨u, hu, hc⟩ := hrel 0
  have hu1 : u = 1 := Units.ext (hu.trans (ExpGB.psJet_zero_of _ (const_ad C a)))
  have hι : homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S) ≫
      lift (jpt y C.d C.x 0 (0 : Fin 2)) (jpt y C.d C.x 0 (1 : Fin 2)) =
        lift (1 : overAt y.x S ⟶ Xo.univ.t.G) (1 : overAt y.x S ⟶ Xo.univ.t.G) := by
    rw [jet_point_zero_eq_one C, jet_point_zero_eq_one C, comp_lift]
    exact congrArg₂ (fun p q => lift p q) (comp_one' _) (comp_one' _)
  have h1 := val_corr hJ hc (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left)
  rw [val_mul hJ, val_pull hJ, val_scale' _ _ _ _ _ z J hJ, hu1,
    show unitΓ (1 : (Jet S (Fin 2 × Fin C.d) 0)ˣ) = 1 by unfold unitΓ; exact map_one _, map_one,
    _root_.one_mul] at h1
  have hpe : val (pe y C.d C.x C.e 0 ![fun j => psIn C.d 0 ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left) z J =
      val (pe y C.d C.x C.e 0 ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)])
        (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left) z J := by
    have hm : (homAt y.x (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
        (![fun j => psIn C.d 0 ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)).left =
        (homAt y.x (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
          (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)).left := by
      rw [jet_zero_hom_ext (jetSubstP 0 _) (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
        (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)]
    unfold pe
    rw [hm]
  rw [hpe, mul_eq_right] at h1
  rw [Category.assoc, ← Over.comp_left, hι] at h1
  exact h1

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

namespace ConjugateMinimaInstance

open NumberField Formalism.MainNotions.ModuliIntegralCharts Formalism.BasicNotions

theorem scalar_frame_w_zero_exists (D : D7) : ∃ w₀ : 𝓞 D.host.E, (w₀ : D.host.E) + D.host.conj w₀ = 1 := by
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hcc : (((D.host.gal D.host.conj).1.2 : ℤˣ) : ℤ) = -1 := by
    have hg : D.host.gal D.host.conj = Formalism.HC.Frame.cc _ := by
      simp [Formalism.HC.HostRaw.conj]
    rw [hg]
    simp only [Formalism.HC.Frame.cc] <;> decide
  have hc : D.host.conj D.host.sqd = -D.host.sqd := by
    rw [D.host.gal_sqd, hcc]
    simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.host.d = 4 * m + 3 := ⟨D.host.d / 4, by omega⟩
  have hs : D.host.sqd ^ 2 = -(4 * (m : D.host.E) + 3) := by
    have h0 := D.host.sqd_sq
    rw [hm] at h0
    push_cast at h0
    exact h0
  have hint : IsIntegral ℤ ((1 + D.host.sqd) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((m : ℤ) + 1), by monicity!, ?_⟩
    rw [← Polynomial.aeval_def]
    simp only [map_add (f := _), map_sub, map_pow, map_one, map_natCast, Polynomial.aeval_X, Polynomial.aeval_C,
      algebraMap_int_eq, eq_intCast, Int.cast_add, Int.cast_natCast, Int.cast_one]
    linear_combination (1 / 4 : D.host.E) * hs
  refine ⟨⟨(1 + D.host.sqd) / 2, hint⟩, ?_⟩
  show (1 + D.host.sqd) / 2 + D.host.conj ((1 + D.host.sqd) / 2) = 1
  rw [map_div₀, map_add (f := _), map_one, hc, map_ofNat]
  ring

theorem conj_ne (D : D7) : ∃ z : D.host.E, D.host.conj z ≠ z := by
  by_contra h
  push_neg at h
  have h1 : D.host.conj = 1 := AlgEquiv.ext h
  have h2 : Formalism.HC.Frame.cc D.R.toFrame = 1 := by
    have := congrArg D.host.gal h1
    simpa [Formalism.HC.HostRaw.conj] using this
  have h3 := congrArg Prod.fst h2
  simp only [Formalism.HC.Frame.cc, Prod.fst_one] at h3
  revert h3
  decide

theorem phiC_rec_eq {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (hj : j < D.R.m)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    X.phiC la y = (eWL B.KO la : ℝ) * (P.loc X.dat (WeightAlgebra.resCh la)).phiCy (X.pt66 la y) := by
  simp [WeightAlgebra.PJ.phiC, hj]

end ConjugateMinimaInstance

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.MainNotions

variable {D : Formalism.BasicNotions.D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def EtVal (X : WeightAlgebra.PJ D B P j) (i : ℕ)
    (η : B.Cusp j (WeightAlgebra.wscalar D j (WeightAlgebra.g0 D * i) (by unfold WeightAlgebra.g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩))) : Prop :=
  ∀ la (y : X.Pt la), ((2 * i * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ η)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
