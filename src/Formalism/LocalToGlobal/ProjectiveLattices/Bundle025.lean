module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle021
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section



noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}



theorem locFrGen_of {L : Type} [CommRing L] (x : Sp L ⟶ Xo.X) {t' : SAB H (Sp L)} (m1 : SABMap t' Xo.univ.t x)
    (σ' : LB.Sec t'.PP.L) (hgen : ∀ s' : LB.Sec t'.PP.L, ∃! a : L, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i) :
    ∃ s : LB.Sec (PPx x), ∀ s'' : LB.Sec (PPx x), ∃! a : L, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨w, hwG, -, -⟩ := m1.lin
  have hw : PGen w := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w).mp hwG
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨s0, hs0⟩ := thf_secUp hw hL hL' σ'
  have P' := m1.cart.1
  obtain ⟨h, hF, hS⟩ : ∃ h : Gx x ⟶ t'.G.left, h ≫ m1.cm.F = (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left ∧ h ≫ t'.G.hom = (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left :=
    ⟨P'.lift _ _ ((Over.w (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G)).trans
      (Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G)).symm),
      P'.lift_fst _ _ _, P'.lift_snd _ _ _⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k : t'.G.left ⟶ Gx x, k ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom ∧ k ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m1.cm.F :=
    ⟨(CartesianMonoidalCategory.lift
        (Over.homMk t'.G.hom P'.w.symm : Over.mk (m1.cm.F ≫ Xo.univ.t.G.hom) ⟶ Over.mk x)
        (Over.homMk m1.cm.F rfl : Over.mk (m1.cm.F ≫ Xo.univ.t.G.hom) ⟶ Xo.univ.t.G)).left,
      congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst _ _),
      congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd _ _)⟩
  have gext : ∀ u v : Gx x ⟶ Gx x, u ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = v ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left → u ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = v ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left → u = v := by
    intro u v e1 e2
    have e3 : (Over.homMk u rfl : Over.mk (u ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G) =
        Over.homMk (U := Over.mk (u ≫ (Over.mk x ⊗ Xo.univ.t.G).hom)) (V := Over.mk x ⊗ Xo.univ.t.G) v (by
          show v ≫ _ = u ≫ _
          rw [← Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G), ← Category.assoc,
            ← Category.assoc, e1]) := by
      apply CartesianMonoidalCategory.hom_ext
      · first | exact Over.OverMorphism.ext e1 | exact Over.Hom.ext e1 | (ext; exact e1)
      · first | exact Over.OverMorphism.ext e2 | exact Over.Hom.ext e2 | (ext; exact e2)
    exact congrArg Over.Hom.left e3
  have hhk : h ≫ k = 𝟙 _ := gext _ _ (by rw [Category.assoc, hk1, hS, Category.id_comp])
    (by rw [Category.assoc, hk2, hF, Category.id_comp])
  have hkh : k ≫ h = 𝟙 _ := P'.hom_ext (by rw [Category.assoc, hF, hk2, Category.id_comp])
    (by rw [Category.assoc, hS, hk1, Category.id_comp])
  have hle : ∀ j, m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ k ⁻¹ᵁ (PPx x).U (fun _ => j) := fun j z hz =>
    Set.mem_iInter.mpr fun _ => Set.mem_iInter.mp
      (chart_le_pullback_open Xo.univ.t.PP.L k hk2 (fun _ => j) (Set.mem_iInter.mpr fun _ => hz)) PUnit.unit
  have hpre : ∀ (z : t'.G.left) j, z ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) →
      z ∈ m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z j hz => Set.mem_iInter.mp hz PUnit.unit
  refine ⟨thfPull1 Xo.univ.t.PP.L h hF s0, fun s'' => ?_⟩
  obtain ⟨σ'', hσ''⟩ := sec_down hw hL hL'
    (fun j => (k.appLE ((PPx x).U (fun _ => j)) (m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j) (hle j)).hom
      (s''.f (fun _ => j))) (by
      intro y j j' hj hj'
      try beta_reduce
      have h1 : k y ∈ (PPx x).U (fun _ => j) := hle j hj
      have h2 : k y ∈ (PPx x).U (fun _ => j') := hle j' hj'
      have hg : gm (𝟙 _ ≫ k) y ((PPx x).U (fun _ => j) ⊓ (PPx x).U (fun _ => j'))
          ((PPx x).g (fun _ => j) (fun _ => j')) =
          gm m1.cm.F y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j') :=
        (gm_linComb Xo.univ.t.PP.L (fun _ : Fin 1 => (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) (fun _ => 1) (𝟙 _ ≫ k) y
          (fun _ => j) (fun _ => j') h1 h2).trans (by rw [Fin.prod_univ_one, zpow_one, Category.id_comp, hk2])
      rw [gs_appLE k _ _ (hle j) (𝟙 _) y hj, gs_appLE k _ _ (hle j') (𝟙 _) y hj',
        gs_compat s'' (𝟙 _ ≫ k) y h1 h2, hg])
  obtain ⟨a, ha, hau⟩ := hgen σ''
  refine ⟨a, fun J => ?_, fun b hb => hau b fun i => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, J = fun _ => j := ⟨J 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
    apply fn_ext
    intro y hy
    have hyh : h y ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) :=
      chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j) hy
    obtain ⟨i, hi⟩ : ∃ i, h y ∈ t'.PP.L.U i := TopologicalSpace.Opens.mem_iSup.mp (by
      rw [hL'.cover]
      first | trivial | exact Set.mem_univ _ | simp)
    have e1 := gs_appLE k _ _ (hle j) h y (hpre _ _ hyh) (s''.f (fun _ => j))
    rw [hhk] at e1
    have e2 := hσ'' _ h y j i (hpre _ _ hyh) hi
    have e3 := hs0 _ h y (fun _ => j) i hyh hi
    have e4 : gs (𝟙 _) y ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s0).f (fun _ => j)) =
        gs (𝟙 _ ≫ h) y _ (s0.f (fun _ => j)) := gs_appLE h _ _ _ (𝟙 _) y hy _
    rw [Category.id_comp] at e4
    have e5 : gs (𝟙 _) y ((PPx x).U (fun _ => j)) (scal x a (fun _ => j)) = cst (𝟙 _ ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y a :=
      gs_constFn (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) (𝟙 _) y hy a
    rw [gs_mul (𝟙 _) y _ hy, e4, e3, e5, ← e1, e2, ha i, gs_mul h y _ hi, gs_constFn t'.G.hom _ h y hi a,
      hS, Category.id_comp]
    ring
  · apply fn_ext
    intro y' hy'
    obtain ⟨j, hj⟩ : ∃ j, m1.cm.F y' ∈ Xo.univ.t.PP.L.U j := TopologicalSpace.Opens.mem_iSup.mp (by
      rw [hL.cover]
      first | trivial | exact Set.mem_univ _ | simp)
    have hkm : k y' ∈ (PPx x).U (fun _ => j) := hle j hj
    have hmem : y' ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) := Set.mem_iInter.mpr fun _ => hj
    have f1 := hσ'' _ (𝟙 _) y' j i hj hy'
    have f2 := gs_appLE k _ _ (hle j) (𝟙 _) y' hj (s''.f (fun _ => j))
    have f3 : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) (scal x b (fun _ => j)) = cst ((𝟙 _ ≫ k) ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y' b :=
      gs_constFn (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) (𝟙 _ ≫ k) y' hkm b
    have f4 : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s0).f (fun _ => j)) =
        gs ((𝟙 _ ≫ k) ≫ h) y' _ (s0.f (fun _ => j)) := gs_appLE h _ _ _ (𝟙 _ ≫ k) y' hkm _
    rw [Category.assoc, hkh, Category.comp_id] at f4
    have f5 := hs0 _ (𝟙 _) y' (fun _ => j) i hmem hy'
    have f2b : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) (s''.f (fun _ => j)) =
        cst ((𝟙 _ ≫ k) ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y' b *
          gs (𝟙 _) y' ((Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j)) (s0.f (fun _ => j)) := by
      rw [hb (fun _ => j), gs_mul (𝟙 _ ≫ k) y' _ hkm, f3, f4]
    rw [f5] at f2b
    have f6 := (f1.symm.trans f2).trans f2b
    rw [Category.id_comp, hk1, mul_left_comm] at f6
    rw [gs_mul (𝟙 _) y' _ hy', gs_constFn t'.G.hom _ (𝟙 _) y' hy' b, Category.id_comp]
    exact (Units.mul_right_inj _).mp f6

end Formalism.L2.Pj
end
end

section



noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}



theorem gfp_gen_of {L : Type} [Field L] (x : Sp L ⟶ Xo.X) {t' : SAB H (Sp L)} (m1 : SABMap t' Xo.univ.t x)
    (σ' : LB.Sec t'.PP.L) (hgen : ∀ s' : LB.Sec t'.PP.L, ∃! a : L, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i) :
    ∃ s : LB.Sec (PPx x), ∀ s'' : LB.Sec (PPx x), ∃! a : L, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨w, hwg, -⟩ := m1.lin
  have hw : PGen w := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w).1 hwg
  obtain ⟨su, hsu⟩ := thf_secUp hw Xo.univ.t.PP.isLB t'.PP.isLB σ'
  have hpb : IsPullback m1.cm.F t'.G.hom Xo.univ.t.G.hom x := And.left m1.cart
  obtain ⟨h, hF, hπ⟩ : ∃ h : Gx x ⟶ t'.G.left,
      h ≫ m1.cm.F = (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left ∧
        h ≫ t'.G.hom = (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left :=
    ⟨hpb.lift _ _ ((Over.w (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G)).trans
      (Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G)).symm), hpb.lift_fst _ _ _,
      hpb.lift_snd _ _ _⟩
  obtain ⟨k, hkφ, hkπ⟩ : ∃ k : t'.G.left ⟶ Gx x,
      k ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m1.cm.F ∧
        k ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom :=
    ⟨(CartesianMonoidalCategory.lift (Over.homMk t'.G.hom rfl : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x)
      (Over.homMk m1.cm.F hpb.w : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G)).left,
      congrArg (fun f => Over.Hom.left f) (CartesianMonoidalCategory.lift_snd
        (Over.homMk t'.G.hom rfl : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x)
        (Over.homMk m1.cm.F hpb.w : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G)),
      congrArg (fun f => Over.Hom.left f) (CartesianMonoidalCategory.lift_fst
        (Over.homMk t'.G.hom rfl : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x)
        (Over.homMk m1.cm.F hpb.w : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G))⟩
  have hkh : k ≫ h = 𝟙 _ := hpb.hom_ext (by rw [Category.assoc, hF, hkφ, Category.id_comp])
    (by rw [Category.assoc, hπ, hkπ, Category.id_comp])
  have hhk : h ≫ k = 𝟙 _ := by
    have e1 : (Over.homMk (h ≫ k) (by
        rw [← Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G)]
        simp only [Category.assoc]
        rw [reassoc_of% hkπ, reassoc_of% hπ]) :
        Over.mk x ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G) = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext
      · ext
        simp only [Over.comp_left, Over.homMk_left, Over.id_left, Category.assoc, Category.id_comp]
        rw [hkπ, hπ]
      · ext
        simp only [Over.comp_left, Over.homMk_left, Over.id_left, Category.assoc, Category.id_comp]
        rw [hkφ, hF]
    exact congrArg (fun f => Over.Hom.left f) e1
  have hscal : ∀ (b : L) (i : (PPx x).ι),
      scal x b i = constFn (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U i) b :=
    fun _ _ => rfl
  have hle : ∀ j, m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ k ⁻¹ᵁ (PPx x).U (fun _ => j) := by
    intro j y hy
    have e : (k ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) y ∈ Xo.univ.t.PP.L.U j := by
      rw [hkφ]; exact hy
    show k y ∈ (PPx x).U (fun _ => j)
    exact Set.mem_iInter.2 fun _ => e
  refine ⟨thfPull1 Xo.univ.t.PP.L h hF su, fun s'' => ?_⟩
  have hσ : ∀ (y : t'.G.left) (j j' : Xo.univ.t.PP.L.ι), m1.cm.F y ∈ Xo.univ.t.PP.L.U j →
      m1.cm.F y ∈ Xo.univ.t.PP.L.U j' →
      gs (𝟙 _) y _ ((k.appLE _ _ (hle j)).hom (s''.f fun _ => j)) =
        (gm m1.cm.F y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j')).val *
          gs (𝟙 _) y _ ((k.appLE _ _ (hle j')).hom (s''.f fun _ => j')) := fun y j j' h1 h2 =>
    (gs_appLE k _ _ (hle j) (𝟙 _) y h1 _).trans ((gs_compat s'' (𝟙 _ ≫ k) y (hle j h1) (hle j' h2)).trans
      (congrArg₂ (· * ·) (congrArg Units.val ((gm_linComb Xo.univ.t.PP.L
        (fun _ : Fin 1 => (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) (fun _ => (1 : ℤ))
        (𝟙 _ ≫ k) y (fun _ => j) (fun _ => j') (hle j h1) (hle j' h2)).trans
          (by rw [Fin.prod_univ_one, zpow_one, Category.id_comp, hkφ])))
        (gs_appLE k _ _ (hle j') (𝟙 _) y h2 _).symm))
  obtain ⟨s', hs'⟩ := sec_down hw Xo.univ.t.PP.isLB t'.PP.isLB
    (fun j => (k.appLE _ _ (hle j)).hom (s''.f fun _ => j)) hσ
  obtain ⟨a, ha, hau⟩ := hgen s'
  refine ⟨a, fun i => ?_, fun b hb => hau b fun k' => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    refine fn_ext fun y hy => ?_
    have hφy := LB.wchart_le Xo.univ.t.PP.L
      (fun _ : Fin 1 => (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) (fun _ => j) 0 hy
    have hFy : m1.cm.F (h y) ∈ Xo.univ.t.PP.L.U j := by
      have e : (h ≫ m1.cm.F) y ∈ Xo.univ.t.PP.L.U j := by rw [hF]; exact hφy
      exact e
    obtain ⟨k', hk'⟩ : ∃ k', h y ∈ t'.PP.L.U k' := by
      have : h y ∈ (⨆ k', t'.PP.L.U k') := by rw [t'.PP.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    have hL : gs (𝟙 _) y _ (s''.f fun _ => j) = (gw w h y j k').val *
        (cst (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left y a * gs h y _ (σ'.f k')) := by
      have e0 : gs (𝟙 (Gx x)) y ((PPx x).U fun _ => j) (s''.f fun _ => j) =
          gs (h ≫ k) y ((PPx x).U fun _ => j) (s''.f fun _ => j) := by rw [hhk]
      rw [e0, ← gs_appLE k _ _ (hle j) h y hFy, hs' _ h y j k' hFy hk', ha k', gs_mul h y _ hk',
        gs_constFn _ _ h y hk' a, hπ]
    rw [hL, gs_mul (𝟙 _) y _ hy]
    erw [hscal]
    rw [gs_constFn _ _ (𝟙 _) y hy a, Category.id_comp, mul_left_comm]
    congr 1
    symm
    refine (gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) (𝟙 _) y hy (su.f fun _ => j)).trans ?_
    rw [Category.id_comp]
    exact hsu _ h y (fun _ => j) k' (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j) hy) hk'
  · refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ : ∃ j, m1.cm.F y ∈ Xo.univ.t.PP.L.U j := by
      have : m1.cm.F y ∈ (⨆ j, Xo.univ.t.PP.L.U j) := by rw [Xo.univ.t.PP.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    have hky : k y ∈ (PPx x).U (fun _ => j) := hle j hj
    have hd := hs' _ (𝟙 _) y j k' hj hy
    have hL : gs (𝟙 _) y _ ((k.appLE _ _ (hle j)).hom (s''.f fun _ => j)) =
        cst t'.G.hom y b * ((gw w (𝟙 _) y j k').val * gs (𝟙 _) y _ (σ'.f k')) := by
      rw [gs_appLE k _ _ (hle j) (𝟙 _) y hj, Category.id_comp, hb (fun _ => j), gs_mul k y _ hky]
      erw [hscal]
      rw [gs_constFn _ _ k y hky b, hkπ]
      congr 1
      refine (gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) k y hky (su.f fun _ => j)).trans ?_
      rw [hkh]
      exact hsu _ (𝟙 _) y (fun _ => j) k' (Set.mem_iInter.2 fun _ => hj) hy
    rw [gs_mul (𝟙 _) y _ hy, gs_constFn _ _ (𝟙 _) y hy b, Category.id_comp]
    apply (Units.mul_right_inj (gw w (𝟙 _) y j k')).1
    exact hd.symm.trans (hL.trans (by ring))

theorem gfp_gen (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {L : Type} [Field L] (x : Sp L ⟶ Xo.X) :
    ∃ s : LB.Sec (PPx x), ∀ s'' : LB.Sec (PPx x), ∃! a : L, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨PP', cub, sym, adj, prim, m1, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull x Xo.univ.t
  obtain ⟨σ', hgen⟩ := globalSections_rank_one_fibre hT amplePt Xo.univ m1
  exact gfp_gen_of x m1 σ' hgen

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def lamOf (la : HeightOneSpectrum (𝓞 c.F)) : PointsOfFlagModel.abelian₂ (Formalism.MainNotions.WeightAlgebra.resCh la) c :=
  ⟨la, by
    have h : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : 𝓞 c.F ⧸ la.asIdeal) = 0 := by
      unfold Formalism.MainNotions.WeightAlgebra.resCh
      exact CharP.cast_eq_zero _ _
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (by simpa using h)⟩

def LiesOverBaseChange (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (η : PointsOfFlagModel.Pt Tw .yy) : Prop :=
  letI := io.toAlgebra
  η.1 = lamOf la ∧ ∃ eF : T.Fr →+* ↥η.2.1.S,
    eF.comp io = η.2.2.1.fK ∧
    (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧
    (∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧
    η.2.2.1.y ≫ pullback.fst _ _ = spMap eF ≫ y.1.x ∧
    ∀ τ i, ∃ u' : Sp (DualNumber ↥η.2.1.S) ⟶ (Tw.Y η.1).oF.t.G.left,
      u' ≫ (Tw.Y η.1).m.φ = (η.2.2.2.u τ i).left ∧
      u' ≫ (Tw.Y η.1).m0.toSABMap.φ = spMap (dualMap eF) ≫ y.1.u τ i

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

instance instCMHost (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

def InR (D : D7) (j : ℕ) : Prop := 1 ≤ j ∧ j ≤ D.R.m

structure Par (D : D7) : Type 1 where
  H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E
  l : Level H
  c : Coeff l
  Dw : ℕ → Datum H
  Xo : ∀ j, Moduli (Dw j) l
  eO : 𝓞 c.F ≃+* D.what₂.O

variable {D : D7}

def IsDatW (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (j : ℕ) (Dw : Datum H) : Prop :=
  letI := D.host.cmStar
  Dw.p = (D.R.sigW j).1 ∧ Dw.q = (D.R.sigW j).2 ∧
  ∃ (φ : Dw.La →ₗ[𝓞 D.host.E] (D.sp.W j).V) (ε : ℤˣ), Function.Injective φ ∧
    LinearMap.range φ = Submodule.span (𝓞 D.host.E)
      {v | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ (D.sp.W j).L0, v = a • x} ∧
    ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * (D.sp.W j).hT (φ x) (φ y))

namespace Par

variable (Q : Par D)

def PinHost : Prop :=
  Q.H.d = D.host.d ∧ (Q.H.rt : D.host.E) = D.host.sqrtMinusD ∧ Q.H.rt0 = D.host.φ₀ D.host.sqrtMinusD ∧
    ∀ t : D.what₂.Tau, DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0

def PinLevel : Prop := Q.l.M = D.host.g 0 * D.host.g 1 ∧ Q.l.A = 1

def PinField : Prop := ∀ x : 𝓞 Q.c.F, D.what₂.embLL (D.what₂.OtoLL (Q.eO x)) = ((x : Q.c.F) : ℂ)

def PinDat : Prop := ∀ j, InR D j → IsDatW D j (Q.Dw j)

def Pins : Prop := Q.PinHost ∧ Q.PinLevel ∧ Q.PinField ∧ Q.PinDat

end Par

def ext0 {p : ℕ} (f : Fin p → ℕ) (i : ℕ) : ℕ := if h : i < p then f ⟨i, h⟩ else 0

theorem matrixExtendByZero_add {p : ℕ} (f g : Fin p → ℕ) (i : ℕ) : ext0 (fun k => f k + g k) i = ext0 f i + ext0 g i := by
  unfold ext0; split_ifs <;> rfl

theorem partitionExtendByZero_antitone {p : ℕ} {f : Fin p → ℕ} (hf : Antitone f) : Antitone (ext0 f) := by
  intro i k hik
  unfold ext0
  by_cases hk : k < p
  · rw [dite_eq_left hk, dite_eq_left (lt_of_le_of_lt hik hk)]; exact hf hik
  · rw [dite_eq_right hk]; exact Nat.zero_le _


open Classical in
def wtA {j : ℕ} (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) : ℕ :=
  ∑ t : D.what₂.Tau, ((if x.1 = DV.tauEmb D t then ext0 (w.aP t) x.2 else 0) +
    if x.1 = conjEmb (DV.tauEmb D t) then ext0 (w.aM t) x.2 else 0)

theorem wtA_wadd {j : ℕ} (w w' : WeightFamilies.Wt D j) : wtA (WeightAlgebra.wadd w w') = wtA w + wtA w' := by
  funext x
  simp only [wtA, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((WeightAlgebra.wadd w w').aP t) x.2 = ext0 (w.aP t) x.2 + ext0 (w'.aP t) x.2 := matrixExtendByZero_add _ _ _
  have h2 : ext0 ((WeightAlgebra.wadd w w').aM t) x.2 = ext0 (w.aM t) x.2 + ext0 (w'.aM t) x.2 := matrixExtendByZero_add _ _ _
  rw [h1, h2]
  split_ifs <;> omega

theorem n_wadd {j : ℕ} (w w' : WeightFamilies.Wt D j) : (WeightAlgebra.wadd w w').n = w.n + w'.n := rfl

theorem dom_wtA {j : ℕ} (w : WeightFamilies.Wt D j) : Dom (wtA w) w.n := by
  refine ⟨fun τ i k hik => ?_, w.n_even⟩
  simp only [wtA]
  refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone t) hik
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti t) hik
    · exact le_rfl

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def incl : M →ₗ[K] L ⊗[K] M := TensorProduct.mk K L M 1

end Ext

section Forms

variable {K : Type} [Field K] {LL : Type} [Field LL] [NumberField LL] [Algebra K LL]
variable {C : Type} [AddCommGroup C] [Module K C] {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {D : D7}

def rhoOf (LL : Type) [Field LL] [Algebra K LL] {G0 : Type} [Group G0] (ρC : G0 →* (C →ₗ[K] C)) :
    G0 →* (LL ⊗[K] C →ₗ[LL] LL ⊗[K] C) where
  toFun g := (ρC g).baseChange LL
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g g' := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

end Forms

end Formalism.L2.Pj
end
end
