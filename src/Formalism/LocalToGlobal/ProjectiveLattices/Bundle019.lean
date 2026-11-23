module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart Rel viaT liftT scaleD)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

instance gfpActHom (a : 𝓞 E) : IsMonHom (Xo.univ.t.act.act a) := Xo.univ.t.act.hom a

theorem gfp_hcId : IsGrpPullback Xo.univ.t.G Xo.univ.t.G (𝟙 Xo.X) (𝟙 Xo.univ.t.G.left) := by
  have : IsMonHom (Iso.refl Xo.univ.t.G).hom := by dsimp only [Iso.refl]; infer_instance
  exact (isGrpPullback_of_iso (Iso.refl Xo.univ.t.G)).congr rfl (Over.id_left _)

def gfpVec {L : Type} [Field L] (x : Sp L ⟶ Xo.X) {n : ℕ}
    (xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L)
      (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G)
    (cc : Fin n → L) : Sp (DualNumber L) ⟶ Xo.univ.t.G.left :=
  (tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x

section V

variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L)
      (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}

theorem gfpVec_w (cc : Fin n → L) :
    gfpVec x xc cc ≫ Xo.univ.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ x := by
  have hw : (tvec (x := xc) cc).left ≫ pullback.snd Xo.univ.t.G.hom x = spMap (algebraMap L (DualNumber L)) := by
    simpa using Over.w (tvec (x := xc) cc)
  simp only [gfpVec, Category.assoc, pullback.condition, reassoc_of% hw]


variable (xc) in
def gfpW (cc : Fin n → L) : tEps x ⟶ Xo.univ.t.G := Over.homMk (gfpVec x xc cc) (gfpVec_w cc)

variable (xc) in
theorem gfp_rel (cc : Fin n → L) :
    Rel (F := 𝟙 Xo.univ.t.G.left) x x
      (gfpW xc cc : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) (tvec (x := xc) cc) := by
  show gfpVec x xc cc ≫ 𝟙 _ = (tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x
  rw [Category.comp_id]
  rfl

theorem gfp_tan (hx : IsUnivChart _ n xc) (cc : Fin n → L) : IsTanAt x (gfpVec x xc cc) := by
  refine ⟨gfpVec_w cc, ?_⟩
  have h1 : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x := xc) cc = 1 := ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc
  have e1 : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x := xc) cc).left =
      (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left := by
    rw [h1]
  have e2 : (pushHom (isGrpPullback_pullback Xo.univ.t.G x) (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L) 1).left =
      (1 : Over.mk ((ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom ≫ x) ⟶ Xo.univ.t.G).left := by
    rw [map_one]
  change (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫
    pullback.fst Xo.univ.t.G.hom x = _ at e2
  show spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ ((tvec (x := xc) cc).left ≫
    pullback.fst Xo.univ.t.G.hom x) = _
  rw [← Category.assoc]
  change (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x = _
  rw [e1, e2, ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']
  simp

theorem gfp_exists (hx : IsUnivChart _ n xc) (w : Sp (DualNumber L) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) :
    ∃ cc, w = gfpVec x xc cc := by
  obtain ⟨hw1, hw2⟩ := hw
  let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L) ⟶ (Over.pullback x).obj Xo.univ.t.G :=
    Over.homMk (pullback.lift w (spMap (algebraMap L (DualNumber L))) hw1) (pullback.lift_snd _ _ hw1)
  have e2 : (pushHom (isGrpPullback_pullback Xo.univ.t.G x) (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L) 1).left =
      (1 : Over.mk ((ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom ≫ x) ⟶ Xo.univ.t.G).left := by
    rw [map_one]
  change (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫
    pullback.fst Xo.univ.t.G.hom x = _ at e2
  have e3 : (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫
      pullback.fst Xo.univ.t.G.hom x = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    rw [e2, ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']
    simp
  have hy : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y := by
    show ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y = 1
    ext
    apply pullback.hom_ext
    · rw [e3]
      change (spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫
        pullback.lift w (spMap (algebraMap L (DualNumber L))) hw1) ≫ pullback.fst Xo.univ.t.G.hom x = _
      rw [Category.assoc, pullback.lift_fst]
      exact hw2
    · have a1 : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y).left ≫ pullback.snd Xo.univ.t.G.hom x =
          (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom := by
        simpa using Over.w (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y)
      have a2 : (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫
          pullback.snd Xo.univ.t.G.hom x = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom := by
        simpa using Over.w (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G)
      rw [a1, a2]
  refine ⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy, ?_⟩
  have e : y = tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy) := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx y hy
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec y hy
  show w = (tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy)).left ≫ pullback.fst Xo.univ.t.G.hom x
  rw [← e]
  exact (pullback.lift_fst _ _ _).symm

theorem gfp_inj (hx : IsUnivChart _ n xc) {c₁ c₂ : Fin n → L} (h : gfpVec x xc c₁ = gfpVec x xc c₂) : c₁ = c₂ := by
  have hw : ∀ c : Fin n → L,
      (tvec (x := xc) c).left ≫ pullback.snd Xo.univ.t.G.hom x = spMap (algebraMap L (DualNumber L)) :=
    fun c => by simpa using Over.w (tvec (x := xc) c)
  have h' : (tvec (x := xc) c₁).left ≫ pullback.fst Xo.univ.t.G.hom x =
      (tvec (x := xc) c₂).left ≫ pullback.fst Xo.univ.t.G.hom x := h
  have ht : tvec (x := xc) c₁ = tvec (x := xc) c₂ :=
    Over.OverMorphism.ext (pullback.hom_ext h' (by rw [hw, hw]))
  first
  | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx ht
  | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj ht

theorem gfp_eig_iff [Algebra c.F L] (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) (cc : Fin n → L) :
    IsEigAt c τ (gfpVec x xc cc) ↔
      cc ∈ eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) (fun a => algebraMap c.F L (embK c τ a)) := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
  refine forall_congr' fun a => ?_
  rw [← ReciprocityTheory.ChartRestriction.G.Chart.tvec_eig_iff hx]
  exact ReciprocityTheory.ChartRestriction.G.Chart.eig_iff gfp_hcId (Xo.univ.t.act.act a) (Xo.univ.t.act.act a)
    (by rw [Category.comp_id, Category.id_comp]) _ (gfp_rel xc cc)

theorem gfp_tvec_sum (hx : IsUnivChart _ n xc) {m : ℕ} (a : Fin m → L) (e : Fin m → Fin n → L) :
    tvec (x := xc) (∑ j, a j • e j) =
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)).prod := by
  have h0 : tvec (x := xc) (0 : Fin n → L) = 1 := by
    have e0 := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → L) 0
    rw [add_zero] at e0
    simpa using e0.symm
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ← ih, Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx]

theorem gfp_comb_iff (hx : IsUnivChart _ n xc) {m : ℕ} (e : Fin m → Fin n → L) (a : Fin m → L) (cc : Fin n → L) :
    IsCombAt x (fun j => gfpVec x xc (e j)) a (gfpVec x xc cc) ↔ cc = ∑ j, a j • e j := by
  have hg : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  let W' : Fin m → (viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) := fun j =>
    liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j))) ≫
      (gfpW xc (e j) : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G)
  have hW' : ∀ j, Rel (F := 𝟙 Xo.univ.t.G.left) x x (W' j)
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)) :=
    fun j => ReciprocityTheory.ChartRestriction.G.Chart.rel_pre _ (gfp_rel xc (e j))
  have hP := ReciprocityTheory.ChartRestriction.G.Chart.rel_prod gfp_hcId hg W' _ hW'
  rw [← gfp_tvec_sum hx a e] at hP
  constructor
  · rintro ⟨u, hu, hprod⟩
    have eu' : u = W' := funext fun j => Over.OverMorphism.ext (hu j)
    have eu : (List.ofFn W').prod =
        (gfpW xc cc : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) := by
      rw [← eu']
      exact Over.OverMorphism.ext hprod
    rw [eu] at hP
    exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (ReciprocityTheory.ChartRestriction.G.Chart.rel_uniq_v (gfp_rel xc cc) hP)
  · intro h
    subst h
    refine ⟨W', fun j => rfl, ?_⟩
    exact congrArg (fun q => q.left) (ReciprocityTheory.ChartRestriction.G.Chart.rel_uniq_w gfp_hcId hP (gfp_rel xc _))

end V

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Clauses

variable (Xo : Moduli Dw l) (c : Coeff l)

def FrChartF : Prop :=
  FrChart (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)

def BorChartF : Prop :=
  BorChart (K := c.F) (ι := Ix Dw) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')

end Clauses

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem evalWD_fr (h : FrChartF Xo c) :
    EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
  evalWD_of_frChart h

theorem wtField_of_borChart (h : BorChartF Xo c) : WtField Xo c := by
  intro a n f hf S _ _ t y y' hy hy' hb
  exact wtAll_of_borChart h (ex Dw a n) hf.1 hf.2 S t y y' hy hy' hb

theorem unitIndep_of_charts (h : BorChartF Xo c) (hL : IntLatU Xo c) : UnitIndep Xo c :=
  unitIndep_of (wtField_of_borChart h) (intDiagUnit_of hL)

end Proofs

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

lemma arcι_X_isUnit (Dw : Datum H) (K₁ : Type) [Field K₁] : IsUnit (arcι Dw K₁ PowerSeries.X) := by
  have h : IsUnit (HahnSeries.ofPowerSeries ℤ K₁ PowerSeries.X) := by
    rw [isUnit_iff_ne_zero]
    first
      | (rw [HahnSeries.ofPowerSeries_X]; exact HahnSeries.single_ne_zero one_ne_zero)
      | (intro h0
         exact PowerSeries.X_ne_zero ((map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).mp h0))
      | (simp; done)
  exact (h.map (MvPolynomial.C (σ := ArcLt Dw))).map
    (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁))

lemma arc_pt_X (Dw : Datum H) (K₁ : Type) [Field K₁] (q : Sp (ArcS Dw K₁)) :
    PowerSeries.X ∉ ((spMap (arcι Dw K₁)) q).asIdeal := by
  intro hX
  have h1 : arcι Dw K₁ PowerSeries.X ∈ q.asIdeal := by
    first
      | exact hX
      | (simpa using hX)
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (arcι_X_isUnit Dw K₁))

theorem arcPt_point (Y : Model Xo c β) {K₁ : Type} [Field K₁] (b : O →+* K₁) [Algebra c.F (ArcS Dw K₁)]
    (hcomp : (algebraMap c.F (ArcS Dw K₁)).comp β = (arcι Dw K₁).comp ((PowerSeries.C (R := K₁)).comp b))
    (χ : Sp (PowerSeries K₁) ⟶ Y.X) (hχs : χ ≫ Y.s = spMap (PowerSeries.C (R := K₁)) ≫ spMap b)
    (hj : ∀ x : Sp (PowerSeries K₁), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) :
    ∃ z : Sp (ArcS Dw K₁) ⟶ Xo.XF c, z ≫ Y.j = spMap (arcι Dw K₁) ≫ χ ∧
      z ≫ Y.jQ ≫ pullback.snd _ _ = spMap (algebraMap c.F (ArcS Dw K₁)) := by
  haveI := Y.jQ_open
  have hw : (spMap (arcι Dw K₁) ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcS Dw K₁)) ≫ spMap β := by
    rw [Category.assoc, hχs, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]
  let g : Sp (ArcS Dw K₁) ⟶ pullback Y.s (spMap β) :=
    pullback.lift (spMap (arcι Dw K₁) ≫ χ) (spMap (algebraMap c.F (ArcS Dw K₁))) hw
  have hg : Set.range g ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen]
    have e1 : (pullback.fst Y.s (spMap β)) (g q) = χ ((spMap (arcι Dw K₁)) q) := by
      have := congrArg (fun f : Sp (ArcS Dw K₁) ⟶ Y.X => f q) (pullback.lift_fst _ _ hw)
      first
        | exact this
        | (simpa using this)
    show (pullback.fst Y.s (spMap β)) (g q) ∈ abLocus Y.t.G
    rw [e1]
    obtain ⟨p, hp⟩ := hj _ (arc_pt_X Dw K₁ q)
    rw [← hp]
    have h2 : Y.jQ p ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]
      exact ⟨p, rfl⟩
    exact h2
  refine ⟨IsOpenImmersion.lift Y.jQ g hg, ?_, ?_⟩
  · show IsOpenImmersion.lift Y.jQ g hg ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

end Formalism.L2.Pj
end
end
