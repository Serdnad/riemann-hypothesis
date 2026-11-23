module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle027
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointnessSeriesTransportFrames
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle072
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSecondPartialLaw
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.chart_law_action_eq_transported_of_coordRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ φi : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) ∧ ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ) := by
  first | exact @GlobalTheory.ChartCmp.law_act_of_coordRel | exact GlobalTheory.ChartCmp.law_act_of_coordRel | (intros; apply GlobalTheory.ChartCmp.law_act_of_coordRel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.pushChartAlt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), ∃ x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G, (∀ m, (x' m).left = (x m).left ≫ n.φ) ∧ (GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x') ∧ (∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V), IsChartG t (𝟙 (Sp V)) d F act tg uv x → IsChartG t' (𝟙 (Sp V)) d F act (fun l => tg l ≫ n.φ) uv x') ∧ ∀ (u : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u (v ≫ n.φ) := by
  first | exact @GlobalTheory.PushChart.pushChart | exact GlobalTheory.PushChart.pushChart | (intros; apply GlobalTheory.PushChart.pushChart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.tangentDirection_two_charts_linearPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by
  first | exact @GlobalTheory.ChartCmp.CoordDir.coord_dir | exact GlobalTheory.ChartCmp.CoordDir.coord_dir | (intros; apply GlobalTheory.ChartCmp.CoordDir.coord_dir <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.exists_coordinateRelation_universalJets : ∀ (V : Type) [CommRing V] (G : Over (Sp V)) [GrpObj G] (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x' → ∃ φ φi : Pt V 1 d, IsInvPair φ φi ∧ CoordRel x x' φ ∧ CoordRel x' x φi := by
  first | exact @GlobalTheory.ChartCmp.exists_coordRel_of_isUnivJ | exact GlobalTheory.ChartCmp.exists_coordRel_of_isUnivJ | (intros; apply GlobalTheory.ChartCmp.exists_coordRel_of_isUnivJ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.adjointness_series_transport_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ad : 𝓞 E → PS V 2 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamAd t (𝟙 (Sp V)) d x act ad e → FamAd t' (𝟙 (Sp V)) d x' act ad e' := by
  first | exact @GlobalTheory.ChartCmp.PushAd.famAd_push | exact GlobalTheory.ChartCmp.PushAd.famAd_push | (intros; apply GlobalTheory.ChartCmp.PushAd.famAd_push <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.exists_pushFr_of_isGen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), w.IsGen → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m, PushFr n w x x' e e' := by
  first | exact @GlobalTheory.ChartCmp.exists_pushFr | exact GlobalTheory.ChartCmp.exists_pushFr | (intros; apply GlobalTheory.ChartCmp.exists_pushFr <;> assumption)
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem constantCoeff_DpolyN_jEq : ∀ (k : Type) [CommRing k] (d n : ℕ) (F : Fin d → PS k 2 d) (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (m : ℕ) (f g : PS k n d), P.totalDegree ≤ m → JEq m f g → MvPowerSeries.constantCoeff (DpolyN F cp u P f) = MvPowerSeries.constantCoeff (DpolyN F cp u P g) := by
  intro k _ d n F Ix _ cp u P m f g hP hfg
  classical
  rw [GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq F cp u P f _ subset_rfl,
    GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq F cp u P g _ subset_rfl]
  refine Finset.sum_congr rfl fun e he => ?_
  congr 1
  refine GlobalTheory.PowGerm.NabJet.constantCoeff_DmonN_congr F cp u e f g fun mo hmo => ?_
  refine hfg mo (hmo.trans (le_trans ?_ hP))
  have := MvPolynomial.le_totalDegree he
  rwa [Finsupp.degree_apply]

end GlobalTheory.ChartCmp
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.PushFirstLaw

section Val
variable {X X' Y Z : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
  (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι)

def isoVal (ψ : Z ⟶ X') : (Z.presheaf.stalk z)ˣ :=
  gm ψ z ((LB.div (L.pull F) L').U (fun _ => J (ψ ≫ F), J' ψ)) (w.s (fun _ => J (ψ ≫ F), J' ψ))

variable {w z J J'}

theorem val_maps (hJ : Good L z J) (hJ' : Good L' z J') {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}
    {g : LB.Gen (LB.LinComb L' φ ε)} {b : LB.Gen (LB.LinComb (L.pull F) φ ε)}
    (h : LB.Gen.Maps (LB.linCombIso w φ ε) g b) (r : Z ⟶ Y) :
    gm r z (LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F)) (b.s fun k _ => J ((r ≫ φ k) ≫ F)) =
      (∏ k, isoVal w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  have h1 : r z ∈ LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ φ k) ≫ F)
  have hm : r z ∈ LB.wchart (L.pull F) φ (fun k _ => J ((r ≫ φ k) ≫ F)) ⊓ LB.wchart L' φ (fun k => J' (r ≫ φ k)) :=
    ⟨h1, hJ'.mem φ r⟩
  refine (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _)
    (h (fun k _ => J ((r ≫ φ k) ≫ F), fun k => J' (r ≫ φ k)))).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have ha : (φ a) (r z) ∈ (L.pull F).U (fun _ => J ((r ≫ φ a) ≫ F)) ⊓ L'.U (J' (r ≫ φ a)) :=
    ⟨LB.wchart_le (L.pull F) φ _ a hm.1, LB.wchart_le L' φ _ a hm.2⟩
  exact (gm_res r z _ hm _).trans (gm_pull r (φ a) z _ ha _)

theorem val_carries (hJ : Good L z J) (hJ' : Good L' z J') {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}
    {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)}
    (h : Carries L F w φ ε g g') (r : Z ⟶ Y) :
    val g' r z J = (∏ k, isoVal w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  refine Eq.trans ?_ (val_maps hJ hJ' h r)
  rw [val_of g' r z J (fun k => J ((r ≫ φ k) ≫ F)) (fun k => by rw [Category.assoc])]
  have h1 : r z ∈ LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ φ k) ≫ F)
  exact (gm_res r z _ h1 _).symm

end Val

section Cube
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem val_theta (m : CubeMap G' G) {L : LB G.left} {L' : LB G'.left} {w : LB.Iso L' (L.pull m.F)}
    {c : LB.Gen (Theta G L)} {c' : LB.Gen (Theta G' L')}
    (h : LB.Gen.Maps (LB.linCombIso w (thφ G' (x3 G')) thε) c' (m.thetaPull L c))
    {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ G.left) → L.ι} {J' : (Z ⟶ G'.left) → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J')
    (r : Z ⟶ (G3 G').left) :
    val (φ := thφ G (x3 G)) (ε := thε) c (r ≫ m.F3) z J =
      (∏ k, isoVal w z J J' (r ≫ thφ G' (x3 G') k) ^ thε k) * val (φ := thφ G' (x3 G')) (ε := thε) c' r z J' := by
  refine Eq.trans ?_ (val_maps hJ hJ' h r)
  have e : ∀ k : thK, (r ≫ m.F3) ≫ thφ G (x3 G) k = (r ≫ thφ G' (x3 G') k) ≫ m.F := fun k => by
    rw [Category.assoc, Category.assoc]
    exact congrArg (r ≫ ·) (m.psum_comm k.down).symm
  refine (val_of (φ := thφ G (x3 G)) (ε := thε) c (r ≫ m.F3) z J (fun k => J ((r ≫ thφ G' (x3 G') k) ≫ m.F))
    (fun k => by rw [e])).trans ?_
  have h1 : r z ∈ LB.wchart (L.pull m.F) (thφ G' (x3 G')) fun k _ => J ((r ≫ thφ G' (x3 G') k) ≫ m.F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ thφ G' (x3 G') k) ≫ m.F)
  exact ((gm_res r z _ h1 _).trans (gm_pull r m.F3 z _ (m.theta_le L _ h1) _)).symm

end Cube

theorem lift_cubeMap {S : Scheme.{0}} {G' G T : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (m : CubeMap G' G) (a : Fin 3 → (T ⟶ G')) (b : Fin 3 → (T ⟶ G)) (h : ∀ i, (b i).left = (a i).left ≫ m.F) :
    (lift (b 0) (lift (b 1) (b 2))).left = (lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3 := by
  have k : ∀ i : Fin 3, (x3 G' i).left ≫ m.F = m.F3 ≫ (x3 G i).left := fun i => by
    have e := m.psum_comm {i}
    have p : psum G (x3 G) {i} = x3 G i * 1 := by fin_cases i <;> rfl
    have p' : psum G' (x3 G') {i} = x3 G' i * 1 := by fin_cases i <;> rfl
    rwa [p, p', _root_.mul_one, _root_.mul_one] at e
  have la : ∀ i : Fin 3, lift (a 0) (lift (a 1) (a 2)) ≫ x3 G' i = a i := fun i => by
    fin_cases i <;> simp [x3]
  have k' : ∀ i : Fin 3, ((lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3) ≫ (x3 G i).left = (b i).left := fun i => by
    rw [Category.assoc, ← k, ← Category.assoc, ← Over.comp_left, la, h]
  let q : T ⟶ G3 G := Over.homMk ((lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3) (by
    rw [← Over.w (x3 G 0), ← Category.assoc, k', Over.w])
  have hq : ∀ i : Fin 3, q ≫ x3 G i = b i := fun i => Over.OverMorphism.ext (k' i)
  have : lift (b 0) (lift (b 1) (b 2)) = q := by
    refine CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (hq 0).symm) ?_
    rw [lift_snd]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [lift_fst, Category.assoc]; exact (hq 1).symm
    · rw [lift_snd, Category.assoc]; exact (hq 2).symm
  rw [this]
  rfl

theorem rearrange {U : Type} [CommGroup U] (a b c u p q r : U) :
    a * (b⁻¹ * c⁻¹) * (u * (p * (q⁻¹ * r⁻¹))) = u * (a * p * ((b * q)⁻¹ * (c * r)⁻¹)) := by
  simp only [mul_inv]
  ac_rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem val_scaleG {X0 : Scheme.{0}} (t : SAB H X0) {Y Z : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)


open GlobalTheory.SecondPartialLaw in
theorem formal_sum {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uv : κ → Fin d → S} (hch : IsChartG t x0 d F act tg uv x) (m : ℕ)
    {U : Type} [CommGroup U] (h : ((jOG x0 d m 3).left ⟶ t.G.left) → U)
    (P : (Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) → U)
    (hP : ∀ φ, P φ = ∏ k, h ((Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] k) ^ cε 2 k) :
    ∏ k : thK.{0}, h ((lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left ≫
        thφ t.G (x3 t.G) k) ^ thε k =
      P ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] *
        ((P ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])⁻¹ *
          (P ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])⁻¹) := by
  have hP' : ∀ (φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (a b : jOG x0 d m 3 ⟶ t.G),
      Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 0 p.2)) ≫ x m = a →
      Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 1 p.2)) ≫ x m = b →
      P φ = h (1 : jOG x0 d m 3 ⟶ t.G).left * (h a.left)⁻¹ * (h b.left)⁻¹ * h (b * a).left := by
    rintro φ _ _ rfl rfl
    rw [← pt_sub m φ 0, ← pt_sub m φ 1]
    have e1 := Finset.prod_congr (s₁ := Finset.univ) rfl fun (k : ULift.{0} (Finset (Fin 2))) _ =>
      congrArg (fun q => h q ^ cε 2 k) (pe_pt (t := t) (x := x) m (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) k)
    have e2 := prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)
      ![Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m (0 : Fin 2),
        Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m (1 : Fin 2)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one] at e2
    exact (hP φ).trans (e1.trans e2)
  rw [hP' ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _
      (pt_law hch m ![0, 1]) (pt_X m 2),
    hP' ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _ (pt_X m 0) (pt_X m 2),
    hP' ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _ (pt_X m 1) (pt_X m 2)]
  refine (Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ thε k) (th_pt _ _ _ k)).trans
    ((prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left) _).trans ?_)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, _root_.mul_one]
  generalize jptG t x0 d x m (0 : Fin 3) = a
  generalize jptG t x0 d x m (1 : Fin 3) = b
  generalize jptG t x0 d x m (2 : Fin 3) = c
  rw [_root_.mul_comm c (a * b), _root_.mul_comm c a, _root_.mul_comm c b, _root_.mul_assoc a b c]
  apply ofMul_eq
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.PushFirstLaw

namespace GlobalTheory

open PushFirstLaw

theorem famPh1_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh1 t (𝟙 (Sp V)) d x F ph e → FamPh1 t' (𝟙 (Sp V)) d x' F ph e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' hw hx _ hp F act κ _ tg uv ph hch h m
  obtain ⟨u, hu, hcor⟩ := h m
  obtain ⟨-, c, -, hc, hcar⟩ := hp m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J hJ => ?_⟩
  obtain ⟨J', hJ', -⟩ := exists_good t.PP.L t.PP.isLB y (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim)
    (fun a => a.elim)
  have k := val_corr hJ' hcor (𝟙 _)
  have hpe : ∀ φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V,
      val (peG t' (𝟙 (Sp V)) d x' e' m φ) (𝟙 _) y J =
        (∏ k, isoVal w y J J' ((Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
          cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] k) ^ cε 2 k) *
          val (peG t (𝟙 (Sp V)) d x e m φ) (𝟙 _) y J' := fun φ => by
    refine (val_pull hJ _ _ _).trans ((val_corr hJ hc _).symm.trans ((val_carries hJ hJ' hcar _).trans
      (congrArg₂ (· * ·) ?_ (val_pull hJ' _ _ _).symm)))
    rw [Category.id_comp]
  have hl := lift_cubeMap n.cm (fun i => jptG t (𝟙 (Sp V)) d x m i) (fun i => jptG t' (𝟙 (Sp V)) d x' m i) (fun i => by
    simp only [jptG, Over.comp_left, hx m, Category.assoc])
  have hs := formal_sum hch m (isoVal w y J J') _ (fun _ => rfl)
  have k2 := (val_pull hJ' _ _ _).symm.trans (k.trans ((val_scaleG t hJ' _ _ _).trans (congrArg (_ * ·)
    ((val_mul hJ' _ _ _).trans (congrArg (_ * ·) ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))))
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_scaleG t' hJ _ _ _).trans (congrArg (_ * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hpe _) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) (hpe _)))
        ((val_inv _ _).trans (congrArg (·⁻¹) (hpe _))))))))).symm)
  refine (congrArg (fun r => val (φ := thφ t'.G (x3 t'.G)) (ε := thε) t'.cub.t r y J)
    ((Category.id_comp _).trans hl)).trans ((val_theta n.cm hw.2 hJ hJ' _).trans ((congrArg₂ (· * ·) hs
      ((congrArg (fun r => val (φ := thφ t.G (x3 t.G)) (ε := thε) t.cub.t r y J') (Category.id_comp _)).symm.trans k2)).trans
        (rearrange _ _ _ _ _ _ _)))

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.PushSecondLaw

open MvPolynomial (X)
open GlobalTheory.SecondPartialLaw

section Values

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
  {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {ε : K → ℤ} {z : Z} {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι}

theorem val_pmaps {φ : K → (Y ⟶ X)} {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (H : PMaps w φ' φ ε a t h) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hJ : Good L z J) (hJ' : Good L' z J') (r : Z ⟶ Y') :
    val t (r ≫ h) z J = (∏ k, (fun q => gw w q z (J (q ≫ F)) (J' q)) (r ≫ φ' k) ^ ε k) * val a r z J' := by
  have e := H _ r z (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => J' (r ≫ φ' k)) (fun k => hJ _) (fun k => hJ' _)
  refine Eq.trans ?_ e
  refine val_of _ _ _ _ _ fun k => congrArg J ?_
  rw [Category.assoc, Category.assoc, hc]

theorem val_carries {g : LB.Gen (LB.LinComb L' φ' ε)} {c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)}
    (H : Carries L F w φ' ε g c) (hJ : Good L z J) (hJ' : Good L' z J') (r : Z ⟶ Y') :
    val c r z J = (∏ k, (fun q => gw w q z (J (q ≫ F)) (J' q)) (r ≫ φ' k) ^ ε k) * val g r z J' := by
  have P : PMaps w φ' (fun k => φ' k ≫ F) ε g c (𝟙 Y') :=
    (maps_iff w φ' _ ε g c (𝟙 Y') (flatGen L F φ' ε c) (fun j => wchart_pull_le L F φ' j) (fun j => rfl)).1 H
  have e := val_pmaps P (fun k => (Category.id_comp _).symm) hJ hJ' r
  rwa [Category.comp_id] at e

end Values

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem val_scaleGenG {X0 : Scheme.{0}} (t : SAB H X0) {Y Z : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J)
    (c : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)



theorem prod_second_law {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S} (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ)
    {U : Type} [CommGroup U] (h : ((jOG x0 d m 3).left ⟶ t.G.left) → U)
    (P : (Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) → U)
    (hP : ∀ φ, P φ = ∏ I : ULift.{0} (Finset (Fin 2)), h ((homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I) ^ cε 2 I) :
    ∏ I, h ((lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3))
        (jptG t x0 d x m (0 : Fin 3)))).left ≫ thφ t.G (x3 t.G) I) ^ thε I =
      P ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)] *
        ((P ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])⁻¹ *
          (P ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])⁻¹) := by
  have hQ : ∀ φ, P φ = ∏ I : ULift.{0} (Finset (Fin 2)), h (psum t.G
      ![Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 0 p.2)) ≫ x m,
        Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 1 p.2)) ≫ x m] I.down).left ^ cε 2 I := fun φ => by
    rw [← pt_sub m φ 0, ← pt_sub m φ 1]
    exact (hP φ).trans (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (pe_pt m _ I))
  simp only [hQ, th_pt, Matrix.cons_val_zero, Matrix.cons_val_one, pt_X, pt_law hch]
  erw [prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
  rw [prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left),
    prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left), prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
  have ha2 : jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3) * jptG t x0 d x m (0 : Fin 3) =
      jptG t x0 d x m (1 : Fin 3) * (jptG t x0 d x m (2 : Fin 3) * jptG t x0 d x m (0 : Fin 3)) := _root_.mul_assoc _ _ _
  apply ofMul_eq
  simp only [ofMul_mul, ofMul_inv, _root_.mul_one]
  erw [ha2]
  abel!

theorem lift_comp_cube {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (n : CubeMap G G') {T : Over S} {a b c : T ⟶ G} {a' b' c' : T ⟶ G'} (ha : a'.left = a.left ≫ n.F)
    (hb : b'.left = b.left ≫ n.F) (hc : c'.left = c.left ≫ n.F) :
    (lift a' (lift b' c')).left = (lift a (lift b c)).left ≫ n.F3 := hom_ext_triple _ fun i => by
  rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
  fin_cases i
  · simpa [x3] using ha
  · simpa [x3] using hb
  · simpa [x3] using hc

theorem alg_step {U : Type} [CommGroup U] {θ θ' u A B C A' B' C' p a b c : U} (k : θ = u * (A * (B⁻¹ * C⁻¹)))
    (hθ : θ' = p * θ) (hA : A' = a * A) (hB : B' = b * B) (hC : C' = c * C) (hp : p = a * (b⁻¹ * c⁻¹)) :
    θ' = u * (A' * (B'⁻¹ * C'⁻¹)) := by
  subst k hθ hA hB hC hp
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem famPh2_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh2 t (𝟙 (Sp V)) d x F ph e → FamPh2 t' (𝟙 (Sp V)) d x' F ph e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' hcub hx _ hfr F act κ _ tg uv ph hch h m
  obtain ⟨u, hu, hcor⟩ := h m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J' hJ' => ?_⟩
  choose J hJ using fun χ : (jOG (𝟙 (Sp V)) d m 3).left ⟶ t.G.left => exists_chart t.PP.isLB (χ y)
  replace hJ : Good t.PP.L y J := hJ
  obtain ⟨W, hW⟩ : ∃ W : ((jOG (𝟙 (Sp V)) d m 3).left ⟶ t.G.left) → ((jOG (𝟙 (Sp V)) d m 3).left.presheaf.stalk y)ˣ,
    W = fun q => gw w q y (J' (q ≫ n.φ)) (J q) := ⟨_, rfl⟩
  obtain ⟨-, c, -, hc, hcar⟩ := hfr m
  have hpt : ∀ i : Fin 3, (jptG t' (𝟙 (Sp V)) d x' m i).left = (jptG t (𝟙 (Sp V)) d x m i).left ≫ n.φ := fun i => by
    rw [jptG, jptG, Over.comp_left, Over.comp_left, hx m, Category.assoc]
  have hpe : ∀ φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V,
      val (peG t' (𝟙 (Sp V)) d x' e' m φ) (𝟙 _) y J' =
        (∏ I : ULift.{0} (Finset (Fin 2)), W ((homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
          cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] I) ^ cε 2 I) *
          val (peG t (𝟙 (Sp V)) d x e m φ) (𝟙 _) y J := fun φ => by
    refine (val_pull hJ' _ _ _).trans ((val_corr hJ' hc _).symm.trans ((val_carries hcar hJ' hJ _).trans ?_))
    refine congrArg₂ (· * ·) ?_ (val_pull hJ _ _ _).symm
    rw [hW, Category.id_comp]
  have P : PMaps w (thφ t.G (x3 t.G)) (thφ t'.G (x3 t'.G)) thε t.cub.t t'.cub.t n.cm.F3 :=
    (maps_iff w _ _ thε t.cub.t t'.cub.t n.cm.F3 _ (fun j => n.cm.theta_le t'.PP.L j) (fun j => rfl)).1 hcub.2
  have hθ := val_pmaps P (fun I => n.cm.psum_comm I.down) hJ' hJ
    (lift (jptG t (𝟙 (Sp V)) d x m (1 : Fin 3)) (lift (jptG t (𝟙 (Sp V)) d x m (2 : Fin 3))
      (jptG t (𝟙 (Sp V)) d x m (0 : Fin 3)))).left
  rw [← hW, ← lift_comp_cube n.cm (hpt 1) (hpt 2) (hpt 0)] at hθ
  have k := (val_pull hJ _ _ _).symm.trans ((val_corr hJ hcor (𝟙 _)).trans ((val_scaleGenG t hJ _ _ _).trans
    (congrArg _ ((val_mul hJ _ _ _).trans (congrArg _ ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))))
  rw [Category.id_comp] at k
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ ((val_scaleGenG t' hJ' _ _ _).trans
    (congrArg _ ((val_mul hJ' _ _ _).trans (congrArg _ ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))).symm)
  rw [Category.id_comp]
  exact alg_step k hθ (hpe _) (hpe _) (hpe _) (prod_second_law hch m W _ (fun _ => rfl))

end GlobalTheory.PushSecondLaw
end
end
