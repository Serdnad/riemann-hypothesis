module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle020
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.CarryCalc

variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem carries_iff (w : LB.Iso L' (L.pull F)) (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε))
    (g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) :
    Carries L F w φ ε g g' ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ k ≫ F) p → r z ∈ LB.wchart L' φ q →
        gm r z (LB.wchart L (fun k => φ k ≫ F) p) (g'.s p) = pw w φ ε r z p q * gm r z (LB.wchart L' φ q) (g.s q) := by
  refine (maps_iff w φ (fun k => φ k ≫ F) ε g g' (𝟙 Y) (flatGen L F φ ε g')
    (fun j x hx => wchart_pull_le L F φ j hx) (fun j => rfl)).trans ⟨fun H Z r z p q hp hq => ?_, fun H Z r z p q hp hq => ?_⟩
  · have := H Z r z p q (Set.mem_iInter.1 hp) (Set.mem_iInter.1 hq)
    rw [Category.comp_id] at this
    exact this
  · rw [Category.comp_id]
    exact H Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)

def fac (w : LB.Iso L' (L.pull F)) {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w ψ z (J (ψ ≫ F)) (J' ψ)

theorem val_of_carries {w : LB.Iso L' (L.pull F)} {φ : K → (Y ⟶ X')} {ε : K → ℤ} {g : LB.Gen (LB.LinComb L' φ ε)}
    {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)} (H : Carries L F w φ ε g g') {Z : Scheme.{0}} (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J') :
    val g' r z J = (∏ k, fac w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  refine ((carries_iff w φ ε g g').1 H Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [pw, fac, Category.assoc]

theorem carries_of_val {w : LB.Iso L' (L.pull F)} (hL' : L'.IsLB) (hL : L.IsLB) (hw : w.IsGen) {φ : K → (Y ⟶ X')}
    {ε : K → ℤ} {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)} (hg : g.IsGen)
    (hg' : g'.IsGen) (h : ∀ (y : Y) J J', Good L y J → Good L' y J' →
      val g' (𝟙 Y) y J = (∏ k, fac w y J J' (𝟙 Y ≫ φ k) ^ ε k) * val g (𝟙 Y) y J') : Carries L F w φ ε g g' := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' g hg
  have hc := (carries_iff w φ ε g t).2 hv
  have e : ∀ j, g'.s j = t.s j := fun j => unit_ext fun y hy => by
    choose J hJ using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
    choose J' hJ' using fun ψ : Y ⟶ X' => exists_chart hL' (ψ y)
    have v' : val g' (𝟙 Y) y J = val t (𝟙 Y) y J := (h y J J' hJ hJ').trans (val_of_carries hc (𝟙 Y) hJ hJ').symm
    exact (gen_trans hg' (𝟙 Y) y hy (Good.mem hJ _ (𝟙 Y))).trans ((congrArg _ v').trans
      (gen_trans ht (𝟙 Y) y hy (Good.mem hJ _ (𝟙 Y))).symm)
  obtain ⟨s⟩ := g'
  obtain ⟨s'⟩ := t
  obtain rfl : s = s' := funext e
  exact hc

theorem exists_good' {M : LB X} (hM : M.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good M z J := by
  choose J hJ using fun ψ : Z ⟶ X => exists_chart hM (ψ z)
  exact ⟨J, hJ⟩

end GlobalTheory.ChartCmp.CarryCalc

namespace GlobalTheory.ChartCmp
open CarryCalc

theorem carries_calculus : ∀ (X X' : Scheme.{0}) (L' : LB X') (L : LB X) (F : X' ⟶ X) [Mono F] (w : LB.Iso L' (L.pull F)), L'.IsLB → L.IsLB → w.IsGen → (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)), g.IsGen → ∃ g', g'.IsGen ∧ Carries L F w φ ε g g') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h', LB.SameSum φ ε φ' ε' → g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → (LB.Gen.Corr L' _ _ _ _ g h ↔ LB.Gen.Corr L _ _ _ _ g' h')) ∧ (∀ (Y Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g' (r : Z ⟶ Y) (g'' : LB.Gen (LB.LinComb L (fun k => (r ≫ φ k) ≫ F) ε)), g.IsGen → g'.IsGen → g''.IsGen → Carries L F w φ ε g g' → LB.Gen.Corr L _ _ _ _ g'' (LB.pullGen L _ _ g' r) → Carries L F w (fun k => r ≫ φ k) ε (LB.pullGen L' φ ε g r) g'') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h' (p : LB.Gen (LB.LinComb L (fun k => Sum.elim φ φ' k ≫ F) (Sum.elim ε ε'))), g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → p.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → LB.Gen.Corr L _ _ _ _ p (LB.mulGen L _ _ _ _ g' h') → Carries L F w (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L' _ _ _ _ g h) p) ∧ (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g', Carries L F w φ ε g g' → Carries L F w φ (fun k => - ε k) (LB.invGen L' φ ε g) (LB.invGen L _ ε g')) := by
  intro X X' L' L F _ w hL' hL hw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Y K _ φ ε g hg
    obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' g hg
    exact ⟨t, ht, (carries_iff w φ ε g t).2 hv⟩
  · intro Y K K' _ _ φ ε φ' ε' g h g' h' hs _ _ _ _ Hg Hh
    have key : ∀ (y : Y) J J', Good L y J → Good L' y J' →
        (val g (𝟙 Y) y J' = val h (𝟙 Y) y J' ↔ val g' (𝟙 Y) y J = val h' (𝟙 Y) y J) := fun y J J' hJ hJ' => by
      rw [val_of_carries Hg (𝟙 Y) hJ hJ', val_of_carries Hh (𝟙 Y) hJ hJ',
        DVR.prod_zpow_of_sameSum φ ε φ' ε' hs (fun ψ => fac w y J J' (𝟙 Y ≫ ψ)), mul_right_inj]
    refine ⟨fun C => corr_of_val hL fun y J hJ => ?_, fun C => corr_of_val hL' fun y J' hJ' => ?_⟩
    · obtain ⟨J', hJ'⟩ := exists_good' hL' y
      exact (key y J J' hJ hJ').1 (val_corr hJ' C _)
    · obtain ⟨J, hJ⟩ := exists_good' hL y
      exact (key y J J' hJ hJ').2 (val_corr hJ C _)
  · intro Y Z K _ φ ε g g' r g'' hg _ hg'' H C
    refine carries_of_val hL' hL hw (DVR.pullGen_isGen _ _ _ _ hg r) hg'' fun y J J' hJ hJ' => ?_
    rw [val_corr hJ C, val_pull hJ, val_pull hJ', val_of_carries H _ hJ hJ']
    simp only [Category.assoc]
  · intro Y K K' _ _ φ ε φ' ε' g h g' h' p hg hh _ _ hp Hg Hh C
    refine carries_of_val hL' hL hw (DVR.mulGen_isGen _ _ _ _ _ _ _ hg hh) hp fun y J J' hJ hJ' => ?_
    rw [val_corr hJ C, val_mul hJ, val_mul hJ', val_of_carries Hg _ hJ hJ', val_of_carries Hh _ hJ hJ',
      Fintype.prod_sum_type, _root_.mul_mul_mul_comm]
    rfl
  · intro Y K _ φ ε g g' H
    refine (carries_iff w φ _ _ _).2 fun Z r z p q hp hq => ?_
    refine (map_inv _ _).trans ((congrArg (·⁻¹) ((carries_iff w φ ε g g').1 H Z r z p q hp hq)).trans ?_)
    refine (mul_inv _ _).trans (congrArg₂ (· * ·) ?_ (map_inv _ _).symm)
    simp only [pw, zpow_neg, Finset.prod_inv_distrib]

end GlobalTheory.ChartCmp
end
end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ChartCmp.Axes

variable {R : Type} [CommRing R]

theorem jEq_iff_order {σ : Type} (m : ℕ) (f g : MvPowerSeries σ R) :
    JEq m f g ↔ ((m + 1 : ℕ) : ℕ∞) ≤ MvPowerSeries.order (f - g) := by
  constructor
  · intro h
    refine MvPowerSeries.nat_le_order fun e he => ?_
    rw [map_sub, h e (by omega), sub_self]
  · intro h e he
    have : MvPowerSeries.coeff e (f - g) = 0 :=
      MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le he) h)
    rwa [map_sub, sub_eq_zero] at this

theorem jEq_mul_right {σ : Type} {m : ℕ} {f g : MvPowerSeries σ R} (u : MvPowerSeries σ R) (h : JEq m f g) :
    JEq m (f * u) (g * u) := by
  rw [jEq_iff_order] at h ⊢
  rw [← sub_mul]
  exact h.trans (le_self_add.trans MvPowerSeries.le_order_mul)

theorem jEq_ev {d n n' m : ℕ} (a : Fin n → Pt R n' d) (ha : ∀ j, GP (a j)) {f g : PS R n d} (h : JEq m f g) :
    JEq m (ev a f) (ev a g) := by
  classical
  intro e he
  unfold ev
  rw [MvPowerSeries.coeff_subst (gt_hasSubst a ha), MvPowerSeries.coeff_subst (gt_hasSubst a ha)]
  refine finsum_congr fun c => ?_
  by_cases hc : c.degree ≤ m
  · rw [h c hc]
  · have : MvPowerSeries.coeff e (c.prod fun s k => (a s.1 s.2) ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_prod _ _)
      have h1 : ((c.degree : ℕ) : ℕ∞) ≤ ∑ s ∈ c.support, MvPowerSeries.order ((a s.1 s.2) ^ c s) := by
        rw [Finsupp.degree_apply, Nat.cast_sum]
        refine Finset.sum_le_sum fun s _ => ?_
        exact MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (ha s.1 s.2)
      refine lt_of_lt_of_le ?_ h1
      exact_mod_cast (by omega : e.degree < c.degree)
    rw [this, smul_zero, smul_zero]

theorem jEq_one_of_idem {σ : Type} {m : ℕ} {e : MvPowerSeries σ R} (hu : IsUnit (MvPowerSeries.constantCoeff e))
    (h : JEq m e (e * e)) : JEq m e 1 := by
  obtain ⟨u, rfl⟩ := MvPowerSeries.isUnit_iff_constantCoeff.2 hu
  have := jEq_mul_right (↑u⁻¹ : MvPowerSeries σ R) h
  rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one] at this
  exact fun e he => (this e he).symm

theorem vec3 {d m n : ℕ} (V : Fin m → Pt R n d) (a b c : Pt R m d) :
    (fun j => evP V (![a, b, c] j)) = ![evP V a, evP V b, evP V c] := by
  funext j; fin_cases j <;> rfl

theorem addOf_zero {d n : ℕ} (F : Fin d → PS R 2 d) (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) :
    addOf F (0 : Pt R n d) 0 = 0 := by
  funext i
  change MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![(0 : Pt R n d), 0] p.1) p.2) (F i) = 0
  have e : (fun p : Fin 2 × Fin d => (![(0 : Pt R n d), 0] p.1) p.2) = 0 := by
    funext p
    obtain ⟨j, l⟩ := p
    fin_cases j <;> rfl
  rw [e]
  exact MvPowerSeries.subst_zero_of_constantCoeff_zero (hF i)

theorem ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one {d n : ℕ} (f : PS R 3 d) (hf : ev (n := 2) ![0, pt R d 0, pt R d 1] f = 1) (z : Pt R n d) (hz : GP z) :
    ev ![0, 0, z] f = 1 := by
  have hV : ∀ j, GP (![(0 : Pt R n d), z] j) := pair_points_zero_constant gp_zero₂ hz
  have := congrArg (ev ![0, z]) hf
  rw [gt_ev_ev' _ _ hV (triple_points_zero_constant gp_zero₂ (gp_pt 0) (gp_pt 1)), vec3, evP_zero _ hV, evP_pt _ hV,
    evP_pt _ hV, ev_one] at this
  exact this

theorem ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one {d n : ℕ} (f : PS R 3 d) (hf : ev (n := 2) ![pt R d 0, pt R d 1, 0] f = 1) (z : Pt R n d) (hz : GP z) :
    ev ![z, 0, 0] f = 1 := by
  have hV : ∀ j, GP (![z, (0 : Pt R n d)] j) := pair_points_zero_constant hz gp_zero₂
  have := congrArg (ev ![z, 0]) hf
  rw [gt_ev_ev' _ _ hV (triple_points_zero_constant (gp_pt 0) (gp_pt 1) gp_zero₂), vec3, evP_zero _ hV, evP_pt _ hV,
    evP_pt _ hV, ev_one] at this
  exact this

end GlobalTheory.ChartCmp.Axes


open GlobalTheory.ChartCmp.Axes in
theorem GlobalTheory.ChartCmp.jRel_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d), JRel m B B' φ φi ε → MvPowerSeries.constantCoeff ε = 1 ∧ JEq m (ev (n := 1) ![0, pt R (n := 1) d 0] ε) 1 ∧ JEq m (ev (n := 1) ![pt R (n := 1) d 0, 0] ε) 1 := by
  intro R _ d O _ _ m B B' φ φi ε h
  have hφ : GP φ := h.inv.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt R (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt R n d) := gp_zero₂
  have hc : ∀ {n : ℕ} (j : Fin n), GP (comp1 φ (pt R (n := n) d j)) := fun j => gp_comp1 φ _ hφ (hp j)
  have h1 : JEq m (ev (n := 1) ![0, pt R (n := 1) d 0] ε) 1 := by
    have hV : ∀ j, GP (![(0 : Pt R 1 d), 0, pt R (n := 1) d 0] j) := triple_points_zero_constant hz hz (hp 0)
    have H := jEq_ev _ hV h.ph1
    rw [gt_ev_mul _ hV, gt_ev_mul _ hV, gt_ev_mul _ hV, ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one _ B'.cocycleLeft_zero_fst _ (hp 0), _root_.one_mul,
      gt_ev_ev' _ _ hV (pair_points_zero_constant (gp_addOf _ B'.G.const _ _ (hp 0) (hp 1)) (hp 2)),
      gt_ev_ev' _ _ hV (triple_points_zero_constant (hc 0) (hc 1) (hc 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 2)), vec3, eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 0) (hp 1), evP_comp1 _ hV _ _ (hp 0), evP_comp1 _ hV _ _ (hp 1),
      evP_comp1 _ hV _ _ (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at H
    change JEq m (ev ![addOf B'.G.F 0 0, pt R (n := 1) d 0] ε)
      (ev ![comp1 φ 0, comp1 φ 0, comp1 φ (pt R (n := 1) d 0)] B.ph1 *
        (ev ![0, pt R (n := 1) d 0] ε * ev ![0, pt R (n := 1) d 0] ε)) at H
    rw [addOf_zero _ B'.G.const, gt_comp1_zero φ hφ, ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one _ B.cocycleLeft_zero_fst _ (hc 0), _root_.one_mul] at H
    refine jEq_one_of_idem ?_ H
    rw [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0))]
    exact h.unit
  have h2 : JEq m (ev (n := 1) ![pt R (n := 1) d 0, 0] ε) 1 := by
    have hV : ∀ j, GP (![pt R (n := 1) d 0, (0 : Pt R 1 d), 0] j) := triple_points_zero_constant (hp 0) hz hz
    have H := jEq_ev _ hV h.ph2
    rw [gt_ev_mul _ hV, gt_ev_mul _ hV, gt_ev_mul _ hV, ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one _ B'.cocycleRight_zero_thd _ (hp 0), _root_.one_mul,
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (gp_addOf _ B'.G.const _ _ (hp 1) (hp 2))),
      gt_ev_ev' _ _ hV (triple_points_zero_constant (hc 0) (hc 1) (hc 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 1)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)), vec3, eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 1) (hp 2), evP_comp1 _ hV _ _ (hp 0), evP_comp1 _ hV _ _ (hp 1),
      evP_comp1 _ hV _ _ (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at H
    change JEq m (ev ![pt R (n := 1) d 0, addOf B'.G.F 0 0] ε)
      (ev ![comp1 φ (pt R (n := 1) d 0), comp1 φ 0, comp1 φ 0] B.ph2 *
        (ev ![pt R (n := 1) d 0, 0] ε * ev ![pt R (n := 1) d 0, 0] ε)) at H
    rw [addOf_zero _ B'.G.const, gt_comp1_zero φ hφ, ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one _ B.cocycleRight_zero_thd _ (hc 0), _root_.one_mul] at H
    refine jEq_one_of_idem ?_ H
    rw [gt_const_ev_eq _ (pair_points_zero_constant (hp 0) hz)]
    exact h.unit
  refine ⟨?_, h1, h2⟩
  have := h1 0 (by simp)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_one] at this
  exact this
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Chart.FrameUp

theorem cube_points_push {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G)
    (hx : ∀ m, (x' m).left ≫ mp.φ = (x m).left) (m : ℕ) :
    cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] =
      fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ := by
  funext J
  let U : Over.mk ((jOG (𝟙 (Sp S)) d m 2).hom ≫ x0) ⟶ jOG x0 d m 2 :=
    Over.homMk (𝟙 _) (by simp)
  have key : ∀ i : Fin 2, pushPt mp.cart.1.w (jptG t' (𝟙 (Sp S)) d x' m i) = U ≫ jptG t x0 d x m i := fun i =>
    Over.OverMorphism.ext (by
      show ((homAt (𝟙 (Sp S)) (jetCopy d m i)).left ≫ (x' m).left) ≫ mp.φ =
        𝟙 _ ≫ (homAt x0 (jetCopy d m i)).left ≫ (x m).left
      rw [Category.id_comp, Category.assoc, hx]
      rfl)
  refine ((psum_push mp.cart
    ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]
    ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] U (fun i => ?_) J.down).trans
      (Category.id_comp _)).symm
  fin_cases i
  · exact key 0
  · exact key 1

theorem exists_frames_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m, (∀ m, (e' m).IsGen) → ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx e' he'
  have main : ∀ m, ∃ e : FrTyG t x0 d x m, e.IsGen ∧
      ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
        jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ e ∧
        LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
          jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁) := fun m => by
    obtain ⟨c₁, hc₁, hv⟩ := exists_up ((isGen_iff w).1 hw.1) t.PP.isLB t'.PP.isLB
      (φ' := cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)])
      (ε := cε 2) (e' m) (he' m)
    have gen : ∀ (ψ : ULift (Finset (Fin 2)) → ((jOG x0 d m 2).left ⟶ t.G.left))
        (c : LB.Gen (LB.LinComb t.PP.L ψ (cε 2))), c.IsGen →
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] = ψ →
        ∃ e : FrTyG t x0 d x m, e.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ c e := by
      intro ψ c hc h
      subst h
      exact ⟨c, hc, ChartPrimTrPf.corr_self _ _ _ c⟩
    obtain ⟨e, he, hce⟩ := gen _ c₁ hc₁ (cube_points_push t x0 t' mp d x x' hx m)
    exact ⟨e, he, c₁, hce, ChartPrimTrPf.maps_flat w _ _ (e' m) c₁ hv⟩
  choose e he hc using main
  exact ⟨e, he, hc⟩

end GlobalTheory.Chart.FrameUp
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.jetChart_coordinates_unique_commGroup : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ → ∀ ψ ψ' : JetR R (Fin d) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin d) m → aug.comp ψ' = jetAug R (Fin d) m → spMap ψ ≫ x m = spMap ψ' ≫ x m → ψ = ψ' := by
  first | exact @GlobalTheory.jetCoord_unique | exact GlobalTheory.jetCoord_unique | (intros; apply GlobalTheory.jetCoord_unique <;> assumption)
end

section

noncomputable section

namespace GlobalTheory

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem genUniqueSq (hs : Function.Surjective (A ⊗ A).hom.appTop.hom) (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((A ⊗ A).left ⟶ A.left)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen)
    (hu' : u'.IsGen) (h : ∀ y J, Good L y J → val u (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J =
      val u' (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J) (Z : Scheme.{0}) (r : Z ⟶ (A ⊗ A).left) (z : Z)
    (J) (hJ : Good L z J) : val u r z J = val u' r z J :=
  gen_unique' hL hF (A ⊗ A).hom _ (Over.w _) hs hu hu' h Z r z J hJ

theorem rosatiGen_swap (hs : Function.Surjective (A ⊗ A).hom.appTop.hom) (hL : L.IsLB) (f g f' g' : A ⟶ A)
    (ef : f' = g) (eg : g' = f)
    (u₁ : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (h₁ : u₁.IsGen)
    (n₁ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₁ (zero2 A)) (LB.oneGen L))
    (u₂ : LB.Gen (LB.LinComb L (rosatiφ A f' g') rosatiε)) (h₂ : u₂.IsGen)
    (n₂ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₂ (zero2 A)) (LB.oneGen L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) (x y : T ⟶ A) : val₂ u₂ z J x y = (val₂ u₁ z J y x)⁻¹ := by
  subst ef eg
  have key := genUniqueSq hs hL (fun U _ k => by
      refine (DVR.prod_neg _ _ (prod_ros g' f' (snd A A) (fst A A) k)).trans
        (Eq.trans ?_ (prod_ros f' g' (fst A A) (snd A A) k).symm)
      rw [mul_comm (snd A A ≫ g'), mul_comm (snd A A)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (DVR.pullGen_isGen _ _ _ _ h₂ (lift (fst A A) (snd A A)).left)
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₁ (lift (snd A A) (fst A A)).left)) (fun y I hI => by
      rw [val_inv, DVR.val_ros _ _ hI, DVR.val_ros _ _ hI, lift_fst, lift_snd, DVR.val₂_one n₁ hI,
        DVR.val₂_one n₂ hI, inv_one])
    _ (lift x y).left z J hJ
  rwa [val_inv, DVR.val_ros _ _ hJ, DVR.val_ros _ _ hJ, lift_fst, lift_snd] at key

theorem rosatiGen_comp (hs : Function.Surjective (A ⊗ A).hom.appTop.hom) (hL : L.IsLB) (f g f' g' F H : A ⟶ A)
    [IsMonHom f'] [IsMonHom g] (eF : F = f' ≫ f) (eH : H = g ≫ g')
    (u : LB.Gen (LB.LinComb L (rosatiφ A F H) rosatiε)) (h : u.IsGen)
    (n : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    (u₁ : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (h₁ : u₁.IsGen)
    (n₁ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₁ (zero2 A)) (LB.oneGen L))
    (u₂ : LB.Gen (LB.LinComb L (rosatiφ A f' g') rosatiε)) (h₂ : u₂.IsGen)
    (n₂ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₂ (zero2 A)) (LB.oneGen L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) (x y : T ⟶ A) :
    val₂ u z J x y = val₂ u₁ z J (x ≫ f') y * val₂ u₂ z J x (y ≫ g) := by
  subst eF eH
  have key := genUniqueSq hs hL (fun U _ k => by
      refine (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ (prod_ros f g (fst A A ≫ f') (snd A A) k)
        (prod_ros f' g' (fst A A) (snd A A ≫ g) k)).trans
        (Eq.trans ?_ (prod_ros (f' ≫ f) (g ≫ g') (fst A A) (snd A A) k).symm)
      rw [Category.assoc, Category.assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (DVR.pullGen_isGen _ _ _ _ h (lift (fst A A) (snd A A)).left)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₁ (lift (fst A A ≫ f') (snd A A)).left)
      (DVR.pullGen_isGen _ _ _ _ h₂ (lift (fst A A) (snd A A ≫ g)).left)) (fun y I hI => by
      rw [val_mul hI, DVR.val_ros _ _ hI, DVR.val_ros _ _ hI, DVR.val_ros _ _ hI, lift_fst_assoc, lift_snd_assoc,
        lift_fst, lift_snd, MonObj.one_comp, MonObj.one_comp, DVR.val₂_one n hI, DVR.val₂_one n₁ hI,
        DVR.val₂_one n₂ hI, _root_.mul_one])
    _ (lift x y).left z J hJ
  rwa [val_mul hJ, DVR.val_ros _ _ hJ, DVR.val_ros _ _ hJ, DVR.val_ros _ _ hJ, lift_fst_assoc, lift_snd_assoc,
    lift_fst, lift_snd] at key

end

theorem rosatiGen_one_mul_star : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)), (∀ a, (u a).IsGen ∧ LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ (u a) (zero2 G)) (LB.oneGen Lr.L)) → ∀ (T : Over S) (z : T.left) (J), Good Lr.L z J → (∀ x y : T ⟶ G, val₂ (u 1) z J x y = 1) ∧ (∀ (a b : O) (x y : T ⟶ G), val₂ (u (a * b)) z J x y = val₂ (u a) z J (x ≫ act.act b) y * val₂ (u b) z J x (y ≫ act.act (star a))) ∧ (∀ (a : O) (x y : T ⟶ G), val₂ (u a) z J x y * val₂ (u (star a)) z J y x = 1) := by
  intro S G _ _ hs _ Lr _ O _ _ act u hu T z J hJ
  have hm : ∀ (a b : O) (x y : T ⟶ G), val₂ (u (a * b)) z J x y =
      val₂ (u a) z J (x ≫ act.act b) y * val₂ (u b) z J x (y ≫ act.act (star a)) := fun a b x y => by
    have := act.hom b
    have := act.hom (star a)
    exact rosatiGen_comp hs Lr.isLB _ _ _ _ _ _ (by rw [mul_comm, act.mul]) (by rw [star_mul', act.mul])
      _ (hu _).1 (hu _).2 _ (hu a).1 (hu a).2 _ (hu b).1 (hu b).2 hJ x y
  refine ⟨fun x y => ?_, hm, fun a x y => ?_⟩
  · have h := hm 1 1 x y
    have e : val₂ (u (1 * 1)) z J x y = val₂ (u 1) z J x y :=
      congrArg (fun a => val₂ (u a) z J x y) (_root_.mul_one 1)
    have e₁ : x ≫ act.act 1 = x := by rw [act.one, Category.comp_id]
    have e₂ : y ≫ act.act (star 1) = y := by rw [star_one, act.one, Category.comp_id]
    rw [e, e₁, e₂] at h
    exact mul_eq_left.1 h.symm
  · rw [rosatiGen_swap hs Lr.isLB _ _ _ _ rfl (by rw [star_star]) _ (hu a).1 (hu a).2 _ (hu (star a)).1
      (hu (star a)).2 hJ y x, mul_inv_cancel]

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isSeriesOfMorphismInCharts_pow_mulFormalGroupLaw : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ F : Fin d → PS R 2 d, GlobalTheory.JetSer.IsLawOf x F → ∀ N : ℕ, GlobalTheory.JetSer.IsMapOf x x ((𝟙 G) ^ N : G ⟶ G) (mulF F N) := by
  first | exact @GlobalTheory.JetSer.isMapOf_pow_mulF | exact GlobalTheory.JetSer.isMapOf_pow_mulF | (intros; apply GlobalTheory.JetSer.isMapOf_pow_mulF <;> assumption)
end
