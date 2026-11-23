module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle002
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAdjointIntegralEndOfLadicLimit
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle023
import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLaw
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle036
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle035
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ActionLimit

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)
variable {d : ℕ} {I : Fin 2 → Type} (X : RawChart C d I (Fin dd))
  (hlg : X.lg = fun i => un1 (Y.lg i)) (hex : X.ex = fun i => un1 (Y.ex i)) (hh : X.h = Y.h)

include hlg hex in
theorem matrixEnd_linearMap' (M : Matrix (Fin dd) (Fin dd) C)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP X M a i =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) i) := by
  have h0 := gp_lg Y
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  have hL : GP (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) := gp_comp1 _ _ (gp_linMap _) h0
  have e0 : endP X M a i =
    MvPowerSeries.subst (fun x => ∑ y, M x y • MvPowerSeries.subst a (un1 (Y.lg y))) (un1 (Y.ex i)) := by
    unfold endP
    rw [hlg, hex]
  rw [e0, funext (subst_linMap M Y.lg h0 a ha)]
  generalize comp1 (LogExpAdaptedGauge.linMap M) Y.lg = L at hL ⊢
  have hz : ∀ x, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (L x)) = 0 :=
    fun x => Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (fun q : Fin 1 × Fin dd => ha q.2) (hL x)
  rw [subst_singlePointUncurry _ hz, germComp1_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => hL q.2) hs]

include hlg hex in
theorem matrixEnd_eq_subst' (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP X (dLin e) a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  rw [matrixEnd_linearMap' Y X hlg hex _ a ha, ← eq_exp_lin_log Y e he hhom]

include hlg hex in
theorem matrixEnd_eq_comp' (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {n : ℕ} (a : Pt C n dd) (ha : GP a) : endP X (dLin e) a = comp1 e a := by
  funext i
  rw [matrixEnd_eq_subst' Y X hlg hex e he hhom a ha, germComp1_eq_subst]

include hh in
theorem hAt_eq_ev_raw {n : ℕ} (a b : Pt C n dd) : hAt X a b = ev ![a, b] Y.h := by
  unfold hAt
  rw [hh]
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s <;> rfl

include hlg hex hh in
theorem isEnd_of_hom_raw (e e' : Pt C 1 dd) (he : GP e) (he' : GP e')
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    (hhom' : comp1 e' (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e' (pt C (n := 2) dd 0)) (comp1 e' (pt C (n := 2) dd 1)))
    (hi : ∀ i, IntS V (e i)) (hi' : ∀ i, IntS V (e' i))
    (hx : IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 e' (pt C dd 1)] Y.h))) :
    IsEnd X V (dLin e) (dLin e') := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have hc : MvPowerSeries.constantCoeff Y.h = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt (0 : Fin 1))) Y.h, Y.gauge.ax0, map_zero]
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [matrixEnd_eq_subst' Y X hlg hex e he hhom _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi i _
  · rw [matrixEnd_eq_subst' Y X hlg hex e' he' hhom' _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi' i _
  · have g0 : gp C (Fin dd) (0 : Fin 2) = pt C dd 0 := rfl
    have g1 : gp C (Fin dd) (1 : Fin 2) = pt C dd 1 := rfl
    rw [g0, g1, matrixEnd_eq_comp' Y X hlg hex e he hhom _ (gp_pt 0), matrixEnd_eq_comp' Y X hlg hex e' he' hhom' _ (gp_pt 1),
      hAt_eq_ev_raw Y X hh, hAt_eq_ev_raw Y X hh, ← subst_exp_eq_mvExp]
    · exact hx
    · rw [map_sub, gt_const_ev _ (pair_points_zero_constant (gp_comp1 _ _ he (gp_pt 0)) (gp_pt 1)) _ hc,
        gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ he' (gp_pt 1))) _ hc, sub_zero]

end Chart

theorem exists_isEnd_of_limit_raw : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) (I : Fin 2 → Type) (X : RawChart C d I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h → ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd X V M M' ∧ IsEnd X V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  intro C _ _ V O _ _ dd Y d I X hlg hex hh a ha
  obtain ⟨c1, c2⟩ := GlobalTheory.T.actionConverges_ladic_cauchy_and_star C V O dd Y a ha
  obtain ⟨e, eb, i1, i2, l1, l2, h1, x1⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y a c1 c2
  obtain ⟨f, fb, -, -, l3, l4, h2, x2⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y (fun n => star (a n)) c2
    (by simpa only [star_star] using c1)
  simp only [star_star] at l4
  obtain rfl : f = eb := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l3 N i μ) (fun N => l2 N i μ)
  obtain rfl : fb = e := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l4 N i μ) (fun N => l1 N i μ)
  have hz : ∀ (g : Pt C 1 dd) (s : ℕ → O), (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (g i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i))) → GP g := by
    intro g s hg i
    refine limit_unique V (fun n => MvPowerSeries.coeff 0 (Y.B.A.act (s n) i)) _ _ (fun N => hg N i 0)
      fun N => ⟨0, fun n _ => ?_⟩
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.B.A.const, sub_zero]
    exact VF.Ge.zero _
  have g1 := hz fb a l1
  have g2 := hz f (fun n => star (a n)) l2
  exact ⟨dLin fb, dLin f, isEnd_of_hom_raw Y X hlg hex hh fb f g1 g2 h1 h2 i1 i2 x1, isEnd_of_hom_raw Y X hlg hex hh f fb g2 g1 h2 h1 i2 i1 x2,
    linear_limit V fb _ l1, linear_limit V f _ l2⟩

end GlobalTheory.ActionLimit
end
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.CEqSt H := by
  first | exact @GlobalTheory.RowLaw.cEqSt_of_rLaw | exact GlobalTheory.RowLaw.cEqSt_of_rLaw | (intros; apply GlobalTheory.RowLaw.cEqSt_of_rLaw <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_adjointIntegralEnd_of_ladicLimit : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd (Y.raw p) V M M' ∧ IsEnd (Y.raw p) V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  first | exact @GlobalTheory.ActionLimit.exists_isEnd_of_limit | exact GlobalTheory.ActionLimit.exists_isEnd_of_limit | (intros; apply GlobalTheory.ActionLimit.exists_isEnd_of_limit <;> assumption)
end

section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

open GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing in
private theorem ker_red_eq {R₀ : Type} [CommRing R₀] (O : LAlg R₀) (x : (dual O : Type))
    (hx : (red O).1 x = 0) :
    x = (incl O).1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x) * eta O := by
  have key : ∀ b : DualNumber (O : Type), TrivSqZeroExt.fst b = 0 →
      b = (TrivSqZeroExt.inl (TrivSqZeroExt.snd b) : DualNumber (O : Type)) * DualNumber.eps :=
    fun b hb => by ext <;> simp [hb]
  exact key x hx

private def liftAlg {R₀ : Type} [CommRing R₀] {O R : Type} [CommRing O] [CommRing R] [Algebra R₀ O]
    [Algebra R₀ R] (s : O →ₐ[R₀] R) (i : R) (hi : i * i = 0) : DualNumber O →ₐ[R₀] R where
  toFun x := s x.fst + s x.snd * i
  map_one' := by simp
  map_mul' x y := by
    simp only [TrivSqZeroExt.fst_mul, DualNumber.snd_mul, map_mul, map_add (f := _)]
    linear_combination (-(s x.snd * s y.snd)) * hi
  map_zero' := by simp
  map_add' x y := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add (f := _)]; ring
  commutes' r := by simp [TrivSqZeroExt.algebraMap_eq_inl']

open GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing in
private theorem exists_lift {R₀ : Type} [CommRing R₀] {O R : LAlg R₀} (s : LHom O R) (i : (R : Type))
    (hi : i * i = 0) : ∃ f : LHom (dual O) R, f.comp (incl O) = s ∧ f.1 (eta O) = i := by
  refine ⟨⟨liftAlg s.1 i hi, ⟨fun x hx => ?_⟩⟩, Subtype.ext (AlgHom.ext fun x => ?_), ?_⟩
  · have hx' : IsUnit (s.1 (TrivSqZeroExt.fst (R := (O : Type)) (M := (O : Type)) x) +
      s.1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x) * i) := hx
    have hn : IsNilpotent (-(s.1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x) * i)) :=
      ⟨2, by linear_combination (s.1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x)) ^ 2 * hi⟩
    have h2 := hn.isUnit_add_left_of_commute hx' (Commute.all _ _)
    rw [add_neg_cancel_right] at h2
    exact TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (s.2.map_nonunit _ h2)
  · change s.1 x + s.1 0 * i = s.1 x
    simp
  · change s.1 0 + s.1 1 * i = i
    simp

private theorem chart_add {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g : ℕ}
    {F : FGLaw (O : Type) g} {Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R}
    (h : BXChart B O F.F Y) (R : LAlg R₀) (s : LHom O R) (e : (R : Type)) (he : e * e = 0)
    (a b : Fin g → (R : Type)) :
    Y R s (fun k => a k * e) + Y R s (fun k => b k * e) = Y R s (fun k => (a k + b k) * e) := by
  have hn : ∀ c : (R : Type), IsNilpotent (c * e) := fun c => ⟨2, by linear_combination c ^ 2 * he⟩
  have key : ∀ (a b : Fin g → (R : Type)) (k : Fin g),
      nv s.1.toRingHom (F.F k) ![fun k => a k * e, fun k => b k * e] =
        (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (F.F k)) * a j +
          ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (F.F k)) * b j) * e := by
    intro a b k
    have h1 := (nv_calculus _ _ s.1.toRingHom 2 g ![fun k => a k * e, fun k => b k * e]
      (fun i j => by fin_cases i <;> exact hn _)).2.2.2.2.2 (fun i j i' j' => by
        have : ∀ c d : (R : Type), c * e * (d * e) = 0 := fun c d => by linear_combination c * d * he
        fin_cases i <;> fin_cases i' <;> exact this _ _) (F.F k)
    rw [h1, F.const, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_two, add_mul,
      Finset.sum_mul, Finset.sum_mul]
    simp [_root_.mul_assoc]
  have law : ∀ a b : Fin g → (R : Type), Y R s (fun k => a k * e) + Y R s (fun k => b k * e) =
      Y R s (fun k => (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (F.F k)) * a j +
          ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (F.F k)) * b j) * e) := by
    intro a b
    rw [h.law R s _ _ (fun _ => hn _) (fun _ => hn _)]
    simp only [key]
  have hz : Y R s (fun k => (0 : Fin g → (R : Type)) k * e) = 0 := by
    rw [← h.zero R s]; congr 1; funext k; simp
  have ha := law a 0
  have hb := law 0 b
  rw [hz, add_zero] at ha
  rw [hz, zero_add] at hb
  have ha' := h.inj R s _ _ (fun _ => hn _) (fun _ => hn _) ha
  have hb' := h.inj R s _ _ (fun _ => hn _) (fun _ => hn _) hb
  rw [law]
  congr 1
  funext k
  have h1 := congrFun ha' k
  have h2 := congrFun hb' k
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at h1 h2
  rw [add_mul, add_mul, ← h1, ← h2]


open GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing in
theorem exists_tanMat : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ gb : Module.Basis (Fin g) R₀ B.gg, ∃ S : Matrix (Fin g) (Fin g) (O : Type), IsUnit S ∧ TanMat B O Y gb S := by
  intro R₀ _ B O g F Y h gb
  have hee := eta_mul_eta O
  have hn : ∀ c : (dual O : Type), IsNilpotent (c * eta O) :=
    fun c => ⟨2, by linear_combination c ^ 2 * hee⟩
  have hη : (red O).1 (eta O) = 0 := rfl
  have hex : ∀ l, ∃ a : Fin g → (dual O : Type), (∀ i, (red O).1 (a i) = 0) ∧
      B.tg (red O) (red_sqZero O) (gb l ⊗ₜ[R₀] ⟨eta O, hη⟩) = Y (dual O) (incl O) a := fun l =>
    h.surj (dual O) O (incl O) (red O) (incl O) (red_comp_incl O) (by rw [red_comp_incl]; rfl)
      (red_sqZero O) _ ((B.tg_ker _ _ _).2 ⟨_, rfl⟩)
  choose a ha0 ha using hex
  let S : Matrix (Fin g) (Fin g) (O : Type) :=
    Matrix.of fun k l => TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) (a l k)
  have haS : ∀ l, a l = fun k => (incl O).1 (S k l) * eta O := fun l =>
    funext fun k => ker_red_eq O _ (ha0 l k)
  have hT : TanMat B O Y gb S := by
    intro R R' s π hπ l i
    have hi : (i : (R : Type)) * i = 0 := by
      have : (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul i.2 i.2
      rwa [hπ.2, Ideal.mem_bot] at this
    obtain ⟨f, hf1, hf2⟩ := exists_lift s (i : (R : Type)) hi
    have hf : ∀ x ∈ (red O).ker, f.1.toLinearMap x ∈ π.ker := fun x hx => by
      rw [ker_red_eq O x hx]
      change π.1 (f.1 (_ * _)) = 0
      have hi0 : π.1 (i : (R : Type)) = 0 := i.2
      rw [map_mul, map_mul, hf2, hi0, mul_zero]
    have h1 := B.tg_nat (red O) π (red_sqZero O) hπ f hf (gb l ⊗ₜ[R₀] ⟨eta O, hη⟩)
    rw [ha, haS, h.nat _ _ _ _ _ (fun _ => hn _), hf1, LinearMap.lTensor_tmul] at h1
    have h2 : (f.1.toLinearMap.restrict hf) ⟨eta O, hη⟩ = i := Subtype.ext hf2
    rw [h2] at h1
    rw [h1]
    congr 1
    funext k
    rw [map_mul, hf2, ← hf1]
    rfl
  refine ⟨S, Matrix.mulVec_surjective_iff_isUnit.1 fun v => ?_, hT⟩
  have hP : ∀ w, ∃ c : Fin g → (O : Type), B.tg (red O) (red_sqZero O) w =
      Y (dual O) (incl O) (fun k => (incl O).1 ((S *ᵥ c) k) * eta O) := by
    let P : B.G (dual O) → Prop := fun x => ∃ c : Fin g → (O : Type),
      x = Y (dual O) (incl O) (fun k => (incl O).1 ((S *ᵥ c) k) * eta O)
    have P0 : P 0 := ⟨0, by rw [← h.zero (dual O) (incl O)]; congr 1; funext k; simp⟩
    have Padd : ∀ x y, P x → P y → P (x + y) := by
      rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
      refine ⟨c + c', ?_⟩
      rw [chart_add h _ _ _ hee]
      simp only [Matrix.mulVec_add, Pi.add_apply, map_add (f := _)]
    intro w
    change P _
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact P0
    | add x y hx hy => rw [map_add (f := _)]; exact Padd _ _ hx hy
    | tmul m i =>

      rw [← gb.sum_repr m, TensorProduct.sum_tmul, map_sum]
      refine Finset.sum_induction _ P Padd P0 fun l _ => ?_
      rw [TensorProduct.smul_tmul]
      generalize (gb.repr m l) • i = j
      refine ⟨Pi.single l (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) j.1), ?_⟩
      rw [hT]
      congr 1
      funext k
      rw [Matrix.mulVec_single]
      simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.smul_apply, Matrix.col_apply,
        map_mul, _root_.mul_assoc]
      rw [← ker_red_eq O j.1 j.2]
  have hx : B.map (red O) (Y (dual O) (incl O) (fun k => (incl O).1 (v k) * eta O)) = 0 := by
    rw [h.nat _ _ _ _ _ (fun _ => hn _), ← h.zero O ((red O).comp (incl O))]
    congr 1
    funext k
    rw [map_mul, hη, mul_zero]; rfl
  obtain ⟨w, hw⟩ := (B.tg_ker _ (red_sqZero O) _).1 hx
  obtain ⟨c, hc⟩ := hP w
  have h3 := h.inj _ _ _ _ (fun _ => hn _) (fun _ => hn _) (hc.symm.trans hw)
  refine ⟨c, funext fun k => ?_⟩
  have h4 := congrArg (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type))) (congrFun h3 k)
  have key : ∀ t : (O : Type), TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type))
      ((incl O).1 t * eta O) = t := fun t => by
    have : TrivSqZeroExt.snd ((TrivSqZeroExt.inl t : DualNumber (O : Type)) *
      (DualNumber.eps : DualNumber (O : Type))) = t := by simp
    exact this
  rwa [key, key] at h4

end GlobalTheory.ChF
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eigenbasis_restriction_surjective_equivariant : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (OE : Type) [CommRing OE] (d n : ℕ) (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O), EigB ρ τ W → Function.Surjective (Pdiv.ChartF.res W) ∧ (∀ a f, Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) = τ a • Pdiv.ChartF.res W f) ∧ eigDim C ρ ((algebraMap O C).comp τ) = n := by
  first | exact @GlobalTheory.ChF.eigB_res_surjective | exact GlobalTheory.ChF.eigB_res_surjective | (intros; apply GlobalTheory.ChF.eigB_res_surjective <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.embeddings_lift_integers_idempotents_conjugation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE], (∀ τ : OE →+* C, ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ) ∧ (∀ (e : ℤ_[p] ⊗[ℤ] OE) (τ : OE →+* O), e * e = e → tauExt τ e = 0 ∨ tauExt τ e = 1) ∧ ∀ [StarRing OE] (τ : OE →+* O) (x : ℤ_[p] ⊗[ℤ] OE), tauExt (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) x = tauExt τ (sigE p OE x) ∧ sig p OE x = sigE p OE x := by
  first | exact @GlobalTheory.ChF.embeddings_idempotents_conjugation | exact GlobalTheory.ChF.embeddings_idempotents_conjugation | (intros; apply GlobalTheory.ChF.embeddings_idempotents_conjugation <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formalGroupAction_linearPart_ringHom : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (OE : Type) [CommRing OE] (act : Geo.Tor.Germ.OAct OE F) (S : Type) [CommRing S] (β : R →+* S), ∃ ρ : OE →+* Matrix (Fin d) (Fin d) S, ∀ a, ρ a = linPart (actMap β act a) ∧ ρ a = (lin (act.act a)).map β := by
  first | exact @GlobalTheory.ChF.linPart_act_ringHom | exact GlobalTheory.ChF.linPart_act_ringHom | (intros; apply GlobalTheory.ChF.linPart_act_ringHom <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.linearData_hodgeTate_inclusion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ c : O, v (algebraMap O C c) ^ (p - 1) ≤ v (algebraMap O C (p : O)) → ∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range s) := by
  first | exact @GlobalTheory.ChF.linDat_hodgeTate_inclusion | exact GlobalTheory.ChF.linDat_hodgeTate_inclusion | (intros; apply GlobalTheory.ChF.linDat_hodgeTate_inclusion <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thickeningQuotientImage_one_iff_exists_torusImage : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ z, QRel c S z 1 ↔ ∃ χ, IRel c S χ z := by
  first | exact @GlobalTheory.ChF.qRel_one_iff_exists_iRel | exact GlobalTheory.ChF.qRel_one_iff_exists_iRel | (intros; apply GlobalTheory.ChF.qRel_one_iff_exists_iRel <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d), (∀ N : ℕ, lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R)) ∧ (∀ N M : ℕ, mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M)) ∧ (∀ N M : ℕ, Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M))) ∧ ∀ (p k : ℕ) (j : Fin d), mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (MvPowerSeries.C : R →+* PS R 1 d) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) := by
  first | exact @GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow | exact GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow | (intros; apply GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow <;> assumption)
end

section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem dl_pairSer_eq_height : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (p : ℕ) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) (g : ℕ) (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)), TanMat B Tw.O Y gb S → ∀ (τ : ℕ → B.G Tw.O) (u : PS (Tw.O : Type) 1 g), MvPowerSeries.constantCoeff u = 1 → PairSer B Tw.O Y p τ u → ∀ ht : B.gg →ₗ[R₀] (Tw.O : Type), (∀ n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ n)) ((Tw.q n).1.toLinearMap ∘ₗ ht)) → Sᵀ *ᵥ dl u = fun l => ht (gb l) := by
  intro R₀ _ B p Tw Dt g Y gb S hS τ u hu hP ht hH
  funext l
  rw [← sub_eq_zero]
  refine Tw.sep _ fun n => (Dt.Dp n).free _ ?_
  set Dp := Dt.Dp n
  obtain ⟨z, hz, hz'⟩ := hH n (gb l)
  let s : LHom Tw.O Dp.D := Dp.σ.comp (Tw.q n)
  have hs : ∀ x, s.1 x = Dp.σ.1 ((Tw.q n).1 x) := fun _ => rfl
  have hc : ((p ^ (n + 1) : ℕ) : (Tw.R n : Type)) = 0 := by
    rw [← map_natCast (Tw.π n).1, Tw.char n, map_zero]
  have hp : IsNilpotent (p : (Dp.D : Type)) :=
    ⟨n + 1, by rw [← Nat.cast_pow, ← map_natCast Dp.σ.1, hc, map_zero]⟩
  have hsq : ∀ x y : (Dp.D : Type), x * Dp.η * (y * Dp.η) = 0 := fun x y => by
    rw [_root_.mul_mul_mul_comm, Dp.η_sq, mul_zero]
  have ha : ∀ k, IsNilpotent (s.1 (S k l) * Dp.η) := fun k => ⟨2, by rw [pow_two, hsq]⟩
  rw [hS Dp.D _ s Dp.π Dp.sqZero l Dp.ηk, ← B.map_comp] at hz
  have h1 := hP Dp.D s (fun k => s.1 (S k l) * Dp.η) n z hp ha hz
  have h2 := (nv_calculus _ _ s.1.toRingHom 1 g ![fun k => s.1 (S k l) * Dp.η]
    (fun i j => by simpa using ha j)).2.2.2.2.2 (fun i j i' j' => by simpa using hsq _ _) u
  rw [h2, hz', hu, map_one, add_right_inj, Fintype.sum_prod_type, Fin.sum_univ_one] at h1
  rw [← hs, map_sub, sub_mul, sub_eq_zero]
  refine Eq.trans ?_ h1.symm

  simp only [mulVec, dotProduct, transpose_apply, dl, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.cons_val_fin_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

end GlobalTheory.ChF
end
end
