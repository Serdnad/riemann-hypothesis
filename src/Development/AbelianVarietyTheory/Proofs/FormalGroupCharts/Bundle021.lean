module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle016
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle020
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
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import Mathlib.RingTheory.PowerSeries.Log
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem nabValN_congr_FK {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    (B : FB R d O) (B' : FB R' d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] [Algebra R' k]
    (hF : B'.FK k = B.FK k) (hA : ∀ a, B'.actK k a = B.actK k a)
    (h : PS k 2 d) (w0 : O) (m : ℕ) {n : ℕ} (f : PS k n d) {κ : Type} [Fintype κ]
    (cp : κ → Fin n) (u : κ → Fin d → k) (P : MvPolynomial κ k) :
    nabValN B k h w0 m f cp u P = nabValN B' k h w0 m f cp u P := by
  unfold nabValN FB.hL
  rw [hF, hA]

theorem isIntPS_iff_exists_map (T : CDVR) {n d : ℕ} (f : PS T.Fr n d) :
    IsIntPS T f ↔ ∃ g : PS T.V n d, MvPowerSeries.map (algebraMap T.V T.Fr) g = f := by
  constructor
  · intro hf
    choose g hg using hf
    refine ⟨g, ?_⟩
    ext m
    exact (MvPowerSeries.coeff_map _ _ _).trans (hg m)
  · rintro ⟨g, rfl⟩ m
    exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

theorem nuLocC_eq_nuAlg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), letI := io.toAlgebra; ∀ BT : FB T.V (chD C.ch) (𝓞 E), BT.FK T.Fr = C.ch.B.FK T.Fr → (∀ a, BT.actK T.Fr a = C.ch.B.actK T.Fr a) → ∀ (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n = nuAlg Dw T BT C.ch.h C.ch.uvec e k a n := by
  intro E _ _ _ H Dw l Xo c _ T io y C
  letI := io.toAlgebra
  intro BT hF hA e k a n
  unfold nuLocC nuAlg
  refine iInf_congr fun P => iInf_congr fun _ => ?_
  apply le_antisymm
  · refine le_iInf fun g => ?_
    refine iInf_le_of_le (MvPowerSeries.map (algebraMap T.V T.Fr) g) ?_
    refine iInf_le_of_le ((isIntPS_iff_exists_map T _).2 ⟨g, rfl⟩) ?_
    exact le_of_eq (congrArg (nval T.V e) (nabValN_congr_FK C.ch.B BT T.Fr hF hA _ _ _ _ _ _ _))
  · refine le_iInf fun f => le_iInf fun hf => ?_
    obtain ⟨g, rfl⟩ := (isIntPS_iff_exists_map T _).1 hf
    refine iInf_le_of_le g ?_
    exact le_of_eq (congrArg (nval T.V e) (nabValN_congr_FK C.ch.B BT T.Fr hF hA _ _ _ _ _ _ _)).symm

end GlobalTheory.ChartCmp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCmp

theorem isMonHom_of_mul_points {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G')
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  constructor
  · have e := h (𝟙_ _) 1 1
    rw [_root_.mul_one] at e
    have e2 : (1 : 𝟙_ (Over S) ⟶ G) ≫ f = 1 := by
      have := e.symm
      exact mul_eq_left.1 this
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _)] using e2
  · simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp]
      using h (G ⊗ G) (fst G G) (snd G G)

theorem exists_iso_of_sabMap_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), ∃ ψ : t.G ≅ t'.G, ψ.hom.left = n.φ ∧ IsMonHom ψ.hom ∧ (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) ∧ n.cm.F3 = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ∧ ∃ w : LB.Iso t.PP.L (t'.PP.L.pull n.φ), CubIso n w := by
  intro E _ _ _ H V _ t t' n
  have hp := n.cart.1
  have hw : n.cm.F ≫ t'.G.hom = t.G.hom := by simpa using hp.w
  haveI : IsIso n.cm.F := hp.isIso_fst_of_isIso
  let ψ : t.G ≅ t'.G := Over.isoMk (asIso n.cm.F) hw
  have hψ : ψ.hom.left = n.cm.F := rfl
  refine ⟨ψ, rfl, ?_, fun a => ?_, ?_, ?_⟩
  · refine isMonHom_of_mul_points _ fun T x y => ?_
    apply Over.OverMorphism.ext
    have e := n.cart.2 T x y (pushPt hp.w x) (pushPt hp.w y) rfl rfl
    rw [Over.comp_left, hψ, ← e]
    exact mul_left_congr (Category.comp_id _) _ _ (x ≫ ψ.hom) (y ≫ ψ.hom) rfl rfl
  · apply Over.OverMorphism.ext
    exact n.act a
  · refine hom_ext_triple _ fun i => ?_
    rw [cubeMap_comp_proj_three, ← Over.comp_left, ← cubeProj_comp_map, Over.comp_left, hψ]
  · obtain ⟨w, h1, -, h3⟩ := n.lin
    exact ⟨w, h1, h3⟩

end GlobalTheory.ChartCmp
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

theorem jeq_pow_congr {R σ : Type} [CommRing R] {m : ℕ} {a b : MvPowerSeries σ R} (h : JEq m a b) (n : ℕ) :
    JEq m (a ^ n) (b ^ n) := by
  classical
  induction n with
  | zero => intro e _; rw [pow_zero, pow_zero]
  | succ n ih =>
    intro e he
    rw [pow_succ, pow_succ, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hd : p.1.degree + p.2.degree = e.degree := by rw [← map_add (f := _), hp]
    rw [ih p.1 (by omega), h p.2 (by omega)]

theorem jeq_psubst_congr {R σ : Type} [CommRing R] {m : ℕ} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (h : JEq m a b)
    (F : PowerSeries R) : JEq m (PowerSeries.subst a F) (PowerSeries.subst b F) := by
  intro e he
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hb)]
  refine finsum_congr fun n => ?_
  rw [jeq_pow_congr h n e he]

theorem jeq_expS_iff_and_exists_log : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (n d m : ℕ), (∀ f g : PS k n d, MvPowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff g = 0 → (JEq m f g ↔ JEq m (FB.expS k f) (FB.expS k g))) ∧ ∀ u : PS k n d, MvPowerSeries.constantCoeff u = 1 → ∃ lam : PS k n d, MvPowerSeries.constantCoeff lam = 0 ∧ FB.expS k lam = u := by
  intro k _ _ n d m
  refine ⟨fun f g hf hg => ⟨fun h => jeq_psubst_congr hf hg h _, fun h => ?_⟩, fun u hu => ?_⟩
  · have h1 : JEq m (PowerSeries.subst f (PowerSeries.exp k) - 1) (PowerSeries.subst g (PowerSeries.exp k) - 1) := by
      intro e he
      rw [map_sub, map_sub]
      exact congrArg (· - _) (h e he)
    have h2 := jeq_psubst_congr (by simp [TB.WickVanishing.constantCoeff_exp hf]) (by simp [TB.WickVanishing.constantCoeff_exp hg]) h1
      (PowerSeries.log k)
    rwa [TB.WickVanishing.log_exp hf, TB.WickVanishing.log_exp hg] at h2
  · exact ⟨_, TB.WickVanishing.constantCoeff_logS hu, TB.WickVanishing.exp_log hu⟩

end GlobalTheory.ChartCmp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.Regauge
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem eq_of_forall_jeq {R σ : Type} [CommRing R] {f g : MvPowerSeries σ R} (h : ∀ m, JEq m f g) : f = g :=
  MvPowerSeries.ext fun e => h e.degree e le_rfl

theorem isCanonGauge_sub : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h g : PS k 2 d), B.IsCanonGauge k h → (∀ m, Biadd m B k g) → B.IsCanonGauge k (h - g) := by
  intro R _ d O _ _ B k _ _ _ h g hc hg
  have hF : ∀ i, MvPowerSeries.constantCoeff (B.FK k i) = 0 := fun i => by
    simp [FB.FK, FGLaw.mapF, B.G.const]
  have hA : ∀ a, GP (B.actK k a) := fun a i => by simp [FB.actK, B.A.const]
  have gA : ∀ {n : ℕ} (i j : Fin n), GP (addOf (B.FK k) (pt k d i) (pt k d j)) :=
    fun i j => gp_addOf _ hF _ _ (gp_pt i) (gp_pt j)
  have gC : ∀ {n : ℕ} (a : O) (i : Fin n), GP (comp1 (B.actK k a) (pt k d i)) :=
    fun a i => gp_comp1 _ _ (hA a) (gp_pt i)
  have a0 := eq_of_forall_jeq fun m => (hg m).ax0
  have a1 := eq_of_forall_jeq fun m => (hg m).ax1
  have d1 := eq_of_forall_jeq fun m => (hg m).add1
  have d2 := eq_of_forall_jeq fun m => (hg m).add2
  have sy := eq_of_forall_jeq fun m => (hg m).sym
  have bal := fun a => eq_of_forall_jeq fun m => (hg m).bal a
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_sub _ (pair_points_zero_constant gp_zero₂ (gp_pt _)), hc.ax0, a0, sub_zero]
  · rw [gt_ev_sub _ (pair_points_zero_constant (gp_pt _) gp_zero₂), hc.ax1, a1, sub_zero]
  · rw [hc.ph1, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)),
      gt_ev_sub _ (pair_points_zero_constant (gA _ _) (gp_pt _)), d1]
    congr 1; ring
  · rw [hc.ph2, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)),
      gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gA _ _)), d2]
    congr 1; ring
  · rw [hc.sy, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), sy]
    congr 1; ring
  · rw [hc.ad a, gt_ev_sub _ (pair_points_zero_constant (gC _ _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gC _ _)), bal a]
    congr 1; ring

end GlobalTheory.ChartCmp.Regauge
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

namespace GlobalTheory.ChartCmp.JCalc

variable {R : Type} [CommRing R] {σ : Type} {m : ℕ}

theorem jeq_refl (f : MvPowerSeries σ R) : JEq m f f := fun _ _ => rfl

theorem jeq_add {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f + g) (f' + g') :=
  fun e he => by rw [map_add (f := _), map_add (f := _), h e he, k e he]

theorem jeq_sub {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f - g) (f' - g') :=
  fun e he => by rw [map_sub, map_sub, h e he, k e he]

theorem jeq_mul {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f * g) (f' * g') := by
  classical
  intro e he
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hsum := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
  rw [map_add (f := _)] at hsum
  rw [h p.1 (by omega), k p.2 (by omega)]

theorem jeq_cancel {f g u : MvPowerSeries σ R} (hu : IsUnit (MvPowerSeries.constantCoeff u))
    (h : JEq m (f * u) (g * u)) : JEq m f g := by
  obtain ⟨c, hc⟩ := hu
  have h1 := MvPowerSeries.mul_invOfUnit u c hc.symm
  have := jeq_mul h (jeq_refl (MvPowerSeries.invOfUnit u c))
  rwa [_root_.mul_assoc, _root_.mul_assoc, h1, _root_.mul_one, _root_.mul_one] at this

theorem jeq_map {R' : Type} [CommRing R'] (β : R →+* R') {f g : MvPowerSeries σ R} (h : JEq m f g) :
    JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g) :=
  fun e he => by rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, h e he]

theorem jeq_iff_truncTotal [Finite σ] (f g : MvPowerSeries σ R) :
    JEq m f g ↔ MvPowerSeries.truncTotal (m + 1) f = MvPowerSeries.truncTotal (m + 1) g := by
  constructor
  · intro h
    ext e
    by_cases he : e.degree ≤ m
    · rw [MvPowerSeries.coeff_truncTotal _ (by omega), MvPowerSeries.coeff_truncTotal _ (by omega), h e he]
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega), MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega)]
  · intro h e he
    rw [← MvPowerSeries.coeff_truncTotal (n := m + 1) f (by omega),
      ← MvPowerSeries.coeff_truncTotal (n := m + 1) g (by omega), h]

theorem jeq_subst [Finite σ] {τ : Type} [Finite τ] {a a' : σ → MvPowerSeries τ R} {f g : MvPowerSeries σ R}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0)
    (h : ∀ i, JEq m (a i) (a' i)) (k : JEq m f g) :
    JEq m (MvPowerSeries.subst a f) (MvPowerSeries.subst a' g) := by
  rw [jeq_iff_truncTotal] at k ⊢
  simp only [jeq_iff_truncTotal] at h
  rw [MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst ha', k]
  simp only [h]

theorem jet_mk_eq_zero_iff (p : MvPolynomial σ R) :
    (Ideal.Quotient.mk _ p : Jet R σ m) = 0 ↔ ∀ e : σ →₀ ℕ, e.degree ≤ m → p.coeff e = 0 := by
  have h : orig R σ = MvPolynomial.idealOfVars σ R := rfl
  rw [Ideal.Quotient.eq_zero_iff_mem, h, MvPolynomial.mem_pow_idealOfVars_iff']
  simp [Nat.lt_succ_iff]

theorem mem_degLE_iff [Fintype σ] [DecidableEq σ] (e : σ →₀ ℕ) : e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  have hd : (e.sum fun _ k => k) = e.degree := rfl
  rw [hd]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine Finset.mem_image.2 ⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans h)⟩,
    Finset.mem_univ _, ?_⟩
  ext i
  simp

theorem coeff_psTrunc_ite [Fintype σ] [DecidableEq σ] (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    (psTrunc m f).coeff e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_degLE_iff]

theorem jeq_iff_psJet [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R) :
    JEq m f g ↔ psJet m f = psJet m g := by
  rw [← sub_eq_zero (a := psJet m f), psJet, psJet, ← map_sub, jet_mk_eq_zero_iff]
  refine forall_congr' fun e => forall_congr' fun he => ?_
  rw [MvPolynomial.coeff_sub, coeff_psTrunc_ite, coeff_psTrunc_ite, if_pos he, if_pos he, sub_eq_zero]

theorem eq_of_jeq {f g : MvPowerSeries σ R} (h : ∀ m', JEq m' f g) : f = g :=
  MvPowerSeries.ext fun e => h _ e le_rfl

theorem jeq_calculus : ∀ (R : Type) [CommRing R] (m : ℕ), (∀ (σ : Type) (f f' g g' : MvPowerSeries σ R), JEq m f f' → JEq m g g' → JEq m (f + g) (f' + g') ∧ JEq m (f - g) (f' - g') ∧ JEq m (f * g) (f' * g')) ∧ (∀ (σ : Type) (f g u : MvPowerSeries σ R), IsUnit (MvPowerSeries.constantCoeff u) → JEq m (f * u) (g * u) → JEq m f g) ∧ (∀ (σ R' : Type) [CommRing R'] (β : R →+* R') (f g : MvPowerSeries σ R), JEq m f g → JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g)) ∧ (∀ (d n n' : ℕ) (a a' : Fin n → Pt R n' d) (f g : PS R n d), (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) → (∀ i j, MvPowerSeries.constantCoeff (a' i j) = 0) → (∀ i j, JEq m (a i j) (a' i j)) → JEq m f g → JEq m (ev a f) (ev a' g)) ∧ (∀ (σ : Type) [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R), JEq m f g ↔ psJet m f = psJet m g) ∧ (∀ (σ : Type) (f g : MvPowerSeries σ R), (∀ m', JEq m' f g) → f = g) :=
  fun _ _ _ =>
  ⟨fun _ _ _ _ _ h k => ⟨jeq_add h k, jeq_sub h k, jeq_mul h k⟩,
    fun _ _ _ _ hu h => jeq_cancel hu h,
    fun _ _ _ β _ _ h => jeq_map β h,
    fun _ _ _ _ _ _ _ ha ha' h k => jeq_subst (fun p => ha p.1 p.2) (fun p => ha' p.1 p.2) (fun p => h p.1 p.2) k,
    fun _ _ _ f g => jeq_iff_psJet f g,
    fun _ _ _ h => eq_of_jeq h⟩

end GlobalTheory.ChartCmp.JCalc
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
open Formalism.MainNotions.ModuliIntegralCharts.H1

namespace GlobalTheory.ChartCmp.FrameRatio

theorem exists_corr_scaled {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ φ' : K → (Y ⟶ X)) (h : φ = φ') (ε : K → ℤ) (g : LB.Gen (LB.LinComb L φ ε))
    (g' : LB.Gen (LB.LinComb L φ' ε)) (hg : g.IsGen) (hg' : g'.IsGen) :
    ∃ U : Γ(Y, ⊤)ˣ, LB.Gen.Corr L φ ε φ' ε g
      (⟨fun j => res le_top U * g'.s j⟩ : LB.Gen (LB.LinComb L φ' ε)) := by
  subst h
  obtain ⟨U, hU⟩ := GaugeR.ratio_of_gen L hL φ ε g' g hg' hg
  refine ⟨U, fun j j' _ _ hx => ?_⟩
  obtain rfl : j = j' := funext fun k => hx k k rfl
  rw [hU j]

theorem comp_psum' {S : Scheme.{0}} (G : Over S) [GrpObj G] {T T' : Over S} (f : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) : f ≫ psum G x I = psum G (fun k => f ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    simp only [List.foldr_cons, padd]
    rw [← Category.assoc, comp_lift]
    congr 2

theorem unitΓ_surj {A : Type} [CommRing A] (U : Γ(Sp A, ⊤)ˣ) : ∃ u : Aˣ, unitΓ u = U := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom U, Units.ext ?_⟩
  simp [unitΓ, toΓ]

theorem psJet_surj {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ) (a : Jet R κ m) :
    ∃ f : MvPowerSeries κ R, psJet m f = a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨(p : MvPowerSeries κ R), GaugeR.psJet_eq_mk m _ p fun e _ => (MvPolynomial.coeff_coe p e).symm⟩

theorem copy_subst {V : Type} [CommRing V] (d m : ℕ) (φ : Fin d → MvPowerSeries (Fin 1 × Fin d) V)
    (ψ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) (i : Fin 2)
    (hψ : ∀ j, ψ i j = psIn d m ![i] (φ j)) :
    (jetCopy d m i).comp (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) =
      (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2).comp (jetCopy d m i) := by
  apply GermD.jet_hom_ext
  rintro ⟨i0, j⟩
  simp only [AlgHom.comp_apply, jetCopy, jetSubstP, GaugeR.jetMap_mk, MvPolynomial.aeval_X, hψ, psIn,
    MvPolynomial.constantCoeff_rename, map_sub, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  congr 2
  generalize psTrunc m (φ j) = P
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p k hp =>
    rw [map_mul, map_mul, hp, MvPolynomial.rename_X, MvPolynomial.aeval_X]
    obtain ⟨a, b⟩ := k
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ : Pt V 1 d), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → ∀ m, ∃ ε : PS V 2 d, IsUnit (MvPowerSeries.constantCoeff ε) ∧ FrRel t x x' e e' φ m ε := by
  intro E _ _ _ H V _ t d x x' e e' φ _ hc he he' m
  let ψ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V :=
    ![fun j => psIn d m ![0] (φ j), fun j => psIn d m ![1] (φ j)]
  have hpt : ∀ i : Fin 2, (∀ j, ψ i j = psIn d m ![i] (φ j)) → jptG t (𝟙 (Sp V)) d x' m i =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2) ≫ jptG t (𝟙 (Sp V)) d x m i := by
    intro i hi
    rw [jptG, jptG, hc m, ← Category.assoc, ← Category.assoc, GermD.homAt_comp, GermD.homAt_comp,
      copy_subst d m φ ψ i hi]
  have hfam : cφG t ![jptG t (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x' m (1 : Fin 2)] =
      fun I => (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2)).left ≫
        cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] I := by
    funext I
    rw [cφG, cφG, ← Over.comp_left, comp_psum']
    congr 2
    funext k
    fin_cases k
    · exact hpt 0 fun _ => rfl
    · exact hpt 1 fun _ => rfl
  obtain ⟨U, hU⟩ := exists_corr_scaled t.PP.L t.PP.isLB _ _ hfam (cε 2) (e' m)
    (peG t (𝟙 (Sp V)) d x e m ψ) (he' m) (DVR.pullGen_isGen _ _ _ _ (he m) _)
  obtain ⟨u, rfl⟩ := unitΓ_surj U
  obtain ⟨ε, hε⟩ := psJet_surj m (u : Jet V (Fin 2 × Fin d) m)
  refine ⟨ε, ?_, u, hε.symm, hU⟩
  rw [← GaugeR.jetAug_psJet m ε, hε]
  exact u.isUnit.map _

end GlobalTheory.ChartCmp.FrameRatio
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isFormalGroupLawOfChart_of_jetChart : ∀ (T : Type) [CommRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∀ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 → (∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left) → GlobalTheory.JetSer.IsLawOf x0 F.F := by
  first | exact @GlobalTheory.ChartJLaw.isLawOf_of_isChartJ | exact GlobalTheory.ChartJLaw.isLawOf_of_isChartJ | (intros; apply GlobalTheory.ChartJLaw.isLawOf_of_isChartJ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.isFrameG_coefficientRing_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (F : Fin d → PS S 2 d) (act : 𝓞 E → Fin d → PS S 1 d) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d), IsFrameG t x0 d x F act ph1 ph2 sy ad e → IsFrameG t x1 d x' (fun i => (MvPowerSeries.map ψ (F i))) (fun a i => (MvPowerSeries.map ψ (act a i))) (MvPowerSeries.map ψ ph1) (MvPowerSeries.map ψ ph2) (MvPowerSeries.map ψ sy) (fun a => (MvPowerSeries.map ψ (ad a))) e' := by
  first | exact @GlobalTheory.isFrameG_baseChange | exact GlobalTheory.isFrameG_baseChange | (intros; apply GlobalTheory.isFrameG_baseChange <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_jetChart_coordinates_nilpotent : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ → ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 → ∃ ψ : JetR R (Fin d) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin d) m ∧ y = spMap ψ ≫ x m := by
  first | exact @GlobalTheory.exists_jet_coordinates | exact GlobalTheory.exists_jet_coordinates | (intros; apply GlobalTheory.exists_jet_coordinates <;> assumption)
end
