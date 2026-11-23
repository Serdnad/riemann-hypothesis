module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle020
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)

theorem om_closed (i a c : Fin d) :
    pderiv ((0 : Fin 1), c) (Om G i a) = pderiv ((0 : Fin 1), a) (Om G i c) := by
  set M : Fin d → PS k 1 d := fun e => pderiv ((0 : Fin 1), e) (Om G i a) - pderiv ((0 : Fin 1), a) (Om G i e)
    with hMdef
  have hM : ∀ b, ∑ e, M e * Jac G e b = 0 := by
    intro b
    simp only [hMdef, sub_mul, Finset.sum_sub_distrib]
    rw [← om_key G i a b]
    simp only [mul_comm, sub_self]
  have h1 : M c = ∑ e, M e * (JM G * Om G) e c := by
    rw [mul_om]
    simp [Matrix.one_apply]
  have h2 : ∑ e, M e * (JM G * Om G) e c = 0 := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := hM b
    simp only [JM, Matrix.of_apply]
    rw [show ∑ x, M x * (Jac G x b * Om G b c) = (∑ x, M x * Jac G x b) * Om G b c by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring, this, zero_mul]
  have h3 : M c = 0 := h1.trans h2
  exact sub_eq_zero.1 h3

theorem d_evY (h : PS k 1 d) (b : Fin d) :
    pderiv ((1 : Fin 2), b) (ev (n := 2) ![pt k d 1] h) = ev (n := 2) ![pt k d 1] (pderiv ((0 : Fin 1), b) h) := by
  rw [pderiv_ev czY, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp [pderiv_pt]

theorem d_evX (h : PS k 1 d) (a : Fin d) :
    pderiv ((0 : Fin 2), a) (ev (n := 2) ![pt k d 0] h) = ev (n := 2) ![pt k d 0] (pderiv ((0 : Fin 1), a) h) := by
  rw [pderiv_ev czX, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp [pderiv_pt]

theorem pderiv_first_ev_second_point_eq_zero (h : PS k 1 d) (a : Fin d) : pderiv ((0 : Fin 2), a) (ev (n := 2) ![pt k d 1] h) = 0 :=
  pderiv_ev_zero czY _ _ (fun j l => by fin_cases j; simp [pderiv_pt])

theorem pderiv_second_ev_first_point_eq_zero (h : PS k 1 d) (b : Fin d) : pderiv ((1 : Fin 2), b) (ev (n := 2) ![pt k d 0] h) = 0 :=
  pderiv_ev_zero czX _ _ (fun j l => by fin_cases j; simp [pderiv_pt])

variable [Algebra ℚ k]

def logOf (i : Fin d) : PS k 1 d := prim (fun v : Fin 1 × Fin d => Om G i v.2)

theorem pderiv_logOf (i a : Fin d) : pderiv ((0 : Fin 1), a) (logOf G i) = Om G i a := by
  have hcl : ∀ v w : Fin 1 × Fin d, pderiv w (Om G i v.2) = pderiv v (Om G i w.2) := by
    rintro ⟨v1, v⟩ ⟨w1, w⟩
    obtain rfl : v1 = 0 := Subsingleton.elim _ _
    obtain rfl : w1 = 0 := Subsingleton.elim _ _
    exact om_closed G i v w
  exact pderiv_prim _ hcl ((0 : Fin 1), a)

theorem logOf_add (i : Fin d) :
    ev (n := 2) ![G.F] (logOf G i) = ev (n := 2) ![pt k d 0] (logOf G i) + ev (n := 2) ![pt k d 1] (logOf G i) := by
  rw [← sub_eq_zero]
  set g := ev (n := 2) ![G.F] (logOf G i) - (ev (n := 2) ![pt k d 0] (logOf G i) + ev (n := 2) ![pt k d 1] (logOf G i))
  have hd : ∀ v, pderiv v g = 0 := by
    rintro ⟨j, c⟩
    fin_cases j
    · simp only [Fin.zero_eta]
      simp only [g, map_sub, map_add (f := _), d_evF, pderiv_logOf, pderiv_first_ev_second_point_eq_zero, d_evX]
      rw [om_P G i c]; ring
    · simp only [Fin.mk_one]
      simp only [g, map_sub, map_add (f := _), d_evF, pderiv_logOf, pderiv_second_ev_first_point_eq_zero, d_evY]
      have := om_Q G i c
      simp only [Ar] at this
      rw [this]; ring
  have hc : constantCoeff g = 0 := by
    simp only [g, map_sub, map_add (f := _), cc_ev (czFF G), cc_ev czX, cc_ev czY, logOf, constantCoeff_prim]
    ring
  rw [eq_C_of_pderiv_zero hd, hc, map_zero]

theorem addPt : (![G.add (pt k (n := 2) d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) = ![G.F] := by
  funext j c
  fin_cases j
  show ev (n := 2) ![pt k d 0, pt k d 1] (G.F c) = G.F c
  have e : (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) = fun j => pt k (n := 2) d j := by
    funext j; fin_cases j <;> rfl
  rw [e, ev_pt]

theorem logSt : LogSt := by
  intro k _ _ d G
  refine ⟨fun i => logOf G i, fun i => constantCoeff_prim _, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    show coeff (Finsupp.single ((0 : Fin 1), j) 1) (logOf G i) = (1 : Matrix (Fin d) (Fin d) k) i j
    have h := congrArg constantCoeff (pderiv_logOf G i j)
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add] at h
    have h2 := congrFun (congrFun (cc_om G) i) j
    simp only [Matrix.map_apply] at h2
    simpa [h2] using h
  · funext i
    show ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (logOf G i) =
      ev (n := 2) ![pt k d 0] (logOf G i) + ev (n := 2) ![pt k d 1] (logOf G i)
    rw [addPt]
    exact logOf_add G i

omit [Algebra ℚ k] in
theorem ez_y (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] h) = C (constantCoeff h) := by
  rw [ev_ev cz1 czY]
  have e : (fun j c => ev (n := 1) ![pt k d 0, 0] ((![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) j c)) =
      fun (_ : Fin 1) (_ : Fin d) => (0 : PS k 1 d) := by
    funext j c; fin_cases j; simp [pt_apply, ev_X cz1]
  rw [e, ev_zeroFam]

theorem logDerivSt : LogDerivSt := by
  intro k _ _ d G ℓ h0 h1 hadd u g
  have hℓ : CZ (![ℓ] : Fin 1 → Pt k 1 d) := CZ.cons h0 CZ.nil
  have hadd' : ∀ c, ev (n := 2) ![G.F] (ℓ c) = ev (n := 2) ![pt k d 0] (ℓ c) + ev (n := 2) ![pt k d 1] (ℓ c) := by
    intro c
    have := congrFun hadd c
    change ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (ℓ c) = _ at this
    rwa [addPt] at this
  have DJ : ∀ c b, ∑ j, pderiv ((0 : Fin 1), j) (ℓ c) * Jac G j b = C (if c = b then 1 else 0) := by
    intro c b
    have h := congrArg (fun x => ev (n := 1) ![pt k d 0, 0] (pderiv ((1 : Fin 2), b) x)) (hadd' c)
    beta_reduce at h
    simp only [d_evF, map_add (f := _), pderiv_second_ev_first_point_eq_zero, d_evY, zero_add, ev_sum cz1, ev_mul cz1, ez_F, ez_dy, ez_y] at h
    rw [h]
    congr 1
    have hc := congrFun (congrFun h1 c) b
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
    simp only [dLin] at hc
    simp [hc, Matrix.one_apply]
  have hch : ∀ j, pderiv ((0 : Fin 1), j) (ev (n := 1) ![ℓ] g) =
      ∑ c, ev (n := 1) ![ℓ] (pderiv ((0 : Fin 1), c) g) * pderiv ((0 : Fin 1), j) (ℓ c) := by
    intro j
    rw [pderiv_ev hℓ, Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  have step : ∀ c, ∑ i, C (u i) * ∑ j, pderiv ((0 : Fin 1), j) (ℓ c) * Jac G j i = (C (u c) : PS k 1 d) := by
    intro c
    simp only [DJ, ← map_mul, mul_ite, mul_one, mul_zero]

    rw [← map_sum]
    simp [Finset.sum_ite_eq]
  show ∑ j : Fin d, (∑ i : Fin d, C (u i) * Jac G j i) * pderiv ((0 : Fin 1), j) (ev (n := 1) ![ℓ] g) = _
  simp only [hch]
  rw [ev_sum hℓ]
  calc ∑ j, (∑ i, C (u i) * Jac G j i) *
        ∑ c, ev (n := 1) ![ℓ] (pderiv ((0 : Fin 1), c) g) * pderiv ((0 : Fin 1), j) (ℓ c)
      = ∑ j, ∑ c, ∑ i, C (u i) * Jac G j i *
          (ev (n := 1) ![ℓ] (pderiv ((0 : Fin 1), c) g) * pderiv ((0 : Fin 1), j) (ℓ c)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul_sum, Finset.sum_comm]
    _ = ∑ c, ∑ j, ∑ i, C (u i) * Jac G j i *
          (ev (n := 1) ![ℓ] (pderiv ((0 : Fin 1), c) g) * pderiv ((0 : Fin 1), j) (ℓ c)) := Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ j, C (u i) * Jac G j i *
          (ev (n := 1) ![ℓ] (pderiv ((0 : Fin 1), c) g) * pderiv ((0 : Fin 1), j) (ℓ c)) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ev (n := 1) ![ℓ] (pderiv ((0 : Fin 1), c) g) *
          ∑ i, C (u i) * ∑ j, pderiv ((0 : Fin 1), j) (ℓ c) * Jac G j i := by
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [step, ev_mul hℓ, ev_C hℓ, mul_comm]

theorem logSt_and_logDerivSt : LogSt ∧ LogDerivSt := ⟨logSt, logDerivSt⟩

end GlobalTheory.FormalLog
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.GaugeBaseChange

open GlobalTheory.QuadDeriv

section

variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {d : ℕ}

theorem map_ev_two {n : ℕ} (a b : Pt k n d) (ha : GP a) (hb : GP b) (f : PS k 2 d) :
    MvPowerSeries.map φ (ev ![a, b] f) = ev ![mapP φ a, mapP φ b] (MvPowerSeries.map φ f) := by
  rw [map_ev φ _ (pair_points_zero_constant ha hb)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem baseChange_zero₂ {n : ℕ} : mapP φ (0 : Pt k n d) = 0 := funext fun _ => map_zero _

theorem map_expS [Algebra ℚ k] [Algebra ℚ k'] {n : ℕ} (f : PS k n d) (hf : constantCoeff f = 0) :
    MvPowerSeries.map φ (FB.expS k f) = FB.expS k' (MvPowerSeries.map φ f) := by
  unfold FB.expS
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf), PowerSeries.map_exp]

theorem map_dpolyOf (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (f : PS k 1 d) :
    MvPowerSeries.map φ (DpolyOf F u P f) =
      DpolyOf (mapP φ F) (fun l i => φ (u l i)) (MvPolynomial.map φ P) (MvPowerSeries.map φ f) := by

  rw [GE.dpolyOf_eq_sum_of_subset _ _ (MvPolynomial.map φ P) P.support
  (MvPolynomial.support_map_subset _ _), DpolyOf, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_C, GlobalTheory.map_dmonOf, MvPolynomial.coeff_map]
  rfl

end

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
  {k k' : Type} [CommRing k] [Algebra R k] [CommRing k'] [Algebra R k'] (β : k →ₐ[R] k')

theorem map_map_alg {σ : Type} (f : MvPowerSeries σ R) :
    MvPowerSeries.map (β : k →+* k') (MvPowerSeries.map (algebraMap R k) f) =
      MvPowerSeries.map (algebraMap R k') f := by
  ext m
  simp [coeff_map]

theorem mapP_FK : mapP (β : k →+* k') (B.FK k) = B.FK k' :=
  funext fun i => map_map_alg β (B.G.F i)

theorem baseChange_actK (a : O) : mapP (β : k →+* k') (B.actK k a) = B.actK k' a :=
  funext fun i => map_map_alg β (B.A.act a i)

theorem gp_FK : GP (B.FK k) := constantCoeff_mapP_eq_zero (algebraMap R k) _ B.G.const

theorem gp_actK (a : O) : GP (B.actK k a) := constantCoeff_mapP_eq_zero (algebraMap R k) _ (B.A.const a)

theorem const_of_axis {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) : constantCoeff h = 0 := by
  have := gt_const_ev_eq (n := 1) ![0, pt k d 0] (pair_points_zero_constant gp_zero₂ (gp_pt 0)) h
  rw [← this, h0, map_zero]

variable [Algebra ℚ k] [Algebra ℚ k']

theorem isCanonGauge_map {h : PS k 2 d} (H : B.IsCanonGauge k h) :
    B.IsCanonGauge k' (MvPowerSeries.map (β : k →+* k') h) := by
  have hc := const_of_axis H.ax0
  have c2 : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → constantCoeff (ev ![a, b] h) = 0 :=
    fun a b ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) h hc
  have gA : ∀ {n : ℕ} (i j : Fin n), GP (addOf (B.FK k) (pt k d i) (pt k d j)) :=
    fun i j => gp_addOf _ (gp_FK B) _ _ (gp_pt i) (gp_pt j)
  have gC : ∀ {n : ℕ} (a : O) (i : Fin n), GP (comp1 (B.actK k a) (pt k d i)) :=
    fun a i => gp_comp1 _ _ (gp_actK B a) (gp_pt i)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ax0
    rwa [map_ev_two _ _ _ gp_zero₂ (gp_pt 0), baseChange_zero₂, baseChange_pt, map_zero] at this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ax1
    rwa [map_ev_two _ _ _ (gp_pt 0) gp_zero₂, baseChange_zero₂, baseChange_pt, map_zero] at this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ph1
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, map_add (f := _), c2 _ _ (gp_pt _) (gp_pt _), c2 _ _ (gp_pt _) (gp_pt _),
        c2 _ _ (gA _ _) (gp_pt _), add_zero, sub_zero]), map_sub, map_add,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gp_pt _),
      map_ev_two _ _ _ (gA _ _) (gp_pt _), baseChange_addOf _ _ _ _ (gp_pt _) (gp_pt _), mapP_FK] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ph2
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, map_add (f := _), c2 _ _ (gp_pt _) (gp_pt _), c2 _ _ (gp_pt _) (gp_pt _),
        c2 _ _ (gp_pt _) (gA _ _), add_zero, sub_zero]), map_sub, map_add,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gp_pt _),
      map_ev_two _ _ _ (gp_pt _) (gA _ _), baseChange_addOf _ _ _ _ (gp_pt _) (gp_pt _), mapP_FK] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.sy
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, c2 _ _ (gp_pt _) (gp_pt _), hc, sub_zero]), map_sub,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _)] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) (H.ad a)
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, c2 _ _ (gC _ _) (gp_pt _), c2 _ _ (gp_pt _) (gC _ _), sub_zero]), map_sub,
      map_ev_two _ _ _ (gC _ _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gC _ _),
      baseChange_comp1 _ _ _ (gp_pt _), baseChange_comp1 _ _ _ (gp_pt _), baseChange_actK, baseChange_actK] at this
    simpa only [baseChange_pt] using this

theorem nabVal_map {h : PS k 2 d} (hc : constantCoeff h = 0) (w0 : O) (m : ℕ) (f : PS k 1 d) {Λ : Type}
    [Fintype Λ] (u : Λ → Fin d → k) (Q : MvPolynomial Λ k) :
    B.nabVal k' (MvPowerSeries.map (β : k →+* k') h) w0 m (MvPowerSeries.map (β : k →+* k') f)
      (fun l i => β (u l i)) (MvPolynomial.map (β : k →+* k') Q) = β (B.nabVal k h w0 m f u Q) := by
  have gC : GP (comp1 (B.actK k w0) (pt k (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL k h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map (β : k →+* k') (B.hL k h w0) =
      B.hL k' (MvPowerSeries.map (β : k →+* k') h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), baseChange_actK, baseChange_pt]
  unfold FB.nabVal
  change _ = (β : k →+* k') _
  rw [← MvPowerSeries.constantCoeff_map, map_dpolyOf, mapP_FK, map_mul,
    map_expS _ _ (by rw [MvPowerSeries.smul_eq_C_mul, map_mul, cL, mul_zero]),
    MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast (β : k →+* k'), eL]
  rfl

end GlobalTheory.GaugeBaseChange

namespace GlobalTheory

theorem canonGauge_nabVal_baseChange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k k' : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] [CommRing k'] [Algebra ℚ k'] [Algebra R k'] (β : k →ₐ[R] k') (h : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k' (MvPowerSeries.map (β : k →+* k') h) ∧ ∀ (w0 : O) (m : ℕ) (f : PS k 1 d) (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (Q : MvPolynomial Λ k), B.nabVal k' (MvPowerSeries.map (β : k →+* k') h) w0 m (MvPowerSeries.map (β : k →+* k') f) (fun l i => β (u l i)) (MvPolynomial.map (β : k →+* k') Q) = β (B.nabVal k h w0 m f u Q) := by
  intro R _ d O _ _ B k k' _ _ _ _ _ _ β h H
  exact ⟨GaugeBaseChange.isCanonGauge_map B β H, fun w0 m f _ _ u Q =>
    GaugeBaseChange.nabVal_map B β (GaugeBaseChange.const_of_axis H.ax0) w0 m f u Q⟩

end GlobalTheory
end
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.isWeaklyRegular_mvPowerSeries_of_finite_colength : ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : σ → MvPowerSeries σ k), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ Ideal.span (Set.range f)) → RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ k) (List.ofFn fun i => f (e i)) := by
  first | exact @GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le | exact GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le | (intros; apply GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.GaugeFirstLaw

variable {k : Type} [CommRing k] {d : ℕ}

theorem expS_inj [Algebra ℚ k] {n : ℕ} {a b : PS k n d} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (h : FB.expS k a = FB.expS k b) : a = b := exp_inj ha hb h

theorem expS_zero [Algebra ℚ k] {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := exp_zero

theorem ev_axis {n : ℕ} (a : Pt k n d) (ha : GP a) (h : PS k 2 d) :
    ev ![a] (ev (n := 1) ![pt k d 0, 0] h) = ev ![a, 0] h := by
  rw [gt_ev_ev' _ _ (single_point_zero_constant ha) (pair_points_zero_constant (gp_pt 0) gp_zero₂), eval_pair_points, evP_zero _ (single_point_zero_constant ha),
    evP_pt _ (single_point_zero_constant ha)]
  rfl

theorem pderiv_axis (h : PS k 2 d) (i : Fin d) :
    pderiv ((0 : Fin 1), i) (ev (n := 1) ![pt k d 0, 0] h) =
      ev (n := 1) ![pt k d 0, 0] (pderiv ((0 : Fin 2), i) h) := by
  rw [GlobalTheory.ChartTrans.pderiv_ev _ (pair_points_zero_constant (gp_pt 0) gp_zero₂), Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, map_zero, mul_zero,
    Finset.sum_const_zero, add_zero, pt]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [pderiv_X_of_ne (by simpa using hj), mul_zero]
  · simp

theorem exists_gauge_first_law :
    (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (c : PS k 3 d), ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 → ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c → ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c + ev (n := 4) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c = ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c + ev (n := 4) ![pt k d 0, addOf G.F (pt k d 1) (pt k d 2), pt k d 3] c → ∃ h : PS k 2 d, ev (n := 1) ![0, pt k d 0] h = 0 ∧ (∀ i, ev (n := 1) ![0, pt k d 0] (pderiv ((0 : Fin 2), i) h) = 0) ∧ c = (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (q : ℕ) (g : PS k (q + 1) d), ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1)) (fun j : Fin q => pt k d j.succ.succ)) g = ev (n := q + 2) (Fin.cons (pt k d 0) (fun j : Fin q => pt k d j.succ.succ)) g + ev (n := q + 2) (Fin.cons (pt k d 1) (fun j : Fin q => pt k d j.succ.succ)) g → (∀ i, ev (n := q) (Fin.cons 0 (fun j : Fin q => pt k d j)) (pderiv ((0 : Fin (q + 1)), i) g) = 0) → g = 0) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) := by
  intro H1 H2 k _ _ d O _ _ B
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hA : ∀ {n : ℕ} (i j : Fin n), GP (addOf B.G.F (pt k (n := n) d i) (pt k d j)) :=
    fun i j => gp_addOf _ B.G.const _ _ (hp i) (hp j)
  have h1 : constantCoeff B.ph1 = 1 := by
    have := congrArg constantCoeff B.cocycleLeft_zero_fst
    rwa [gt_const_ev_eq _ (triple_points_zero_constant hz (hp 0) (hp 1)), map_one] at this
  obtain ⟨c, hc0, hc⟩ : ∃ c : PS k 3 d, constantCoeff c = 0 ∧ B.ph1 = FB.expS k c :=
    ⟨_, constantCoeff_logS h1, (exp_log h1).symm⟩
  have E : ∀ {n : ℕ} (V : Fin 3 → Pt k n d), (∀ j, GP (V j)) →
      ev V B.ph1 = FB.expS k (ev V c) ∧ constantCoeff (ev V c) = 0 := by
    intro n V hV
    exact ⟨by rw [hc, gt_ev_expS V hV c hc0], gt_const_ev V hV c hc0⟩
  have a0 : ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 := by
    obtain ⟨e, e0⟩ := E (n := 2) _ (triple_points_zero_constant hz (hp 0) (hp 1))
    refine expS_inj e0 (map_zero _) ?_
    rw [← e, B.cocycleLeft_zero_fst, expS_zero]
  have a2 : ev (n := 2) ![pt k d 0, pt k d 1, 0] c = 0 := by
    obtain ⟨e, e0⟩ := E (n := 2) _ (triple_points_zero_constant (hp 0) (hp 1) hz)
    refine expS_inj e0 (map_zero _) ?_
    rw [← e, B.cocycleLeft_zero_thd, expS_zero]
  have cm : ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c := by
    obtain ⟨e, e0⟩ := E (n := 3) _ (triple_points_zero_constant (hp 1) (hp 0) (hp 2))
    refine expS_inj e0 hc0 ?_
    rw [← e, B.cocycleLeft_comm, hc]
  have as : ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c +
      ev (n := 4) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c =
      ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c +
      ev (n := 4) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2), pt k d 3] c := by
    obtain ⟨e1, f1⟩ := E (n := 4) _ (triple_points_zero_constant (hp 0) (hp 1) (hp 3))
    obtain ⟨e2, f2⟩ := E (n := 4) _ (triple_points_zero_constant (hA 0 1) (hp 2) (hp 3))
    obtain ⟨e3, f3⟩ := E (n := 4) _ (triple_points_zero_constant (hp 1) (hp 2) (hp 3))
    obtain ⟨e4, f4⟩ := E (n := 4) _ (triple_points_zero_constant (hp 0) (hA 1 2) (hp 3))
    refine expS_inj (by rw [map_add (f := _), f1, f2, add_zero]) (by rw [map_add (f := _), f3, f4, add_zero]) ?_
    rw [gt_expS_add _ _ f1 f2, gt_expS_add _ _ f3 f4, ← e1, ← e2, ← e3, ← e4]
    exact B.cocycleLeft_assoc
  obtain ⟨h, hx0, hd, hch⟩ := H1 k d B.G c a0 cm as
  refine ⟨h, ⟨hx0, ?_⟩, by rw [hc, hch]⟩
  have hV : ∀ j, GP ((![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) j) := triple_points_zero_constant (hp 0) (hp 1) hz
  rw [hch, gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hA 0 1) (hp 2)),
    eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ (hp 0) (hp 1),
    evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at a2
  have cons1 : ∀ {n : ℕ} (a : Pt k n d) (r : Fin 0 → Pt k n d),
      (Fin.cons a r : Fin (0 + 1) → Pt k n d) = ![a] := by
    intro n a r
    funext j
    fin_cases j
    rfl
  refine H2 k d B.G 0 (ev (n := 1) ![pt k d 0, 0] h) ?_ ?_
  · rw [cons1, cons1, cons1]
    have t0 := ev_axis (pt k (n := 2) d 0) (hp 0) h
    have t1 := ev_axis (pt k (n := 2) d 1) (hp 1) h
    have t2 := ev_axis _ (hA (n := 2) 0 1) h
    refine t2.trans (Eq.trans ?_ (congrArg₂ (· + ·) t0 t1).symm)
    exact (sub_eq_zero.1 a2).symm
  · intro i
    rw [cons1]
    have hZ : ∀ j, GP ((![0] : Fin 1 → Pt k 0 d) j) := single_point_zero_constant hz
    have e := congrArg (ev (n := 0) ![0]) (hd i)
    rw [gt_ev_ev' _ _ hZ (pair_points_zero_constant hz (hp 0)), eval_pair_points, evP_zero _ hZ, evP_pt _ hZ,
      gt_ev_zero _ hZ] at e
    refine (congrArg (ev (n := 0) ![0]) (pderiv_axis h i)).trans ?_
    rw [ev_axis _ hz]
    exact e

end GlobalTheory.GaugeFirstLaw
end
end
