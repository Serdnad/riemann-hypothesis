module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle006
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle003
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle004
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Field
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_ev {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have hz : CZ (fun (_ : Fin n) (_ : Fin d) => (0 : PS k n d)) := fun _ _ => map_zero _
  have h1 := ev_zeroFam (n := n) (ev a f)
  rw [ev_ev hz ha] at h1
  have e : (fun j i => ev (fun (_ : Fin n) (_ : Fin d) => (0 : PS k n d)) (a j i)) =
      fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d) := by
    funext j i; rw [ev_zeroFam, ha j i, map_zero]
  rw [e, ev_zeroFam] at h1
  simpa using (congrArg constantCoeff h1).symm

variable (G : FGLaw k d)

theorem formalFamilyConstantCoeffZero_zero_secondVar : CZ (![0, pt k (n := 1) d 0] : Fin 2 → Pt k 1 d) := CZ.cons cc_zero (CZ.cons (cc_pt 0) CZ.nil)

theorem cc_jac (i b : Fin d) : constantCoeff (Jac G i b) = if i = b then 1 else 0 := by
  rw [Jac, cc_ev cz1, ← cc_ev formalFamilyConstantCoeffZero_zero_secondVar]
  have h := congrArg (pderiv (R := k) ((0 : Fin 1), b)) (G.unit i)
  rw [pderiv_ev formalFamilyConstantCoeffZero_zero_secondVar, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, map_zero, mul_zero,
    Finset.sum_const_zero, zero_add, pderiv_pt] at h
  simp only [Fin.isValue, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  rw [h, pderiv_X]
  simp [Pi.single_apply, eq_comm]

def JM : Matrix (Fin d) (Fin d) (PS k 1 d) := Matrix.of (Jac G)

def Om : Matrix (Fin d) (Fin d) (PS k 1 d) := (JM G)⁻¹

theorem jm_map_cc : (JM G).map constantCoeff = 1 := by
  refine Matrix.ext fun i b => ?_
  simp [JM, cc_jac, Matrix.one_apply]

theorem isUnit_det_jm : IsUnit (JM G).det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, jm_map_cc,
    Matrix.det_one]
  exact isUnit_one

theorem om_mul : Om G * JM G = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_jm G)

theorem mul_om : JM G * Om G = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_jm G)

theorem map_ev_mul {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (M N : Matrix (Fin d) (Fin d) (PS k m d)) :
    (M * N).map (ev a) = M.map (ev a) * N.map (ev a) := by
  have h : (M * N).map (evHom ha) = M.map (evHom ha) * N.map (evHom ha) := Matrix.map_mul
  have e : (⇑(evHom ha)) = ev a := funext (evHom_apply ha)
  rw [e] at h
  exact h

theorem map_ev_one {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) :
    (1 : Matrix (Fin d) (Fin d) (PS k m d)).map (ev a) = 1 := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h; simp [← evHom_apply ha]
  · simp [h, ev_zero' ha]

theorem cc_om : (Om G).map constantCoeff = 1 := by
  have h := congrArg (fun M => M.map constantCoeff) (mul_om G)
  simp only [Matrix.map_mul (f := constantCoeff), jm_map_cc, Matrix.one_mul] at h
  rw [h]; refine Matrix.ext fun i j => ?_; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem om_Q (i b : Fin d) : ∑ j, ev (n := 2) ![G.F] (Om G i j) * Ar G j b = ev (n := 2) ![pt k d 1] (Om G i b) := by
  have hJ : (JM G).map (ev (n := 2) ![G.F]) = Matrix.of (Ar G) * (JM G).map (ev (n := 2) ![pt k d 1]) := by
    refine Matrix.ext fun i b => ?_
    simp only [Matrix.map_apply, JM, Matrix.of_apply, Matrix.mul_apply]
    exact jac_F G i b
  have hy : (JM G).map (ev (n := 2) ![pt k d 1]) * (Om G).map (ev (n := 2) ![pt k d 1]) = 1 := by
    rw [← map_ev_mul czY, mul_om, map_ev_one czY]
  have hF : (Om G).map (ev (n := 2) ![G.F]) * (JM G).map (ev (n := 2) ![G.F]) = 1 := by
    rw [← map_ev_mul (czFF G), om_mul, map_ev_one (czFF G)]
  have key : (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G) = (Om G).map (ev (n := 2) ![pt k d 1]) := by
    calc _ = (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G) *
          ((JM G).map (ev (n := 2) ![pt k d 1]) * (Om G).map (ev (n := 2) ![pt k d 1])) := by rw [hy, Matrix.mul_one]
      _ = (Om G).map (ev (n := 2) ![G.F]) * (JM G).map (ev (n := 2) ![G.F]) *
          (Om G).map (ev (n := 2) ![pt k d 1]) := by rw [hJ, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = _ := by rw [hF, Matrix.one_mul]
  have := congrFun (congrFun key i) b
  simpa [Matrix.mul_apply] using this

theorem czSw : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)
theorem czX : CZ (![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt 0) CZ.nil

theorem sw_F (h : PS k 1 d) : ev (n := 2) ![pt k d 1, pt k d 0] (ev (n := 2) ![G.F] h) = ev (n := 2) ![G.F] h := by
  rw [ev_ev czSw (czFF G)]
  congr 1
  funext j c
  fin_cases j
  exact G.comm c

theorem sw_y (h : PS k 1 d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (ev (n := 2) ![pt k d 1] h) = ev (n := 2) ![pt k d 0] h := by
  rw [ev_ev czSw czY]
  congr 1
  funext j c
  fin_cases j
  simp [pt_apply, ev_X czSw]

theorem sw_dF (j b : Fin d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (pderiv (R := k) ((1 : Fin 2), b) (G.F j)) = pderiv (R := k) ((0 : Fin 2), b) (G.F j) := by
  have h := congrArg (pderiv (R := k) ((0 : Fin 2), b)) (G.comm j)
  rw [pderiv_ev czSw, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pderiv_pt] at h
  exact h

theorem om_P (i a : Fin d) :
    ∑ j, ev (n := 2) ![G.F] (Om G i j) * pderiv (R := k) ((0 : Fin 2), a) (G.F j) = ev (n := 2) ![pt k d 0] (Om G i a) := by
  have h := congrArg (ev (n := 2) ![pt k d 1, pt k d 0]) (om_Q G i a)
  rw [ev_sum czSw, sw_y] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_mul czSw, sw_F, Ar, sw_dF]

theorem d_evF (h : PS k 1 d) (v : Fin 2 × Fin d) :
    pderiv (R := k) v (ev (n := 2) ![G.F] h) = ∑ c, ev (n := 2) ![G.F] (pderiv (R := k) ((0 : Fin 1), c) h) * pderiv (R := k) v (G.F c) := by
  rw [pderiv_ev (czFF G), Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem ez_F (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  rw [ev_ev cz1 (czFF G)]
  conv_rhs => rw [← ev_pt h]
  congr 1
  funext j c
  fin_cases j
  exact formalGroupLaw_ev_x_zero G c

theorem ez_dx (j a : Fin d) :
    ev (n := 1) ![pt k d 0, 0] (pderiv (R := k) ((0 : Fin 2), a) (G.F j)) = if j = a then 1 else 0 := by
  have h := congrArg (pderiv (R := k) ((0 : Fin 1), a)) (formalGroupLaw_ev_x_zero G j)
  rw [pderiv_ev cz1, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pderiv_pt] at h
  rw [h, pderiv_X]
  simp [Pi.single_apply]

theorem ez_dy (c b : Fin d) : ev (n := 1) ![pt k d 0, 0] (pderiv (R := k) ((1 : Fin 2), b) (G.F c)) = Jac G c b := rfl

theorem om_key (i a b : Fin d) :
    ∑ j, Jac G j b * pderiv (R := k) ((0 : Fin 1), a) (Om G i j) = ∑ c, pderiv (R := k) ((0 : Fin 1), c) (Om G i a) * Jac G c b := by
  have hQ := congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv (R := k) ((0 : Fin 2), a) g)) (om_Q G i b)
  have hP := congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv (R := k) ((1 : Fin 2), b) g)) (om_P G i a)
  beta_reduce at hQ hP
  rw [pderiv_ev_zero czY _ _ (fun j l => by fin_cases j; simp [pderiv_pt]), ev_zero' cz1] at hQ
  rw [pderiv_ev_zero czX _ _ (fun j l => by fin_cases j; simp [pderiv_pt]), ev_zero' cz1] at hP

  simp only [map_sum, Derivation.leibniz, smul_eq_mul, d_evF, ev_sum cz1, ev_add cz1, ev_mul cz1, ez_F, ez_dx,
  ez_dy, Ar, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hQ hP
  rw [Finset.sum_add_distrib] at hQ hP
  have hR : ∑ j, Om G i j * ev (n := 1) ![pt k d 0, 0] (pderiv (R := k) ((0 : Fin 2), a) (pderiv (R := k) ((1 : Fin 2), b) (G.F j))) =
      ∑ j, Om G i j * ev (n := 1) ![pt k d 0, 0] (pderiv (R := k) ((1 : Fin 2), b) (pderiv (R := k) ((0 : Fin 2), a) (G.F j))) := by
    simp only [pderiv_comm ((0 : Fin 2), a) ((1 : Fin 2), b)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, one_mul, zero_mul] at hQ hP
  rw [hR] at hQ
  linear_combination hQ - hP

end GlobalTheory.FormalLog
end
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem pow_span_X_le_and_finite_quotient_of_le_sup_pow_succ : ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (I : Ideal (MvPowerSeries σ k)) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ I ⊔ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ (M + 1) → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ I ∧ Module.Finite k (MvPowerSeries σ k ⧸ I) := by
  intro k _ σ _ I M h
  set m : Ideal (MvPowerSeries σ k) := Ideal.span (Set.range MvPowerSeries.X) with hm
  have hfg : m.FG := Submodule.fg_span (Set.finite_range _)
  have hjac : m ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hm, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hle : m ^ M ≤ I := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (N' := m ^ M) (N := I) (I := m)
      (Ideal.FG.pow hfg) hjac ?_
    rw [pow_succ'] at h
    exact h
  exact ⟨hle, FormalIsogeny.finite_quotient_of_pow_le (N := M) hle⟩

end GlobalTheory
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isWeaklyRegular_mvPowerSeries_of_pow_le :
    ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ)
      (f : σ → MvPowerSeries σ k), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) →
      (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤
        Ideal.span (Set.range f)) →
      RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ k) (List.ofFn fun i => f (e i)) := by
  rintro k _ σ _ n e f h0 ⟨M, hM⟩
  have := FormalIsogeny.isRegularLocalRing_mvPowerSeries k σ
  refine (isRegular_of_radical_eq_maximalIdeal ?_ ?_).1
  · have h1 : Ideal.ofList (List.ofFn fun i => f (e i)) = Ideal.span (Set.range f) := by
      rw [ofList_ofFn_eq_span_range]
      exact congrArg Ideal.span (e.surjective.range_comp f)
    rw [h1]
    refine le_antisymm ((maximalIdeal.isMaximal _).isPrime.radical_le_iff.2 ?_) fun g hg => ?_
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp [h0])
    · have h2 : MvPowerSeries.constantCoeff g = 0 := by
        simpa [maximalIdeal_eq_bot] using FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
      have h3 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) := by
        rw [← germIdeal_eq_span]
        exact h2
      exact ⟨M, hM (Ideal.pow_mem_pow h3 M)⟩
  · rw [FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_field, zero_add,
      List.length_ofFn, ← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory

theorem canonGauge_sub_isBiadd : G2.CanonicalGaugeDiffBiadditive := by
  intro R _ d O _ _ k _ _ _ B h h' hh hh'
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hF : ∀ i, constantCoeff (B.FK k i) = 0 := fun i => by
    simp only [FB.FK, FGLaw.mapF, MvPowerSeries.constantCoeff_map, B.G.const i, map_zero]
  have hA : ∀ a, GP (B.actK k a) := fun a i => by
    simp only [FB.actK, MvPowerSeries.constantCoeff_map, B.A.const a i, map_zero]
  have h0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero] at this
  have h0' : constantCoeff h' = 0 := by
    have := congrArg constantCoeff hh'.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero] at this
  have inj : ∀ {n : ℕ} {a b : PS k n d}, constantCoeff a = 0 → constantCoeff b = 0 →
      FB.expS k a = FB.expS k b → a = b := fun ha hb e => exp_inj ha hb e
  refine ⟨?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_sub _ (pair_points_zero_constant hz (hp 0)), hh.ax0, hh'.ax0, sub_zero]
  · rw [gt_ev_sub _ (pair_points_zero_constant (hp 0) hz), hh.ax1, hh'.ax1, sub_zero]
  · have a1 := pair_points_zero_constant (hp (n := 3) 0) (hp 2)
    have a2 := pair_points_zero_constant (hp (n := 3) 1) (hp 2)
    have a3 := pair_points_zero_constant (gp_addOf _ hF _ _ (hp (n := 3) 0) (hp 1)) (hp 2)
    have e := inj
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp)
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp)
      (hh.ph1.symm.trans hh'.ph1)
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]
    linear_combination -e
  · have a1 := pair_points_zero_constant (hp (n := 3) 0) (hp 1)
    have a2 := pair_points_zero_constant (hp (n := 3) 0) (hp 2)
    have a3 := pair_points_zero_constant (hp (n := 3) 0) (gp_addOf _ hF _ _ (hp (n := 3) 1) (hp 2))
    have e := inj
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp)
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp)
      (hh.ph2.symm.trans hh'.ph2)
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]
    linear_combination -e
  · have a1 := pair_points_zero_constant (gp_comp1 _ _ (hA a) (hp (n := 2) 0)) (hp 1)
    have a2 := pair_points_zero_constant (hp (n := 2) 0) (gp_comp1 _ _ (hA (star a)) (hp (n := 2) 1))
    have e := inj
      (by rw [map_sub, gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, sub_zero])
      (by rw [map_sub, gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', sub_zero])
      ((hh.ad a).symm.trans (hh'.ad a))
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2]
    linear_combination -e

end GlobalTheory
end
end

section

set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem germ_expS_add : G2.ExpAddZeroConstant :=
  fun _ _ _ _ _ f g hf hg => WickVanishing.gt_expS_add f g hf hg

theorem germ_constantCoeff_ev : G2.ConstantCoeffSubstitution :=
  fun _ _ _ _ _ a f ha => WickVanishing.gt_const_ev_eq a ha f

theorem germ_expAdd_and_evConst : G2.ExpAddZeroConstant ∧ G2.ConstantCoeffSubstitution :=
  ⟨germ_expS_add, germ_constantCoeff_ev⟩

end GlobalTheory
end
