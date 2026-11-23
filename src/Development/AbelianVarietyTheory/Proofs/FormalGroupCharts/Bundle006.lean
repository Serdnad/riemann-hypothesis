module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.MvPolynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt k (n := n) d j i) = 0 := by
  show constantCoeff (X (j, i) : PS k n d) = 0
  simp

theorem cc_zero {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt k n d) i) = 0 := by simp

theorem CZ.nil {n : ℕ} : CZ (![] : Fin 0 → Pt k n d) := fun j => j.elim0

theorem CZ.cons {m n : ℕ} {p : Pt k n d} {a : Fin m → Pt k n d} (hp : ∀ i, constantCoeff (p i) = 0) (ha : CZ a) :
    CZ (Matrix.vecCons p a) := by
  intro j i
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa using hp i
  · simpa using ha j i

theorem pt_apply {n : ℕ} (j : Fin n) (i : Fin d) : pt k (n := n) d j i = (X (j, i) : PS k n d) := rfl

variable (G : FGLaw k d)

theorem formalGroupLaw_ev_x_zero (i : Fin d) : ev (n := 1) ![pt k d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  have hz : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt 0) (CZ.cons cc_zero CZ.nil)
  have hs : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)
  have h := congrArg (ev (n := 1) ![pt k d 0, 0]) (G.comm i)
  rw [ev_ev hz hs] at h
  have e : (fun j c => ev (n := 1) ![pt k d 0, 0] ((![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) j c)) =
      (![0, pt k (n := 1) d 0] : Fin 2 → Pt k 1 d) := by
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X hz]
  rw [e, G.unit] at h
  exact h.symm

theorem pderiv_ev_zero {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d)
    (h : ∀ j i, pderiv v (a j i) = 0) : pderiv v (ev a f) = 0 := by
  rw [pderiv_ev ha]; simp [h]

theorem pderiv_pt {n : ℕ} (v : Fin n × Fin d) (j : Fin n) (i : Fin d) :
    pderiv v (pt k (n := n) d j i) = if (j, i) = v then 1 else 0 := by
  classical
  rw [pt_apply, pderiv_X]
  simp [Pi.single_apply, eq_comm]

def Jac (G : FGLaw k d) : Fin d → Fin d → PS k 1 d := fun i b => ev (n := 1) ![pt k d 0, 0] (pderiv ((1 : Fin 2), b) (G.F i))

def Ar (G : FGLaw k d) : Fin d → Fin d → PS k 2 d := fun i b => pderiv ((1 : Fin 2), b) (G.F i)

section Fams

theorem cz1 : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt 0) (CZ.cons cc_zero CZ.nil)
theorem czY : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt 1) CZ.nil
theorem czZ : CZ (![pt k (n := 2) d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) :=
  CZ.cons (cc_pt 0) (CZ.cons (cc_pt 1) (CZ.cons cc_zero CZ.nil))
theorem czFF : CZ (![G.F] : Fin 1 → Pt k 2 d) := CZ.cons G.const CZ.nil
theorem cz01 : CZ (![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 0) (CZ.cons (cc_pt 1) CZ.nil)
theorem cz12 : CZ (![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 2) CZ.nil)

end Fams

theorem formal_ev_second_point_of_x_zero (g : PS k 2 d) :
    ev (n := 2) ![pt k d 1] (ev (n := 1) ![pt k d 0, 0] g) = ev (n := 2) ![pt k d 1, 0] g := by
  rw [ev_ev czY cz1]
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czY, ev_zero' czY]

theorem ev_z_yz (g : PS k 2 d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] g) = ev (n := 2) ![pt k d 1, 0] g := by
  rw [ev_ev czZ cz12]
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czZ]

theorem formalGroupLaw_ev_y_zero (c : Fin d) : ev (n := 2) ![pt k d 1, 0] (G.F c) = (X ((1 : Fin 2), c) : PS k 2 d) := by
  rw [← formal_ev_second_point_of_x_zero, formalGroupLaw_ev_x_zero, ev_X czY]; rfl

theorem jac_F (i b : Fin d) :
    ev (n := 2) ![G.F] (Jac G i b) = ∑ c, Ar G i c * ev (n := 2) ![pt k d 1] (Jac G c b) := by
  set aL : Fin 2 → Pt k 3 d := ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] with haL
  set aR : Fin 2 → Pt k 3 d := ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] with haR
  have hL : CZ aL := CZ.cons (fun l => constantCoeff_ev cz01 (G.const l)) (CZ.cons (cc_pt 2) CZ.nil)
  have hR : CZ aR := CZ.cons (cc_pt 0) (CZ.cons (fun l => constantCoeff_ev cz12 (G.const l)) CZ.nil)
  have dL : pderiv ((2 : Fin 3), b) (ev aL (G.F i)) = ev aL (pderiv ((1 : Fin 2), b) (G.F i)) := by
    rw [pderiv_ev hL, Fintype.sum_prod_type, Fin.sum_univ_two]
    have h0 : ∀ c, pderiv ((2 : Fin 3), b) (aL 0 c) = 0 := fun c =>
      pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
    simp only [h0, mul_zero, Finset.sum_const_zero, zero_add]
    simp [haL, pderiv_pt]
  have dR : pderiv ((2 : Fin 3), b) (ev aR (G.F i)) = ∑ c, ev aR (pderiv ((1 : Fin 2), c) (G.F i)) *
      ev (n := 3) ![pt k d 1, pt k d 2] (pderiv ((1 : Fin 2), b) (G.F c)) := by
    rw [pderiv_ev hR, Fintype.sum_prod_type, Fin.sum_univ_two]
    have h0 : ∀ c, pderiv ((2 : Fin 3), b) (aR 0 c) = 0 := fun c => by simp [haR, pderiv_pt]
    have h1 : ∀ c, pderiv ((2 : Fin 3), b) (aR 1 c) =
        ev (n := 3) ![pt k d 1, pt k d 2] (pderiv ((1 : Fin 2), b) (G.F c)) := fun c => by
      simp only [haR, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [pderiv_ev cz12, Fintype.sum_prod_type, Fin.sum_univ_two]
      simp [pderiv_pt]
    simp only [h0, h1, mul_zero, Finset.sum_const_zero, zero_add]
  have h := congrArg (fun g => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv ((2 : Fin 3), b) g)) (G.assoc i)
  beta_reduce at h
  rw [dL, dR, ev_sum czZ] at h
  have eL : ∀ g : PS k 2 d, ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev aL g) = ev (n := 2) ![G.F, 0] g := by
    intro g
    rw [ev_ev czZ hL]
    congr 1
    funext j c
    fin_cases j
    · show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 0, pt k d 1] (G.F c)) = G.F c
      rw [ev_ev czZ cz01]
      have : (fun j c => ev (n := 2) ![pt k d 0, pt k d 1, 0] ((![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) j c)) =
          fun j => pt k (n := 2) d j := by
        funext j c; fin_cases j <;> simp [pt_apply, ev_X czZ]
      rw [this, ev_pt]
    · simp [haL, pt_apply, ev_X czZ]
  have eR : ∀ g : PS k 2 d, ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev aR g) = g := by
    intro g
    rw [ev_ev czZ hR]
    conv_rhs => rw [← ev_pt g]
    congr 1
    funext j c
    fin_cases j
    · simp [haR, pt_apply, ev_X czZ]
    · show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] (G.F c)) = X ((1 : Fin 2), c)
      rw [ev_z_yz, formalGroupLaw_ev_y_zero]
  have eJ : ev (n := 2) ![G.F] (Jac G i b) = ev (n := 2) ![G.F, 0] (pderiv ((1 : Fin 2), b) (G.F i)) := by
    rw [Jac, ev_ev (czFF G) cz1]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X (czFF G), ev_zero' (czFF G)]
  rw [eL, ← eJ] at h
  rw [h]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ev_mul czZ, eR, ev_z_yz, ← formal_ev_second_point_of_x_zero]
  rfl

end GlobalTheory.FormalLog
end
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory.NoTangent

open MvPowerSeries

theorem leibniz_eq_zero {O C σ : Type} [CommRing O] [CommRing C]
    (φ₀ : MvPowerSeries σ O →+* C) (E : MvPowerSeries σ O →+ C) (a : σ → O)
    (hmul : ∀ g h, E (g * h) = φ₀ g * E h + φ₀ h * E g)
    (hC : ∀ c, E (MvPowerSeries.C c) = 0) (hX : ∀ j, E (X j) = 0)
    (ha : ∀ j, φ₀ (X j - MvPowerSeries.C (a j)) = 0)
    (hP : ∀ g : MvPowerSeries σ O, ∃ P : MvPolynomial σ O,
      g - (P : MvPowerSeries σ O) ∈
        Ideal.span (Set.range fun j => (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)))
    (g : MvPowerSeries σ O) : E g = 0 := by
  have h1 : ∀ P : MvPolynomial σ O, E (P : MvPowerSeries σ O) = 0 := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.coe_C]; exact hC c
    | add p q hp hq => rw [MvPolynomial.coe_add, map_add (f := _), hp, hq, add_zero]
    | mul_X p j hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, hmul, hp, hX]; simp
  have h2 : ∀ h ∈ Ideal.span (Set.range fun j =>
      (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)), φ₀ h = 0 ∧ E h = 0 := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact ⟨ha j, by simp only [map_sub, hX, hC, sub_zero]⟩
    | zero => simp
    | add x y _ _ hx hy => simp [hx.1, hx.2, hy.1, hy.2]
    | smul s x _ hx => simp [hmul, hx.1, hx.2]
  obtain ⟨P, hP⟩ := hP g
  have := (h2 _ hP).2
  rwa [map_sub, h1, sub_zero] at this

theorem finite_quotient {O σ : Type} [CommRing O] [Finite σ] (I : Ideal (MvPowerSeries σ O))
    (M : ℕ) (h : ∀ g : MvPowerSeries σ O, ∃ P : MvPolynomial σ O, P.totalDegree ≤ M ∧
      g - (P : MvPowerSeries σ O) ∈ I) : Module.Finite O (MvPowerSeries σ O ⧸ I) := by
  let L : MvPolynomial.restrictTotalDegree σ O M →ₗ[O] (MvPowerSeries σ O ⧸ I) :=
    (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ
      (MvPolynomial.coeToMvPowerSeries.algHom (σ := σ) (R := O) O).toLinearMap ∘ₗ
      (MvPolynomial.restrictTotalDegree σ O M).subtype
  refine Module.Finite.of_surjective L ?_
  intro q
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨P, hP, hg⟩ := h g
  refine ⟨⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩, ?_⟩
  have : L ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩ =
      Ideal.Quotient.mk I (P : MvPowerSeries σ O) := by
    simp [L]
  rw [this]
  exact (Ideal.Quotient.eq.2 hg).symm

theorem algHom_dualNumber_ext : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (p : ℕ), p ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O → ∀ J : Ideal O, J.FG → J ≠ ⊤ → (p : O) ∈ J → ∀ (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : Fin n → MvPowerSeries σ O) (M N : ℕ) (U : (MvPowerSeries σ O)ˣ), N ≠ 0 → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : O →+* MvPowerSeries σ O) J → Matrix.det (Matrix.of fun i j : Fin n => MvPowerSeries.pderiv (R := O) (e j) (f i)) = (N : MvPowerSeries σ O) * U → ∀ φ φ' : (MvPowerSeries σ O ⧸ Ideal.span (Set.range f)) →ₐ[O] DualNumber C, (∀ a, (φ a).fst = (φ' a).fst) → φ = φ' := by
  intro C _ _ _ v O _ _ hv p hp hc J hJ hJt hpJ σ _ n e f M N U hN hM hdet φ φ' hfst
  classical
  have hJc := GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers C v O hv p hp hc J hJ hJt hpJ
  have hfin := finite_quotient _ M (GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem O J hJ hJc σ (Fin n) f M hM)
  let I := Ideal.span (Set.range f)
  let ψ : MvPowerSeries σ O →ₐ[O] DualNumber C := φ.comp (Ideal.Quotient.mkₐ O I)
  let ψ' : MvPowerSeries σ O →ₐ[O] DualNumber C := φ'.comp (Ideal.Quotient.mkₐ O I)
  let φ₀ : MvPowerSeries σ O →ₐ[O] C := (TrivSqZeroExt.fstHom O C C).comp ψ
  have h0 : ∀ g, (ψ g).fst = φ₀ g := fun g => rfl
  have h0' : ∀ g, (ψ' g).fst = φ₀ g := fun g => (hfst _).symm
  have hψI : ∀ g ∈ I, ψ g = 0 := fun g hg => by
    simp [ψ, Ideal.Quotient.eq_zero_iff_mem.2 hg]
  have hψI' : ∀ g ∈ I, ψ' g = 0 := fun g hg => by
    simp [ψ', Ideal.Quotient.eq_zero_iff_mem.2 hg]
  have hCa : ∀ c : O, (MvPowerSeries.C c : MvPowerSeries σ O) = algebraMap O _ c := fun c => rfl
  have hle : ∀ g, v (φ₀ g) ≤ 1 := by
    intro g
    have h1 : IsIntegral O (Ideal.Quotient.mkₐ O I g) := Algebra.IsIntegral.isIntegral _
    have h2 := h1.map ((TrivSqZeroExt.fstHom O C C).comp φ)
    exact hv.mem_of_integral h2
  choose a ha using fun j => hv.exists_of_le_one (hle (X j))
  let K : Ideal (MvPowerSeries σ O) :=
    { carrier := {g | v (φ₀ g) < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at hx hy ⊢
        exact v.map_add_lt hx hy
      zero_mem' := by simp
      smul_mem' := fun s x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hx ⊢
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle s) zero_le hx }
  have hK : ∀ g, g ∈ K ↔ v (φ₀ g) < 1 := fun g => Iff.rfl
  have hJK : J ≤ K.comap (MvPowerSeries.C : O →+* MvPowerSeries σ O) := by
    intro c hc
    rw [Ideal.mem_comap, hK, hCa, AlgHom.commutes]
    refine lt_of_le_of_ne (hv.map_le_one c) fun h => hJt ?_
    exact J.eq_top_of_isUnit_mem hc (hv.isUnit_of_one' h)
  have hIK : I ≤ K := by
    intro g hg
    rw [hK, ← h0, hψI g hg]; simp
  have hXK : ∀ j, X j ∈ K := by
    intro j
    have h1 : (X j : MvPowerSeries σ O) ^ M ∈ K :=
      (hM.trans (sup_le hIK (Ideal.map_le_iff_le_comap.2 hJK)))
        (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) M)
    rw [hK, map_pow, map_pow] at h1
    have hM0 : M ≠ 0 := by
      intro h
      subst M
      simp at h1
    rw [hK]
    exact (pow_lt_one_iff_of_nonneg zero_le hM0).1 h1
  let J' : Ideal O := J ⊔ Ideal.span (Set.range a)
  have hJ' : J'.FG := Submodule.FG.sup hJ (Submodule.fg_span (Set.finite_range a))
  have hJ'K : J' ≤ K.comap (MvPowerSeries.C : O →+* MvPowerSeries σ O) := by
    refine sup_le hJK (Ideal.span_le.2 ?_)
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, hK, hCa, AlgHom.commutes, ha]
    exact hXK j
  have hJ't : J' ≠ ⊤ := by
    intro h
    have : (1 : O) ∈ J' := h ▸ Submodule.mem_top
    have h2 := hJ'K this
    rw [Ideal.mem_comap, hK] at h2
    simp at h2
  have hJ'c := GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers C v O hv p hp hc J' hJ' hJ't (Ideal.mem_sup_left hpJ)
  have hP := GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem O J' hJ' hJ'c σ σ
    (fun j => (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)) 1 (by
      rw [pow_one, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : (X j : MvPowerSeries σ O) =
          (X j - MvPowerSeries.C (a j)) + MvPowerSeries.C (a j) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.subset_span ⟨j, rfl⟩)
        (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))))
  let d : Fin n → C := fun j => (ψ' (X (e j))).snd - (ψ (X (e j))).snd
  let E : MvPowerSeries σ O →+ C :=
    { toFun := fun g => (ψ' g).snd - (ψ g).snd - ∑ j, φ₀ (pderiv (R := O) (e j) g) * d j
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [map_add (f := _), TrivSqZeroExt.snd_add, add_mul, Finset.sum_add_distrib]; ring }
  have hE : ∀ g, E g = (ψ' g).snd - (ψ g).snd - ∑ j, φ₀ (pderiv (R := O) (e j) g) * d j :=
    fun g => rfl
  have hE0 : ∀ g, E g = 0 := by
    refine leibniz_eq_zero (φ₀ : MvPowerSeries σ O →+* C) E a ?_ ?_ ?_ ?_
      (fun g => (hP g).imp fun P h => h.2)
    · intro g h
      simp only [hE, map_mul, DualNumber.snd_mul, h0, h0', Derivation.leibniz, smul_eq_mul,
        map_add, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
        RingHom.coe_coe]
      ring
    · intro c
      rw [hE]
      simp only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero, sub_zero]
      rw [hCa, AlgHom.commutes, AlgHom.commutes, sub_self]
    · intro s
      obtain ⟨k, rfl⟩ := e.surjective s
      rw [hE, Finset.sum_eq_single k]
      · simp [d, pderiv_X]
      · intro j _ hj
        simp [pderiv_X, hj, hj.symm]
      · simp
    · intro j
      rw [RingHom.coe_coe, map_sub, hCa, AlgHom.commutes, ha, sub_self]
  have hd : d = 0 := by
    let A : Matrix (Fin n) (Fin n) (MvPowerSeries σ O) :=
      Matrix.of fun i j : Fin n => MvPowerSeries.pderiv (R := O) (e j) (f i)
    refine Matrix.eq_zero_of_mulVec_eq_zero
      (M := (φ₀ : MvPowerSeries σ O →+* C).mapMatrix A) ?_ ?_
    · rw [← RingHom.map_det, hdet, map_mul, map_natCast]
      exact mul_ne_zero (Nat.cast_ne_zero.2 hN) (U.isUnit.map _).ne_zero
    · funext i
      have h1 := hE0 (f i)
      have hi : f i ∈ I := Ideal.subset_span ⟨i, rfl⟩
      rw [hE, hψI _ hi, hψI' _ hi, sub_self, zero_sub, neg_eq_zero] at h1
      simpa [Matrix.mulVec, dotProduct, A] using h1
  refine AlgHom.ext fun q => ?_
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine TrivSqZeroExt.ext (hfst _) ?_
  have h1 := hE0 g
  rw [hE, hd] at h1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero] at h1
  exact (sub_eq_zero.1 h1).symm

end GlobalTheory.NoTangent
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_universal_thickening_of_finite_points : ∀ (k : Type) [Field k] (K : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType K.hom], (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite (Over.mk t ⟶ K)) → ∀ e : Chart.sp (R₀ := k) k ⟶ K, ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (aug : A →ₐ[k] k) (M : ℕ) (io : Chart.sp (R₀ := k) A ⟶ K), RingHom.ker aug ^ (M + 1) = ⊥ ∧ Chart.spMap aug ≫ io = e ∧ ∀ (Q : Type) [CommRing Q] [Algebra k Q] (augQ : Q →ₐ[k] k) (j : ℕ), RingHom.ker augQ ^ (j + 1) = ⊥ → ∀ z : Chart.sp (R₀ := k) Q ⟶ K, Chart.spMap augQ ≫ z = e → ∃ a : A →ₐ[k] Q, augQ.comp a = aug ∧ z = Chart.spMap a ≫ io := by
  first | exact @GlobalTheory.IsolPt.exists_universal_thickening | exact GlobalTheory.IsolPt.exists_universal_thickening | (intros; apply GlobalTheory.IsolPt.exists_universal_thickening <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ChartInv

variable {k : Type} [CommRing k] {d : ℕ}

theorem formalComp_apply_eq_mvPowerSeries_subst (φ ψ : Pt k 1 d) (i : Fin d) :
    comp1 φ ψ i = (φ i).subst (fun p : Fin 1 × Fin d => ψ p.2) := by
  unfold comp1 ev
  congr 1
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases a
  rfl

theorem linearPart_eq_submatrix (φ : Pt k 1 d) :
    GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2) =
      (dLin φ).submatrix (Equiv.uniqueProd (Fin d) (Fin 1)) (Equiv.uniqueProd (Fin d) (Fin 1)) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  obtain rfl : b = 0 := Subsingleton.elim _ _
  rfl

theorem exists_isInvPair :
    ∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) →
      IsUnit (dLin φ).det → ∃ φi : Pt k 1 d, IsInvPair φ φi := by
  intro k _ d φ h0 hdet
  have hu : ∀ p : Fin 1 × Fin d, constantCoeff ((fun p : Fin 1 × Fin d => φ p.2) p) = 0 :=
    fun p => h0 p.2
  have hA : IsUnit (GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2)) := by
    rw [Matrix.isUnit_iff_isUnit_det, linearPart_eq_submatrix, Matrix.det_submatrix_equiv_self]
    exact hdet
  obtain ⟨v, hv, h1, h2⟩ := (GlobalTheory.FormalInv.exists_substInv_iff hu).2 hA
  have hvv : (fun p : Fin 1 × Fin d => v (0, p.2)) = v := by
    funext ⟨a, j⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  refine ⟨fun i => v (0, i), h0, fun i => hv _, ?_, ?_⟩
  · funext i
    rw [formalComp_apply_eq_mvPowerSeries_subst, hvv]
    exact h1 (0, i)
  · funext i
    rw [formalComp_apply_eq_mvPowerSeries_subst]
    exact h2 (0, i)

end GlobalTheory.ChartInv
end
