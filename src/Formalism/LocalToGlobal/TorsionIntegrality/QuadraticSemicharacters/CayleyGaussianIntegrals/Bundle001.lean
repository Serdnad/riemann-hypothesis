module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyIdentity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

namespace Cay

section Det

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem gram_det_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (H : Sesq V) (hpos : IsPosDef H)
    (e : Module.Basis ι ℂ V) : (Matrix.of fun i j => H (e i) (e j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hHw : H (∑ i, v i • e i) = 0 := by
    apply e.ext
    intro j
    have h := congrFun hM j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at h

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.zero_apply]
    exact h
  have hw0 : (∑ i, v i • e i) ≠ 0 := by
    intro h0
    exact hv (funext fun i => Fintype.linearIndependent_iff.1 e.linearIndependent v h0 i)
  have h := hpos _ hw0
  rw [hHw, LinearMap.zero_apply, Complex.zero_re] at h
  exact lt_irrefl _ h

theorem det_adj (H : Sesq V) (hpos : IsPosDef H) (f f' : V →ₗ[ℂ] V) (h : ∀ x y, H (f x) y = H x (f' y)) :
    LinearMap.det f = conj (LinearMap.det f') := by
  classical
  let e := Module.finBasis ℂ V
  have hG := gram_det_ne_zero H hpos e
  have hfe : ∀ (g : V →ₗ[ℂ] V) j, g (e j) = ∑ k, LinearMap.toMatrix e e g k j • e k := fun g j => by
    simp only [LinearMap.toMatrix_apply]; exact (e.sum_repr (g (e j))).symm
  have hmat : (LinearMap.toMatrix e e f).transpose * (Matrix.of fun i j => H (e i) (e j))
      = (Matrix.of fun i j => H (e i) (e j)) * (LinearMap.toMatrix e e f').map (starRingEnd ℂ) := by
    ext i j
    have h1 := h (e i) (e j)
    rw [hfe f i, hfe f' j] at h1

    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul] at h1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply]
    exact h1.trans (Finset.sum_congr rfl fun k _ => mul_comm _ _)
  have hc : ((LinearMap.toMatrix e e f').map (starRingEnd ℂ)).det
      = starRingEnd ℂ (LinearMap.toMatrix e e f').det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc] at hdet
  rw [← LinearMap.det_toMatrix e f, ← LinearMap.det_toMatrix e f']
  exact mul_right_cancel₀ hG (hdet.trans (mul_comm _ _))

end Det

end Cay

theorem cayleyDet : DetCayley := by
  intro V _ _ _ H hH hpos δ Ae hI hA
  have hi : ∀ a b, H (δ a) (δ b) = H a b := fun a b => hI a b
  have hadj : ∀ x y, H ((Ae : V →ₗ[ℂ] V) x) y = H x (((LinearMap.id : V →ₗ[ℂ] V) - (δ : V →ₗ[ℂ] V)) y) := by
    intro x y
    obtain ⟨x, rfl⟩ : ∃ x', x = δ x' := ⟨δ.symm x, by simp⟩
    simp only [LinearEquiv.coe_coe, hA, LinearEquiv.symm_apply_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_sub, hi]
  have h1 := Cay.det_adj H hpos _ _ hadj
  have h2 : ((LinearMap.id : V →ₗ[ℂ] V) - (δ : V →ₗ[ℂ] V)) = ((-1 : ℂ) • (δ : V →ₗ[ℂ] V)) ∘ₗ (Ae : V →ₗ[ℂ] V) := by
    ext x
    simp [hA]
  conv_lhs => rw [h1, Complex.conj_conj, h2, LinearMap.det_comp, LinearMap.det_smul]

namespace Cay

theorem selfDual_img {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V)
    (δ : V ≃ₗ[ℂ] V) (hδ : IsIsom H H (δ : V →ₗ[ℂ] V)) (hΛ : IsSelfDual H Λ) :
    IsSelfDual H (imgLat (δ : V →ₗ[ℂ] V) Λ) := by
  have hi : ∀ a b, H (δ a) (δ b) = H a b := fun a b => hδ a b
  unfold IsSelfDual at hΛ ⊢
  ext x
  constructor
  · intro hx
    have hx' : ∀ y ∈ imgLat (δ : V →ₗ[ℂ] V) Λ, ∃ m : ℤ, altE H x y = m := hx
    rw [imgLat, AddSubgroup.mem_map]
    refine ⟨δ.symm x, ?_, by simp⟩
    rw [← hΛ]
    show ∀ y ∈ Λ, ∃ m : ℤ, altE H (δ.symm x) y = m
    intro y hy
    obtain ⟨m, hm⟩ := hx' (δ y) (by rw [imgLat, AddSubgroup.mem_map]; exact ⟨y, hy, rfl⟩)
    refine ⟨m, ?_⟩
    have e := hi (δ.symm x) y
    rw [LinearEquiv.apply_symm_apply] at e
    show (H (δ.symm x) y).im = m
    rw [← e]; exact hm
  · intro hx
    rw [imgLat, AddSubgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← hΛ] at ha
    have ha' : ∀ y ∈ Λ, ∃ m : ℤ, altE H a y = m := ha
    show ∀ y ∈ imgLat (δ : V →ₗ[ℂ] V) Λ, ∃ m : ℤ, altE H (δ a) y = m
    intro y hy
    rw [imgLat, AddSubgroup.mem_map] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨m, hm⟩ := ha' b hb
    refine ⟨m, ?_⟩
    show (H (δ a) (δ b)).im = m
    rw [hi]; exact hm

end Cay

theorem UnitaryEighth_of (hC : UnitaryConstant) (hG : UnitaryGauss) (hI : UnitaryIndex) : UnitaryEighth := by
  intro V _ _ _ H Λ α δ Ae hL hU hAML θ hθ hθ0 c hc
  have hd : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0 := (LinearEquiv.isUnit_det' Ae).ne_zero
  obtain ⟨_, hidx⟩ := hI V H Λ α δ Ae hL hU
  have hne : relIdx (latA Λ δ Ae) Λ ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hidx
    have h1 : (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) ≠ 0 := by exact_mod_cast hU.idx₁
    exact mul_ne_zero h1 (pow_ne_zero _ (norm_ne_zero_iff.2 hd)) hidx.symm
  obtain ⟨S, hS⟩ := (cosetRepsExist V (latA Λ δ Ae) Λ hne).1
  have hc' := hC V H Λ α δ Ae hL hU hAML S hS θ hθ
  have hg := hG V H Λ α δ Ae hU S hS
  have hI0 : inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at hc
    apply hθ0
    funext z
    have h1 := congrFun hc (δ z)
    simpa [pullInv] using h1
  have hceq : c = (‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V)
      * gaussC H α Ae S := smul_left_injective ℂ hI0 (hc.symm.trans hc')
  have hdc := cayleyDet V H hU.herm hU.pos δ Ae hU.isom hU.cay
  rw [hceq, mul_pow, hg, mul_one, div_pow]
  generalize LinearMap.det (Ae : V →ₗ[ℂ] V) = d at *
  generalize LinearMap.det (δ : V →ₗ[ℂ] V) = D at *
  have hn2 : ((‖d‖ : ℝ) : ℂ) ^ 2 = d * conj d := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hs : ((-1 : ℂ) ^ Module.finrank ℂ V) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [show ((‖d‖ : ℝ) : ℂ) ^ 8 = (((‖d‖ : ℝ) : ℂ) ^ 2) ^ 4 by ring, hn2, hdc, div_eq_iff (pow_ne_zero _ hd)]
  linear_combination (D ^ 4 * d ^ 8) * hs

end Formalism.L2.Th1.H
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open MeasureTheory Module

namespace Formalism.L2.Th1.H

private theorem exists_real_basis_span_int_eq_of_isLat {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (Λ : AddSubgroup V) (hΛ : IsLat Λ) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ V),
      (Submodule.span ℤ (Set.range b)).toAddSubgroup = Λ := by
  obtain ⟨hdisc, hspan⟩ := hΛ
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  refine ⟨_, inferInstance, (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L, ?_⟩
  rw [Module.Basis.ofZLatticeBasis_span]
  rfl

theorem fundamentalDomainExists : FundDomain := by
  intro V _ _ _ _ _ μ _ Λ hΛ
  obtain ⟨ι, _, b, hb⟩ := exists_real_basis_span_int_eq_of_isLat Λ hΛ
  subst hb
  set L := (Submodule.span ℤ (Set.range b)).toAddSubgroup with hL
  set D := ZSpan.fundamentalDomain b with hDdef
  have hFD : IsAddFundamentalDomain L D μ := ZSpan.isAddFundamentalDomain b μ
  have hbdd : Bornology.IsBounded D := ZSpan.fundamentalDomain_isBounded b
  have hmeas : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet b
  have hne : μ D ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero b
  have htop : μ D ≠ ⊤ := hbdd.measure_lt_top.ne
  refine ⟨D, hFD, hbdd, ENNReal.toReal_pos hne htop, ?_⟩
  intro Λ' hle hidx
  have hmem : ∀ v : V, v ∈ L → ∀ x : V, (v + x ∈ D ↔ v = -(ZSpan.floor b x : V)) := by
    intro v hv x
    have := ZSpan.vadd_mem_fundamentalDomain b ⟨v, hv⟩ x
    rw [Subtype.ext_iff, Submodule.coe_neg] at this
    exact this
  have hfl : ∀ x : V, (ZSpan.floor b x : V) ∈ L := fun x => (ZSpan.floor b x).2
  set H := Λ'.addSubgroupOf L with hH
  have hcardQ : Nat.card (L ⧸ H) = relIdx Λ' L := rfl
  haveI : Finite (L ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact hidx)
  letI : Fintype (L ⧸ H) := Fintype.ofFinite _
  let rep : L ⧸ H → V := fun q => ((Quotient.out q : L) : V)
  have hrepL : ∀ q, rep q ∈ L := fun q => (Quotient.out q).2
  have hrep : ∀ q : L ⧸ H, ((Quotient.out q : L) : L ⧸ H) = q := fun q => QuotientAddGroup.out_eq' q
  have hdisj : Pairwise (Function.onFun Disjoint fun q : L ⧸ H => rep q +ᵥ D) := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    intro y hyp hyq
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hyp hyq
    have e1 := (hmem _ (L.neg_mem (hrepL p)) y).mp hyp
    have e2 := (hmem _ (L.neg_mem (hrepL q)) y).mp hyq
    apply hpq
    have hpq' : rep p = rep q := by
      rw [← neg_neg (rep p), e1, ← e2, neg_neg]
    rw [← hrep p, ← hrep q]
    congr 1
    exact Subtype.ext hpq'
  refine ⟨⋃ q : L ⧸ H, rep q +ᵥ D, ?_, ?_, ?_⟩
  · refine IsAddFundamentalDomain.mk' (MeasurableSet.iUnion fun q => hmeas.const_vadd _).nullMeasurableSet ?_
    intro x
    set l0 : V := -(ZSpan.floor b x : V) with hl0def
    have hl0 : l0 ∈ L := L.neg_mem (hfl x)
    set q0 : L ⧸ H := ((⟨-l0, L.neg_mem hl0⟩ : L) : L ⧸ H) with hq0def
    have hq0 : rep q0 + l0 ∈ Λ' := by
      have h1 := hrep q0
      rw [hq0def, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
      have h2 : -(-(rep q0) + -l0) ∈ Λ' := Λ'.neg_mem (by simpa [rep] using h1)
      rwa [neg_add_rev, neg_neg, neg_neg, add_comm] at h2
    refine ⟨⟨rep q0 + l0, hq0⟩, ?_, ?_⟩
    · show rep q0 + l0 + x ∈ ⋃ q : L ⧸ H, rep q +ᵥ D
      refine Set.mem_iUnion.mpr ⟨q0, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        show -rep q0 + (rep q0 + l0 + x) = l0 + x by abel]
      exact (hmem l0 hl0 x).mpr rfl
    · intro g hg
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hg
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hq
      have hgx : -rep q + (g : V) + x ∈ D := by
        rw [add_assoc]
        exact hq
      have hv : -rep q + (g : V) ∈ L := L.add_mem (L.neg_mem (hrepL q)) (hle g.2)
      have e1 : -rep q + (g : V) = l0 := (hmem _ hv x).mp hgx
      have hqq : q = q0 := by
        rw [← hrep q, hq0def, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        have h3 : -rep q + -l0 = -(g : V) := by
          rw [← e1]
          abel
        have h4 : -(g : V) ∈ Λ' := Λ'.neg_mem g.2
        simpa [rep, h3] using h4
      apply Subtype.ext
      show (g : V) = rep q0 + l0
      rw [← hqq, ← e1]
      abel
  · exact Bornology.isBounded_iUnion.mpr fun q => hbdd.vadd (rep q)
  · have hμ : μ (⋃ q : L ⧸ H, rep q +ᵥ D) = (Fintype.card (L ⧸ H) : ENNReal) * μ D := by
      rw [measure_iUnion hdisj (fun q => hmeas.const_vadd _), tsum_fintype]
      simp [measure_vadd]
    rw [hμ, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← hcardQ, Nat.card_eq_fintype_card]

theorem characterIntegral : CharIntegral := by
  intro V _ _ _ _ _ μ _ H _ hH Λ' D' hD v hv hv0
  set f : V → ℂ := fun z => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H v z : ℂ)) with hf
  have hadd : ∀ x y : V, altE H v (x + y) = altE H v x + altE H v y := by
    intro x y
    simp [altE, map_add (f := _)]
  have hmul : ∀ x y : V, f (x + y) = f x * f y := by
    intro x y
    simp only [hf, hadd]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hper : ∀ (g : Λ') (z : V), f (g +ᵥ z) = f z := by
    intro g z
    obtain ⟨m, hm⟩ := hv g g.2
    show f ((g : V) + z) = f z
    rw [hmul]
    have : f (g : V) = 1 := by
      simp only [hf, hm]
      have := Complex.exp_int_mul_two_pi_mul_I m
      rw [← this]
      congr 1
      push_cast
      ring
    rw [this, one_mul]
  by_cases hμ : μ D' = 0
  · exact setIntegral_measure_zero _ hμ
  haveI : Countable Λ' := by
    have hc := Measure.countable_meas_pos_of_disjoint_iUnion₀ (μ := μ) (As := fun g : Λ' => g +ᵥ D')
      (fun g => hD.nullMeasurableSet_vadd g) hD.aedisjoint
    have huniv : {g : Λ' | 0 < μ (g +ᵥ D')} = Set.univ := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [measure_vadd]
      exact pos_iff_ne_zero.mpr hμ
    rw [huniv] at hc
    exact Set.countable_univ_iff.mp hc
  have htr : ∀ w : V, ∫ z in D', f z ∂μ = f w * ∫ z in D', f z ∂μ := by
    intro w
    have hD2 : IsAddFundamentalDomain Λ' (w +ᵥ D') μ := hD.vadd_of_comm w
    have e1 : ∫ z in w +ᵥ D', f z ∂μ = ∫ z in D', f z ∂μ := hD2.setIntegral_eq hD hper
    have e2 : ∫ z in w +ᵥ D', f z ∂μ = ∫ z in D', f (w + z) ∂μ := by
      rw [← Set.image_vadd]
      exact (measurePreserving_add_left μ w).setIntegral_image_emb (measurableEmbedding_addLeft w) f D'
    calc ∫ z in D', f z ∂μ = ∫ z in w +ᵥ D', f z ∂μ := e1.symm
      _ = ∫ z in D', f (w + z) ∂μ := e2
      _ = f w * ∫ z in D', f z ∂μ := by
        simp only [hmul]
        rw [integral_const_mul]
  have ha : 0 < (H v v).re := hH v hv0
  set c : ℂ := ((1 / (2 * (H v v).re) : ℝ) : ℂ) * Complex.I with hc
  have hw : altE H v (c • v) = -(1 / 2) := by
    simp only [altE, LinearMap.map_smulₛₗ, hc, smul_eq_mul, Complex.mul_im, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im]
    field_simp
    ring
  have hfw : f (c • v) = -1 := by
    simp only [hf, hw]
    push_cast
    have : 2 * (Real.pi : ℂ) * Complex.I * -(1 / 2) = -(Real.pi * Complex.I) := by ring
    rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have := htr (c • v)
  rw [hfw] at this
  linear_combination this / 2

end Formalism.L2.Th1.H
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.H

theorem gauss_plane (l : ℂ) (hl : 0 < l.re) :
    Integrable (fun z : ℂ => Complex.exp (-((Real.pi : ℂ) * l) * ((‖z‖ : ℝ) : ℂ) ^ 2)) ∧
      ∫ z : ℂ, Complex.exp (-((Real.pi : ℂ) * l) * ((‖z‖ : ℝ) : ℂ) ^ 2) = l⁻¹ := by
  have hl0 : l ≠ 0 := fun h => by simp [h] at hl
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hb : 0 < ((Real.pi : ℂ) * l).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos Real.pi_pos hl
  refine ⟨?_, ?_⟩
  · have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 (0 : ℂ)
    simpa using this
  · rw [GaussianFourier.integral_cexp_neg_mul_sq_norm (V := ℂ) hb, Complex.finrank_real_complex]
    rw [show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, Complex.cpow_one]
    field_simp

theorem gauss_pi {n : Type*} [Fintype n] (l : n → ℂ) (hl : ∀ i, 0 < (l i).re) :
    Integrable (fun w : n → ℂ => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2)) ∧
      ∫ w : n → ℂ, Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2) = (∏ i, l i)⁻¹ := by
  have hfun : (fun w : n → ℂ => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2)) =
      fun w => ∏ i, Complex.exp (-((Real.pi : ℂ) * l i) * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    rw [← Complex.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hfun]
  refine ⟨?_, ?_⟩
  · exact Integrable.fintype_prod
      (f := fun i (z : ℂ) => Complex.exp (-((Real.pi : ℂ) * l i) * ((‖z‖ : ℝ) : ℂ) ^ 2))
      (fun i => (gauss_plane (l i) (hl i)).1)
  · rw [integral_fintype_prod_volume_eq_prod
      (fun i (z : ℂ) => Complex.exp (-((Real.pi : ℂ) * l i) * ((‖z‖ : ℝ) : ℂ) ^ 2)),
      ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => (gauss_plane (l i) (hl i)).2

theorem haar_transfer {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {n : Type*} [Fintype n] (Φ : (n → ℂ) ≃ₗ[ℂ] V) :
    ∃ κ : ℝ, ∀ f : V → ℂ, (Integrable (fun w => f (Φ w)) → Integrable f μ) ∧
      ∫ z, f z ∂μ = (κ : ℂ) * ∫ w, f (Φ w) := by
  classical
  let Ψ : (n → ℂ) ≃L[ℂ] V := Φ.toContinuousLinearEquiv
  let ν : Measure V := Measure.map Ψ volume
  have hme : MeasurableEmbedding Ψ := Ψ.toHomeomorph.measurableEmbedding
  obtain ⟨c, hμ⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  subst hμ
  refine ⟨(c : ℝ), fun f => ⟨fun hf => ?_, ?_⟩⟩
  · apply Integrable.smul_measure_nnreal
    rw [hme.integrable_map_iff]
    exact hf
  · rw [integral_smul_nnreal_measure, hme.integral_map, NNReal.smul_def, Complex.real_smul]
    try rfl

theorem cayleyGaussianIntegral : GaussQuad := by
  intro V _ _ _ _ _ μ _ H hH hP δ Ae hδ hAe
  classical
  obtain ⟨b, l, hb, hbl, hl⟩ := unitary_diag H hH hP δ Ae hδ hAe
  obtain ⟨κ, hκ⟩ := haar_transfer μ b.equivFun.symm
  have hq : (fun w => gq H Ae (b.equivFun.symm w)) =
      fun w => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    have h1 := form_of_diag H b l (Ae : V →ₗ[ℂ] V) hb hbl w
    simp only [LinearEquiv.coe_coe] at h1
    unfold gq
    rw [h1]
  have hw : (fun w => ((wt H (b.equivFun.symm w) : ℝ) : ℂ)) =
      fun w => Complex.exp (-(Real.pi : ℂ) * ∑ i, (fun _ => (1 : ℂ)) i * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    have h1 := form_of_diag H b (fun _ => (1 : ℂ)) LinearMap.id hb (fun i => by simp) w
    simp only [LinearMap.id_apply] at h1
    have hs : (∑ i, (fun _ => (1 : ℂ)) i * ((‖w i‖ : ℝ) : ℂ) ^ 2) = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simp
    unfold wt
    rw [h1, hs, Complex.ofReal_re, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  have hgq := gauss_pi l hl
  have hgw := gauss_pi (n := Fin (Module.finrank ℂ V)) (fun _ => (1 : ℂ)) (fun _ => by simp)
  rw [← hq] at hgq
  rw [← hw] at hgw
  refine ⟨(hκ _).1 hgq.1, ?_⟩
  rw [(hκ (gq H Ae)).2, hgq.2, ← integral_complex_ofReal, (hκ (fun z => ((wt H z : ℝ) : ℂ))).2, hgw.2,
    det_of_diag b l (Ae : V →ₗ[ℂ] V) hbl]
  simp [div_eq_mul_inv]

end Formalism.L2.Th1.H
end
end
