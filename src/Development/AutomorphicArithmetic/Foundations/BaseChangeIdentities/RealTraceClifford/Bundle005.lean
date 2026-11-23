module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle001
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle002
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle002
public import Formalism.RealPlaceAnalysis.Bundle002
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {J : Type} [Fintype J] [DecidableEq J]

private theorem mt_ap (M : Matrix J J ℂ) (x : Ten J V) (j : J) :
    (UpperTheory.RealTr.mt V M x).ofLp j = ∑ k, M j k • x.ofLp k := rfl

private theorem lf_ap (T : Module.End ℂ V) (x : Ten J V) (j : J) :
    (lf J T x).ofLp j = T (x.ofLp j) := rfl

private theorem mt_mul (M N : Matrix J J ℂ) : UpperTheory.RealTr.mt V (M * N) = UpperTheory.RealTr.mt V M * UpperTheory.RealTr.mt V N := by
  refine LinearMap.ext fun x => PiLp.ext fun j => ?_
  simp only [Module.End.mul_apply, mt_ap, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

private theorem mt_one : UpperTheory.RealTr.mt V (1 : Matrix J J ℂ) = 1 := by
  ext x j
  simp [mt_ap, Matrix.one_apply]

private theorem mt_add (M N : Matrix J J ℂ) : UpperTheory.RealTr.mt V (M + N) = UpperTheory.RealTr.mt V M + UpperTheory.RealTr.mt V N := by
  ext x j
  simp [mt_ap, add_smul, Finset.sum_add_distrib]

private theorem mt_smul (r : ℂ) (M : Matrix J J ℂ) : UpperTheory.RealTr.mt V (r • M) = r • UpperTheory.RealTr.mt V M := by
  ext x j
  simp [mt_ap, smul_smul, Finset.smul_sum]

private theorem lf_mt (M : Matrix J J ℂ) (T : Module.End ℂ V) :
    lf J T * UpperTheory.RealTr.mt V M = UpperTheory.RealTr.mt V M * lf J T := by
  ext x j

  simp [mt_ap, lf_ap, map_sum]

private theorem mt_adj (M : Matrix J J ℂ) (x y : Ten J V) :
    ⟪UpperTheory.RealTr.mt V M x, y⟫_ℂ = ⟪x, UpperTheory.RealTr.mt V Mᴴ y⟫_ℂ := by
  simp only [PiLp.inner_apply, mt_ap, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.conjTranspose_apply, Complex.star_def]
  exact Finset.sum_comm

private theorem lf_adj (T T' : Module.End ℂ V) (h : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T' y⟫_ℂ) (x y : Ten J V) :
    ⟪lf J T x, y⟫_ℂ = ⟪x, lf J T' y⟫_ℂ := by
  simp only [PiLp.inner_apply, lf_ap, h]

private theorem spn_adj {n : ℕ} (c : Fin n → Fin n → Matrix J J ℂ) (hc : ∀ a b, (c a b)ᴴ = c b a) (a b : Fin n) :
    (spn c a b)ᴴ = spn c b a := by
  simp only [spn, Matrix.conjTranspose_sub, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, hc,
    Algebra.algebraMap_eq_smul_one]
  congr 1
  split_ifs with h1 h2 h2
  · simp [Matrix.conjTranspose_smul, Complex.star_def]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

private theorem real_trace_matrix_sub {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {J : Type} [Fintype J]
    (M N : Matrix J J ℂ) : UpperTheory.RealTr.mt V (M - N) = UpperTheory.RealTr.mt V M - UpperTheory.RealTr.mt V N := by
  refine LinearMap.ext fun x => PiLp.ext fun j => ?_
  simp [mt_ap, sub_smul, Finset.sum_sub_distrib]

private theorem real_trace_matrix_zero {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {J : Type} [Fintype J] :
    UpperTheory.RealTr.mt V (0 : Matrix J J ℂ) = 0 := by
  refine LinearMap.ext fun x => PiLp.ext fun j => ?_
  simp [mt_ap]

private theorem gl_dg {n : ℕ} (K : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix J J ℂ)
    (hK : GlRel K) (hs : GlRel (spn c)) : GlRel (dg K c) := by
  intro a b e d
  have h1 : lf J (K a b) * lf J (K e d) - lf J (K e d) * lf J (K a b) =
      lf J ((if b = e then K a d else 0) - if d = a then K e b else 0) := by
    rw [← hK a b e d, map_sub, map_mul, map_mul]
  have h2 : UpperTheory.RealTr.mt V (spn c a b) * UpperTheory.RealTr.mt V (spn c e d) -
      UpperTheory.RealTr.mt V (spn c e d) * UpperTheory.RealTr.mt V (spn c a b) =
      UpperTheory.RealTr.mt V ((if b = e then spn c a d else 0) - if d = a then spn c e b else 0) := by
    rw [← hs a b e d, real_trace_matrix_sub, mt_mul, mt_mul]
  have h3 := lf_mt (V := V) (spn c e d) (K a b)
  have h4 := lf_mt (V := V) (spn c a b) (K e d)
  have key : dg K c a b * dg K c e d - dg K c e d * dg K c a b =
      lf J ((if b = e then K a d else 0) - if d = a then K e b else 0) +
      UpperTheory.RealTr.mt V ((if b = e then spn c a d else 0) - if d = a then spn c e b else 0) := by
    rw [← h1, ← h2]
    simp only [dg, add_mul, mul_add]
    rw [h3, h4]
    abel
  rw [key]
  split_ifs <;> simp only [dg, map_sub, map_zero, real_trace_matrix_sub, real_trace_matrix_zero, sub_zero] <;> abel
end

theorem UpperTheory.RealTr.tenF :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (J : Type) [Fintype J] [DecidableEq J],
      (∃ φ : Matrix J J ℂ →ₐ[ℂ] Module.End ℂ (Ten J V), ∀ M, φ M = mt V M) ∧ (∀ M (T : Module.End ℂ V), lf J T * mt V M = mt V M * lf J T) ∧
      (∀ M (x y : Ten J V), ⟪mt V M x, y⟫_ℂ = ⟪x, mt V Mᴴ y⟫_ℂ) ∧
      (∀ T T' : Module.End ℂ V, (∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T' y⟫_ℂ) → ∀ x y : Ten J V, ⟪lf J T x, y⟫_ℂ = ⟪x, lf J T' y⟫_ℂ) ∧
      ∀ (K : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), UF K → ClifMod c η → UF (dg K c) := by
  intro n V _ _ J _ _
  refine ⟨⟨AlgHom.ofLinearMap ⟨⟨UpperTheory.RealTr.mt V, fun M N => mt_add M N⟩, fun r M => mt_smul r M⟩
      mt_one (fun M N => mt_mul M N), fun M => rfl⟩,
    fun M T => lf_mt M T, fun M x y => mt_adj M x y, fun T T' h x y => lf_adj T T' h x y, ?_⟩
  intro K c η hK hc
  refine ⟨gl_dg K c hK.gl (spnRel n _ c hc.rel).1, ?_⟩
  intro a b x y
  simp only [dg, LinearMap.add_apply, inner_add_left, inner_add_right]
  rw [lf_adj _ _ (hK.unit a b), mt_adj, spn_adj c hc.adj]
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem trOn_bot' {V : Type} [AddCommGroup V] [Module ℂ V] (L : V →ₗ[ℂ] V) :
    trOn (⊥ : Submodule ℂ V) L = 0 := by
  unfold trOn
  split_ifs with h
  · have : Subsingleton (⊥ : Submodule ℂ V) := inferInstance
    have h0 : L.restrict h = 0 := Subsingleton.elim _ _
    rw [h0, map_zero]
  · rfl

private theorem cf_sum {n : ℕ} (s : Finset (Wt n)) (g : Wt n → ℂ) (μ : Wt n) :
    cf (∑ x ∈ s, g x • ex x) μ = if μ ∈ s then g μ else 0 := by
  classical
  simp [cf, ex, AddMonoidAlgebra.coeff, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem UpperTheory.RealTr.chEx :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ B, ∃ c, IsCh F S B c := by
  intro n V _ _ F hF S hS hSt B
  obtain ⟨s, hs, -, -⟩ := wtDec n V F hF S hS hSt
  refine ⟨∑ μ ∈ s, trOn (wsp F μ ⊓ S) B • ex μ, fun μ => ?_⟩
  rw [cf_sum]
  split_ifs with h
  · rfl
  · rw [hs μ h, trOn_bot']
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem ex_prod' {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Wt n) :
    ∏ a ∈ s, ex (f a) = ex (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [(cfBasic n).2.1]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, (cfBasic n).1]

private theorem ex_pow' {n : ℕ} (x : Wt n) (k : ℕ) : ex x ^ k = ex (k • x) := by
  induction k with
  | zero => simp [(cfBasic n).2.1]
  | succ k ih => rw [pow_succ, ih, ← (cfBasic n).1, succ_nsmul]

private theorem sg_smul' {n : ℕ} (w : Equiv.Perm (Fin n)) (f : FR n) :
    sg w • f = (((Equiv.Perm.sign w : ℤ) : FR n)) * f := by
  rw [sg, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

theorem UpperTheory.RealTr.denom :
    ∀ (n : ℕ) (t : ℝ), alt (t • rhoV n) = ex (t • rhoV n) * ∏ p ∈ posP n, (1 - ex (-(t • rt p.1 p.2))) := by
  intro n t
  classical
  set Y : Fin n → FR n := fun a => ex (-(t • (Pi.single a (1 : ℝ) : Wt n))) with hY
  set c : Wt n := fun _ => t * (((n : ℝ) - 1) / 2) with hc
  have hA : alt (t • rhoV n) = ex c * (Matrix.vandermonde Y).transpose.det := by
    rw [Matrix.det_apply, Finset.mul_sum, alt]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hprod : ex c * ∏ i, (Matrix.vandermonde Y).transpose (w i) i = ex ((t • rhoV n) ∘ ⇑w) := by
      simp only [Matrix.transpose_apply, Matrix.vandermonde_apply, hY, ex_pow', ex_prod',
        ← (cfBasic n).1]
      congr 1
      funext b
      simp [Finset.sum_apply, Pi.single_apply, rhoV]
      ring
    rw [mul_smul_comm, hprod, sg_smul', Units.smul_def, zsmul_eq_mul]
  have h1 : ∀ a b : Fin n, 1 - ex (-(t • rt a b)) = ex (t • (Pi.single b (1 : ℝ) : Wt n)) * (Y b - Y a) := by
    intro a b
    rw [mul_sub, hY]
    simp only
    rw [← (cfBasic n).1, ← (cfBasic n).1, add_neg_cancel, (cfBasic n).2.1]
    congr 2
    rw [rt, smul_sub]
    abel
  have h2 : ∏ p ∈ posP n, (1 - ex (-(t • rt p.1 p.2))) =
      ∏ i, ∏ j ∈ Finset.Ioi i, (1 - ex (-(t • rt i j))) := by
    unfold posP
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  have h3 : ex (t • rhoV n) * ∏ i, ∏ j ∈ Finset.Ioi i, ex (t • (Pi.single j (1 : ℝ) : Wt n)) = ex c := by
    simp only [ex_prod', ← (cfBasic n).1]
    congr 1
    funext k
    simp [Finset.sum_apply, Pi.single_apply, rhoV]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
      Fin.card_Iio, nsmul_eq_mul, hc]
    ring
  rw [h2, hA, Matrix.det_transpose, Matrix.det_vandermonde, ← h3]
  simp_rw [h1, Finset.prod_mul_distrib]
  ring
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem dot_rt {n : ℕ} (x : Wt n) (a b : Fin n) : ∑ c, x c * rt a b c = x a - x b := by
  simp [rt, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

private theorem dot_add {n : ℕ} (x u v : Wt n) :
    ∑ c, x c * (u + v) c = ∑ c, x c * u c + ∑ c, x c * v c := by
  simp [mul_add, Finset.sum_add_distrib]

private theorem wt_shift {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hg : GlRel F) {μ : Wt n} {y : V}
    (hy : IsWeight F μ y) (a b : Fin n) : IsWeight F (μ + rt a b) (F a b y) := by
  intro c
  have h := LinearMap.congr_fun (hg c c a b) y
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hy c, map_smul, sub_eq_iff_eq_add] at h
  rw [h]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb
    simp [rt]
  · subst hca
    simp [rt, Pi.single_apply, hcb, Ne.symm hcb, add_smul]
    abel
  · subst hcb
    simp [rt, Pi.single_apply, hca, Ne.symm hca, add_smul, sub_smul]
    abel
  · simp [rt, Pi.single_apply, hca, hcb, Ne.symm hcb]

private theorem wt_word {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hg : GlRel F) {μ : Wt n} {x : V}
    (hx : IsWeight F μ x) (w : List (Fin n × Fin n)) :
    IsWeight F (μ + (w.map fun p => rt p.1 p.2).sum) (Formalism.REAL.ew F w x) := by
  induction w with
  | nil => simpa [Formalism.REAL.ew] using hx
  | cons p w ih =>
    have h := wt_shift hg ih p.1 p.2
    rw [Formalism.REAL.ew.eq_2]
    simp only [List.map_cons, List.sum_cons, Module.End.mul_apply]
    rwa [show ∀ u v : Wt n, μ + (u + v) = (μ + v) + u from fun u v => by abel]

private theorem maj_word {n : ℕ} (ν x : Wt n) (hx : Antitone x) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, p.2 < p.1) :
    ∑ a, x a * (ν + (w.map fun p => rt p.1 p.2).sum) a ≤ ∑ a, x a * ν a := by
  induction w with
  | nil => simp
  | cons p w ih =>
    have hp := hw p (by simp)
    have ih' := ih (fun q hq => hw q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons]
    rw [show ∀ u v : Wt n, ν + (u + v) = (ν + v) + u from fun u v => by abel, dot_add, dot_rt]
    have := hx hp.le
    linarith

private theorem rhoC_true (n : ℕ) : Formalism.REAL.rhoC (fun _ : Fin n => true) = rhoV n := by
  funext a
  simp only [Formalism.REAL.rhoC, rhoV]
  simp only [and_true, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  have ha := a.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

private theorem nsq_eq {n : ℕ} (u : Fin n → ℝ) : Formalism.REAL.nsq u = nsq u := by
  simp [Formalism.REAL.nsq, Formalism.REAL.dot, nsq, sq]

private theorem rhoV_anti (n : ℕ) : Antitone (rhoV n) := by
  intro a b hab
  have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [rhoV]
  linarith

theorem UpperTheory.RealTr.isoFacts :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ ν : Wt n, (∀ μ, μ ≠ ν → hw F μ ⊓ S = ⊥) →
      (∀ x ∈ S, Cas F x = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • x) ∧ (∀ μ, wsp F μ ⊓ S ≠ ⊥ → Maj μ ν) ∧ wsp F ν ⊓ S = hw F ν ⊓ S := by
  intro n V _ _ F hF S hS hst ν hν
  have hK : Formalism.REAL.KRel (fun _ : Fin n => true) F := Formalism.REAL.glRel_kRel _ F hF.gl
  have hU : Formalism.REAL.KUnit (fun _ : Fin n => true) F := fun a b _ x y => hF.unit a b x y
  have hSt : Formalism.REAL.KStable (fun _ : Fin n => true) F S := fun a b _ x hx => hst a b x hx
  obtain ⟨m, x, μ, hx, horth, hsup⟩ := Formalism.REAL.kDecomp V n (fun _ => true) F S hS hK hU hSt
  have hμ : ∀ i, μ i = ν := by
    intro i
    by_contra h
    have h0 := hν (μ i) h
    have hi : x i ∈ hw F (μ i) ⊓ S := Submodule.mem_inf.mpr ⟨(hx i).2.2, (hx i).1⟩
    rw [h0] at hi
    exact (hx i).2.1 ((Submodule.mem_bot ℂ).mp hi)
  have hC : ∀ y ∈ S, Cas F y = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • y := by
    have hCas : Formalism.REAL.CasK (fun _ : Fin n => true) F = Cas F := by
      simp [Formalism.REAL.CasK, Formalism.REAL.Cas]
    have hck : Formalism.REAL.ckv (fun _ : Fin n => true) ν = nsq (ν + rhoV n) - nsq (rhoV n) := by
      simp only [Formalism.REAL.ckv, rhoC_true, nsq_eq]
    intro y hy
    rw [← hsup] at hy
    refine Submodule.iSup_induction _ (motive := fun y => Cas F y = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • y) hy ?_ ?_ ?_
    · intro i z hz
      have hz' := Formalism.REAL.kCasSpan V n _ F (μ i) (x i) hK (hx i).2.2 z hz
      rw [hCas, hμ i, hck] at hz'
      exact hz'
    · simp
    · intro a b ha hb
      rw [map_add (f := _), ha, hb, smul_add]
  have hM : ∀ μ', wsp F μ' ⊓ S ≠ ⊥ → Maj μ' ν := by
    intro μ' hne
    by_contra hnot
    apply hne
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
    rw [Submodule.mem_bot]
    have hle : S ≤ LinearMap.ker (innerₛₗ ℂ y) := by
      rw [← hsup]
      apply iSup_le
      intro i
      rw [(Formalism.REAL.kLow V n _ F (μ i) (x i) hK (hx i).2.2).1, Formalism.REAL.lowSpan, Submodule.span_le]
      rintro z ⟨w, hwl, rfl⟩
      have hwt := wt_word hF.gl (hx i).2.2.1 w
      rw [hμ i] at hwt
      have hne' : μ' ≠ ν + (w.map fun p => rt p.1 p.2).sum := by
        rintro rfl
        exact hnot (fun t ht => maj_word ν t ht w (fun p hp => (hwl p hp).2))
      simp only [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply]
      exact Formalism.REAL.kWtOrth V n _ F μ' _ y _ hU hyw hwt hne'
    have h0 := hle hyS
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero] at h0
    exact h0
  refine ⟨hC, hM, ?_⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
    have hk : KHighest (fun _ : Fin n => true) F ν y := by
      refine ⟨hyw, ?_⟩
      intro a b hab _
      by_contra hne
      have hmem : F a b y ∈ wsp F (ν + rt a b) ⊓ S :=
        Submodule.mem_inf.mpr ⟨wt_shift hF.gl hyw a b, hst a b y hyS⟩
      have hM' := hM (ν + rt a b) (by
        intro h
        rw [h] at hmem
        exact hne ((Submodule.mem_bot ℂ).mp hmem))
      have h1 := hM' (rhoV n) (rhoV_anti n)
      rw [dot_add, dot_rt] at h1
      have hlt : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
      have h2 : rhoV n b < rhoV n a := by
        simp only [rhoV]
        linarith
      linarith
    exact Submodule.mem_inf.mpr ⟨hk, hyS⟩
  · intro y hy
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hy
    exact Submodule.mem_inf.mpr ⟨(show KHighest (fun _ : Fin n => true) F ν y from h1).1, h2⟩
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.gelf2 :
    ∀ (n : ℕ) (χ : Fin n → ℂ), GlobalTheory.Dec.gelfVal χ 2 = ∑ a, χ a ^ 2 - (nsq (rhoV n) : ℂ) := by
  intro n χ
  have hr : Formalism.QuantumDeterminants.rhoStd n = rhoV n := rfl
  rw [GlobalTheory.CasimirEigen.gelfVal_two_eq, hr, nsq]
  push_cast
  simp only [sq]
end
end
