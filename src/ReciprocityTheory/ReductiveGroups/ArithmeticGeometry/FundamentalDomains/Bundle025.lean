module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContinuousRl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientMatrices
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientLattice

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace MajorantConjugateTransfer

variable {r : ℕ} (X : Data E r)

theorem maj_transfer {x y : Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) (τ : X.Ψ)
    (g g' : Matrix (Fin r) (Fin r) ℂ) (hgg' : ∀ w, Matrix.mulVec g (Matrix.mulVec g' w) = w)
    (hiso : ∀ u v, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g v) = hermC τ.1 X.Gm u v)
    (H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec g (X.colP x τ c) = ∑ a, K a • X.colP y τ a)
    (H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP y τ a = ∑ c, L c • Matrix.mulVec g (X.colP x τ c))
    (w : Fin r → ℂ) : X.maj y τ w = X.maj x τ (Matrix.mulVec g' w) := by
  have pp : ∀ (x' : Frame X.Ψ r) (v : Fin r → ℂ),
      X.posPart x' τ v = (hermC τ.1 X.Gm (X.ppos x' τ v) v).re := by
    intro x' v
    rw [X.hermC_ppos_self]
    rfl
  set u := Matrix.mulVec g' w with hu
  set p := Matrix.mulVec g (X.ppos x τ u) with hp
  set z := Matrix.mulVec g u with hz
  have hA : ∀ d : Fin r → ℂ, (∀ c', hermC τ.1 X.Gm d (X.colP y τ c') = 0) →
      ∀ c, hermC τ.1 X.Gm d (Matrix.mulVec g (X.colP x τ c)) = 0 := by
    intro d hd c
    obtain ⟨K, hK⟩ := H1 c
    rw [hK, hermC_sum_right]
    exact Finset.sum_eq_zero fun a _ => by rw [hermC_smul_right, hd, mul_zero]
  have hB : ∀ b, hermC τ.1 X.Gm z (X.colP y τ b) = hermC τ.1 X.Gm p (X.colP y τ b) := by
    intro b
    rw [← sub_eq_zero, ← hermC_sub_left]
    obtain ⟨L, hL⟩ := H2 b
    rw [hL, hermC_sum_right]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hermC_smul_right, hz, hp, ← Matrix.mulVec_sub, hiso, hermC_sub_left,
      X.hermC_ppos_colP hx, sub_self, mul_zero]
  have h1 : X.ppos y τ z = X.ppos y τ p := by
    rw [X.ppos_eq, X.ppos_eq]
    simp only [hB]
  have h2 : ∀ c', hermC τ.1 X.Gm (X.ppos y τ p - p) (X.colP y τ c') = 0 := by
    intro c'
    rw [hermC_sub_left, X.hermC_ppos_colP hy, sub_self]
  have h3 : ∀ d, (∀ c', hermC τ.1 X.Gm d (X.colP y τ c') = 0) → hermC τ.1 X.Gm d p = 0 := by
    intro d hd
    rw [hp, X.ppos_eq x τ u, Matrix.mulVec_sum, hermC_sum_right]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Matrix.mulVec_smul, hermC_smul_right, hA d hd a, mul_zero]
  have key : hermC τ.1 X.Gm (X.ppos y τ z) z = hermC τ.1 X.Gm (X.ppos x τ u) u := by
    have e := h3 _ h2
    rw [hermC_sub_left, sub_eq_zero] at e
    rw [X.hermC_ppos_left hy τ z z, h1, ← X.hermC_ppos_left hy τ p p, e, hp, hiso,
      ← X.hermC_ppos_left hx τ u u]
  have hwz : w = z := (hgg' w).symm
  rw [hwz]
  simp only [Data.maj]
  rw [pp, pp, key, hz, hiso]

theorem maj_zero (x : Frame X.Ψ r) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  simp [Data.maj, Data.posPart, hermC_zero_left]

theorem maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, maj_zero X x τ]
  · exact (X.maj_pos hx τ hv).le

theorem Hf_sub_left (x : Frame X.Ψ r) (τ : X.Ψ) (u u' w : Fin r → ℂ) :
    X.Hf x τ (u - u') w = X.Hf x τ u w - X.Hf x τ u' w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.ppos_sub, hermC_sub_left,
    hermC_sub_left]
  ring

theorem Hf_smul_left (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (k • u) w = k * X.Hf x τ u w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.ppos_smul_eq, hermC_smul_left, hermC_smul_left]
  ring

theorem Hf_sub_right (x : Frame X.Ψ r) (τ : X.Ψ) (u w w' : Fin r → ℂ) :
    X.Hf x τ u (w - w') = X.Hf x τ u w - X.Hf x τ u w' := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hermC_sub_right, hermC_sub_right]
  ring

theorem Hf_smul_right (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ u (k • w) = conj k * X.Hf x τ u w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hermC_smul_right, hermC_smul_right]
  ring

theorem Hf_conj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf x τ u w) = X.Hf x τ w u := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, map_sub, map_mul, map_ofNat, hermC_conj _ X.Gm_herm,
    hermC_conj _ X.Gm_herm, X.ppos_selfadj hx τ w u]

theorem cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    ‖X.Hf x τ u v‖ ^ 2 ≤ X.maj x τ u * X.maj x τ v := by
  by_cases hv : v = 0
  · have h0 : X.Hf x τ u 0 = 0 := by
      have := Hf_sub_right X x τ u 0 0
      simpa using this
    rw [hv, h0, maj_zero X x τ]
    simp
  have hm : 0 < X.maj x τ v := X.maj_pos hx τ hv
  have hmu := maj_nonneg X hx τ u

  set H := X.Hf x τ u v with hH
  have hw := X.Hf_self hx τ ((X.maj x τ v : ℂ) • u - H • v)
  have hn := maj_nonneg X hx τ ((X.maj x τ v : ℂ) • u - H • v)
  simp only [Hf_sub_left, Hf_sub_right, Hf_smul_left, Hf_smul_right] at hw
  rw [X.Hf_self hx τ u, X.Hf_self hx τ v, ← Hf_conj X hx τ u v, ← hH, Complex.conj_ofReal] at hw
  have hHH : H * conj H = (Complex.normSq H : ℂ) := Complex.mul_conj H
  have e : ((X.maj x τ ((X.maj x τ v : ℂ) • u - H • v) : ℝ) : ℂ) =
      ((X.maj x τ v * (X.maj x τ v * X.maj x τ u - Complex.normSq H) : ℝ) : ℂ) := by
    rw [← hw]
    push_cast
    linear_combination (-(X.maj x τ v : ℂ)) * hHH
  have e' := Complex.ofReal_injective e
  rw [e'] at hn
  have hle : Complex.normSq H ≤ X.maj x τ v * X.maj x τ u := by
    by_contra hc
    push_neg at hc
    have : X.maj x τ v * (X.maj x τ v * X.maj x τ u - Complex.normSq H) < 0 :=
      mul_neg_of_pos_of_neg hm (by linarith)
    linarith
  rw [Complex.sq_norm]
  linarith [mul_comm (X.maj x τ u) (X.maj x τ v)]

end MajorantConjugateTransfer

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices MeasureTheory Set Filter
open scoped ComplexConjugate

noncomputable section

section Gen

variable {ι : Type} [Fintype ι] {N : ℕ} (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ)

def Bv (t : Fin N → ℝ) : ι → Fin 2 → Fin 2 → ℂ := ∑ j, (t j : ℂ) • ω j

lemma Bv_add (t s : Fin N → ℝ) : Bv ω (t + s) = Bv ω t + Bv ω s := by
  simp only [Bv, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

lemma Bv_zero : Bv ω 0 = 0 := by
  simp [Bv]

lemma Bv_herm (hωh : ∀ j, IsHermFam (ω j)) (t : Fin N → ℝ) : IsHermFam (Bv ω t) := by
  intro τ i k

  simp only [Bv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hωh j τ i k]

lemma Bv_cont : Continuous (Bv ω) := continuous_finsetSum _ (fun j _ => (Complex.continuous_ofReal.comp (continuous_apply j)).smul continuous_const)

lemma pair_Bv (χ : ι → Fin 2 → Fin 2 → ℂ) (t : Fin N → ℝ) :
    pr χ (Bv ω t) = ∑ j, t j * pr χ (ω j) := by
  have hadd : ∀ b b' : ι → Fin 2 → Fin 2 → ℂ, pr χ (b + b') = pr χ b + pr χ b' := by
    intro b b'
    simp only [pr, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]
  have hsm : ∀ (c : ℝ) (b : ι → Fin 2 → Fin 2 → ℂ), pr χ ((c : ℂ) • b) = c * pr χ b := by
    intro c b
    simp only [pr, Pi.smul_apply, smul_eq_mul]
    rw [← Complex.re_ofReal_mul]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun k _ => by ring)))
  let P : (ι → Fin 2 → Fin 2 → ℂ) →+ ℝ := AddMonoidHom.mk' (pr χ) hadd
  have h1 : pr χ (Bv ω t) = P (Bv ω t) := rfl

  rw [h1, Bv, map_sum]
  exact Finset.sum_congr rfl (fun j _ => hsm _ _)

def ech (χ : ι → Fin 2 → Fin 2 → ℂ) (t : Fin N → ℝ) : ℂ :=
  cexp (-(4 * Real.pi * I) * (pr χ (Bv ω t) : ℂ))

lemma ech_cont (χ : ι → Fin 2 → Fin 2 → ℂ) : Continuous (ech ω χ) := by
  have h : ech ω χ = fun t => cexp (-(4 * Real.pi * I) * ((∑ j, t j * pr χ (ω j) : ℝ) : ℂ)) := by
    funext t
    simp only [ech, pair_Bv]
  rw [h]
  fun_prop

lemma ech_add (χ : ι → Fin 2 → Fin 2 → ℂ) (t s : Fin N → ℝ) :
    ech ω χ (t + s) = ech ω χ t * ech ω χ s := by
  simp only [ech, pair_Bv, Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.ofReal_add, mul_add,
    Complex.exp_add]

lemma ech_int (χ : ι → Fin 2 → Fin 2 → ℂ) {k : Fin N → ℤ} (hk : ∀ j, 2 * pr χ (ω j) = k j)
    (n : Fin N → ℤ) : ech ω χ (fun i => (n i : ℝ)) = 1 := by
  have hk' : ∀ j, pr χ (ω j) = (k j : ℝ) / 2 := fun j => by linarith [hk j]
  rw [ech, pair_Bv, Complex.exp_eq_one_iff]
  refine ⟨-∑ j, n j * k j, ?_⟩
  simp only [hk']
  push_cast
  rw [Finset.mul_sum, neg_mul (∑ x, ((n x : ℂ) * (k x : ℂ))), Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end Gen

def cube (N : ℕ) : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

lemma cube_compact (N : ℕ) : IsCompact (cube N) := isCompact_univ_pi (fun _ => isCompact_Icc)

lemma cube_meas (N : ℕ) : MeasurableSet (cube N) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma ubox_ae (N : ℕ) : (I2.DimB.ubox N) =ᵐ[volume] cube N := by
  have h1 : I2.DimB.ubox N = Set.pi Set.univ (fun i => Ioc ((0 : Fin N → ℝ) i) ((1 : Fin N → ℝ) i)) := by
    ext x
    simp [I2.DimB.ubox]
  have h2 : cube N = Set.Icc (0 : Fin N → ℝ) 1 := by
    rw [cube, ← Set.pi_univ_Icc]
    rfl
  rw [h1, h2]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

section Mean

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E) (g : ℕ) (ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ)
  (G : Frame X.Ψ r → ℂ)

def Ich (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∫ t in cube (4 * Fintype.card X.Ψ), G (X.Zb u (Bv ω t) x) * ech ω χ t

variable {X u g ω G}
variable (hω : X.IsLZBasis g ω)
  (hadd : ∀ b b' x, X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x)
  (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)

include hω in
lemma herm_ω (j : Fin (4 * Fintype.card X.Ψ)) : IsHermFam (ω j) := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.herm_of_LZ X g (hω.1 j)

include hω in
lemma Bv_LZ (n : Fin (4 * Fintype.card X.Ψ) → ℤ) : Bv ω (fun i => (n i : ℝ)) ∈ X.LZ g := by
  exact ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.LZ_sum X g hω.1 n

include hω hdomH in
lemma Zb_dom (t : Fin (4 * Fintype.card X.Ψ) → ℝ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.Zb u (Bv ω t) x ∈ X.dom := hdomH _ (Bv_herm ω (fun j => herm_ω hω j) t) x hx

include hω hdomH in
lemma psi_cont (hG : DifferentiableOn ℂ G X.dom) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Continuous fun t => G (X.Zb u (Bv ω t) x) := by
  have hB : Continuous (Bv ω) := Bv_cont ω
  have hc : Continuous fun t => X.Zb u (Bv ω t) x := by
    unfold Data.Zb Data.zmat
    fun_prop
  exact hG.continuousOn.comp_continuous hc (fun t => Zb_dom hω hdomH t hx)

include hω hadd hdomH in
lemma psi_per (hper : ∀ b ∈ X.LZ g, ∀ x ∈ X.dom, G (X.Zb u b x) = G x) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (n : Fin (4 * Fintype.card X.Ψ) → ℤ) (t : Fin (4 * Fintype.card X.Ψ) → ℝ) :
    G (X.Zb u (Bv ω (t + fun i => (n i : ℝ))) x) = G (X.Zb u (Bv ω t) x) := by
  have hx' := Zb_dom hω hdomH t hx
  rw [Bv_add, add_comm, ← hadd]
  exact hper _ (Bv_LZ hω n) _ hx'

include hω hdomH in
lemma Ich_diff (hG : DifferentiableOn ℂ G X.dom) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) :
    DifferentiableOn ℂ (Ich X u ω G χ) X.dom := by
  have := FourierCoefficientDomain.diffOn_param (cube_compact _) (cube_meas _)
    (fun t => FourierCoefficientDomain.ZbL X u (Bv ω t)) (FourierCoefficientDomain.cont_ZbL X u (Bv_cont ω))
    (FourierCoefficientDomain.isOpen_dom X) (fun t _ x hx => Zb_dom hω hdomH t hx) G hG (ech ω χ) (ech_cont ω χ)
  exact this

lemma Ich_rmul (la : Wt X.Ψ r) (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = bchar la b * G x)
    (hω : X.IsLZBasis g ω) (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : Ich X u ω G χ (rmul x b) = bchar la b * Ich X u ω G χ x := by
  have hcomm : ∀ t, X.Zb u (Bv ω t) (rmul x b) = rmul (X.Zb u (Bv ω t) x) b := by
    intro t
    funext τ
    show X.zmat u (Bv ω t) τ * mat (rmul x b) τ = mat (X.Zb u (Bv ω t) x) τ * mat b τ
    change X.zmat u (Bv ω t) τ * (mat x τ * mat b τ) = _
    rw [mat_Zb, Matrix.mul_assoc]
  unfold Ich
  simp_rw [hcomm]
  have h2 : ∀ t, G (rmul (X.Zb u (Bv ω t) x) b) * ech ω χ t = bchar la b * (G (X.Zb u (Bv ω t) x) * ech ω χ t) := by
    intro t
    rw [hB _ (Zb_dom hω hdomH t hx) b hb, mul_assoc]
  simp_rw [h2]
  exact integral_const_mul _ _

end Mean

end

end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
end
