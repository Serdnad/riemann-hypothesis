module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BfSubRight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UbasisAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantFamilyNorms

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma Bf_single (Z : X.Coord) (τ : X.Ψ) (j k : Fin r) :
    Bf X Z τ (Pi.single j 1) (Pi.single k 1) = Gp X Z τ j k := by
  unfold Bf
  simp [Pi.single_apply]

lemma Bf_split (Z : X.Coord) (τ : X.Ψ) (v t : Fin r → ℂ) (h1 : Bf X Z τ v t = 0) :
    Bf X Z τ v v = Bf X Z τ (v - t) (v - t) - Bf X Z τ t t := by
  have h2 : Bf X Z τ t v = 0 := by rw [Bf_conj, h1, map_zero]
  simp only [Bf_sub_left, Bf_sub_right]
  rw [h1, h2]
  ring

lemma blk_Gp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (c : Fin r) : (blk (Gp X Z τ) c).det ≠ 0 := by
  rw [← gram_xZ X ho Z τ]
  exact blk_det X (xZ_mem_dom X hx ho hZ) τ c

lemma dOf_eq {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (τ : X.Ψ) (k : Fin r) :
    dOf X (X.xZ x Z) τ k = Bf X Z τ (fun a => uMat (Gp X Z τ) a k) (fun a => uMat (Gp X Z τ) a k) := by
  have hG : gram τ.1 X.Gm (mat (X.xZ x Z) τ) = Gp X Z τ := gram_xZ X ho Z τ
  unfold dOf uOf
  rw [hG]
  set M := mat (X.xZ x Z) τ with hM
  set U := uMat (Gp X Z τ) with hU
  have hcol : col (M * U) k = ∑ a, U a k • col M a := by
    funext i
    simp [col, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  show hermC τ.1 X.Gm (col (M * U) k) (col (M * U) k) = _
  rw [hcol, hermC_quad]
  unfold Bf
  rw [← hG]
  rfl

lemma pivot_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (k : Fin r) (hk : (k : ℕ) < X.p0) :
    1 - X.zN Z ^ 2 ≤ (dOf X (X.xZ x Z) τ k).re ∧ (dOf X (X.xZ x Z) τ k).re ≤ 1 := by
  have hdet := blk_Gp X hx ho hZ τ
  have hz0 : 0 ≤ X.zN Z := Real.iSup_nonneg fun τ => opN_nonneg _
  have hz1 : 0 ≤ 1 - X.zN Z ^ 2 := by nlinarith
  rw [dOf_eq X ho Z τ k]
  set v : Fin r → ℂ := fun a => uMat (Gp X Z τ) a k with hv
  have hvk : v k = 1 := by simp [hv, uMat]
  have hvgt : ∀ b, k < b → v b = 0 := by
    intro b hb
    simp [hv, uMat, hb.ne', not_lt.mpr hb.le]
  set t : Fin r → ℂ := fun b => if b < k then v b else 0 with ht
  have ht0 : ∀ b, k ≤ b → t b = 0 := fun b hb => by simp [ht, not_lt.mpr hb]
  have hvt : Bf X Z τ v t = 0 := Bf_gv_zero X Z τ hdet k t ht0
  have hsplit := Bf_split X Z τ v t hvt
  have hsingle : v - t = Pi.single k 1 := by
    funext b
    rcases lt_trichotomy b k with hb | hb | hb
    · simp [ht, hb, hb.ne]
    · rw [hb]
      simp [ht, hvk]
    · simp [ht, not_lt.mpr hb.le, hvgt b hb, hb.ne']
  rw [hsingle, Bf_single] at hsplit
  have hvn : ∀ m, v (nI X m) = 0 := fun m => hvgt _ (by
    rw [Fin.lt_def]
    simp [nI]
    omega)
  have hlow := Bf_pos_ge X Z τ v hvn
  have hkk : Fin.castLE X.p0_le (⟨k, hk⟩ : Fin X.p0) = k := Fin.ext rfl
  have hnsq : 1 ≤ nsq (Pv X v) := by
    unfold nsq Pv
    have := Finset.single_le_sum (f := fun j : Fin X.p0 => ‖v (Fin.castLE X.p0_le j)‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ (⟨k, hk⟩ : Fin X.p0))
    simp only [hkk, hvk, norm_one, one_pow] at this
    exact this
  have htn : ∀ m, t (nI X m) = 0 := fun m => ht0 _ (by
    rw [Fin.le_def]
    simp [nI]
    omega)
  have htpos := Bf_pos_ge X Z τ t htn
  have hnsqt : 0 ≤ nsq (Pv X t) := Finset.sum_nonneg fun j _ => by positivity
  have hGkk : (Gp X Z τ k k).re ≤ 1 := by
    rw [← hkk, Gp_pp]
    simp only [if_true, Complex.sub_re, Complex.one_re, Complex.re_sum]
    have : 0 ≤ ∑ m, (Z τ m ⟨k, hk⟩ * conj (Z τ m ⟨k, hk⟩)).re :=
      Finset.sum_nonneg fun m _ => by
        rw [Complex.mul_conj]
        simp [Complex.normSq_nonneg]
    linarith
  constructor
  · nlinarith
  · rw [hsplit, Complex.sub_re]
    nlinarith

lemma pivot_neg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (m0 : Fin (r - X.p0)) : (dOf X (X.xZ x Z) τ (nI X m0)).re ≤ -1 := by
  have hdet := blk_Gp X hx ho hZ τ
  have hz0 : 0 ≤ X.zN Z := Real.iSup_nonneg fun τ => opN_nonneg _
  have hz1 : 0 ≤ 1 - X.zN Z ^ 2 := by nlinarith
  rw [dOf_eq X ho Z τ (nI X m0)]
  set k := nI X m0 with hkdef
  set v : Fin r → ℂ := fun a => uMat (Gp X Z τ) a k with hv
  have hvk : v k = 1 := by simp [hv, uMat]
  set t : Fin r → ℂ := fun b => if (b : ℕ) < X.p0 then v b else 0 with ht
  have ht0 : ∀ b, k ≤ b → t b = 0 := fun b hb => by
    have hb' : ¬ ((b : ℕ) < X.p0) := by
      rw [Fin.le_def] at hb
      simp [hkdef, nI] at hb
      omega
    simp [ht, hb']
  have hvt : Bf X Z τ v t = 0 := Bf_gv_zero X Z τ hdet k t ht0
  have hsplit := Bf_split X Z τ v t hvt
  have htn : ∀ m, t (nI X m) = 0 := fun m => by simp [ht, nI]
  have htpos := Bf_pos_ge X Z τ t htn
  have hnsqt : 0 ≤ nsq (Pv X t) := Finset.sum_nonneg fun j _ => by positivity
  have hre := Bf_self_re X Z τ (v - t)
  have hP0 : Pv X (v - t) = 0 := by
    funext a
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := by simp [Fin.coe_castLE]
    simp [Pv, ht, ha]
  have hNm : Nv X Z τ (v - t) m0 = 1 := by
    have h1 : ∀ c : Fin X.p0, (v - t) (Fin.castLE X.p0_le c) = 0 := fun c => congrFun hP0 c
    simp only [Nv, h1, mul_zero, Finset.sum_const_zero, add_zero]
    rw [Pi.sub_apply, ← hkdef, hvk, ht0 k le_rfl, sub_zero]
  have hN : 1 ≤ nsq (Nv X Z τ (v - t)) := by
    unfold nsq
    have := Finset.single_le_sum (f := fun j => ‖Nv X Z τ (v - t) j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ m0)
    simp only [hNm, norm_one, one_pow] at this
    exact this
  have hn0 : nsq (0 : Fin X.p0 → ℂ) = 0 := by simp [nsq]
  rw [hsplit, Complex.sub_re, hre, hP0, hn0]
  nlinarith

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem maj_xZ {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 10)
    {Z : X.Coord} (hZ : X.zN Z ≤ ρ) (τ : X.Ψ) (v : Fin r → ℂ) :
    (1 - ρ) / (1 + ρ) * X.maj x τ v ≤ X.maj (X.xZ x Z) τ v ∧
      X.maj (X.xZ x Z) τ v ≤ (1 + ρ) / (1 - ρ) * X.maj x τ v := by
  have hy : X.xZ x Z ∈ X.dom := xZ_mem_dom X hx ho (by linarith)
  exact mj_bounds X hx ho hρ0 hρ hZ hy τ v

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def Jt (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ :=
  I • ((2 : ℂ) • X.ppos x τ v - v)

def UBasis (z0 : Frame X.Ψ r) (ξ : Fin r → E) (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) : Prop :=
  ∀ τ : X.Ψ,
    (∀ k, hermC τ.1 X.Gm (f τ k) (emb τ.1 ξ) = 0 ∧ hermC τ.1 X.Gm (X.Jt z0 τ (f τ k)) (emb τ.1 ξ) = 0) ∧
    (∀ k, X.Jt z0 τ (f τ k) = (if (k : ℕ) < X.p0 - 1 then I else -I) • f τ k) ∧
    (∀ k l, hermC τ.1 X.Gm (f τ k) (f τ l) =
      if k = l then (if (k : ℕ) < X.p0 - 1 then 1 else -1) else 0) ∧
    (∀ c : Fin (r - 2) → ℂ, X.maj z0 τ (∑ k, c k • f τ k) = ∑ k, ‖c k‖ ^ 2) ∧
    (∀ v : Fin r → ℂ, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 → hermC τ.1 X.Gm (X.Jt z0 τ v) (emb τ.1 ξ) = 0 →
      v ∈ Submodule.span ℂ (Set.range (f τ)))

end Data

theorem exists_unitary_basis_same_flag (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 x0 : Frame X.Ψ r) (hξ : X.IsIso ξ)
    (hz : z0 ∈ X.dom) (hx0 : x0 ∈ X.dom) (hortho : X.IsOrtho x0) (hflag : X.SameFlag z0 x0) :
    ∃ f : X.Ψ → Fin (r - 2) → Fin r → ℂ, X.UBasis z0 ξ f := by

  choose f hf using fun τ : X.Ψ =>
    OrthonormalPerpBasis.ubasis_at (X := X.toData) ξ z0 x0 hξ.2.2 hξ.2.1 hz hx0 hortho hflag τ
  exact ⟨f, fun τ => hf τ⟩

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma herm_swap_eq_zero_of_eq_zero (X : Data E r) (x y : Fin r → E) (h : herm X.Gm x y = 0) :
    herm X.Gm y x = 0 := by
  have e : cc (herm X.Gm x y) = herm X.Gm y x := by

    simp only [herm, cc, map_sum, map_mul, NumberField.IsCMField.complexConj_apply_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    first
      | (have hg := X.Gm_herm b a
         simp only [cc] at hg
         rw [hg]
         ring)
      | (have hg := X.Gm_herm a b
         simp only [cc] at hg
         rw [hg]
         ring)
  rw [← e, h]
  simp [cc]

private lemma herm_smul_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G (c • x) z = c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma herm_smul_right_eq_cc_mul (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G x (c • z) = cc c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul]
  ring

theorem isIsoPair_of (X : DataX E r) {ξ x : Fin r → E} (hξ : X.IsIso ξ) (hxξ : herm X.Gm x ξ = 0)
    (hxx : herm X.Gm x x = 0) (hne : ∀ e : E, x ≠ e • ξ) :
    IsIsoPair X.Gm ![ξ, (X.NC : E) • x] := by
  obtain ⟨-, hξξ, hξ0⟩ := hξ
  have hξx : herm X.Gm ξ x = 0 := herm_swap_eq_zero_of_eq_zero X.toData x ξ hxξ
  unfold IsIsoPair
  refine ⟨?_, LinearIndependent.pair_iff.mpr fun s t hst => ?_⟩
  · intro i k
    fin_cases i <;> fin_cases k <;>
      simp [herm_smul_left_fundamental_domains, herm_smul_right_eq_cc_mul, hξξ, hxξ, hxx, hξx]
  · by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hξ0, rfl⟩
    · exfalso
      have hNC : (X.NC : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NC_pos.ne'
      have htn : t * (X.NC : E) ≠ 0 := mul_ne_zero ht hNC
      have h1 : (t * (X.NC : E)) • x = -(s • ξ) := by
        rw [mul_smul]
        exact eq_neg_of_add_eq_zero_right hst
      apply hne (-(s / (t * X.NC)))
      calc x = (t * X.NC)⁻¹ • ((t * X.NC) • x) := by rw [smul_smul, inv_mul_cancel₀ htn, one_smul]
        _ = -(s / (t * X.NC)) • ξ := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem mem_pair (X : DataX E r) {ξ x : Fin r → E} (hξ : X.IsIso ξ) (hx : x ∈ X.L') :
    ∀ i, (![ξ, (X.NC : E) • x] : Fin 2 → Fin r → E) i ∈ X.Λ := by
  obtain ⟨hξΛ, -, -⟩ := hξ
  intro i
  fin_cases i
  · exact hξΛ
  · exact X.NC_sub x hx

theorem xp_facts (X : Data E r) {ξ x : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0)
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom)
    (τ : X.Ψ) :
    hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0 ∧
      hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (X.ucomp z0 ξ (X.embV x) τ) = 0 ∧
      X.Hf z0 τ (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0 := by
  set α := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hα
  have hxp : X.ucomp z0 ξ (X.embV x) τ = Data.emb τ.1 x - α • Data.emb τ.1 ξ := rfl
  have h1 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb, hxξ, map_zero]
  have h2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb, hξξ, map_zero]
  have h3 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 x) = 0 := by
    rw [hermC_emb, hxx, map_zero]
  have h4 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 x) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm, h1, map_zero]
  have hne : X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [X.Hf_self hz0 τ]
    exact_mod_cast (X.maj_pos hz0 τ (emb_ne_zero τ.1 hξ0)).ne'
  rw [hxp]
  refine ⟨?_, ?_, ?_⟩
  · rw [hermC_sub_left, hermC_smul_left, h1, h2, mul_zero, sub_zero]
  · simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right, h1, h2, h3, h4]
    simp
  · rw [Hf_sub_left, Hf_smul_left, hα, div_mul_cancel₀ _ hne, sub_self]

theorem e_facts (X : Data E r) {ξ x : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0)
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom)
    (e : X.Ψ → Fin r → ℂ) (hxp0 : ∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0)
    (he : ∀ τ, e τ = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) •
      X.ucomp z0 ξ (X.embV x) τ) :
    X.IsIsoV e ∧ (∀ τ, hermC τ.1 X.Gm (e τ) (Data.emb τ.1 ξ) = 0) ∧
      (∀ τ, X.Hf z0 τ (e τ) (Data.emb τ.1 ξ) = 0) ∧ (∀ τ, X.c τ * X.maj z0 τ (e τ) = 1) := by
  have key : ∀ τ, ∃ k : ℝ, 0 < k ∧ e τ = (k : ℂ) • X.ucomp z0 ξ (X.embV x) τ ∧
      k ^ 2 * (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) = 1 := by
    intro τ
    have hm : 0 < X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) :=
      mul_pos (MajorantFamilyNorms.c_pos X τ) (X.maj_pos hz0 τ (hxp0 τ))
    refine ⟨(Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹,
      inv_pos.mpr (Real.sqrt_pos.mpr hm), ?_, ?_⟩
    · simp only [he τ, Complex.ofReal_inv]
    · rw [inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']
  refine ⟨fun τ => ?_, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩
  · obtain ⟨k, hk, hek, -⟩ := key τ
    have hf := xp_facts X hξξ hξ0 hxξ hxx hz0 τ
    refine ⟨?_, ?_⟩
    · rw [hek, hermC_smul_left, hermC_smul_right, hf.2.1, mul_zero, mul_zero]
    · rw [hek]
      exact smul_ne_zero (Complex.ofReal_ne_zero.mpr hk.ne') (hxp0 τ)
  · obtain ⟨k, -, hek, -⟩ := key τ
    rw [hek, hermC_smul_left, (xp_facts X hξξ hξ0 hxξ hxx hz0 τ).1, mul_zero]
  · obtain ⟨k, -, hek, -⟩ := key τ
    rw [hek, Hf_smul_left, (xp_facts X hξξ hξ0 hxξ hxx hz0 τ).2.2, mul_zero]
  · obtain ⟨k, -, hek, hk2⟩ := key τ
    rw [hek, maj_smul X hz0, ← hk2]
    ring

theorem flow_facts (X : Data E r) {ξ : Fin r → E} {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.FramesOverBasis ξ)
    (e : X.Ψ → Fin r → ℂ) (hiso : X.IsIsoV e)
    (heξ : ∀ τ, hermC τ.1 X.Gm (e τ) (Data.emb τ.1 ξ) = 0)
    (hHe : ∀ τ, X.Hf z0 τ (e τ) (Data.emb τ.1 ξ) = 0) (hce : ∀ τ, X.c τ * X.maj z0 τ (e τ) = 1)
    {z : Frame X.Ψ r} (hz : z ∈ X.dom) (hf : X.SameFlag z0 z) :
    (∀ τ, X.ttV e z τ = 1) ∧ X.flowV e (fun _ => -(I / 2)) z ∈ X.FramesOverBasis ξ := by
  have httv : ∀ τ, X.ttV e z τ = 1 := by
    intro τ
    rw [Data.ttV, maj_flag X hz0.1 hz hf, hce τ, div_one]
  have hTz : X.flowV e (fun _ => -(I / 2)) z ∈ X.dom := by
    refine (flowDomainCriterion_holds r X e hiso z hz (fun _ => -(I / 2))).1.mpr fun τ => ?_
    rw [httv τ]
    norm_num
  refine ⟨httv, hTz, fun τ => ?_⟩
  have hve : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (e τ) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm, heξ τ, map_zero]
  have hpe : hermC τ.1 X.Gm (X.ppos z τ (Data.emb τ.1 ξ)) (e τ) = 0 :=
    hpe_of X hz τ (Data.emb τ.1 ξ) (e τ) (by rw [Hf_flag X hz0.1 hz hf]; exact hHe τ) (heξ τ)
  rw [maj_flowV X e _ hz hTz τ _ hve hpe, maj_flag X hz0.1 hz hf, hz0.2 τ]

end ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
end
