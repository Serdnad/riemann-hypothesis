module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentOnHyperbolicComplement
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle019
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle017

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem Hf_sub_left (x : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf x τ (u - v) w = X.Hf x τ u w - X.Hf x τ v w := by
  simp only [Data.Hf_eq_jp, Data.jp_sub, hermC_sub_left]

theorem Hf_smul_left (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (k • u) w = k * X.Hf x τ u w := by
  simp only [Data.Hf_eq_jp, Data.jp_smul, hermC_smul_left]

theorem Hf_smul_right (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ u (k • w) = conj k * X.Hf x τ u w := by
  simp only [Data.Hf_eq_jp, hermC_smul_right]

theorem maj_smul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : ℝ) (v : Fin r → ℂ) :
    X.maj x τ ((k : ℂ) • v) = k ^ 2 * X.maj x τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hx τ, Hf_smul_left, Hf_smul_right, X.Hf_self hx τ, Complex.conj_ofReal]
  push_cast; ring

theorem ppos_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (v : Fin r → ℂ) : X.ppos z' τ v = X.ppos z τ v := by
  have hspan := hf τ
  have hmem : X.ppos z τ v ∈ Submodule.span ℂ
      (Set.range fun a : Fin X.p0 => col (mat z' τ) (Fin.castLE X.p0_le a)) := by
    rw [← hspan]
    unfold Data.ppos
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  rw [← hβ]
  apply X.ppos_eq_of z' τ (X.gramPos_det_ne hz' τ) v β
  intro b
  rw [hβ]
  have hb : col (mat z' τ) (Fin.castLE X.p0_le b) ∈ Submodule.span ℂ
      (Set.range fun a : Fin X.p0 => col (mat z τ) (Fin.castLE X.p0_le a)) := by
    rw [hspan]; exact Submodule.subset_span ⟨b, rfl⟩
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hb
  rw [← hγ, hermC_sum_right]
  exact Finset.sum_eq_zero fun a _ => by
    rw [hermC_smul_right, X.ppos_orth z τ (X.gramPos_det_ne hz τ) v a, mul_zero]

theorem Hf_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (u w : Fin r → ℂ) : X.Hf z' τ u w = X.Hf z τ u w := by
  simp only [Data.Hf, ppos_flag X hz hz' hf]

theorem maj_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj z' τ v = X.maj z τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hz' τ, ← X.Hf_self hz τ, Hf_flag X hz hz' hf]

theorem flowMatV_mulVec (e : Fin r → ℂ) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMatV e τ s) v = v + (-(I * X.c τ * s) * hermC τ.1 X.Gm v e) • e := by
  funext a
  simp only [Data.flowMatV, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hermC, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ppos_flowV (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) {z : Frame X.Ψ r} (hz : z ∈ X.dom)
    (hTz : X.flowV e s z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ)
    (hve : hermC τ.1 X.Gm v (e τ) = 0) (hpe : hermC τ.1 X.Gm (X.ppos z τ v) (e τ) = 0) :
    X.ppos (X.flowV e s z) τ v = X.ppos z τ v := by
  have hcol : ∀ a, col (mat (X.flowV e s z) τ) a =
      Matrix.mulVec (X.flowMatV (e τ) τ (s τ)) (col (mat z τ) a) :=
    fun a => Data.col_mul (X.flowMatV (e τ) τ (s τ)) (mat z τ) a
  have hT := flowMatV_mulVec X (e τ) τ (s τ)
  set β : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos z τ)⁻¹ b a with hβ
  have hp : X.ppos z τ v = ∑ a, β a • col (mat z τ) (Fin.castLE X.p0_le a) := rfl
  have hcoef : ∑ a, β a * (-(I * X.c τ * s τ) *
      hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a)) (e τ)) = 0 := by
    have : ∑ a, β a * (-(I * X.c τ * s τ) *
        hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a)) (e τ)) =
        -(I * X.c τ * s τ) * hermC τ.1 X.Gm (X.ppos z τ v) (e τ) := by
      rw [hp, hermC_sum_left, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hermC_smul_left]; ring
    rw [this, hpe, mul_zero]
  have hsum : ∑ a, β a • col (mat (X.flowV e s z) τ) (Fin.castLE X.p0_le a) = X.ppos z τ v := by
    simp only [hcol, hT, smul_add, Finset.sum_add_distrib, smul_smul]
    rw [← hp, ← Finset.sum_smul, hcoef, zero_smul, add_zero]
  rw [← hsum]
  apply X.ppos_eq_of _ τ (X.gramPos_det_ne hTz τ) v β
  intro b
  rw [hsum, hcol, hT, hermC_add_right, hermC_smul_right,
    X.ppos_orth z τ (X.gramPos_det_ne hz τ) v b, zero_add, hermC_sub_left, hve, hpe, sub_zero,
    mul_zero]

theorem maj_flowV (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) {z : Frame X.Ψ r} (hz : z ∈ X.dom)
    (hTz : X.flowV e s z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ)
    (hve : hermC τ.1 X.Gm v (e τ) = 0) (hpe : hermC τ.1 X.Gm (X.ppos z τ v) (e τ) = 0) :
    X.maj (X.flowV e s z) τ v = X.maj z τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hTz τ, ← X.Hf_self hz τ]
  simp only [Data.Hf, ppos_flowV X e s hz hTz τ v hve hpe]

theorem hpe_of {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v e : Fin r → ℂ)
    (hH : X.Hf z τ e v = 0) (hh : hermC τ.1 X.Gm e v = 0) :
    hermC τ.1 X.Gm (X.ppos z τ v) e = 0 := by
  have h1 : hermC τ.1 X.Gm (X.ppos z τ e) v = 0 := by
    rw [Data.Hf_eq_two_ppos, hh, sub_zero] at hH
    simpa using hH
  rw [X.ppos_selfadj hz, ← hermC_conj τ.1 X.Gm_herm, h1, map_zero]

end ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField InfinitePlace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem integerApproximationCount_holds : IntegerApproximationCount (E := E) := by
  intro r X
  refine ⟨fun w' => ?_, fun R hR => PackingSeparation.count R hR⟩
  classical
  have hconjmem : ∀ φ : E →+* ℂ, φ ∉ X.Ψ → ComplexEmbedding.conjugate φ ∈ X.Ψ := by
    intro φ h
    have := X.cmType (ComplexEmbedding.conjugate φ)
    rw [TraceIntegralBasis.conj_conj] at this
    exact this.mpr h
  let Z : TraceIntegralBasis.VS E := WithLp.toLp 2 (fun w : TraceIntegralBasis.CP E =>
    if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
    else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩))
  obtain ⟨α, hα⟩ := RingOfIntegersCovering.cover_OE Z
  refine ⟨α, fun τ => ?_⟩
  set w : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩ with hw
  have hcoord : ‖Z w - w.1.embedding (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
    have h := PiLp.norm_apply_le (Z - TraceIntegralBasis.iota E (α : E)) w
    rw [PiLp.sub_apply, TraceIntegralBasis.iota_apply] at h
    exact h.trans hα
  have hZw : Z w = if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
      else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩) := rfl
  have hmk : InfinitePlace.mk w.1.embedding = InfinitePlace.mk τ.1 := mk_embedding _
  rcases InfinitePlace.mk_eq_iff.mp hmk with h | h
  · have hmem : w.1.embedding ∈ X.Ψ := h ▸ τ.2
    have hZ : Z w = w' τ := by
      rw [hZw, dite_eq_left hmem]
      congr 1
      exact Subtype.ext h
    rw [hZ, h] at hcoord
    rwa [norm_sub_rev] at hcoord
  · have hnot : w.1.embedding ∉ X.Ψ := by
      intro hm
      exact ((X.cmType _).mp hm) (h ▸ τ.2)
    have hZ : Z w = conj (w' τ) := by
      rw [hZw, dite_eq_right hnot]
      congr 2
      exact Subtype.ext h
    have hemb : w.1.embedding (α : E) = conj (τ.1 (α : E)) := by
      rw [← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
    rw [hZ, hemb, ← map_sub, Complex.norm_conj] at hcoord
    rwa [norm_sub_rev] at hcoord

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma normSq_sub_le_two (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]

namespace Data

variable {r : ℕ} (X : Data E r)

lemma Jp_sub (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Jp x τ (u - v) = X.Jp x τ u - X.Jp x τ v := by
  unfold Jp
  rw [X.ppos_sub, smul_sub]
  abel

section perTau

variable {x : Frame X.Ψ r} {τ : X.Ψ}

lemma maj_smul (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ)) (c : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (c • v) = Complex.normSq c * X.maj x τ v := by
  have hJ : X.Jp x τ (c • v) = c • X.Jp x τ v := by
    unfold Jp; rw [X.ppos_smul, smul_comm (2 : ℂ) c, ← smul_sub]
  have hH : ∀ u w, hermC τ.1 X.Gm (c • u) (c • w) = (Complex.normSq c : ℂ) * hermC τ.1 X.Gm u w := by
    intro u w
    unfold hermC
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have h1 := hself (c • v)
  rw [show X.Hf x τ (c • v) (c • v) = hermC τ.1 X.Gm (X.Jp x τ (c • v)) (c • v) from rfl, hJ, hH,
    show hermC τ.1 X.Gm (X.Jp x τ v) v = X.Hf x τ v v from rfl, hself v] at h1
  exact_mod_cast h1.symm

lemma maj_zero' (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ)) : X.maj x τ 0 = 0 := by
  have h1 := X.maj_smul hself (0 : ℂ) 0
  simpa using h1

lemma maj_nonneg' (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
    (hpos : ∀ v, v ≠ 0 → 0 < X.maj x τ v) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, X.maj_zero' hself]
  · exact (hpos v hv).le

variable {e : Fin r → ℂ} (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ) (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0)
  (hq : X.d2q x τ e ≠ 0) (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
include hx he hq hself

lemma maj_Ce_bz (C b : ℂ) :
    X.maj x τ (C • e - b • X.d2z x τ e δ) =
      Complex.normSq C * X.maj x τ e + Complex.normSq b * X.maj x τ (X.d2z x τ e δ) := by
  have hfz : hermC τ.1 X.Gm (X.Jp x τ e) (X.d2z x τ e δ) = 0 := by
    rw [hsym, unipotent_shift_orthogonal_Je X δ hx he hq, map_zero]
  have hze : hermC τ.1 X.Gm (X.Jp x τ (X.d2z x τ e δ)) e = 0 := by
    rw [Jp_adj X hx, unipotent_shift_orthogonal_Je X δ hx he hq]
  have h3 : X.Hf x τ (C • e - b • X.d2z x τ e δ) (C • e - b • X.d2z x τ e δ) =
      C * conj C * X.Hf x τ e e + b * conj b * X.Hf x τ (X.d2z x τ e δ) (X.d2z x τ e δ) := by
    show hermC τ.1 X.Gm (X.Jp x τ (C • e - b • X.d2z x τ e δ)) (C • e - b • X.d2z x τ e δ) =
      C * conj C * hermC τ.1 X.Gm (X.Jp x τ e) e +
        b * conj b * hermC τ.1 X.Gm (X.Jp x τ (X.d2z x τ e δ)) (X.d2z x τ e δ)
    rw [Jp_sub, Jp_smul, Jp_smul]
    simp only [hC_sub_left, hC_smul_left, hC_sub_right, hC_smul_right, hfz, hze]
    ring
  rw [hself, hself, hself, Complex.mul_conj, Complex.mul_conj] at h3
  exact_mod_cast h3

lemma maj_decomp (w : Fin r → ℂ) (hw1 : hermC τ.1 X.Gm w e = 0)
    (hw2 : hermC τ.1 X.Gm w (X.Jp x τ e) = 0) (a b : ℂ) :
    X.maj x τ (w + a • e + b • X.Jp x τ e) =
      Complex.normSq a * X.maj x τ e + Complex.normSq b * X.maj x τ e + X.maj x τ w := by
  have k1 : hermC τ.1 X.Gm (X.Jp x τ w) e = 0 := by rw [Jp_adj X hx, hw2]
  have k2 : hermC τ.1 X.Gm (X.Jp x τ w) (X.Jp x τ e) = 0 := by
    rw [Jp_adj X hx, Jp_Jp X hx, hw1]
  have k3 : hermC τ.1 X.Gm (X.Jp x τ e) w = 0 := by rw [hsym, hw2, map_zero]
  have k4 : hermC τ.1 X.Gm e w = 0 := by rw [hsym, hw1, map_zero]
  have k5 := hermitian_pairing_Je_Je_zero X hx he
  have k6 : hermC τ.1 X.Gm (X.Jp x τ e) e = X.Hf x τ e e := rfl
  have k7 : hermC τ.1 X.Gm e (X.Jp x τ e) = X.Hf x τ e e := hermitian_pairing_e_Je X hx
  have h3 : X.Hf x τ (w + a • e + b • X.Jp x τ e) (w + a • e + b • X.Jp x τ e) =
      a * conj a * X.Hf x τ e e + b * conj b * X.Hf x τ e e + X.Hf x τ w w := by
    show hermC τ.1 X.Gm (X.Jp x τ (w + a • e + b • X.Jp x τ e)) (w + a • e + b • X.Jp x τ e) =
      a * conj a * X.Hf x τ e e + b * conj b * X.Hf x τ e e + hermC τ.1 X.Gm (X.Jp x τ w) w
    rw [Jp_add, Jp_add, Jp_smul, Jp_smul, Jp_Jp X hx]
    simp only [hC_add_left, hC_smul_left, hC_add_right, hC_smul_right, k1, k2, k3, k4, k5, k6, k7,
      he]
    ring
  rw [hself, hself, hself, Complex.mul_conj, Complex.mul_conj] at h3
  exact_mod_cast h3

lemma unipotent_sub_one_majorant_bound (hpos : ∀ v, v ≠ 0 → 0 < X.maj x τ v) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hδ : ∀ u, hermC τ.1 X.Gm u e = 0 → hermC τ.1 X.Gm u (X.Jp x τ e) = 0 →
      X.maj x τ (δ u • e) ≤ κ ^ 2 * X.maj x τ u) (v : Fin r → ℂ) :
    X.maj x τ (Matrix.mulVec (X.d2n x τ e δ - 1) v) ≤ (3 * κ) ^ 2 * X.maj x τ v := by
  have hnn := maj_nonneg' X hself hpos
  have hqQ : X.d2q x τ e = (X.maj x τ e : ℂ) := hself e
  have hQ : 0 < X.maj x τ e := by
    rcases (hnn e).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hqQ, ← h]; simp) hq
  set Q := X.maj x τ e with hQdef
  set z := X.d2z x τ e δ with hzdef

  have hA : Matrix.mulVec (X.d2n x τ e δ - 1) v =
      (δ (X.d2pi x τ e v) - δ z / 2 * X.d2b x τ e v) • e - X.d2b x τ e v • z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, unipotent_mulVec_formula]
    abel
  rw [hA, maj_Ce_bz X δ hx he hq hself]

  have hv : v = X.d2pi x τ e v + X.d2a x τ e v • e + X.d2b x τ e v • X.Jp x τ e := by
    rw [hyperbolic_projection_apply]; abel
  have hw1 := hyperbolic_projection_perp_e X hx he hq v
  have hw2 := hyperbolic_projection_perp_Je X hx he hq v
  conv_rhs => rw [hv, maj_decomp X hx he hq hself _ hw1 hw2]

  have hz1 : hermC τ.1 X.Gm (X.Jp x τ z) e = 0 := by rw [Jp_adj X hx, unipotent_shift_orthogonal_Je X δ hx he hq]
  have hz2 : hermC τ.1 X.Gm (X.Jp x τ z) (X.Jp x τ e) = 0 := by
    rw [Jp_adj X hx, Jp_Jp X hx, unipotent_shift_orthogonal_e X δ hx he hq]
  have hmJz : X.maj x τ (X.Jp x τ z) = X.maj x τ z := by
    have h1 := hself (X.Jp x τ z)
    have h2 := hself z
    have h3 : X.Hf x τ (X.Jp x τ z) (X.Jp x τ z) = X.Hf x τ z z := by
      show hermC τ.1 X.Gm (X.Jp x τ (X.Jp x τ z)) (X.Jp x τ z) = X.Hf x τ z z
      rw [Jp_Jp X hx, Hf_eq X x hx]
      rfl
    rw [h1, h2] at h3
    exact_mod_cast h3
  have hZc : (X.maj x τ z : ℂ) = (Q : ℂ) * δ (X.Jp x τ z) := by
    rw [← hself z, ← hqQ]
    show hermC τ.1 X.Gm (X.Jp x τ z) z = _
    rw [unipotent_shift_spec X δ hx he hq, hyperbolic_projection_of_perp X hx he hq hz1 hz2]
  have hdJ : δ (X.Jp x τ z) = ((X.maj x τ z / Q : ℝ) : ℂ) := by
    have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
    push_cast
    rw [hZc]
    field_simp
  have hZ0 := hnn z
  have hZ : X.maj x τ z ≤ κ ^ 2 * Q := by
    have h := hδ _ hz1 hz2
    rw [maj_smul X hself, hdJ, Complex.normSq_ofReal, hmJz] at h

    have h' : X.maj x τ z * X.maj x τ z ≤ κ ^ 2 * Q * X.maj x τ z := by
      have e1 : X.maj x τ z / Q * (X.maj x τ z / Q) * Q = X.maj x τ z * X.maj x τ z / Q := by
        field_simp
      rw [e1, div_le_iff₀ hQ] at h
      nlinarith
    rcases hZ0.lt_or_eq with h0 | h0
    · exact le_of_mul_le_mul_right h' h0
    · rw [← h0]; positivity
  have hDz : Complex.normSq (δ z) ≤ κ ^ 4 := by
    have h := hδ z (unipotent_shift_orthogonal_e X δ hx he hq) (unipotent_shift_orthogonal_Je X δ hx he hq)
    rw [maj_smul X hself] at h
    have h2 : Complex.normSq (δ z) * Q ≤ κ ^ 4 * Q := by nlinarith
    exact le_of_mul_le_mul_right h2 hQ
  have hw := hyperbolic_projection_perp_e X hx he hq v
  have hD := hδ (X.d2pi x τ e v) hw1 hw2
  rw [maj_smul X hself] at hD
  have hC : Complex.normSq (δ (X.d2pi x τ e v) - δ z / 2 * X.d2b x τ e v) ≤
      2 * Complex.normSq (δ (X.d2pi x τ e v)) +
        Complex.normSq (δ z) * Complex.normSq (X.d2b x τ e v) / 2 := by
    have h1 := normSq_sub_le_two (δ (X.d2pi x τ e v)) (δ z / 2 * X.d2b x τ e v)
    have h2 : Complex.normSq (δ z / 2 * X.d2b x τ e v) =
        Complex.normSq (δ z) * Complex.normSq (X.d2b x τ e v) / 4 := by
      rw [Complex.normSq_mul, Complex.normSq_div]
      norm_num
      ring
    linarith
  have hWn := hnn (X.d2pi x τ e v)
  have hAn := Complex.normSq_nonneg (X.d2a x τ e v)
  have hBn := Complex.normSq_nonneg (X.d2b x τ e v)
  have hDn := Complex.normSq_nonneg (δ (X.d2pi x τ e v))
  have hDzn := Complex.normSq_nonneg (δ z)
  have hk4 : κ ^ 4 ≤ κ ^ 2 := pow_le_pow_of_le_one hκ0 hκ1 (by norm_num)
  have t1 := mul_le_mul_of_nonneg_right hC hQ.le
  have t2 := mul_le_mul_of_nonneg_left hZ hBn
  have t3 := mul_le_mul_of_nonneg_right hDz (mul_nonneg hBn hQ.le)
  have t4 := mul_le_mul_of_nonneg_right hk4 (mul_nonneg hBn hQ.le)
  have t5 := mul_nonneg (sq_nonneg κ) (mul_nonneg hAn hQ.le)
  have t6 := mul_nonneg (sq_nonneg κ) hWn
  have t7 := mul_nonneg (sq_nonneg κ) (mul_nonneg hBn hQ.le)
  nlinarith

end perTau

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end
