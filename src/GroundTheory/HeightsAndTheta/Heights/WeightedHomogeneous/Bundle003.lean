module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseChart
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField
open scoped ContDiff

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}


namespace ArithVariety

variable (P : ArithVariety n)

def IsLive (c : (k : ι) → Fin (n k + 1)) : Prop :=
  ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal

def chartRing (c : (k : ι) → Fin (n k + 1)) : Subring P.FunField :=
  Subring.closure (Set.range (P.chartCoord c))

def chartPow (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) : P.FunField :=
  ∏ k, P.mkF (X ⟨k, c k⟩) ^ a k

def IsOfDegree (a : ι → ℤ) (x : P.FunField) : Prop :=
  ∃ (f g : MvPolynomial (Coord n) ℤ) (δf δg : ι → ℕ), IsWeightedHomogeneous (coordDeg n) f δf ∧
    IsWeightedHomogeneous (coordDeg n) g δg ∧ (∀ k, (δf k : ℤ) - δg k = a k) ∧ g ∉ P.ideal ∧
    x = P.mkF f / P.mkF g

end ArithVariety

structure AddBlockData (P : ArithVariety n) where

  deg : ι → ℤ

  size : ℕ

  elt : Fin (size + 1) → P.FunField
  elt_deg : ∀ j, P.IsOfDegree deg (elt j)
  chart_mem : ∀ c, P.IsLive c → ∀ j, elt j / P.chartPow c deg ∈ P.chartRing c
  generating : ∀ c, P.IsLive c → ∃ u : Fin (size + 1) → P.FunField,
    (∀ j, u j ∈ P.chartRing c) ∧ ∑ j, u j * (elt j / P.chartPow c deg) = 1

namespace AddBlockData

variable {P : ArithVariety n} (D : AddBlockData P)

def extSizes : Option ι → ℕ := fun o ↦ o.elim D.size n

def den (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ)
    {r : ℕ} (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ) (z : Cone n ℂ) : ℝ :=
  (∑ c, ∑ j, ‖evalCone z (g c j)‖ ^ 2) +
    ∑ i, ‖evalCone z (G i)‖ ^ 2 * ∏ k, l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k))

end AddBlockData

namespace HermLine

def pow (A : HermLine n) (m : ℕ) : HermLine n where
  deg := m • A.deg
  metric z := A.metric z ^ m
  metric_pos z hz := pow_pos (A.metric_pos z hz) m
  metric_smul c z hc hz := by
    rw [A.metric_smul c z hc hz, mul_pow, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Pi.smul_apply, nsmul_eq_mul, mul_comm, zpow_mul, zpow_natCast]
  metric_smooth := A.metric_smooth.pow m

def inv (A : HermLine n) : HermLine n where
  deg := -A.deg
  metric z := (A.metric z)⁻¹
  metric_pos z hz := inv_pos.mpr (A.metric_pos z hz)
  metric_smul c z hc hz := by
    rw [A.metric_smul c z hc hz, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Pi.neg_apply, zpow_neg]
  metric_smooth := A.metric_smooth.inv fun z hz ↦ (A.metric_pos z hz).ne'

end HermLine

omit [DecidableEq ι] in
theorem chartMonomial_add (c : (k : ι) → Fin (n k + 1)) (d d' : ι → ℕ) :
    chartMonomial c (d + d') = chartMonomial c d * chartMonomial c d' := by
  simp only [chartMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq ι] in
theorem chartMonomial_nsmul (c : (k : ι) → Fin (n k + 1)) (m : ℕ) (d : ι → ℕ) :
    chartMonomial c (m • d) = chartMonomial c d ^ m := by
  simp only [chartMonomial, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm]


namespace IntegralSection

variable {P : ArithVariety n} {a b : ι → ℤ}

def pow (s : IntegralSection P a) (m : ℕ) : IntegralSection P (m • a) where
  num := s.num ^ m
  den := s.den ^ m
  numDeg := m • s.numDeg
  denDeg := m • s.denDeg
  num_isHomogeneous := s.num_isHomogeneous.pow m
  den_isHomogeneous := s.den_isHomogeneous.pow m
  deg_eq k := by
    simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
    rw [← s.deg_eq k]
    ring
  den_not_mem h := s.den_not_mem (P.isPrime.mem_of_pow_mem m h)
  regular c hc := by
    obtain ⟨d, e, ⟨δ, he, hδ⟩, hmem⟩ := s.regular c hc
    refine ⟨m • d, e ^ m, ⟨m • δ, he.pow m, fun k ↦ ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, hδ k]
      ring
    · rw [chartMonomial_nsmul, ← Ideal.Quotient.eq_zero_iff_mem]
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at hmem
      rw [map_sub, sub_eq_zero, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, ← mul_pow,
        ← mul_pow, ← map_mul, ← map_mul, hmem]

end IntegralSection

def blockIncl (k₀ : ι) : Coord (fun _ : Unit ↦ n k₀) → Coord n := fun v ↦ ⟨k₀, v.2⟩

variable {K : Type*} [Field K] [NumberField K] {e r : ℕ}


end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace IdealIndexPlaces

theorem genIndex_comap {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G' →+ G)
    {A B : AddSubgroup G} (hA : A ≤ f.range) (hB : B ≤ f.range) :
    genIndex (A.comap f) (B.comap f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_comap, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self hA,
    AddSubgroup.map_comap_eq_self hB]

theorem absNorm_eq_index {L : Type*} [Field L] [NumberField L] (A : Ideal (𝓞 L)) :
    A.absNorm = A.toAddSubgroup.index := Ideal.absNorm_eq_index A

theorem genIndex_ideal {L : Type*} [Field L] [NumberField L] {A B : Ideal (𝓞 L)} (hA : A ≠ ⊥)
    (hB : B ≠ ⊥) : genIndex A.toAddSubgroup B.toAddSubgroup = (B.absNorm : ℝ) / A.absNorm := by
  have hAB : A ⊓ B ≠ ⊥ := fun h ↦ (mul_ne_zero hA hB) (le_bot_iff.mp (h ▸ Ideal.mul_le_inf))
  have hn : (A ⊓ B).absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hAB
  have hAn : A.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hA
  have hBn : B.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hB
  have h1 : B.toAddSubgroup.relIndex A.toAddSubgroup * A.absNorm = (A ⊓ B).absNorm := by
    rw [← AddSubgroup.inf_relIndex_left A.toAddSubgroup B.toAddSubgroup, absNorm_eq_index,
      AddSubgroup.relIndex_mul_index inf_le_left, absNorm_eq_index]
    rfl
  have h2 : A.toAddSubgroup.relIndex B.toAddSubgroup * B.absNorm = (A ⊓ B).absNorm := by
    rw [← AddSubgroup.inf_relIndex_right A.toAddSubgroup B.toAddSubgroup, absNorm_eq_index,
      AddSubgroup.relIndex_mul_index inf_le_right, absNorm_eq_index]
    rfl
  have h1' : (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) = (A ⊓ B).absNorm / A.absNorm := by
    rw [← h1]; push_cast; field_simp
  have h2' : (A.toAddSubgroup.relIndex B.toAddSubgroup : ℝ) = (A ⊓ B).absNorm / B.absNorm := by
    rw [← h2]; push_cast; field_simp
  unfold genIndex
  rw [h1', h2']
  field_simp

end IdealIndexPlaces


open IdealIndexPlaces in
theorem IdealIndexPlaces.proof : IdealIndexPlaces.Statement := by
  intro L _ _ ι _ y hy
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L)) y
  choose z hz using hint
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL : (b : L) ≠ 0 := by rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hzy : ∀ i, ((z i : 𝓞 L) : L) = (b : L) * y i := fun i ↦ by
    have h := hz i
    simp only [Algebra.smul_def] at h
    exact h
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  replace hi0 : y i0 ≠ 0 := hi0
  set c : 𝓞 L := z i0 with hc
  have hcy : (c : L) = b * y i0 := hzy i0
  have hcL : (c : L) ≠ 0 := by rw [hcy]; exact mul_ne_zero hbL hi0
  have hc0 : c ≠ 0 := fun h ↦ hcL (by rw [h]; rfl)
  set M := multiplierIdeal y with hMdef
  let g : 𝓞 L →ₗ[𝓞 L] L :=
    (LinearMap.mulLeft (𝓞 L) ((c : L)⁻¹)).comp (Algebra.linearMap (𝓞 L) L)
  have hg : ∀ t, g t = (c : L)⁻¹ * t := fun t ↦ rfl
  set I : Ideal (𝓞 L) := M.comap g with hIdef
  set J : Ideal (𝓞 L) := Ideal.span (Set.range z) with hJdef
  have hI : ∀ t : 𝓞 L, t ∈ I ↔ ∀ i, t * z i ∈ Ideal.span {c * b} := by
    intro t
    change (∀ i, (c : L)⁻¹ * t * y i ∈ Set.range (algebraMap (𝓞 L) L)) ↔ _
    refine forall_congr' fun i ↦ ?_
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨e, he⟩
      refine ⟨e, RingOfIntegers.ext ?_⟩
      change (e : L) * ((c : L) * b) = t * z i
      change (e : L) = _ at he
      rw [he, hzy i]
      field_simp
    · rintro ⟨e, he⟩
      refine ⟨e, ?_⟩
      have he' : (e : L) * ((c : L) * b) = t * z i := congrArg (fun s : 𝓞 L ↦ (s : L)) he
      rw [hzy i] at he'
      have h3 : (e : L) * c = t * y i := mul_right_cancel₀ hbL (by linear_combination he')
      change (e : L) = _
      field_simp
      linear_combination h3

  have hIJ : I * J ≤ Ideal.span {c * b} := by
    refine Ideal.mul_le.mpr fun t ht s hs ↦ ?_
    have hle : J ≤ Submodule.comap (LinearMap.mulLeft (𝓞 L) t) (Ideal.span {c * b}) :=
      Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (hI t).mp ht i)
    exact hle hs
  have hcbJ : Ideal.span {c * b} ≤ J :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mul_mem_right b J (Ideal.subset_span ⟨i0, rfl⟩))
  have hcb0 : Ideal.span {c * b} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact mul_ne_zero hc0 hb0
  have hJ0 : J ≠ ⊥ := fun h ↦ hcb0 (le_bot_iff.mp (h ▸ hcbJ))
  obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.mpr hcbJ
  have hKI : K ≤ I := fun t ht ↦ (hI t).mpr fun i ↦ by
    rw [hK, mul_comm t]; exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_range_self i)) ht
  have hIK : I ≤ K := by
    have h : J * K ∣ J * I := Ideal.dvd_iff_le.mpr (by rw [mul_comm J I, ← hK]; exact hIJ)
    exact Ideal.le_of_dvd ((mul_dvd_mul_iff_left hJ0).mp h)
  have hIeq : I = K := le_antisymm hIK hKI
  have hI0 : I ≠ ⊥ := by
    intro h; rw [hIeq] at h; rw [h, Ideal.mul_bot] at hK; exact hcb0 hK
  have hnorm : (I.absNorm : ℝ) * J.absNorm =
      |((Algebra.norm ℤ c : ℤ) : ℝ)| * |((Algebra.norm ℤ b : ℤ) : ℝ)| := by
    have h := congrArg (fun A ↦ (Ideal.absNorm A : ℝ)) hK
    simp only [map_mul, Ideal.absNorm_span_singleton, Int.natAbs_mul, Nat.cast_mul,
      Nat.cast_natAbs] at h
    rw [hIeq]
    push_cast at h
    linear_combination -1 * h

  set C : Ideal (𝓞 L) := (1 : Submodule (𝓞 L) L).comap g with hCdef
  have hC : C = Ideal.span {c} := by
    ext t
    rw [Ideal.mem_span_singleton']
    show g t ∈ (1 : Submodule (𝓞 L) L) ↔ _
    rw [Submodule.mem_one, hg]
    constructor
    · rintro ⟨e, he⟩
      refine ⟨e, RingOfIntegers.ext ?_⟩
      change (e : L) * c = t
      change (e : L) = _ at he
      rw [he]
      field_simp
    · rintro ⟨e, rfl⟩
      refine ⟨e, ?_⟩
      change (e : L) = (c : L)⁻¹ * ((e : L) * c)
      field_simp
  have hrange1 : M.toAddSubgroup ≤ g.toAddMonoidHom.range := by
    intro a ha
    have ha' : a ∈ M := ha
    obtain ⟨e, he⟩ := ha' i0
    refine ⟨b * e, ?_⟩
    change (c : L)⁻¹ * ((b : L) * e) = a
    change (e : L) = _ at he
    rw [he, hcy]
    field_simp
  have hrange2 : (1 : Submodule (𝓞 L) L).toAddSubgroup ≤ g.toAddMonoidHom.range := by
    intro a ha
    obtain ⟨e, rfl⟩ := Submodule.mem_one.mp ha
    refine ⟨c * e, ?_⟩
    change (c : L)⁻¹ * ((c : L) * e) = e
    field_simp
  have hC0 : C ≠ ⊥ := by rw [hC, Ne, Ideal.span_singleton_eq_bot]; exact hc0
  have hgen : genIndex M.toAddSubgroup (1 : Submodule (𝓞 L) L).toAddSubgroup =
      |((Algebra.norm ℤ c : ℤ) : ℝ)| / I.absNorm := by
    rw [← genIndex_comap g.toAddMonoidHom hrange1 hrange2]
    have e1 : M.toAddSubgroup.comap g.toAddMonoidHom = I.toAddSubgroup := rfl
    have e2 : (1 : Submodule (𝓞 L) L).toAddSubgroup.comap g.toAddMonoidHom = C.toAddSubgroup := rfl
    rw [e1, e2, genIndex_ideal hI0 hC0, hC, Ideal.absNorm_span_singleton, Nat.cast_natAbs]
    push_cast
    rfl

  have hz0 : z ≠ 0 := fun h ↦ hc0 (congrFun h i0)
  have hprodz := absNorm_mul_finprod_finitePlace_eq_one hz0
  have hsup : ∀ w : FinitePlace L, ⨆ i, w (z i : L) = w (b : L) * ⨆ i, w (y i) := by
    intro w
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [hsup] at hprodz
  rw [finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hbL) (hasFiniteMulSupport_iSup_place hy),
    FinitePlace.prod_eq_inv_abs_norm_int hb0] at hprodz
  rw [hgen]
  set P := ∏ᶠ w : FinitePlace L, ⨆ i, w (y i) with hPdef
  have hbn : |((Algebra.norm ℤ b : ℤ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero, Int.cast_ne_zero, Ne, Algebra.norm_eq_zero_iff]; exact hb0
  have hIn : (I.absNorm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  have hJn : (J.absNorm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ0)
  have hinv := mul_inv_cancel₀ hbn
  have hP : (J.absNorm : ℝ) * P = |((Algebra.norm ℤ b : ℤ) : ℝ)| := by
    linear_combination |((Algebra.norm ℤ b : ℤ) : ℝ)| * hprodz - (J.absNorm : ℝ) * P * hinv
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq hIn]
  apply mul_left_cancel₀ hJn
  linear_combination |((Algebra.norm ℤ c : ℤ) : ℝ)| * hP - hnorm

end

end GroundTheory.Heights₂.Heights
end
