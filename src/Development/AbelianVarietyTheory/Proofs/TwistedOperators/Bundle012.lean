module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

section

open Module

namespace GlobalTheory.DualFrameSpan

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

lemma sum_comp' {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  ext x; simp [LinearMap.sum_apply]

lemma comp_sum' {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  ext x; simp [LinearMap.sum_apply]

lemma eq_zero_of_trace_adjoint_comp_self (B : H →ₗ[ℂ] H)
    (h : LinearMap.trace ℂ H (LinearMap.adjoint B ∘ₗ B) = 0) : B = 0 := by
  set b := stdOrthonormalBasis ℂ H
  rw [LinearMap.trace_eq_sum_inner _ b] at h
  have h' : ∀ i, (inner ℂ (b i) ((LinearMap.adjoint B ∘ₗ B) (b i)) : ℂ)
      = ((‖B (b i)‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast; first | rfl | simp | norm_cast
  simp_rw [h'] at h
  have h2 : (∑ i, ‖B (b i)‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h2
  apply b.toBasis.ext
  intro i
  have := h3 i (Finset.mem_univ _)
  simpa using this

noncomputable def pairing (W : Submodule ℂ (H →ₗ[ℂ] H)) : LinearMap.BilinForm ℂ W :=
  LinearMap.mk₂ ℂ (fun X Y : W => LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)))
    (fun x y z => by simp [LinearMap.add_comp]) (fun c x y => by simp [LinearMap.smul_comp])
    (fun x y z => by simp [LinearMap.comp_add]) (fun c x y => by simp [LinearMap.comp_smul])

lemma pairing_apply (W : Submodule ℂ (H →ₗ[ℂ] H)) (X Y : W) :
    pairing W X Y = LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)) := rfl

lemma pairing_nondegenerate (W : Submodule ℂ (H →ₗ[ℂ] H))
    (hW : ∀ X ∈ W, LinearMap.adjoint X ∈ W) : (pairing W).Nondegenerate := by
  have key : ∀ y : W, (∀ x : W, pairing W x y = 0) → y = 0 := by
    intro y hy
    have := hy ⟨LinearMap.adjoint (y : H →ₗ[ℂ] H), hW _ y.2⟩
    rw [pairing_apply] at this
    exact Subtype.ext (eq_zero_of_trace_adjoint_comp_self _ this)
  refine ⟨fun x hx => key x (fun y => ?_), fun y hy => key y hy⟩
  rw [pairing_apply, LinearMap.trace_comp_comm']
  exact hx y

section span

variable {G : Type} [Mul G] (K : Set G) (ρ : G → (H →ₗ[ℂ] H))

lemma adjoint_mem_span (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g')
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    LinearMap.adjoint X ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', he⟩ := hadj g hg
    rw [he]; exact Submodule.subset_span ⟨g', hg', rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

lemma comp_mem_span (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h) {h : G} (hh : h ∈ K)
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    X ∘ₗ ρ h ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [← hρ g hg h hh]; exact Submodule.subset_span ⟨_, hmul g hg h hh, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [LinearMap.add_comp]; exact add_mem hx hy
  | smul a x _ hx => rw [LinearMap.smul_comp]; exact Submodule.smul_mem _ _ hx

end span

theorem dual_frame : ∀ {G H : Type} [Mul G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g'), ∃ (m : ℕ) (k : Fin m → G) (B : Fin m → (H →ₗ[ℂ] H)), (∀ j, k j ∈ K) ∧
      (∀ A : H →ₗ[ℂ] H, ∀ g ∈ K, LinearMap.trace ℂ H (ρ g ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) * LinearMap.trace ℂ H (ρ g ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j) := by
  intro G H _ _ _ _ K ρ hmul hρ hadj
  classical
  obtain ⟨t, hts, hsp, hli⟩ := exists_linearIndependent ℂ (ρ '' K)
  set W := Submodule.span ℂ (ρ '' K) with hWdef
  have hWt : Submodule.span ℂ (Set.range ((↑) : t → (H →ₗ[ℂ] H))) = W := by
    rw [Subtype.range_coe]; exact hsp
  haveI : Finite t := hli.finite
  letI : Fintype t := Fintype.ofFinite t
  let b0 : Basis t ℂ W := (Basis.span hli).map (LinearEquiv.ofEq _ _ hWt)
  let e := Fintype.equivFin t
  let b : Basis (Fin (Fintype.card t)) ℂ W := b0.reindex e
  have hb : ∀ j, ((b j : W) : H →ₗ[ℂ] H) = ((e.symm j : t) : H →ₗ[ℂ] H) := by
    intro j; simp [b, b0, Basis.span_apply]
  have hbK : ∀ j, ∃ g ∈ K, ρ g = (b j : H →ₗ[ℂ] H) := fun j => by
    rw [hb]; exact hts (e.symm j).2
  choose k hkK hk using hbK
  have hnd := pairing_nondegenerate W (fun X hX => adjoint_mem_span K ρ hadj hX)
  let D := (pairing W).dualBasis hnd b
  have expand : ∀ X ∈ W, X = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ X) • (D j : H →ₗ[ℂ] H) := by
    intro X hX
    have h1 := congrArg Subtype.val (D.sum_repr ⟨X, hX⟩)
    rw [Submodule.coe_sum] at h1
    change _ = X at h1
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, LinearMap.BilinForm.dualBasis_repr_apply, pairing_apply, hk,
      LinearMap.trace_comp_comm' (b j : H →ₗ[ℂ] H) X]
  have hdual : ∀ i j, LinearMap.trace ℂ H (ρ (k i) ∘ₗ (D j : H →ₗ[ℂ] H)) = if i = j then 1 else 0 := by
    intro i j
    rw [hk, LinearMap.trace_comp_comm']
    exact LinearMap.BilinForm.apply_dualBasis_left hnd b j i
  refine ⟨Fintype.card t, k, fun j => (D j : H →ₗ[ℂ] H), hkK, ?_, ?_⟩
  · intro A g hg
    set A' := ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) • (D j : H →ₗ[ℂ] H) with hA'
    have hbi : ∀ i, LinearMap.trace ℂ H (ρ (k i) ∘ₗ A') = LinearMap.trace ℂ H (ρ (k i) ∘ₗ A) := by
      intro i

      simp only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, hdual, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hvan : ∀ C ∈ W, LinearMap.trace ℂ H (C ∘ₗ A') = LinearMap.trace ℂ H (C ∘ₗ A) := by
      intro C hC
      have h1 := congrArg Subtype.val (b.sum_repr ⟨C, hC⟩)
      rw [Submodule.coe_sum] at h1
      change _ = C at h1
      rw [← h1]

      simp only [Submodule.coe_smul, sum_comp', LinearMap.smul_comp, map_sum, map_smul, ← hk, hbi]
    rw [← hvan (ρ g) (Submodule.subset_span ⟨g, hg, rfl⟩)]

    simp only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul]
  · intro i h hh
    exact expand _ (comp_mem_span K ρ hmul hρ hh (D i).2)

end GlobalTheory.DualFrameSpan
end

section

open scoped InnerProductSpace

namespace GlobalTheory

theorem weyl_number_operator_commutation
    (V A κ : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Ring A] [Algebra ℂ A]
    [Fintype κ] (J : V ≃ₗᵢ[ℝ] V) (e : OrthonormalBasis κ ℝ V) (D a c : V → A) (N : A)
    (hJJ : ∀ x, J (J x) = -x) (hadd : ∀ u v, D (u + v) = D u + D v)
    (hsmul : ∀ (r : ℝ) v, D (r • v) = (r : ℂ) • D v)
    (hcomm : ∀ u v, D u * D v - D v * D u =
      (2 * Real.pi * Complex.I * (inner ℝ u (J v) : ℝ) : ℂ) • 1)
    (hc : ∀ z, c z = D z - Complex.I • D (J z)) (ha : ∀ z, a z = -(D z + Complex.I • D (J z)))
    (hN : N = ∑ j, c (e j) * a (e j)) :
    (∀ z, a z * c z - c z * a z = ((4 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) • 1) ∧
    (∀ z, N * c z = c z * (N + ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧
    (∀ z, N * a z = a z * (N - ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧
    ∀ z, D z ∈ Submodule.span ℂ (Set.range (fun j => a (e j)) ∪ Set.range fun j => c (e j)) := by
  have I3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have hJl : ∀ u v, inner ℝ (J u) v = -inner ℝ u (J v) := by
    intro u v
    have h := J.inner_map_map (J u) v
    rw [hJJ, inner_neg_left] at h
    linarith
  have hJself : ∀ z, inner ℝ z (J z) = 0 := by
    intro z
    have h := hJl z z
    have h' := real_inner_comm z (J z)
    linarith
  have hDneg : ∀ w, D (-w) = -D w := by
    intro w
    have h := hsmul (-1) w
    simpa using h
  have key : ∀ F : V → A, (∀ u v, F (u + v) = F u + F v) →
      (∀ (r : ℝ) v, F (r • v) = (r : ℂ) • F v) →
      ∀ w, F w = ∑ j, ((inner ℝ (e j) w : ℝ) : ℂ) • F (e j) := by
    intro F hFa hFs w
    have h := map_sum (AddMonoidHom.mk' F hFa) (fun j => inner ℝ (e j) w • e j) Finset.univ
    simp only [AddMonoidHom.mk'_apply, e.sum_repr'] at h
    rw [h]
    exact Finset.sum_congr rfl fun j _ => hFs _ _
  have hca : ∀ u v, c (u + v) = c u + c v := by
    intro u v; rw [hc, hc, hc, map_add (f := _), hadd, hadd, smul_add]; abel
  have hcs : ∀ (r : ℝ) v, c (r • v) = (r : ℂ) • c v := by
    intro r v; rw [hc, hc, map_smul, hsmul, hsmul, smul_sub, smul_comm Complex.I (r : ℂ)]
  have haa' : ∀ u v, a (u + v) = a u + a v := by
    intro u v; rw [ha, ha, ha, map_add (f := _), hadd, hadd, smul_add]; abel
  have has : ∀ (r : ℝ) v, a (r • v) = (r : ℂ) • a v := by
    intro r v
    rw [ha, ha, map_smul, hsmul, hsmul, smul_comm Complex.I (r : ℂ), ← smul_add, smul_neg]
  have hcJ : ∀ w, c (J w) = Complex.I • c w := by
    intro w
    rw [hc, hc, hJJ, hDneg]
    simp only [smul_sub, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  have haJ : ∀ w, a (J w) = -(Complex.I • a w) := by
    intro w
    rw [ha, ha, hJJ, hDneg]
    simp only [smul_add, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
    abel
  have hsw : ∀ u v, D u * D v = D v * D u +
      (2 * Real.pi * Complex.I * (inner ℝ u (J v) : ℝ) : ℂ) • 1 := by
    intro u v; rw [← hcomm u v]; abel
  have hac : ∀ z w, a z * c w - c w * a z =
      (4 * (Real.pi : ℂ) * ((inner ℝ z w : ℝ) : ℂ)
        - 4 * Real.pi * Complex.I * ((inner ℝ z (J w) : ℝ) : ℂ)) • (1 : A) := by
    intro z w
    rw [ha, hc]
    simp only [mul_sub, sub_mul, mul_add, add_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    rw [hsw z w, hsw z (J w), hsw (J z) w, hsw (J z) (J w)]
    simp only [hJJ, map_neg, inner_neg_right, inner_neg_left, hJl, neg_neg]
    match_scalars <;> (ring_nf; try simp only [Complex.I_sq, I3]; try ring_nf)
  have hcc : ∀ z w, c z * c w = c w * c z := by
    intro z w
    rw [← sub_eq_zero, hc, hc]
    simp only [mul_sub, sub_mul, mul_add, add_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    rw [hsw z w, hsw z (J w), hsw (J z) w, hsw (J z) (J w)]
    simp only [hJJ, map_neg, inner_neg_right, inner_neg_left, hJl, neg_neg]
    match_scalars <;> (ring_nf; try simp only [Complex.I_sq, I3]; try ring_nf)
  have haa : ∀ z w, a z * a w = a w * a z := by
    intro z w
    rw [← sub_eq_zero, ha, ha]
    simp only [mul_sub, sub_mul, mul_add, add_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    rw [hsw z w, hsw z (J w), hsw (J z) w, hsw (J z) (J w)]
    simp only [hJJ, map_neg, inner_neg_right, inner_neg_left, hJl, neg_neg]
    match_scalars <;> (ring_nf; try simp only [Complex.I_sq, I3]; try ring_nf)
  have hcsum := key c hca hcs
  have hasum := key a haa' has
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    rw [hac, hJself, real_inner_self_eq_norm_sq]
    congr 1
    push_cast
    ring
  · intro z
    have hterm : ∀ j, c (e j) * a (e j) * c z - c z * (c (e j) * a (e j)) =
        (4 * (Real.pi : ℂ)) • (((inner ℝ (e j) z : ℝ) : ℂ) • c (e j))
          - (4 * Real.pi * Complex.I) • (((inner ℝ (e j) (J z) : ℝ) : ℂ) • c (e j)) := by
      intro j
      rw [mul_assoc, ← mul_assoc (c z), hcc z (e j), mul_assoc, ← mul_sub, hac (e j) z,
        mul_smul_comm, mul_one]
      module
    have hsum : N * c z - c z * N = ((8 * Real.pi : ℝ) : ℂ) • c z := by
      rw [hN, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      simp only [hterm, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [← hcsum z, ← hcsum (J z), hcJ, smul_smul, ← sub_smul]
      congr 1
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [mul_add, mul_smul_comm, mul_one, ← sub_eq_iff_eq_add', hsum]
  · intro z
    have hterm : ∀ j, c (e j) * a (e j) * a z - a z * (c (e j) * a (e j)) =
        -((4 * (Real.pi : ℂ)) • (((inner ℝ (e j) z : ℝ) : ℂ) • a (e j))
          + (4 * Real.pi * Complex.I) • (((inner ℝ (e j) (J z) : ℝ) : ℂ) • a (e j))) := by
      intro j
      have h1 := hac z (e j)
      have h2 : inner ℝ z (J (e j)) = -inner ℝ (e j) (J z) := by
        rw [real_inner_comm (J (e j)) z, hJl]
      rw [real_inner_comm (e j) z, h2] at h1
      have h3 : c (e j) * a (e j) * a z - a z * (c (e j) * a (e j)) =
          -((a z * c (e j) - c (e j) * a z) * a (e j)) := by
        rw [mul_assoc, haa (e j) z]
        noncomm_ring
      rw [h3, h1, smul_mul_assoc, one_mul]
      simp only [Complex.ofReal_neg]
      module
    have hsum : N * a z - a z * N = -(((8 * Real.pi : ℝ) : ℂ) • a z) := by
      rw [hN, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      simp only [hterm, Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
      rw [← hasum z, ← hasum (J z), haJ, smul_neg, smul_smul, ← sub_eq_add_neg, ← sub_smul]
      congr 2
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [mul_sub, mul_smul_comm, mul_one, sub_eq_iff_eq_add.mp hsum]
    abel
  · intro z
    have hDz : D z = (1 / 2 : ℂ) • (c z - a z) := by
      rw [hc, ha]
      module
    rw [hDz, hcsum z, hasum z]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_) <;>
      refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    · exact Or.inr ⟨j, rfl⟩
    · exact Or.inl ⟨j, rfl⟩

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory.SeparatedSetCardBound

theorem card_le_of_separated {G E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (φ : G → E) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (T : Finset G)
    (hT : ∀ h ∈ T, ‖φ h‖ ≤ R) (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r < ‖φ a - φ b‖) :
    (T.card : ℝ) ≤ ((R + r) / r) ^ Module.finrank ℝ E := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure E, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  haveI := hμ
  set d := Module.finrank ℝ E
  have hdisj : Set.PairwiseDisjoint (T : Set G) (fun h => Metric.ball (φ h) r) := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_iff]
    rintro z ⟨hza, hzb⟩
    have hs := hsep a ha b hb hab
    rw [Metric.mem_ball, dist_eq_norm] at hza hzb
    have h3 : ‖φ a - φ b‖ ≤ ‖z - φ b‖ + ‖z - φ a‖ := by
      calc ‖φ a - φ b‖ = ‖(z - φ b) - (z - φ a)‖ := by congr 1; abel
        _ ≤ ‖z - φ b‖ + ‖z - φ a‖ := norm_sub_le _ _
    linarith
  have hsub : (⋃ h ∈ T, Metric.ball (φ h) r) ⊆ Metric.ball (0 : E) (R + r) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨h, hh, hz⟩ := hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have h4 : ‖z‖ ≤ ‖z - φ h‖ + ‖φ h‖ := by
      calc ‖z‖ = ‖(z - φ h) + φ h‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - φ h‖ + ‖φ h‖ := norm_add_le _ _
    linarith [hT h hh]
  have hle : μ (⋃ h ∈ T, Metric.ball (φ h) r) ≤ μ (Metric.ball (0 : E) (R + r)) := measure_mono hsub
  rw [measure_biUnion_finset hdisj (fun h _ => measurableSet_ball)] at hle
  simp only [Measure.addHaar_ball_of_pos _ _ hr, Measure.addHaar_ball_of_pos _ _ (by linarith : (0 : ℝ) < R + r),
    Finset.sum_const, nsmul_eq_mul] at hle
  have hB0 : μ (Metric.ball (0 : E) 1) ≠ 0 := (Metric.measure_ball_pos μ _ one_pos).ne'
  have hBt : μ (Metric.ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hB0 hBt] at hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hrd : 0 < r ^ d := pow_pos hr d
  rw [div_pow, le_div_iff₀ hrd]
  exact hle

theorem main : ∀ {G E : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : MeasureTheory.Measure G) [MeasureTheory.Measure.IsMulLeftInvariant μ] [MeasureTheory.SFinite μ] [inst_8 : NormedAddCommGroup E] [inst_9 : NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : G → E), Continuous φ → ∀ (W : Set G) (R r : ℝ), (0 : ℝ) ≤ R → (0 : ℝ) < r → (∀ (g h : G), ‖φ h‖ ≤ R → ‖φ g - φ h‖ ≤ (2 : ℝ) * r → h⁻¹ * g ∈ W) → (μ : Set G → ENNReal) {g : G | ‖φ g‖ ≤ R} ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * (μ : Set G → ENNReal) W := by
  intro G E _ _ _ _ _ _ μ _ _ _ _ _ φ _ W R r hR hr hW
  classical
  let P : Finset G → Prop := fun T =>
    (∀ h ∈ T, ‖φ h‖ ≤ R) ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r < ‖φ a - φ b‖
  let A : Set ℕ := {n | ∃ T, P T ∧ T.card = n}
  have hA0 : A.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hAb : BddAbove A := by
    refine ⟨⌈((R + r) / r) ^ Module.finrank ℝ E⌉₊, ?_⟩
    rintro n ⟨T, hT, rfl⟩
    have h1 := card_le_of_separated φ R r hR hr T hT.1 hT.2
    have h2 := h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  obtain ⟨T, hT, hTc⟩ := Nat.sSup_mem hA0 hAb
  have hcover : {g : G | ‖φ g‖ ≤ R} ⊆ ⋃ h ∈ T, (fun x => h⁻¹ * x) ⁻¹' W := by
    intro g hg
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists] at hne
    have hg' : ‖φ g‖ ≤ R := hg
    have hgT : g ∉ T := fun hgT => hne g hgT (hW g g hg' (by simp; positivity))
    have far : ∀ h ∈ T, 2 * r < ‖φ g - φ h‖ := by
      intro h hh
      by_contra hle
      push_neg at hle
      exact hne h hh (hW g h (hT.1 h hh) hle)
    have hP : P (insert g T) := by
      refine ⟨?_, ?_⟩
      · intro h hh
        rw [Finset.mem_insert] at hh
        rcases hh with rfl | hh
        · exact hg'
        · exact hT.1 h hh
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact far b hb
        · rw [norm_sub_rev]; exact far a ha
        · exact hT.2 a ha b hb hab
    have hmem : (insert g T).card ∈ A := ⟨_, hP, rfl⟩
    have hle := le_csSup hAb hmem
    rw [Finset.card_insert_of_notMem hgT, ← hTc] at hle
    omega
  calc μ {g : G | ‖φ g‖ ≤ R} ≤ μ (⋃ h ∈ T, (fun x => h⁻¹ * x) ⁻¹' W) := measure_mono hcover
    _ ≤ ∑ h ∈ T, μ ((fun x => h⁻¹ * x) ⁻¹' W) := measure_biUnion_finset_le _ _
    _ = T.card * μ W := by simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * μ W := by
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (card_le_of_separated φ R r hR hr T hT.1 hT.2)

end GlobalTheory.SeparatedSetCardBound
end

section

namespace GlobalTheory.LemmaTwoFortyThirteen

theorem main {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ (0 : R) ∧ a • v ∈ M) :
    Submodule.span K (↑M : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha, hav⟩ := h v
  have hK : algebraMap R K a ≠ 0 := by
    simpa using (IsFractionRing.injective R K).ne ha
  have hv : v = (algebraMap R K a)⁻¹ • (a • v) := by
    rw [← algebraMap_smul K a v, smul_smul, inv_mul_cancel₀ hK, one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hav)

end GlobalTheory.LemmaTwoFortyThirteen
end
