module

public import Formalism.HermitianCurvature.StatementJ
public import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix

namespace Formalism.FourierDecayAlt.P.Jx6

end Formalism.FourierDecayAlt.P.Jx6

namespace Formalism.FourierDecayAlt.P

open Jx6

theorem form_gives_theorem_A : Formalism.FourierDecayAlt.J.FormGivesMain := by
  intro hM P _ B hPos he hKV h2A hF hMass hform hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35⟩ := hPos
  have hn : 0 < B.n0c := a33
  have hen : 0 < B.e1 * B.n0c := mul_pos he hn
  have key := hM P { B with supdens := B.e1, KtopV := B.KV / (B.e1 * B.n0c) }
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, he.le, a35⟩ h2A hF
    (by
      constructor
      · show B.KV ≤ B.e1 * B.n0c * (B.KV / (B.e1 * B.n0c))
        rw [mul_div_cancel₀ _ hen.ne']
      · show 0 ≤ B.KV / (B.e1 * B.n0c)
        exact div_nonneg hKV hen.le)
    hMass
    (by show B.e1 ≤ B.e1; exact le_refl _)
    (by
      show B.c0 * B.c0' * (B.KV / (B.e1 * B.n0c)) ≤ (1 + B.δ) * B.IntN
      rw [← mul_div_assoc, div_le_iff₀ hen]
      linarith)
    hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  exact key

end Formalism.FourierDecayAlt.P
end

section

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.FiniteSumSwap

theorem finsum_swap {I J : Type} (P : I → Prop) [DecidablePred P] (T : J → Prop) [DecidablePred T]
    (hP : {q | P q}.Finite) (hT : {z | T z}.Finite) (a : ℂ) (g : J → ℂ) (F : J → I → ℂ)
    (e : I → ℂ) :
    ∑ᶠ q : I, (if P q then a * ∑ᶠ z : J, (if T z then g z * F z q else 0) else 0) * e q =
      a * ∑ᶠ z : J, (if T z then g z * ∑ᶠ q : I, (if P q then F z q else 0) * e q else 0) := by
  have h1 : ∀ f : I → ℂ, ∑ᶠ q : I, (if P q then f q else 0) * e q =
      ∑ q ∈ hP.toFinset, f q * e q := by
    intro f
    rw [finsum_eq_sum_of_support_subset (s := hP.toFinset)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [if_pos (by simpa using hq)]
    · intro q hq
      by_contra hq'
      have : ¬ P q := by simpa using hq'
      simp [this] at hq
  have h2 : ∀ f : J → ℂ, ∑ᶠ z : J, (if T z then f z else 0) = ∑ z ∈ hT.toFinset, f z := by
    intro f
    rw [finsum_eq_sum_of_support_subset (s := hT.toFinset)]
    · refine Finset.sum_congr rfl fun z hz => ?_
      rw [if_pos (by simpa using hz)]
    · intro z hz
      by_contra hz'
      have : ¬ T z := by simpa using hz'
      simp [this] at hz
  rw [h1, h2]
  simp_rw [h1, h2]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun q _ => ?_
  ring

end Formalism.FourierDecayAlt.P.FiniteSumSwap

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.FiniteSumSwap

theorem germExpansionKernelOfSteps : Formalism.FourierDecayAlt.A6.GermKernelAssemble := by
  intro hGerm hKp hInt hRoots K _ _ _ R ψ hD hn m hm γ hγ h Q hQ hQu
  obtain ⟨V, hV, H⟩ := hGerm K R ψ hD hn m hm γ hγ h Q hQ hQu
  refine ⟨V, hV, fun t c ht hc w' => ?_⟩
  have := hD.artin
  have := hD.red
  have hT : {z : Kˣ | z ^ (m + 1) = (-t) ^ m * c}.Finite :=
    hRoots K (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) ((-t) ^ m * c)
  have hP : {q : Cos R w' | IsInt R (orbZ w' (rep R q))}.Finite := hInt K R ψ hD w'
  rw [hKp K R ψ hD (pt2 h m t c) w']
  simp_rw [H t c ht hc]
  unfold germSum
  simp_rw [hKp K R ψ hD (addBlock h (m + 1) _) w']
  classical
  convert finsum_swap (fun q : Cos R w' => IsInt R (orbZ w' (rep R q)))
    (fun z : Kˣ => z ^ (m + 1) = (-t) ^ m * c) hP hT _ (germCoef R ψ m γ t)
    (fun z q => bbZ R ψ (addBlock h (m + 1) z) (orbZ w' (rep R q)))
    (fun q => conj (phase ψ (rep R q)))

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.FourierDecayAlt.A6

namespace Formalism.FourierDecayAlt.P

namespace A6x1

theorem norm_sq_sum_orth {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : Type}
    [Fintype A] (P : A → E) (e₁ : A → ℂ) (he : ∀ ρ, ‖e₁ ρ‖ = 1)
    (h : ∀ ρ ρ', ρ ≠ ρ' → inner ℂ (P ρ) (P ρ') = 0) :
    ‖∑ ρ, e₁ ρ • P ρ‖ ^ 2 = ∑ ρ, ‖P ρ‖ ^ 2 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [inner_sum, Finset.sum_eq_single ρ]
  · rw [inner_self_eq_norm_sq (𝕜 := ℂ), norm_smul, he ρ, one_mul]
  · intro ρ' _ hne
    rw [inner_smul_left, inner_smul_right, h ρ ρ' (Ne.symm hne), mul_zero, mul_zero]
  · intro hρ
    exact absurd (Finset.mem_univ ρ) hρ

end A6x1

theorem doubleMeanSplit : Formalism.FourierDecayAlt.A6.MeanSplit := by
  intro E _ _ A B _ _ u e₁ e₂
  rw [Fintype.sum_prod_type, mul_inv, mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [smul_comm, Finset.smul_sum (r := e₁ ρ)]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul]

theorem partialMeansOrthogonal : Formalism.FourierDecayAlt.A6.POrth := by
  intro E _ _ A B _ _ u e₂ h ρ ρ' hne
  simp only [inner_smul_left, inner_smul_right, sum_inner, inner_sum]
  simp [h ρ ρ' _ _ hne]

theorem orthogonalMeanNorm : Formalism.FourierDecayAlt.A6.OrthNorm := by
  intro E _ _ A _ P e₁ he h
  rw [norm_smul, mul_pow, A6x1.norm_sq_sum_orth P e₁ he h, norm_inv, Complex.norm_natCast]

theorem averageBoundOfSteps : Formalism.FourierDecayAlt.A6.AvgBoundAssemble := by
  intro hM hP hO E _ _ A B _ _ u T e₁ e₂ hT he h
  rw [hM E A B u e₁ e₂]
  have h1 := hO E A (fun ρ => (Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b)) e₁ he
    (hP E A B u e₂ h)
  have h2 := hT ((Fintype.card A : ℂ)⁻¹ •
    ∑ ρ, e₁ ρ • ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b)))
  calc _ ≤ ‖(Fintype.card A : ℂ)⁻¹ •
        ∑ ρ, e₁ ρ • ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b))‖ ^ 2 := by
        gcongr
    _ = _ := by rw [h1]; ring

theorem averageBound : Formalism.FourierDecayAlt.A6.AvgBound :=
  averageBoundOfSteps doubleMeanSplit partialMeansOrthogonal orthogonalMeanNorm

end Formalism.FourierDecayAlt.P
end

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P

namespace RealPowerIdentities

theorem inv_pow_triangle_mul_rpow_half {T : ℝ} (hT : 0 < T) (m : ℕ) :
    (T ^ (m * (m + 1) / 2))⁻¹ * T ^ ((m : ℝ) / 2) = T ^ (-((m : ℝ) ^ 2) / 2) := by
  have h2 : (2 : ℕ) ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  have hc : ((m * (m + 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    push_cast
    ring
  rw [← Real.rpow_natCast, hc, ← Real.rpow_neg hT.le, ← Real.rpow_add hT]
  congr 1
  ring

theorem rpow_half_mul_pow_triangle {Z : ℝ} (hZ : 0 < Z) {m : ℕ} (hm : 1 ≤ m) :
    Z ^ ((m : ℝ) / 2) * Z ^ (m * (m - 1) / 2) = Z ^ ((m : ℝ) ^ 2 / 2) := by
  have h2 : (2 : ℕ) ∣ m * (m - 1) := (Nat.even_mul_pred_self m).two_dvd
  have hc : ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    push_cast [Nat.cast_sub hm]
    ring
  rw [← Real.rpow_natCast, hc, ← Real.rpow_add hZ]
  congr 1
  ring

end RealPowerIdentities

open RealPowerIdentities in
theorem germExpansionOfTestFunction : Formalism.FourierDecayAlt.A6.GermPhiAssemble := by
  intro hOsc hSt hInv hMod K _ _ _ R ψ hd hn m hm γ hγ L₀ Λ₀ Q hL₀ hΛ₀ hQc hQu
  obtain ⟨L₁, Λ₁, hL₁, hΛ₁, V₁, hV₁, hO⟩ := hOsc K R ψ hd hn m hm L₀ Λ₀ Q hL₀ hΛ₀ hQc hQu
  have hQ'c : IsCompact ((fun d : K => (-1) ^ m * d) '' Q) :=
    hQc.image (continuous_const.mul continuous_id)
  have hQ'u : ∀ d ∈ (fun d : K => (-1) ^ m * d) '' Q, IsUnit d := by
    rintro _ ⟨d, hdQ, rfl⟩
    exact (isUnit_one.neg.pow m).mul (hQu d hdQ)
  obtain ⟨V₂, hV₂, hS⟩ := hSt K R ψ hd hn m hm γ hγ L₁ Λ₁ _ hL₁ hΛ₁ hQ'c hQ'u
  refine ⟨V₁ ∩ V₂, Filter.inter_mem hV₁ hV₂, ?_⟩
  intro Φ hΦ t c ht hc
  have hD : ((c * t ^ m : Kˣ) : K) ∈ Q := by simpa using hc
  obtain ⟨A, hA, hAz, hAo⟩ := hO Φ hΦ (c * t ^ m) hD
  obtain ⟨Λ, hΛ, hinv⟩ := hInv K R ψ hd hn m L₁ Λ₁ hL₁ hΛ₁ A ((t⁻¹ : Kˣ) : K)
    (((-1) ^ m * (c * t ^ m) : Kˣ) : K) hA
  have hD' : (((-1) ^ m * (c * t ^ m) : Kˣ) : K) ∈ (fun d : K => (-1) ^ m * d) '' Q :=
    ⟨_, hD, by simp⟩
  have hDeq : ((-1) ^ m * (c * t ^ m) : Kˣ) = (-t) ^ m * c := by
    rw [neg_pow t m]
    ac_rfl
  have hT : 0 < modK R (t : K) := (hMod K R ψ hd t t).1
  rw [hAo t c ht.1 rfl Λ hΛ hinv, hS t _ A ht.2 hD' hA Λ hΛ hinv]
  unfold germSum
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_pow_triangle_mul_rpow_half hT m]
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : z ^ (m + 1) = (-1) ^ m * (c * t ^ m)
  · have hZ : 0 < modK R (z : K) := (hMod K R ψ hd z z).1
    rw [if_pos hz, if_pos (hz.trans hDeq), hAz z hz]
    unfold germCoef
    rw [← rpow_half_mul_pow_triangle hZ hm]
    push_cast
    ring
  · rw [if_neg hz, if_neg (fun h => hz (h.trans hDeq.symm))]

end Formalism.FourierDecayAlt.P
end

section

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.A6x2

lemma normsq_eq_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (w : E) :
    ((‖w‖ : ℝ) : ℂ) ^ 2 = inner ℂ w w := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w).symm

lemma sum_addChar_norm_sq (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (G : Type)
    [AddCommGroup G] [Fintype G] (v : G → E) :
    ∑ χ : AddChar G ℂ, ‖∑ g, χ (-g) • v g‖ ^ 2 = (Fintype.card G : ℝ) * ∑ g, ‖v g‖ ^ 2 := by
  classical
  have key : ((∑ χ : AddChar G ℂ, ‖∑ g, χ (-g) • v g‖ ^ 2 : ℝ) : ℂ) =
      (((Fintype.card G : ℝ) * ∑ g, ‖v g‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    have h1 : ∀ χ : AddChar G ℂ, ((‖∑ g, χ (-g) • v g‖ : ℂ)) ^ 2 =
        ∑ g, ∑ h, χ (g - h) * inner ℂ (v g) (v h) := by
      intro χ
      rw [normsq_eq_inner, sum_inner]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [inner_smul_left, inner_smul_right, AddChar.map_neg_eq_conj, Complex.conj_conj,
        sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ g : G, ∑ χ : AddChar G ℂ, ∑ h, χ (g - h) * inner ℂ (v g) (v h) =
        (Fintype.card G : ℂ) * (‖v g‖ : ℂ) ^ 2 := by
      intro g
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite, sub_eq_zero]
      rw [Finset.sum_eq_single g]
      · rw [if_pos rfl, normsq_eq_inner]
      · intro b _ hb
        rw [if_neg (Ne.symm hb), zero_mul]
      · intro h; exact absurd (Finset.mem_univ g) h
    simp_rw [h2]
    rw [Finset.mul_sum]
  exact_mod_cast key

theorem parsevalGroup : ParsevalGroup := by
  intro E _ _ G _ _ v
  classical
  rw [finsum_eq_sum_of_fintype]
  have hN : (Fintype.card G : ℝ) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos_iff.2 ⟨0⟩
    positivity
  have h1 : ∀ χ : AddChar G ℂ, ‖(Fintype.card G : ℂ)⁻¹ • ∑ g, χ (-g) • v g‖ ^ 2 =
      ((Fintype.card G : ℝ)⁻¹) ^ 2 * ‖∑ g, χ (-g) • v g‖ ^ 2 := by
    intro χ
    rw [norm_smul, mul_pow, norm_inv, Complex.norm_natCast]
  simp_rw [h1]
  rw [← Finset.mul_sum, sum_addChar_norm_sq]
  field_simp

theorem pSDClosed : PSDClosed := by
  intro X F k l hk hl a
  have ht : Tendsto (fun j => ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y) atTop
      (𝓝 (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y)) :=
    tendsto_finsetSum _ fun x hx => tendsto_finsetSum _ fun y hy => (hl x hx y hy).const_mul _
  constructor
  · have h1 := (Complex.continuous_im.tendsto _).comp ht
    have h2 : (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).im) = fun _ => (0 : ℝ) := by
      funext j; exact (hk j a).1
    have h3 : Tendsto (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).im) atTop
        (𝓝 ((∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y).im)) := h1
    rw [h2] at h3
    exact (tendsto_nhds_unique h3 tendsto_const_nhds)
  · have h1 : Tendsto (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).re) atTop
        (𝓝 ((∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y).re)) :=
      (Complex.continuous_re.tendsto _).comp ht
    exact ge_of_tendsto' h1 fun j => (hk j a).2

theorem boundedSubseq : BoundedSubseq := by
  intro I _ θ C hC
  have := Fintype.ofFinite I
  have hb : ∀ j, θ j ∈ Metric.closedBall (0 : I → ℂ) (max C 0) := by
    intro j
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    exact fun i => (hC j i).trans (le_max_left _ _)
  obtain ⟨l, -, φ, hφ, hl⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hb
  exact ⟨φ, l, hφ, fun i => (tendsto_pi_nhds.1 hl) i⟩

lemma posSemidef_of_isPSD {X : Type} (F : Finset X) (k : X → X → ℂ) (h : IsPSD F k) :
    (Matrix.of fun x y : F => conj (k x y)).PosSemidef := by
  classical
  rw [← Matrix.isPositive_toEuclideanLin_iff, LinearMap.isPositive_iff_complex]
  intro v
  have hv : inner ℂ ((Matrix.of fun x y : F => conj (k x y)).toEuclideanLin v) v =
      ∑ x ∈ F, ∑ y ∈ F, (fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0) x *
        conj ((fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0) y) * k x y := by
    rw [← Finset.sum_coe_sort F]
    simp_rw [← Finset.sum_coe_sort F (fun y => _ * k _ y)]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [hv]
  obtain ⟨h1, h2⟩ := h (fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0)
  refine ⟨?_, h2⟩
  apply Complex.ext
  · simp
  · simpa using h1.symm

open scoped MatrixOrder in
lemma exists_factor {X : Type} (F : Finset X) (k : X → X → ℂ) (h : IsPSD F k) :
    ∃ S : F → F → ℂ, ∀ x y : F, k x y = ∑ j, S j x * conj (S j y) := by
  classical
  have h0 := (posSemidef_of_isPSD F k h).nonneg
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 h0
  refine ⟨fun j x => B j x, fun x y => ?_⟩
  have h1 := congrFun (congrFun hB x) y
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply] at h1
  have h2 := congrArg conj h1

  rw [Complex.conj_conj, map_sum] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem gramRealiseCut : GramRealiseCut := by
  intro X F G Gc h1 h2
  classical
  obtain ⟨S1, hS1⟩ := exists_factor F Gc h1
  obtain ⟨S2, hS2⟩ := exists_factor F _ h2
  let e : (F ⊕ F) ≃ Fin (Fintype.card (F ⊕ F)) := Fintype.equivFin _
  let u : X → EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) := fun x =>
    WithLp.toLp 2 (fun i => if hx : x ∈ F then
      Sum.elim (fun j => S1 j ⟨x, hx⟩) (fun j => S2 j ⟨x, hx⟩) (e.symm i) else 0)
  let d : Fin (Fintype.card (F ⊕ F)) → ℂ := fun i => if (e.symm i).isLeft then 1 else 0
  let T : EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) :=
    { toFun := fun v => WithLp.toLp 2 (fun i => d i * v i)
      map_add' := by
        intro v w; ext i; simp [mul_add]
      map_smul' := by
        intro c v; ext i; simp; ring }
  refine ⟨_, u, T, ?_, ?_, ?_⟩
  · intro v
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    show ‖d i * v i‖ ^ 2 ≤ ‖v i‖ ^ 2
    by_cases hi : (e.symm i).isLeft
    · simp [d, hi]
    · simp [d, hi]
  · intro x hx y hy
    rw [PiLp.inner_apply, ← e.sum_comp, Fintype.sum_sum_type]
    have h3 := hS1 ⟨x, hx⟩ ⟨y, hy⟩
    have h4 := hS2 ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Finset.univ_eq_attach] at h3 h4
    simp only [u, hx, hy, dite_true, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
      RCLike.inner_apply, Finset.univ_eq_attach]
    rw [← h3, ← h4]
    ring
  · intro x hx y hy
    rw [PiLp.inner_apply, ← e.sum_comp, Fintype.sum_sum_type]
    have h3 := hS1 ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Finset.univ_eq_attach] at h3
    simp [u, T, d, hx, hy]
    exact h3.symm

theorem pSDEntryBound : PSDEntryBound := by
  intro X F k M h1 h2 x hx y hy
  obtain ⟨n, u, T, hT, hG, hGc⟩ := gramRealiseCut X F M k h1 h2
  have hn : ∀ z ∈ F, ‖u z‖ ^ 2 = (M z z).re := by
    intro z hz
    rw [← hG z hz z hz]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (u z)).symm
  rw [← hGc x hx y hy, ← hn x hx, ← hn y hy, ← mul_pow]
  have h3 : ‖inner ℂ (T (u y)) (T (u x))‖ ≤ ‖u x‖ * ‖u y‖ :=
    calc ‖inner ℂ (T (u y)) (T (u x))‖ ≤ ‖T (u y)‖ * ‖T (u x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u y‖ * ‖u x‖ := mul_le_mul (hT _) (hT _) (norm_nonneg _) (norm_nonneg _)
      _ = ‖u x‖ * ‖u y‖ := mul_comm _ _
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

end Formalism.FourierDecayAlt.P.A6x2

namespace Formalism.FourierDecayAlt.P

theorem parsevalGroup_statement : Formalism.FourierDecayAlt.A6.ParsevalGroup := A6x2.parsevalGroup

theorem gramRealisation : Formalism.FourierDecayAlt.A6.GramRealiseCut := A6x2.gramRealiseCut

theorem posSemidefEntryBound : Formalism.FourierDecayAlt.A6.PSDEntryBound := A6x2.pSDEntryBound

theorem posSemidefClosed : Formalism.FourierDecayAlt.A6.PSDClosed := A6x2.pSDClosed

theorem boundedSubsequence : Formalism.FourierDecayAlt.A6.BoundedSubseq := A6x2.boundedSubseq

end Formalism.FourierDecayAlt.P
end
end
