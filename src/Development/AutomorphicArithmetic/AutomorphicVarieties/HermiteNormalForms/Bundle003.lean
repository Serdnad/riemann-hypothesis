module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.orbit_number_power_bound (D d N p : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (hd : N ≤ d) :
    (D ^ N * d ^ d) ^ (1 + d * N) *
      ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1)) ≤
    (2 * D * d) ^ (12 * (p + 1) * d ^ 3 * N) := by
  have hd1 : 1 ≤ d := le_trans hN hd
  set B := 2 * D * d with hBdef
  have hB2 : 2 ≤ B := by
    have : 1 ≤ D * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rw [hBdef, mul_assoc]
    omega
  have hDB : D ≤ B := by
    rw [hBdef]
    nlinarith
  have hdB : d ≤ B := by
    rw [hBdef]
    nlinarith
  have hNB : N ≤ B := le_trans hd hdB
  have hX : D ^ N * d ^ d ≤ B ^ (2 * d) := by
    have a : D ^ N ≤ B ^ d :=
      le_trans (Nat.pow_le_pow_left hDB N) (Nat.pow_le_pow_right (by omega) hd)
    have b : d ^ d ≤ B ^ d := Nat.pow_le_pow_left hdB d
    calc D ^ N * d ^ d ≤ B ^ d * B ^ d := Nat.mul_le_mul a b
      _ = B ^ (2 * d) := by ring
  have hX1 : 1 ≤ D ^ N * d ^ d :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)))
  have hNN : N ^ N ≤ B ^ d :=
    le_trans (Nat.pow_le_pow_left hNB N) (Nat.pow_le_pow_right (by omega) hd)
  have hNN1 : 1 ≤ N ^ N := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have f1 : (D ^ N * d ^ d) ^ (1 + d * N) ≤ B ^ (2 * d * (1 + d * N)) := by
    rw [pow_mul B]
    exact Nat.pow_le_pow_left hX _
  have hin : 2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1 ≤ B ^ (5 * d + 2) := by
    have hY1 : 1 ≤ N ^ N * (D ^ N * d ^ d) ^ 2 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
    have hY : N ^ N * (D ^ N * d ^ d) ^ 2 ≤ B ^ d * (B ^ (2 * d)) ^ 2 :=
      Nat.mul_le_mul hNN (Nat.pow_le_pow_left hX 2)
    have h4 : 4 ≤ B ^ 2 := by nlinarith
    calc 2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1 ≤ 4 * (N ^ N * (D ^ N * d ^ d) ^ 2) := by omega
      _ ≤ B ^ 2 * (B ^ d * (B ^ (2 * d)) ^ 2) := Nat.mul_le_mul h4 hY
      _ = B ^ (5 * d + 2) := by ring
  have hin2 : (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1 ≤ B ^ ((5 * d + 2) * d + 1) := by
    have a : (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d ≤ B ^ ((5 * d + 2) * d) := by
      rw [pow_mul B]
      exact Nat.pow_le_pow_left hin d
    have b : 1 ≤ B ^ ((5 * d + 2) * d) := Nat.one_le_pow _ _ (by omega)
    calc (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1 ≤ 2 * B ^ ((5 * d + 2) * d) := by omega
      _ ≤ B * B ^ ((5 * d + 2) * d) := Nat.mul_le_mul_right _ hB2
      _ = B ^ ((5 * d + 2) * d + 1) := by ring
  have f2 : ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1)) ≤
      B ^ (((5 * d + 2) * d + 1) * (d * N * (p + 1))) := by
    rw [pow_mul B]
    exact Nat.pow_le_pow_left hin2 _
  have hexp : 2 * d * (1 + d * N) + ((5 * d + 2) * d + 1) * (d * N * (p + 1)) ≤
      12 * (p + 1) * d ^ 3 * N := by
    have e1 : d ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d ^ 2 * N * (p + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have e2 : d ^ 2 * N ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d * (p + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have e3 : d * N * (p + 1) ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    have e4 : d ^ 2 * N * (p + 1) ≤ d ^ 3 * N * (p + 1) := by
      have : d ^ 2 * N * (p + 1) * 1 ≤ d ^ 2 * N * (p + 1) * d := Nat.mul_le_mul_left _ hd1
      nlinarith
    nlinarith
  calc (D ^ N * d ^ d) ^ (1 + d * N) *
        ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1))
      ≤ B ^ (2 * d * (1 + d * N)) * B ^ (((5 * d + 2) * d + 1) * (d * N * (p + 1))) :=
        Nat.mul_le_mul f1 f2
    _ = B ^ (2 * d * (1 + d * N) + ((5 * d + 2) * d + 1) * (d * N * (p + 1))) := by ring
    _ ≤ B ^ (12 * (p + 1) * d ^ 3 * N) := Nat.pow_le_pow_right (by omega) hexp

theorem UpperTheory.V.KT.orbnum :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (p : ℕ), 1 ≤ N →
    orbBound L N p ≤ (2 * absD L * dd L N) ^ (12 * (p + 1) * dd L N ^ 3 * N) := by
  intro L _ _ N p hN
  have hD : 1 ≤ absD L := Nat.one_le_iff_ne_zero.mpr (by
    simp only [absD, ne_eq, Int.natAbs_eq_zero]
    exact NumberField.discr_ne_zero L)
  have hd : N ≤ dd L N := by
    simp only [dd]
    have : 1 ≤ Module.finrank ℚ L := Module.finrank_pos
    nlinarith
  have := orbit_number_power_bound (absD L) (dd L N) N p hD hN hd
  simpa only [orbBound, I0, RR] using this
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem ryne_place (L : Type) [Field L] [NumberField L] (x : 𝓞 L) (hx : x ≠ 0) :
    ∃ w : InfinitePlace L, 1 ≤ w (x : L) := by
  classical
  by_contra hc
  push_neg at hc
  have hprod := InfinitePlace.prod_eq_abs_norm (x : L)
  rw [← Algebra.coe_norm_int] at hprod
  have hn : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  have h1 : (1 : ℝ) ≤ ((|((Algebra.norm ℤ x : ℤ) : ℚ)| : ℚ) : ℝ) := by
    have := Int.one_le_abs hn
    rw [← Int.cast_abs]
    exact_mod_cast this
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have hf : ∀ w : InfinitePlace L, 0 ≤ w (x : L) ^ w.mult := fun w => by positivity
  have hlt : ∀ w : InfinitePlace L, w (x : L) ^ w.mult < 1 := fun w =>
    pow_lt_one₀ (by positivity) (hc w) InfinitePlace.mult_pos.ne'
  have hle : ∏ w ∈ Finset.univ.erase w0, w (x : L) ^ w.mult ≤ 1 :=
    Finset.prod_le_one₀ (fun w _ => hf w) (fun w _ => (hlt w).le)
  have : ∏ w : InfinitePlace L, w (x : L) ^ w.mult < 1 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w0)]
    calc w0 (x : L) ^ w0.mult * ∏ w ∈ Finset.univ.erase w0, w (x : L) ^ w.mult
        ≤ w0 (x : L) ^ w0.mult * 1 := mul_le_mul_of_nonneg_left hle (hf w0)
      _ < 1 := by rw [mul_one]; exact hlt w0
  linarith

theorem UpperTheory.V.KT.ryne :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), (Ry L N).Nonempty := by
  intro L _ _ N
  refine ⟨mkHS (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ => isHermitian_one), ?_⟩
  intro y hy
  have hterm : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (funext hc)
  obtain ⟨w, hw⟩ := ryne_place L (y a) ha
  have hw' : ‖embO w (y a)‖ = w ((y a : 𝓞 L) : L) := by
    simp only [embO, RingHom.comp_apply]
    exact InfinitePlace.norm_embedding_eq w _
  simp only [q, qR, mat_mkHS, one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum, hterm, toR]
  calc (1 : ℝ) ≤ ‖embO w (y a)‖ ^ 2 := by rw [hw']; nlinarith
    _ ≤ ∑ a', ‖embO w (y a')‖ ^ 2 :=
      Finset.single_le_sum (f := fun a' => ‖embO w (y a')‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ a)
    _ ≤ ∑ w', ∑ a', ‖embO w' (y a')‖ ^ 2 :=
      Finset.single_le_sum (f := fun w' => ∑ a', ‖embO w' (y a')‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ w)
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.exbasis :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Set (Lat L N)), Spans M →
    ∃ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 ∧ ∀ a, (fun i => A i a) ∈ M := by
  intro L _ _ N M hM
  classical
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent L (toL '' M)
  have htop : (⊤ : Submodule L (Fin N → L)) ≤ Submodule.span L (Set.range ((↑) : s → Fin N → L)) := by
    rw [Subtype.range_coe, hspan]
    exact hM.ge
  let B := Module.Basis.mk hli htop
  haveI : Fintype s := @Fintype.ofFinite s (Module.Finite.finite_basis B)
  have hcard : Fintype.card s = N := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : Fin N ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ a, ∃ y ∈ M, toL y = (e a : Fin N → L) := fun a => hs (e a).2
  choose y hyM hy using hmem
  refine ⟨fun i a => y a i, ?_, fun a => hyM a⟩
  intro h0
  have hli' : LinearIndependent L (fun a => ((e a : s) : Fin N → L)) := hli.comp e e.injective
  let C : Matrix (Fin N) (Fin N) L := fun i a => ((e a : s) : Fin N → L) i
  have hC : IsUnit C := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli'
  let A : Matrix (Fin N) (Fin N) (𝓞 L) := fun i a => y a i
  have hCA : C = (algebraMap (𝓞 L) L).mapMatrix A := by
    ext i a
    simp only [C, A, RingHom.mapMatrix_apply, Matrix.map_apply, ← hy]
    rfl
  have hdet : C.det = algebraMap (𝓞 L) L A.det := by
    rw [hCA]
    exact (RingHom.map_det (algebraMap (𝓞 L) L) A).symm
  have h0' : A.det = 0 := h0
  rw [h0', map_zero] at hdet
  exact (Matrix.isUnit_iff_isUnit_det C |>.mp hC).ne_zero hdet
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem lowbd_cont (L : Type) [Field L] [NumberField L] (N : ℕ) :
    Continuous (fun p : HS L N × VR L N => qR p.1 p.2) := by
  unfold qR mat
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply]
  have hv : Continuous fun p : HS L N × VR L N => (p.1 : InfinitePlace L → Fin N → Fin N → ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : HS L N × VR L N => (p.2 : InfinitePlace L → Fin N → ℂ) := continuous_snd
  refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_star.comp ((continuous_apply i).comp ((continuous_apply w).comp hz))).mul ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp hv))).mul
    ((continuous_apply j).comp ((continuous_apply w).comp hz))

private theorem lowbd_smul {L : Type} [Field L] [NumberField L] {N : ℕ} (k : HS L N) (r : ℝ)
    (z : VR L N) : qR k (r • z) = r ^ 2 * qR k z := by
  unfold qR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.smul_apply, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, smul_eq_mul]
  ring

private theorem lowbd_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  have hne : ∃ w, z w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hz (funext hc)
  obtain ⟨w0, hw0⟩ := hne
  have hp : ∀ w, (mat h w).PosDef := hh
  unfold qR
  apply Finset.sum_pos'
  · intro w _
    by_cases hw : z w = 0
    · simp [hw]
    · exact le_of_lt (Complex.pos_iff.mp ((hp w).dotProduct_mulVec_pos hw)).1
  · exact ⟨w0, Finset.mem_univ _, (Complex.pos_iff.mp ((hp w0).dotProduct_mulVec_pos hw0)).1⟩

theorem UpperTheory.V.KT.lowbd :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), h ∈ Pos L N →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in nhds h, ∀ z : VR L N, c * ‖z‖ ^ 2 ≤ qR k z := by
  intro L _ _ N h hh
  have hK : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have hcont := lowbd_cont L N
  have hsec : Continuous fun z : VR L N => (h, z) := by fun_prop
  obtain ⟨m, hm, hmle⟩ := hK.exists_forall_le' (f := fun z => qR h z)
    (hcont.comp hsec).continuousOn (a := 0)
    (fun z hz => lowbd_pos hh (by
      intro h0
      rw [h0] at hz
      simp at hz))
  refine ⟨m / 2, by positivity, ?_⟩
  have hev : ∀ᶠ k in nhds h, ∀ z ∈ Metric.sphere (0 : VR L N) 1, m / 2 < qR k z := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hlt : m / 2 < qR h z := by linarith [hmle z hz]
    exact (hcont.tendsto (h, z)).eventually (lt_mem_nhds hlt)
  filter_upwards [hev] with k hk z
  by_cases hz : z = 0
  · subst hz
    have h0 : qR k (0 : VR L N) = 0 := by simpa using lowbd_smul k 0 (0 : VR L N)
    simp [h0]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : VR L N) 1 := by
      simp [norm_smul, hn.ne']
    have hzu : ‖z‖ • (‖z‖⁻¹ • z) = z := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hlt := hk _ hu
    calc m / 2 * ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 * qR k (‖z‖⁻¹ • z) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hlt.le (by positivity)
      _ = qR k (‖z‖ • (‖z‖⁻¹ • z)) := (lowbd_smul k ‖z‖ _).symm
      _ = qR k z := by rw [hzu]
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.cntconj :
    ∀ (L : Type) [Field L] [NumberField L] (R : ℕ),
    {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}.Finite ∧
      {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}.ncard ≤ (2 * R + 1) ^ Module.finrank ℚ L := by
  intro L _ _ R
  have hq : 2 * R + 1 ≠ 0 := by omega
  have hsep : ∀ a ∈ {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}, ∀ b ∈ {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R},
      ∀ x : 𝓞 L, a - b = (2 * R + 1) • x → a = b := by
    intro a ha b hb x hab
    by_cases hx : x = 0
    · rw [hx, smul_zero, sub_eq_zero] at hab
      exact hab
    exfalso
    have key : ∀ w : InfinitePlace L, w (x : L) < 1 := by
      intro w
      have h1 : ‖embO w (a - b)‖ ≤ 2 * R := by
        rw [map_sub]
        calc ‖embO w a - embO w b‖ ≤ ‖embO w a‖ + ‖embO w b‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add (ha w) (hb w)
          _ = 2 * R := by ring
      rw [hab, map_nsmul, nsmul_eq_mul, norm_mul, Complex.norm_natCast] at h1
      have hn : ‖embO w x‖ = w (x : L) := InfinitePlace.norm_embedding_eq w (x : L)
      rw [hn] at h1
      push_cast at h1
      by_contra hc
      push_neg at hc
      have : (2 * (R : ℝ) + 1) * 1 ≤ (2 * (R : ℝ) + 1) * w (x : L) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      linarith
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
    have := InfinitePlace.one_le_of_lt_one (w := w0) hx (fun z _ => key z)
    linarith [key w0]
  obtain ⟨hfin, hcard⟩ := cardsep (𝓞 L) (2 * R + 1) hq _ hsep
  refine ⟨hfin, ?_⟩
  rwa [RingOfIntegers.rank] at hcard
end

section

open NumberField Matrix

noncomputable section

namespace UpperTheory.V.KT

variable (L : Type) [Field L] [NumberField L] (N : ℕ)

abbrev NZ : Type := {y : Lat L N // y ≠ 0}

def qc (y : NZ L N) : HS L N →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (ev y.1)

def Psd : Set (HS L N) := {h | open ComplexOrder in ∀ w, (mat h w).PosSemidef}

variable {L N}

@[simp] theorem qc_apply (y : NZ L N) (h : HS L N) : qc L N y h = q h y.1 := rfl

theorem poly_qc : ConeExtensionAcyclic.poly (qc L N) = Ry L N := by
  ext h; exact ⟨fun H y hy => H ⟨y, hy⟩, fun H y => H y.1 y.2⟩

open ComplexOrder in
theorem smul_mem_Psd (g : Gm L N) {h : HS L N} (hh : h ∈ Psd L N) : g • h ∈ Psd L N :=
  fun w => (hh w).conjTranspose_mul_mul_same _

theorem smul_ne_zero_lat (g : Gm L N) {y : Lat L N} (hy : y ≠ 0) : g • y ≠ 0 :=
  fun e => hy (by rw [← inv_smul_smul g y, e, smul_zero])

def actL (g : Gm L N) : HS L N →L[ℝ] HS L N :=
  LinearMap.toContinuousLinearMap (pull ((g⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)))

@[simp] theorem actL_apply (g : Gm L N) (h : HS L N) : actL g h = g • h := rfl

theorem isVert_smul (g : Gm L N) {h : HS L N} (hh : ConeExtensionAcyclic.IsVert (qc L N) h) :
    ConeExtensionAcyclic.IsVert (qc L N) (g • h) := by
  refine ⟨?_, fun k hk => ?_⟩
  · have := hh.1
    rw [poly_qc] at this ⊢
    exact smul_mem_Ry g this
  · have : g⁻¹ • k = 0 := hh.2 _ fun y hy => by
      have := hk ⟨g • y.1, smul_ne_zero_lat g y.2⟩ (by simpa [q_smul] using hy)
      simpa [q_smul] using this
    rw [← smul_inv_smul g k, this, smul_zero]

variable (L N)

abbrev Vx : Type := ConeExtensionAcyclic.Vert (qc L N)

instance : MulAction (Gm L N) (Vx L N) where
  smul g v := ⟨g • v.1, isVert_smul g v.2⟩
  one_smul v := Subtype.ext (one_smul _ v.1)
  mul_smul g k v := Subtype.ext (mul_smul g k v.1)

variable {L N}

theorem Vx.smul_val (g : Gm L N) (v : Vx L N) : (g • v).1 = g • v.1 := rfl

theorem smul_mem_simp (g : Gm L N) {n : ℕ} {t : Fin n → Vx L N}
    (ht : t ∈ ConeExtensionAcyclic.simp (qc L N) (Psd L N) n) :
    (fun j => g • t j) ∈ ConeExtensionAcyclic.simp (qc L N) (Psd L N) n := by
  obtain ⟨x, hx, hj⟩ := ht
  refine ⟨x.comp (actL g⁻¹), fun k hk h0 => ?_, fun j h' hh' => ?_⟩
  · exact hx _ (smul_mem_Psd _ hk) (fun e => h0 (by
      have e' : g⁻¹ • k = 0 := e
      rw [← smul_inv_smul g k, e', smul_zero]))
  · rw [poly_qc] at hh'
    have := hj j (g⁻¹ • h') (by rw [poly_qc]; exact smul_mem_Ry _ hh')
    simpa [Vx.smul_val] using this

variable (L N)

def Sx (p : ℕ) : Type := {t : Fin (p + 1) → Vx L N // t ∈ ConeExtensionAcyclic.simp (qc L N) (Psd L N) (p + 1)}

instance (p : ℕ) : MulAction (Gm L N) (Sx L N p) where
  smul g t := ⟨fun j => g • t.1 j, smul_mem_simp g t.2⟩
  one_smul t := Subtype.ext (funext fun j => one_smul _ (t.1 j))
  mul_smul g k t := Subtype.ext (funext fun j => mul_smul g k (t.1 j))

def Sx.face (p : ℕ) (i : Fin (p + 2)) (t : Sx L N (p + 1)) : Sx L N p :=
  ⟨t.1 ∘ i.succAbove, ConeExtensionAcyclic.nerve_faceClosed _ _ _ t.1 t.2 i⟩

variable {L N}

theorem Sx.smul_val {p : ℕ} (g : Gm L N) (t : Sx L N p) (j : Fin (p + 1)) :
    (g • t).1 j = g • t.1 j := rfl

theorem Sx.face_smul (p : ℕ) (i : Fin (p + 2)) (g : Gm L N) (t : Sx L N (p + 1)) :
    Sx.face L N p i (g • t) = g • Sx.face L N p i t := rfl

def nearVx (A : Matrix (Fin N) (Fin N) (𝓞 L)) : Set (Vx L N) := {v | ColsMin A v.1}

abbrev BI (L : Type) [Field L] [NumberField L] : Type := Module.Free.ChooseBasisIndex ℤ (𝓞 L)

def intVec (c : Fin N × BI L → ℤ) : Lat L N :=
  fun a => ∑ i, c (a, i) • RingOfIntegers.basis L i

def realVec (x : Fin N × BI L → ℝ) : VR L N :=
  fun w a => ∑ i, (x (a, i) : ℂ) * embO w (RingOfIntegers.basis L i)

def gram (h : HS L N) : Matrix (Fin N × BI L) (Fin N × BI L) ℝ :=
  Matrix.of fun s t => ∑ w, (star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
    embO w (RingOfIntegers.basis L t.2)).re

end UpperTheory.V.KT
end
end
