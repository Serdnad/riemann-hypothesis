module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle001
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel ComplexConjugate

namespace GlobalTheory.CompanionTheory.JSBoundStep

theorem column_average_hermitian_positive : L0 → L3 → ColumnsMirabolic → FormHermitianPositive := by
  intro h0 h3 h3c
  unfold FormHermitianPositive ForR ForF
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hsm l k B B' hk hW hI hC
  unfold L0 ForF at h0
  unfold L3 ForR ForF at h3
  unfold ColumnsMirabolic ForF at h3c
  obtain ⟨-, hlat⟩ := h0 F μ ψ hψ
  obtain ⟨hlatM, hcv⟩ := hlat (k + 1)
  have h3' := h3 F μ ψ hψ n V ρ hsm
  obtain ⟨hcadd, hc0, hcP, -, -, -⟩ := h3c F μ ψ hψ n k hk
  obtain ⟨herm, psd, null, quasi, -⟩ := hI
  clear h0 h3 h3c hlat
  have hψinv : ∀ t : F, ψ (-t) * ψ t = 1 := fun t => by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hψconj : ∀ t : F, conj (ψ (-t)) = ψ t := by
    intro t
    have hn : ‖ψ (-t)‖ = 1 := hψ.2.2 (-t)
    calc conj (ψ (-t)) = conj (ψ (-t)) * (ψ (-t) * ψ t) := by rw [hψinv, mul_one]
      _ = (conj (ψ (-t)) * ψ (-t)) * ψ t := by ring
      _ = ψ t := by rw [Complex.conj_mul', hn]; simp
  have hinv : ∀ (x : Fin (k + 1) → F) (b : V),
      ρ (PositivityTheory.JacquetShalikaLocal.col n k x) (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) = b := by
    intro x b
    have h1 : PositivityTheory.JacquetShalikaLocal.col n k x * PositivityTheory.JacquetShalikaLocal.col n k (-x) = 1 := by
      rw [← hcadd, add_neg_cancel, hc0]
    calc ρ (PositivityTheory.JacquetShalikaLocal.col n k x) (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b)
        = (ρ (PositivityTheory.JacquetShalikaLocal.col n k x * PositivityTheory.JacquetShalikaLocal.col n k (-x))) b := by rw [map_mul]; rfl
      _ = b := by rw [h1, map_one]; rfl
  have hB : ∀ (x : Fin (k + 1) → F) (a b : V),
      B (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) a) b = B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) := by
    intro x a b
    have hq := quasi (PositivityTheory.JacquetShalikaLocal.col n k x) (hcP x).1 a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b)
    rw [hinv, (hcP x).2.2.1, map_one] at hq
    simpa using hq

  have hnegS : ∀ (M : ℕ), ∀ x ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, -x ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M := by
    intro M x hx
    simp only [PositivityTheory.JacquetShalikaLocal.lat, Set.mem_setOf_eq, Pi.neg_apply, mul_neg] at hx ⊢
    exact fun i => neg_mem (hx i)
  have hvol : ∀ M : ℕ, 0 < (Measure.pi fun _ => μ).real (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) :=
    fun M => (hlatM M).2.2.2
  have hmeas : ∀ M : ℕ, MeasurableSet (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) := fun M => (hlatM M).2.2.1
  have hvol' : ∀ M : ℕ, ∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)
      = (((Measure.pi fun _ => μ).real (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) : ℝ) : ℂ) := by
    intro M
    rw [setIntegral_const]
    simp
  have hv : ∀ M : ℕ, ∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ) ≠ 0 := by
    intro M
    rw [hvol' M]
    exact Complex.ofReal_ne_zero.mpr (hvol M).ne'
  have hmv : ∀ x : Fin (k + 1) → F,
      (↑(-1 : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).mulVec x = -x := by
    intro x
    rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hcvS : ∀ (M : ℕ) (f : (Fin (k + 1) → F) → ℂ),
      ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, f (-x) ∂(Measure.pi fun _ => μ)
        = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, f x ∂(Measure.pi fun _ => μ) := by
    intro M f
    have himg : (fun x => (↑(-1 : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).mulVec x)
        '' PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M = PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [hmv]
        exact hnegS M y hy
      · intro hx
        exact ⟨-x, hnegS M x hx, by simp only [hmv, neg_neg]⟩
    have e1 := hcv (-1) (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) (fun _ => (1 : ℂ)) (hmeas M)
    have e2 := hcv (-1) (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) f (hmeas M)
    rw [himg] at e1 e2
    simp only [hmv] at e2
    have alg : ∀ c v I J : ℂ, v ≠ 0 → v = c * v → I = c * J → J = I := by
      intro c v I J hv0 h1 h2
      have hc : c = 1 := by
        have : c * v = 1 * v := by rw [← h1, one_mul]
        exact mul_right_cancel₀ hv0 this
      rw [h2, hc, one_mul]
    exact alg _ _ _ _ (hv M) e1 e2

  have hξ : ∀ x : Fin (k + 1) → F, Pi.single (Fin.last k) (1 : F) ⬝ᵥ x = x (Fin.last k) := by
    intro x
    simp [dotProduct, Pi.single_apply]
  choose P hP1 hP2 using fun (M : ℕ) (u : V) => h3' k M (Pi.single (Fin.last k) (1 : F)) u
  simp only [hξ] at hP1 hP2
  have hSA : ∀ (M : ℕ) (a b : V), B (P M a) b = B a (P M b) := by
    intro M a b
    calc B (P M a) b = conj (B b (P M a)) := (herm b (P M a)).symm
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            conj (ψ (-x (Fin.last k)) * B b (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) a)) ∂(Measure.pi fun _ => μ) := by
          rw [hP1 M a (B b), integral_conj]
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            ψ (-(-x) (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) ∂(Measure.pi fun _ => μ) := by
          congr 1
          funext x
          rw [map_mul, hψconj, herm, hB x a b]
          simp only [Pi.neg_apply, neg_neg]
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            ψ (-x (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) b) ∂(Measure.pi fun _ => μ) :=
          hcvS M (fun x => ψ (-x (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) b))
      _ = B a (P M b) := (hP1 M b (B a)).symm
  have hE : ∀ (M : ℕ) (u v : V),
      (∀ y ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, ρ (PositivityTheory.JacquetShalikaLocal.col n k y) v = ψ (y (Fin.last k)) • v) →
      B u (P M v) = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * B u v := by
    intro M u v hv0
    rw [hP1 M v (B u), ← integral_mul_const]
    refine setIntegral_congr_fun (hmeas M) ?_
    intro x hx
    beta_reduce
    rw [hv0 x hx, map_smul, smul_eq_mul, ← mul_assoc, hψinv]
  have hL : ∀ (M : ℕ) (u : V),
      l (P M u) = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * l u := by
    intro M u
    rw [hP1 M u l, ← integral_mul_const]
    congr 1
    funext x
    rw [hW (PositivityTheory.JacquetShalikaLocal.col n k x) (hcP x).2.1.1 u, (hcP x).2.2.2, ← mul_assoc, hψinv]
  have hrel : ∀ (M : ℕ) (u : V), B (P M u) (P M u)
      = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * B u (P M u) := by
    intro M u
    rw [hSA M u (P M u), hE M u (P M u) (hP2 M u)]
  have hchar : ∀ u u' : V, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → B' u' u = B u' (P M u) := by
    intro u u'
    obtain ⟨M₀, h⟩ := hC u u'
    exact ⟨M₀, fun M hM => by rw [h M hM, hP1 M u (B u')]⟩
  refine ⟨fun u u' => ?_, fun u => ?_, fun u hu => ?_⟩
  · obtain ⟨M1, h1⟩ := hchar u u'
    obtain ⟨M2, h2⟩ := hchar u' u
    rw [h2 (max M1 M2) (le_max_right _ _), h1 (max M1 M2) (le_max_left _ _), herm, hSA]
  · obtain ⟨M1, h1⟩ := hchar u u
    rw [h1 M1 le_rfl]
    have hp := psd (P M1 u)
    rw [hrel M1 u, hvol' M1, Complex.re_ofReal_mul] at hp
    exact (mul_nonneg_iff_of_pos_left (hvol M1)).mp hp
  · obtain ⟨M1, h1⟩ := hchar u u
    rw [h1 M1 le_rfl] at hu
    have h0' : B (P M1 u) (P M1 u) = 0 := by rw [hrel, hu, mul_zero]
    have hl0 := null (P M1 u) h0'
    rw [hL M1 u] at hl0
    exact (mul_eq_zero.mp hl0).resolve_left (hv M1)

end GlobalTheory.CompanionTheory.JSBoundStep

end
end

section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.Satake

theorem norm_sq_le_of_psd {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (herm : ∀ u u', starRingEnd ℂ (B u u') = B u' u) (psd : ∀ u, 0 ≤ (B u u).re) (x y : V) :
    ‖B x y‖ ^ 2 ≤ (B x x).re * (B y y).re :=
  _root_.UpperTheory.Reformulated.B.DYhd3.main B herm psd x y

theorem tendsto_zero_of_sum_sq_le (g : ℕ → ℂ) (D : ℝ)
    (hD : ∀ T, ∑ j ∈ Finset.range T, ‖g j‖ ^ 2 ≤ D) :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  have hs : Summable fun j => ‖g j‖ ^ 2 :=
    summable_of_sum_range_le (fun _ => sq_nonneg _) hD
  have h0 := hs.tendsto_atTop_zero
  have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
  rw [Real.sqrt_zero] at h1
  refine tendsto_zero_iff_norm_tendsto_zero.2 (h1.congr fun j => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

theorem recursion_scaled {n : ℕ} (s : ℂ) (hs : s ≠ 0) (z : Fin n → ℂ) (h : ℕ → ℂ) (j : ℕ)
    (hrec : ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) * h (j - r) = 0) :
    ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) *
        (h (j - r) / s ^ (j - r)) = 0 := by
  have key : ∀ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) *
        (h (j - r) / s ^ (j - r)) = ((-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) * h (j - r)) / s ^ j := by
    intro r hr
    have hrj : r ≤ j := by simpa [Nat.lt_succ_iff] using hr
    have e1 : (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) =
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) / s ^ r := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 hS).2]
    have e2 : s ^ j = s ^ r * s ^ (j - r) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e1, e2]
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, hrec, zero_div]

theorem bound_arith (r : ℝ) (hr : 0 < r) (m j : ℕ) (W H a b : ℝ)
    (hcs : (W * ((r ^ ((m + 1) * j))⁻¹ * H)) ^ 2 ≤ a * b) :
    W ^ 2 * (H / r ^ j) ^ 2 ≤ a * ((r ^ 2) ^ (j * m) * b) := by
  have hY : (r ^ 2) ^ (j * m) = (r ^ (j * m)) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hXY : r ^ ((m + 1) * j) = r ^ j * r ^ (j * m) := by
    rw [← pow_add]
    congr 1
    ring
  have hX : r ^ j ≠ 0 := (pow_pos hr _).ne'
  have hYn : r ^ (j * m) ≠ 0 := (pow_pos hr _).ne'
  have e : W ^ 2 * (H / r ^ j) ^ 2 = (r ^ (j * m)) ^ 2 * (W * ((r ^ ((m + 1) * j))⁻¹ * H)) ^ 2 := by
    rw [hXY]
    field_simp
  rw [e, hY]
  calc _ ≤ (r ^ (j * m)) ^ 2 * (a * b) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by ring

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem inU_zero_of_mem {g : GL (Fin n) F} (hg : g ∈ unipotent F n) : inU 0 g := by
  refine ⟨hg, fun i j hj => ?_⟩
  by_cases hij : i = j
  · subst hij
    rw [hg.2 i, Matrix.one_apply_eq]
  · have hlt : j < i := by
      have : (j : ℕ) < i := by
        have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
        omega
      exact this
    rw [hg.1 hlt, Matrix.one_apply_ne hij]

theorem antitone_single (hn : 0 < n) (j : ℕ) :
    Antitone (Pi.single (⟨0, hn⟩ : Fin n) (j : ℤ) : Fin n → ℤ) := by
  intro a b hab
  by_cases hb : b = ⟨0, hn⟩
  · have ha : a = ⟨0, hn⟩ := by
      subst hb
      exact Fin.ext (by have h : (a : ℕ) ≤ 0 := hab; show (a : ℕ) = 0; omega)
    rw [ha, hb]
  · by_cases ha : a = ⟨0, hn⟩
    · simp [ha, hb]
    · simp [ha, hb]

theorem rhoPair_single_zero (hn : 0 < n) (j : ℕ) :
    rhoPair (Pi.single (⟨0, hn⟩ : Fin n) (j : ℤ) : Fin n → ℤ) = ((n : ℤ) - 1) * j := by
  rw [rhoPair, Finset.sum_eq_single (⟨0, hn⟩ : Fin n) (fun b _ hb => by simp [hb])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

end

theorem l10 : L6 → L7 → L8 → liftZP_newton → ParameterUpperBound := by
  intro h6 h7 h8 h9
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hsm hn l B hW hU v z hH hg i
  obtain ⟨g₀, hg₀⟩ := hg
  have hlv : l v ≠ 0 := by
    intro h0
    apply hg₀
    rw [h7 F ψ hψ n V ρ v z hH l hW g₀, h0, zero_mul]
  obtain ⟨B', hI, hbd⟩ := h6 F μ ψ hψ n V ρ hsm l B hn hW hU
  obtain ⟨C, hC⟩ := hbd v hH.1
  have hn0 : 0 < n := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set s := sqrtQ F with hsdef
  have hs : s ≠ 0 := sqrtQ_ne_zero
  set r := ‖s‖ with hrdef
  have hr : 0 < r := norm_pos_iff.2 hs
  have hq : (qF F : ℝ) = r ^ 2 := by
    rw [hrdef, ← norm_pow, hsdef, sqrtQ_sq, Complex.norm_natCast]
  set w := B' v v with hwdef
  have hw : w ≠ 0 := fun h => hlv (hI.null v h)
  have hW' : Whit ρ ψ (B' v) := fun g hg u => hI.equi g (inU_zero_of_mem hg) u v
  let h : ℕ → ℂ := fun j => evalAt z (schur (Pi.single (⟨0, hn0⟩ : Fin (m + 2)) (j : ℤ)))
  let a : ℕ → GL (Fin (m + 2)) F := fun j => torusPow F (m + 2) (Pi.single ⟨0, hn0⟩ (j : ℤ))
  have hC' : ∀ T : ℕ, ∑ j ∈ Finset.range T, (qF F : ℝ) ^ (j * m) *
      (B' (ρ (a j) v) (ρ (a j) v)).re ≤ C := hC
  have hval : ∀ j, B' v (ρ (a j) v) = w * ((s ^ ((m + 1) * j))⁻¹ * h j) := by
    intro j
    rw [h7 F ψ hψ (m + 2) V ρ v z hH (B' v) hW', sphericalWhittaker_torusPow hψ.1, if_pos (antitone_single hn0 j),
      halfModulus_eq, rhoPair_single_zero]
    congr 2
    rw [_root_.zpow_neg]
    congr 1
    rw [← zpow_natCast]
    congr 1
    push_cast
    ring
  let g : ℕ → ℂ := fun j => h j / s ^ j
  have hterm : ∀ j, ‖w‖ ^ 2 * ‖g j‖ ^ 2 ≤
      w.re * ((qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re) := by
    intro j
    have hcs := norm_sq_le_of_psd B' hI.herm hI.psd v (ρ (a j) v)
    rw [hval j, norm_mul, norm_mul, norm_inv, norm_pow] at hcs
    have := bound_arith r hr m j ‖w‖ ‖h j‖ w.re _ hcs
    rw [hq]
    simpa [g, norm_div, norm_pow] using this
  have hwpos : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.2 hw) 2
  have hsum : ∀ T, ∑ j ∈ Finset.range T, ‖g j‖ ^ 2 ≤ w.re * C / ‖w‖ ^ 2 := by
    intro T
    rw [le_div_iff₀ hwpos, Finset.sum_mul]
    calc _ ≤ ∑ j ∈ Finset.range T,
          w.re * ((qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re) :=
          Finset.sum_le_sum fun j _ => by rw [mul_comm]; exact hterm j
      _ = w.re * ∑ j ∈ Finset.range T,
          (qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re := by rw [Finset.mul_sum]
      _ ≤ w.re * C := mul_le_mul_of_nonneg_left (hC' T) (hI.psd v)
  have htend := tendsto_zero_of_sum_sq_le g _ hsum
  obtain ⟨h80, h8r⟩ := h8 (m + 2) hn0 z
  have hg0 : g 0 = 1 := by
    simpa [g, h] using h80
  have hrec : ∀ j : ℕ, 1 ≤ j → ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard r, ∏ i ∈ S, (z i : ℂ) / s) * g (j - r) = 0 :=
    fun j hj => recursion_scaled s hs (fun i => (z i : ℂ)) h j (h8r j hj)
  have hfin := h9 (m + 2) (fun i => (z i : ℂ) / s) g hg0 hrec htend i
  have hsq : Real.sqrt (qF F) = r := by rw [hq, Real.sqrt_sq hr.le]
  rw [hsq]
  rw [norm_div, div_lt_one hr] at hfin
  exact hfin

end GlobalTheory.CompanionTheory.Satake
end

section

open PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

open PowerSeries Filter Topology

theorem tendsto_coeff_mul_one_sub (G : ℂ⟦X⟧) (b : ℂ)
    (h : Tendsto (fun j => coeff j G) atTop (𝓝 0)) :
    Tendsto (fun j => coeff j (G * (1 - C b * X))) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have e : ∀ j : ℕ, coeff (j + 1) (G * (1 - C b * X)) = coeff (j + 1) G - b * coeff j G := by
    intro j
    have : G * (1 - C b * X) = G - C b * (G * X) := by ring
    rw [this, map_sub, coeff_C_mul, coeff_succ_mul_X]
  simp only [e]
  have h1 := (tendsto_add_atTop_iff_nat 1).2 h
  simpa using h1.sub (h.const_mul b)

theorem tendsto_coeff_mul_prod (G : ℂ⟦X⟧) {ι : Type*} (s : Finset ι) (β : ι → ℂ)
    (h : Tendsto (fun j => coeff j G) atTop (𝓝 0)) :
    Tendsto (fun j => coeff j (G * ∏ k ∈ s, (1 - C (β k) * X))) atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have : G * ((1 - C (β a) * X) * ∏ k ∈ s, (1 - C (β k) * X)) =
        (G * ∏ k ∈ s, (1 - C (β k) * X)) * (1 - C (β a) * X) := by ring
    rw [this]
    exact tendsto_coeff_mul_one_sub _ _ ih

theorem coeff_eq_pow_of_mul_one_sub (H : ℂ⟦X⟧) (b : ℂ) (h : H * (1 - C b * X) = 1) (j : ℕ) :
    coeff j H = b ^ j := by
  have e : H = 1 + C b * (H * X) := by
    calc H = H * (1 - C b * X) + C b * (H * X) := by ring
      _ = 1 + C b * (H * X) := by rw [h]
  induction j with
  | zero =>
    rw [e]; simp
  | succ j ih =>
    rw [e, map_add (f := _), coeff_C_mul, coeff_succ_mul_X, ih, pow_succ]
    simp [coeff_one, mul_comm]

theorem coeff_prod_one_sub {n : ℕ} (β : Fin n → ℂ) (r : ℕ) :
    coeff r (∏ i, (1 - C (β i) * X) : ℂ⟦X⟧) =
      (-1) ^ r * ∑ S ∈ Finset.powersetCard r Finset.univ, ∏ i ∈ S, β i := by
  classical
  have e : ∀ t : Finset (Fin n), ∏ i ∈ t, (-(C (β i) * X) : ℂ⟦X⟧) =
      C ((-1) ^ t.card * ∏ i ∈ t, β i) * X ^ t.card := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      simp only [map_mul, map_pow, map_neg, map_one]
      ring
  have e2 : (∏ i, (1 - C (β i) * X) : ℂ⟦X⟧) = ∏ i, (1 + -(C (β i) * X)) := by
    simp only [sub_eq_add_neg]

  rw [e2, Finset.prod_one_add, map_sum, Finset.powersetCard_eq_filter, Finset.sum_filter,
  Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [e, coeff_C_mul, coeff_X_pow]
  by_cases h : r = t.card
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp

theorem mk_mul_prod_eq_one {n : ℕ} (β : Fin n → ℂ) (g : ℕ → ℂ) (h0 : g 0 = 1)
    (hrec : ∀ j : ℕ, 1 ≤ j → ∑ r ∈ Finset.range (j + 1),
      ((-1) ^ r * ∑ S ∈ Finset.powersetCard r Finset.univ, ∏ i ∈ S, β i) * g (j - r) = 0) :
    (PowerSeries.mk g : ℂ⟦X⟧) * ∏ i, (1 - C (β i) * X) = 1 := by
  ext j
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_sub, coeff_mk]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [h0, coeff_one]
  · rw [hrec j hj, coeff_one, if_neg (by omega)]

end GlobalTheory.CompanionTheory.SatakeBound

theorem GlobalTheory.CompanionTheory.SatakeBound.norm_lt_one : liftZP_newton := by
  intro n β g h0 hrec hg i
  classical
  have hG := GlobalTheory.CompanionTheory.SatakeBound.mk_mul_prod_eq_one β g h0 hrec
  have hc : Filter.Tendsto (fun j => PowerSeries.coeff j (PowerSeries.mk g : PowerSeries ℂ))
      Filter.atTop (nhds 0) := by
    simpa [PowerSeries.coeff_mk] using hg
  have hH := GlobalTheory.CompanionTheory.SatakeBound.tendsto_coeff_mul_prod _ (Finset.univ.erase i) β hc
  have hone : ((PowerSeries.mk g : PowerSeries ℂ) *
      ∏ k ∈ Finset.univ.erase i, (1 - PowerSeries.C (β k) * PowerSeries.X)) *
      (1 - PowerSeries.C (β i) * PowerSeries.X) = 1 := by
    have hs := Finset.mul_prod_erase Finset.univ
      (fun k => (1 - PowerSeries.C (β k) * PowerSeries.X : PowerSeries ℂ)) (Finset.mem_univ i)
    calc _ = (PowerSeries.mk g : PowerSeries ℂ) * ((1 - PowerSeries.C (β i) * PowerSeries.X) *
          ∏ k ∈ Finset.univ.erase i, (1 - PowerSeries.C (β k) * PowerSeries.X)) := by ring
      _ = 1 := by rw [hs, hG]
  have hp := GlobalTheory.CompanionTheory.SatakeBound.coeff_eq_pow_of_mul_one_sub _ _ hone
  simp only [hp] at hH
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 hH
end
