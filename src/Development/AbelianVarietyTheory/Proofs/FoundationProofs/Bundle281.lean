module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HomDual

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rw [← h, ← h, star_star]

theorem pairing_mem (D : D7) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L)
    {u x : Fin N → D.host.E} (hu : u ∈ L) (hx : x ∈ L) :
    ∃ c : 𝓞 D.host.E, (c : D.host.E) = ∑ b, D.host.conj (u b) * x b := by
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  obtain ⟨c, hc⟩ := (hL.2.2 x).1 hx u hu
  refine ⟨c, hc.trans ?_⟩
  simp only [stdH, h]

theorem exists_resolution (D : D7) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hL : SD D L) : ∃ (m : ℕ) (v w : Fin m → Fin N → D.host.E), (∀ i, v i ∈ L) ∧ (∀ i, w i ∈ L) ∧
      ∀ (u : Fin N → D.host.E) (a : Fin N),
        u a = ∑ i, (∑ b, u b * D.host.conj (w i b)) * v i a := by
  letI := D.host.cmStar
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h' : ∀ x : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x := h
  have hh : ∀ x y : Fin N → D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.herm 1 y x = stdH D.host.E N x y := by
    intro x y
    rw [GlobalTheory.DualFamily.herm_one_eq]
    simp only [stdH, h, h', mul_comm]
  have hr : ∀ z : D.host.E, z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ z :=
    fun z => ⟨fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  obtain ⟨-, m, v, w, hv, hw, he⟩ := GlobalTheory.exists_dual_family L hL.1
    (fun x hx y hy => by rw [hh, ← hr]; exact (hL.2.2 x).1 hx y hy)
    (fun x hx => (hL.2.2 x).2 fun y hy => by rw [hr, ← hh]; exact hx y hy)
  refine ⟨m, v, w, hv, hw, fun u a => ?_⟩
  have := congrFun (he u) a
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.DualFamily.herm_one_eq, h']
    using this

theorem rank_one_mem (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) {c : D.host.E}
    (hc : c ∈ D.host.AA0) {u : Fin N → D.host.E} (hu : u ∈ L) {v : Fin N' → D.host.E}
    (hv : v ∈ L') :
    c • (Matrix.of fun a b => v a * D.host.conj (u b)) ∈ YYl D L L' := by
  refine Submodule.subset_span ⟨c, hc, _, Submodule.subset_span fun x hx => ?_, rfl⟩
  obtain ⟨e, he⟩ := pairing_mem D hL hu hx
  have : (Matrix.of fun a b => v a * D.host.conj (u b)).mulVec x = e • v := by
    funext a
    change ∑ b, v a * D.host.conj (u b) * x b = (e : D.host.E) * v a
    rw [he, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  exact L'.smul_mem e hv

theorem exists_dual_family_hom : ∀ (D : D7), (∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∃ (r : ℕ) (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i, y i ∈ YYl D L L') ∧ (∀ i, y' i ∈ YYl D L L') ∧ ∀ x : Matrix (Fin N') (Fin N) D.host.E, x = ∑ i, hYY D x (y' i) • y i := by
  rintro D ⟨r, a, a', ha, ha', ht⟩ N N' L L' hL hL'
  obtain ⟨m, u, u', hu, hu', eu⟩ := exists_resolution D hL
  obtain ⟨m', v, v', hv, hv', ev⟩ := exists_resolution D hL'
  let Y : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E :=
    fun p => a p.2.2 • Matrix.of fun s t => v p.1 s * D.host.conj (u p.2.1 t)
  let Y' : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E :=
    fun p => a' p.2.2 • Matrix.of fun s t => v' p.1 s * D.host.conj (u' p.2.1 t)
  let e := (Fintype.equivFin (Fin m' × Fin m × Fin r)).symm
  refine ⟨_, Y ∘ e, Y' ∘ e, fun i => rank_one_mem D hL (ha _) (hu _) (hv _),
    fun i => rank_one_mem D hL (ha' _) (hu' _) (hv' _), fun x => ?_⟩
  refine Eq.trans ?_ (e.sum_comp fun p => hYY D x (Y' p) • Y p).symm
  refine Matrix.ext fun s t => ?_
  have eu' : ∀ (z : Fin N → D.host.E) (t : Fin N),
      z t = ∑ i, (∑ b, z b * u' i b) * D.host.conj (u i t) := by
    intro z t
    have := congrArg D.host.conj (eu (fun b => D.host.conj (z b)) t)

    simpa only [map_sum, map_mul, conj_conj] using this
  have hT : ∀ j i k, hYY D x (Y' (j, i, k)) = Algebra.trace D.host.K D.host.E
      ((∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b) * D.host.conj (a' k)) := by
    intro j i k
    unfold hYY
    congr 1
    simp only [Y', Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul, conj_conj,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Matrix.sum_apply, Fintype.sum_prod_type, ev (fun c => x c t) s]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type, eu' (fun b => ∑ c, x c b * D.host.conj (v' j c)) t, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ht (∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b), Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hT]
  simp only [Y, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, smul_mul_assoc]
  congr 1
  ring

end GlobalTheory.HomDual
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.TraceInt

theorem pair_integral {E : Type} [Field E] [NumberField E] [StarRing E] {N N' : ℕ}
    {L : Submodule (𝓞 E) (Fin N → E)} {L' : Submodule (𝓞 E) (Fin N' → E)}
    (hL : IsSDLat E N L) (hL' : IsSDLat E N' L') {A B : Matrix (Fin N') (Fin N) E}
    (hA : ∀ x ∈ L, A.mulVec x ∈ L') (hB : ∀ x ∈ L, B.mulVec x ∈ L') :
    IsIntegral ℤ (∑ i, ∑ j, A i j * star (B i j)) := by
  obtain ⟨hLfg, hLspan, hLdual⟩ := hL
  obtain ⟨-, -, hL'dual⟩ := hL'
  obtain ⟨m, x, φ, hx, hφ, hxφ⟩ := GlobalTheory.TauLat.exists_dual_family L
    { toIsLattice := Submodule.IsLattice.of_fg E hLfg, span_eq_top := hLspan }

  set ψ : Fin m → Fin N → E := fun k b => star (φ k b) with hψdef
  have hψ : ∀ k, ψ k ∈ L := by
    intro k
    rw [hLdual]
    intro y hy
    rw [GlobalTheory.TauLat.mem_range_iff]
    have h1 : ∑ i, star (y i) * ψ k i = starRingEnd E (φ k ⬝ᵥ y) := by
      rw [starRingEnd_apply, dotProduct, star_sum]
      simp [hψdef, star_mul', mul_comm]
    unfold stdH
    rw [h1]
    exact GlobalTheory.TauLat.integral_map _ (hφ k y hy)

  have key : ∀ i, ∑ j, A i j * star (B i j) = ∑ k, (A.mulVec (x k)) i * star ((B.mulVec (ψ k)) i) := by
    intro i
    have e1 : ∑ j, A i j * star (B i j) =
        ∑ a, ∑ b, A i a * star (B i b) * ∑ k, x k a * φ k b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [hxφ, mul_ite]
    rw [e1]
    simp only [Matrix.mulVec, dotProduct, hψdef, star_sum, star_mul', star_star, Finset.mul_sum,
      Finset.sum_mul]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_comm]
  refine IsIntegral.sum _ fun k _ => ?_

  have hint : IsIntegral ℤ (∑ i, star ((A.mulVec (x k)) i) * (B.mulVec (ψ k)) i) := by
    rw [← GlobalTheory.TauLat.mem_range_iff]
    exact (hL'dual _).1 (hB _ (hψ k)) _ (hA _ (hx k))
  have h2 : ∑ i, (A.mulVec (x k)) i * star ((B.mulVec (ψ k)) i) =
      starRingEnd E (∑ i, star ((A.mulVec (x k)) i) * (B.mulVec (ψ k)) i) := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, starRingEnd_apply, starRingEnd_apply, star_star, mul_comm]
  rw [h2]
  exact GlobalTheory.TauLat.integral_map _ hint

theorem mulVec_mem_of_homL (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D L L') : ∀ x ∈ L, A.mulVec x ∈ L' := by
  unfold homL at hA
  induction hA using Submodule.span_induction with
  | mem B hB => exact hB
  | zero => intro x _; simp
  | add B C _ _ hB hC =>
    intro x hx
    rw [Matrix.add_mulVec]
    exact L'.add_mem (hB x hx) (hC x hx)
  | smul c B _ hB =>
    intro x hx
    rw [Matrix.smul_mulVec]
    exact L'.smul_mem c (hB x hx)

theorem hYY_add_left (D : D7) {N N' : ℕ} (x x' y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (x + x') y = hYY D x y + hYY D x' y := by
  unfold hYY
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem hYY_add_right (D : D7) {N N' : ℕ} (x y y' : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D x (y + y') = hYY D x y + hYY D x y' := by
  unfold hYY
  simp only [Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hYY_gen (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) (hL' : SD D L')
    {a a' : D.host.E} (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (ha' : a' ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    {A B : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D L L') (hB : B ∈ homL D L L') :
    hYY D (a • A) (a' • B) ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  have hs : IsIntegral ℤ (∑ i, ∑ j, A i j * D.host.conj (B i j)) := by
    let _ := D.host.cmStar
    have h := pair_integral (E := D.host.E) hL hL' (mulVec_mem_of_homL D hA) (mulVec_mem_of_homL D hB)
    simpa only [bridge_star_holds _ D.host] using h
  have hsum : ∑ i, ∑ j, (a • A) i j * D.host.conj ((a' • B) i j) =
      a * (∑ i, ∑ j, A i j * D.host.conj (B i j)) * D.host.conj a' := by
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have has : a * (∑ i, ∑ j, A i j * D.host.conj (B i j)) ∈ D.host.AA0 := by
    have h1 : ∀ c : 𝓞 D.host.E, (c : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
      intro c
      have h := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
      rwa [Algebra.smul_def] at h
    rw [mul_comm]
    exact h1 ⟨_, hs⟩
  unfold hYY
  rw [hsum]
  exact (factMMUnimodular _ D.host _).1 has a' ha'

private theorem exists_ringOfIntegers_eq_conj (D : D7) (c : 𝓞 D.host.E) :
    ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = D.host.conj (c : D.host.E) :=
  ⟨⟨D.host.conj (c : D.host.E),
    GlobalTheory.TauLat.integral_map (D.host.conj : D.host.E →+* D.host.E) c.isIntegral_coe⟩, rfl⟩

private theorem conjO_conjO_unimodular_class_representatives (D : D7) (z : D.host.E) : D.host.conj (D.host.conj z) = z := by
  let _ := D.host.cmStar
  rw [← bridge_star_holds _ D.host z, ← bridge_star_holds _ D.host (star z), star_star]

private theorem hYY_smul_left_eq_conj_smul_right (D : D7) {N N' : ℕ} (c c' : 𝓞 D.host.E)
    (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (c • x) y = hYY D x (c' • y) := by
  unfold hYY
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
  change (c : D.host.E) * x i j * D.host.conj (y i j) =
    x i j * (D.host.conj (c' : D.host.E) * D.host.conj (y i j))
  rw [hc, conjO_conjO_unimodular_class_representatives]
  ring

private theorem hYY_smul_right_eq_conj_smul_left (D : D7) {N N' : ℕ} (c c' : 𝓞 D.host.E)
    (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D x (c • y) = hYY D (c' • x) y := by
  have hc' : (c : D.host.E) = D.host.conj (c' : D.host.E) := by rw [hc, conjO_conjO_unimodular_class_representatives]
  exact (hYY_smul_left_eq_conj_smul_right D c' c hc' x y).symm

theorem hYY_integral : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    ∀ x ∈ YYl D L L', ∀ y ∈ YYl D L L', hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  intro D N N' L L' hL hL' x hx y hy
  have hsub : ∀ (c : 𝓞 D.host.E) (a : D.host.E),
      a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) →
      (c : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro c a ha
    have h := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
    rwa [Algebra.smul_def] at h

  have hgen : ∀ y ∈ YYl D L L', ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      ∀ A ∈ homL D L L', hYY D (a • A) y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
    intro y hy
    unfold YYl at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a', ha', B, hB, rfl⟩ := hz
      intro a ha A hA
      exact hYY_gen D hL hL' ha ha' hA hB
    | zero =>
      intro a _ A _
      unfold hYY
      simp
    | add z w _ _ hz hw =>
      intro a ha A hA
      rw [hYY_add_right]
      exact Subring.add_mem _ (hz a ha A hA) (hw a ha A hA)
    | smul c z _ hz =>
      intro a ha A hA
      obtain ⟨c', hc'⟩ := exists_ringOfIntegers_eq_conj D c
      rw [hYY_smul_right_eq_conj_smul_left D c c' hc', ← smul_assoc, Algebra.smul_def]
      exact hz _ (hsub c' a ha) A hA
  unfold YYl at hx
  induction hx using Submodule.span_induction generalizing y with
  | mem z hz =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hz
    exact hgen y hy a ha A hA
  | zero =>
    unfold hYY
    simp
  | add z w _ _ hz hw =>
    rw [hYY_add_left]
    exact Subring.add_mem _ (hz y hy) (hw y hy)
  | smul c z _ hz =>
    obtain ⟨c', hc'⟩ := exists_ringOfIntegers_eq_conj D c
    rw [hYY_smul_left_eq_conj_smul_right D c c' hc']
    exact hz _ ((YYl D L L').smul_mem c' hy)

end GlobalTheory.NormSum.TraceInt
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.OrthoCoord

variable {D : D7}

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) : φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

theorem embT_injective : Function.Injective (embT D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem embT_indep (c : D.what₂.Tau → ℂ) (h : ∀ x, ∑ τ, c τ * embT D τ x = 0) (τ : D.what₂.Tau) : c τ = 0 := by
  have h1 := (linearIndependent_monoidHom D.host.E ℂ).comp
    (fun τ : D.what₂.Tau => ((embT D τ : D.host.E →+* ℂ) : D.host.E →* ℂ))
    (fun a b hab => embT_injective (RingHom.coe_monoidHom_injective hab))
  rw [Fintype.linearIndependent_iff] at h1
  refine h1 c ?_ τ
  funext x
  simpa [Finset.sum_apply] using h x

theorem coordB_embV (h : TraceMapNormalisation D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Orthonormal D b) (j k : Fin r) :
    coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if j = k then 1 else 0 := by
  have h1 := h (∑ i, ∑ i', b k i i' * D.host.conj (b j i i'))
  have h2 := hb k j
  unfold hYY at h2
  rw [h2] at h1
  have h3 : coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) =
      ∑ τ, embT D τ (∑ i, ∑ i', b k i i' * D.host.conj (b j i i')) := by

    simp only [coordB, embV, tor0, map_sum, map_mul, emb_conj]
  rw [h3, h1]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk, Ne.symm hjk]

theorem coordB_sum (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E) (j : Fin r)
    (c : Fin r → ℂ) (v : Fin r → VC D a d) :
    coordB D T b j (∑ k, c k • v k) = ∑ k, c k * coordB D T b j (v k) := by
  let L : VC D a d →ₗ[ℂ] ℂ :=
    { toFun := coordB D T b j
      map_add' := fun x y => by simp [coordB, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc] }
  change L _ = ∑ k, c k * L (v k)

  simp [map_sum, map_smul]

theorem embV_mem_span (h : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Submodule.span D.host.K (Set.range b) = ⊤)
    (A : Matrix (Fin d) (Fin a) D.host.E) :
    embV D (tor0 D cc δ) A ∈ Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) := by
  have hA : A ∈ Submodule.span D.host.K (Set.range b) := by rw [hb]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hA
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun k => D.host.φ₀ (c k : D.host.E), ?_⟩
  funext τ i j

  simp only [embV, tor0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.smul_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← h τ, ← map_mul]
  rfl

theorem span_eq_top (h : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Submodule.span D.host.K (Set.range b) = ⊤) :
    Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  let e : D.what₂.Tau → Fin d → Fin a → VC D a d := fun τ i j => Pi.single τ (Pi.single i (Pi.single j 1))
  have hz : ∀ z : VC D a d, z = ∑ τ, ∑ i, ∑ j, z τ i j • e τ i j := by
    intro z
    funext τ i j
    simp [e, Finset.sum_apply, Pi.single_apply, ite_apply]
  have he : ∀ τ i j, f (e τ i j) = 0 := by
    intro τ i j
    refine embT_indep (fun τ => f (e τ i j)) (fun x => ?_) τ
    have h1 : f (embV D (tor0 D cc δ) (Matrix.single i j x)) = 0 := hf (embV_mem_span h cc δ hb _)
    have h2 : embV D (tor0 D cc δ) (Matrix.single i j x) = ∑ τ, embT D τ x • e τ i j := by
      funext τ' i' j'
      simp only [e, embV, tor0, Matrix.single_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, ite_apply,
        smul_eq_mul]
      by_cases hi : i = i'
      · by_cases hj : j = j'
        · subst hi hj; simp
        · simp [hj, Ne.symm hj]
      · simp [hi, Ne.symm hi]
    rw [h2] at h1

    simpa [map_sum, map_smul, mul_comm] using h1
  refine LinearMap.ext fun z => ?_
  rw [hz z]

  simp [map_sum, map_smul, he]

theorem orthonormal_coord : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ i j, coordB D (tor0 D cc δ) b i (embV D (tor0 D cc δ) (b j)) = if i = j then 1 else 0) ∧ ∀ z : VC D N N', z = ∑ j, coordB D (tor0 D cc δ) b j z • embV D (tor0 D cc δ) (b j) := by
  intro D h cc δ N N' r b hb
  refine ⟨coordB_embV h.2 cc δ hb.1, fun z => ?_⟩
  have hz : z ∈ Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) := by
    rw [span_eq_top h.1 cc δ hb.2]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordB_sum]
  simp [coordB_embV h.2 cc δ hb.1]

end GlobalTheory.OrthoCoord
end
end
