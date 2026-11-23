module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle022
public import GroundTheory.HeightsAndTheta.Theta.SplitLinear.RankMinors
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle025
public import Mathlib.RingTheory.Derivation.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Analytic.Polynomial
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem zeroSetIn_subset_closure_diff (hvan : VanishNearPoint.Statement) {σ : Type} [Fintype σ]
    (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (hI : I.IsPrime) (hh : h ∉ I) :
    zeroSetIn I ⊆ closure (zeroSetIn I \ {z | eval z h = 0}) := by
  intro z hz
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  set e := Fintype.equivFin σ with he
  set J : Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ) := I.comap (rename e.symm) with hJ
  have hre : ∀ q : MvPolynomial (Fin (Fintype.card σ)) ℂ, rename e (rename e.symm q) = q := by
    intro q
    rw [rename_rename, show (⇑e ∘ ⇑e.symm) = id from funext e.apply_symm_apply, rename_id_apply]
  have hre' : ∀ p : MvPolynomial σ ℂ, rename e.symm (rename e p) = p := by
    intro p
    rw [rename_rename, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply, rename_id_apply]
  have hJp : J.IsPrime := Ideal.comap_isPrime _ _
  have hmemJ : ∀ y : Fin (Fintype.card σ) → ℂ, y ∘ e ∈ zeroSetIn I → y ∈ zeroLocus J := by
    intro y hy q hq
    rw [← hre q, eval_rename]
    exact hy _ hq
  have hJZ : ∀ y : Fin (Fintype.card σ) → ℂ, y ∈ zeroLocus J → y ∘ e ∈ zeroSetIn I := by
    intro y hy p hp
    have := hy (rename e p) (by rw [hJ, Ideal.mem_comap, hre']; exact hp)
    rwa [eval_rename] at this
  have hx : z ∘ e.symm ∈ zeroLocus J := hmemJ _ (by
    rw [Function.comp_assoc, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply]
    exact hz)
  have hcont : Continuous fun y : Fin (Fintype.card σ) → ℂ => y ∘ e :=
    continuous_pi fun i => continuous_apply _
  have hlim : Filter.Tendsto (fun y : Fin (Fintype.card σ) → ℂ => y ∘ e) (𝓝 (z ∘ e.symm)) (𝓝 z) := by
    have := hcont.tendsto (z ∘ e.symm)
    rwa [Function.comp_assoc, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply,
      Function.comp_id] at this
  have hev : ∀ᶠ y in 𝓝 (z ∘ e.symm), y ∈ zeroLocus J → eval y (rename e h) = 0 := by
    filter_upwards [hlim ht] with y hyt hyJ
    rw [eval_rename]
    by_contra hne'
    exact hne ⟨y ∘ e, hyt, hJZ y hyJ, hne'⟩
  have hmem := hvan _ J (rename e h) _ hJp hx hev
  apply hh
  rw [hJ, Ideal.mem_comap, hre'] at hmem
  exact hmem

theorem NormalLocallyIrreducible.proof (hvan : VanishNearPoint.Statement)
    (hcon : NormalComplementConnected.Statement) : NormalLocallyIrreducible.Statement := by
  intro σ _ I h w hI hnorm hh hw U hU
  obtain ⟨B, hBo, hwB, hBU, hpre⟩ := hcon σ I h w hI hnorm hh hw U hU
  refine ⟨B, hBo, hwB, hBU, hpre, ?_⟩
  rintro z ⟨hzZ, hzB⟩
  have h1 : z ∈ B ∩ closure (zeroSetIn I \ {z | eval z h = 0}) :=
    ⟨hzB, zeroSetIn_subset_closure_diff hvan I h hI hh hzZ⟩
  refine closure_mono ?_ (hBo.inter_closure h1)
  rintro y ⟨hyB, hyZ, hyh⟩
  exact ⟨⟨hyZ, hyB⟩, hyh⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem IsRegularPointOf.exists_ball_chart {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {z : σ → ℂ}
    (hz : IsRegularPointOf Y z) {W : Set (σ → ℂ)} (hW : W ∈ 𝓝 z) :
    ∃ (d : ℕ) (V : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧ IsOpen B ∧ IsPreconnected B ∧ AnalyticOnNhd ℂ g B ∧
        Y ∩ V = g '' B := by
  obtain ⟨hzY, d, A, O, V, g, hO, hV, hzV, hg, hAg, hYV⟩ := hz
  have hzO : z ∈ g '' O := by rw [← hYV]; exact ⟨hzY, hzV⟩
  obtain ⟨y₀, hy₀O, rfl⟩ := hzO
  have hN : interior W ∩ V ∈ 𝓝 (g y₀) := inter_mem (interior_mem_nhds.2 hW) (hV.mem_nhds hzV)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (hO.mem_nhds hy₀O) ((hg y₀ hy₀O).continuousAt.preimage_mem_nhds hN))
  refine ⟨d, V ∩ interior W ∩ A ⁻¹' Metric.ball y₀ r, Metric.ball y₀ r, g,
    (hV.inter isOpen_interior).inter (Metric.isOpen_ball.preimage A.continuous),
    ⟨⟨hzV, mem_interior_iff_mem_nhds.2 hW⟩, ?_⟩, fun x hx => interior_subset hx.1.2,
    Metric.isOpen_ball, (convex_ball y₀ r).isPreconnected, fun y hy => hg y (hball hy).1, ?_⟩
  · show A (g y₀) ∈ Metric.ball y₀ r
    rw [hAg y₀ hy₀O]
    exact Metric.mem_ball_self hr
  · ext x
    constructor
    · rintro ⟨hxY, ⟨hxV, -⟩, hxB⟩
      have hx : x ∈ g '' O := by rw [← hYV]; exact ⟨hxY, hxV⟩
      obtain ⟨y, hyO, rfl⟩ := hx
      have hyB : A (g y) ∈ Metric.ball y₀ r := hxB
      rw [hAg y hyO] at hyB
      exact ⟨y, hyB, rfl⟩
    · rintro ⟨y, hyB, rfl⟩
      have hyO : y ∈ O := (hball hyB).1
      have hyN : g y ∈ interior W ∩ V := (hball hyB).2
      have hgy : g y ∈ Y ∩ V := by rw [hYV]; exact ⟨y, hyO, rfl⟩
      refine ⟨hgy.1, ⟨hyN.2, hyN.1⟩, ?_⟩
      show A (g y) ∈ Metric.ball y₀ r
      rw [hAg y hyO]
      exact hyB

theorem eq_zero_on_chart_of_eventually_eq_zero {σ : Type} [Fintype σ] {Y V : Set (σ → ℂ)} {d : ℕ}
    {B : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → σ → ℂ} (hBo : IsOpen B) (hBc : IsPreconnected B)
    (hg : AnalyticOnNhd ℂ g B) (hYV : Y ∩ V = g '' B) (F : (σ → ℂ) → ℂ) (hF : AnalyticOnNhd ℂ F V)
    (h0 : ∃ y ∈ Y ∩ V, ∀ᶠ u in 𝓝 y, u ∈ Y → F u = 0) : ∀ u ∈ Y ∩ V, F u = 0 := by
  obtain ⟨y, hy, hyF⟩ := h0
  have hgB : ∀ t ∈ B, g t ∈ Y ∩ V := fun t ht => by rw [hYV]; exact ⟨t, ht, rfl⟩
  have hy' : y ∈ g '' B := by rw [← hYV]; exact hy
  obtain ⟨t₀, ht₀, rfl⟩ := hy'
  have hFg : AnalyticOnNhd ℂ (F ∘ g) B := fun t ht => (hF (g t) (hgB t ht).2).comp (hg t ht)
  have hev : F ∘ g =ᶠ[𝓝 t₀] 0 := by
    filter_upwards [(hg t₀ ht₀).continuousAt.tendsto.eventually hyF, hBo.mem_nhds ht₀] with t ht htB
    exact ht (hgB t htB).1
  have hzero := hFg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc ht₀ hev
  intro u hu
  have hu' : u ∈ g '' B := by rw [← hYV]; exact hu
  obtain ⟨t, ht, rfl⟩ := hu'
  exact hzero ht

theorem RegularLocusIdentity.proof (hreg : RegularOffHypersurface.Statement) :
    RegularLocusIdentity.Statement := by
  intro σ _ I hI
  obtain ⟨h, hhI, hh⟩ := hreg σ I hI
  refine ⟨h, hhI, fun z hz hhz W hW => ?_⟩
  obtain ⟨d, V, B, g, hVo, hzV, hVW, hBo, hBc, hg, hYV⟩ := (hh z hz hhz).exists_ball_chart hW
  exact ⟨V, hVo, hzV, hVW, fun F hF h0 => eq_zero_on_chart_of_eventually_eq_zero hBo hBc hg hYV F hF h0⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjectionUnramifiedGeneric

theorem pderiv_inr_rename_inl {α β : Type} (b : β) (a : MvPolynomial α ℂ) :
    pderiv (Sum.inr b) (rename (Sum.inl : α → α ⊕ β) a) = 0 := by
  classical
  induction a using MvPolynomial.induction_on with
  | C c => simp
  | add p p' hp hp' => simp [hp, hp']
  | mul_X p i hp => simp [pderiv_mul, hp, pderiv_X, Pi.single_apply]

theorem proof : ProjectionUnramifiedGeneric.Statement := by
  classical
  intro α β _ _ Q r q t hQ hint hqQ htQ hgen
  let L := FractionRing (MvPolynomial (α ⊕ β) ℂ ⧸ Q)
  let φ : MvPolynomial (α ⊕ β) ℂ →+* L := (algebraMap (MvPolynomial (α ⊕ β) ℂ ⧸ Q) L).comp (Ideal.Quotient.mk Q)
  have hφ : ∀ p, φ p = 0 ↔ p ∈ Q := by
    intro p
    have hinj := IsFractionRing.injective (MvPolynomial (α ⊕ β) ℂ ⧸ Q) L
    simp only [φ, RingHom.comp_apply]
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_zero (algebraMap (MvPolynomial (α ⊕ β) ℂ ⧸ Q) L)]
    exact hinj.eq_iff
  let ι : MvPolynomial α ℂ →+* MvPolynomial (α ⊕ β) ℂ := (rename Sum.inl : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial (α ⊕ β) ℂ).toRingHom

  let D : (β → L) → MvPolynomial (α ⊕ β) ℂ → L := fun c p => ∑ b, φ (pderiv (Sum.inr b) p) * c b
  have hDadd : ∀ c p p', D c (p + p') = D c p + D c p' := by
    intro c p p'
    simp only [D, map_add (f := _), add_mul, Finset.sum_add_distrib]
  have hDmul : ∀ c p p', D c (p * p') = φ p * D c p' + φ p' * D c p := by
    intro c p p'
    simp only [D]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [pderiv_mul]
    simp only [map_add (f := _), map_mul]
    ring
  have hDsum : ∀ c (f : Fin r → MvPolynomial (α ⊕ β) ℂ), D c (∑ j, f j) = ∑ j, D c (f j) := by
    intro c f

    simp only [D, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hDX : ∀ c b, D c (X (Sum.inr b)) = c b := by
    intro c b
    simp [D, pderiv_X, Pi.single_apply]
  have hDι : ∀ c a, D c (ι a) = 0 := by
    intro c a
    simp [D, ι, pderiv_inr_rename_inl]
  have hDpoly : ∀ c b (G : Polynomial (MvPolynomial α ℂ)),
      D c (G.eval₂ ι (X (Sum.inr b))) =
        φ ((Polynomial.derivative G).eval₂ ι (X (Sum.inr b))) * c b := by
    intro c b G
    induction G using Polynomial.induction_on with
    | C a => simp [hDι]
    | add f g hf hg => simp only [Polynomial.eval₂_add, hDadd, hf, hg, Polynomial.derivative_add,
        map_add, add_mul]
    | monomial n a h =>
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial (MvPolynomial α ℂ)) =
          Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by ring
      rw [e, Polynomial.eval₂_mul, hDmul, h, Polynomial.eval₂_X, hDX]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.eval₂_add,
        Polynomial.eval₂_mul, Polynomial.eval₂_one, Polynomial.eval₂_X, map_add, map_mul, mul_one]
      ring

  have hker : ∀ c : β → L, (∀ j, D c (q j) = 0) → c = 0 := by
    intro c hc
    have hDQ : ∀ p ∈ Q, D c p = 0 := by
      intro p hp
      obtain ⟨i, hi⟩ := hgen p hp
      obtain ⟨g, hg⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hi
      have h1 : D c (t ^ i * p) = 0 := by
        rw [← hg, hDsum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hDmul, hc j, (hφ _).2 (hqQ j)]
        ring
      rw [hDmul, (hφ p).2 hp, zero_mul, add_zero] at h1
      have ht : φ t ≠ 0 := fun h => htQ ((hφ t).1 h)
      rw [map_pow] at h1
      exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ ht)
    funext b
    obtain ⟨F, hFm, hF⟩ := hint b
    set y : L := φ (X (Sum.inr b))
    set Fb : Polynomial L := F.map (φ.comp ι)
    have hFb0 : Fb ≠ 0 := (hFm.map _).ne_zero
    have hev : ∀ G : Polynomial (MvPolynomial α ℂ),
        φ (G.eval₂ ι (X (Sum.inr b))) = (G.map (φ.comp ι)).eval y := by
      intro G
      rw [Polynomial.eval_map, Polynomial.hom_eval₂]
    have hroot : Fb.IsRoot y := by
      show Fb.eval y = 0
      rw [← hev]
      exact (hφ _).2 hF
    set k := Polynomial.rootMultiplicity y Fb
    have hk : 0 < k := (Polynomial.rootMultiplicity_pos hFb0).2 hroot
    set G := Polynomial.derivative^[k - 1] F
    have hG : G.eval₂ ι (X (Sum.inr b)) ∈ Q := by
      rw [← hφ, hev, ← Polynomial.iterate_derivative_map]
      exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (Nat.sub_lt hk one_pos)
    have hG' : φ ((Polynomial.derivative G).eval₂ ι (X (Sum.inr b))) ≠ 0 := by
      have e : Polynomial.derivative G = Polynomial.derivative^[k] F := by
        rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk).symm, Function.iterate_succ_apply']
      rw [e, hev, ← Polynomial.iterate_derivative_map, Polynomial.eval_iterate_derivative_rootMultiplicity]
      have : CharZero L := charZero_of_injective_ringHom (φ.comp MvPolynomial.C).injective
      rw [nsmul_eq_mul]
      exact mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
        (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero y hFb0)
    have h0 := hDQ _ hG
    rw [hDpoly] at h0
    exact (mul_eq_zero.1 h0).resolve_left hG'

  let M : Matrix (Fin r) β L := Matrix.of fun j b => φ (pderiv (Sum.inr b) (q j))
  have hMinj : Function.Injective M.mulVecLin := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    apply hker c
    intro j
    have := congrFun hc j
    simpa [M, Matrix.mulVec, dotProduct, D] using this
  have hrank : M.rank = Fintype.card β := by
    rw [← Matrix.finrank_range_mulVecLin, LinearMap.finrank_range_of_inj hMinj, Module.finrank_fintype_fun_eq_card]
  obtain ⟨I, J, hIJ⟩ := GroundTheory.Heights₂.Theta.SplitLinear.exists_minor_ne_zero M hrank.ge
  have hJinj : Function.Injective J := by
    intro x x' hxx'
    by_contra hne
    exact hIJ (Matrix.det_zero_of_column_eq hne fun p => by simp [M, hxx'])
  have hJbij : Function.Bijective J :=
    (Fintype.bijective_iff_injective_and_card J).2 ⟨hJinj, by simp⟩
  let e := Equiv.ofBijective J hJbij
  let μ : MvPolynomial (α ⊕ β) ℂ := (Matrix.of fun p p' => pderiv (Sum.inr (J p')) (q (I p))).det
  refine ⟨μ, ?_, ?_⟩
  · intro hμ
    apply hIJ
    rw [← (hφ μ).2 hμ, RingHom.map_det]
    congr 1
  · intro w _ hw v hvX hv
    have hdet : (Matrix.of fun p p' => eval w (pderiv (Sum.inr (J p')) (q (I p)))).det ≠ 0 := by
      rw [RingHom.map_det] at hw
      convert hw using 2
      ext p p'
      simp [RingHom.mapMatrix_apply]
    have hsub : Matrix.mulVec (Matrix.of fun p p' => eval w (pderiv (Sum.inr (J p')) (q (I p))))
        (fun p => v (Sum.inr (J p))) = 0 := by
      funext p
      have h1 := hv (I p)
      rw [Fintype.sum_sum_type] at h1
      simp only [hvX, mul_zero, Finset.sum_const_zero, zero_add] at h1
      rw [← Equiv.sum_comp e] at h1
      simpa [Matrix.mulVec, dotProduct, e] using h1
    have hz := Matrix.eq_zero_of_mulVec_eq_zero hdet hsub
    funext s
    cases s with
    | inl a => exact hvX a
    | inr b =>
      have h1 : v (Sum.inr (J (e.symm b))) = 0 := congrFun hz (e.symm b)
      have h2 : J (e.symm b) = b := e.apply_symm_apply b
      rwa [h2] at h1

end ProjectionUnramifiedGeneric

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace NormalCurveRegularPoint

theorem fderiv_eval_single {σ : Type} [Fintype σ] [DecidableEq σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) (i : σ) :
    fderiv ℂ (fun x : σ → ℂ => eval x g) z (Pi.single i 1) = eval z (pderiv i g) := by
  induction g using MvPolynomial.induction_on generalizing z with
  | C a => simp
  | add p q hp hq =>
    have hp' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) p z trivial).differentiableAt
    have hq' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) q z trivial).differentiableAt
    simp only [map_add (f := _)]
    rw [fderiv_fun_add hp' hq']
    simp [hp, hq]
  | mul_X p j hp =>
    have hp' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) p z trivial).differentiableAt
    have hX : DifferentiableAt ℂ (fun x : σ → ℂ => x j) z := differentiableAt_apply j z
    simp only [eval_mul, eval_X]
    rw [fderiv_fun_mul hp' hX]
    simp [hp, Derivation.leibniz, pderiv_X, Pi.single_apply, fderiv_apply, mul_comm]
    split_ifs <;> simp

end NormalCurveRegularPoint

theorem NormalCurveRegularPoint.proof (hJ : NormalCurveJacobian.Statement) : NormalCurveRegularPoint.Statement := by
  classical
  intro σ _ I w hI hnorm hdim hw
  obtain ⟨k, f, D, hk, hfI, hlin, hD, hgen⟩ := hJ σ I w hI hnorm hdim hw
  set W : Set (σ → ℂ) := {z | eval z D ≠ 0}
  have hWo : IsOpen W := isOpen_ne_fun (continuous_eval D) continuous_const
  have hder : ∀ j, (fun i : σ => fderiv ℂ (fun z : σ → ℂ => eval z (f j)) w (Pi.single i 1)) =
      fun i => eval w (pderiv i (f j)) := fun j => funext fun i =>
    NormalCurveRegularPoint.fderiv_eval_single (f j) w i
  let Φ : ((σ → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] (σ → ℂ) :=
    { toFun := fun L i => L (Pi.single i 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hlin' : LinearIndependent ℂ (fun j => fderiv ℂ (fun z : σ → ℂ => eval z (f j)) w) := by
    refine LinearIndependent.of_comp Φ ?_
    convert hlin using 1
    funext j
    exact hder j
  obtain ⟨d, A, O, V, g, hd, hO, hV, hwV, hVW, hg, hAg, hset⟩ :=
    IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.proof σ (Fin k) (fun j z => eval z (f j)) w W
      (fun j => AnalyticOnNhd.eval_mvPolynomial (f j) w trivial) (fun j => hw _ (hfI j)) hlin'
      (hWo.mem_nhds hD)
  simp only [Fintype.card_fin] at hd
  obtain rfl : d = 1 := by omega
  refine ⟨A, O, V, g, hO, hV, hwV, hg, hAg, ?_⟩
  rw [← hset]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, hzV⟩
    exact ⟨hzV, fun j => hz _ (hfI j)⟩
  · rintro ⟨hzV, hzf⟩
    refine ⟨fun q hq => ?_, hzV⟩
    have hspan : Ideal.span (Set.range f) ≤ RingHom.ker (eval z) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hzf j
    have h0 : eval z (D * q) = 0 := hspan (hgen q hq)
    rw [eval_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hVW hzV)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem DerivationMinorOfDetection.polyOriginIdeal_isPrime : polyOriginIdeal.IsPrime :=
  polyOriginIdeal_isMaximal.isPrime

attribute [local instance] DerivationMinorOfDetection.polyOriginIdeal_isPrime

def DerivationMinorOfDetection.Statement : Prop :=
  ∀ (T : Type) [CommRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (f : Fin h → T), (∀ i, f i ∈ P) →
    (∀ a : Fin h → Localization.AtPrime P,
      ∑ i, a i * algebraMap T (Localization.AtPrime P) (f i) ∈ maximalIdeal (Localization.AtPrime P) ^ 2 →
        ∀ i, a i ∈ maximalIdeal (Localization.AtPrime P)) →
    (∀ g ∈ P, (∀ D : Derivation ℤ T T, D g ∈ P) →
      algebraMap T (Localization.AtPrime P) g ∈ maximalIdeal (Localization.AtPrime P) ^ 2) →
    ∃ D : Fin h → Derivation ℤ T T, (Matrix.of fun i j => D j (f i)).det ∉ P

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreNormalOfRegularDepth.Statement : Prop :=
  ∀ (A : Type) [CommRing A], IsNoetherianRing A → SerreR A 1 → SerreS A 2 → NormalRing A

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
