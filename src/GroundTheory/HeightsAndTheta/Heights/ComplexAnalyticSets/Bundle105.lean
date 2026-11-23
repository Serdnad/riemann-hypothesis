module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle088
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle104
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HolomorphicZerosNotIsolated
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle101
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle080
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle078
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle103
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle079
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets
open scoped nonZeroDivisors

noncomputable section

theorem SliceMassFinite.exists_projClosure {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (hI : I.IsPrime) (hℓ : linForm ℓ - 1 ∈ I)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (W : Ideal (MvPolynomial (Fin n) ℂ)) (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ),
      IsProjPrime W ∧ IsChowForm W (e + 2) F ∧ linForm ℓ ∉ W ∧ W ⊔ Ideal.span {linForm ℓ - 1} = I := by
  obtain ⟨W, hW, hℓW, hWI, -⟩ := ChartHomogenise.proof ℂ n I ℓ hI hℓ
  have hP := hW.isPrime

  have hx : Ideal.Quotient.mk W (linForm ℓ - 1) ∈ (MvPolynomial (Fin n) ℂ ⧸ W)⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hP.ne_top ?_
    have h00 := hW.isHomog _ (Ideal.Quotient.eq_zero_iff_mem.mp h0) 0
    rw [homogeneousComponent_zero] at h00
    have hc : AddMonoidAlgebra.coeff (linForm ℓ - 1) 0 = -1 := by
      simp [linForm, coeff_sum, coeff_C_mul, coeff_X]
    rw [hc, map_neg, map_one, Ideal.neg_mem_iff] at h00
    exact (Ideal.eq_top_iff_one W).mpr h00
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx
  have eq := DoubleQuot.quotQuotEquivQuotSup W (Ideal.span {linForm ℓ - 1})
  rw [Ideal.map_span, Set.image_singleton] at eq
  rw [ringKrullDim_eq_of_ringEquiv eq, hWI, hdim] at h1

  have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : WithBot ℕ∞) := by
    have := ringKrullDim_quotient_le W
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at this

  have hdimW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    generalize hD : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = D at h1 h2
    induction D using WithBot.recBotCoe with
    | bot => simp at h1
    | coe b =>
      induction b using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : (⊤ : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h2
        exact ENat.natCast_ne_top _ (top_le_iff.mp h3)
      | coe m =>
        have hm1 : e + 1 + 1 ≤ m := by exact_mod_cast h1
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have hA' : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety W (k + 1) := ⟨hP, by rw [hD]; rfl⟩
        have h3 := IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice hA' hW.isHomog hℓW
        rw [hWI, hdim] at h3
        have hk : k ≤ e + 1 := by exact_mod_cast h3
        have hke : k + 1 = e + 1 + 1 := by omega
        rw [hke]
        rfl
  obtain ⟨F, hFW⟩ := (IndefiniteRowSideFullHecke.ComplexSets.exists_isChowForm_iff (e := e + 1) hW).mpr ⟨hP, hdimW⟩
  exact ⟨W, F, hW, hFW, hℓW, hWI⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets Metric Set

noncomputable section

namespace GoodPointBranch

theorem exists_branch {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    {u q : Fin n → ℂ} (hqu : linEval u q = 0)
    {A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)} {O : Set (Fin d → ℂ)} {V : Set (Fin n → ℂ)}
    {g : (Fin d → ℂ) → Fin n → ℂ} (hV : IsOpen V) (hqV : q ∈ V) (hg : AnalyticOnNhd ℂ g O)
    (hAg : ∀ y ∈ O, A (g y) = y) (hS : zeroSet J ∩ {x | linEval u x = 0} ∩ V = g '' O)
    {N₀ : Set (Fin n → ℂ)} (hN₀ : N₀ ∈ 𝓝 q)
    (hdouble : ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal,
      IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' →
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N₀ → w ≠ w' → linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0)
    {w : Fin n ⊕ Fin M.m → ℂ} (hwq : IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q)
    {r : ℝ} {φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ} {k : ℕ} (hr : 0 < r)
    (hφd : DifferentiableOn ℂ φ (ball 0 r)) (hφi : InjOn φ (ball 0 r)) (hφ0 : φ 0 = w)
    (hφZ : MapsTo φ (ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal))
    (hφU : ∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' ball 0 s)
    (hvan : VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k)
    (hinjD : ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
      fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0)
    {G : Set (Fin n ⊕ Fin M.m → ℂ)} (hG : G ∈ 𝓝 w) :
    ∃ γ : VarBranch J (d + 1) q,
      (∃ U ∈ 𝓝 w, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U,
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' ∈ γ.image) ∧
      (∀ x ∈ γ.image, x ∈ N₀ ∧
        ∃ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ G, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' = x) ∧
      (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ γ.slice) ∧
      VanishesToOrder (fun t => linEval u (γ.toFun t)) γ.radius k ∧
      Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) (0 : Fin (d + 1) → ℂ)) := by
  set ψ : (Fin (d + 1) → ℂ) → Fin n → ℂ := fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t) with hψdef
  have hψd : DifferentiableOn ℂ ψ (ball 0 r) :=
    differentiableOn_pi.2 fun i => differentiableOn_pi.1 hφd (Sum.inl i)
  have h0r : (0 : Fin (d + 1) → ℂ) ∈ ball 0 r := mem_ball_self hr
  have hψ : HasStrictFDerivAt ψ (fderiv ℂ ψ 0) 0 :=
    (analyticOnNhd_of_differentiableOn isOpen_ball hψd 0 h0r).hasStrictFDerivAt
  have hψ0 : ψ 0 = q := by simp only [hψdef, hφ0, hwq]
  obtain ⟨H, hHd, hH0, hF⟩ := hvan
  have hk : k ≠ 0 := by
    intro hk0
    have h : linEval u (ψ 0) = (0 : Fin (d + 1) → ℂ) 0 ^ k * H 0 := hF 0 h0r
    rw [hψ0, hqu, hk0, pow_zero, one_mul] at h
    exact hH0 0 h0r h.symm
  have hzero : ∀ t ∈ ball (0 : Fin (d + 1) → ℂ) r, linEval u (ψ t) = 0 ↔ t 0 = 0 := by
    intro t ht
    have h : linEval u (ψ t) = t 0 ^ k * H t := hF t ht
    rw [h, mul_eq_zero, pow_eq_zero_iff hk]
    exact or_iff_left (hH0 t ht)
  have hψZ : ∀ t ∈ ball (0 : Fin (d + 1) → ℂ) r, ψ t ∈ zeroSet J := fun t ht =>
    NormalModelFibre.firstCoords_mem_zeroSet M (hφZ ht)
  have hslice : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), ψ (consZero d v) ∈ zeroSet J ∩ {x | linEval u x = 0} := by
    filter_upwards [ball_mem_nhds (0 : Fin d → ℂ) hr] with v hv
    have hv' := consZero_mem_ball hv
    exact ⟨hψZ _ hv', (hzero _ hv').2 (consZero_apply_zero v)⟩
  obtain ⟨ha, W, hW, hWinj, hcov⟩ := slice_chart hψ hψ0 hinjD hV hqV hg hAg hS hslice
  have hE : ball (0 : Fin (d + 1) → ℂ) r ∩ φ ⁻¹' G ∩ ψ ⁻¹' N₀ ∈ 𝓝 (0 : Fin (d + 1) → ℂ) := by
    have hφc : ContinuousAt φ 0 := hφd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
    have hψc : ContinuousAt ψ 0 := hψd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
    exact inter_mem (inter_mem (ball_mem_nhds 0 hr) (hφc.preimage_mem_nhds (by rw [hφ0]; exact hG)))
      (hψc.preimage_mem_nhds (by rw [hψ0]; exact hN₀))
  obtain ⟨ε₁, hε₁, hε₁E⟩ := Metric.mem_nhds_iff.1 hE
  obtain ⟨ε₂, hε₂, hε₂W⟩ := Metric.mem_nhds_iff.1 hW
  have hs : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have hs1 : ball (0 : Fin (d + 1) → ℂ) (min ε₁ ε₂) ⊆ ball 0 r ∩ φ ⁻¹' G ∩ ψ ⁻¹' N₀ :=
    (ball_subset_ball (min_le_left _ _)).trans hε₁E
  have hsr : ball (0 : Fin (d + 1) → ℂ) (min ε₁ ε₂) ⊆ ball 0 r := fun t ht => (hs1 ht).1.1
  have hs2 : ball (0 : Fin d → ℂ) (min ε₁ ε₂) ⊆ W := (ball_subset_ball (min_le_right _ _)).trans hε₂W
  have hinj : InjOn ψ (ball 0 (min ε₁ ε₂)) := by
    intro t ht t' ht' htt
    by_cases hφe : φ t = φ t'
    · exact hφi (hsr ht) (hsr ht') hφe
    · have hu : linEval u (ψ t) = 0 :=
        hdouble _ (hφZ (hsr ht)) _ (hφZ (hsr ht')) htt (hs1 ht).2 hφe
      have ht0 : t 0 = 0 := (hzero t (hsr ht)).1 hu
      have ht'0 : t' 0 = 0 := (hzero t' (hsr ht')).1 (by rw [← htt]; exact hu)
      have htail : Fin.tail t = Fin.tail t' := hWinj (hs2 (tail_mem_ball ht)) (hs2 (tail_mem_ball ht'))
        (by show ψ (consZero d (Fin.tail t)) = ψ (consZero d (Fin.tail t'))
            rw [consZero_tail t ht0, consZero_tail t' ht'0]
            exact htt)
      calc t = consZero d (Fin.tail t) := (consZero_tail t ht0).symm
        _ = t' := by rw [htail, consZero_tail t' ht'0]
  let γ : VarBranch J (d + 1) q :=
    { radius := min ε₁ ε₂, radius_pos := hs, toFun := ψ, differentiableOn := hψd.mono hsr, injOn := hinj,
      map_zero := hψ0, mapsTo := fun t ht => hψZ t (hsr ht) }
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨U, hU, hUs⟩ := hφU (min ε₁ ε₂) hs
    refine ⟨U, hU, fun w' hw' => ?_⟩
    obtain ⟨t, ht, rfl⟩ := hUs hw'
    exact ⟨t, ht, rfl⟩
  · rintro x ⟨t, ht, rfl⟩
    exact ⟨(hs1 ht).2, φ t, ⟨hφZ (hsr ht), (hs1 ht).1.2⟩, rfl⟩
  · obtain ⟨N, hN, hNS⟩ := hcov (ball 0 (min ε₁ ε₂)) (ball_mem_nhds 0 hs) hs2
    refine ⟨N, hN, fun x hx hxu => ?_⟩
    obtain ⟨v, hv, hvx⟩ := hNS ⟨⟨hx.1, hxu⟩, hx.2⟩
    exact ⟨consZero d v, ⟨consZero_mem_ball hv, consZero_apply_zero v⟩, hvx⟩
  · exact ⟨H, hHd.mono hsr, fun t ht => hH0 t (hsr ht), fun t ht => hF t (hsr ht)⟩
  · have hπ : ∀ x : Fin n → ℂ, LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ x = A x :=
      fun x => LinearMap.toMatrix'_mulVec _ x
    have h1 : HasFDerivAt (fun τ : Fin (d + 1) → ℂ => (τ 0, A (ψ τ)))
        ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0))) 0 :=
      (hasFDerivAt_apply 0 0).prodMk (A.hasFDerivAt.comp 0 hψ.hasFDerivAt)
    have h2 : HasFDerivAt (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ))
        ((consCLM d).comp ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0)))) 0 := by
      have h3 := (consCLM d).hasFDerivAt.comp 0 h1
      have hfun : (fun τ => vecCons (τ 0)
          (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) =
          ⇑(consCLM d) ∘ fun τ : Fin (d + 1) → ℂ => (τ 0, A (ψ τ)) := by
        funext τ
        rw [Function.comp_apply, consCLM_apply, hπ]
      rw [hfun]
      exact h3
    rw [h2.fderiv]
    set L := (consCLM d).comp ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0))) with hL
    have hLinj : Function.Injective L := by
      refine (injective_iff_map_eq_zero L).2 fun v hv => ?_
      have hLv : L v = vecCons (v 0) (A (fderiv ℂ ψ 0 v)) := by
        rw [hL, ContinuousLinearMap.comp_apply, consCLM_apply]
        rfl
      have hv' : vecCons (v 0) (A (fderiv ℂ ψ 0 v)) = 0 := by rw [← hLv]; exact hv
      have h0 : v 0 = 0 := by simpa using congrFun hv' 0
      have hA : A (fderiv ℂ ψ 0 v) = 0 := by
        funext j
        simpa using congrFun hv' j.succ
      exact ha v h0 hA
    exact ⟨hLinj, LinearMap.injective_iff_surjective
      (f := (L : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ))).1 hLinj⟩

end GoodPointBranch

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SliceDim.homogeneousComponent_zero_linForm_sub_one {n : ℕ} (ℓ : Fin n → ℂ) :
    homogeneousComponent 0 (linForm ℓ - 1 : MvPolynomial (Fin n) ℂ) = -1 := by
  rw [homogeneousComponent_zero]
  simp [linForm, coeff_sum, coeff_C_mul, coeff_X]

theorem SliceDim.linForm_sub_one_not_mem {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hH : IsHomogIdeal J) (hJ : J ≠ ⊤) (ℓ : Fin n → ℂ) : linForm ℓ - 1 ∉ J := by
  intro h
  have h0 := hH _ h 0
  rw [SliceDim.homogeneousComponent_zero_linForm_sub_one, neg_mem_iff] at h0
  exact hJ ((Ideal.eq_top_iff_one J).mpr h0)

theorem SliceDim.proof : SliceDim.Statement := by
  intro n e J ℓ hJ hdim hℓ
  have hP := hJ.isPrime
  refine le_antisymm ?_ (IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice ⟨hP, hdim⟩ hJ.isHomog hℓ)
  set r := Ideal.Quotient.mk J (linForm ℓ - 1) with hr_def
  have hr0 : r ≠ 0 := by
    rw [hr_def, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact SliceDim.linForm_sub_one_not_mem hJ.isHomog hP.ne_top ℓ
  have hr : r ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) := mem_nonZeroDivisors_of_ne_zero hr0
  have hle : J ≤ J ⊔ Ideal.span {linForm ℓ - 1} := le_sup_left
  have hkill : Ideal.Quotient.factor hle r = 0 := by
    rw [hr_def, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact le_sup_right (a := J) (Ideal.subset_span rfl)
  have key := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) hr hkill
  rw [hdim] at key
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) = D at key ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      norm_cast at key
    | coe m =>
      have : m + 1 ≤ e + 1 := by exact_mod_cast key
      exact_mod_cast (by omega : m ≤ e)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Metric Matrix ComplexSets

theorem ParamCritNull.proof : ParamCritNull.Statement := by
  intro n d W A σ r N hW hdim hA hσ hinj hN hZ
  have hg : DifferentiableOn ℂ (fun v => A *ᵥ σ v) (ball (0 : Fin d → ℂ) r) := by
    have hL : Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable
    exact hL.comp_differentiableOn hσ
  set Ω : Set (Fin d → ℂ) := ball (0 : Fin d → ℂ) r ∩ σ ⁻¹' N with hΩdef
  have hΩ : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage isOpen_ball hN
  rcases Set.eq_empty_or_nonempty Ω with hemp | hne
  · have hsub : {w | w ∈ ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} ⊆ Ω :=
      fun w hw => ⟨hw.1, hw.2.1⟩
    rw [hemp] at hsub
    rw [Set.subset_empty_iff.mp hsub, measure_empty]

  have hsome : ∃ w ∈ ball (0 : Fin d → ℂ) r,
      LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hrank : ∀ v ∈ Ω, ¬ Function.Injective (fderiv ℂ (fun v => A *ᵥ σ v) v) := by
      intro v hv hinjv
      have h0 := hcon v hv.1
      rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
      exact h0 (LinearMap.ker_eq_bot.mpr hinjv)
    obtain ⟨y, hy⟩ := IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.proof d d Ω (fun v => A *ᵥ σ v) hΩ hne
      (hg.mono Set.inter_subset_left) hrank
    have himg : (σ '' {t | t ∈ Ω ∧ A *ᵥ σ t = y}).Infinite :=
      hy.image (hinj.mono fun t ht => ht.1.1)
    have hfin := (ComplexSets.FibreBound.proof n d W A hW hdim hA y).2.1
    refine himg (hfin.subset ?_)
    rintro x ⟨t, ⟨⟨htb, htN⟩, hty⟩, rfl⟩
    exact ⟨hZ t htb htN, hty⟩

  have han : AnalyticOnNhd ℂ (fun w =>
      LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ))
      (ball (0 : Fin d → ℂ) r) := fun w hw =>
    IndefiniteRowSideFullHecke.ComplexSets.analyticAt_det_fderiv
      (IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.analyticAt_of_differentiableOn isOpen_ball hg hw)
  refine measure_mono_null ?_ (ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_ball
    (convex_ball (0 : Fin d → ℂ) r).isPreconnected han hsome)
  exact fun w hw => ⟨hw.1, hw.2.2⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

namespace LelongNumberMonotone

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem maDens_logDistSq_nonneg (x z : Fin n → ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (hzx : z ≠ x)
    (hs : IsSheetAt J A z s) :
    0 ≤ ReciprocityTheory.AnForm.maDens (fun _ : Fin (d + 1) => logDistSq x ∘ s) (A *ᵥ z) := by
  have han : AnalyticAt ℂ s (A *ᵥ z) := FormIntegralPositivity.analyticAt_sheet hs
  have hsz : s (A *ᵥ z) = z := by
    obtain ⟨U, -, -, -, h, -⟩ := hs
    exact h
  exact ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ =>
    RegularizedLogDensityNonneg.hessC_logDistSq_comp_posSemidef x s _ han (hsz.symm ▸ hzx)

theorem chartDens_annulus_nonneg (x : Fin n → ℂ) {r s : ℝ} (hr : 0 < r) (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1) (fun _ => logDistSq x) y := by
  unfold chartDens sheetSum
  refine finsum_nonneg fun z => finsum_nonneg fun hz => ?_
  split_ifs with h
  · beta_reduce
    by_cases hza : z ∈ euclBall x s \ euclBall x r
    · rw [Set.indicator_of_mem hza, one_mul]
      have := maDens_logDistSq_nonneg x z h.choose (ne_of_mem_euclBall_diff hr hza) h.choose_spec
      rwa [hz.2] at this
    · rw [Set.indicator_of_notMem hza, zero_mul]
  · exact le_rfl

end LelongNumberMonotone


open LelongNumberMonotone in
theorem VarLelongMono.proof (hA : VarLelongAnnulus.Statement) : VarLelongMono.Statement := by
  intro n d J A x r s hJ hdim hAf hr hrs
  have heq := hA n d J A x r s hJ hdim hAf hr hrs
  have hτ : 0 ≤ ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (fun _ => logDistSq x) y :=
    integral_nonneg fun y => chartDens_annulus_nonneg x hr y
  have hrs0 : 0 ≤ r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) :=
    mul_nonneg (pow_nonneg hr.le _) (pow_nonneg (hr.le.trans hrs) _)
  have := mul_nonneg hrs0 hτ
  linarith

end

end GroundTheory.Heights₂.Heights
end
