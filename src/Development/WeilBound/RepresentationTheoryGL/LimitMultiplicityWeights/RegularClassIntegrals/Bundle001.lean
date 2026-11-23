module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem identTwo : IdentTwo := by
  intro H _ _ _ _ _ _ _ _ n ι hc s B hB μ _ _ dt _ _ φ hφc hφs hO h
  have : μ.IsInvInvariant := GlobalTheory.SqIntRep.isInvInvariant_of_unimodular μ
  set f : H → ℂ := fun z => φ (z⁻¹ * s * z) * (B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) : ℂ) with hfdef
  set F : H → ℂ := fun k => φ (k * (h⁻¹ * s * h) * k⁻¹) *
    (B (matCoord ι (k * (h⁻¹ * s * h) * k⁻¹), matCoord ι k) : ℂ) with hFdef
  have hsub : ∫ k, F k ∂μ = ∫ z, f z ∂μ := by
    have h1 := integral_mul_right_eq_self (μ := μ) (fun k => F k) h
    have h2 := integral_inv_eq_self (fun k => F (k * h)) μ
    rw [← h1, ← h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have e : z⁻¹ * h * (h⁻¹ * s * h) * (z⁻¹ * h)⁻¹ = z⁻¹ * s * z := by group
    simp only [hFdef, hfdef, e]
  have hBc : Continuous B := hB.smooth.continuous
  have hfc : Continuous f := by
    have h1 : Continuous fun z : H => z⁻¹ * s * z := by fun_prop
    have h2 : Continuous fun z : H => z⁻¹ * h := by fun_prop
    exact (hφc.comp h1).mul (Complex.continuous_ofReal.comp (hBc.comp ((hc.comp h1).prodMk (hc.comp h2))))
  obtain ⟨K, hK, hKp⟩ := hB.proper (tsupport φ) {h⁻¹ * s * h} hφs isCompact_singleton
  have hfs : HasCompactSupport f := by
    refine HasCompactSupport.intro (hK.image (f := fun k => h * k⁻¹) (by fun_prop)) fun z hz => ?_
    by_contra hne
    apply hz
    have hne' : φ (z⁻¹ * s * z) * (B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) : ℂ) ≠ 0 := hne
    have m1 : z⁻¹ * s * z ∈ tsupport φ := subset_tsupport _ (left_ne_zero_of_mul hne')
    have m2 : B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) ≠ 0 := by
      intro h0; apply hne'; rw [h0]; simp
    have m3 : (z * (z⁻¹ * h))⁻¹ * s * (z * (z⁻¹ * h)) ∈ ({h⁻¹ * s * h} : Set H) := by
      rw [mul_inv_cancel_left]; exact Set.mem_singleton _
    exact ⟨z⁻¹ * h, hKp z (z⁻¹ * h) m1 m3 m2, by group⟩
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hW := (weil_integral (T := cent s) (dt := dt) (dh := μ) (isClosed_cent s) hfi).2.2
  set κ : ℂ := ∫ t : cent s, (B (matCoord ι s, matCoord ι ((t : H)⁻¹)) : ℂ) ∂dt with hκ
  have hfib : ∀ x, ∫ t : cent s, f (t * x) ∂dt = φ (x⁻¹ * s * x) * κ := by
    intro x
    obtain ⟨t₀, ht₀, hsh⟩ := hB.shift x h 1 1
    have e1 : ∀ t : cent s, ((t : H) * x)⁻¹ * s * ((t : H) * x) = x⁻¹ * s * x := by
      intro t
      have hts := mem_cent.1 t.2
      have : (t : H)⁻¹ * s * t = s := by rw [mul_assoc, ← hts, inv_mul_cancel_left]
      calc ((t : H) * x)⁻¹ * s * ((t : H) * x) = x⁻¹ * ((t : H)⁻¹ * s * t) * x := by group
        _ = x⁻¹ * s * x := by rw [this]
    have e2 : ∀ t : cent s, f (t * x) = φ (x⁻¹ * s * x) *
        (B (matCoord ι s, matCoord ι ((((⟨t₀, ht₀⟩ : cent s)⁻¹ * t : cent s) : H)⁻¹)) : ℂ) := by
      intro t
      have hs' := hsh (t : H)⁻¹ (inv_mem t.2)
      simp only [inv_one, one_mul, mul_one] at hs'
      have hco : (t : H)⁻¹ * t₀ = ((((⟨t₀, ht₀⟩ : cent s)⁻¹ * t : cent s) : H))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv]
      simp only [hfdef, e1]
      rw [show ((t : H) * x)⁻¹ * h = x⁻¹ * (t : H)⁻¹ * h by group, hs', hco]
    simp_rw [e2]
    rw [integral_const_mul]
    congr 1
    exact integral_mul_left_eq_self (fun t : cent s => (B (matCoord ι s, matCoord ι ((t : H))⁻¹) : ℂ)) _
  have hfun : (fun x => ∫ t : cent s, f (t * x) ∂dt) = fun x => conjFn s φ x * κ := funext fun x => hfib x
  show ∫ k, F k ∂μ = 0
  rw [hsub, ← hW, hfun]
  have h0 := hO.2
  unfold quotInt descend at h0 ⊢
  show ∫ q, conjFn s φ q.out * κ ∂quotMeas (cent s) dt μ = 0
  rw [integral_mul_const, h0, zero_mul]

end MainStatements.WeightKernel

end
end

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PVanish

def mul3 {n : ℕ} (A B C : MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n := fun a b => (of A * of B * of C) a b

theorem contDiff_triple_matrix_product {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g h : E → MainStatements.WeightKernel.Mx n}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ fun x => mul3 (f x) (g x) (h x) := by
  have e : ∀ (u : E → Mx n), ContDiff ℝ ∞ u → ∀ a b : Fin n, ContDiff ℝ ∞ fun x => u x a b :=
    fun u hu a b => contDiff_pi.1 (contDiff_pi.1 hu a) b
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [mul3, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun j _ =>
    (ContDiff.sum fun k _ => (e f hf a k).mul (e g hg k j)).mul (e h hh j b)

theorem triple_product_matrix_coordinates {H : Type} [Group H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (g h l : H) :
    mul3 (matCoord ι g) (matCoord ι h) (matCoord ι l) = matCoord ι (g * h * l) := by
  funext a b
  show (ι g * ι h * ι l) a b = ι (g * h * l) a b
  rw [map_mul, map_mul]

end MainStatements.WeightKernel.PVanish

open MainStatements.WeightKernel.PVanish in
theorem MainStatements.WeightKernel.vanish : KerSwap → IdentOne → IdentTwo → Vanish := by
  intro hSwap hOne hTwo H _ _ _ _ _ _ _ _ n ι hemb s B hB μ _ _ dt _ _ Ω I _ _ m _ c q hK hq hInv φ hφ hOrb
  obtain ⟨hφc, Φφ, hΦφ, hφeq⟩ := hφ
  have hmc : Continuous (matCoord ι) := hemb.continuous
  have hφcont : Continuous φ := by
    rw [show φ = fun g => Φφ (matCoord ι g) from funext hφeq]
    exact hΦφ.continuous.comp hmc
  let bp : ContDiffBump (matCoord ι s) := ⟨1, 2, one_pos, one_lt_two⟩
  let ψ : H → ℝ := fun y => bp (matCoord ι y)
  have hψc : Continuous ψ := bp.continuous.comp hmc
  have hψcs : HasCompactSupport ψ := bp.hasCompactSupport.comp_isClosedEmbedding hemb
  have hψs : 0 < ψ s := by
    have : ψ s = 1 := bp.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
    rw [this]
    exact one_pos
  obtain ⟨a, ha0, ha⟩ := hOne H n ι hmc s B hB μ dt ψ hψc hψcs (fun y => bp.nonneg) hψs
  obtain ⟨Kset, hKc, hKprop⟩ := hB.proper (tsupport φ) (tsupport ψ) hφc.isCompact hψcs.isCompact
  let p : H → Mx n × Mx n := fun k => (matCoord ι k, matCoord ι k⁻¹)
  have hp : Continuous p := hmc.prodMk (hmc.comp continuous_inv)
  let W₁ : Mx n × (Mx n × Mx n) → ℂ := fun z =>
    Φφ z.1 * ((B (z.1, z.2.1) : ℝ) : ℂ) * ((bp (mul3 z.2.2 z.1 z.2.1) : ℝ) : ℂ)
  let W₂ : Mx n × (Mx n × Mx n) → ℂ := fun z =>
    Φφ (mul3 z.2.1 z.1 z.2.2) * ((B (mul3 z.2.1 z.1 z.2.2, z.2.1) : ℝ) : ℂ) * ((bp z.1 : ℝ) : ℂ)
  have hfst : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.1 := contDiff_fst
  have hA : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.2.1 := contDiff_fst.comp contDiff_snd
  have hC : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.2.2 := contDiff_snd.comp contDiff_snd
  have hM1 := contDiff_triple_matrix_product hC hfst hA
  have hM2 := contDiff_triple_matrix_product hA hfst hC
  have hW₁ : ContDiff ℝ ∞ W₁ :=
    ((hΦφ.comp hfst).mul (Complex.ofRealCLM.contDiff.comp (hB.smooth.comp (hfst.prodMk hA)))).mul
      (Complex.ofRealCLM.contDiff.comp (bp.contDiff.comp hM1))
  have hW₂ : ContDiff ℝ ∞ W₂ :=
    ((hΦφ.comp hM2).mul (Complex.ofRealCLM.contDiff.comp (hB.smooth.comp (hM2.prodMk hA)))).mul
      (Complex.ofRealCLM.contDiff.comp (bp.contDiff.comp hfst))
  have hW₁pt : ∀ y k : H, W₁ (matCoord ι y, p k) =
      φ y * ((B (matCoord ι y, matCoord ι k) : ℂ) * (ψ (k⁻¹ * y * k) : ℂ)) := by
    intro y k
    simp only [W₁, p, ψ]
    rw [triple_product_matrix_coordinates, hφeq, mul_assoc]
  have hW₂pt : ∀ y k : H, W₂ (matCoord ι y, p k) =
      φ (k * y * k⁻¹) * (B (matCoord ι (k * y * k⁻¹), matCoord ι k) : ℂ) * (ψ y : ℂ) := by
    intro y k
    simp only [W₂, p, ψ]
    rw [triple_product_matrix_coordinates, hφeq]
  have hvan1 : ∀ z k : H, k ∉ Kset → W₁ (matCoord ι (z⁻¹ * s * z), p k) = 0 := by
    intro z k hk
    rw [hW₁pt]
    by_contra hne
    apply hk
    have h1 : φ (z⁻¹ * s * z) ≠ 0 := left_ne_zero_of_mul hne
    have h23 := right_ne_zero_of_mul hne
    have h2 : (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) ≠ 0 := left_ne_zero_of_mul h23
    have h3 : (ψ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ) ≠ 0 := right_ne_zero_of_mul h23
    have e : (z * k)⁻¹ * s * (z * k) = k⁻¹ * (z⁻¹ * s * z) * k := by group
    refine hKprop z k (subset_tsupport _ h1) ?_ (fun h0 => h2 (by simp [h0]))
    rw [e]
    exact subset_tsupport _ (Function.mem_support.2 (fun h0 => h3 (by simp [h0])))
  have hvan2 : ∀ w k : H, k ∉ Kset → W₂ (matCoord ι (w⁻¹ * s * w), p k) = 0 := by
    intro w k hk
    rw [hW₂pt]
    by_contra hne
    apply hk
    have h12 := left_ne_zero_of_mul hne
    have h3 : (ψ (w⁻¹ * s * w) : ℂ) ≠ 0 := right_ne_zero_of_mul hne
    have h1 : φ (k * (w⁻¹ * s * w) * k⁻¹) ≠ 0 := left_ne_zero_of_mul h12
    have h2 : (B (matCoord ι (k * (w⁻¹ * s * w) * k⁻¹), matCoord ι k) : ℂ) ≠ 0 :=
      right_ne_zero_of_mul h12
    have e1 : (w * k⁻¹)⁻¹ * s * (w * k⁻¹) = k * (w⁻¹ * s * w) * k⁻¹ := by group
    have e2 : (w * k⁻¹ * k)⁻¹ * s * (w * k⁻¹ * k) = w⁻¹ * s * w := by group
    refine hKprop (w * k⁻¹) k ?_ ?_ ?_
    · rw [e1]
      exact subset_tsupport _ h1
    · rw [e2]
      exact subset_tsupport _ (Function.mem_support.2 (fun h0 => h3 (by simp [h0])))
    · rw [e1]
      exact fun h0 => h2 (by simp [h0])
  have h1 := hSwap H n ι hemb μ Ω I m c q hK (Mx n × Mx n) W₁ p Kset (tsupport φ) hW₁ hp hKc
    hφc.isCompact (by
      intro k _ y hy
      have : φ y = 0 := by
        by_contra h0
        exact hy (subset_tsupport _ h0)
      rw [hW₁pt, this, zero_mul])
  have h2 := hSwap H n ι hemb μ Ω I m c q hK (Mx n × Mx n) W₂ p Kset (tsupport ψ) hW₂ hp hKc
    hψcs.isCompact (by
      intro k _ y hy
      have : ψ y = 0 := by
        by_contra h0
        exact hy (subset_tsupport _ h0)
      rw [hW₂pt, this]
      simp)
  have hR1 : ∫ x, ker c q (fun y => ∫ k in Kset, W₁ (matCoord ι y, p k) ∂μ) x ∂m =
      a * ∫ x, ker c q φ x ∂m := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [MainStatements.WeightKernel.ker]
    rw [← tsum_mul_left]
    congr 1
    funext i
    obtain ⟨z, hz⟩ := hq i x
    rw [hz, setIntegral_eq_integral_of_forall_compl_eq_zero (hvan1 z)]
    simp only [hW₁pt]
    rw [integral_const_mul, ha z]
    ring
  have hstep : ∀ k : H, ∫ x, ker c q (fun y => W₁ (matCoord ι y, p k)) x ∂m =
      ∫ x, ker c q (fun y => W₂ (matCoord ι y, p k)) x ∂m := by
    intro k
    have hmem : (fun y => W₂ (matCoord ι y, p k)) ∈ CcMat ι := by
      refine ⟨?_, fun Y => W₂ (Y, p k), hW₂.comp (contDiff_id.prodMk contDiff_const), fun g => rfl⟩
      refine hψcs.mono ?_
      intro y hy
      rw [Function.mem_support] at hy ⊢
      intro h0
      apply hy
      rw [hW₂pt, h0]
      simp
    have hfun : (fun y => W₁ (matCoord ι y, p k)) =
        fun y => W₂ (matCoord ι (k⁻¹ * y * k⁻¹⁻¹), p k) := by
      funext y
      rw [hW₂pt, hW₁pt]
      have e : k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ = y := by group
      rw [e, inv_inv]
      ring
    rw [hfun]
    exact hInv _ hmem k⁻¹
  have hR2 : ∫ x, ker c q (fun y => ∫ k in Kset, W₂ (matCoord ι y, p k) ∂μ) x ∂m = 0 := by
    have hz : ∀ x, ker c q (fun y => ∫ k in Kset, W₂ (matCoord ι y, p k) ∂μ) x = 0 := by
      intro x
      simp only [MainStatements.WeightKernel.ker]
      refine (tsum_congr fun i => ?_).trans tsum_zero
      obtain ⟨w, hw⟩ := hq i x
      rw [hw, setIntegral_eq_integral_of_forall_compl_eq_zero (hvan2 w)]
      simp only [hW₂pt]
      rw [integral_mul_const, hTwo H n ι hmc s B hB μ dt φ hφcont hφc hOrb w]
      simp
    simp [hz]
  have key : a * ∫ x, ker c q φ x ∂m = 0 := by
    rw [← hR1, ← h1]
    simp only [hstep]
    rw [h2]
    exact hR2
  exact (mul_eq_zero.1 key).resolve_left ha0

end
end

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PKerUnif

theorem ker_eq_sum {H Ω I : Type} (c : I → Ω → ℂ) (q : I → Ω → H) (φ : H → ℂ) (C : Set H) (x : Ω)
    (hf : {i | c i x ≠ 0 ∧ q i x ∈ C}.Finite) (hφ : ∀ y ∉ C, φ y = 0) :
    MainStatements.WeightKernel.ker c q φ x = ∑ i ∈ hf.toFinset, c i x * φ (q i x) := by
  unfold MainStatements.WeightKernel.ker
  apply tsum_eq_sum
  intro i hi
  rw [Set.Finite.mem_toFinset] at hi
  by_cases h1 : c i x = 0
  · simp [h1]
  · have h2 : q i x ∉ C := fun h => hi ⟨h1, h⟩
    simp [hφ _ h2]

end MainStatements.WeightKernel.PKerUnif

open MainStatements.WeightKernel.PKerUnif in
theorem MainStatements.WeightKernel.kerUnif : SmoothSum → ClosedGraph → KerUnif := by
  intro hS hCG H _ _ _ _ _ _ _ _ n ι hι Ω I _ _ m _ c q hker P _ _ _ W p K C hW hp hK hC hvan
  obtain ⟨M, hM⟩ := ((hC.image hι.continuous).prod (hK.image hp)).exists_bound_of_continuousOn
    hW.continuous.continuousOn
  have hMb : ∀ y ∈ C, ∀ k ∈ K, ‖W (matCoord ι y, p k)‖ ≤ M := fun y hy k hk =>
    hM _ (Set.mk_mem_prod ⟨y, hy, rfl⟩ ⟨k, hk, rfl⟩)
  obtain ⟨R, hR⟩ := (hC.image hι.continuous).isBounded.subset_closedBall (0 : Mx n)
  obtain ⟨Bd, hBd⟩ := hCG Ω K m (fun (k : K) x => ker c q (fun y => W (matCoord ι y, p k)) x) (by
    intro x
    refine ⟨∑ i ∈ (hker.fin x C hC).toFinset, ‖c i x‖ * M, fun k => ?_⟩
    rw [ker_eq_sum c q _ C x (hker.fin x C hC) (fun y hy => hvan k k.2 y hy)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hMb _ ((Set.Finite.mem_toFinset _).1 hi).2 _ k.2) (norm_nonneg _)) (by
    intro a ha
    have hz : ∀ y ∉ C, ∑' k : K, a k * W (matCoord ι y, p k) = 0 := by
      intro y hy
      have : ∀ k : K, a k * W (matCoord ι y, p k) = 0 := fun k => by rw [hvan k.1 k.2 y hy, mul_zero]
      simp [this]
    let bump : ContDiffBump (0 : Mx n) :=
      ⟨max R 0 + 1, max R 0 + 2, add_pos_of_nonneg_of_pos (le_max_right _ _) one_pos, by linarith⟩
    obtain ⟨Φ, hΦs, hΦ⟩ := hS (Mx n) P W hW (p '' K) (Metric.closedBall 0 (max R 0 + 2)) (hK.image hp)
      (isCompact_closedBall _ _) K (fun k => p k.1) (fun k => ⟨k.1, k.2, rfl⟩) a ha
    have hψ : (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) ∈ CcMat ι := by
      refine ⟨HasCompactSupport.intro hC fun y hy => hz y hy, fun z => Complex.ofRealCLM (bump z) * Φ z,
        (Complex.ofRealCLM.contDiff.comp bump.contDiff).mul hΦs, fun y => ?_⟩
      simp only [Complex.ofRealCLM_apply]
      by_cases hy : y ∈ C
      · have hin : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 1) :=
          Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)
        have hin2 : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2) :=
          Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)
        have h1 : bump (matCoord ι y) = 1 := bump.one_of_mem_closedBall hin
        rw [h1, hΦ _ hin2]
        simp
      · by_cases hb : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2)
        · rw [hΦ _ hb]
          simp [hz y hy]
        · have h0 : bump (matCoord ι y) = 0 :=
            image_eq_zero_of_notMem_tsupport (by rw [bump.tsupport_eq]; exact hb)
          simp [h0, hz y hy]
    refine (hker.int _ hψ).congr (ae_of_all m fun x => ?_)
    have hf := hker.fin x C hC
    have hs : ∀ i ∈ hf.toFinset, Summable (fun k : K => a k * W (matCoord ι (q i x), p k)) := by
      intro i hi
      have hq := ((Set.Finite.mem_toFinset _).1 hi).2
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (ha.mul_right M))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMb _ hq _ k.2) (norm_nonneg _)
    have hu : ∀ k : K, ker c q (fun y => W (matCoord ι y, p k)) x
        = ∑ i ∈ hf.toFinset, c i x * W (matCoord ι (q i x), p k) :=
      fun k => ker_eq_sum c q _ C x hf (fun y hy => hvan k k.2 y hy)
    symm
    calc ∑' k : K, a k * ker c q (fun y => W (matCoord ι y, p k)) x
        = ∑' k : K, ∑ i ∈ hf.toFinset, c i x * (a k * W (matCoord ι (q i x), p k)) := by
          congr 1; ext k; rw [hu k, Finset.mul_sum]; congr 1; ext i; ring
      _ = ∑ i ∈ hf.toFinset, ∑' k : K, c i x * (a k * W (matCoord ι (q i x), p k)) :=
          Summable.tsum_finsetSum fun i hi => (hs i hi).mul_left _
      _ = ∑ i ∈ hf.toFinset, c i x * ∑' k : K, a k * W (matCoord ι (q i x), p k) := by
          congr 1; ext i; rw [tsum_mul_left]
      _ = ker c q (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) x :=
          (ker_eq_sum c q _ C x hf hz).symm)
  exact ⟨Bd, fun k hk => hBd ⟨k, hk⟩⟩

end
end

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem bumpOn : BumpOn := by
  intro H _ _ _ _ _ _ _ _ n ι hemb C hC
  have hK : IsCompact (matCoord ι '' C) := hC.image hemb.continuous
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  let f : ContDiffBump (0 : Fin n → Fin n → ℂ) :=
    ⟨max r 1, max r 1 + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩
  refine ⟨fun g => ((f (matCoord ι g) : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · refine HasCompactSupport.intro (hemb.isCompact_preimage (isCompact_closedBall (0 : Fin n → Fin n → ℂ) (max r 1 + 1))) ?_
    intro g hg
    simp only [Set.mem_preimage, Metric.mem_closedBall, not_le] at hg
    have : f (matCoord ι g) = 0 := f.zero_of_le_dist hg.le
    simp [this]
  · refine ⟨fun x => ((f x : ℝ) : ℂ), ?_, fun g => rfl⟩
    exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · intro y hy
    have hm : matCoord ι y ∈ Metric.closedBall (0 : Fin n → Fin n → ℂ) (max r 1) :=
      Metric.closedBall_subset_closedBall (le_max_left _ _) (hr ⟨y, hy, rfl⟩)
    have : f (matCoord ι y) = 1 := f.one_of_mem_closedBall hm
    simp [this]

end MainStatements.WeightKernel

end
end

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PFdRight

end MainStatements.WeightKernel.PFdRight

theorem MainStatements.WeightKernel.fdRight : MainStatements.WeightKernel.FDRight := by
  intro G _ _ _ _ _ _ Γ _ μ _ _ 𝓕 h𝓕 F hF g
  have h2 : IsFundamentalDomain Γ ((fun x : G => x * g⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have key : ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in (fun x : G => x * g⁻¹) ⁻¹' 𝓕, F x ∂μ := by
    rw [← Set.image_mul_right,
      (measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) F 𝓕]
  rw [key]
  exact h2.setIntegral_eq h𝓕 (fun γ x => by rw [Subgroup.smul_def, smul_eq_mul]; exact hF γ γ.2 x)
end
end
