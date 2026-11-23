module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix

theorem FibreSectionsCovering.proof : FibreSectionsCovering.Statement := by
  intro n e N A Ω X hX hfib hsec
  let f : X → Ω := Set.MapsTo.restrict _ X Ω hX
  show IsCoveringMap f
  have hAc : Continuous (fun x : Fin n → ℂ => A *ᵥ x) :=
    (Matrix.mulVecLin A).continuous_of_finiteDimensional
  choose O V' g hO hAO hV' hxV' hg hgx hAg hXV' using hsec

  have key : ∀ x₀ (h₀ : x₀ ∈ X) x, x ∈ X → x ∈ V' x₀ h₀ → g x₀ h₀ (A *ᵥ x) = x := by
    intro x₀ h₀ x hx hxv
    have hx' : x ∈ g x₀ h₀ '' O x₀ h₀ := hXV' x₀ h₀ ▸ ⟨hx, hxv⟩
    obtain ⟨o, ho, rfl⟩ := hx'
    rw [hAg x₀ h₀ o ho]

  have inX : ∀ x₀ (h₀ : x₀ ∈ X) w, w ∈ O x₀ h₀ → g x₀ h₀ w ∈ X ∧ g x₀ h₀ w ∈ V' x₀ h₀ := by
    intro x₀ h₀ w hw
    have h : g x₀ h₀ w ∈ X ∩ V' x₀ h₀ := hXV' x₀ h₀ ▸ ⟨w, hw, rfl⟩
    exact h
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have : IsEmpty X := by
      refine ⟨fun x => ?_⟩
      have h := hfib _ (hX x.2)
      rw [hN, Nat.cast_zero, Set.encard_eq_zero] at h
      have hm : (x : Fin n → ℂ) ∈ {x' | x' ∈ X ∧ A *ᵥ x' = A *ᵥ (x : Fin n → ℂ)} := ⟨x.2, rfl⟩
      rw [h] at hm
      exact hm
    exact IsCoveringMap.of_isEmpty _
  intro y

  have hFenc : {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)}.encard = N := hfib y y.2
  have hFfin := Set.finite_of_encard_eq_coe hFenc
  have := hFfin.to_subtype
  have hFcard : Nat.card {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)} = N := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hFenc]
    rfl
  let eq := (Finite.equivFinOfCardEq hFcard).symm
  let pt : Fin N → Fin n → ℂ := fun i => (eq i : Fin n → ℂ)
  have pt_mem : ∀ i, pt i ∈ X ∧ A *ᵥ pt i = y := fun i => (eq i).2
  have pt_inj : Function.Injective pt := fun i j h => eq.injective (Subtype.ext h)
  let G : Fin N → (Fin (e + 1) → ℂ) → Fin n → ℂ := fun i => g (pt i) (pt_mem i).1
  let OO : Fin N → Set (Fin (e + 1) → ℂ) := fun i => O (pt i) (pt_mem i).1
  let VV : Fin N → Set (Fin n → ℂ) := fun i => V' (pt i) (pt_mem i).1
  have hGy : ∀ i, G i y = pt i := fun i => by
    rw [← (pt_mem i).2]
    exact hgx (pt i) (pt_mem i).1
  have hOy : ∀ i, OO i ∈ 𝓝 (y : Fin (e + 1) → ℂ) := fun i =>
    (hO _ _).mem_nhds (by have h : A *ᵥ pt i ∈ OO i := hAO _ _; rwa [(pt_mem i).2] at h)
  have hGc : ∀ i, ∀ w ∈ OO i, ContinuousAt (G i) w := fun i w hw =>
    (hg _ _).continuousOn.continuousAt ((hO _ _).mem_nhds hw)
  have hS : ∀ᶠ w in 𝓝 (y : Fin (e + 1) → ℂ), (∀ i, w ∈ OO i) ∧ ∀ i j, i ≠ j → G i w ≠ G j w := by
    refine (Filter.eventually_all.2 hOy).and
      (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_)
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · have hne : G i y ≠ G j y := by
        rw [hGy, hGy]
        exact fun h => hij (pt_inj h)
      exact (((hGc i y (mem_of_mem_nhds (hOy i))).ne_iff_eventually_ne
        (hGc j y (mem_of_mem_nhds (hOy j)))).1 hne).mono fun _ hw _ => hw
  obtain ⟨W, hWS, hWo, hyW⟩ := mem_nhds_iff.1 hS
  have hWO : ∀ i, ∀ w ∈ W, w ∈ OO i := fun i w hw => (hWS hw).1 i
  have hWd : ∀ w ∈ W, ∀ i j, i ≠ j → G i w ≠ G j w := fun w hw => (hWS hw).2
  have hGX : ∀ i, ∀ w ∈ W, G i w ∈ X := fun i w hw => (inX _ _ w (hWO i w hw)).1
  have hGV : ∀ i, ∀ w ∈ W, G i w ∈ VV i := fun i w hw => (inX _ _ w (hWO i w hw)).2
  have hAG : ∀ i, ∀ w ∈ W, A *ᵥ G i w = w := fun i w hw => hAg _ _ w (hWO i w hw)
  have hfc : Continuous f := (hAc.comp continuous_subtype_val).subtype_mk fun x => hX x.2
  have hres : ∀ i (q : Ω) (hq : (q : Fin (e + 1) → ℂ) ∈ W),
      f ⟨G i q, hGX i q hq⟩ = q := fun i q hq =>
    Subtype.ext (hAG i q hq)
  let V : Set Ω := {p | (p : Fin (e + 1) → ℂ) ∈ W}
  let U : Fin N → Set X := fun i => {x | (x : Fin n → ℂ) ∈ VV i ∧ A *ᵥ (x : Fin n → ℂ) ∈ W}
  have hVo : IsOpen V := continuous_subtype_val.isOpen_preimage _ hWo
  have hUo : ∀ i, IsOpen (U i) := fun i =>
    continuous_subtype_val.isOpen_preimage _ ((hV' _ _).inter (hWo.preimage hAc))

  have hUG : ∀ i (x : X), x ∈ U i → G i (A *ᵥ (x : Fin n → ℂ)) = x := fun i x hx =>
    key _ _ _ x.2 hx.1
  have open_iff : ∀ i {W' : Set Ω}, W' ⊆ V → (IsOpen W' ↔ IsOpen (f ⁻¹' W' ∩ U i)) := by
    intro i W' hW'V
    refine ⟨fun h => (hfc.isOpen_preimage _ h).inter (hUo i), fun h => ?_⟩
    obtain ⟨T', hT'o, hT'eq⟩ := isOpen_induced_iff.1 h
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hpW : (p : Fin (e + 1) → ℂ) ∈ W := hW'V hp
    have hGp : G i p ∈ T' := by
      have hm : (⟨G i p, hGX i p hpW⟩ : X) ∈ f ⁻¹' W' ∩ U i := by
        refine ⟨?_, hGV i p hpW, ?_⟩
        · show f ⟨G i p, hGX i p hpW⟩ ∈ W'
          rw [hres i p hpW]
          exact hp
        · show A *ᵥ G i p ∈ W
          rw [hAG i p hpW]
          exact hpW
      rw [← hT'eq] at hm
      exact hm
    rw [mem_nhds_subtype]
    refine ⟨W ∩ G i ⁻¹' T', Filter.inter_mem (hWo.mem_nhds hpW)
      ((hGc i p (hWO i p hpW)).preimage_mem_nhds (hT'o.mem_nhds hGp)), ?_⟩
    rintro q ⟨hqW, hqT⟩
    have hm : (⟨G i q, hGX i q hqW⟩ : X) ∈ Subtype.val ⁻¹' T' := hqT
    rw [hT'eq] at hm
    have h1 := hm.1
    rw [Set.mem_preimage, hres i q hqW] at h1
    exact h1
  have inj : ∀ i, (U i).InjOn f := by
    intro i x hx x' hx' hxx'
    have h : A *ᵥ (x : Fin n → ℂ) = A *ᵥ (x' : Fin n → ℂ) := congrArg Subtype.val hxx'
    apply Subtype.ext
    rw [← hUG i x hx, ← hUG i x' hx', h]
  have surj : ∀ i, (U i).SurjOn f V := by
    intro i p hp
    refine ⟨⟨G i p, hGX i p hp⟩, ⟨hGV i p hp, ?_⟩, hres i p hp⟩
    show A *ᵥ G i p ∈ W
    rw [hAG i p hp]
    exact hp
  have disj : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hxi hxj => ?_
    exact hWd _ hxi.2 i j hij ((hUG i x hxi).trans (hUG j x hxj).symm)
  have exh : f ⁻¹' V ⊆ ⋃ i, U i := by
    intro x hx
    have hxW : A *ᵥ (x : Fin n → ℂ) ∈ W := hx
    set w := A *ᵥ (x : Fin n → ℂ) with hw
    have hwΩ : w ∈ Ω := hX x.2
    have hFw := hfib w hwΩ
    have hsub : Set.range (fun i => G i w) ⊆ {x' | x' ∈ X ∧ A *ᵥ x' = w} := by
      rintro _ ⟨i, rfl⟩
      exact ⟨hGX i w hxW, hAG i w hxW⟩
    have hinj : Function.Injective (fun i => G i w) := by
      intro i j h
      by_contra hij
      exact hWd w hxW i j hij h
    have heq : Set.range (fun i => G i w) = {x' | x' ∈ X ∧ A *ᵥ x' = w} := by
      refine ((Set.finite_of_encard_eq_coe hFw).subset hsub).eq_of_subset_of_encard_le hsub ?_
      rw [hFw]
      rw [hinj.encard_range]
      simp
    have hxmem : (x : Fin n → ℂ) ∈ Set.range (fun i => G i w) := by
      rw [heq]
      exact ⟨x.2, rfl⟩
    obtain ⟨i, hi⟩ := hxmem
    refine Set.mem_iUnion.2 ⟨i, ?_, hxW⟩
    show (x : Fin n → ℂ) ∈ VV i
    rw [← hi]
    exact hGV i w hxW
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Ω → X) := ⟨fun _ => ⟨pt ⟨0, hN⟩, (pt_mem _).1⟩⟩
  let T := IsOpen.trivializationDiscrete (f := f) U V hVo open_iff inj surj disj exh
  have hyT : y ∈ T.baseSet := hyW
  exact (IsEvenlyCovered.of_trivialization hyT).to_isEvenlyCovered_preimage

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open scoped InnerProductSpace

theorem det_one_add_adjoint_comp_self_pos {k m : ℕ}
    (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < LinearMap.det ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
      LinearMap.adjoint B ∘ₗ B) := by
  set S : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) := 1 + LinearMap.adjoint B ∘ₗ B
    with hSdef
  have hBB : (LinearMap.adjoint B ∘ₗ B).IsPositive := LinearMap.isPositive_adjoint_comp_self B
  have hS : S.IsPositive := LinearMap.isPositive_one.add hBB
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  rw [hS.isSymmetric.det_eq_prod_eigenvalues hn]
  refine Finset.prod_pos fun i _ => ?_
  set v := hS.isSymmetric.eigenvectorBasis hn i
  have hv : ‖v‖ = 1 := (hS.isSymmetric.eigenvectorBasis hn).orthonormal.1 i
  have h1 : ⟪S v, v⟫_ℝ = hS.isSymmetric.eigenvalues hn i := by
    rw [hS.isSymmetric.apply_eigenvectorBasis hn i]
    simp [real_inner_smul_left, hv, v]
  have h2 : ⟪S v, v⟫_ℝ = ‖v‖ ^ 2 + ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ := by
    rw [hSdef, LinearMap.add_apply, inner_add_left, Module.End.one_apply, real_inner_self_eq_norm_sq]
  have h3 : 0 ≤ ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ := by
    simpa using hBB.re_inner_nonneg_left v
  have : 0 < (hS.isSymmetric.eigenvalues hn i : ℝ) := by
    rw [← h1, h2, hv]; linarith
  simpa using this

theorem graphJac_pos {k m : ℕ} (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < graphJac B :=
  Real.sqrt_pos.mpr (det_one_add_adjoint_comp_self_pos B)

theorem continuous_graphJac (k m : ℕ) :
    Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  have hc : Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      (1 + (ContinuousLinearMap.adjoint B).comp B :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :=
    continuous_const.add ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)
  have heq : (fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) =
      fun B => √((1 + (ContinuousLinearMap.adjoint B).comp B :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)).det) := by
    funext B
    rfl
  rw [heq]
  exact (ContinuousLinearMap.continuous_det.comp hc).sqrt

theorem GraphJacContinuous.proof : GraphJacContinuous.Statement := by
  intro k m A ε hε
  set g := fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
    graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) with hg
  have hgA : 0 < g A := graphJac_pos _
  set η := ε * g A / (1 + ε) with hη
  have hη0 : 0 < η := by positivity
  have hηe : (1 + ε) * η = ε * g A := by rw [hη]; field_simp
  obtain ⟨δ, hδ, hδη⟩ := Metric.continuous_iff.mp (continuous_graphJac k m) A η hη0
  refine ⟨δ / 2, half_pos hδ, fun B hB => ?_⟩
  have hd : dist B A < δ := by rw [dist_eq_norm]; linarith
  have h := hδη B hd
  rw [Real.dist_eq, abs_lt] at h
  change g B ≤ (1 + ε) * g A ∧ g A ≤ (1 + ε) * g B
  constructor
  · nlinarith
  · nlinarith

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set Filter Function Topology

open scoped ENNReal NNReal

noncomputable section

theorem WeightedAreaFormula.proof : WeightedAreaFormula.Statement := by
  intro E _ _ _ _ _ μ _ A f H hA hf hfin hint
  classical
  have hder : ∀ x ∈ A, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hf x hx).differentiableAt (hA.mem_nhds hx)).hasFDerivAt
  set B : Set E := {x ∈ A | (fderiv ℝ f x).det ≠ 0} with hBdef
  have hBA : B ⊆ A := sep_subset _ _

  have hBm : MeasurableSet B := by
    have hm : Measurable fun x => (fderiv ℝ f x).det :=
      ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ f)
    exact hA.measurableSet.inter (hm (measurableSet_singleton 0).compl)

  have hZ : μ (f '' {x ∈ A | (fderiv ℝ f x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hder x hx.1).hasFDerivWithinAt) (fun x hx => hx.2)

  let r : (E →L[ℝ] E) → ℝ≥0 := fun L => (‖L.inverse‖₊ + 1)⁻¹
  obtain ⟨t, L, htd, htm, hcov, happ, hL⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B (fderiv ℝ f)
      (fun x hx => (hder x hx.1).hasFDerivWithinAt) r (fun _ => inv_ne_zero (by positivity))
  set P : ℕ → Set E := fun n => B ∩ t n with hPdef
  have hPm : ∀ n, MeasurableSet (P n) := fun n => hBm.inter (htm n)
  have hPd : Pairwise (Disjoint on P) := fun m n hmn =>
    (htd hmn).mono inter_subset_right inter_subset_right
  have hPA : ∀ n, P n ⊆ A := fun n => inter_subset_left.trans hBA
  have hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (fderiv ℝ f x) (P n) x := fun n x hx =>
    (hder x (hPA n hx)).hasFDerivWithinAt
  have hinj : ∀ n, InjOn f (P n) := by
    intro n
    rcases (P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact injOn_empty f
    obtain ⟨y, hy, hLy⟩ := hL ⟨x, hx.1⟩ n
    set e := (fderiv ℝ f y).toContinuousLinearEquivOfDetNeZero hy.2
    have he : (e : E →L[ℝ] E) = L n := by
      rw [hLy]; exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have ha := happ n
    rw [← he] at ha
    refine ha.injOn ?_
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    right
    have hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ := by
      simp only [r, ContinuousLinearMap.inverse_equiv]
    rw [hr]
    have hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
      rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
      intro h0
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      apply hz
      simpa using congrArg (fun T : E →L[ℝ] E => T (e z)) h0
    exact (inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)
  have hBU : B = ⋃ n, P n := by
    rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
  have himg : ∀ n, MeasurableSet (f '' P n) := fun n =>
    measurable_image_of_fderivWithin (hPm n) (hderP n) (hinj n)

  let g : ℕ → E → ℝ := fun n y => H (invFunOn f (P n) y)
  have hgP : ∀ n, ∀ x ∈ P n, g n (f x) = H x := fun n x hx =>
    congrArg H (hinj n (invFunOn_mem ⟨x, hx, rfl⟩) hx (invFunOn_eq ⟨x, hx, rfl⟩))
  let F : ℕ → E → ℝ := fun n => (f '' P n).indicator (g n)
  have hFint : ∀ n, Integrable (F n) μ := fun n =>
    (integrable_indicator_iff (himg n)).2
      ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ (hPm n) (hderP n) (hinj n)
        (g n)).2 ((hint.mono_set (hPA n)).congr_fun
          (fun x hx => by simp only [smul_eq_mul, hgP n x hx]) (hPm n)))
  have hFint_eq : ∀ n, ∫ y, F n y ∂μ = ∫ x in P n, |(fderiv ℝ f x).det| * H x ∂μ := fun n => by
    calc ∫ y, F n y ∂μ = ∫ y in f '' P n, g n y ∂μ := integral_indicator (himg n)
      _ = ∫ x in P n, |(fderiv ℝ f x).det| • g n (f x) ∂μ :=
        integral_image_eq_integral_abs_det_fderiv_smul μ (hPm n) (hderP n) (hinj n) (g n)
      _ = ∫ x in P n, |(fderiv ℝ f x).det| * H x ∂μ :=
        setIntegral_congr_fun (hPm n) fun x hx => by simp only [smul_eq_mul, hgP n x hx]
  have hFlint : ∀ n, ∫⁻ y, ‖F n y‖ₑ ∂μ = ∫⁻ x in P n, ‖|(fderiv ℝ f x).det| * H x‖ₑ ∂μ :=
    fun n => by
    calc ∫⁻ y, ‖F n y‖ₑ ∂μ = ∫⁻ y, (f '' P n).indicator (fun z => ‖g n z‖ₑ) y ∂μ :=
          lintegral_congr fun y => enorm_indicator_eq_indicator_enorm (g n) y
      _ = ∫⁻ y in f '' P n, ‖g n y‖ₑ ∂μ := lintegral_indicator (himg n) _
      _ = ∫⁻ x in P n, ENNReal.ofReal |(fderiv ℝ f x).det| * ‖g n (f x)‖ₑ ∂μ :=
        lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hPm n) (hderP n) (hinj n)
          (fun z => ‖g n z‖ₑ)
      _ = ∫⁻ x in P n, ‖|(fderiv ℝ f x).det| * H x‖ₑ ∂μ := by
        refine setLIntegral_congr_fun (hPm n) fun x hx => ?_
        simp only [hgP n x hx, enorm_mul, Real.enorm_eq_ofReal_abs, abs_abs]
  have hsumlint : ∑' n, ∫⁻ y, ‖F n y‖ₑ ∂μ ≠ ∞ := by
    simp_rw [hFlint]
    rw [← lintegral_iUnion hPm hPd, ← hBU]
    exact (lt_of_le_of_lt (lintegral_mono_set hBA) (hasFiniteIntegral_iff_enorm.1 hint.2)).ne

  have hinjT : ∀ y, InjOn (fun n => invFunOn f (P n) y) {n | y ∈ f '' P n} := by
    intro y m hm n hn hmn
    by_contra hne
    refine Set.disjoint_left.1 (hPd hne) (invFunOn_mem hm) ?_
    simp only at hmn
    rw [hmn]; exact invFunOn_mem hn
  have hT : ∀ y, {n | y ∈ f '' P n}.Finite := by
    intro y
    refine Set.Finite.of_finite_image ((hfin y).subset ?_) (hinjT y)
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨hPA n (invFunOn_mem hn), invFunOn_eq hn⟩
  have hsum : ∀ y, HasSum (fun n => F n y) (∑ n ∈ (hT y).toFinset, F n y) := fun y =>
    hasSum_sum_of_ne_finset_zero fun n hn =>
      show (f '' P n).indicator (g n) y = 0 from
        indicator_of_notMem (s := f '' P n) (fun h => hn ((hT y).mem_toFinset.2 h)) (g n)

  have hae : ∀ᵐ y ∂μ, ∑' n, F n y = ∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy
    have hbij : BijOn (fun n => invFunOn f (P n) y) {n | y ∈ f '' P n}
        {x | x ∈ A ∧ f x = y} := by
      refine ⟨fun n hn => ⟨hPA n (invFunOn_mem hn), invFunOn_eq hn⟩, hinjT y, ?_⟩
      rintro x ⟨hxA, hxy⟩
      have hxB : x ∈ B := ⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩
      obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hxB)
      have hxP : x ∈ P n := ⟨hxB, hn⟩
      have hyn : y ∈ f '' P n := ⟨x, hxP, hxy⟩
      exact ⟨n, hyn, hinj n (invFunOn_mem hyn) hxP ((invFunOn_eq hyn).trans hxy.symm)⟩
    rw [(hsum y).tsum_eq]
    change _ = ∑ᶠ (x : E) (_ : x ∈ {x | x ∈ A ∧ f x = y}), H x
    rw [← finsum_mem_eq_of_bijOn _ hbij
      (f := fun n => H (invFunOn f (P n) y)) (fun n _ => rfl),
      finsum_mem_eq_finite_toFinset_sum _ (hT y)]
    exact Finset.sum_congr rfl fun n hn =>
      indicator_of_mem (s := f '' P n) ((hT y).mem_toFinset.1 hn) (g n)

  have hGm : AEStronglyMeasurable (fun y => ∑' n, F n y) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (integrable_finsetSum (Finset.range N) fun n _ => hFint n).1)
      (ae_of_all _ fun y => (hsum y).summable.hasSum.tendsto_sum_nat)
  have hGfin : HasFiniteIntegral (fun y => ∑' n, F n y) μ := by
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ y, ‖∑' n, F n y‖ₑ ∂μ ≤ ∫⁻ y, ∑' n, ‖F n y‖ₑ ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [(hsum y).tsum_eq]
          exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)
      _ = ∑' n, ∫⁻ y, ‖F n y‖ₑ ∂μ := lintegral_tsum fun n => (hFint n).1.enorm
      _ < ∞ := hsumlint.lt_top

  have hIA : ∫ x in A, |(fderiv ℝ f x).det| * H x ∂μ =
      ∫ x in B, |(fderiv ℝ f x).det| * H x ∂μ :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA.measurableSet hBA fun x hx => by
      have h0 : (fderiv ℝ f x).det = 0 := by
        by_contra h; exact hx.2 ⟨hx.1, h⟩
      simp [h0]
  have hBint : IntegrableOn (fun x => |(fderiv ℝ f x).det| * H x) (⋃ n, P n) μ := by
    rw [← hBU]; exact hint.mono_set hBA
  refine ⟨Integrable.congr (⟨hGm, hGfin⟩ : Integrable (fun y => ∑' n, F n y) μ) hae, ?_⟩
  rw [← integral_congr_ae hae, integral_tsum (fun n => (hFint n).1) hsumlint, hIA, hBU]
  simp_rw [hFint_eq]
  exact (hasSum_integral_iUnion hPm hPd hBint).tsum_eq

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalGermIrreducible.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I →
      GermIrreducibleAt (zeroSetIn I) w

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
