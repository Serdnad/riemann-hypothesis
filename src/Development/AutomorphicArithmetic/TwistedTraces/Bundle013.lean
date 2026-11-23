module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle009
public import Mathlib.Topology.ContinuousMap.CompactlySupported
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle003
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.AutomorphicForms.WhittakerRelevance
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_deriv_orbit_le_of_polynomial_annihilated :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u : ℝ → H →L[ℂ] H) (p : ℝ → ℂ[X]) (M : ℝ) (v y : H), u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t x, ‖u t x‖ = ‖x‖) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t => u t v)) → HasDerivAt (fun t : ℝ => u t v) y 0 → (∀ t, aeval (u t) (p t) v = 0) → (∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M) → ‖y‖ ≤ M * ‖v‖ := by
  intro H _ _ u p M v y h0 hadd hiso hfin hy hp hM
  obtain ⟨E, hE⟩ : ∃ E : Submodule ℂ H, E = Submodule.span ℂ (Set.range fun t => u t v) := ⟨_, rfl⟩
  rw [← hE] at hfin
  haveI : FiniteDimensional ℂ E := hfin
  have hcomm : ∀ s t x, u s (u t x) = u t (u s x) := by
    intro s t x
    have h : u s * u t = u t * u s := by rw [← hadd, ← hadd, add_comm]
    exact DFunLike.congr_fun h x
  have h0' : ∀ a, u 0 a = a := by
    intro a
    rw [h0]
    rfl
  have hstab : ∀ s, ∀ x ∈ E, u s x ∈ E := by
    intro s x hx
    rw [hE] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact Submodule.subset_span ⟨s + t, by simp [hadd]⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
    | smul c a _ ha => simpa using Submodule.smul_mem _ c ha
  have hvE : v ∈ E := by
    rw [hE]
    exact Submodule.subset_span ⟨0, h0' v⟩
  have hclosed : IsClosed (E : Set H) := Submodule.closed_of_finiteDimensional E
  have hlim : ∀ w ∈ E, ∀ d, HasDerivAt (fun t : ℝ => u t w) d 0 → d ∈ E := by
    intro w hw d hd
    have ht := hasDerivAt_iff_tendsto_slope.1 hd
    refine hclosed.mem_of_tendsto ht (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    exact (E.restrictScalars ℝ).smul_mem _ (E.sub_mem (hstab t w hw) (hstab 0 w hw))
  have hsh : ∀ (s : ℝ) (w d : H), HasDerivAt (fun t : ℝ => u t w) d 0 →
      HasDerivAt (fun t : ℝ => u t (u s w)) (u s d) 0 := by
    intro s w d hd
    let LR : H →L[ℝ] H := (u s).restrictScalars ℝ
    have h1 : HasDerivAt (fun t : ℝ => LR (u t w)) (LR d) 0 :=
      LR.hasFDerivAt.comp_hasDerivAt 0 hd
    have h2 : (fun t : ℝ => LR (u t w)) = fun t => u t (u s w) := by
      funext t
      exact hcomm s t w
    rw [h2] at h1
    exact h1
  have hder : ∀ w ∈ E, ∃ d, HasDerivAt (fun t : ℝ => u t w) d 0 := by
    intro w hw
    rw [hE] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact ⟨u s y, hsh s v y hy⟩
    | zero => exact ⟨0, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨da, hda⟩ := ha
      obtain ⟨db, hdb⟩ := hb
      refine ⟨da + db, ?_⟩
      convert hda.add hdb using 1
      funext t
      simp
    | smul c a _ ha =>
      obtain ⟨da, hda⟩ := ha
      refine ⟨c • da, ?_⟩
      convert hda.const_smul c using 1
      funext t
      simp
  have hd : ∀ w : E, HasDerivAt (fun t : ℝ => u t (w : H)) (deriv (fun t : ℝ => u t (w : H)) 0) 0 := by
    intro w
    obtain ⟨d, hd⟩ := hder w w.2
    rw [hd.deriv]
    exact hd
  let D : Module.End ℂ E :=
    { toFun := fun w => ⟨deriv (fun t : ℝ => u t (w : H)) 0, hlim _ w.2 _ (hd w)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        refine (hd (a + b)).unique ?_
        convert (hd a).add (hd b) using 1
        · funext t
          simp
      map_smul' := by
        intro c a
        apply Subtype.ext
        refine (hd (c • a)).unique ?_
        convert (hd a).const_smul c using 1
        · funext t
          simp
      }
  let u' : ℝ → Module.End ℂ E := fun t => (u t : H →ₗ[ℂ] H).restrict (hstab t)
  have hu' : ∀ t (x : E), ((u' t x : E) : H) = u t (x : H) := fun t x => rfl
  have hD : ∀ x : E, ((D x : E) : H) = deriv (fun t : ℝ => u t (x : H)) 0 := fun x => rfl
  have haev : ∀ (t : ℝ) (q : ℂ[X]) (x : E), ((aeval (u' t) q x : E) : H) = aeval (u t) q (x : H) := by
    intro t q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [aeval_C]
    | add f g hf hg =>
      intro x
      simp [hf, hg]
    | monomial n a ih =>
      intro x
      have h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X := by ring
      rw [h1, map_mul (aeval (u' t)) (C a * X ^ n) X, map_mul (aeval (u t)) (C a * X ^ n) X, aeval_X, aeval_X, Module.End.mul_apply, ContinuousLinearMap.mul_apply, ih, hu']
  have hcq : ∀ (s t : ℝ) (q : ℂ[X]) (x : H), aeval (u t) q (u s x) = u s (aeval (u t) q x) := by
    intro s t q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [aeval_C]
    | add f g hf hg =>
      intro x
      simp [hf, hg]
    | monomial n a ih =>
      intro x
      have h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X := by ring
      rw [h1, map_mul, aeval_X, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hcomm t s, ih]
  have hkill : ∀ t, ∀ x ∈ E, aeval (u t) (p t) x = 0 := by
    intro t x hx
    rw [hE] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      show aeval (u t) (p t) (u s v) = 0
      rw [hcq, hp, map_zero]
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c a _ ha => simp [ha]
  have hder' : ∀ x : E, HasDerivAt (fun t : ℝ => u' t x) (D x) 0 := by
    intro x
    rw [hasDerivAt_iff_tendsto_slope]
    have h := hasDerivAt_iff_tendsto_slope.1 (hd x)
    rw [tendsto_subtype_rng]
    refine h.congr fun t => ?_
    simp [slope_def_module, hu']
  have hbound := UpperTheory.norm_generator_le_of_polynomial_annihilated E u' D p M
    (by
      ext x
      simp [hu', h0'])
    (by
      intro s t
      ext x
      simp [hu', hadd])
    (by
      intro t x
      exact hiso t x)
    hder'
    (by
      intro t
      ext x
      rw [haev]
      simpa using hkill t x x.2)
    hM ⟨v, hvE⟩
  have hDv : ((D ⟨v, hvE⟩ : E) : H) = y := by
    rw [hD]
    exact hy.deriv
  have hn : ‖D ⟨v, hvE⟩‖ = ‖y‖ := by
    rw [← hDv]
    rfl
  rw [hn] at hbound
  exact hbound
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.exists_finite_basis_leftInvariant_compactSupport :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (V : Subgroup G),
        IsOpen (V : Set G) → IsCompact (V : Set G) → ∀ S : Set G, IsCompact S →
        ∃ (m : ℕ) (b : Fin m → G) (e : Fin m → CompactlySupportedContinuousMap G ℂ),
          (∀ j, ∀ v ∈ V, ∀ h, e j (v * h) = e j h) ∧
          ∀ f : G → ℂ, (∀ v ∈ V, ∀ h, f (v * h) = f h) → (∀ h, h ∉ S → f h = 0) →
            ∀ h, f h = ∑ j, e j h * f (b j) := by
  intro G _ _ _ _ V hVo hVc S hS
  classical
  have hVcl : IsClosed (V : Set G) := Subgroup.isClosed_of_isOpen V hVo

  let W : G → Set G := fun b => {h | b * h⁻¹ ∈ V}
  have hWpre : ∀ b, W b = (fun h : G => b * h⁻¹) ⁻¹' (V : Set G) := fun b => rfl
  have hcont : ∀ b : G, Continuous (fun h : G => b * h⁻¹) := fun b =>
    continuous_const.mul continuous_inv
  have hWo : ∀ b, IsOpen (W b) := fun b => by
    rw [hWpre]; exact hVo.preimage (hcont b)
  have hWcl : ∀ b, IsClosed (W b) := fun b => by
    rw [hWpre]; exact hVcl.preimage (hcont b)
  have hWself : ∀ b, b ∈ W b := fun b => by
    show b * b⁻¹ ∈ V
    simpa using V.one_mem
  have hWK : ∀ b, W b ⊆ (fun v : G => v⁻¹ * b) '' (V : Set G) := fun b h hh =>
    ⟨b * h⁻¹, hh, by group⟩
  have hKc : ∀ b, IsCompact ((fun v : G => v⁻¹ * b) '' (V : Set G)) := fun b =>
    hVc.image (continuous_inv.mul continuous_const)
  have hWinv : ∀ b, ∀ v ∈ V, ∀ h, v * h ∈ W b ↔ h ∈ W b := fun b v hv h => by
    show b * (v * h)⁻¹ ∈ V ↔ b * h⁻¹ ∈ V
    have : b * (v * h)⁻¹ = b * h⁻¹ * v⁻¹ := by group
    rw [this]
    exact V.mul_mem_cancel_right (V.inv_mem hv)

  let E : G → CompactlySupportedContinuousMap G ℂ := fun b =>
    { toFun := (W b).indicator (fun _ => (1 : ℂ))
      continuous_toFun := (IsClopen.continuous_indicator ⟨hWcl b, hWo b⟩ continuous_const)
      hasCompactSupport' := by
        refine HasCompactSupport.intro (hKc b) (fun x hx => ?_)
        exact Set.indicator_of_notMem (fun hxW => hx (hWK b hxW)) _ }
  have hE : ∀ b h, E b h = (W b).indicator (fun _ => (1 : ℂ)) h := fun _ _ => rfl

  let q : G → Quotient (QuotientGroup.rightRel V) := fun h => Quotient.mk _ h
  have hq : ∀ x y : G, q x = q y ↔ x ∈ W y := fun x y => by
    show Quotient.mk _ x = Quotient.mk _ y ↔ y * x⁻¹ ∈ V
    rw [Quotient.eq]
    exact QuotientGroup.rightRel_apply
  obtain ⟨t, -, ht⟩ := hS.elim_nhds_subcover W (fun x _ => (hWo x).mem_nhds (hWself x))
  let T : Finset (Quotient (QuotientGroup.rightRel V)) := t.image q
  let ε := T.equivFin
  let b : Fin T.card → G := fun j => (ε.symm j).1.out
  have hqb : ∀ j, q (b j) = (ε.symm j).1 := fun j => Quotient.out_eq _
  refine ⟨T.card, b, fun j => E (b j), ?_, ?_⟩
  · intro j v hv h
    rw [hE, hE]
    by_cases hh : h ∈ W (b j)
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hWinv _ v hv h).2 hh)]
    · rw [Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (fun h' => hh ((hWinv _ v hv h).1 h'))]
  · intro f hfV hfS h
    have hfW : ∀ c x, x ∈ W c → f x = f c := fun c x hx => by
      have := hfV (c * x⁻¹) hx x
      simpa using this.symm
    by_cases hT : q h ∈ T
    · let j0 : Fin T.card := ε ⟨q h, hT⟩
      have hj0 : q (b j0) = q h := by
        rw [hqb]; simp [j0]
      have hmem : h ∈ W (b j0) := (hq _ _).1 hj0.symm
      rw [Finset.sum_eq_single j0]
      · rw [hE, Set.indicator_of_mem hmem, one_mul]
        exact hfW _ _ hmem
      · intro j _ hj
        have hnot : h ∉ W (b j) := fun hm => by
          apply hj
          have h1 : (ε.symm j).1 = q h := by rw [← hqb]; exact ((hq _ _).2 hm).symm
          have h2 : ε.symm j = ⟨q h, hT⟩ := Subtype.ext h1
          simp [j0, ← h2]
        rw [hE, Set.indicator_of_notMem hnot, zero_mul]
      · intro hj; exact absurd (Finset.mem_univ _) hj
    · have hhS : h ∉ S := fun hs => by
        have := ht hs
        simp only [Set.mem_iUnion] at this
        obtain ⟨x, hx, hxW⟩ := this
        exact hT (Finset.mem_image.2 ⟨x, hx, ((hq _ _).2 hxW).symm⟩)
      rw [hfS h hhS]
      symm
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have hnot : h ∉ W (b j) := fun hm => hT (by
        rw [(hq _ _).2 hm, hqb]; exact (ε.symm j).2)
      rw [hE, Set.indicator_of_notMem hnot, zero_mul]
end
