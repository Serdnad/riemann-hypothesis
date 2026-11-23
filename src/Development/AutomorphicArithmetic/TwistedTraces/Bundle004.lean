module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import GroundTheory.AutomorphicForms.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Trace
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

private lemma prj_idem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : prj V ∘L prj V = prj V := by
  ext v
  have h : prj V v ∈ V.topologicalClosure := by
    simp [prj]
  simpa [prj] using Submodule.starProjection_eq_self_iff.2 h

private lemma prj_comp_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {V W : Submodule ℂ H} (h : V ≤ W) : prj W ∘L prj V = prj V := by
  ext v
  have h1 : prj V v ∈ V.topologicalClosure := by
    simp [prj]
  have h2 : prj V v ∈ W.topologicalClosure := Submodule.topologicalClosure_mono h h1
  simpa [prj] using Submodule.starProjection_eq_self_iff.2 h2

private lemma prj_adj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : ContinuousLinearMap.adjoint (prj V) = prj V := by
  have : IsSelfAdjoint (prj V) := by
    simpa [prj] using isSelfAdjoint_starProjection V.topologicalClosure
  exact this

private lemma prj_comp_le' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {V W : Submodule ℂ H} (h : V ≤ W) : prj V ∘L prj W = prj V := by
  have := congrArg ContinuousLinearMap.adjoint (prj_comp_le h)
  simpa [ContinuousLinearMap.adjoint_comp, prj_adj] using this

theorem UpperTheory.trOn_sub_sum_eq_trace_comp_compression :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (E : ℝ → Submodule ℂ H) (S : Finset ℝ) (a : ℝ → ℂ) (F T : H →L[ℂ] H), (∀ x, E x ≤ W) → IsTraceClass (prj W ∘L T ∘L prj W) → trOn W (F ∘L prj W ∘L T) - ∑ x ∈ S, a x * trOn (E x) T = trace ((prj W ∘L F ∘L prj W - ∑ x ∈ S, a x • prj (E x)) ∘L (prj W ∘L T ∘L prj W)) := by
  intro H _ _ _ W E S a F T hE hT
  set P := prj W with hPdef
  set T0 := P ∘L T ∘L P with hT0
  have hPP : P ∘L P = P := prj_idem W
  let L : (H →L[ℂ] H) →ₗ[ℂ] ℂ :=
    { toFun := fun C => trace (C ∘L T0)
      map_add' := fun C D => by
        rw [ContinuousLinearMap.add_comp]
        exact trace_add (hT.comp_left C) (hT.comp_left D)
      map_smul' := fun c C => by
        rw [ContinuousLinearMap.smul_comp]
        exact trace_smul c (hT.comp_left C) }
  have hL : ∀ C, L C = trace (C ∘L T0) := fun _ => rfl
  have h1 : trOn W (F ∘L P ∘L T) = L (P ∘L F ∘L P) := by
    rw [hL, trOn]
    congr 1
    have : (P ∘L F ∘L P) ∘L T0 = P ∘L F ∘L (P ∘L P) ∘L T ∘L P := by
      simp only [hT0, ContinuousLinearMap.comp_assoc]
    rw [this, hPP]
    simp only [hPdef, ContinuousLinearMap.comp_assoc]
  have h2 : ∀ x, trOn (E x) T = L (prj (E x)) := by
    intro x
    set Q := prj (E x) with hQ
    have hQP : Q ∘L P = Q := prj_comp_le' (hE x)
    have hPQ : P ∘L Q = Q := prj_comp_le (hE x)
    have hQQ : Q ∘L Q = Q := prj_idem (E x)
    have hc := trace_comp_comm (hT.comp_left Q) Q
    have e1 : Q ∘L (Q ∘L T0) = Q ∘L T0 := by
      rw [← ContinuousLinearMap.comp_assoc, hQQ]
    have e2 : (Q ∘L T0) ∘L Q = Q ∘L T ∘L Q := by
      have : (Q ∘L T0) ∘L Q = (Q ∘L P) ∘L T ∘L (P ∘L Q) := by
        simp only [hT0, ContinuousLinearMap.comp_assoc]
      rw [this, hQP, hPQ]
    rw [e1, e2] at hc
    rw [hL, trOn, hc]
  rw [h1]
  simp only [h2]
  have h3 : L (P ∘L F ∘L P - ∑ x ∈ S, a x • prj (E x)) = trace ((P ∘L F ∘L P - ∑ x ∈ S, a x • prj (E x)) ∘L T0) := rfl

  rw [← h3, map_sub, map_sum]
  simp only [map_smul, smul_eq_mul]
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.prj_eigIn_of_eigenvector_prj :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (A : H →L[ℂ] H), IsClosed (W : Set H) → IsSelfAdjoint A → ∀ (v : H) (μ x : ℝ), A (prj W v) = (μ : ℂ) • prj W v → prj (eigIn W A x) v = if x = μ then prj W v else 0 := by
  intro H _ _ _ W A hW hA v μ x hv
  have hWc : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hPW : prj W v ∈ W := by
    have : prj W v ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hWc] at this
  have hperp : ∀ w ∈ W, inner ℂ w (v - prj W v) = 0 := by
    intro w hw
    have : v - prj W v ∈ W.topologicalClosureᗮ := Submodule.sub_starProjection_mem_orthogonal v
    exact this w (W.le_topologicalClosure hw)
  have hmem : ∀ w, w ∈ eigIn W A x ↔ w ∈ W ∧ A w = (x : ℂ) • w := by
    intro w
    simp [eigIn, Module.End.mem_eigenspace_iff]
  have key : ∀ u ∈ eigIn W A x, (∀ w ∈ eigIn W A x, inner ℂ w (v - u) = 0) →
      prj (eigIn W A x) v = u := by
    intro u hu h
    refine Submodule.eq_starProjection_of_mem_orthogonal
      ((eigIn W A x).le_topologicalClosure hu) ?_
    rw [Submodule.orthogonal_closure]
    exact fun w hw => h w hw
  split_ifs with hx
  · subst hx
    exact key _ ((hmem _).2 ⟨hPW, hv⟩) fun w hw => hperp w ((hmem w).1 hw).1
  · refine key 0 (Submodule.zero_mem _) fun w hw => ?_
    obtain ⟨hwW, hwA⟩ := (hmem w).1 hw
    have h1 : inner ℂ (A w) (prj W v) = inner ℂ w (A (prj W v)) :=
      hA.isSymmetric w (prj W v)
    rw [hwA, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
    have h2 : inner ℂ w (prj W v) = 0 := by
      by_contra h0
      exact hx (by exact_mod_cast mul_right_cancel₀ h0 h1)
    have h3 := hperp w hwW
    rw [inner_sub_right, h2] at h3
    rw [inner_sub_right, inner_zero_right]
    exact h3
end

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

section SlopeTestRemainingChoices

open scoped InnerProductSpace

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] : UpperTheory.ConvolutionTheory.C.prj E = E.starProjection := by
  have h : E.topologicalClosure = E := E.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  unfold UpperTheory.ConvolutionTheory.C.prj
  congr 1

private noncomputable def cprs (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) : Module.End ℂ E :=
  (E.orthogonalProjection : H →ₗ[ℂ] E) ∘ₗ (T : H →ₗ[ℂ] H) ∘ₗ E.subtype

private theorem cprs_coe (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) (v : E) :
    (cprs E T v : H) = E.starProjection (T v) := rfl

private theorem trOn_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) :
    UpperTheory.ConvolutionTheory.C.trOn E T = LinearMap.trace ℂ E (cprs E T) := by
  let b := stdOrthonormalBasis ℂ E
  rw [LinearMap.trace_eq_sum_inner _ b, UpperTheory.ConvolutionTheory.C.trOn, prj_eq, GroundTheory.Automorphic.trace]
  set S : H →L[ℂ] H := T ∘L E.starProjection with hS
  refine HasSum.tsum_eq ?_
  have h := hasSum_sum (s := Finset.univ) fun k _ =>
    (GroundTheory.Automorphic.stdHilbertBasis ℂ H).hasSum_inner_mul_inner (ContinuousLinearMap.adjoint S (b k : H)) (b k : H)
  convert (preTransparency := .reducible) h using 1
  · rfl
  · funext i
    rw [ContinuousLinearMap.comp_apply, b.starProjection_eq_sum_rankOne]
    simp only [ContinuousLinearMap.sum_apply, inner_sum, InnerProductSpace.rankOne_apply, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, Submodule.coe_inner, cprs_coe, hS, ContinuousLinearMap.comp_apply,
      Submodule.starProjection_eq_self_iff.2 (b k).2, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (b k).2]

private theorem trOn_of_restrict (E : Submodule ℂ H) [FiniteDimensional ℂ E] (B : H →L[ℂ] H) (b : Module.End ℂ E)
    (hb : ∀ v : E, ((b v : E) : H) = B v) : UpperTheory.ConvolutionTheory.C.trOn E B = LinearMap.trace ℂ E b := by
  rw [trOn_eq]
  congr 1
  ext v
  rw [cprs_coe, ← hb, Submodule.starProjection_eq_self_iff.2 (b v).2]

end SlopeTestRemainingChoices

theorem UpperTheory.trOn_restrict_and_eq_of_maps_into :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (X Y : Submodule ℂ H) [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y] (B : H →L[ℂ] H), (∀ b : Module.End ℂ X, (∀ v : X, ((b v : X) : H) = B v) → trOn X B = LinearMap.trace ℂ X b) ∧ (X ≤ Y → (∀ v ∈ Y, B v ∈ X) → trOn Y B = trOn X B) := by
  intro H _ _ _ X Y _ _ B
  refine ⟨fun b hb => trOn_of_restrict X B b hb, fun hXY hY => ?_⟩
  let p : Y →ₗ[ℂ] X := LinearMap.codRestrict X ((B : H →ₗ[ℂ] H) ∘ₗ Y.subtype) fun v => hY v v.2
  let i : X →ₗ[ℂ] Y := Submodule.inclusion hXY
  rw [trOn_of_restrict Y B (i ∘ₗ p) fun v => rfl, trOn_of_restrict X B (p ∘ₗ i) fun v => rfl]
  exact LinearMap.trace_comp_comm' p i
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.eigIn_finite_above_of_isCompactOperator :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (A : H →L[ℂ] H), IsClosed (W : Set H) → IsSelfAdjoint A → (∀ v ∈ W, A v ∈ W) → IsCompactOperator (A ∘L prj W) → ∀ η : ℝ, 0 < η → {x : ℝ | η < x ∧ eigIn W A x ≠ ⊥}.Finite ∧ ∀ x : ℝ, η < x → FiniteDimensional ℂ (eigIn W A x) := by
  intro H _ _ _ W A hW hA hAW hC η hη
  have hWc : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hPW : ∀ v, prj W v ∈ W := by
    intro v
    have : prj W v ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hWc] at this
  have hperp : ∀ v, ∀ w ∈ W, inner ℂ w (v - prj W v) = 0 := by
    intro v w hw
    have : v - prj W v ∈ W.topologicalClosureᗮ := Submodule.sub_starProjection_mem_orthogonal v
    exact this w (W.le_topologicalClosure hw)
  have hfix : ∀ w ∈ W, prj W w = w := by
    intro w hw
    refine Submodule.eq_starProjection_of_mem_orthogonal
      (W.le_topologicalClosure hw) ?_
    simp
  have hmem : ∀ x : ℝ, ∀ w, w ∈ eigIn W A x ↔ w ∈ W ∧ A w = (x : ℂ) • w := by
    intro x w
    simp [eigIn, Module.End.mem_eigenspace_iff]
  have hB : IsSelfAdjoint (A ∘L prj W) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro u v
    change inner ℂ (A (prj W u)) v = inner ℂ u (A (prj W v))
    have h1 : inner ℂ (A (prj W u)) v = inner ℂ (A (prj W u)) (prj W v) := by
      have := hperp v _ (hAW _ (hPW u))
      rw [inner_sub_right, sub_eq_zero] at this
      exact this
    have h2 : inner ℂ u (A (prj W v)) = inner ℂ (prj W u) (A (prj W v)) := by
      have := hperp u _ (hAW _ (hPW v))
      rw [inner_sub_right, sub_eq_zero] at this
      rw [← inner_conj_symm, this, inner_conj_symm]
    rw [h1, h2]
    exact hA.isSymmetric _ _
  have hle : ∀ x : ℝ, eigIn W A x ≤
      Module.End.eigenspace ((A ∘L prj W : H →L[ℂ] H) : H →ₗ[ℂ] H) (x : ℂ) := by
    intro x w hw
    obtain ⟨hwW, hwA⟩ := (hmem x w).1 hw
    rw [Module.End.mem_eigenspace_iff]
    change A (prj W w) = _
    rw [hfix w hwW, hwA]
  have hfin := GroundTheory.Automorphic.CompactSelfAdjoint.finite_eigenvalues_norm_ge hC hB hη
  refine ⟨?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun x : ℝ => (x : ℂ)) (hfin.subset ?_)
      (Complex.ofReal_injective.injOn)
    rintro _ ⟨x, ⟨hx, hne⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hle x hw, hw0⟩
    · have : η ≤ |x| := hx.le.trans (le_abs_self x)
      simpa using this
  · intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by
      have : x ≠ 0 := (hη.trans hx).ne'
      exact_mod_cast this
    haveI : FiniteDimensional ℂ (Module.End.eigenspace ((A ∘L prj W : H →L[ℂ] H) : H →ₗ[ℂ] H) (x : ℂ)) :=
      ContinuousLinearMap.finite_dimensional_eigenspace hC _ hx0
    exact Submodule.finiteDimensional_of_le (hle x)
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.exists_hilbertBasis_prj_eigenvectors_of_isCompactOperator :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (A : H →L[ℂ] H), IsClosed (W : Set H) → IsSelfAdjoint A → (∀ v ∈ W, A v ∈ W) → IsCompactOperator (A ∘L prj W) → ∃ (s : Set H) (b : HilbertBasis s ℂ H), ∀ i, ∃ μ : ℝ, A (prj W (b i)) = (μ : ℂ) • prj W (b i) := by
  intro H _ _ _ W A hW hsa hinv hK
  have hcl : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hmem : ∀ u, prj W u ∈ W := fun u =>
    hcl.le (Submodule.starProjection_apply_mem W.topologicalClosure u)
  have hfix : ∀ w ∈ W, prj W w = w := fun w hw =>
    Submodule.starProjection_eq_self_iff.mpr (W.le_topologicalClosure hw)
  have hPsym : ∀ x y : H, inner ℂ (prj W x) y = inner ℂ x (prj W y) := fun x y =>
    Submodule.inner_starProjection_left_eq_right W.topologicalClosure x y
  have hAsym : ∀ x y : H, inner ℂ (A x) y = inner ℂ x (A y) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  have hBsa : IsSelfAdjoint (A ∘L prj W) := by
    refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun u v => ?_
    change inner ℂ (A (prj W u)) v = inner ℂ u (A (prj W v))
    calc inner ℂ (A (prj W u)) v = inner ℂ (prj W (A (prj W u))) v := by
          rw [hfix _ (hinv _ (hmem u))]
      _ = inner ℂ (A (prj W u)) (prj W v) := hPsym _ _
      _ = inner ℂ (prj W u) (A (prj W v)) := hAsym _ _
      _ = inner ℂ u (prj W (A (prj W v))) := hPsym _ _
      _ = inner ℂ u (A (prj W v)) := by rw [hfix _ (hinv _ (hmem v))]
  obtain ⟨s, b, hb, hev⟩ :=
    GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors hK hBsa
  refine ⟨s, b, fun i => ?_⟩
  have hbi : b i ∈ s := by
    rw [hb]
    exact i.2
  obtain ⟨μ, hμ⟩ := hev (b i) hbi
  have hμ' : A (prj W (b i)) = (μ : ℂ) • b i := hμ
  refine ⟨μ, ?_⟩
  have h2 : prj W (A (prj W (b i))) = (μ : ℂ) • prj W (b i) := by
    rw [hμ', map_smul]
  rw [← h2, hfix _ (hinv _ (hmem _))]
end
