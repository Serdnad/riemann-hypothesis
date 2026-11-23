module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle046
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle381
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle373
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle163
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle374
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle152
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
open scoped InnerProductSpace

namespace GlobalTheory.TensorTrace

section Hilbert

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_eq_zero_of_mem_closure_span {S : Set H} {a : H} (h : ∀ x ∈ S, ⟪x, a⟫_ℂ = 0)
    {x : H} (hx : x ∈ (Submodule.span ℂ S).topologicalClosure) : ⟪x, a⟫_ℂ = 0 := by
  have hle : (Submodule.span ℂ S).topologicalClosure ≤ (ℂ ∙ a)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    intro y hy
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h y hy)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hx)

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_orthonormal (L : W →ₗ[ℂ] H) (hL : Function.Injective L) (Z : Submodule ℂ W)
    [FiniteDimensional ℂ Z] :
    ∃ (n : ℕ) (z : Fin n → W), (∀ j, z j ∈ Z) ∧ Orthonormal ℂ (fun j => L (z j)) ∧
      (∀ x ∈ Z, L x = ∑ j, ⟪L (z j), L x⟫_ℂ • L (z j)) ∧
      (∀ (f : W →ₗ[ℂ] W) (hf : ∀ x ∈ Z, f x ∈ Z),
        LinearMap.trace ℂ Z (f.restrict hf) = ∑ j, ⟪L (z j), L (f (z j))⟫_ℂ) := by
  let LZ := L ∘ₗ Z.subtype
  have hLZ : Function.Injective LZ := hL.comp Subtype.val_injective
  let e := LinearEquiv.ofInjective LZ hLZ
  haveI : FiniteDimensional ℂ (LinearMap.range LZ) := LinearEquiv.finiteDimensional e
  let b := stdOrthonormalBasis ℂ (LinearMap.range LZ)
  have he : ∀ x : Z, ((e x : LinearMap.range LZ) : H) = L x := fun x => rfl
  have hb : ∀ j, L ((e.symm (b j) : Z) : W) = (b j : H) := fun j => by
    rw [← he, e.apply_symm_apply]
  refine ⟨_, fun j => ((e.symm (b j) : Z) : W), fun j => (e.symm (b j)).2, ?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro j k
    simp only [hb]
    rw [← Submodule.coe_inner]
    exact orthonormal_iff_ite.1 b.orthonormal j k
  · intro x hx
    have h1 := congrArg (fun v : LinearMap.range LZ => (v : H)) (b.sum_repr' (e ⟨x, hx⟩))
    simp only [Submodule.coe_sum, Submodule.coe_smul, he] at h1
    simp only [hb]
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_inner, he]
  · intro f hf
    rw [← LinearMap.trace_conj' _ e, LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_inner, hb, LinearEquiv.conj_apply]
    rfl

end Hilbert

section Tensor

variable {ι : Type} [Fintype ι] {Hs : ι → Type} [∀ i, NormedAddCommGroup (Hs i)]
  [∀ i, InnerProductSpace ℂ (Hs i)] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evalAt (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (u : ∀ i, Hs i) : W →ₗ[ℂ] H where
  toFun w := T w u
  map_add' a b := by simp
  map_smul' c a := by simp

theorem evalAt_apply (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (u : ∀ i, Hs i) (w : W) :
    evalAt T u w = T w u := rfl

variable {T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H} {β : W → W → ℂ}

theorem beta_eq (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {u : ∀ i, Hs i} (hu : ∀ i, ⟪u i, u i⟫_ℂ = 1) (w w' : W) :
    β w w' = ⟪evalAt T u w', evalAt T u w⟫_ℂ := by
  rw [evalAt_apply, evalAt_apply, hβ]
  simp only [hu, Finset.prod_const_one, mul_one]

theorem evalAt_injective (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {u : ∀ i, Hs i} (hu : ∀ i, ⟪u i, u i⟫_ℂ = 1) (hT : Function.Injective T) :
    Function.Injective (evalAt T u) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => hT ?_
  rw [map_zero]
  ext y
  have h1 : β w w = 0 := by rw [beta_eq hβ hu, hw, inner_zero_left]
  have h2 : ⟪T w y, T w y⟫_ℂ = 0 := by rw [hβ, h1, zero_mul]
  simpa using inner_self_eq_zero.1 h2

variable [CompleteSpace H]

theorem starProjection_tensor
    (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {z : W} (hz : β z z = 1) (w : W) (y : ∀ i, Hs i) :
    (Submodule.span ℂ {x | ∃ y', x = T z y'}).topologicalClosure.starProjection (T w y) = β w z • T z y := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun x hx => ?_
  · exact Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, rfl⟩))
  · rw [inner_eq_zero_symm]
    refine inner_eq_zero_of_mem_closure_span ?_ hx
    rintro _ ⟨y', rfl⟩
    rw [inner_sub_right, inner_smul_right, hβ, hβ, hz, one_mul, sub_self]

theorem starProjection_eq_zero_tensor {z : W} {v : H} (hv : ∀ y, ⟪T z y, v⟫_ℂ = 0) :
    (Submodule.span ℂ {x | ∃ y', x = T z y'}).topologicalClosure.starProjection v = 0 := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) fun x hx => ?_
  rw [sub_zero, inner_eq_zero_symm]
  exact inner_eq_zero_of_mem_closure_span (by rintro _ ⟨y, rfl⟩; exact hv y) hx

end Tensor

theorem hasTrace_finiteRank_tensor : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Type) [AddCommGroup W] [Module ℂ W] (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (β : W → W → ℂ), (∀ w w' y y', inner ℂ (T w' y') (T w y) = β w w' * ∏ i, inner ℂ (y' i) (y i)) → Function.Injective T → (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = ⊤ → ∀ (A : W →ₗ[ℂ] W) (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A c → ∀ Z : Submodule ℂ W, FiniteDimensional ℂ Z → LinearMap.range A ≤ Z → (∀ w, (∀ z ∈ Z, β w z = 0) → A w = 0) → ∀ (B : ∀ i, Hs i →L[ℂ] Hs i) (b : ι → ℂ), (∀ i, HasTrace (B i) (b i)) → ∀ X : H →L[ℂ] H, (∀ w y, X (T w y) = T (A w) fun i => B i (y i)) → HasTrace X (c * ∏ i, b i) := by
  intro ι _ _ Hs _ _ _ H _ _ _ W _ _ T β hβ hT hdense A c hA Z _ hAZ hA0 B b hB X hX
  by_cases hnt : ∀ i, Nontrivial (Hs i)
  · obtain ⟨u, hu⟩ : ∃ u : ∀ i, Hs i, ∀ i, ⟪u i, u i⟫_ℂ = 1 := by
      have hv : ∀ i, ∃ v : Hs i, v ≠ 0 := fun i => @exists_ne _ (hnt i) 0
      choose v hv using hv
      refine ⟨fun i => ((‖v i‖ : ℂ)⁻¹) • v i, fun i => ?_⟩
      rw [inner_self_eq_norm_sq_to_K, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 (hv i))]
      simp
    obtain ⟨n, z, hzZ, hon, hdec, htr⟩ :=
      exists_orthonormal (evalAt T u) (evalAt_injective hβ hu hT) Z
    have hzz : ∀ j, β (z j) (z j) = 1 := fun j => by
      have := orthonormal_iff_ite.1 hon j j
      simp only [if_pos rfl] at this
      rw [beta_eq hβ hu]
      exact this
    have hAw : ∀ w, A w = ∑ j, β w (z j) • A (z j) := by
      intro w
      have hperp : ∀ k, ⟪evalAt T u (z k), evalAt T u (w - ∑ j, β w (z j) • z j)⟫_ℂ = 0 := by
        intro k
        have h1 := hon.inner_right_fintype (fun j => β w (z j)) k

        rw [map_sub, map_sum, inner_sub_right]
        simp only [map_smul]
        rw [h1, beta_eq hβ hu, sub_self]
      have h0 : A (w - ∑ j, β w (z j) • z j) = 0 := by
        refine hA0 _ fun x hx => ?_
        rw [beta_eq hβ hu, hdec x hx, sum_inner]
        exact Finset.sum_eq_zero fun k _ => by rw [inner_smul_left, hperp k, mul_zero]

      rw [map_sub, map_sum, sub_eq_zero] at h0
      simpa only [map_smul] using h0
    let P : Fin n → H →L[ℂ] H := fun j =>
      (Submodule.span ℂ {x | ∃ y', x = T (z j) y'}).topologicalClosure.starProjection
    have hXsum : X = ∑ j, X ∘L P j := by
      refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 hdense) ?_
      rintro _ ⟨w, y, rfl⟩
      rw [ContinuousLinearMap.sum_apply]
      simp only [ContinuousLinearMap.comp_apply, P, starProjection_tensor hβ (hzz _), map_smul, hX]

      rw [hAw w, map_sum, ContinuousMultilinearMap.sum_apply]
      simp only [map_smul, ContinuousMultilinearMap.smul_apply]
    have hj : ∀ j, GlobalTheory.OpTrace.HasTrace (X ∘L P j) (β (A (z j)) (z j) * ∏ i, b i) := fun j =>
      GlobalTheory.T.hilbertTensor_traceClass_hasTrace_prod ι Hs H (T (z j)) (T (A (z j))) (β (A (z j)) (z j)) (β (A (z j)) (A (z j)))
        (fun y y' => by rw [hβ, hzz, one_mul]) (fun y y' => hβ _ _ _ _) (fun y y' => hβ _ _ _ _) B b hB
        (X ∘L P j)
        (fun y => by
          simp only [ContinuousLinearMap.comp_apply, P, starProjection_tensor hβ (hzz j), hzz j, one_smul, hX])
        (fun v hv => by
          simp only [ContinuousLinearMap.comp_apply, P, starProjection_eq_zero_tensor hv, map_zero])
    have hf : ∀ x ∈ Z, A x ∈ Z := fun x _ => hAZ (LinearMap.mem_range_self A x)
    have hc : c = ∑ j, β (A (z j)) (z j) := by
      have h1 := GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le W A Z hAZ
      rw [← hA.2, h1.2, htr A hf]
      simp only [beta_eq hβ hu]
    rw [hXsum]
    refine ⟨GlobalTheory.OpTrace.isTraceClass_sum _ fun j _ => (hj j).1, ?_⟩
    rw [GlobalTheory.OpTrace.trace_sum _ fun j _ => (hj j).1, hc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => (hj j).2
  · push_neg at hnt
    obtain ⟨i0, hi0⟩ := hnt
    have hTz : ∀ w y, T w y = 0 := fun w y => (T w).map_coord_zero i0 (Subsingleton.elim _ _)
    have hH : ∀ v : H, v = 0 := by
      intro v
      have hv : v ∈ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure := by
        rw [hdense]; exact Submodule.mem_top
      have := inner_eq_zero_of_mem_closure_span (a := v)
        (by rintro _ ⟨w, y, rfl⟩; rw [hTz, inner_zero_left]) hv
      exact inner_self_eq_zero.1 this
    have hX0 : X = 0 := ContinuousLinearMap.ext fun v => hH _
    have hB0 : B i0 = 0 := ContinuousLinearMap.ext fun v => Subsingleton.elim _ _
    have hb0 : b i0 = 0 := by rw [← (hB i0).2, hB0, GlobalTheory.OpTrace.trace_zero]
    rw [hX0, Finset.prod_eq_zero (Finset.mem_univ i0) hb0, mul_zero]
    exact ⟨GlobalTheory.OpTrace.isTraceClass_zero, GlobalTheory.OpTrace.trace_zero⟩

end GlobalTheory.TensorTrace
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.representation_transport_topGroupEquiv : ∀ (G G' : Type) [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G'] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G'] (Φ : G ≃ₜ* G') (ν : Measure G) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), (σ.IsIrreducible → Representation.IsIrreducible (σ.comp Φ.symm.toMulEquiv.toMonoidHom)) ∧ (IsAdmissible σ → IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W)) ∧ ∀ (f : G → ℂ) (f' : G' → ℂ), (∀ g, f' (Φ g) = f g) → ∀ A, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (ν.map Φ) (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W) f' A ↔ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ f A := by
  first | exact @GlobalTheory.TransportIso.irreducible_admissible_integralOp_transport | exact GlobalTheory.TransportIso.irreducible_admissible_integralOp_transport | (intros; apply GlobalTheory.TransportIso.irreducible_admissible_integralOp_transport <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.adelicIsometryConj_differ_by_innerAutomorphism : ∀ (D : D7) (V V' : HSp D) (j j₀ : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Φ Φ₀ : GfC V ≃ₜ* GfC V'), GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsIsom V V' (Formalism.L2.Herm.Af D.host.F) j → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsIsom V V' (Formalism.L2.Herm.Af D.host.F) j₀ → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy V V' j Φ → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy V V' j₀ Φ₀ → ∃ b : GfC V, ∀ g, Φ g = Φ₀ (b * g * b⁻¹) := by
  first | exact @GlobalTheory.InnerTwist.conj_inner | exact GlobalTheory.InnerTwist.conj_inner | (intros; apply GlobalTheory.InnerTwist.conj_inner <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorHeis

open GlobalTheory.SplitScalar GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

theorem wAt_wAt (p : Place D) (w : WO S T) : wAt p (wAt p w) = wAt p w := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p]

theorem wAt_off {P : Finset (Place D)} {w r : WO S T} (h : w = ∑ q ∈ P, wAt q w + r) {p : Place D} (hp : p ∉ P) :
    wAt p w = wAt p r := by
  have e : wAt p w = wAt p (∑ q ∈ P, wAt q w + r) := by rw [← h]
  simp only [wAt_eq_smul, smul_add, Finset.smul_sum, smul_smul] at e ⊢
  rw [e, Finset.sum_eq_zero, zero_add]
  intro q hq
  rw [(GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q (fun hpq => hp (hpq ▸ hq)), zero_smul]

theorem wAt_on {P : Finset (Place D)} {w r : WO S T} (h : w = ∑ q ∈ P, wAt q w + r) {p : Place D} (hp : p ∈ P) :
    wAt p r = 0 := by
  have e : wAt p w = wAt p (∑ q ∈ P, wAt q w + r) := by rw [← h]
  simp only [wAt_eq_smul, smul_add, Finset.smul_sum, smul_smul] at e ⊢
  rw [Finset.sum_eq_single p (fun q _ hqp => by rw [(GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q (Ne.symm hqp), zero_smul])
    (fun hn => absurd hp hn), (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p] at e
  exact add_left_cancel (e.symm.trans (add_zero _).symm)

theorem symplO_wAt (p : Place D) (x y : WO S T) : symplO S T (wAt p x) y = symplO S T x (wAt p y) := by
  rw [wAt_eq_smul, wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p]

private theorem symplO_sum_wAt_left (P : Finset (Place D)) (x y : WO S T) :
    symplO S T (∑ q ∈ P, wAt q x) y = ∑ q ∈ P, symplO S T (wAt q x) (wAt q y) := by
  induction P using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.SplitScalar.symplO_zero_left]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, GlobalTheory.LatVac.symplO_add_left, ih, ← symplO_wAt, wAt_wAt]

private theorem wAt_add' (p : Place D) (x y : WO S T) : wAt p (x + y) = wAt p x + wAt p y := by
  rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

theorem symplO_split {P : Finset (Place D)} {w r w' r' : WO S T} (h : w = ∑ q ∈ P, wAt q w + r)
    (h' : w' = ∑ q ∈ P, wAt q w' + r') :
    symplO S T w w' = ∑ q ∈ P, symplO S T (wAt q w) (wAt q w') + symplO S T r r' := by
  have hr : ∀ q ∈ P, wAt q r = 0 := fun q hq => wAt_on h hq
  have hr' : ∀ q ∈ P, wAt q r' = 0 := fun q hq => wAt_on h' hq
  have hB : ∀ q ∈ P, wAt q (∑ q' ∈ P, wAt q' w') = wAt q w' := by
    intro q hq
    have e : wAt q w' = wAt q (∑ q' ∈ P, wAt q' w' + r') := by rw [← h']
    rw [wAt_add', hr' q hq, add_zero] at e
    exact e.symm
  have s1 : ∑ q ∈ P, symplO S T (wAt q w) (wAt q (∑ q' ∈ P, wAt q' w')) =
      ∑ q ∈ P, symplO S T (wAt q w) (wAt q w') :=
    Finset.sum_congr rfl fun q hq => by rw [hB q hq]
  have s2 : ∑ q ∈ P, symplO S T (wAt q w) (wAt q r') = 0 :=
    Finset.sum_eq_zero fun q hq => by rw [hr' q hq, GlobalTheory.SplitScalar.symplO_zero_right]
  have s3 : ∑ q ∈ P, symplO S T (wAt q w') (wAt q r) = 0 :=
    Finset.sum_eq_zero fun q hq => by rw [hr q hq, GlobalTheory.SplitScalar.symplO_zero_right]
  conv_lhs => rw [h, h']
  rw [GlobalTheory.LatVac.symplO_add_left, GlobalTheory.LatVac.symplO_add_right, GlobalTheory.LatVac.symplO_add_right,
    symplO_sum_wAt_left, symplO_sum_wAt_left, GlobalTheory.SplitScalar.symplO_skew S T (∑ q ∈ P, wAt q w') r,
    symplO_sum_wAt_left, s1, s2, s3, add_zero, neg_zero, zero_add]

variable {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem cocycle_two (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {u u' : WO S T}
    (hu : u ∈ latO S T ΛS ΛT fun _ => True) (hu' : u' ∈ latO S T ΛS ΛT fun _ => True) :
    ψ (symplOH S T (2 • u) (2 • u')) = 1 := by
  have hd : ψ (symplO S T u u') = 1 :=
    ((GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hS hT).1 u (GlobalTheory.SplitScalar.latO_fin hu)).mp hu u' hu'
  rw [two_nsmul, two_nsmul, GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_right,
    GlobalTheory.SplitScalar.symplOH_add_self, AddChar.map_add_eq_mul, hd, one_mul]

theorem wAt_mem {u : WO S T} (hu : u ∈ latO S T ΛS ΛT fun _ => True) (p : Place D) :
    wAt p u ∈ latO S T ΛS ΛT fun _ => True :=
  latO_mono (fun _ _ => trivial) (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu p).1

theorem wAt_two (p : Place D) (u : WO S T) : wAt p (2 • u) = 2 • wAt p u := by
  rw [two_nsmul, two_nsmul, wAt_eq_smul, wAt_eq_smul, smul_add]

private theorem eq_zero_of_add_self_eq_zero_AF {a : AF D.host.F} (h : a + a = 0) : a = 0 := by
  have h2 : IsUnit (2 : AF D.host.F) := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  rw [← two_mul] at h
  exact h2.mul_right_eq_zero.mp h

private theorem symplOH_eq_sum_wAt_add_of_decomp {P : Finset (Place D)} {w r w' r' : WO S T} (h : w = ∑ q ∈ P, wAt q w + r)
    (h' : w' = ∑ q ∈ P, wAt q w' + r') :
    symplOH S T w w' = ∑ q ∈ P, symplOH S T (wAt q w) (wAt q w') + symplOH S T r r' := by
  apply sub_eq_zero.mp
  apply eq_zero_of_add_self_eq_zero_AF
  rw [sub_add_sub_comm, GlobalTheory.SplitScalar.symplOH_add_self, add_add_add_comm, ← Finset.sum_add_distrib]
  simp only [GlobalTheory.SplitScalar.symplOH_add_self]
  rw [symplO_split h h', sub_self]

private theorem addChar_sum_eq_prod' (ψ : AddChar (AF D.host.F) ℂ) (s : Finset (Place D)) (g : Place D → AF D.host.F) :
    ψ (∑ p ∈ s, g p) = ∏ p ∈ s, ψ (g p) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, AddChar.map_add_eq_mul, ih]

theorem cocycle_prod (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (w w' : WO S T) :
    ∃ P : Finset (Place D), (∀ p ∉ P, ψ (symplOH S T (wAt p w) (wAt p w')) = 1) ∧
      ψ (symplOH S T w w') = ∏ p ∈ P, ψ (symplOH S T (wAt p w) (wAt p w')) := by
  classical
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w'
  obtain ⟨u, hu, hw⟩ := hP₀ (P₀ ∪ P₁) (fun _ hx => Finset.mem_union_left _ hx)
  obtain ⟨u', hu', hw'⟩ := hP₁ (P₀ ∪ P₁) (fun _ hx => Finset.mem_union_right _ hx)
  refine ⟨P₀ ∪ P₁, fun p hp => ?_, ?_⟩
  · rw [wAt_off hw hp, wAt_off hw' hp, wAt_two, wAt_two]
    exact cocycle_two hψ hS hT (wAt_mem hu p) (wAt_mem hu' p)
  · rw [symplOH_eq_sum_wAt_add_of_decomp hw hw', AddChar.map_add_eq_mul, cocycle_two hψ hS hT hu hu', mul_one,
      addChar_sum_eq_prod']

theorem isPure_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ w : WO S T, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => heisO ψ S T (wAt p w) (x p)) (heisO ψ S T w f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx w
  classical
  have hψ := base_std hB
  have hθ := base_inf hB
  have hf₀ := base_theta hB
  have hB' := hB
  unfold IsBase at hB'
  have hS : IsSelfDualC S ΛS := hB'.2.2.1
  have hT : IsSelfDualC T ΛT := hB'.2.2.2.1
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  unfold IsPure IsRestricted at hx ⊢
  obtain ⟨⟨hloc, hfin⟩, hf, hprod⟩ := hx
  have hxθ : ∀ p, IsThetaFunO ψ S T (x p) := fun p => by
    have hl := hloc p
    unfold IsLocal at hl
    exact hl.1
  have hneg : ∀ (p : Place D) (a : WO S T), wAt p (-a) = -wAt p a := fun p a => by
    rw [wAt_eq_smul, wAt_eq_smul, smul_neg]
  have hadd : ∀ (p : Place D) (a b : WO S T), wAt p (a + b) = wAt p a + wAt p b := fun p a b => by
    rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w
  obtain ⟨u, hu, hwu⟩ := hP₀ P₀ (Finset.Subset.refl _)
  have hvac : ∀ p, p ∉ P₀ → (∀ τ, p ≠ .inr τ) → heisO ψ S T (wAt p w) f₀ = f₀ := by
    intro p hp hτ
    rcases p with v | τ
    · have hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f₀ := base_vacAt hB (.inl v)
      rw [wAt_off hwu hp, wAt_two]
      refine hv.1 _ (latO_mono ?_ (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu (.inl v)).1)
      rintro v' ⟨-, hv'⟩
      exact Sum.inl_injective hv'
    · exact absurd rfl (hτ τ)
  have hfinV : {p : Place D | heisO ψ S T (wAt p w) f₀ ≠ f₀}.Finite := by
    refine ((P₀.finite_toSet).union (Set.finite_range (Sum.inr : D.what₂.Tau → Place D))).subset ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_range, not_or, not_exists] at hc
    exact hp (hvac p hc.1 fun τ h => hc.2 τ h.symm)
  refine ⟨⟨fun p => ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x p) (hxθ p)).2 p (hloc p)).1 w, ?_⟩,
    laws.1 w f hf, fun w' => ?_⟩
  · refine (hfin.union hfinV).subset ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hp
    show heisO ψ S T (wAt p w) (x p) = f₀
    rw [hc.1, hc.2]

  have hfac : ∀ p, ipO μ 𝓕 (heisO ψ S T (wAt p w) (x p)) (heisO ψ S T (wAt p w') f₀) =
      (starRingEnd ℂ) (ψ (symplOH S T (wAt p (-w)) (wAt p w'))) *
        ipO μ 𝓕 (x p) (heisO ψ S T (wAt p (-w + w')) f₀) := by
    intro p
    have I := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x p) (heisO ψ S T (wAt p (-w + w')) f₀) (hxθ p) (laws.1 _ f₀ hf₀)
    have J := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x p) (heisO ψ S T (wAt p w') f₀) (hxθ p) (laws.1 _ f₀ hf₀)
    rw [(J.2.2.2.2.2.2.1 (wAt p w)).2, laws.2.1, ← hneg, ← hadd, (I.2.2.1 _).2]
  obtain ⟨P, hP1, hP2⟩ := cocycle_prod hψ hS hT (-w) w'
  have hcfin : (Function.mulSupport fun p => (starRingEnd ℂ) (ψ (symplOH S T (wAt p (-w)) (wAt p w')))) ⊆ ↑P := by
    intro p hp
    by_contra hc
    simp only [Function.mem_mulSupport] at hp
    exact hp (by rw [hP1 p (fun h => hc (Finset.mem_coe.mpr h)), map_one])
  have hgfin := (hprod (-w + w')).1
  beta_reduce
  simp only [hfac]
  refine ⟨((P.finite_toSet.subset hcfin).union hgfin).subset (Function.mulSupport_mul _ _), ?_⟩
  have K0 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T w' f₀) hf (laws.1 _ _ hf₀)
  have K1 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T (-w + w') f₀) hf (laws.1 _ _ hf₀)
  rw [(K0.2.2.2.2.2.2.1 w).2, laws.2.1, (K1.2.2.1 _).2, (hprod (-w + w')).2, hP2, map_prod,
    finprod_mul_distrib (P.finite_toSet.subset hcfin) hgfin, finprod_eq_prod_of_mulSupport_subset _ hcfin]

end GlobalTheory.PlaceTensorHeis
end
