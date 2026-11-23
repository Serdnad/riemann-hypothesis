module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow
import GroundTheory.AutomorphicForms.CuspidalAdmissible
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem prj_prj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : prj V ∘L prj V = prj V := by
  ext v
  simp only [prj, ContinuousLinearMap.comp_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

private theorem rhoL_prj {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) {k : GL (Fin n) (w.adicCompletion K)} (hk : k ∈ J) :
    rhoL μ w k ∘L prj (fixL μ w J) = prj (fixL μ w J) := by
  ext1 v
  have hle : (fixL μ w J).topologicalClosure ≤
      LinearMap.eqLocus (rhoL μ w k : LL μ →ₗ[ℂ] LL μ) LinearMap.id := by
    apply Submodule.topologicalClosure_minimal
    · unfold fixL fixF rhoL
      exact iInf₂_le (AdelicGLn.localEmbedding w k) (Subgroup.mem_map_of_mem _ hk)
    · exact isClosed_eq (rhoL μ w k).continuous continuous_id
  exact hle (Submodule.starProjection_apply_mem _ v)

private theorem hop_one {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) : Hop μ w J 1 = prj (fixL μ w J) := by
  have hs : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * 1)} =
      {QuotientGroup.mk 1} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, mul_one]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact QuotientGroup.eq.mpr (by simpa using hk)
    · rintro rfl
      exact ⟨1, J.one_mem, rfl⟩
  unfold Hop
  rw [hs, finsum_mem_singleton]
  apply rhoL_prj
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul J (1 : GL (Fin n) (w.adicCompletion K))
  rw [hh, one_mul]
  exact h.2

theorem UpperTheory.ConvolutionTheory.C.uiwPow :
    UpperTheory.ConvolutionTheory.C.UiwPow := by
  intro K _ _ n μ _ w ν hν j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, zero_smul, Uiw, GroundTheory.Automorphic.Parabolic.diagPow_zero, hop_one]
    rfl
  · rw [(UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w ν ν hν hν).2.1 j hj, Uiw, Hop, ContinuousLinearMap.comp_assoc, prj_prj]
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory.GM
open scoped Classical

namespace UpperTheory.ConvolutionTheory.C

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def sphOff (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (P : Finset (Pl K)) : Submodule ℂ (LL μ) :=
  ⨅ v ∉ P, fixL μ v (GLnLocal.integralGL (v.adicCompletion K) n)

def levOn (P : Finset (Pl K)) (U : ∀ v : Pl K, Subgroup (Gw n v)) : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
  levF fun v => if v ∈ P then U v else GLnLocal.integralGL (v.adicCompletion K) n

def FixLev : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (P : Finset (Pl K))
    (U : ∀ v : Pl K, Subgroup (Gw n v)), fixF μ (levOn P U) = sphOff μ P ⊓ ⨅ v ∈ P, fixL μ v (U v)

def OfinProd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (mf : Measure (AdelicGLn.FiniteAdelicGL K n)) [mf.IsHaarMeasure], mf (AdelicGLn.integralFiniteGL K n) = 1 →
    ∀ (r : ℕ) (w : Fin r → Pl K) [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))]
      (m : ∀ i, Measure (Gw n (w i))) (φ : ∀ i, Gw n (w i) → ℂ) (T : Fin r → LL μ →L[ℂ] LL μ) (e : TF K n),
      Function.Injective w → (∀ i, (m i).IsHaarMeasure ∧ m i (GLnLocal.integralGL ((w i).adicCompletion K) n) = 1) →
      (∀ i, Test (φ i)) → (∀ i, IsOloc μ (w i) (m i) (φ i) (T i)) →
      (∀ x, e x = if ∀ v ∉ Finset.univ.image w, finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n then
        ∏ i, φ i (finAt (w i) (finEmb K n x)) else 0) →
      Ofin μ mf e = (List.ofFn T).prod ∘L prj (sphOff μ (Finset.univ.image w))

def EigAdm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n) (x : ℝ), x ≠ 0 → ∀ (P : Finset (Pl K))
    (U : ∀ v : Pl K, Subgroup (Gw n v)), (∀ v ∈ P, CO (U v)) →
    FiniteDimensional ℂ ↥(eigIn (cuspidalL2 μ) (Oinf μ ν a) x ⊓ sphOff μ P ⊓ ⨅ v ∈ P, fixL μ v (U v))

def TermF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E)
    (n l : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := F) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup F n)) [ν.IsHaarMeasure]
    [∀ v : Pl F, MeasurableSpace (Gw n v)] [∀ v : Pl F, BorelSpace (Gw n v)] (m : ∀ v : Pl F, Measure (Gw n v)),
    (∀ v, (m v).IsHaarMeasure ∧ m v (GLnLocal.integralGL (v.adicCompletion F) n) = 1) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ (a : TI F n) (q : Pl F) (w₀ : PlacesOver E q) (S : Finset (Pl F)) (V : Submodule ℂ (LL μ))
      (τ : ∀ v : Pl F, SmIrr (Gw n v)) (x : ℝ), IsSummand μ V → 0 < x → (∀ v ∈ insert q S, Occurs μ V v (τ v)) →
      ∃ N : ℕ, (0 < N ↔ eigIn V (Oinf μ ν a) x ⊓ sphOff μ (insert q S) ≠ ⊥) ∧
        ∀ (L : Loc σ n q w₀) (e : Fin n → ℤ) (𝔣 : Side (Twist.id μ) l), L.S = S → Antitone e → IsSideF L ν a e 𝔣 →
        ∀ (j : ℕ) (sq : ℂ) (s : Pl F → ℂ), HasTrace (m q) (τ q).ρ ((iwCoset q (j • e)).indicator 1) sq →
          (∀ v ∈ S, HasTrace (m v) (τ v).ρ (L.f v) (s v)) →
          trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) = κ * x * N * sq * ∏ v ∈ S, s v

end UpperTheory.ConvolutionTheory.C
end
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.C.Sf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def locU (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) : UnitaryRep (Gw n w) (LL μ) :=
  (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom ((MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w))
    (MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1)

theorem locU_apply (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (g : Gw n w) : locU μ w g = rhoL μ w g := rfl

theorem fixU_locU (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (Gw n w)) :
    fixU (locU μ w) J = fixL μ w J := by
  ext v
  simp only [mem_fixU, fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
  constructor
  · rintro h _ ⟨u, hu, rfl⟩
    exact h u hu
  · intro h u hu
    exact h _ (Subgroup.mem_map_of_mem _ hu)

end UpperTheory.ConvolutionTheory.C.Sf
end
end
