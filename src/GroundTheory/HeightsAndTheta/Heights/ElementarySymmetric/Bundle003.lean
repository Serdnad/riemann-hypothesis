module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
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
public import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Field

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def FrameGraphGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∃ (I₀ : Finset (Fin n)) (q : MvPolynomial (Fin n) ℂ), I₀.card = d ∧ q ∉ J ∧
        ∀ z ∈ zeroSetEuc J, eval (fun i => z i) q ≠ 0 →
          ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
            (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
              DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧
              zeroSetEuc J ∩ V = g '' Ω

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def FramePlaneGraph.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∃ (I₀ : Finset (Fin n)) (J' : Ideal (MvPolynomial (Fin n) ℂ)), I₀.card = d ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') < d ∧
        ∀ z ∈ zeroSetEuc J \ zeroSetEuc J', ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
          (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
            DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧
            (zeroSetEuc J \ zeroSetEuc J') ∩ V = g '' Ω

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace PointIntegral

variable {n : ℕ}

theorem zeroSet_ker_eval (p : Fin n → ℂ) :
    zeroSet (RingHom.ker (MvPolynomial.eval p)) = {p} := by
  ext x
  simp only [zeroSet, Set.mem_ofPred_eq, Set.mem_singleton_iff, RingHom.mem_ker]
  constructor
  · intro h
    funext i
    have := h (X i - C (p i)) (by simp)
    simpa [sub_eq_zero] using this
  · rintro rfl q hq
    exact hq

theorem isFiniteProjection (p : Fin n → ℂ) (A : Matrix (Fin 0) (Fin n) ℂ) :
    IsFiniteProjection (RingHom.ker (MvPolynomial.eval p)) A := by
  have hsurj : Function.Surjective (projHom (RingHom.ker (MvPolynomial.eval p)) A) := by
    intro q
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨C (eval p q), ?_⟩
    simp only [projHom, pullback, AlgHom.comp_apply, aeval_C, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, RingHom.mem_ker]
    simp
  refine ⟨?_, ?_⟩
  · intro P Q hPQ
    obtain ⟨a, rfl⟩ : ∃ a, P = C a := ⟨AddMonoidAlgebra.coeff P 0, (eq_C_of_isEmpty P)⟩
    obtain ⟨b, rfl⟩ : ∃ b, Q = C b := ⟨AddMonoidAlgebra.coeff Q 0, (eq_C_of_isEmpty Q)⟩
    simp only [projHom, pullback, AlgHom.comp_apply, aeval_C, Ideal.Quotient.mkₐ_eq_mk] at hPQ
    rw [Ideal.Quotient.eq, RingHom.mem_ker] at hPQ
    simp [sub_eq_zero] at hPQ
    rw [hPQ]
  · exact RingHom.Finite.of_surjective _ hsurj

theorem proof : PointIntegral.Statement := by
  intro n p f φ
  set J := RingHom.ker (MvPolynomial.eval p)
  have hZ : zeroSet J = {p} := zeroSet_ker_eval p
  have hex : ∃ A : Matrix (Fin 0) (Fin n) ℂ, IsFiniteProjection J A :=
    ⟨0, isFiniteProjection p 0⟩
  rw [varInt, dite_eq_left hex]
  set A := hex.choose
  have hsheet : IsSheetAt J A p (fun _ => p) := by
    refine ⟨Set.univ, isOpen_univ, trivial, differentiableOn_const _, rfl, ?_, Set.univ,
      Filter.univ_mem, ?_⟩
    · intro y _
      exact ⟨Subsingleton.elim _ _, by rw [hZ]; rfl⟩
    · intro x hx _
      rw [hZ] at hx
      exact hx.1
  have hfib : ∀ y, fibre J A y = {p} := by
    intro y
    ext x
    simp only [fibre, Set.mem_ofPred_eq, hZ, Set.mem_singleton_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _⟩⟩
  have hdens : ∀ y, chartDens J A f φ y = f p := by
    intro y
    rw [chartDens, sheetSum, hfib y, finsum_mem_singleton]
    have hs : ∃ s, IsSheetAt J A p s := ⟨_, hsheet⟩
    rw [dite_eq_left hs]
    simp [ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]
  rw [chartInt]
  simp_rw [hdens]
  simp [Measure.real, MeasureTheory.volume_pi]

end PointIntegral

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def FrameImplicitGraph.Statement : Prop :=
  ∀ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n)),
    (∀ k, eval (fun i => z i) (f k) = 0) → eval (fun i => z i) (frameJacobianDet b I f) ≠ 0 →
    ∀ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → z ∈ U →
      ∃ (Ω : Set (I → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n))) (g : (I → ℂ) → EuclideanSpace ℂ (Fin n)),
        IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ DifferentiableOn ℂ g Ω ∧
          (∀ w ∈ Ω, frameProj b I (g w) = w) ∧
          {x : EuclideanSpace ℂ (Fin n) | ∀ k, eval (fun i => x i) (f k) = 0} ∩ V = g '' Ω

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

theorem JacobianRankGeneric.kaehler_D_aeval {σ K : Type*} [Fintype σ] [Field K] [Algebra ℂ K] (x : σ → K)
    (f : MvPolynomial σ ℂ) :
    KaehlerDifferential.D ℂ K (aeval x f) =
      ∑ l, aeval x (pderiv l f) • KaehlerDifferential.D ℂ K (x l) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib, add_smul]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hp, Finset.smul_sum, smul_smul, map_add (f := _), add_smul,
      Finset.sum_add_distrib, pderiv_X, smul_eq_mul, Pi.single_apply]
    rw [add_left_inj]
    simp [apply_ite, ite_smul]

theorem JacobianRankGeneric.finrank_kaehler_eq_card {k K : Type} [Field k] [Field K] [Algebra k K] (s : Finset K)
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    (H : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K) :
    Module.finrank K Ω[K⁄k] = s.card := by
  have hx : AlgebraicIndependent k (fun i : s => (i : K)) := hs.1
  let _ : Algebra (MvPolynomial s k) K := (aeval (fun i : s => (i : K))).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial s k) K := IsScalarTower.of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra]
  let _ : Algebra (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) :=
    ((hx.aevalEquivField).toRingHom.comp (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)))).toAlgebra
  let e : FractionRing (MvPolynomial s k) ≃ₐ[MvPolynomial s k]
      IntermediateField.adjoin k (Set.range fun i : s => (i : K)) :=
    { hx.aevalEquivField with commutes' := fun q => rfl }
  have : Algebra.FormallyEtale (MvPolynomial s k) (FractionRing (MvPolynomial s k)) :=
    .of_isLocalization (nonZeroDivisors _)
  have : Algebra.FormallyEtale (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) :=
    .of_equiv e
  have : IsScalarTower (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K :=
    IsScalarTower.of_algebraMap_eq fun q => by
      change aeval (fun i : s => (i : K)) q =
        ((hx.aevalEquivField (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)) q) : _) : K)
      rw [hx.aevalEquivField_algebraMap_apply_coe]
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K := by
    convert! H <;> simp
  have : Algebra.FormallyEtale (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K :=
    .of_isSeparable _ K
  have : Algebra.FormallyEtale (MvPolynomial s k) K :=
    .comp (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K
  have : Module.Free (MvPolynomial s k) Ω[MvPolynomial s k⁄k] :=
    Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis k s)
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial s k) K).finrank_eq,
    Module.finrank_baseChange, Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis k s),
    Fintype.card_coe]

theorem JacobianRankGeneric.proof : JacobianRankGeneric.Statement := by
  classical
  intro n d J _ hd
  set A := MvPolynomial (Fin n) ℂ ⧸ J
  set K := FractionRing A

  let ψ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] K := (IsScalarTower.toAlgHom ℂ A K).comp (Ideal.Quotient.mkₐ ℂ J)
  let x : Fin n → K := fun l => ψ (X l)
  have hψ : ∀ f, ψ f = aeval x f := fun f => congrArg (fun φ => φ f) (MvPolynomial.aeval_unique ψ)
  have hgrad : ∀ f l, genericGradient J f l = aeval x (pderiv l f) := fun f l => hψ (pderiv l f)
  let Φ : (Fin n → K) →ₗ[K] Ω[K⁄ℂ] :=
    ∑ l, (LinearMap.proj l : (Fin n → K) →ₗ[K] K).smulRight (KaehlerDifferential.D ℂ K (x l))
  have hΦ : ∀ w, Φ w = ∑ l, w l • KaehlerDifferential.D ℂ K (x l) := fun w => by
    simp [Φ, LinearMap.sum_apply]

  have hker : Submodule.span K (genericGradient J '' (J : Set _)) ≤ LinearMap.ker Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h0 : aeval x f = 0 := by
      rw [← hψ]
      simp only [ψ, AlgHom.comp_apply]
      rw [show Ideal.Quotient.mkₐ ℂ J f = 0 from Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hΦ, hgrad]
    rw [← JacobianRankGeneric.kaehler_D_aeval, h0, map_zero]

  have hsurj : LinearMap.range Φ = ⊤ := by
    have hA : ∀ f, KaehlerDifferential.D ℂ K (ψ f) ∈ LinearMap.range Φ := fun f =>
      ⟨fun l => aeval x (pderiv l f), by rw [hΦ, hψ, JacobianRankGeneric.kaehler_D_aeval]⟩
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨u, v, _, rfl⟩ := IsFractionRing.div_surjective (A := A) a
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hf := hA f
    have hg := hA g
    change KaehlerDifferential.D ℂ K (ψ f / ψ g) ∈ _
    rw [Derivation.leibniz_div]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hg))

  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField ℂ K
  have hcard : s.card = d := by
    have h1 := hs.cardinalMk_eq_trdeg
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing ℂ (A := A) K
    rw [hd, ← h1, Cardinal.mk_coe_finset] at h2
    simp at h2
    exact_mod_cast h2.symm
  have hrank : Module.finrank K Ω[K⁄ℂ] = d := by
    rw [JacobianRankGeneric.finrank_kaehler_eq_card s hs H, hcard]

  have h1 := Submodule.finrank_mono hker
  have h2 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hsurj, finrank_top, hrank, Module.finrank_fin_fun] at h2
  change Module.finrank K (Submodule.span K (genericGradient J '' (J : Set _))) ≤ n - d
  calc _ ≤ _ := h1
    _ = n - d := by
      generalize Module.finrank K (LinearMap.ker Φ) = m at h2 ⊢
      omega

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial KaehlerDifferential TensorProduct IsLocalRing

theorem ConormalGenerationGeneric.proof : ConormalGenerationGeneric.Statement :=
  _root_.UpperTheory.Reformulated.B.Qf34.proof

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open GroundTheory.Heights₂.Heights (varInt SmoothNear euclPot contDiff_euclPot)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
open scoped ContDiff

def VarIntGraphCompact.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ)
    (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ),
    J.IsPrime → SmoothNear (zeroSet (graphIdeal J p)) F → HasCompactSupport F →
    (∀ k, SmoothNear (zeroSet (graphIdeal J p)) (Φ k)) →
      varInt (graphIdeal J p) e F Φ = varInt J e (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x))

end GroundTheory.Heights₂.Heights.Targets
end
end
