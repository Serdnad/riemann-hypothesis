module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.SemistableReduction.Bundle002

@[expose] public section

section

namespace GlobalTheory.UnitaryChar

section Mat

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : ℕ}

theorem root {S A : Matrix (Fin n) (Fin n) ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hA : A.PosSemidef)
    (h : A * S * A = S) : ∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ R * R = A ∧ R * S * R = S := by
  obtain ⟨R, hR, hRR, hu⟩ : ∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ R * R = A ∧
      ∀ T : Matrix (Fin n) (Fin n) ℂ, T.PosSemidef → T * T = A → R = T :=
    ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      fun T hT e => CFC.sqrt_unique e hT.nonneg⟩
  have a1 : R * (R * (S * A * S)) = 1 := by
    rw [← Matrix.mul_assoc, hRR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, h1]
  have a2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (Matrix.isUnit_det_of_right_inverse a1)
  have a3 : R⁻¹ * R⁻¹ = S * A * S := by
    calc R⁻¹ * R⁻¹ = R⁻¹ * R⁻¹ * (R * (R * (S * A * S))) := by rw [a1, Matrix.mul_one]
      _ = R⁻¹ * (R⁻¹ * R) * R * (S * A * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [a2, Matrix.mul_one, a2, Matrix.one_mul]
  have a4 : R = S * R⁻¹ * S := by
    refine hu _ ?_ ?_
    · have := hR.inv.conjTranspose_mul_mul_same S
      rwa [h2] at this
    · calc S * R⁻¹ * S * (S * R⁻¹ * S) = S * (R⁻¹ * (S * S) * R⁻¹) * S := by simp only [Matrix.mul_assoc]
        _ = (S * S) * A * (S * S) := by rw [h1, Matrix.mul_one, a3, ← h1]; simp only [Matrix.mul_assoc]
        _ = A := by rw [h1, Matrix.mul_one, Matrix.one_mul]
  refine ⟨R, hR, hRR, ?_⟩
  calc R * S * R = S * R⁻¹ * S * S * R := by rw [← a4]
    _ = S * (R⁻¹ * (S * S) * R) := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h1, Matrix.mul_one, a2, Matrix.mul_one]

theorem polar_std {S U : Matrix (Fin n) (Fin n) ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hU : Uᴴ * S * U = S) :
    ∃ K Q : Matrix (Fin n) (Fin n) ℂ, Kᴴ * S * K = S ∧ S * K = K * S ∧ Qᴴ * S * Q = S ∧ S * Q * S * Q = 1 ∧
      U = K * Q * Q := by
  have hS : ∀ X : Matrix (Fin n) (Fin n) ℂ, S * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b1 : (S * Uᴴ * S) * U = 1 := by
    rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hU, h1]
  have b2 : U * S * Uᴴ = S := by
    have := congrArg (· * S) (mul_eq_one_comm.1 b1)
    simpa only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨P, hP, hPP, hPS⟩ := root h1 h2 (Matrix.posSemidef_conjTranspose_mul_self U) (by
    calc Uᴴ * U * S * (Uᴴ * U) = Uᴴ * (U * S * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = S := by rw [b2, hU])
  obtain ⟨Q, hQ, hQQ, hQS⟩ := root h1 h2 hP hPS
  have hP' : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (S * (P * X)) = S * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPS]
  have c0 : (U * (S * P * S))ᴴ = S * P * S * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, h2, hP.isHermitian.eq, Matrix.mul_assoc]
  have c1 : (U * (S * P * S))ᴴ * S * (U * (S * P * S)) = S := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * S * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hU]; simp only [Matrix.mul_assoc, hS, hP']
  have c2 : (U * (S * P * S))ᴴ * (U * (S * P * S)) = 1 := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hPP]; simp only [Matrix.mul_assoc, hS, hP', h1]
  refine ⟨U * (S * P * S), Q, c1, ?_, by rw [hQ.isHermitian.eq, hQS], ?_, ?_⟩
  · generalize U * (S * P * S) = K at c1 c2
    calc S * K = (K * Kᴴ) * S * K := by rw [mul_eq_one_comm.1 c2, Matrix.one_mul]
      _ = K * (Kᴴ * S * K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [c1]
  · rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hQS, h1]
  · rw [Matrix.mul_assoc _ Q, hQQ, Matrix.mul_assoc, Matrix.mul_assoc S, Matrix.mul_assoc S, hPS, h1, Matrix.mul_one]

theorem polar {G s u : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.IndefR.Datum.IsCartanInv G s) (hu : uᴴ * G * u = G) :
    ∃ k q : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G ∧ s * k = k * s ∧ qᴴ * G * q = G ∧ s * q * s * q = 1 ∧
      u = k * q * q := by
  obtain ⟨h1, h2, h3⟩ := h
  have hG : Gᴴ = G := by
    have e : sᴴ * Gᴴ = G * s := by rw [← Matrix.conjTranspose_mul, h3.isHermitian.eq]
    have e1 : sᴴ * sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    rw [← Matrix.one_mul Gᴴ, ← e1, Matrix.mul_assoc, e, ← Matrix.mul_assoc, h2]
  obtain ⟨B, hB, hBB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ, Bᴴ = B ∧ B * B = G * s :=
    ⟨CFC.sqrt (G * s), (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ h3.posSemidef.nonneg⟩
  have hd : IsUnit B.det := by
    have : IsUnit (B * B).det := by rw [hBB]; exact (Matrix.isUnit_iff_isUnit_det _).1 h3.isUnit
    rw [Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨C, hC, i1, i2⟩ : ∃ C : Matrix (Fin n) (Fin n) ℂ, Cᴴ = C ∧ B * C = 1 ∧ C * B = 1 :=
    ⟨B⁻¹, by rw [Matrix.conjTranspose_nonsing_inv, hB], Matrix.mul_nonsing_inv B hd, Matrix.nonsing_inv_mul B hd⟩
  have j1 : ∀ X : Matrix (Fin n) (Fin n) ℂ, B * (C * X) = X := fun X => by
    rw [← Matrix.mul_assoc, i1, Matrix.one_mul]
  have j2 : ∀ X : Matrix (Fin n) (Fin n) ℂ, C * (B * X) = X := fun X => by
    rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  obtain ⟨S, hs, hGS⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, s = C * S * B ∧ G = B * S * B :=
    ⟨B * s * C, by simp only [Matrix.mul_assoc, j2, i2, Matrix.mul_one], by
      simp only [Matrix.mul_assoc, i2, Matrix.mul_one]
      rw [← Matrix.mul_assoc, hBB, Matrix.mul_assoc, h1, Matrix.mul_one]⟩
  have hS : S = C * G * C := by rw [hGS]; simp only [Matrix.mul_assoc, j2, i1, Matrix.mul_one]
  have s1 : S * S = 1 := by
    have := congrArg (fun X => B * X * C) h1
    simpa only [hs, Matrix.mul_assoc, j1, i1, Matrix.mul_one] using this
  have s2 : Sᴴ = S := by
    rw [hS]; simp only [Matrix.conjTranspose_mul, hC, hG, Matrix.mul_assoc]
  have tr : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * S * X = S → (C * X * B)ᴴ * G * (C * X * B) = G := fun X hX => by
    calc _ = B * (Xᴴ * S * X) * B := by
          rw [hGS]; simp only [Matrix.conjTranspose_mul, hC, hB, Matrix.mul_assoc, j1, j2]
      _ = G := by rw [hX, hGS]
  obtain ⟨K, Q, k1, k2, q1, q2, e⟩ := polar_std (U := B * u * C) s1 s2 (by
    calc _ = C * (uᴴ * (B * S * B) * u) * C := by
          simp only [Matrix.conjTranspose_mul, hC, hB, Matrix.mul_assoc]
      _ = S := by rw [← hGS, hu, ← hS])
  refine ⟨C * K * B, C * Q * B, tr K k1, ?_, tr Q q1, ?_, ?_⟩
  · have := congrArg (fun X => C * X * B) k2
    simpa only [hs, Matrix.mul_assoc, j1] using this
  · have := congrArg (fun X => C * X * B) q2
    simpa only [hs, Matrix.mul_assoc, j1, Matrix.one_mul, i2] using this
  · have := congrArg (fun X => C * X * B) e
    simpa only [Matrix.mul_assoc, j1, j2, i2, Matrix.mul_one] using this

end Mat

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem compAt_mt_mul {D : D7} (θ : InfFam D) (W : HSp D) (τ : D.what₂.Tau) (g g' : GA D W) :
    compAt θ τ (Formalism.L2.Theta.mt W (g * g')) =
      compAt θ τ (Formalism.L2.Theta.mt W g) * compAt θ τ (Formalism.L2.Theta.mt W g') :=
  Matrix.map_mul (L := Formalism.L2.Theta.mt W g) (M := Formalism.L2.Theta.mt W g') (f := (θ τ).comp (infPart D))

theorem compAt_mt_one {D : D7} (θ : InfFam D) (W : HSp D) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 :=
  Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)

theorem ext_real {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) {g g' : GA D W} (hg : g ∈ GinfC W)
    (hg' : g' ∈ GinfC W) (h : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W g) = compAt θ τ (Formalism.L2.Theta.mt W g')) :
    g = g' := by
  refine mul_inv_eq_one.1 ((GlobalTheory.UnitarySplit.real_finite_split D W).2.2.1 _ (mul_mem hg (inv_mem hg'))
    ((GlobalTheory.SmoothForms.RealPts.glue θ hθ W).1 _ fun τ => ?_))
  show compAt θ τ (Formalism.L2.Theta.mt W (g * g'⁻¹)) = 1
  rw [compAt_mt_mul, h, ← compAt_mt_mul, mul_inv_cancel, compAt_mt_one]

theorem char_eq_one : ∀ (D : D7) (θ : InfFam D) (W : HSp D), IsInfFam θ → ∀ (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → ∀ c : GA D W → ℂ, (∀ u ∈ GinfC W, ∀ u' ∈ GinfC W, c (u * u') = c u * c u') → (∀ u ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W u) = compAt θ τ (Formalism.L2.Theta.mt W u) * s τ) → c u = 1) → ∀ u ∈ GinfC W, c u = 1 := by
  intro D θ W hθ s hs c hm hK u hu
  have gl : ∀ x : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ τ, (x τ)ᴴ * gramAt D W τ * x τ = gramAt D W τ) →
      ∃ g ∈ GinfC W, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W g) = x τ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ W).2
  choose k q k1 k2 q1 q2 e using fun τ => polar (u := compAt θ τ (Formalism.L2.Theta.mt W u)) (hs τ)
    (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W u τ)
  obtain ⟨k', hk, ek⟩ := gl k k1
  obtain ⟨q', hq, eq⟩ := gl q q1
  obtain ⟨σ, hσ, eσ⟩ := gl s fun τ => (hs τ).2.1
  have ck : c k' = 1 := hK _ hk fun τ => by rw [ek, k2]
  have cσ : c σ = 1 := hK _ hσ fun τ => by rw [eσ]
  have c1 : c 1 = 1 := hK _ (one_mem _) fun τ => by rw [compAt_mt_one, Matrix.mul_one, Matrix.one_mul]
  have e1 : u = k' * q' * q' := ext_real hθ W hu (mul_mem (mul_mem hk hq) hq) fun τ => by
    rw [compAt_mt_mul, compAt_mt_mul, ek, eq, e]
  have e2 : σ * q' * σ * q' = 1 := ext_real hθ W (mul_mem (mul_mem (mul_mem hσ hq) hσ) hq) (one_mem _) fun τ => by
    rw [compAt_mt_mul, compAt_mt_mul, compAt_mt_mul, eσ, eq, q2, compAt_mt_one]
  rw [← e2, hm _ (mul_mem (mul_mem hσ hq) hσ) _ hq, hm _ (mul_mem hσ hq) _ hσ, hm _ hσ _ hq, cσ, one_mul,
    mul_one] at c1
  rw [e1, hm _ (mul_mem hk hq) _ hq, hm _ hk _ hq, ck, one_mul, c1]

end GlobalTheory.UnitaryChar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.FockPos

variable {D : D7}

def frAt {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  fr.1.map (tauE D τ)

def zCo (θ : InfFam D) {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (w : WO S T) :
    Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank :=
  fun τ => (frAt frT τ)⁻¹ * compAt θ τ w * frAt frS τ

def gaussO (θ : InfFam D) {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (w : WO S T) : ℂ :=
  Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ))

theorem cartan_eq_one {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) (hG : G.PosDef) : s = 1 := by
  obtain ⟨hss, -, hP⟩ := h
  have key : ∀ v : Fin k → ℂ, (s - 1) *ᵥ v = 0 := by
    intro v
    by_contra hx
    set x := (s - 1) *ᵥ v with hxdef
    have hsx : s *ᵥ x = -x := by
      rw [hxdef, Matrix.mulVec_mulVec, Matrix.mul_sub, hss, Matrix.mul_one, ← neg_sub, Matrix.neg_mulVec]
    have h1 := hP.dotProduct_mulVec_pos hx
    have h2 := hG.dotProduct_mulVec_pos hx
    rw [← Matrix.mulVec_mulVec, hsx, Matrix.mulVec_neg, dotProduct_neg] at h1
    have := add_pos h1 h2
    simp at this
  have : s - 1 = 0 := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  exact sub_eq_zero.1 this

theorem frAt_det_ne {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : (frAt fr τ).det ≠ 0 := by
  have e : (frAt fr τ).det = tauE D τ fr.1.det := (RingHom.map_det (tauE D τ) fr.1).symm
  rw [e, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 fr.isUnit).ne_zero

theorem frAt_on {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1) (τ : D.what₂.Tau) :
    (frAt fr τ)ᴴ * gramAt D S τ * frAt fr τ = 1 := by
  have hs : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) := fun x => by
    have := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x
  have h2 := congrArg (fun M => M.map (tauE D τ)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  rw [← h2, frAt, gramAt]
  congr 2
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  exact (hs _).symm

theorem gramAt_posDef {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1) (τ : D.what₂.Tau) :
    (gramAt D S τ).PosDef := by
  have hMd : IsUnit (frAt fr τ).det := isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)
  have hM : IsUnit (frAt fr τ) := (Matrix.isUnit_iff_isUnit_det _).2 hMd
  have hMHd : IsUnit (frAt fr τ)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hMd.star
  have h1 := frAt_on fr h τ
  have e : ((frAt fr τ)⁻¹)ᴴ * 1 * (frAt fr τ)⁻¹ = gramAt D S τ := by
    calc ((frAt fr τ)⁻¹)ᴴ * 1 * (frAt fr τ)⁻¹
        = ((frAt fr τ)ᴴ)⁻¹ * ((frAt fr τ)ᴴ * gramAt D S τ * frAt fr τ) * (frAt fr τ)⁻¹ := by
          rw [h1, Matrix.conjTranspose_nonsing_inv]
      _ = (((frAt fr τ)ᴴ)⁻¹ * (frAt fr τ)ᴴ) * gramAt D S τ * (frAt fr τ * (frAt fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = gramAt D S τ := by
          rw [Matrix.nonsing_inv_mul _ hMHd, Matrix.mul_nonsing_inv _ hMd, Matrix.one_mul, Matrix.mul_one]
  rw [← e]
  refine Matrix.PosDef.one.conjTranspose_mul_mul_same ?_
  exact Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hM)

theorem cart_one {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1)
    {s : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} (hs : ∀ τ, IsCartanInv (gramAt D S τ) (s τ)) : s = fun _ => 1 := by
  funext τ
  have h1 : (gramAt D S τ).PosDef := gramAt_posDef fr h τ
  exact cartan_eq_one (hs τ) h1

end GlobalTheory.FockPos
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.RapidDecayReal

theorem height_le (a : ℕ) (N : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (K : ℝ)
    (hb : ∀ i, r i ≤ K ∧ (r i)⁻¹ ≤ K) :
    (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ (1 + 2 * a * K) ^ N := by
  have h0 : 0 ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hr i).le)
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (inv_pos.2 (hr i)).le)
    linarith
  apply pow_le_pow_left₀ h0
  have h1 : ∑ i, r i ≤ ∑ _i : Fin a, K := Finset.sum_le_sum (fun i _ => (hb i).1)
  have h2 : ∑ i, (r i)⁻¹ ≤ ∑ _i : Fin a, K := Finset.sum_le_sum (fun i _ => (hb i).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
  linarith

theorem char_ge (a : ℕ) (lam : Fin a → ℝ) (L : ℕ) (hL : ∑ i, |lam i| ≤ L) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i) (K : ℝ) (hK : 1 ≤ K) (hb : ∀ i, r i ≤ K ∧ (r i)⁻¹ ≤ K) :
    (K ^ L)⁻¹ ≤ ∏ i, r i ^ lam i := by
  have hK0 : 0 < K := by linarith
  have hi : ∀ i, K ^ (-|lam i|) ≤ r i ^ lam i := by
    intro i
    rcases le_or_gt 0 (lam i) with h | h
    · rw [abs_of_nonneg h, Real.rpow_neg hK0.le, ← Real.inv_rpow hK0.le]
      apply Real.rpow_le_rpow (inv_nonneg.2 hK0.le) _ h
      rw [inv_le_comm₀ hK0 (hr i)]; exact (hb i).2
    · rw [abs_of_neg h, neg_neg]
      have e1 : K ^ lam i = (K⁻¹) ^ (-lam i) := by
        rw [Real.inv_rpow hK0.le, Real.rpow_neg hK0.le, inv_inv]
      have e2 : r i ^ lam i = ((r i)⁻¹) ^ (-lam i) := by
        rw [Real.inv_rpow (hr i).le, Real.rpow_neg (hr i).le, inv_inv]
      rw [e1, e2]
      apply Real.rpow_le_rpow (inv_nonneg.2 hK0.le) _ (by linarith)
      exact inv_anti₀ (hr i) (hb i).1
  calc (K ^ L)⁻¹ = K ^ (-(L : ℝ)) := by rw [Real.rpow_neg hK0.le, Real.rpow_natCast]
    _ ≤ K ^ (∑ i, -|lam i|) := by
        apply Real.rpow_le_rpow_of_exponent_le hK
        rw [Finset.sum_neg_distrib]; linarith
    _ = ∏ i, K ^ (-|lam i|) := Real.rpow_sum_of_pos hK0 _ _
    _ ≤ ∏ i, r i ^ lam i :=
        Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg hK0.le _) (fun i _ => hi i)

theorem key (a : ℕ) (lam : Fin a → ℝ) (L N : ℕ) (hL : ∑ i, |lam i| ≤ L) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hb : ∀ i, r i ≤ C0 * ρ ^ a ∧ (r i)⁻¹ ≤ C0 * ρ ^ a) :
    (ρ ^ (a * N + a * L))⁻¹ * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤
      ((1 + 2 * a * C0) ^ N * C0 ^ L) * ∏ i, r i ^ lam i := by
  set P := ρ ^ a with hPdef
  have hP : 1 ≤ P := one_le_pow₀ hρ
  have hC00 : 0 < C0 := by linarith
  have hP0 : 0 < P := by linarith
  have hK : 1 ≤ C0 * P := by nlinarith
  have h1 := height_le a N r hr (C0 * P) hb
  have h2 := char_ge a lam L hL r hr (C0 * P) hK hb
  have h3 : (1 + 2 * (a : ℝ) * (C0 * P)) ^ N ≤ ((1 + 2 * a * C0) * P) ^ N := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hm : ρ ^ (a * N + a * L) = P ^ N * P ^ L := by
    rw [hPdef, ← pow_mul, ← pow_mul, ← pow_add]
  rw [hm]
  calc (P ^ N * P ^ L)⁻¹ * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N
      ≤ (P ^ N * P ^ L)⁻¹ * ((1 + 2 * a * C0) * P) ^ N :=
        mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)
    _ = ((1 + 2 * a * C0) ^ N * C0 ^ L) * ((C0 * P) ^ L)⁻¹ := by
        rw [mul_pow, mul_pow]
        field_simp
    _ ≤ ((1 + 2 * a * C0) ^ N * C0 ^ L) * ∏ i, r i ^ lam i :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

end GlobalTheory.RapidDecayReal


open GlobalTheory.RapidDecayReal in
theorem GlobalTheory.rapidDecay_real : ∀ (a : ℕ) (t : ℝ), 0 < t → ∀ (lam : Fin a → ℝ) (N : ℕ), ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i ∨ ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ (r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i := by
  intro a t ht lam N
  obtain ⟨C0, hC0, hC⟩ := GlobalTheory.T.coneCoordinate_le_pow_of_prod_eq_one a t ht
  set L := ⌈∑ i, |lam i|⌉₊ with hLdef
  have hL : ∑ i, |lam i| ≤ L := Nat.le_ceil _
  refine ⟨a * N + a * L, (1 + 2 * a * C0) ^ N * C0 ^ L, by positivity, ?_⟩
  intro r hr hcone hprod
  by_cases hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ r j
  · left
    have hb := hC r 1 hr hcone hprod le_rfl (fun i j hij => by rw [one_mul]; exact hall i j hij)
    have := key a lam L N hL C0 hC0 r hr 1 le_rfl hb
    simpa using this
  · right
    push_neg at hall
    obtain ⟨i, j, hij, hlt⟩ := hall
    set S := (Finset.univ : Finset (Fin a × Fin a)).filter (fun p => (p.2 : ℕ) = p.1 + 1) with hS
    have hne : S.Nonempty := ⟨(i, j), by simp [hS, hij]⟩
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun p => r p.1 / r p.2) hne
    have hpadj : (p.2 : ℕ) = p.1 + 1 := by simpa [hS] using hp
    have hij' : r i / r j ≤ r p.1 / r p.2 := hmax (i, j) (by simp [hS, hij])
    have hρ : 1 ≤ r p.1 / r p.2 := by
      have : 1 < r i / r j := by rw [one_lt_div (hr j)]; exact hlt
      linarith
    have hadj : ∀ i' j' : Fin a, (j' : ℕ) = i' + 1 → r i' ≤ (r p.1 / r p.2) * r j' := by
      intro i' j' h'
      have := hmax (i', j') (by simp [hS, h'])
      rwa [div_le_iff₀ (hr j')] at this
    have hb := hC r _ hr hcone hprod hρ hadj
    refine ⟨p.1, p.2, hpadj, ?_⟩
    have := key a lam L N hL C0 hC0 r hr _ hρ hb
    rw [← inv_div (r p.1) (r p.2), inv_pow]
    exact this
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem vanish_transfer_of_algClosure :
    ∀ (F σ : Type) [Field F] [Finite σ] (J : Ideal (MvPolynomial σ F)) (f : MvPolynomial σ F),
      (∀ x : σ → AlgebraicClosure F, (∀ g ∈ J, aeval x g = 0) → aeval x f = 0) →
      ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (x : σ → Ω), (∀ g ∈ J, aeval x g = 0) →
        aeval x f = 0 := by
  intro F σ _ _ J f hf Ω _ _ x hx
  have hrad : f ∈ J.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure F)]
    exact fun y hy => hf y hy
  obtain ⟨m, hm⟩ := hrad
  have h0 : (aeval x f) ^ m = 0 := by
    rw [← map_pow]
    exact hx _ hm
  exact IsNilpotent.eq_zero ⟨m, h0⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_base_element_negative_at_two_embeddings : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L], Module.finrank K L = 2 → ∀ σ : L →+* L, σ ≠ RingHom.id L → (∀ x : K, σ (algebraMap K L x) = algebraMap K L x) → (∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ ε ε' : L →+* ℂ, ε ≠ ε' → ε ≠ ComplexEmbedding.conjugate ε' → ∃ h : K, h ≠ 0 ∧ (ε (algebraMap K L h)).re < 0 ∧ (ε' (algebraMap K L h)).re < 0 ∧ (∀ φ : L →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' → φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ (algebraMap K L h)).re) ∧ ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : v.adicCompletion K ⊗[K] L, Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) h := by
  first | (exact @GlobalTheory.QuadSigns.exists_signs) | (exact GlobalTheory.QuadSigns.exists_signs) | (intros; apply GlobalTheory.QuadSigns.exists_signs  <;> assumption)
end
