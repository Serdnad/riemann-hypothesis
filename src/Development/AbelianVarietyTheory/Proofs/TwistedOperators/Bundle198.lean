module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle743
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle095
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumDiagOrderEqOfIntegralTranslateIndicatorRelati
public import Formalism.LocalRingCardinality.Bundle006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle184
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle185
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle188
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle189
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.CoverContr

theorem inner_map_of_norm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : H →L[ℂ] H)
    (hA : ∀ x, ‖A x‖ = ‖x‖) (x y : H) : inner ℂ (A x) (A y) = inner ℂ x y := by
  let L : H →ₗᵢ[ℂ] H := ⟨A.toLinearMap, hA⟩
  exact L.inner_map_map x y

private theorem inner_unitary_apply_eq_inner_inv {G E : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : G →* E →L[ℂ] E) (hU : ∀ g x, ‖U g x‖ = ‖x‖) (g : G) (v w : E) :
    inner ℂ (U g v) w = inner ℂ v (U g⁻¹ w) := by
  have h1 : U g (U g⁻¹ w) = w := by
    have h := congrArg (fun f : E →L[ℂ] E => f w) (map_mul U g g⁻¹)
    simpa using h.symm
  conv_lhs => rw [← h1]
  exact inner_map_of_norm (U g) (hU g) v (U g⁻¹ w)

theorem exists_isCoverIt : ∀ (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H), (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') → (∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) → ∃ B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H, IsCoverIt R₁ R₂ B := by
  intro p q r s T₀ T₁ T₂ F R₁ R₂ Tm hTm hEq

  have hnorm : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hTm x x y y
    simp only [inner_self_eq_norm_sq_to_K] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
      rw [mul_pow]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).1 h2
  have hflip : ∀ y, ‖Tm.flip y‖ ≤ ‖y‖ := fun y =>
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y) fun x => by
      rw [ContinuousLinearMap.flip_apply, hnorm, mul_comm]

  have hsrc : ∀ (g : T₁.G) (y : R₂.U.H) (v : F.H),
      R₁.U.π g (ContinuousLinearMap.adjoint (Tm.flip y) v) =
        ContinuousLinearMap.adjoint (Tm.flip y) (F.π (g, 1) v) := by
    intro g y v
    apply ext_inner_right ℂ
    intro x
    rw [inner_unitary_apply_eq_inner_inv R₁.U.π R₁.U.isom, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.flip_apply]
    have e1 : Tm (R₁.U.π g⁻¹ x) y = F.π (g⁻¹, 1) (Tm x y) := by
      rw [hEq]; simp
    have e2 : F.π (g, 1) v = F.Om (F.emb (g, 1)) v := rfl
    have e3 : F.π (g⁻¹, 1) (Tm x y) = F.Om (F.emb (g, 1))⁻¹ (Tm x y) := by
      have : ((g⁻¹, 1) : T₁.G × T₂.G) = (g, 1)⁻¹ := by simp
      show F.Om (F.emb (g⁻¹, 1)) (Tm x y) = _
      rw [this, map_inv]
    rw [e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]

  have htgt : ∀ (h : T₂.G) (y : R₂.U.H) (v : F.H),
      ContinuousLinearMap.adjoint (Tm.flip (R₂.U.π h y)) v =
        ContinuousLinearMap.adjoint (Tm.flip y) (F.π (1, h⁻¹) v) := by
    intro h y v
    apply ext_inner_right ℂ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
    have e1 : Tm x (R₂.U.π h y) = F.π (1, h) (Tm x y) := by
      rw [hEq]; simp
    have e2 : F.π (1, h⁻¹) v = F.Om (F.emb (1, h⁻¹)) v := rfl
    have e3 : F.π (1, h) (Tm x y) = F.Om (F.emb (1, h⁻¹))⁻¹ (Tm x y) := by
      have : ((1, h) : T₁.G × T₂.G) = (1, h⁻¹)⁻¹ := by simp
      show F.Om (F.emb (1, h)) (Tm x y) = _
      rw [this, map_inv]
    rw [e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]
  let B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H :=
    { toFun := fun P =>
        { toFun := fun y => ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P)
          map_add' := fun y y' => by simp
          map_smul' := fun c y => by
            rw [map_smul, LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply] }
      map_add' := fun P P' => by ext y; simp
      map_smul' := fun c P => by ext y; simp }
  have hB : ∀ P y, B P y = ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) := fun _ _ => rfl
  refine ⟨B, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro P
    refine ⟨‖F.ι P‖, fun y => ?_⟩
    rw [hB]
    calc ‖ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P)‖
        ≤ ‖ContinuousLinearMap.adjoint (Tm.flip y)‖ * ‖F.ι P‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Tm.flip y‖ * ‖F.ι P‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ ‖y‖ * ‖F.ι P‖ := by gcongr; exact hflip y
      _ = ‖F.ι P‖ * ‖y‖ := mul_comm _ _
  · intro P y
    rw [R₁.ι_range, hB]
    unfold KFin
    have hk := (GlobalTheory.FockKFin.kfin_fock p q r s T₀ T₁ T₂ F
      (GlobalTheory.FockDegree.Om_Kset_homog p q r s T₀ T₁ T₂ F) P).1
    unfold KFin at hk
    haveI := hk
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.map
      (ContinuousLinearMap.adjoint (Tm.flip y)).toLinearMap
      (Submodule.span ℂ (Set.range fun k : ↥T₁.Kset => F.π ((k : T₁.G), 1) (F.ι P)))) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (hsrc _ y _).symm⟩
  · intro y hy
    by_contra hcon
    push_neg at hcon
    haveI := R₁.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R₁.U.H)
    have hz : (fun v : F.H => inner ℂ v (Tm x y)) = fun _ => 0 := by
      refine Continuous.ext_on F.dense (continuous_id.inner continuous_const) continuous_const ?_
      rintro _ ⟨P, rfl⟩
      have h0 : ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) = 0 := by rw [← hB]; exact hcon P
      have := ContinuousLinearMap.adjoint_inner_left (Tm.flip y) x (F.ι P)
      rw [h0, inner_zero_left, ContinuousLinearMap.flip_apply] at this
      exact this.symm
    have h1 : Tm x y = 0 := inner_self_eq_zero.1 (congrFun hz (Tm x y))
    have h2 := hnorm x y
    rw [h1, norm_zero] at h2
    exact mul_ne_zero (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy) h2.symm
  · intro Z hZ P y
    have hd := (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F).2.1 Z hZ P
    have hc := ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    have e : (fun t : ℝ => R₁.U.π (T₁.expt (t • Z)) (B P y)) =
        (ContinuousLinearMap.adjoint (Tm.flip y)) ∘
          (fun t : ℝ => F.π (T₁.expt (t • Z), 1) (F.ι P)) := by
      funext t
      rw [hB, Function.comp_apply, hsrc]
    rw [e, hB]
    exact hc
  · intro Z hZ P y
    have hone : T₂.expt ((0 : ℝ) • Z) = 1 := by
      have h := T₂.expt_add Z hZ 0 0
      rw [add_zero] at h
      have h' := congrArg (· * (T₂.expt ((0 : ℝ) • Z))⁻¹) h
      simpa [mul_assoc] using h'.symm
    have hinv : ∀ t : ℝ, (T₂.expt (t • Z))⁻¹ = T₂.expt ((-t) • Z) := by
      intro t
      have h := T₂.expt_add Z hZ (-t) t
      rw [neg_add_cancel, hone] at h
      exact (eq_inv_of_mul_eq_one_left h.symm).symm
    have hd := (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F).2.2 Z hZ P
    have hd' : HasDerivAt (fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P))
        (F.ι (fockAct2 p q r s Z P)) (-(0 : ℝ)) := by rw [neg_zero]; exact hd
    have hn := hd'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    have hc := ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hn
    have e : (fun t : ℝ => B P (R₂.U.π (T₂.expt (t • Z)) y)) =
        (ContinuousLinearMap.adjoint (Tm.flip y)) ∘
          ((fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P)) ∘ fun t : ℝ => -t) := by
      funext t
      rw [hB, htgt, hinv]
      rfl
    have hval : ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ)
        ((-1 : ℝ) • F.ι (fockAct2 p q r s Z P)) =
        -(ContinuousLinearMap.adjoint (Tm.flip y)) (F.ι (fockAct2 p q r s Z P)) := by
      rw [neg_one_smul, map_neg]
      rfl
    rw [e, hB, ← hval]
    exact hc

end GlobalTheory.Chain.CoverContr

end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.heckeVec_satake_sum_unitaryBorel_representatives : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ), ∀ h ∈ Hecke ℂ (KU σ n), ∃ (ι : Type) (_ : Fintype ι) (b : ι → GU σ n), (∀ i, IsBorelU (b i)) ∧ (∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GU σ n) M) (s : M), (∀ k ∈ KU σ n, π k s = s) → heckeVec π (KU σ n) h s = ∑ i, h (b i) • π (b i) s) ∧ ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = ∑ i, h (b i) * ∏ k : Fin (n / 2), ((α k : ℂ) * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k.1 : ℤ)))) ^ ordL ((b i).1.1 (lo n k) (lo n k)) := by
  first | exact @GlobalTheory.SatBorel.heckeVec_satU_borel | exact GlobalTheory.SatBorel.heckeVec_satU_borel | (intros; apply GlobalTheory.SatBorel.heckeVec_satU_borel <;> assumption)
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ a : Matrix (Fin n') (Fin n) L, a ∈ mixLat L n' n → (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ∃ a ∈ mixLat L n' n, (∀ (r : Fin n') (c : Fin n), c.1 < n - n / 2 → a r c = 0) ∧ (h.1.1 * embLow n' n z * g.1.1 : Matrix (Fin n') (Fin n) L) = a + embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1) := by
  first | exact @GlobalTheory.SphTheta.borel_mixLat_lowBlock | exact GlobalTheory.SphTheta.borel_mixLat_lowBlock | (intros; apply GlobalTheory.SphTheta.borel_mixLat_lowBlock <;> assumption)
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cayley_unitaryTorus_inv_det_integral_order : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → ∀ (n' : ℕ) (k : Fin (n' / 2)) (t : GU σ n'), t.1.1 = tMat ϖ n' (n' / 2) (Pi.single k 1) → (1 + (t⁻¹).1.1).det ≠ 0 ∧ (1 + (t⁻¹).1.1)⁻¹ ∈ intMat L (Fin n') (Fin n') ∧ ordL (1 + (t⁻¹).1.1).det = -1 := by
  first | exact @GlobalTheory.CayleyTorus.cayley_torus_inv | exact GlobalTheory.CayleyTorus.cayley_torus_inv | (intros; apply GlobalTheory.CayleyTorus.cayley_torus_inv <;> assumption)
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.upperTriangularUnitary_lowerHalfBlock_triangular : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (hn : n ≤ n'), (∀ g : GU σ n, IsBorelU g → ∃ U : GL (Fin (n / 2)) L, U.1 = lowBlock g.1.1 ∧ U.1.BlockTriangular id ∧ ∀ r, ordL (U.1 r r) = -ordL (g.1.1 (lo n r.rev) (lo n r.rev))) ∧ ∀ h : GU σ n', IsBorelU h → ∃ V : GL (Fin (n / 2)) L, V.1.BlockTriangular id ∧ (∀ r : Fin (n / 2), ordL (V.1 r.rev r.rev) = ordL (h.1.1 (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩) (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩))) ∧ ∀ t : Matrix (Fin (n / 2)) (Fin (n / 2)) L, lowBlock (h⁻¹).1.1 * (Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0) = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then (V.1 * t) ⟨r.1, e⟩ c else 0 := by
  first | exact @GlobalTheory.SphTheta.lowBlocks_borel | exact GlobalTheory.SphTheta.lowBlocks_borel | (intros; apply GlobalTheory.SphTheta.lowBlocks_borel <;> assumption)
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.borelMultiplicative_eq_prod_diagonal_valuations : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (f : GU σ n → ℂ), (∀ b b', IsBorelU b → IsBorelU b' → f (b * b') = f b * f b') → (∀ k ∈ KU σ n, IsBorelU k → f k = 1) → ∀ y : Fin (n / 2) → ℂ, (∀ (k : Fin (n / 2)) (t : GU σ n), t.1.1 = tMat ϖ n (n / 2) (Pi.single k 1) → f t = y k) → ∀ b, IsBorelU b → f b = ∏ k, y k ^ ordL (b.1.1 (lo n k) (lo n k)) := by
  first | exact @GlobalTheory.BorelChar.borel_char | exact GlobalTheory.BorelChar.borel_char | (intros; apply GlobalTheory.BorelChar.borel_char <;> assumption)
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.sum_diag_order_eq_of_integralTranslateIndicator_relation : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (m : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ] (c : ι → ℂ) (c' : κ → ℂ) (U : ι → GL (Fin m) L) (V : κ → GL (Fin m) L), (∀ i, (U i).1.BlockTriangular id) → (∀ j, (V j).1.BlockTriangular id) → (∀ t : GL (Fin m) L, ∑ i, c i * (if t.1 * (U i).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) = ∑ j, c' j * (if (V j).1 * t.1 ∈ intMat L (Fin m) (Fin m) then 1 else 0)) → ∀ f : (Fin m → ℤ) → ℂ, ∑ i, c i * f (fun r => ordL ((U i).1 r r)) = ∑ j, c' j * f (fun r => ordL ((V j).1 r.rev r.rev)) := by
  first | exact @GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator | exact GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator | (intros; apply GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare GlobalTheory.Chain.ParOfSizes

namespace GlobalTheory.Chain.ParOfNodeGap

theorem minSig_lamS_le {D : D7} (k : Fin D.R.m) (τ : D.what₂.Tau) : minSig (lamS D k τ) ≤ D.R.m := by
  unfold minSig
  refine (min_le_right _ _).trans ?_
  calc ((lamS D k τ).filter fun x => x.2 = false).card
      ≤ (Finset.univ.image fun i : Fin D.R.m =>
          ((val (D.hc τ) (k : ℕ) (Sum.inr (Sum.inl i)) + (D.hc τ).e k : ℚ), false)).card := by
        apply Finset.card_le_card
        rintro ⟨a, s⟩ hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hx, hs⟩ := hx
        simp only at hs
        subst hs
        obtain ⟨y, hy, hsy⟩ := (mem_lamS k τ a false).1 hx
        rcases y with y | y | y
        · simp [sgn] at hsy
        · exact Finset.mem_image.2 ⟨y, Finset.mem_univ _, by rw [hy]⟩
        · simp [sgn] at hsy
    _ ≤ (Finset.univ : Finset (Fin D.R.m)).card := Finset.card_image_le
    _ = D.R.m := by simp

theorem num_bound' {n q m N : ℕ} (hq : q ≤ m) (hn : n ≤ N) (hm : 2 ≤ m) (hN : 3 * m ^ 2 ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 * (N : ℝ) ^ 3 := by
  have hqm : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ (2 : ℕ) := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h
        rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
        positivity
      · rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le
        · exact Nat.one_le_cast.mpr h
        · norm_num
    refine h1.trans ?_
    have : (q : ℝ) ≤ m := by exact_mod_cast hq
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hNR : 3 * (m : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hN12 : (12 : ℝ) ≤ N := by nlinarith
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (m : ℝ) ^ 2 :=
        mul_le_mul (by linarith) hqm hpos (by positivity)
    _ ≤ 120 * (N : ℝ) * ((N : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 40 * (N : ℝ) ^ 2 := by ring
    _ ≤ 4 * (N : ℝ) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (by linarith : (0 : ℝ) ≤ N - 10)]

private theorem le_sub_b_succ_of_nodeGap {D : D7} {h : ℝ} (H : D.NodeGap h) (τ : D.what₂.Tau) :
    ∀ (i : ℕ) (hi : i + 1 < D.R.m), h ≤ (((D.hc τ).b ⟨i + 1, hi⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) := by
  intro i hi
  have := H D.u₀ τ i hi
  rwa [D.hcW_base] at this

private theorem rankY_le_N (D : D7) {j : ℕ} (hj : j ≤ D.R.m) : D.R.rankY j ≤ D.R.N D.R.m := by
  have h1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul hj le_rfl
  simp only [Ranks.rankY, Ranks.r, Ranks.N]
  rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem three_mul_m_sq_le_N (D : D7) : 3 * D.R.m ^ 2 ≤ D.R.N D.R.m := by
  have h1 : 3 * D.R.m + 1 ≤ D.R.t := D.R.three_m_lt_t
  have h2 : D.R.m * (3 * D.R.m + 1) ≤ D.R.m * D.R.t := Nat.mul_le_mul le_rfl h1
  simp only [Ranks.N]
  nlinarith

theorem stepGap_of_nodeGap {D : D7} (h : D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6))
    (k : Fin D.R.m) : StepGap D k := by
  set H : ℝ := 4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6 with hH
  have hg := le_sub_b_succ_of_nodeGap h
  have hNpos : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcube : ∀ j : ℕ, j ≤ D.R.m → ((D.R.rankY j : ℕ) : ℝ) ^ 3 < H := by
    intro j hj
    have : ((D.R.rankY j : ℕ) : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := by exact_mod_cast rankY_le_N D hj
    have : ((D.R.rankY j : ℕ) : ℝ) ^ 3 ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) this 3
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    nlinarith [pow_nonneg hNpos 3]
  intro τ
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamT k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamT k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    refine le_trans ?_ (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
    have hb := num_bound' (minSig_lamS_le k τ) (rankY_le_N D k.isLt.le) D.R.two_le_m (three_mul_m_sq_le_N D)
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith

theorem chainPar_of_nodeGap :
    ∀ D : D7, D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6) → ∀ k, GlobalTheory.Chain.ChainPar D k := by
  intro D h k
  exact (chainPar_iff_stepGap k).mpr (stepGap_of_nodeGap h k)

end GlobalTheory.Chain.ParOfNodeGap

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.det_twoDiagBlocks_properties : ∀ (κ : Type) [CommRing κ] (n r t : ℕ) (hr : r ≤ n) (g : GL (Fin n) κ), (g ∈ blockTri (blk2 r) → Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g) ∧ (n = r + t → g ∈ blockTri (blkOf r t) → dBlk (blkOf r t) 1 g = dBlk (blk2 r) 1 g) ∧ (n = r → Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) = Matrix.GeneralLinearGroup.det g) := by
  first | exact @GlobalTheory.VecInv.TwoBlockDet.det_blocks | exact GlobalTheory.VecInv.TwoBlockDet.det_blocks | (intros; apply GlobalTheory.VecInv.TwoBlockDet.det_blocks <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory



theorem extV_mem_levSubV_of_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (z : (R.HV i t).H), (∀ (g0 : P.H) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0.1 κ → ∀ h, R.extV i t z (h * κ) = levChi _ (R.βV i) (flagL (R.datVt i t)) κ • ((((P.chi g0 : ℂˣ) : ℂ))⁻¹ • R.extV i t z h)) → R.extV i t z ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t P)) (levChi _ (R.βV i) (RecTie.datVP R i t P)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t P z hz k hk g
  have hlift : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t)
      (⟨Formalism.L2.DIV.rTup (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) k), hk.2.2⟩ : P.H).1 k :=
    ⟨hk.1, hk.2.1, rfl⟩
  have h2 := (GlobalTheory.lift_mem_levVP R i t P _ k hlift).2
  rw [hz _ k hlift g, h2, smul_smul, mul_comm]

end GlobalTheory
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

theorem _root_.GlobalTheory.T.integral_mul_eq_zero_of_coset_integral_eq_zero_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure G) [μ.IsHaarMeasure] (f w : G → ℂ), Continuous f → HasCompactSupport f → LocallyIntegrable w μ → (∀ u ∈ H, (fun g => w (u * g)) =ᵐ[μ] w) → (∀ g, ∫ u : H, f (u * g) ∂ν = 0) → ∫ g, f g * w g ∂μ = 0 := by
  first | exact @GlobalTheory.CosetIntegralZero.integral_mul_eq_zero_of_coset_integral_eq_zero | exact GlobalTheory.CosetIntegralZero.integral_mul_eq_zero_of_coset_integral_eq_zero | (intros; apply GlobalTheory.CosetIntegralZero.integral_mul_eq_zero_of_coset_integral_eq_zero <;> assumption)
end

section

open GlobalTheory.Orb
open scoped Topology ContDiff Manifold

theorem _root_.GlobalTheory.T.exists_contDiff_comp_of_locally_smooth_compactSupport : ∀ (H : Type) [TopologicalSpace H] (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (c : H → X) (f : H → ℂ), Continuous c → HasCompactSupport f → (∀ a, ∃ V : Set X, IsOpen V ∧ c a ∈ V ∧ ∃ Φ : X → ℂ, ContDiffOn ℝ ∞ Φ V ∧ ∀ g, c g ∈ V → f g = Φ (c g)) → ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) := by
  first | exact @GlobalTheory.glue_smooth_of_compactSupport | exact GlobalTheory.glue_smooth_of_compactSupport | (intros; apply GlobalTheory.glue_smooth_of_compactSupport <;> assumption)
end
