module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.ExistsDoubledUnitaryBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.RealSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelInt
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelicCoordinatesEvalZeroFormMemAdmissible
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.DetConjMulVec
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.FrOfFrame
public import Development.WeilBound.ThetaLifts.LeviDeterminants.DoubledUnitaryCharacterTrivialOfSiegel
public import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.LagLine
public import Development.WeilBound.ThetaLifts.CTKernel
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdelicEstimatesHolds
import Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransportAlg
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.LawWLevi, Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.LevScalar2, Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.MixWOfAdel, Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixWClosed

-- ===== clump member: Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.LawWLevi =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.LawWLevi", "h": "module\n\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.ExistsDoubledUnitaryBlock\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.RealSt\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff\npublic import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelInt\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelicCoordinatesEvalZeroFormMemAdmissible\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.DetConjMulVec\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.FrOfFrame\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.DoubledUnitaryCharacterTrivialOfSiegel\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.LagLine\nimport Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKF0.Chr

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}

theorem ax_of (hA : PositivityTheory.Mix.AdelSt) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : Ax (adeleClass F) ψ :=
  by
    have hb : AxB (adeleClass F) ψ := by
      constructor
      · exact fun κ _ => (_root_.GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).1
      · intro κ _
        obtain ⟨φ, h, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
        exact ⟨φ, h, fun e => h0 (congrFun e 0)⟩
      · exact fun κ _ => adelicCoordinatesEvalZeroForm_mem_admissible κ
      · exact fun κ₁ κ _ _ j hj φ hφ => GlobalTheory.RestrSchA.mem_schA_comp_extend F j hj φ hφ
      · intro κ₁ κ _ _ j hj l hl g hg
        obtain ⟨T, hT⟩ := hl _ (GlobalTheory.RestrSchA.sb_comp_extend F hj hg)
        refine ⟨T.comp (GlobalTheory.RestrSchA.restrS F hj), fun f => ?_⟩
        rw [ContinuousLinearMap.comp_apply, ← hT]
        exact congrArg l (funext fun y => GlobalTheory.RestrSchA.pureA_extend F hj f g y)
      · exact fun κ κ' _ _ => GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ'
      · exact fun κ κ' _ _ => box_adm κ κ'
    exact ⟨hb, axDelta_of lagLine hψ, axImp_of hA hψ⟩

theorem det_ne_of_sig {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) {a : ℂ} (h : HasSig (a • J.map τ) r s) : J.det ≠ 0 :=
  fun h0 => GlobalTheory.det_ne_zero_of_hasSig h (by rw [det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])

variable {n d d₁ r s r' s' r₁ s₁ i₀ i₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {M : Model σ X W}
  {M₁ : Model σ X W₁} {χX χW : Chr F E} {om : Rep σ X W} {om₁ : Rep σ X W₁} {e : Fn F n d →ₗ[ℂ] Fn F n d₁}

theorem lawW_levi (hA : PositivityTheory.Mix.AdelSt) (hP : IsPair B M χX χW om r s r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hP₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) {t h₁ m} (hm : IsLevi H' t h₁ m) :
    ∀ Φ ∈ schA F (Fin n × Fin d),
      e (om (1, m) Φ) = ((χX t : ℂ) * (((absE F E t : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ)) • om₁ (1, h₁) (e Φ) := by
  have hB := hP.base
  have := hB.cm.1
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨S, j, hS, hj, hE, hrel, -⟩ := setW hB hP.herm hP.skew hP.good hH hP₁.good he
  obtain ⟨π, ρ, hF⟩ := fr_plane hB hH hP.skew.lat (-1) (fun i j => by simp [hP.skew.skew])
  let T : GL Unit (AE F E) := ⟨diagonal fun _ => t.1, diagonal fun _ => (t⁻¹).1, by simp, by simp⟩
  have hT : GeneralLinearGroup.det T = t := Units.ext (by simp [T])
  have key := TB (ax_of hA hB.std) hS hj hE hF hrel hP.weil.1 hP₁.weil.1
    (parabolic_character_trivial_on_diagonal F E σ hB.cm d₁ W₁.J (-1) (fun i j => by simp [hP₁.skew.skew])
      (det_ne_of_sig _ (hP₁.skew.sig (Classical.arbitrary _)))) m h₁ T hm.2.2 (by
      ext i k
      exact (congrFun hm.1 i).trans (by simp [T, mul_comm]))
  rw [hT, fac, Fintype.card_fin] at key
  rw [absE_eq]
  exact key

theorem lawW_left (hA : PositivityTheory.Mix.AdelSt) (hP : IsPair B M χX χW om r s r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hP₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) (g : UA σ X.J) :
    ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = om₁ (g, 1) (e Φ) := by
  have hB := hP.base
  have := hB.cm.1
  obtain ⟨S, j, hS, hj, hE, hrel, hy⟩ := setW hB hP.herm hP.skew hP.good hH hP₁.good he
  obtain ⟨π, ρ, hF⟩ := fr_plane hB hH hP.skew.lat (-1) (fun i j => by simp [hP.skew.skew])
  obtain ⟨d', hd', hW⟩ := hP.weil.2.1
  obtain ⟨d₁', hd₁', hW₁⟩ := hP₁.weil.2.1
  have hd : ∀ u, d'.e u = M.co.e uᵀ := fun u => hd' uᵀ
  have hd₁ : ∀ u, d₁'.e u = M₁.co.e uᵀ := fun u => hd₁' uᵀ
  refine TA' (ι := incM F H'.ι) (x := incV F H'.x) (y := incV F H'.y) (ax_of hA hB.std) axInt hS hj hE (by simp [hH.rank])
    (fun u z => ?_) (fun b => ?_) (fun b hb => ?_) (fun u => ?_) hW hW₁
    (parabolic_character_trivial_on_diagonal F E σ hB.cm n X.J 1 (fun i j => by simp [hP.herm.herm])
      (GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hP.herm).ne_zero) g
  · rw [hd, hd₁, hrel]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨fun i => a i (), ?_⟩
      rw [← transpose_transpose u, ha, mul_col, transpose_add, transpose_vecMulVec, ← transpose_mul, transpose_transpose]
    · rintro ⟨b, rfl⟩
      refine ⟨replicateCol Unit b, ?_⟩
      rw [mul_col, transpose_add, transpose_vecMulVec, transpose_mul]
      rfl
  · rw [hd, transpose_vecMulVec]
    exact hy b
  · have h1 : ρ *ᵥ incV F H'.y = fun i => (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (AE F E)) i (.inr ()) :=
      funext fun i => congrFun (congrFun hF.rz i) (.inr ())
    have h2 := congrArg (ρ * ·) hb
    simp only [mul_vecMulVec, h1, Matrix.mul_zero] at h2
    funext k
    simpa [vecMulVec_apply] using congrFun (congrFun h2 (.inr ())) k
  · refine ⟨π * u, (ρ * u) (.inl ()), (ρ * u) (.inr ()), ?_⟩
    conv_lhs => rw [← Matrix.one_mul u, ← hF.one, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [add_assoc]
    congr 1
    ext i k
    simp [Matrix.mul_apply, vecMulVec_apply]

end PositivityTheory.ThKF0.Chr
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.LawWLevi =====

-- ===== clump member: Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.MixWOfAdel =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.MixWOfAdel", "h": "module\n\npublic import Development.WeilBound.ThetaLifts.CTKernel\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.RealSt\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.FrOfFrame\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.LawWLevi\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.LevScalar2\nimport Development.WeilBound.ThetaLifts.LeviDeterminants.DoubledUnitaryCharacterTrivialOfSiegel\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.ExistsDoubledUnitaryBlock\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKF0.Chr

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {n d d₁ r s r' s' r₁ s₁ i₀ i₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {M : Model σ X W}
  {M₁ : Model σ X W₁} {χX χW : Chr F E} {om : Rep σ X W} {om₁ : Rep σ X W₁} {e : Fn F n d →ₗ[ℂ] Fn F n d₁}

theorem lawW_unip (hA : PositivityTheory.Mix.AdelSt) (hP : IsPair B M χX χW om r s r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hP₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) :
    ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, u) Φ) = e Φ := by
  have hB := hP.base
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨S, j, hS, hj, hE, hrel, -⟩ := setW hB hP.herm hP.skew hP.good hH hP₁.good he
  obtain ⟨π, ρ, hF⟩ := fr_plane hB hH hP.skew.lat (-1) (fun i j => by simp [hP.skew.skew])
  have pr : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) := hP.weil.isUSplitting.pres
  have hmul : ∀ u v : UA σ W.J, ∀ Φ, om (1, u * v) Φ = om (1, u) (om (1, v) Φ) := fun u v Φ => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    choose a ha using hu.2
    have key := TU (ax_of hA hB.std) hS hj hE hF hrel hP.weil.1 hP₁.weil.1
      (parabolic_character_trivial_on_diagonal F E σ hB.cm d₁ W₁.J (-1) (fun i j => by simp [hP₁.skew.skew])
        (det_ne_of_sig _ (hP₁.skew.sig (Classical.arbitrary _)))) u 1 1 (replicateRow Unit fun k => a (Pi.single k 1)) (by
        ext i k
        have := congrFun (ha (Pi.single k 1)) i
        rw [mulVec_mulVec] at this
        simpa [mat, mul_comm, Matrix.mul_apply] using this) (by
        ext i k
        exact (congrFun hu.1 i).trans (by simp))
    intro Φ hΦ
    simpa [fac, Prod.mk_one_one] using key Φ hΦ
  | one => intro Φ _; rw [Prod.mk_one_one, map_one, Module.End.one_apply]
  | mul u v _ _ hu hv => intro Φ hΦ; rw [hmul, hu _ (pr _ _ hΦ), hv _ hΦ]
  | inv u _ hu =>
    intro Φ hΦ
    rw [← hu _ (pr _ _ hΦ), ← hmul, mul_inv_cancel, Prod.mk_one_one, map_one, Module.End.one_apply]

end PositivityTheory.ThKF0.Chr

theorem PositivityTheory.ThKF0.mixW_of_adel (hA : PositivityTheory.Mix.AdelSt) : PositivityTheory.ThKG.MixW := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he g t h₁ m hm u hu Φ hΦ
  have pr : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) := hP.weil.isUSplitting.pres
  have h2 : om (g, u * m) = om (g, 1) * om (1, u) * om (1, m) := by
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, mul_one, one_mul]
  rw [h2, Module.End.mul_apply, Module.End.mul_apply, Chr.lawW_left hA hP hH hP₁ he g _ (pr _ _ (pr _ _ hΦ)),
    Chr.lawW_unip hA hP hH hP₁ he u hu _ (pr _ _ hΦ), Chr.lawW_levi hA hP hH hP₁ he hm Φ hΦ, map_smul, ← Module.End.mul_apply,
    ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.MixWOfAdel =====

-- ===== clump member: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixWClosed =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixWClosed", "h": "module\n\npublic import Development.WeilBound.ThetaLifts.CTKernel\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.MixWOfAdel\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdelicEstimatesHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

theorem PositivityTheory.Mix.mixW_closed : PositivityTheory.ThKG.MixW := PositivityTheory.ThKF0.mixW_of_adel PositivityTheory.Mix.adelic_estimates_holds
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixWClosed =====
