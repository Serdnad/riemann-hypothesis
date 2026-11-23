module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle351
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle490
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle331
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle350
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TendstoSlopeOfArchimedeanPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.RealDict
theorem lie_derivative_mem_coinvariants : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
          f₁ ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  intro hPr D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs Ws Mo ψ' χX χW om τ hP hR Φ hinj hrange hF γ hγ f hf f₁ hact
  obtain ⟨hcm, hstd, hherm, hdetX, hskew, hdetW, -, -, -, -, hweil, -, -⟩ := hP
  have hpsi := hR.psi
  subst hpsi
  obtain ⟨f₀, r, hvac, hne, hFr⟩ := hF
  rw [← hrange] at hf
  obtain ⟨P, rfl⟩ := hf
  obtain ⟨g, hg, hder⟩ := _root_.GlobalTheory.T.theta_lineDeriv_vanishes_on_coinvariants hPr D ψ' θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs hR.JX f₀ hvac γ hγ
  obtain ⟨Q, hQ, hQd⟩ := hder P
  have hGM : M.gram.det ≠ 0 := by
    intro h0
    apply hdetX
    rw [hR.JX, Matrix.det_smul, h0, mul_zero]
  have hG : (sgn ε M).gram.det ≠ 0 := by
    cases ε
    · exact hGM
    · change (-M.gram).det ≠ 0
      rw [Matrix.det_neg]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hGM
  obtain ⟨T, hT, hTinj⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Mo ψ' (sgn ε M).gram (Equiv.refl _) hR.good hstd hdetX hdetW hG
  have hΦ1 : Φ 1 ≠ 0 := fun h => one_ne_zero (hinj (h.trans (map_zero Φ).symm))
  have hRf₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r := GlobalTheory.T.complementaryAdelicSchwartz_archimedean_replace _ f₁ r (hFr 1).1 hΦ1
  have hRQ := (hFr Q).1
  have hone : GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hR.JW 1 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hR.JW 1).1.1 = 1
    rw [GlobalTheory.TripleRead.toUX_val, GlobalTheory.WeilVacMove.mt_one]
    exact Matrix.submatrix_one_equiv _
  have key : ∀ x, GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl _) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) x =
      GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl _) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ Q) r) x := by
    intro x
    have h1 := _root_.GlobalTheory.T.thetaSum_differentiable_along_line hPr Mo ψ' χX χW om hstd hR.good hweil γ hγ (Φ P) f₁ r (hFr P).1 hact
      (GlobalTheory.TripleRead.ptO (sgn ε M).gram (Equiv.refl _) x)
    have h2 : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum D.host.F (Mo.co.rho ψ' (GlobalTheory.TripleRead.ptO (sgn ε M).gram (Equiv.refl _) x)
        (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r))) =
        ω (g t, 1) (ptF (V := sgn ε M) ψ' θ (frSgn ε A) B f₀ P) x := by
      intro t
      have h3 := hR.transp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r) (hFr P).1.2 (g t) 1
      rw [hg t, hone, (hFr P).2] at h3
      exact congrFun h3 x
    simp only [h2] at h1
    have h4 := h1.unique (hQd x)
    rw [(hFr Q).2]
    exact h4
  obtain ⟨d, hd⟩ : ∃ d : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank), d = f₁ - Φ Q := ⟨_, rfl⟩
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) d r =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ Q) r := by
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, sub_mul, hd]
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) d r ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin X.rank) := by
    rw [e1]; exact sub_mem hRf₁.2 hRQ.2
  have hT0 : T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) d r) = 0 := by
    rw [e1, map_sub, hT _ hRf₁.2, hT _ hRQ.2, funext key, sub_self]
  have hz := hTinj _ hmem hT0
  have hr : ∃ x₀, r x₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) r = 0 := funext fun x => by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hcon]
    have h2 := (hFr 1).2
    rw [h0, ← hT 0 (zero_mem _), map_zero, GlobalTheory.LieScalar.ptF_one] at h2
    exact hne h2.symm
  have hfeq : f₁ = Φ Q := by
    obtain ⟨x₀, hx₀⟩ := hr
    rw [← sub_eq_zero, ← hd]
    refine DFunLike.ext _ _ fun y => ?_
    let z : Fin M.rank × Fin X.rank → AF D.host.F := fun i => LinearMap.inl D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (x₀ i)))
    have hzAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) z := by
      intro u hu
      have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective (by rw [map_zero]; exact hu)
      funext i
      show u * z i = 0
      refine Prod.ext ?_ ?_
      · show u.1 * (z i).1 = 0
        rw [hu1, zero_mul]
      · show u.2 * (z i).2 = 0
        simp [z]
    have hev : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F ((x₀ + z) i)) = y := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F ((x₀ i).1 + (z i).1) = y i
      rw [map_add (f := _)]
      show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (x₀ i) + InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
        ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (x₀ i))) = y i
      rw [RingEquiv.apply_symm_apply, add_sub_cancel]
    have h5 := congrFun hz (x₀ + z)
    have h6 : r (x₀ + z) = r x₀ := (hFr 1).1.1 x₀ z hzAt
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.zero_apply] at h5
    rw [hev, h6] at h5
    simpa [hx₀] using h5
  rw [hfeq]
  exact Submodule.mem_map_of_mem hQ
end GlobalTheory.RealDict
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.real_lie_derivative_mem_coinvariants : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
          f₁ ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  first | exact @_root_.GlobalTheory.RealDict.lie_derivative_mem_coinvariants | exact _root_.GlobalTheory.RealDict.lie_derivative_mem_coinvariants | (intros; apply _root_.GlobalTheory.RealDict.lie_derivative_mem_coinvariants <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open Filter Topology
noncomputable section
open scoped Classical
namespace GlobalTheory.LineAdd
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
section
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
theorem line_sum_curve_eq_prod (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd)
    (hψ : IsStd ψ) (hG : M.IsGood ψ) (hW : M.IsWeil ψ χX χW om)
    {ι : Type} (γs : ι → (Multiplicative ℝ →* UA σ Y.J)) (hγs : ∀ i, γs i ∈ Lines σ Y)
    (r : (Fin n × Fin d → AF F) → ℂ) (hr00 : r 0 ≠ 0) (hr : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) f r)
    (f : SInf F (Fin n × Fin d)) (g : ι → SInf F (Fin n × Fin d))
    (hg : ∀ i, ∃ c : ℝ → SInf F (Fin n × Fin d),
      (∀ t, om (γs i (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) ∧ c 0 = f ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 (g i))) :
    ∀ l : List ι, ∃ c : ℝ → SInf F (Fin n × Fin d),
      (∀ t, om ((l.map fun i => γs i (Multiplicative.ofAdd t)).prod, 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) ∧
      c 0 = f ∧ Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 (l.map g).sum) := by
  have hr0 : ∃ x, r x ≠ 0 := ⟨0, hr00⟩
  have canc := GlobalTheory.ArchCancel.eq_of_tens_eq F r (hr f).1 hr0
  have img : ∀ i (h : SInf F (Fin n × Fin d)) (t : ℝ), ∃ k : SInf F (Fin n × Fin d),
      om (γs i (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑h r) = tens (evI F) ⇑k r := by
    intro i h t
    obtain ⟨c, -, hc, -⟩ := _root_.GlobalTheory.T.archimedean_line_pairing_twist hP M ψ χX χW om hψ hG hW (γs i) (hγs i) h r (hr h)
    exact ⟨c t, hc t⟩
  intro l
  induction l with
  | nil =>
    refine ⟨fun _ => f, fun t => ?_, rfl, ?_⟩
    · simp only [List.map_nil, List.prod_nil]
      exact om_one_one om _
    · simp only [sub_self, smul_zero, List.map_nil, List.sum_nil]
      exact tendsto_const_nhds
  | cons i l' ih =>
    obtain ⟨c', hc', hc'0, hlim'⟩ := ih
    obtain ⟨ci, hci, hci0, hlimi⟩ := hg i
    set S' := (l'.map g).sum with hS'
    let s : ℝ → SInf F (Fin n × Fin d) := fun t => if t = 0 then S' else t⁻¹ • (c' t - f)
    choose k hk using fun t => img i (s t) t
    have hs : Tendsto s (𝓝 0) (𝓝 S') := by
      rw [← nhdsNE_sup_pure (0 : ℝ)]
      refine Tendsto.sup ?_ ?_
      · refine hlim'.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [s, if_neg (show t ≠ 0 from ht)]
      · simp only [tendsto_pure_left, s, if_pos rfl]
        exact fun _ => mem_of_mem_nhds
    have hk' : Tendsto k (𝓝 0) (𝓝 S') :=
      _root_.GlobalTheory.T.jointly_continuous_archimedean_weil_action hP M ψ χX χW om hψ hG hW (γs i) (hγs i) r hr00 hr s k S' hk hs
    have hcs : ∀ t, c' t = f + t • s t := by
      intro t
      by_cases ht : t = 0
      · subst ht; simp [hc'0]
      · simp only [s, if_neg ht, smul_smul, mul_inv_cancel₀ ht, one_smul, add_sub_cancel]
    refine ⟨fun t => ci t + t • k t, fun t => ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons]
      rw [om_prod_one, hc' t, hcs t, tens_add_smul, map_add (f := _), map_smul, hci t, hk t, tens_add_smul]
    · simp [hci0]
    · simp only [List.map_cons, List.sum_cons]
      refine (hlimi.add (hk'.mono_left nhdsWithin_le_nhds)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := ht
      rw [add_sub_right_comm, smul_add, smul_smul, inv_mul_cancel₀ ht', one_smul]
end GlobalTheory.LineAdd
open GlobalTheory.LineAdd GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem GlobalTheory.LineAdd.deriv_prod_lines_eq_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (fs : ι → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γs i (Multiplicative.ofAdd t), 1)) f (fs i)) →
    f₁ = (l.map fs).sum := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om a b a' b' hpair ι l γs hγs γ _ hprod f _ f₁ fs hD hDs
  obtain ⟨r, hr00, hr⟩ := GlobalTheory.ThK.exists_rest_inf F (Fin n × Fin d)
  have hψ := hpair.base.std
  have hG := hpair.good
  have hW := hpair.weil
  have canc := GlobalTheory.ArchCancel.eq_of_tens_eq F r (hr f).1 ⟨0, hr00⟩
  choose cs gs hcs hlims using fun i => _root_.GlobalTheory.T.archimedean_line_pairing_twist hP M B.ψ χX χW om hψ hG hW (γs i) (hγs i) f r (hr f)
  have hcs0 : ∀ i, cs i 0 = f := by
    intro i
    refine canc _ _ ?_
    rw [← hcs i 0]
    simp only [ofAdd_zero, map_one]
    exact om_one_one om _
  have hlims' : ∀ i, Tendsto (fun t : ℝ => t⁻¹ • (cs i t - f)) (𝓝[≠] 0) (𝓝 (gs i)) := by
    intro i; simpa [hcs0 i] using hlims i
  have hfs : ∀ i, fs i = gs i := by
    intro i
    refine canc _ _ (funext fun x => ?_)
    exact (hDs i r (hr f) x).unique (hasDerivAt_of_curve (hcs i) (hcs0 i) (hlims' i) x)
  obtain ⟨c, hc, hc0, hlim⟩ := _root_.GlobalTheory.LineAdd.line_sum_curve_eq_prod hP M B.ψ χX χW om hψ hG hW γs hγs r hr00 hr f gs
    (fun i => ⟨cs i, hcs i, hcs0 i, hlims' i⟩) l
  have hc' : ∀ t, om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r := by
    intro t; rw [hprod]; exact hc t
  have e1 : f₁ = (l.map gs).sum := by
    refine canc _ _ (funext fun x => ?_)
    exact (hD r (hr f) x).unique (hasDerivAt_of_curve hc' hc0 hlim x)
  rw [e1]
  congr 1
  exact List.map_congr_left fun i _ => (hfs i).symm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.line_derivative_additive_in_lines : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (fs : ι → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γs i (Multiplicative.ofAdd t), 1)) f (fs i)) →
    f₁ = (l.map fs).sum := by
  first | exact @_root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum | exact _root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum | (intros; apply _root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum <;> assumption)
end
end

section

section
noncomputable section
open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
namespace GlobalTheory.PolActsPf
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.RealActs
section Swap
variable {P Q R S : ℕ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Swap
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Graph
variable {κ V : Type} [Fintype κ] [AddCommGroup V] [Module ℂ V] {Φ : V →ₗ[ℂ] SInf F κ}
end Graph
theorem mem_polarizationStabilizer_of_dualPair (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype κ] {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w}
    {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {a b : ℂ}
    {A : InfinitePlace F → Matrix α (Ix P Q) ℂ} {C : InfinitePlace F → Matrix β (Ix R S) ℂ}
    {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)}
    {θ : InfinitePlace F → Matrix β β ℂ} (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (fr : Framed τ JA JB a b A C)
    (hΦ : IsFockMap ψ τ d A C Φ) (hs : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (hθ : ∀ w, θ w * C w = C w * Jm R S) :
    (∀ γ ∈ RLines (σ := σ) JB, DerOn (LinearMap.range Φ) (fun t => om (γ (Multiplicative.ofAdd t)))) ∧
    ∀ k : UG (cA σ) JB, At (evI F) ((k.1 : Matrix β β (AE F E)) - 1) →
      (∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) → OpOn (LinearMap.range Φ) (om k) := by
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hls : LieScalar := _root_.GlobalTheory.T.weil_lie_algebra_scalar_action hP hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  have hgen : GenEx := GlobalTheory.T.oneParamSubgroup_generators_exist
  have hkl : KLine := kLine_of_lineEx exists_line_of_upq
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ ψ τ _ _ d a b A C Φ om hcm hψ fr hΦ hs
  refine ⟨fun γ hγ => ?_, fun k hk hc => ?_⟩
  · obtain ⟨Y, -, hY⟩ := hgen F E σ β R S τ JB b C hcm fr.2.2 γ hγ
    exact derOn_of_sd hΦ.1 _ _ (fun t => map_zero _) (hact γ hγ Y hY)
  · obtain ⟨γ, hγ, Y, hY, hKC, hγ1⟩ := hkl F E σ β R S τ JB b C θ hcm fr.2.2 hθ k hk hc
    have hloc := locFin_sumPl _ _ _ (fun w => locFin_compact P Q R S (Y w) (hKC w) (c w * (Y w).trace))
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F κ _ Φ _ (om.comp γ) hloc
      (fun t l hl => hs.adm _ l hl) (fun T => hact γ hγ Y hY T)
    change ∀ T, SA (om (γ (Multiplicative.ofAdd 1))) (Φ T) (Φ (U T)) at hSA
    rw [hγ1] at hSA
    exact opOn_of_sa hΦ.1 U _ (map_zero _) hSA
theorem polarization_acts_of_isDualPair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealActs.PolActs B M om := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  have hb := h.base
  have hfr : FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hfe : FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_real, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_real]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have fr' : Framed B.emb (incM F W.J) (incM F X.J) Complex.I 1 C A := ⟨mul_one _, hC1, hA1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := h.weil
  obtain ⟨d', hd', hB⟩ := hwp.2.1
  have hr' : LinearMap.range (Φ ∘ₗ (flipT (InfinitePlace F) r s r' s').toLinearMap) = M.Pol B.ψ B.emb := by
    rw [LinearEquiv.range_comp, hr]
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.PolActsPf.mem_polarizationStabilizer_of_dualPair hP hb.cm hb.std fr' (isFockMap_flip hΦ hd') hB.1 hAθ
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.PolActsPf.mem_polarizationStabilizer_of_dualPair hP hb.cm hb.std fr hΦ hwp.1.1 hCθ
  rw [hr'] at h1 h2
  rw [hr] at h3 h4
  exact ⟨fun γ hγ => h1 γ hγ, fun k hk => h2 k hk.1 hk.2, fun γ hγ => h3 γ hγ, fun k hk => h4 k hk.1 hk.2⟩
end GlobalTheory.PolActsPf
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem _root_.GlobalTheory.T.dualPair_preserves_polarization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealActs.PolActs B M om := by
  first | exact @_root_.GlobalTheory.PolActsPf.polarization_acts_of_isDualPair | exact _root_.GlobalTheory.PolActsPf.polarization_acts_of_isDualPair | (intros; apply _root_.GlobalTheory.PolActsPf.polarization_acts_of_isDualPair <;> assumption)
end
end
