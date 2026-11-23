module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVector
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle258
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
open GlobalTheory.OrientedHeis GlobalTheory.Core.Rk.FockBox

noncomputable section

namespace GlobalTheory.Core.Rk.FockBoxT

theorem killed_of_leibniz₂ {P₁ P₂ Q U₁ U₂ V : Type} [Zero U₁] [Zero U₂] [AddCommGroup V] (a₁ : P₁ → U₁ → U₁)
    (a₂ : P₂ → U₂ → U₂) (b : Q → V → V) (T₁ : U₁ → Prop) (T₂ : U₂ → Prop)
    (TV : V → Prop) (δ : U₁ → U₂ → V) (c₁ : Q → P₁) (c₂ : Q → P₂) (ha₁ : ∀ p f, T₁ f → T₁ (a₁ p f))
    (ha₂ : ∀ p f, T₂ f → T₂ (a₂ p f)) (hb : ∀ q f, TV f → TV (b q f))
    (hadd : ∀ q f g, TV f → TV g → b q (f + g) = b q f + b q g) (hb0 : ∀ q, b q 0 = 0)
    (hδ : ∀ f g, T₁ f → T₂ g → TV (δ f g)) (h1 : ∀ g, δ 0 g = 0) (h2 : ∀ f, δ f 0 = 0)
    (hL : ∀ q f g, T₁ f → T₂ g → b q (δ f g) = δ (a₁ (c₁ q) f) g + δ f (a₂ (c₂ q) g)) (N : ℕ) :
    ∀ (N₁ N₂ : ℕ) (f : U₁) (g : U₂), N₁ + N₂ ≤ N → T₁ f → T₂ g →
      (∀ l : List P₁, l.length = N₁ → l.foldr a₁ f = 0) → (∀ l : List P₂, l.length = N₂ → l.foldr a₂ g = 0) →
      ∀ l : List Q, l.length = N → l.foldr b (δ f g) = 0 := by
  have w0 : ∀ l : List Q, l.foldr b 0 = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hb0]
  have wT : ∀ (l : List Q) f, TV f → TV (l.foldr b f) := fun l f hf => by
    induction l with
    | nil => exact hf
    | cons q l ih => exact hb _ _ ih
  have wadd : ∀ (l : List Q) f g, TV f → TV g → l.foldr b (f + g) = l.foldr b f + l.foldr b g := fun l f g hf hg => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hadd _ _ _ (wT l f hf) (wT l g hg)]; rfl
  have step : ∀ {P U : Type} [Zero U] (a : P → U → U) (M : ℕ) (f : U) (p : P),
      (∀ l : List P, l.length = M + 1 → l.foldr a f = 0) →
      ∀ l : List P, l.length = M → l.foldr a (a p f) = 0 := fun a M f p h l hl => by
    have := h (l ++ [p]) (by simp [hl])
    rwa [List.foldr_append] at this
  induction N with
  | zero =>
    intro N₁ N₂ f g hN _ _ k₁ _ l _
    have : f = 0 := k₁ [] (by simp; omega)
    rw [this, h1, w0]
  | succ N ih =>
    intro N₁ N₂ f g hN hf hg k₁ k₂ l hl
    rcases N₁ with _ | M₁
    · have : f = 0 := k₁ [] rfl
      rw [this, h1, w0]
    rcases N₂ with _ | M₂
    · have : g = 0 := k₂ [] rfl
      rw [this, h2, w0]
    obtain rfl | ⟨l', q, rfl⟩ := l.eq_nil_or_concat'
    · simp at hl
    have hl' : l'.length = N := by simpa using hl
    rw [List.foldr_append, List.foldr_cons, List.foldr_nil, hL q f g hf hg,
      wadd _ _ _ (hδ _ _ (ha₁ _ _ hf) hg) (hδ _ _ hf (ha₂ _ _ hg)),
      ih M₁ (M₂ + 1) _ _ (by omega) (ha₁ _ _ hf) hg (step _ _ _ _ k₁) k₂ l' hl',
      ih (M₁ + 1) M₂ _ _ (by omega) hf (ha₂ _ _ hg) k₁ (step _ _ _ _ k₂) l' hl', add_zero]

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}

theorem lineAt_mul_left (hθ : IsInfFam θ) {k m n : ℕ} (p : Mx D k m) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (Formalism.IndefR.Datum.compAt θ τ p * z) t = (HMul.hMul p (lineAt θ τ z t) : Mx D k n) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ Mx D k n :=
    { toFun := fun t => HMul.hMul p (lineAt θ τ z t)
      map_zero' := by rw [AddMonoidHom.map_zero, Matrix.mul_zero]
      map_add' := fun s t => by rw [AddMonoidHom.map_add (f := _), Matrix.mul_add] }
  have hL' : IsLineAt θ τ (Formalism.IndefR.Datum.compAt θ τ p * z) L := by
    refine ⟨continuous_const.matrix_mul hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (HMul.hMul p (lineAt θ τ z t) : Mx D k n).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1, Matrix.mul_zero]
    · show Formalism.IndefR.Datum.compAt θ τ' (HMul.hMul p (lineAt θ τ z t) : Mx D k n) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul]
      · rw [Matrix.mul_zero]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

variable {A B W H : HSp D} (o : OrthDec B W H)

theorem compAt_pA (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ o.pA = o.qA.map (tauE D τ) := by
  ext i j
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem compAt_pB (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ o.pB = o.qB.map (tauE D τ) := by
  ext i j
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem dRho_boxT (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin B.rank) (Fin A.rank) ℂ) {f : WO A W → ℂ} {g : WO A H → ℂ} (hf : IsThetaFunO ψ A W f)
    (hg : IsThetaFunO ψ A H g) :
    Formalism.IndefR.Datum.dRho (heisO ψ A B) θ τ z (o.boxT A f g) =
      o.boxT A (Formalism.IndefR.Datum.dRho (heisO ψ A W) θ τ (o.qA.map (tauE D τ) * z) f) g +
        o.boxT A f (Formalism.IndefR.Datum.dRho (heisO ψ A H) θ τ (o.qB.map (tauE D τ) * z) g) := by
  funext x
  have d := (hasDerivAt_dRho hθ hψ τ (o.qA.map (tauE D τ) * z) hf (o.resT A x).1).mul
    (hasDerivAt_dRho hθ hψ τ (o.qB.map (tauE D τ) * z) hg (o.resT A x).2)
  simp only [map_zero, heisO_zero] at d
  refine Eq.trans ?_ d.deriv
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [o.heisO_boxT, Pi.mul_apply, ← compAt_pA o hθ, ← compAt_pB o hθ, lineAt_mul_left hθ, lineAt_mul_left hθ]
  rfl

theorem qA_sumMat (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    o.qA.map (tauE D τ) * sumMat o sW sH τ = sW τ * o.qA.map (tauE D τ) := by
  simp only [sumMat_apply, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qA_iA, o.qA_iB,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem qB_sumMat (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    o.qB.map (tauE D τ) * sumMat o sW sH τ = sH τ * o.qB.map (tauE D τ) := by
  simp only [sumMat_apply, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qB_iA, o.qB_iB,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, zero_add]

theorem mul_cplxO {k m n : ℕ} {q : Matrix (Fin k) (Fin m) ℂ} {s : Matrix (Fin m) (Fin m) ℂ}
    {s' : Matrix (Fin k) (Fin k) ℂ} (h : q * s = s' * q) (r : Matrix (Fin n) (Fin n) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    q * cplxO r s z = cplxO r s' (q * z) := by
  unfold cplxO
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_assoc s']

theorem annih_boxT (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (s : Matrix (Fin A.rank) (Fin A.rank) ℂ) (sW : RealMat W) (sH : RealMat H)
    (z : Matrix (Fin B.rank) (Fin A.rank) ℂ) {f : WO A W → ℂ} {g : WO A H → ℂ} (hf : IsThetaFunO ψ A W f)
    (hg : IsThetaFunO ψ A H g) :
    annih (heisO ψ A B) θ τ (cplxO s (sumMat o sW sH τ)) z (o.boxT A f g) =
      o.boxT A (annih (heisO ψ A W) θ τ (cplxO s (sW τ)) (o.qA.map (tauE D τ) * z) f) g +
        o.boxT A f (annih (heisO ψ A H) θ τ (cplxO s (sH τ)) (o.qB.map (tauE D τ) * z) g) := by
  unfold annih
  rw [dRho_boxT o hθ hψ τ _ hf hg, dRho_boxT o hθ hψ τ _ hf hg, mul_cplxO (qA_sumMat o sW sH τ),
    mul_cplxO (qB_sumMat o sW sH τ)]
  funext x
  simp only [OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem isFockVec_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B W H : HSp D) (o : OrthDec B W H) (sA : RealMat A) (sW : RealMat W) (sH : RealMat H), IsStdChar D ψ (-1) → IsInfFam θ → ∀ Φ Φ', IsFockVec ψ θ A W sA sW Φ → IsFockVec ψ θ A H sA sH Φ' → IsFockVec ψ θ A B sA (sumMat o sW sH) (o.boxT A Φ Φ') := by
  intro D ψ θ A B W H o sA sW sH hψ hθ Φ₁ Φ₂ ⟨t₁, N₁, k₁⟩ ⟨t₂, N₂, k₂⟩
  have hT : ∀ (S : HSp D) τ J z f, IsThetaFunO ψ A S f → IsThetaFunO ψ A S (annih (heisO ψ A S) θ τ J z f) :=
    fun S τ J z f hf => theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ _ hf))
  refine ⟨o.isThetaFunO_boxT t₁ t₂, N₁ + N₂, ?_⟩
  refine killed_of_leibniz₂ (P₁ := D.what₂.Tau × Matrix (Fin W.rank) (Fin A.rank) ℂ)
    (P₂ := D.what₂.Tau × Matrix (Fin H.rank) (Fin A.rank) ℂ)
    (Q := D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (fun p f => annih (heisO ψ A W) θ p.1 (cplxO (sA p.1) (sW p.1)) p.2 f)
    (fun p f => annih (heisO ψ A H) θ p.1 (cplxO (sA p.1) (sH p.1)) p.2 f)
    (fun p f => annih (heisO ψ A B) θ p.1 (cplxO (sA p.1) (sumMat o sW sH p.1)) p.2 f)
    (IsThetaFunO ψ A W) (IsThetaFunO ψ A H) (IsThetaFunO ψ A B) (o.boxT A)
    (fun q => (q.1, o.qA.map (tauE D q.1) * q.2)) (fun q => (q.1, o.qB.map (tauE D q.1) * q.2))
    (fun p f hf => hT W _ _ _ f hf) (fun p f hf => hT H _ _ _ f hf) (fun p f hf => hT B _ _ _ f hf)
    (fun q f g hf hg => ?_) (fun q => ?_)
    (fun f g hf hg => o.isThetaFunO_boxT hf hg) (fun g => ?_) (fun f => ?_)
    (fun q f g hf hg => annih_boxT o hθ hψ q.1 (sA q.1) sW sH q.2 hf hg)
    _ N₁ N₂ Φ₁ Φ₂ le_rfl t₁ t₂ k₁ k₂
  · simp only [annih]
    rw [GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hf hg, GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hf hg, smul_add]
    abel
  · funext x
    simp [annih, Formalism.IndefR.Datum.dRho, heisO]
  · funext x
    simp [OrthDec.boxT]
  · funext x
    simp [OrthDec.boxT]

end GlobalTheory.Core.Rk.FockBoxT

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extendByZero_target_tensor_row_product : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), extFun β α₀ (tensRow Ψ b) = o.boxT T (extFun β α Ψ) (GlobalTheory.FinPl.ExtZero.rowFun β ζ b) := by
  exact @GlobalTheory.FinPl.ExtZero.extFun_tensRow
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_source_box_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (o.boxS T Φ (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT))) := by
  first | exact @GlobalTheory.FinPl.ExtZero.SBBox.isSBHalf_boxS | exact GlobalTheory.FinPl.ExtZero.SBBox.isSBHalf_boxS | (intros; apply GlobalTheory.FinPl.ExtZero.SBBox.isSBHalf_boxS <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_target_box_dualIndicator : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) = o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) (o.boxT T Φ (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT))) := by
  first | exact @GlobalTheory.FinPl.ExtZero.isSBHalf_boxT_rowFun_dualInd | exact GlobalTheory.FinPl.ExtZero.isSBHalf_boxT_rowFun_dualInd | (intros; apply GlobalTheory.FinPl.ExtZero.isSBHalf_boxT_rowFun_dualInd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extendByZero_mem_completed_lattice_source : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), (∀ u : WO A T, MxAt (· = p.v) u → (u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), ψ (symplO A T u u') = 1)) → (∀ u : WO S T, MxAt (· = p.v) u → (u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), ψ (symplO S T u u') = 1)) → halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), (o.resS T).symm (u, 0) ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  first | exact @GlobalTheory.FinPl.ExtZero.extZero_mem_latO | exact GlobalTheory.FinPl.ExtZero.extZero_mem_latO | (intros; apply GlobalTheory.FinPl.ExtZero.extZero_mem_latO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.datum_list_cons_eq_idempotent_tensor : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (i : ι) (J : List ι), i ∉ J → (∀ j ∈ J, (p i).e * (p j).e = 0) → GlobalTheory.FinPl.PutIn.datJ p α β Ψ (i :: J) = GlobalTheory.FinPl.PutIn.tens (p i).e (GlobalTheory.FinPl.PutIn.datJ p α β Ψ J) (extFun (α i) (β i) (Ψ i)) := by
  exact @GlobalTheory.FinPl.PutIn.datJ_cons
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.continuous_idempotentCut_and_isClosed_scaledKernel : ∀ (D : D7) (V : HSp D), (∀ (ε : AF D.host.F) (hε : ε * ε = ε), Continuous (GlobalTheory.FinPl.SetCut.cutG V ε hε)) ∧ ∀ c : AF D.host.F, IsClosed {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} := by
  first | exact @GlobalTheory.FinPl.SetCut.continuous_cutG_and_isClosed | exact GlobalTheory.FinPl.SetCut.continuous_cutG_and_isClosed | (intros; apply GlobalTheory.FinPl.SetCut.continuous_cutG_and_isClosed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryIdempotentCut_mem_fourierJacobi_besselGroup : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (ε : AF D.host.F) (hε : ε * ε = ε), (∀ g ∈ jacGrp d, GlobalTheory.FinPl.SetCut.cutG V ε hε g ∈ jacGrp d) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∀ g ∈ besGrp d o, GlobalTheory.FinPl.SetCut.cutG V ε hε g ∈ besGrp d o := by
  first | exact @GlobalTheory.FinPl.SetCut.cutG_mem_jacGrp_besGrp | exact GlobalTheory.FinPl.SetCut.cutG_mem_jacGrp_besGrp | (intros; apply GlobalTheory.FinPl.SetCut.cutG_mem_jacGrp_besGrp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BiJoinDeriv

open GlobalTheory.BiTransfer GlobalTheory.WeilVacMove GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem dLine_apply' {S T : HSp D} {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a))
    {L : ℝ →+ WO S T} (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dLine ψ S T L f w = phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := by
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth
  have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
      f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
    funext t
    rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
  unfold dLine
  rw [e]
  exact (hasDerivAt_exp_mul _ _ f hfs _ w).deriv

theorem dLine_add_line (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {L L' : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (hL' : Continuous L') (hL0' : ∀ t, (L' t).map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T (L + L') f = dLine ψ S T L f + dLine ψ S T L' f := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hS : Continuous (L + L') := hL.add hL'
  have hS0 : ∀ t, ((L + L') t).map (finPart D) = 0 := fun t => by
    ext i j
    have h := congrFun (congrFun (hL0 t) i) j
    have h' := congrFun (congrFun (hL0' t) i) j
    simpa [Matrix.map_apply, (finPart D).map_add] using congrArg₂ (· + ·) h h'
  funext w
  rw [Pi.add_apply, dLine_apply' h hl hlam hS hS0 hf, dLine_apply' h hl hlam hL hL0 hf, dLine_apply' h hl hlam hL' hL0' hf,
    AddMonoidHom.add_apply, map_add, ContinuousLinearMap.map_add]
  have e : phase lam S T (L 1 + L' 1) w = phase lam S T (L 1) w + phase lam S T (L' 1) w := by
    show lam (symplOH S T w (L 1 + L' 1)) = lam (symplOH S T w (L 1)) + lam (symplOH S T w (L' 1))
    rw [symplOH_add_right, map_add (f := _)]
  rw [e]
  ring

variable {W A A' : HSp D} (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (S : HSp D)

theorem inl_fst_add_inr_snd (x : WO W S) : inlH d S (fstH d S x) + inrH d S (sndH d S x) = x := by
  rw [inlH_apply, inrH_apply, fstH_apply, sndH_apply, ← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add]
  have : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S A' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger A' S (d.resS S x).2) = (d.resS S x).2 :=
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger A' S _
  rw [this, Prod.mk.eta, AddEquiv.symm_apply_apply]

theorem dLine_inlH (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO A S) :
    dLine ψ W S ((inlH d S).comp M) (join d S G) = join d S (fun u v => dLine ψ A S M (fun u' => G u' v) u) := by
  funext x
  simp only [dLine, join_apply]
  congr 1
  funext t
  simp only [AddMonoidHom.comp_apply, heisO, symplOH_split d, map_add (fstH d S), map_add (sndH d S), fst_inl, snd_inl,
    GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, join_apply]

theorem dLine_inrH (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO S A') :
    dLine ψ W S ((inrH d S).comp M) (join d S G) = join d S (fun u v => dLine ψ S A' M (G u) v) := by
  funext x
  simp only [dLine, join_apply]
  congr 1
  funext t
  simp only [AddMonoidHom.comp_apply, heisO, symplOH_split d, map_add (fstH d S), map_add (sndH d S), fst_inr, snd_inr,
    GlobalTheory.WeilVacMove.symplOH_zero_right, zero_add, add_zero, join_apply]

end GlobalTheory.BiJoinDeriv

namespace GlobalTheory.BiJoinDeriv

open GlobalTheory.BiTransfer GlobalTheory.WeilVacMove

theorem dLine_join : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W A S A' : HSp D) (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → ∀ M : ℝ →+ WO W S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (∀ s, (GlobalTheory.BiTransfer.fstH d S (M s)).map (finPart D) = 0) ∧ (∀ s, (GlobalTheory.BiTransfer.sndH d S (M s)).map (finPart D) = 0) ∧ GlobalTheory.WeilVacMove.dLine ψ W S M (GlobalTheory.BiTransfer.join d S G) = GlobalTheory.BiTransfer.join d S fun u v => GlobalTheory.WeilVacMove.dLine ψ A S ((GlobalTheory.BiTransfer.fstH d S).comp M) (fun u' => G u' v) u + GlobalTheory.WeilVacMove.dLine ψ S A' ((GlobalTheory.BiTransfer.sndH d S).comp M) (G u) v := by
  intro D ψ hψ W A S A' d G hG M hM hM0
  have h1 : ∀ s, (fstH d S (M s)).map (finPart D) = 0 := fun s => map_mul_eq_zero_left _ (hM0 s) _
  have h2 : ∀ s, (sndH d S (M s)).map (finPart D) = 0 := fun s => fin_dagger A' S (map_mul_eq_zero_left _ (hM0 s) _)
  refine ⟨h1, h2, ?_⟩
  have hj := isThetaFunO_join d hG
  have eM : M = (inlH d S).comp ((fstH d S).comp M) + (inrH d S).comp ((sndH d S).comp M) := by
    ext1 t
    exact (inl_fst_add_inr_snd d S (M t)).symm
  rw [eM, dLine_add_line hψ ((continuous_inlH d S).comp ((continuous_fstH d S).comp hM)) (fun t => map_inlH d S _ (h1 t))
    ((continuous_inrH d S).comp ((continuous_sndH d S).comp hM)) (fun t => fin_inrH d S (h2 t)) hj,
    dLine_inlH, dLine_inrH, ← eM]
  funext x
  simp only [Pi.add_apply, join_apply]

end GlobalTheory.BiJoinDeriv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BiDeriv

open GlobalTheory.BiTransfer

variable {D : D7}

theorem dLine_inl (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO A S) :
    GlobalTheory.WeilVacMove.dLine ψ _ S ((inlH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) (join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S G) =
      join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S (fun u v => GlobalTheory.WeilVacMove.dLine ψ A S M (fun u' => G u' v) u) := by
  funext x
  simp only [GlobalTheory.WeilVacMove.dLine, join_apply]
  congr 1
  funext t
  simp only [AddMonoidHom.comp_apply, heisO, join_apply, map_add, fst_inl, snd_inl, add_zero]
  rw [symplOH_split (sumDec A (GlobalTheory.ChiGrid.negSp A')) S, fst_inl, snd_inl,
    GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero]

theorem dLine_inr (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO S A') :
    GlobalTheory.WeilVacMove.dLine ψ _ S ((inrH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) (join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S G) =
      join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S (fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M (G u) v) := by
  funext x
  simp only [GlobalTheory.WeilVacMove.dLine, join_apply]
  congr 1
  funext t
  simp only [AddMonoidHom.comp_apply, heisO, join_apply, map_add, fst_inr, snd_inr, add_zero]
  rw [symplOH_split (sumDec A (GlobalTheory.ChiGrid.negSp A')) S, fst_inr, snd_inr,
    GlobalTheory.WeilVacMove.symplOH_zero_right, zero_add]

theorem isBiTheta_dLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → (∀ M : ℝ →+ WO A S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → IsBiTheta ψ A S A' fun u v => GlobalTheory.WeilVacMove.dLine ψ A S M (fun u' => G u' v) u) ∧ ∀ M' : ℝ →+ WO S A', Continuous M' → (∀ s, (M' s).map (finPart D) = 0) → IsBiTheta ψ A S A' fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u) v := by
  intro D ψ hψ A S A' G hG
  have hj := isThetaFunO_join (sumDec A (GlobalTheory.ChiGrid.negSp A')) hG
  refine ⟨fun M hM hM0 => ?_, fun M hM hM0 => ?_⟩
  · have h := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ (L := (inlH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) ((continuous_inlH _ S).comp hM)
      (fun t => map_inlH _ S _ (hM0 t)) hj).2
    rw [dLine_inl] at h
    exact isBiTheta_of_join _ h
  · have h := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ (L := (inrH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) ((continuous_inrH _ S).comp hM)
      (fun t => fin_inrH _ S (hM0 t)) hj).2
    rw [dLine_inr] at h
    exact isBiTheta_of_join _ h

end GlobalTheory.BiDeriv

end
end

section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling


theorem _root_.GlobalTheory.T.exists_borel_spherical_same_double_coset_sums_zonal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), HasSatake π α → ∀ ω : GL (Fin n) k → ℂ, IsZonal π (KO k (Fin n)) ω → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ ∀ g, Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) ω 1 = Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) φ 1 := by
  first | exact @GlobalTheory.ZonalBorel.exists_isBorelSph_hAct_eq | exact GlobalTheory.ZonalBorel.exists_isBorelSph_hAct_eq | (intros; apply GlobalTheory.ZonalBorel.exists_isBorelSph_hAct_eq <;> assumption)
end
