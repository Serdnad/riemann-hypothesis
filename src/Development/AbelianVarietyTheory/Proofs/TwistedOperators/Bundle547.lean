module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle532
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle537
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle050
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle533
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle475
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle439
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle331
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle349
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle438
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle346
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical


theorem _root_.GlobalTheory.T.exists_archimedeanOperator_weilRep_pureTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ h ∈ UAt σ W (evI F), ∃ T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (T f) := by
  first | exact @GlobalTheory.ArchFactorPair.exists_archOperator_pair | exact GlobalTheory.ArchFactorPair.exists_archOperator_pair | (intros; apply GlobalTheory.ArchFactorPair.exists_archOperator_pair <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix


theorem _root_.GlobalTheory.T.firstMember_lieAlgebra_preserves_polynomialFock : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → GlobalTheory.LFun.IsHecke F E χX → GlobalTheory.LFun.IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w, (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  first | exact @GlobalTheory.RealLieFockX.lie_deriv_polX | exact GlobalTheory.RealLieFockX.lie_deriv_polX | (intros; apply GlobalTheory.RealLieFockX.lie_deriv_polX <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical


theorem _root_.GlobalTheory.T.archimedeanPoint_pureTensor_keeps_finiteFactor : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F), ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ c : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      om (1, g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure c φ := by
  first | exact @GlobalTheory.ArchPure.pure_arch | exact GlobalTheory.ArchPure.pure_arch | (intros; apply GlobalTheory.ArchPure.pure_arch <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.OscLie

theorem exists_lie_deriv_pol : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')), ∀ f ∈ G.M.Pol B.ψ B.emb,
      δ f ∈ G.M.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ
  choose T hT' using fun t : ℝ => GlobalTheory.T.exists_archOperator_unitaryW_seesaw B G X om om' hT (γ (Multiplicative.ofAdd t)) (hγ.2 _)
  have hvac : ∀ f₀, G.M.IsGauss B.ψ B.emb f₀ → f₀ ∈ G.M.Pol B.ψ B.emb := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hstab : ∀ u, At (evI F) u → ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      ActsD (evI F) (G.M.heisLine B.ψ u) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb := fun u hu f hf f₁ h =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h
  let N : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) :=
    { carrier := {f | f ∈ G.M.Pol B.ψ B.emb ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f p.2) ∧
        ∃ f' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0}
      zero_mem' := ⟨zero_mem _, by simpa using contDiff_const, 0, zero_mem _, fun x => by simpa using hasDerivAt_const _ _⟩
      add_mem' := by
        rintro f g ⟨hf, hf1, f', hf', hf2⟩ ⟨hg, hg1, g', hg', hg2⟩
        refine ⟨add_mem hf hg, by simpa using hf1.add hg1, f' + g', add_mem hf' hg', fun x => ?_⟩
        show HasDerivAt (fun t => T t (f + g) x) ((f' + g') x) 0
        simp only [map_add (f := _), SchwartzMap.add_apply]
        exact (hf2 x).add (hg2 x)
      smul_mem' := by
        rintro c f ⟨hf, hf1, f', hf', hf2⟩
        refine ⟨Submodule.smul_mem _ c hf, by simpa using hf1.const_smul c, c • f', Submodule.smul_mem _ c hf', fun x => ?_⟩
        simpa using (hf2 x).const_mul c }
  have hPN : G.M.Pol B.ψ B.emb ≤ N := by
    refine sInf_le ⟨fun f₀ h => ?_, fun u hu f hf f₁ h => ?_⟩
    · exact ⟨hvac f₀ h, GlobalTheory.T.weilAction_oneParamSubgroup_gaussVacuum_smooth B G X om om' hT γ hγ T hT' f₀ h⟩
    · obtain ⟨hf0, hf1, hf2⟩ := hf
      exact ⟨hstab u hu f hf0 f₁ h, GlobalTheory.T.smooth_weilOrbit_preserved_by_heisenbergDerivatives B G X om om' hT γ hγ T hT' u hu f hf0 hf1 hf2 f₁ h⟩
  have hex : ∀ f : G.M.Pol B.ψ B.emb, ∃ f' : SInf F (Fin a × Fin (a + a')), f' ∈ G.M.Pol B.ψ B.emb ∧
      ∀ x, HasDerivAt (fun t => T t (f : SInf F (Fin a × Fin (a + a'))) x) (f' x) 0 := fun f => by
    obtain ⟨-, -, f', hf', h⟩ := hPN f.2
    exact ⟨f', hf', h⟩
  choose d hdP hd using hex
  have huniq : ∀ (f g₁ g₂ : SInf F (Fin a × Fin (a + a'))), (∀ x, HasDerivAt (fun t => T t f x) (g₁ x) 0) →
      (∀ x, HasDerivAt (fun t => T t f x) (g₂ x) 0) → g₁ = g₂ := fun f g₁ g₂ h₁ h₂ =>
    SchwartzMap.ext fun x => (h₁ x).unique (h₂ x)
  let δ₀ : G.M.Pol B.ψ B.emb →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    { toFun := d
      map_add' := fun f g => huniq _ _ _ (hd (f + g)) (fun x => by
        show HasDerivAt (fun t => T t ((f : SInf F (Fin a × Fin (a + a'))) + g) x) ((d f + d g) x) 0
        simp only [map_add (f := _), SchwartzMap.add_apply]
        exact (hd f x).add (hd g x))
      map_smul' := fun c f => huniq _ _ _ (hd (c • f)) (fun x => by simpa using (hd f x).const_mul c) }
  obtain ⟨δ, hδ⟩ := LinearMap.exists_extend δ₀
  have e : ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), δ f = d ⟨f, hf⟩ := fun f hf => by
    have := congrArg (fun φ => φ ⟨f, hf⟩) hδ
    exact this
  refine ⟨δ, fun f hf => ⟨by rw [e f hf]; exact hdP _, fun r hr x => ?_⟩⟩
  have h1 : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) = tens (evI F) (T t f) r :=
    fun t => hT' t f r hr
  simp only [h1]
  rw [e f hf]
  exact (hd ⟨f, hf⟩ _).mul_const (r x)

end GlobalTheory.OscLie
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix


theorem _root_.GlobalTheory.T.firstMember_maximalCompact_preserves_polynomialFock : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → GlobalTheory.LFun.IsHecke F E χX → GlobalTheory.LFun.IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w, (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X τ, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  first | exact @GlobalTheory.FockCompactX.pol_stable_compact_left | exact GlobalTheory.FockCompactX.pol_stable_compact_left | (intros; apply GlobalTheory.FockCompactX.pol_stable_compact_left <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefUnfold

theorem isoPart_add' {D : D7} (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y z : Mx D W.rank r) :
    isoPart V W C (y + z) = isoPart V W C y + isoPart V W C z := by
  unfold isoPart
  rw [Matrix.add_mul]

private theorem symplOH_eq_zero_of_symplO_eq_zero {D : D7} (S T : HSp D) (a b : WO S T) (h : symplO S T a b = 0) :
    symplOH S T a b = 0 := by
  have h2 : (2 : AF D.host.F) * symplOH S T a b = 0 := by
    rw [two_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 a b, h]
  have hu : IsUnit (2 : AF D.host.F) := by
    have e : (algebraMap D.host.F (AF D.host.F)) 2 = 2 := map_ofNat _ 2
    rw [← e]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  exact hu.mul_right_eq_zero.1 h2

theorem sum_translates_eq : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ y : Mx D W.rank r, Summable (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV‖) → ∑' a : Matrix (Fin W.rank) (Fin r) D.host.E, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = κ • ∫ y' in 𝓨, ∫ x in 𝓕', F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  intro D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ F G hF hG y hs
  have hY' := hY
  obtain ⟨hμH, hYF, hY1⟩ := hY'
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  haveI : IsTopologicalAddGroup (Mx D W.rank r) := i1
  haveI : LocallyCompactSpace (Mx D W.rank r) := i2
  haveI : SecondCountableTopology (Mx D W.rank r) := i3
  haveI : T2Space (Mx D W.rank r) := i4
  haveI : DiscreteTopology (ratMx D W.rank r) := i5
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : Countable D.host.E := Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin W.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin r → D.host.E))
  have hsp := GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal D V V' W r C B hCB C' h1 h2 h3
  have hiso0 : isoPart V W C' (0 : Mx D W.rank r) = 0 := by
    have e := isoPart_add' V W C' (0 : Mx D W.rank r) 0
    rw [add_zero] at e
    have e' : isoPart V W C' (0 : Mx D W.rank r) + isoPart V W C' 0 = isoPart V W C' 0 + 0 := by
      rw [add_zero]; exact e.symm
    exact add_left_cancel e'
  have hpt : ∀ (y' : Mx D W.rank r) (x : WO V' W),
      heisO ψ V W (isoPart V W C y) F (isoPart V W C y' + midPart V V' W B x) =
        F (isoPart V W C (y + y') + midPart V V' W B x) := by
    intro y' x
    have z1 : symplOH V W (isoPart V W C y') (isoPart V W C y) = 0 :=
      symplOH_eq_zero_of_symplO_eq_zero V W _ _ (hsp.1 y' y)
    have z2 : symplOH V W (midPart V V' W B x) (isoPart V W C y) = 0 := by
      rw [GlobalTheory.MixModel.symplOH_skew, symplOH_eq_zero_of_symplO_eq_zero V W _ _ (hsp.2.1 y x), neg_zero]
    show ψ (symplOH V W (isoPart V W C y' + midPart V V' W B x) (isoPart V W C y)) *
        F (isoPart V W C y' + midPart V V' W B x + isoPart V W C y) = _
    rw [(GlobalTheory.OrientedFormLaws.symplOH_laws D V W).1, z1, z2, add_zero, AddChar.map_zero_eq_one, one_mul,
      isoPart_add']
    congr 1
    abel
  have hP : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C y) F) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1 _ _ hF
  let χ : Matrix (Fin W.rank) (Fin r) D.host.E → Mx D W.rank r → ℂ :=
    fun a t => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))
  let Φ : Mx D W.rank r → ℂ := fun t => κ • ∫ y' in 𝓨, ∫ x in 𝓕',
    heisO ψ V W (isoPart V W C y) F (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) *
      star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ
  have hterm : ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E,
      (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) =
        ∫ t in 𝓨, χ a t * Φ t ∂μ := fun a =>
    GlobalTheory.T.matrixCoeff_isotropicTranslates_eq_fourierCoeffs D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ F G hF hG y a
  obtain ⟨hχc, hχx, hχa, hχΓ, hχ0⟩ := GlobalTheory.T.isotropic_part_rational_characters_adelic_matrices D V V' W r C B hCB C' h1 h2 h3 ψ hψ
  obtain ⟨hΦc, hΦp⟩ := GlobalTheory.T.thetaProductMean_continuous_periodic_dualVariable D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μ' 𝓕' hμ' hF' _ G hP hG
  have hsum : Summable (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ t in 𝓨, χ a t * Φ t ∂μ‖) := by
    have e : (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ t in 𝓨, χ a t * Φ t ∂μ‖) =
        fun a => ‖∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV‖ :=
      funext fun a => by rw [hterm a]
    rw [e]
    exact hs
  have key := GlobalTheory.T.fourier_inversion_zero_compact_quotient (Mx D W.rank r) (ratMx D W.rank r) K hK hKc (Matrix (Fin W.rank) (Fin r) D.host.E) χ
    hχc (fun a t s => hχx a t s) (fun a b t => hχa a b t) (fun a t => hψ.1.2.1 _) hχΓ hχ0 μ 𝓨 hμH hYF hY1 Φ
    (hΦc.const_smul κ) (fun γ hγ t => congrArg (fun z : ℂ => κ • z) (hΦp γ hγ t)) hsum
  rw [tsum_congr hterm, ← key]
  show κ • (∫ y' in 𝓨, ∫ x in 𝓕',
    heisO ψ V W (isoPart V W C y) F (isoPart V W C' 0 + isoPart V W C y' + midPart V V' W B x) *
      star (G (isoPart V W C' 0 + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = _
  simp only [hiso0, zero_add]
  simp_rw [hpt]

private theorem symplOH_eq_zero_of_symplO_eq_zero' {D : D7} (S T : HSp D) (a b : WO S T) (h : symplO S T a b = 0) :
    symplOH S T a b = 0 := by
  have h2 : (2 : AF D.host.F) * symplOH S T a b = 0 := by
    rw [two_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 a b, h]
  have hu : IsUnit (2 : AF D.host.F) := by
    have e : (algebraMap D.host.F (AF D.host.F)) 2 = 2 := map_ofNat _ 2
    rw [← e]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  exact hu.mul_right_eq_zero.1 h2

theorem coef_unfold : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ ν : Measure (Mx D W.rank r), ν.IsAddHaarMeasure ∧ ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ x : WO V' W, ∫ w in 𝓕', heisO ψ V' W x (res V V' W C B μ 𝓨 F) w * star (res V V' W C B μ 𝓨 G w) ∂μ' = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B x) F w * star (G w) ∂μV) ∂ν := by
  intro D V V' W r C B hCB ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding D V V' r C B hCB
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.integral_hom_fundamental_domain_isotropic_split_coords D V V' W r C B hCB C' h1 h2 h3 μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  have hY' := hY
  obtain ⟨hμH, hYF, -⟩ := hY'
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := hμH
  have hc0 : ENNReal.ofReal κ⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hκ0)).ne'
  refine ⟨ENNReal.ofReal κ⁻¹ • μ, MeasureTheory.Measure.IsAddHaarMeasure.smul μ hc0 ENNReal.ofReal_ne_top, ?_⟩
  intro F G hF hG x
  have hsp := GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal D V V' W r C B hCB C' h1 h2 h3
  have hF₁ := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1 (midPart V V' W B x) F hF
  have he : ∀ y : Mx D W.rank r, heisO ψ V W (isoPart V W C y) (heisO ψ V W (midPart V V' W B x) F) =
      heisO ψ V W (isoPart V W C y + midPart V V' W B x) F := by
    intro y
    rw [(GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).2.1, symplOH_eq_zero_of_symplO_eq_zero' V W _ _ (hsp.2.1 y x),
      AddChar.map_zero_eq_one, one_smul]
  rw [← ((GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hCB ψ hψ μ 𝓨 hY).1 F hF).2.2.1 x,
    ← GlobalTheory.T.isotropicMean_thetaProduct_conj_eq_restrictionProduct D V V' W r C B hCB ψ hψ μ 𝓨 hY μ' 𝓕' hμ' hF' _ G hF₁ hG]
  simp_rw [← he]
  obtain ⟨hsum, hint⟩ := GlobalTheory.T.integral_eq_setIntegral_tsum_rationalTranslates D W.rank r μ 𝓨 hμH hYF
    (fun y => ∫ w in 𝓕V, heisO ψ V W (isoPart V W C y) (heisO ψ V W (midPart V V' W B x) F) w * star (G w) ∂μV)
    (GlobalTheory.T.integrable_matrixCoeff_adelicIsotropicPart D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ hμH μV 𝓕V hμV hFV _ G hF₁ hG)
  beta_reduce at hsum hint
  rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 hκ0).le, hint,
    ← MeasureTheory.integral_smul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hsum] with y hy
  rw [sum_translates_eq D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ _ G hF₁ hG y hy,
    smul_smul, inv_mul_cancel₀ hκ0.ne', one_smul]

end GlobalTheory.CoefUnfold

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isotropicMean_changes_by_scalar_of_trivial_action : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (HMul.hMul (HMul.hMul (P.map (incA D)) (y' : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (ratMx D a b) μ 𝓨 → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∃ y : Mx D a b, actO V W g h x = x + (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → ∃ c : Circle, ∀ f, IsThetaFunO ψ V W f → ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∫ y in 𝓨, heisO ψ V W x (ω (g, h) f) (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = (c : ℂ) * ∫ y in 𝓨, heisO ψ V W x f (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  first | exact @GlobalTheory.IsoMean.mean_scalar | exact GlobalTheory.IsoMean.mean_scalar | (intros; apply GlobalTheory.IsoMean.mean_scalar <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinear

open GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove

variable {D : D7} {S T : HSp D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_nsmul_actO (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT)
    (g : GA D S) (h : GA D T) : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      N • actO S T g h u ∈ latO S T ΛS ΛT fun _ => True := by
  obtain ⟨M, hM, hMu⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.toIsLattice.fg hT.toIsLattice.fg
  obtain ⟨K, hK, hKt⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_mul (Formalism.L2.Herm.intAf D.host.F D.host.E)
    (fun z => GlobalTheory.PlaceDatum.exists_den_adele z) ((Formalism.L2.Theta.mt T h).map (toEAf D))
    ((Formalism.L2.Theta.mt S g⁻¹).map (toEAf D))
  refine ⟨K * (N * M), Nat.mul_pos hK (Nat.mul_pos hN hM), fun u hu => ?_⟩
  rw [← smul_smul]
  apply hKt
  · have h0 := GlobalTheory.SplitScalar.latO_fin hu
    have hz : (actO S T g h u).map (infPart D) = 0 := by
      simp only [actO, Matrix.map_mul, h0, Matrix.mul_zero, Matrix.zero_mul]
    ext i j
    have hij := congrFun (congrFun hz i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul, Matrix.zero_apply] at hij ⊢
    rw [hij, smul_zero]
  · intro i j
    have hX := hNm M (u.map (toEAf D)) (fun i j => hMu u hu i j) i j
    have e1 : toEAf D (((N * M) • actO S T g h u) i j) = ((N * M : ℕ) : EAf D) *
        ((Formalism.L2.Theta.mt T h).map (toEAf D) * u.map (toEAf D) * (Formalism.L2.Theta.mt S g⁻¹).map (toEAf D)) i j := by
      simp only [actO]
      rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    rw [e1]
    exact hX

theorem isSBHalf_actO (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT) {a : AE D}
    (g : GA D S) (h : GA D T) {Φ : WO S T → ℂ} (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) :
    IsSBHalf a (latO S T ΛS ΛT fun _ => True) fun t => Φ (actO S T g h t) := by
  simp only [IsSBHalf] at hΦ ⊢
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  obtain ⟨N, hN, hNu⟩ := exists_nsmul_actO hS hT g h
  obtain ⟨M, hM, hMu⟩ := exists_nsmul_actO hS hT g⁻¹ h⁻¹
  refine ⟨fun t ht => isHalf_of_act g h (h1 _ ht), k * (N * M), Nat.mul_pos hk (Nat.mul_pos hN hM), ?_, ?_⟩
  · intro u hu hua t
    rw [act_add, act_nsmul]
    have hw := hNu u hu
    have hwa : IsHalf a (N • actO S T g h u) :=
      GlobalTheory.SplitScalar.isHalf_nsmul (GlobalTheory.SplitHecke.isHalf_actO g h hua) N
    have e : (k * (N * M)) • actO S T g h u = k • (M • (N • actO S T g h u)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [e]
    exact h2 _ (AddSubgroup.nsmul_mem _ hw M) (GlobalTheory.SplitScalar.isHalf_nsmul hwa M) _
  · intro t ht
    have hm := hMu _ (h3 _ ht)
    rw [act_nsmul, GlobalTheory.SplitHecke.actO_inv_actO] at hm
    have e : (k * (N * M)) • t = N • (M • (k • t)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [e]
    exact AddSubgroup.nsmul_mem _ hm N

theorem absV_mul {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : (Fv F v)ˣ) :
    absV F v (x * y) = absV F v x * absV F v y := by
  unfold absV
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  rw [Units.val_mul, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), zpow_add₀ hq]

theorem absFin_mul (x y : (AE D)ˣ) : absFin D (x * y) = absFin D x * absFin D y := by
  unfold absFin
  simp_rw [map_mul, absV_mul]
  exact finprod_mul_distrib (absFin_finite D x) (absFin_finite D y)

theorem absFin_one : absFin D 1 = 1 := by
  have h := absFin_mul (D := D) 1 1
  rw [mul_one] at h
  have hp := absFin_pos D 1
  have h2 : absFin D 1 * (absFin D 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hp.ne'
  · linarith

theorem modFac_mul (x x' y y' : (AE D)ˣ) : modFac S T (x * x') (y * y') = modFac S T x y * modFac S T x' y' := by
  unfold modFac
  rw [absFin_mul, absFin_mul, Real.mul_rpow (absFin_pos D x).le (absFin_pos D x').le,
    Real.mul_rpow (absFin_pos D y).le (absFin_pos D y').le]
  ring

theorem modFac_one : modFac S T 1 1 = 1 := by
  unfold modFac
  rw [absFin_one, Real.one_rpow, Real.one_rpow, one_mul]

end GlobalTheory.SplitLinear

end
end
