module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle393
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle459
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle334
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle047
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle045
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle551
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle015
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle035
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle036
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KFinAlg
theorem polynomial_vector_kFinite (fockFirst : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∃ (A : InfinitePlace F → Matrix (Fin a) (Formalism.BasicNotions.TH.Ix (a - Γ.p) Γ.p) ℂ)
      (Φ : GlobalTheory.RealLift.Tens F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (c : InfinitePlace F → ℂ),
      (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w))) (A w)) ∧
      (∀ w, Γ.V.θ w * A w = A w * Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p) ∧
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.RealLift.ActsBy Bs.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) c) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb,
    ∃ P : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), FiniteDimensional ℂ P ∧ P ≤ Γ.M.Pol Bs.ψ Bs.emb ∧
      f ∈ P ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ g ∈ P, ∃ g₁ ∈ P,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) (⇑g) (⇑g₁) := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT f hf
  classical
  obtain ⟨A, Φ, c, hA, hAθ, hr, hact⟩ := fockFirst hPr F E σ Bs a a' Γ Xc om om' hT
  have hb := hT.base
  have hwp : GlobalTheory.WeilM.IsUWeilPair (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.WeilM.adeleClass F) Bs.ψ (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.W.J) Γ.M.co Xc.β (Xc.β / Xc.α) om := hT.weil
  have hadm := fun g => (hwp.isUSplitting).adm g
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain ⟨D, hD⟩ := exists_tensDeg T
  haveI : FiniteDimensional ℂ (tensDeg F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) D) :=
    LinearMap.finiteDimensional_range _
  refine ⟨(tensDeg F _ _ _ _ D).map Φ, inferInstance, hr ▸ LinearMap.map_le_range, ⟨T, hD, rfl⟩, ?_⟩
  rintro k hk _ ⟨T', hT', rfl⟩
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.T.unitaryLieElements_generate_oneParamLines F E σ (Fin a) _ _ Bs.emb
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) 1 A Γ.V.θ hb.cm hA hAθ k hk.1 hk.2
  let L := GlobalTheory.RealLift.sumPl (fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
    (c w * (Yg w).trace) • (1 : Module.End ℂ _))
  have hloc : GlobalTheory.RealLift.LocFin L := GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w v => by
    obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights _ _ _ _).1 v
    exact ⟨W, hW, hv, fun y hy => W.add_mem (hs (Yg w) (hKC w) y hy) (W.smul_mem _ hy)⟩
  obtain ⟨U, hexp, hSA⟩ := GlobalTheory.T.weakExponential_action_on_fockVectors F (Fin a × Fin (a + a')) _ Φ L ((om.comp (MonoidHom.inl _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  let Lw : ∀ w : InfinitePlace F, Module.End ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
      (c w * (Yg w).trace) • (1 : Module.End ℂ _)
  let Nw : ∀ w : InfinitePlace F, Submodule ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun _ => MvPolynomial.restrictTotalDegree _ ℂ D
  have hN : ∀ i, ∀ z ∈ Nw i, Lw i z ∈ Nw i := by
    intro i z hz
    simp only [Lw, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.add_mem _ (GlobalTheory.FockPolGK.kStable1 _ _ _ _ D (Yg i) (hKC i) z hz) (Submodule.smul_mem _ _ hz)
  have hLst : ∀ y ∈ tensDeg F _ _ _ _ D, L y ∈ tensDeg F _ _ _ _ D := by
    intro y hy
    change GlobalTheory.RealLift.sumPl Lw y ∈ _
    rw [GlobalTheory.RealLift.sumPl, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun w _ => GlobalTheory.RealLift.atPl_mem_range_map Lw Nw hN w y hy
  refine ⟨Φ (U T'), ⟨U T', exp_stable hexp _ hLst T' hT', rfl⟩, ?_⟩
  have h1 := hSA T'
  change GlobalTheory.RealLift.SA (om (γ (Multiplicative.ofAdd 1), 1)) (Φ T') (Φ (U T')) at h1
  rw [hγ1] at h1
  exact (GlobalTheory.RealLift.actsLaws F _ (Φ T') (Φ (U T')) (Φ (U T'))).2.1 _ (map_zero _) h1
theorem derivation_algebra_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT ΦD hΦ
  have hPair := GlobalTheory.ThK.RealUniq.isPair_V hT
  have hstdM := hPair.good.std
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hcof, rfl⟩ := hx
    obtain ⟨P, hPfin, hPle, hfP, hPst⟩ := _root_.GlobalTheory.SquareAgree.KFinAlg.polynomial_vector_kFinite _root_.GlobalTheory.T.real_lift_exists_fock_map hPr F E σ Bs a a' Γ Xc om om' hT f hf
    have hstd : ∀ᶠ v in Filter.cofinite,
        φ v = Set.indicator {x : Fin a × Fin (a + a') → Fv F v |
          ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hcof, hstdM] with v h1 h2
      rw [h1, h2]
    refine ⟨P.map (pureL φ), inferInstance, ?_, ⟨f, hfP, rfl⟩, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact Submodule.subset_span ⟨g, φ, hPle hg, hSB, hcof, rfl⟩
    · rintro k hk _ ⟨g, hg, rfl⟩
      obtain ⟨g₁, hg₁, hA⟩ := hPst k hk g hg
      have key : om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ :=
        hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure _ _ hSB hstd)
      exact ⟨g₁, hg₁, key.symm⟩
  | zero =>
    exact ⟨⊥, inferInstance, bot_le, Submodule.zero_mem _, fun k _ x hx => by
      rw [Submodule.mem_bot] at hx; subst hx; rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, h1, l1, m1, s1⟩ := hx
    obtain ⟨U₂, h2, l2, m2, s2⟩ := hy
    refine ⟨U₁ ⊔ U₂, inferInstance, sup_le l1 l2, Submodule.add_mem_sup m1 m2, fun k hk z hz => ?_⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (s1 k hk y₁ hy₁) (s2 k hk y₂ hy₂)
  | smul c x _ hx =>
    obtain ⟨U, h, l, m, s⟩ := hx
    exact ⟨U, h, l, U.smul_mem c m, s⟩
end GlobalTheory.SquareAgree.KFinAlg
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

theorem _root_.GlobalTheory.T.kFinite_algebra_closed_under_derivation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  first | exact @_root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite | exact _root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite | (intros; apply _root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.TripleAssembly.LieInv
variable {D : D7}
end GlobalTheory.TripleAssembly.LieInv
namespace GlobalTheory.TripleAssembly.LieInv
variable {D : D7}
end GlobalTheory.TripleAssembly.LieInv
namespace GlobalTheory.TripleAssembly.LieInv
variable {D : D7}
end GlobalTheory.TripleAssembly.LieInv
namespace GlobalTheory.TripleAssembly.LieInv
variable {D : D7}
theorem thetaLift_lie_derivative_eq_zero (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {k : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D}
    {Yv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Yv Z) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Yv Z) (ω : WRep M X)
    (e : Fin k ≃ Fin X.rank) (c : D.host.E) (hc : Yv.J = c • M.gram)
    (hX : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver (E := D.host.E) w)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin k) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin M.rank × Fin k → Fv D.host.F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (Mo.vac v) = s v)
    (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hM : Mo.IsGood ψ) (hW : Mo.IsWeil ψ χX χW om)
    (hDer : ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Yv,
      GlobalTheory.RealActs.DerOn (Mo.Pol ψ emb) (fun t => om (γ (Multiplicative.ofAdd t), 1)))
    (hlie : ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Yv, ∀ f ∈ Mo.Pol ψ emb,
      ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin k),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
        pr f₁ = 0)
    (T : ((Fin M.rank × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] (WO M X → ℂ))
    (hT : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram e Φ)
    (hinj : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin k), T Φ = 0 → Φ = 0)
    (htr : GlobalTheory.TripleRead.IsTransp ψ ε Mo om ω e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc) (GlobalTheory.TripleRead.toUX X e hX))
    (hθ : IsInfFam θ) (τ : D.what₂.Tau) (Y : Matrix (Fin M.rank) (Fin M.rank) ℂ) (hY : Y ∈ lieAt M τ)
    (Ψ : (Fin M.rank × Fin k → AF D.host.F) → ℂ) (hΨ : Ψ ∈ darbAlg Mo ψ emb) (Φ' : WO M X → ℂ)
    (hD : IsDer θ M (fun g => ω (g, 1)) τ Y (T Ψ) Φ') :
    thetaLift Mo ψ (sgn ε M).gram e (darbAlg Mo ψ emb) (liftPure Mo pr pv s) Φ' = 0 := by
  classical
  obtain ⟨γ, hγ, hγt⟩ := exists_line_conjU θ M τ Y hθ hY Yv c hc
  obtain ⟨Dop, hDpol, hDiff⟩ := hDer γ hγ
  obtain ⟨m, f, φ, hf, rfl⟩ := exists_sum_pure Mo ψ emb hΨ
  let f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin k) := fun i => Dop (f i)
  have hA : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
      (fun t => om (γ (Multiplicative.ofAdd t), 1)) (f i) (f₁ i) := fun i => (hDiff (f i) (hf i).1 (f₁ i)).2 rfl
  have hstdv : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 := by
    intro i
    filter_upwards [hM.std, (hf i).2.2] with v hv hv' using hv'.trans hv
  have hsch : ∀ g : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin k),
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin k) := fun g =>
    Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstdv i)
  have hΨ₁ : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i) ∈ darbAlg Mo ψ emb :=
    Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f₁ i, φ i, hDpol _ (hf i).1, (hf i).2.1, (hf i).2.2, rfl⟩
  have hder := _root_.GlobalTheory.ThetaLineDerFirst.hasDerivAt_thetaSum_along_line hP Mo ψ χX χW om hstd hM hW γ hγ m f f₁ φ (fun i => ⟨(hf i).2.1, (hf i).2.2⟩) hA
  have hΦ' : Φ' = GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) := by
    funext z
    have h1 := hD z
    have h2 := hder (GlobalTheory.TripleRead.ptO (sgn ε M).gram e z)
    refine h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
    have h3 := htr _ (hsch f) (oneP θ M τ Y t) 1
    rw [toUX_one, ← hγt t] at h3
    show ω (oneP θ M τ Y t, 1) (T _) z = GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram e _ z
    rw [hT _ (hsch f), ← h3]
  have hsub := GlobalTheory.TripleAssembly.darbAlg_le_schA _ _ _ Mo ψ emb hM
  have H : ∃ q : (Matrix (Fin X.rank) (Fin M.rank) (AE D) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s,
      ∀ Ψ ∈ darbAlg Mo ψ emb, q (GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram e Ψ) = liftPure Mo pr pv s Ψ := by
    obtain ⟨q, hq⟩ := exists_factor T (darbAlg Mo ψ emb) (fun x hx => hinj x (hsub hx)) (liftPure Mo pr pv s)
    exact ⟨q, fun Ψ hΨ => by rw [← hT Ψ (hsub hΨ)]; exact hq Ψ hΨ⟩
  have e1 : thetaLift Mo ψ (sgn ε M).gram e (darbAlg Mo ψ emb) (liftPure Mo pr pv s) Φ' =
      liftPure Mo pr pv s (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) := by
    rw [hΦ']
    unfold thetaLift
    rw [dite_eq_left H]
    exact H.choose_spec _ hΨ₁
  have HL := GlobalTheory.PureLift.exists_pureLift D.sp.cm.sig Yv Z Mo ψ hM P pr N pv s hs
  have e2 : ∀ i, liftPure Mo pr pv s (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) = 0 := by
    intro i
    unfold liftPure
    rw [dite_eq_left HL, HL.choose_spec _ _ (hf i).2.1 (hf i).2.2, hlie γ hγ (f i) (hf i).1 (f₁ i) (hA i),
      TensorProduct.zero_tmul]

  rw [e1, map_sum]
  exact Finset.sum_eq_zero fun i _ => e2 i
end GlobalTheory.TripleAssembly.LieInv
open GlobalTheory.TripleAssembly.LieInv in
theorem GlobalTheory.TripleAssembly.LieInv.theta_triple_maps_lie_action_eq_zero : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ τ, ∀ Y ∈ lieAt W τ, ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ W (fun g => ωA (g, 1)) τ Y Φ Φ' → GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = 0) ∧
          ∀ τ, ∀ Y ∈ lieAt W₁ τ, ∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ W₁ (fun g => ωB (g, 1)) τ Y Φ Φ' → GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ' = 0 := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm
  obtain ⟨iA, iB⟩ := _root_.GlobalTheory.T.theta_image_eq_span_darboux hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm
  have hg := hm.triple.geo
  have hψ' : Bs.ψ = ψ := h.ψ
  subst hψ'
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hm.triple.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have dV : Γ.V.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV.sig w)
  have dV' : Γ.V'.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV'.sig w)
  have dW : Γ.W.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 Complex.I (hg.hW.sig w)
  have gA : (sgn true W).gram.det ≠ 0 := by
    have e1 : (sgn true W).gram = -W.gram := rfl
    rw [h.JW, one_smul] at dV
    rw [e1, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) dV
  have gB : (sgn false W₁).gram.det ≠ 0 := by
    have e1 : (sgn false W₁).gram = W₁.gram := rfl
    rw [h.JW₁, Matrix.det_smul] at dV'
    rw [e1]
    exact right_ne_zero_of_mul dV'
  have PA := _root_.GlobalTheory.T.dualPair_preserves_polarization hP _ _ D.sp.cm.sig Bs _ _ Γ.V Γ.W Γ.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hm.triple)
  have PB := _root_.GlobalTheory.T.dualPair_preserves_polarization hP _ _ D.sp.cm.sig Bs _ _ Γ.V' Γ.W Γ.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hm.triple)
  constructor
  · intro τ Y hY Φ hΦ Φ' _ hD
    obtain ⟨T, hT, hinj⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Γ.M Bs.ψ (sgn true W).gram e hg.hM hstd dV dW gA
    have hΦ2 : Φ ∈ (darbAlg Γ.M Bs.ψ Bs.emb).map T := by rw [iA T hT]; exact hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := hΦ2
    exact _root_.GlobalTheory.TripleAssembly.LieInv.thetaLift_lie_derivative_eq_zero hP Bs.ψ θ true Γ.M om ωA e 1 h.JW h.JX Bs.emb Xc.β (Xc.β / Xc.α) R.p Rf.p (vacIm Γ Rf)
      (Filter.Eventually.of_forall fun _ => rfl) hstd hg.hM hm.triple.weil PA.1 hm.real.quot.lie T hT hinj tA hθ τ Y hY
      Ψ hΨ Φ' hD
  · intro τ Y hY Φ hΦ Φ' _ hD
    obtain ⟨T, hT, hinj⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Γ.M' Bs.ψ (sgn false W₁).gram e hg.hM' hstd dV' dW gB
    have hΦ2 : Φ ∈ (darbAlg Γ.M' Bs.ψ Bs.emb).map T := by rw [iB T hT]; exact hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := hΦ2
    refine _root_.GlobalTheory.TripleAssembly.LieInv.thetaLift_lie_derivative_eq_zero hP Bs.ψ θ false Γ.M' om' ωB e (-1) h.JW₁ h.JX Bs.emb Xc.α (Xc.α / Xc.β) R.p' Rf.p'
      (vacIm Γ Rf) ?_ hstd hg.hM' hm.triple.weil' PB.1 hm.real.quot'.lie T hT hinj tB hθ τ Y hY Ψ hΨ Φ' hD
    filter_upwards [Xc.T.eventually_cofinite_notMem] with v hv using (hm.fin.sph v hv).1.symm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.theta_triple_lift_lie_invariant : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ τ, ∀ Y ∈ lieAt W τ, ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ W (fun g => ωA (g, 1)) τ Y Φ Φ' → GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = 0) ∧
          ∀ τ, ∀ Y ∈ lieAt W₁ τ, ∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ W₁ (fun g => ωB (g, 1)) τ Y Φ Φ' → GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ' = 0 := by
  first | exact @_root_.GlobalTheory.TripleAssembly.LieInv.theta_triple_maps_lie_action_eq_zero | exact _root_.GlobalTheory.TripleAssembly.LieInv.theta_triple_maps_lie_action_eq_zero | (intros; apply _root_.GlobalTheory.TripleAssembly.LieInv.theta_triple_maps_lie_action_eq_zero <;> assumption)
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
noncomputable section
namespace GlobalTheory.SphFix
theorem spherical_fixes_pure_vacuum_vectors : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), S₀ ⊆ S → ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) →
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F w)) → (∀ w ∉ S, φ w = G.M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∧
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w ∉ S, φ w = G.M'.vac w) →
      om' (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  classical
  intro P F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨S₁, h₁⟩ := _root_.GlobalTheory.T.spherical_vector_fixed_at_almost_all_places P F E σ B a a' G X om om' hT
  obtain ⟨S₂, h₂⟩ := _root_.GlobalTheory.T.restricted_tensor_spherical_uniqueness_off_finite P F E σ B a a' G X om om' hT
  refine ⟨S₁ ∪ S₂, fun S hS k hinf hSk hl hl' => ⟨fun f φ hφ hv => ?_, fun f φ hφ hv => ?_⟩⟩
  · exact GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor F E σ a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om S (Nat.zero_lt_of_lt hT.geo.lt)
      hT.geo.hV.lat hT.geo.hW.lat.toIsLattice hT.geo.hM hT.weil
      (fun v hv k hk => h₁ v (fun h => hv (hS (Finset.mem_union_left _ h))) k hk) k hinf hSk hl f φ hφ hv
  · exact GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor F E σ a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' S
      (lt_of_le_of_lt (Nat.zero_le _) hT.geo.aBig) hT.geo.hV'.lat hT.geo.hW.lat.toIsLattice hT.geo.hM' hT.weil'
      (fun v hv k hk => h₂ v (fun h => hv (hS (Finset.mem_union_right _ h))) k hk) k hinf hSk hl' f φ hφ hv
end GlobalTheory.SphFix
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

theorem _root_.GlobalTheory.T.spherical_vector_fixes_vacua : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), S₀ ⊆ S → ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) →
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F w)) → (∀ w ∉ S, φ w = G.M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∧
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w ∉ S, φ w = G.M'.vac w) →
      om' (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  first | exact @_root_.GlobalTheory.SphFix.spherical_fixes_pure_vacuum_vectors | exact _root_.GlobalTheory.SphFix.spherical_fixes_pure_vacuum_vectors | (intros; apply _root_.GlobalTheory.SphFix.spherical_fixes_pure_vacuum_vectors <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
namespace GlobalTheory.ArchTens
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end GlobalTheory.ArchTens
open GlobalTheory.ArchTens in
theorem _root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) : InfTensK := by
  obtain ⟨F1, h1⟩ := _root_.GlobalTheory.T.local_character_power_conductor_bound hP
  obtain ⟨F2, h2⟩ := _root_.GlobalTheory.T.archimedean_tensor_factor_unfolding hP
  obtain ⟨F3, h3⟩ := _root_.GlobalTheory.T.archimedean_tensor_volume_bound hP
  refine ⟨max F1 (max F2 F3), fun CF hCF => ?_⟩
  obtain ⟨C1, h1⟩ := h1 CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, h2⟩ := h2 CF (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hCF)
  obtain ⟨C3, h3⟩ := h3 CF (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hCF)
  refine ⟨max (max (4 * C1) (2 * C2)) (max (2 * C3) 0), fun ε C hC => ?_⟩
  have hC1 : C1 ≤ C / 2 / 2 := by have := (le_max_left _ _).trans ((le_max_left _ _).trans hC); linarith
  have hC2 : C2 ≤ C / 2 := by have := (le_max_right _ _).trans ((le_max_left _ _).trans hC); linarith
  have hC3 : C3 ≤ C / 2 := by have := (le_max_left _ _).trans ((le_max_right _ _).trans hC); linarith
  have hC0 : 0 ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans hC)
  obtain ⟨x1, h1⟩ := h1 ε (C / 2 / 2) hC1
  obtain ⟨x2, h2⟩ := h2 ε (C / 2) hC2
  obtain ⟨x3, h3⟩ := h3 ε (C / 2) hC3
  refine ⟨max x1 (max x2 x3), ?_⟩
  intro D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF
  exact infTensAt_of_places ch hC0
    (h2 D large₂ he (((le_max_left _ _).trans (le_max_right _ _)).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
      (h1 D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF))
    (h3 D large₂ he (((le_max_right _ _).trans (le_max_right _ _)).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF)
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.sum_size_archimedean_tensor_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → InfTensK := by
  first | exact @_root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local | exact _root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local | (intros; apply _root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local <;> assumption)
end
end
