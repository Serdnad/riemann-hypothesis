module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle103
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle175
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle317
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle323
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle318
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136

@[expose] public section

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

namespace GlobalTheory.RealLieOp

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.RealLift

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem actsD_zero' (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e]
  simp only [map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _


open scoped Classical in
theorem actsD_comb (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ g g₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) (hg : ActsD (evI F) (fun t => ⇑(L t)) ⇑g ⇑g₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(c • f + g) ⇑(c • f₁ + g₁) := by
  have e : ∀ (r : (κ → AF F) → ℂ) (φ ψ : SInf F κ),
      tens (evI F) ⇑(c • φ + ψ) r = c • tens (evI F) ⇑φ r + tens (evI F) ⇑ψ r := by
    intro r φ ψ; funext y; simp [tens]; ring
  have key : ∀ r, Rest (evI F) ⇑f r → Rest (evI F) ⇑g r → ∀ x,
      HasDerivAt (fun t => L t (tens (evI F) ⇑(c • f + g) r) x) (tens (evI F) ⇑(c • f₁ + g₁) r x) 0 := by
    intro r h1 h2 x
    rw [e, e]
    have h := ((hf r h1 x).const_mul c).add (hg r h2 x)
    have hfun : (fun t => L t (c • tens (evI F) ⇑f r + tens (evI F) ⇑g r) x) =
        (fun t => c * L t (tens (evI F) ⇑f r) x) + (fun t => L t (tens (evI F) ⇑g r) x) := by
      funext t; simp [map_add (f := _), map_smul]
    rw [hfun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h

  set g₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl
  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r₀ := fun φ =>
    ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨φ, g₀, hg₀, rfl⟩⟩
  have hzeroT : ∀ r : (κ → AF F) → ℂ, tens (evI F) ⇑(0 : SInf F κ) r = 0 := by
    intro r; funext x; simp [tens]
  intro r hr x
  by_cases h0 : c • f + g = 0
  · have hz : c • f₁ + g₁ = 0 := by
      ext a
      have h := key r₀ (hrest₀ f) (hrest₀ g) (ptAt a 0)
      rw [h0, hzeroT] at h
      simp only [map_zero, Pi.zero_apply] at h
      have h' := h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
      rw [htens₀, pureA_ptAt, hg₀0, mul_one] at h'
      simpa using h'
    rw [h0, hz, hzeroT]
    simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const _ _
  · have hR : (fun y => r (fun i => ((0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F), y i))) ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :=
      mem_SB_of_pureA_mem h0 (tens_eq_pureA _ hr.1 ▸ hr.2)
    have hrest : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r := fun φ =>
      ⟨hr.1, by rw [tens_eq_pureA _ hr.1]; exact Submodule.subset_span ⟨φ, _, hR, rfl⟩⟩
    exact key r (hrest f) (hrest g) x

theorem actsD_add (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) {f f₁ g g₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) (hg : ActsD (evI F) (fun t => ⇑(L t)) ⇑g ⇑g₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(f + g) ⇑(f₁ + g₁) := by
  simpa only [one_smul] using actsD_comb L 1 hf hg

theorem actsD_smul (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(c • f) ⇑(c • f₁) := by
  simpa only [add_zero] using actsD_comb L c hf (actsD_zero' L)

end GlobalTheory.RealLieOp

theorem GlobalTheory.RealLieOp.exists_realOp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∃ T : Module.End ℂ R.Pi,
      (∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p f₁ = T (R.p f)) ∧
      ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f' f₁' → R.p' f₁' = T (R.p' f') := by
  intro F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM γ hγ
  let L : ℝ → Module.End ℂ ((Fin a × Fin (a + a') → AF F) → ℂ) := fun t => om (1, γ (Multiplicative.ofAdd t))
  let L' : ℝ → Module.End ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) := fun t => om' (1, γ (Multiplicative.ofAdd t))
  let S : Set (R.Pi × R.Pi) :=
    {z | ∃ f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')), f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁ ∧ z = (R.p f, R.p f₁)} ∪
    {z | ∃ f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')), f ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑f ⇑f₁ ∧ z = (R.p' f, R.p' f₁)}
  have hspan : ∀ z ∈ Submodule.span ℂ S, ∃ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (f' f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁ ∧ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑f' ⇑f₁' ∧
      z = (R.p f + R.p' f', R.p f₁ + R.p' f₁') := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨f, f₁, hf, h1, rfl⟩ | ⟨f, f₁, hf, h1, rfl⟩
      · exact ⟨f, f₁, 0, 0, hf, h1, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L', by simp⟩
      · exact ⟨0, 0, f, f₁, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L, hf, h1, by simp⟩
    | zero => exact ⟨0, 0, 0, 0, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L', Prod.ext (by simp) (by simp)⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hx
      obtain ⟨g, g₁, g', g₁', hg, h2, hg', h2', rfl⟩ := hy
      refine ⟨f + g, f₁ + g₁, f' + g', f₁' + g₁', add_mem hf hg, GlobalTheory.RealLieOp.actsD_add L h1 h2,
        add_mem hf' hg', GlobalTheory.RealLieOp.actsD_add L' h1' h2', ?_⟩
      simp only [map_add (f := _), Prod.mk_add_mk]
      abel_nf
    | smul c x _ hx =>
      obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hx
      refine ⟨c • f, c • f₁, c • f', c • f₁', Submodule.smul_mem _ c hf, GlobalTheory.RealLieOp.actsD_smul L c h1,
        Submodule.smul_mem _ c hf', GlobalTheory.RealLieOp.actsD_smul L' c h1', ?_⟩
      simp only [map_smul, Prod.smul_mk, smul_add]
  have hgraph : ∀ z ∈ Submodule.span ℂ S, z.1 = 0 → z.2 = 0 := by
    intro z hz hz0
    obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hspan z hz
    have e : R.p f + R.p' f' = 0 := hz0
    have e2 : R.p f = R.p' (-f') := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left e
    have hn : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑(-f') ⇑(-f₁') := by
      simpa only [neg_one_smul] using GlobalTheory.RealLieOp.actsD_smul L' (-1) h1'
    have := hM.real.lie γ hγ f hf (-f') (neg_mem hf') f₁ (-f₁') h1 hn e2
    show R.p f₁ + R.p' f₁' = 0
    rw [this, map_neg, neg_add_cancel]
  obtain ⟨T, hT⟩ := LinearMap.exists_extend (Submodule.span ℂ S).toLinearPMap.toFun
  have hT' : ∀ z ∈ Submodule.span ℂ S, T z.1 = z.2 := by
    intro z hz
    have hz' : z ∈ (Submodule.span ℂ S).toLinearPMap.graph := by
      rw [Submodule.toLinearPMap_graph_eq _ hgraph]; exact hz
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hz'
    rw [← hy1, ← hy2]
    exact LinearMap.congr_fun hT y
  refine ⟨T, fun f hf f₁ h1 => ?_, fun f hf f₁ h1 => ?_⟩
  · exact (hT' (R.p f, R.p f₁) (Submodule.subset_span (Or.inl ⟨f, f₁, hf, h1, rfl⟩))).symm
  · exact (hT' (R.p' f, R.p' f₁) (Submodule.subset_span (Or.inr ⟨f, f₁, hf, h1, rfl⟩))).symm
end
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

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.ThetaInterchange

open Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {Wd : Spc F E d}

def Good (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ))
    (Φ : (Fin n × Fin d → AF F) → ℂ) : Prop :=
  Φ ∈ schA F (Fin n × Fin d) ∧ ∃ Φ' ∈ schA F (Fin n × Fin d), (∀ x, HasDerivAt (fun t => T t Φ x) (Φ' x) 0) ∧
    ∀ w, HasDerivAt (fun t => thetaSum F (M.co.rho ψ w (T t Φ))) (thetaSum F (M.co.rho ψ w Φ')) 0

theorem rho_add (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E))
    (a b : (Fin n × Fin d → AF F) → ℂ) : M.co.rho ψ w (a + b) = M.co.rho ψ w a + M.co.rho ψ w b := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]

theorem rho_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ)
    (a : (Fin n × Fin d → AF F) → ℂ) : M.co.rho ψ w (c • a) = c • M.co.rho ψ w a := by
  funext x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem rho_zero (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    M.co.rho ψ w (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem theta_add (M : Model σ Y Wd) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : Matrix (Fin n) (Fin d) (AE F E))
    {a b : (Fin n × Fin d → AF F) → ℂ} (ha : a ∈ schA F (Fin n × Fin d)) (hb : b ∈ schA F (Fin n × Fin d)) :
    thetaSum F (M.co.rho ψ w (a + b)) = thetaSum F (M.co.rho ψ w a) + thetaSum F (M.co.rho ψ w b) := by
  rw [rho_add]
  unfold GlobalTheory.WeilM.thetaSum
  exact (GlobalTheory.WeilM.summable_of_mem_schA F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ w _ ha)).tsum_add
    (GlobalTheory.WeilM.summable_of_mem_schA F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ w _ hb))

theorem theta_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ)
    (a : (Fin n × Fin d → AF F) → ℂ) : thetaSum F (M.co.rho ψ w (c • a)) = c * thetaSum F (M.co.rho ψ w a) := by
  rw [rho_smul]
  unfold GlobalTheory.WeilM.thetaSum
  simp only [Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem good_zero (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) :
    Good M ψ T 0 := by
  refine ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, fun x => ?_, fun w => ?_⟩
  · simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const _ _
  · simp only [map_zero, rho_zero, GlobalTheory.WeilM.thetaSum, Pi.zero_apply, tsum_zero]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem good_add (M : Model σ Y Wd) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)} (hT : ∀ t, ∀ Φ ∈ schA F (Fin n × Fin d), T t Φ ∈ schA F _)
    {a b : (Fin n × Fin d → AF F) → ℂ} (ha : Good M ψ T a) (hb : Good M ψ T b) : Good M ψ T (a + b) := by
  obtain ⟨ha, a', ha', hpa, hta⟩ := ha
  obtain ⟨hb, b', hb', hpb, htb⟩ := hb
  refine ⟨Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb', fun x => ?_, fun w => ?_⟩
  · simp only [map_add (f := _), Pi.add_apply]
    exact (hpa x).add (hpb x)
  · have e : (fun t => thetaSum F (M.co.rho ψ w (T t (a + b)))) =
        fun t => thetaSum F (M.co.rho ψ w (T t a)) + thetaSum F (M.co.rho ψ w (T t b)) := by
      funext t
      rw [map_add (f := _), theta_add M hψ w (hT t a ha) (hT t b hb)]
    rw [e, theta_add M hψ w ha' hb']
    exact (hta w).add (htb w)

theorem good_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) (c : ℂ)
    {a : (Fin n × Fin d → AF F) → ℂ} (ha : Good M ψ T a) : Good M ψ T (c • a) := by
  obtain ⟨ha, a', ha', hpa, hta⟩ := ha
  refine ⟨Submodule.smul_mem _ c ha, c • a', Submodule.smul_mem _ c ha', fun x => ?_, fun w => ?_⟩
  · simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact (hpa x).const_mul c
  · simp only [map_smul, theta_smul]
    exact (hta w).const_mul c

theorem schA_le_of_pure {κ : Type} [Fintype κ] {N : Submodule ℂ ((κ → AF F) → ℂ)}
    (h : ∀ (f : SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) → pure f φ ∈ N) :
    schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  replace hg := GlobalTheory.SBSpan.mem_span_restrictedProd F _ g hg
  induction hg using Submodule.span_induction with
  | zero => rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; exact N.zero_mem
  | add a b _ _ ha hb =>
    rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; exact N.add_mem ha hb
  | smul c a _ ha =>
    rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; exact N.smul_mem c ha
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    exact h f φ hφ hs

end GlobalTheory.ThetaInterchange

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

namespace GlobalTheory.PureLift

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_sep (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ)
    (hstd : ∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (lam : SInf F κ →ₗ[ℂ] ℂ) (l : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (hl : {v | l v (vac v) ≠ 1}.Finite) :
    ∃ Λ : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, ∀ (f : SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
      (∀ᶠ v in Filter.cofinite, φ v = vac v) → Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = lam f * ∏ᶠ v, l v (φ v) := by
  first
  | exact @_root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure
  | exact _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure
  | (apply _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure ..)

theorem exists_pureLift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ),
    M.IsGood ψ → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    (N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type) [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v),
    (∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) →
    ∃ q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s,
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
  intro F E _ _ _ _ _ σ n d Y Z M ψ hM P _ _ pr N _ _ pv s hs
  classical
  let b := Module.Free.chooseBasis ℂ P
  have hsep : ∀ (i : Module.Free.ChooseBasisIndex ℂ P) (l : GlobalTheory.SmallThetaModules.AdmFun s),
      ∃ Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ), (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = (b.coord i) (pr f) * ∏ᶠ v, l.1 v (pv v (φ v)) := by
    intro i l
    refine exists_sep M.vac hM.std ((b.coord i).comp pr) (fun v => (l.1 v).comp (pv v)) ?_
    refine ((Filter.eventually_cofinite.1 hs).union l.2).subset fun v hv => ?_
    by_cases e : pv v (M.vac v) = s v
    · right
      simp only [Set.mem_setOf_eq, LinearMap.comp_apply, e] at hv ⊢
      exact hv
    · left
      exact e
  choose Λ hΛ using hsep
  let ι' : P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s →ₗ[ℂ]
      (Module.Free.ChooseBasisIndex ℂ P → GlobalTheory.SmallThetaModules.AdmFun s → ℂ) :=
    (LinearMap.compLeft (GlobalTheory.SmallThetaModules.RTens s).subtype _) ∘ₗ Finsupp.lcoeFun ∘ₗ
      (TensorProduct.equivFinsuppOfBasisLeft b).toLinearMap
  have hinj : Function.Injective ι' := by
    intro t t' h
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i : 1
    apply Subtype.ext
    exact congrFun h i
  obtain ⟨r, hr⟩ := ι'.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨r ∘ₗ LinearMap.pi (fun i => LinearMap.pi (fun l => Λ i l)), fun f φ _ hφ => ?_⟩
  have hR : Formalism.MainNotions.KudlaSiegelWeil.Restr s (fun v => pv v (φ v)) := by
    refine ((Filter.eventually_cofinite.1 hφ).union (Filter.eventually_cofinite.1 hs)).subset fun v hv => ?_
    by_cases e : φ v = M.vac v
    · right
      simp only [Set.mem_setOf_eq, e] at hv ⊢
      exact hv
    · left
      exact e
  have h1 : LinearMap.pi (fun i => LinearMap.pi (fun l => Λ i l)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      ι' (pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v))) := by
    funext i l
    rw [LinearMap.pi_apply, LinearMap.pi_apply, hΛ i l f φ hφ]
    simp only [ι', LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lcoeFun_apply, LinearMap.compLeft_apply,
      Function.comp_apply, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Submodule.subtype_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, GlobalTheory.SmallThetaModules.coe_pureT hR,
      GlobalTheory.SmallThetaModules.evFam, Module.Basis.coord_apply]
  rw [LinearMap.comp_apply, h1, ← LinearMap.comp_apply, hr, LinearMap.id_apply]

end GlobalTheory.PureLift
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.continuous_nrm2_om_sub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsCovolOne (ratL T S) μ 𝓕 → ∀ f₁ f₂ : WO S T → ℂ, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ → Continuous fun p : GA D S × GA D T => nrm2 μ 𝓕 (om p f₁ - f₂) := by
  first | exact @GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub | exact GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub | (intros; apply GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) g) (ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) g) 0 ∧ ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) g = -ipO μ 𝓕 f (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g) := by
  first | exact @GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew | exact GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew | (intros; apply GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockPolynomialVector_maximalCompact_moved_bases : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), BS' τ = BS τ * κS → BT' τ = BT τ * κT → (∀ ρ, ρ ≠ τ → BS' ρ = BS ρ ∧ BT' ρ = BT ρ) → ∀ P, pureTensorO ψ θ S T sS sT BS' BT' f P = pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  first | exact @GlobalTheory.FockSubBoth.pureTensorO_fockSub | exact GlobalTheory.FockSubBoth.pureTensorO_fockSub | (intros; apply GlobalTheory.FockSubBoth.pureTensorO_fockSub <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.splitPlaceBoundedMatrix_from_halfHomLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, a ∈ D.host.AA → a ≠ 0 → ∀ y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v), (∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ a)) → ∃ u, u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e u ∧ mapCo φ S T (frCo φ βS) (frCo φ βT) u = y := by
  first | exact @GlobalTheory.SplitHomOnto.honto | exact GlobalTheory.SplitHomOnto.honto | (intros; apply GlobalTheory.SplitHomOnto.honto <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockVectors_inner_eq_fockInnerProduct_mul_norm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ P Q, ipO μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f P) (pureTensorO ψ θ S T sS sT BS BT f Q) = fockIp P Q * (nrm2 μ 𝓕 f : ℂ) := by
  first | exact @GlobalTheory.FockIsometry.ipO_pureTensorO | exact GlobalTheory.FockIsometry.ipO_pureTensorO | (intros; apply GlobalTheory.FockIsometry.ipO_pureTensorO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeOperator_faceLevel_eq_principalLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (b : Bool) (i : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (B : Finset (GA D (Wc D i))), Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) SF P d B → Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B := by
  first | exact @GlobalTheory.LevOpFace.heckeOp_face_to_principal | exact GlobalTheory.LevOpFace.heckeOp_face_to_principal | (intros; apply GlobalTheory.LevOpFace.heckeOp_face_to_principal <;> assumption)
end
