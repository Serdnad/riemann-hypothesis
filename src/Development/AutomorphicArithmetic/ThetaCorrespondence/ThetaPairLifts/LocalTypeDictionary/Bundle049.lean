module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle334
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle364
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle401
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle402
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle430

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
namespace GlobalTheory.LineSum
theorem lineSum_exists_derivative_factor (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (hθ : IsInfFam θ) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om') (τ : D.what₂.Tau)
    (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (hY : Y ∈ lieAt X τ) :
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∃ Ψ ∈ algD Γ.M Bs.ψ Bs.emb,
      ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) ΦD x) (Ψ x) 0 := by
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hJ
  obtain ⟨Dop, hDP, hD⟩ := (_root_.GlobalTheory.T.dualPair_preserves_polarization hP _ _ D.sp.cm.sig Bs _ _ Γ.V Γ.W Γ.M Xc.β (Xc.β / Xc.α) om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hT)).2.2.1 γ hγ
  have hfun : ∀ Φ : (Fin a × Fin (a + a') → AF D.host.F) → ℂ, ∀ x,
      (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) Φ x) = fun t => om (1, γ (Multiplicative.ofAdd t)) Φ x := by
    intro Φ x; funext t; rw [hγt t]
  intro ΦD hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add p q _ _ hp hq =>
    obtain ⟨p', hp', hdp⟩ := hp
    obtain ⟨q', hq', hdq⟩ := hq
    refine ⟨p' + q', add_mem hp' hq', fun x => ?_⟩
    have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) (p + q) x) =
        fun t => om (1, kapX X e hJ (oneP θ X τ Y t)) p x + om (1, kapX X e hJ (oneP θ X τ Y t)) q x := by
      funext t; simp
    rw [e1]
    exact (hdp x).add (hdq x)
  | smul c p _ hp =>
    obtain ⟨p', hp', hdp⟩ := hp
    refine ⟨c • p', Submodule.smul_mem _ c hp', fun x => ?_⟩
    have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X τ Y t)) (c • p) x) =
        fun t => c * om (1, kapX X e hJ (oneP θ X τ Y t)) p x := by
      funext t; simp
    rw [e1]
    simpa using (hdp x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
      (hev.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dop f) φ, Submodule.subset_span ⟨Dop f, φ, hDP f hf, hSB, hev, rfl⟩, fun x => ?_⟩
    rw [hfun]
    exact ((hD f hf (Dop f)).2 rfl) _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x
theorem lineSum_product_rule (hpure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin a × Fin (a + a') → v.adicCompletion D.host.F) → ℂ,
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
    ∀ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (∑ i, Ψ i x) 0) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (∑ i, Ψ i x) 0 := by
  intro hP D θ X a a' e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD
  have hex : ∀ (Φ : (Fin a × Fin (a + a') → AF D.host.F) → ℂ), Φ ∈ algD Γ.M Bs.ψ Bs.emb → ∀ i : Fin l.length,
      ∃ Ψ ∈ algD Γ.M Bs.ψ Bs.emb, ∀ x,
      HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) Φ x) (Ψ x) 0 :=
    fun Φ hΦ i => _root_.GlobalTheory.LineSum.lineSum_exists_derivative_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) Φ hΦ
  induction hΦD using Submodule.span_induction with
  | zero =>
    intro Ψ hΨ x
    have h0 : ∀ i, Ψ i x = 0 := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    simp only [h0, Finset.sum_const_zero]
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add p q hp hq ihp ihq =>
    intro Ψ hΨ x
    choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)
    choose Ψq hΨq hdq using hex q (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hq)
    have hsplit : ∀ i, Ψ i x = Ψp i x + Ψq i x := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (p + q) x) =
          fun t => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x +
            om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) q x := by
        funext t; simp
      rw [e1]
      exact (hdp i x).add (hdq i x)
    have e2 : (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (p + q) x) =
        fun t => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x +
          om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) q x := by
      funext t; simp
    rw [e2, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
    exact (ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).add (ihq Ψq (fun i => ⟨hΨq i, hdq i⟩) x)
  | smul c p hp ihp =>
    intro Ψ hΨ x
    choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)
    have hsplit : ∀ i, Ψ i x = c * Ψp i x := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      have e1 : (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (c • p) x) =
          fun t => c * om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x := by
        funext t; simp
      rw [e1]
      exact (hdp i x).const_mul c
    have e2 : (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (c • p) x) =
        fun t => c * om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x := by
      funext t; simp
    rw [e2, Finset.sum_congr rfl (fun i _ => hsplit i), ← Finset.mul_sum]
    exact (ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    exact hpure hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl f hf φ hSB hev
theorem lineSum_derivative_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D : (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
      Φ₁D = ∑ i, Ψ i := by
  intro hP D θ X a a' e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD Φ₁D hΦ₁
  have hex : ∀ i : Fin l.length, ∃ Ψ ∈ algD Γ.M Bs.ψ Bs.emb, ∀ x,
      HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ x) 0 :=
    fun i => _root_.GlobalTheory.LineSum.lineSum_exists_derivative_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) ΦD hΦD
  choose Ψ hΨ hder using hex
  refine ⟨Ψ, fun i => ⟨hΨ i, hder i⟩, ?_⟩
  funext x
  rw [Finset.sum_apply]
  exact (hΦ₁ x).unique (_root_.GlobalTheory.LineSum.lineSum_product_rule _root_.GlobalTheory.T.derivative_pure_tensor_product hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD Ψ (fun i => ⟨hΨ i, hder i⟩) x)
end GlobalTheory.LineSum
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

theorem _root_.GlobalTheory.T.derivative_of_line_sum_theta : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D : (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
      Φ₁D = ∑ i, Ψ i := by
  first | exact @_root_.GlobalTheory.LineSum.lineSum_derivative_sum | exact _root_.GlobalTheory.LineSum.lineSum_derivative_sum | (intros; apply _root_.GlobalTheory.LineSum.lineSum_derivative_sum <;> assumption)
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
namespace GlobalTheory.SquareAgree.CompactStableD
theorem algebraic_vectors_kInfty_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.V Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (k, 1) ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ _ hT _ _ _ _ _ _ k hk ΦD hΦ
  obtain ⟨Dop, hDP, hD⟩ := (_root_.GlobalTheory.T.dualPair_preserves_polarization hP _ _ D.sp.cm.sig Bs _ _ Γ.V Γ.W Γ.M Xc.β (Xc.β / Xc.α) om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hT)).2.1 k hk
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hcof, rfl⟩ := hx
    have hstd : ∀ᶠ v in Filter.cofinite,
        φ v = Set.indicator {x : Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v |
          ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 := by
      filter_upwards [hcof, hT.geo.hM.std] with v h1 h2
      rw [h1, h2]
    have key : om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dop f) φ :=
      (hD _ hf _).2 rfl _ (GlobalTheory.ThK.EvUniqInf.rest_pure _ _ hSB hstd)
    rw [key]
    exact Submodule.subset_span ⟨Dop f, φ, hDP _ hf, hSB, hcof, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
end GlobalTheory.SquareAgree.CompactStableD
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

theorem _root_.GlobalTheory.T.weil_algebraic_subspace_kInfty_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.V Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (k, 1) ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
  first | exact @_root_.GlobalTheory.SquareAgree.CompactStableD.algebraic_vectors_kInfty_stable | exact _root_.GlobalTheory.SquareAgree.CompactStableD.algebraic_vectors_kInfty_stable | (intros; apply _root_.GlobalTheory.SquareAgree.CompactStableD.algebraic_vectors_kInfty_stable <;> assumption)
end
end

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
noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaInterchange
open Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {Wd : Spc F E d}
theorem thetaInterchange_isPure (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ Y Wd)
    (hcm : IsCMExt F E σ) (hψ : IsStd ψ)
    (hG : M.IsGood ψ) (hW : M.IsWeil ψ χX χW om) (γ : Multiplicative ℝ →* UA σ Wd.J) (hγ : γ ∈ Lines σ Wd)
    (f : SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _)
    (hs : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Good M ψ (fun t => om (1, γ (Multiplicative.ofAdd t))) (pure f φ) := by
  have hv : ∀ᶠ v in cofinite, φ v = M.vac v := (hs.and hG.std).mono fun v h => h.1.trans h.2.symm
  obtain ⟨c, g, hc, hlim⟩ := _root_.GlobalTheory.T.twisted_smoothLine_pure_weight hPr M ψ χX χW om hcm hψ hG hW γ hγ f φ hφ hv
  refine ⟨GlobalTheory.TensUniq.pure_mem_schA f φ hφ hs, pure g φ, GlobalTheory.TensUniq.pure_mem_schA g φ hφ hs, fun x => ?_, fun w => ?_⟩
  · have ev : Continuous fun s : SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) := by
      have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
      exact (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
        (fun j => evI F (x j))).comp h1
    simp only [hc]
    rw [hasDerivAt_iff_tendsto_slope]
    refine (((ev.tendsto g).comp hlim).mul_const (∏ᶠ v, φ v fun j => evFin F v (x j))).congr'
      (Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    simp only [Function.comp_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
    ring
  · obtain ⟨Λ, hΛ⟩ := GlobalTheory.ThetaHeisCLM.exists_clm_thetaSum_rho_pure M ψ hψ hG w φ hφ hv
    simp only [hc, hΛ]
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((Λ.continuous.tendsto g).comp hlim).congr' (Eventually.of_forall fun t => ?_)
    simp [slope_def_module, map_sub, map_smul]
end GlobalTheory.ThetaInterchange
open GlobalTheory.ThetaInterchange in
theorem GlobalTheory.ThetaInterchange.hasDerivAt_theta_integral_interchange : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) {n k : ℕ} (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → Mo.IsGood ψ' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws,
    ∀ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin n × Fin k)) (r : (Fin n × Fin k → AF D.host.F) → ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
      ∀ {d : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (e : Fin k ≃ Fin d) (x : Matrix (Fin d) (Fin n) (AE D)),
        HasDerivAt (fun t : ℝ => GlobalTheory.TripleRead.thO Mo ψ' G e
            (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f r)) x)
          (GlobalTheory.TripleRead.thO Mo ψ' G e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) x) 0 := by
  intro hPr D n k Xs Ws Mo ψ' χX χW om τ hP hG γ hγ f f₁ r hr hr₁ hD d G e x
  obtain ⟨hcm, hψ, -, -, -, -, -, -, -, -, hW, -, -⟩ := hP
  have hT : ∀ t : ℝ, ∀ Φ ∈ schA D.host.F (Fin n × Fin k), om (1, γ (Multiplicative.ofAdd t)) Φ ∈ schA D.host.F _ :=
    fun t Φ hΦ => (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW).pres _ Φ hΦ
  let N : Submodule ℂ ((Fin n × Fin k → AF D.host.F) → ℂ) :=
    { carrier := {Φ | Good Mo ψ' (fun t => om (1, γ (Multiplicative.ofAdd t))) Φ}
      zero_mem' := good_zero Mo ψ' _
      add_mem' := fun ha hb => good_add Mo hψ hT ha hb
      smul_mem' := fun c _ ha => good_smul Mo ψ' _ c ha }
  have hle : schA D.host.F (Fin n × Fin k) ≤ N :=
    schA_le_of_pure fun f φ hφ hs => _root_.GlobalTheory.ThetaInterchange.thetaInterchange_isPure hPr Mo ψ' χX χW om hcm hψ hG hW γ hγ f φ hφ hs
  obtain ⟨-, Φ', -, hpt, hth⟩ := hle hr.2
  have hΦ' : Φ' = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r :=
    funext fun y => (hpt y).unique (hD r hr y)
  have := hth (GlobalTheory.TripleRead.ptO G e x)
  rw [hΦ'] at this
  exact this
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

theorem _root_.GlobalTheory.T.theta_interchange_derivative_pure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) {n k : ℕ} (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → Mo.IsGood ψ' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws,
    ∀ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin n × Fin k)) (r : (Fin n × Fin k → AF D.host.F) → ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
      ∀ {d : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (e : Fin k ≃ Fin d) (x : Matrix (Fin d) (Fin n) (AE D)),
        HasDerivAt (fun t : ℝ => GlobalTheory.TripleRead.thO Mo ψ' G e
            (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f r)) x)
          (GlobalTheory.TripleRead.thO Mo ψ' G e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) x) 0 := by
  first | exact @_root_.GlobalTheory.ThetaInterchange.hasDerivAt_theta_integral_interchange | exact _root_.GlobalTheory.ThetaInterchange.hasDerivAt_theta_integral_interchange | (intros; apply _root_.GlobalTheory.ThetaInterchange.hasDerivAt_theta_integral_interchange <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowLift
theorem twisted_lift_from_base_field : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b → ∀ (a : Fin ch.n) (u : R.HE.H),
    ThetaConv ch.W ch.M ch.ρ (ch.Phi a) (ch.form u) ∧
      IsAutFun (ch.G.V (.grid D.R.m 0)) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.form u)) := by
  intro hP hL D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hb CF hs a u
  obtain ⟨G', hG', hM⟩ := _root_.GlobalTheory.T.twist_row_lift_exists hP large₂ hS ch hb CF hs
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.CuspAlong G' :=
    hL D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hS.size) Γ Pl0 T A Ks R G' (rowBase_of_core hS.core) hG'
  let C : ∀ i, Set (Fn ch.G (.grid i 0)) := fun i =>
    {φ | ∃ Φ' ∈ (G'.V i 0).Cusp R.θ, ∃ v, HEq (Φ' v) φ}
  have step : ∀ (i : Fin D.R.m) φ, φ ∈ C i → LiftConv ch.W ch.M (.right (i : ℕ) 0) (ch.W.datum ch.ρ (ch.Phi a) i) φ ∧
      liftA ch.W ch.M (.right (i : ℕ) 0) (ch.W.datum ch.ρ (ch.Phi a) i) φ ∈ C ((i : ℕ) + 1) := by
    rintro i φ ⟨Φ', hΦ', v, hv⟩
    obtain ⟨f, hf, p, hK⟩ := hM.ker ch.ρ (ch.Phi a) i
    obtain ⟨F', hF', H⟩ := hC.X A.μ0 i 0 i.2 (Nat.zero_le _) f hf Φ' hΦ'
    rw [G'.meas_zero] at H
    have T := transport_stepS (hM.V i i.2.le) (hM.V (i + 1) i.2) (hM.ν i i.2.le) (hM.fd i i.2.le) hK hv
      (fun h => (H p v h).1) (fun h => (H p v h).2)
    exact ⟨T.1, F', hF', _, T.2⟩
  have h0 : ch.form u ∈ C 0 := ⟨_, start_mem hS.core u, ch.w, HEq.rfl⟩
  obtain ⟨h1, Φ', hΦ', v, hv⟩ := row_induction ch.W ch.M C D.R.m _ step _ h0
  exact ⟨h1, isAutFun_transportS (hM.V _ le_rfl) hv (isAutFun_of_mem_cusp _ R.θ hΦ' v)⟩
end GlobalTheory.RowLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twisted_base_change_lift_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b → ∀ (a : Fin ch.n) (u : R.HE.H),
    ThetaConv ch.W ch.M ch.ρ (ch.Phi a) (ch.form u) ∧
      IsAutFun (ch.G.V (.grid D.R.m 0)) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.form u)) := by
  first | exact @_root_.GlobalTheory.RowLift.twisted_lift_from_base_field | exact _root_.GlobalTheory.RowLift.twisted_lift_from_base_field | (intros; apply _root_.GlobalTheory.RowLift.twisted_lift_from_base_field <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotTransfer
theorem bottom_constant_transfer_along_tower : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
      NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D)
      (Y : Tri T B B' WW₁) (c : T → ℂ), IsBottomTri W i j X → IsBottomTri W i j Y → Y.IsConst W.ψ W.θ c →
      ∃ u : T → D.what₂.LLˣ, X.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  intro _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W S hψ hN i j A A' WW X B B' WW₁ Y c hX hY hc
  obtain ⟨X₁, hX₁, hX₁c⟩ := GlobalTheory.T.definiteBottomTriple_transport_same_ranks_constants W i j A A' WW X B B' WW₁ Y hX hY
  obtain ⟨Y₁, hY₁, e1, e2, e3, hY₁c⟩ := GlobalTheory.T.exists_definiteBottomTriple_transferred_frames W S hψ μ₀ hL hN i j B B' WW₁ X₁ Y hX₁ hY
  obtain ⟨u, hu⟩ := hY₁c c hc
  exact ⟨u, hX₁c _ (GlobalTheory.T.definiteBottomTriple_constants_eq_of_same_lattices W i j B B' WW₁ X₁ Y₁ hX₁ hY₁ e1.symm e2.symm e3.symm _ hu)⟩
end GlobalTheory.BotTransfer
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.witt_tower_bottom_constant_transfer : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
      NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D)
      (Y : Tri T B B' WW₁) (c : T → ℂ), IsBottomTri W i j X → IsBottomTri W i j Y → Y.IsConst W.ψ W.θ c →
      ∃ u : T → D.what₂.LLˣ, X.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  first | exact @_root_.GlobalTheory.BotTransfer.bottom_constant_transfer_along_tower | exact _root_.GlobalTheory.BotTransfer.bottom_constant_transfer_along_tower | (intros; apply _root_.GlobalTheory.BotTransfer.bottom_constant_transfer_along_tower <;> assumption)
end
end
