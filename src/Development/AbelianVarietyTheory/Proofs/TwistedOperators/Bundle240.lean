module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle230
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceCoverProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle234
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle233
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
import Mathlib.Tactic.Lemma
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
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DatumFock

open GlobalTheory.SplitScalar

theorem exists_derivForm : ∃ l : (ℝ → ℂ) →ₗ[ℂ] ℂ, ∀ g, DifferentiableAt ℝ g 0 → l g = deriv g 0 := by
  let p : Submodule ℂ (ℝ → ℂ) :=
    { carrier := {g | DifferentiableAt ℝ g 0}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := differentiableAt_const _
      smul_mem' := fun c _ hg => hg.const_smul c }
  let d : p →ₗ[ℂ] ℂ :=
    { toFun := fun g => deriv g.1 0
      map_add' := fun g h => deriv_add g.2 h.2
      map_smul' := fun c g => deriv_const_smul c g.2 }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend d
  exact ⟨l, fun g hg => LinearMap.congr_fun hl ⟨g, hg⟩⟩

variable {D : D7}

def alongLine (l : (ℝ → ℂ) →ₗ[ℂ] ℂ) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (L : ℝ → WO S T) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun g := fun x => l fun t => heisO ψ S T (L t) g x
  map_add' g g' := by
    funext x
    rw [Pi.add_apply, ← map_add (f := _)]
    congr 1
    funext t
    exact congrFun ((heisL ψ S T (L t)).map_add g g') x
  map_smul' c g := by
    funext x
    rw [RingHom.id_apply, Pi.smul_apply, ← map_smul]
    congr 1
    funext t
    exact congrFun ((heisL ψ S T (L t)).map_smul c g) x

theorem alongLine_heisO (l : (ℝ → ℂ) →ₗ[ℂ] ℂ) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {L : ℝ → WO S T}
    (hL : ∀ t, (L t).map (finPart D) = 0) {u : WO S T} (hu : u.map (infPart D) = 0) (g : WO S T → ℂ) :
    alongLine l ψ S T L (heisO ψ S T u g) = heisO ψ S T u (alongLine l ψ S T L g) := by
  funext x
  have hc : ∀ t, heisO ψ S T (L t) (heisO ψ S T u g) = heisO ψ S T u (heisO ψ S T (L t) g) := by
    intro t
    rw [GlobalTheory.SplitScalar.heisO_comm, GlobalTheory.SplitScalar.symplO_real_fin S T (hL t) hu, AddChar.map_zero_eq_one,
      one_smul]
  have key : ∀ h : WO S T → ℂ, heisO ψ S T u h x = ψ (symplOH S T x u) * h (x + u) := fun _ => rfl
  simp only [alongLine, LinearMap.coe_mk, AddHom.coe_mk, hc, key]
  exact l.map_smul (ψ (symplOH S T x u)) (fun t => heisO ψ S T (L t) g (x + u))

private lemma differentiable_of_continuous_additive_char {φ : ℝ → ℂ} (hφ : Continuous φ) (h0 : φ 0 = 1)
    (hmul : ∀ s t, φ (s + t) = φ s * φ t) : Differentiable ℝ φ := by
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, φ x with hFdef
  have hF : ∀ b, HasDerivAt F (φ b) b := fun b => (hφ.integral_hasStrictDerivAt 0 b).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by
    by_contra hcon
    have hz : F = fun _ => (0:ℂ) := funext fun δ => by
      by_contra h
      exact hcon ⟨δ, h⟩
    have h1 := hF 0
    rw [hz, h0] at h1
    exact one_ne_zero (h1.unique (hasDerivAt_const (0:ℝ) (0:ℂ)))
  have key : ∀ t, φ t = (F (δ + t) - F t) * (F δ)⁻¹ := by
    intro t
    have h1 : ∫ x in (0:ℝ)..δ, φ (x + t) = F (δ + t) - F t := by
      rw [intervalIntegral.integral_comp_add_right, zero_add, hFdef]
      exact (intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _)
        (hφ.intervalIntegrable _ _)).symm
    have h2 : ∫ x in (0:ℝ)..δ, φ (x + t) = F δ * φ t := by
      simp_rw [hmul]
      exact intervalIntegral.integral_mul_const _ _
    rw [← h1, h2, mul_comm (F δ) (φ t), mul_assoc, mul_inv_cancel₀ hδ, mul_one]
  intro t
  have hd : DifferentiableAt ℝ (fun t => (F (δ + t) - F t) * (F δ)⁻¹) t :=
    ((((hF (δ + t)).differentiableAt).comp t (differentiableAt_id.const_add δ)).sub
      (hF t).differentiableAt).mul_const _
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall key)

theorem exists_annihLin {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    ∃ A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
      (∀ u : WO S T, u.map (infPart D) = 0 → ∀ g, A (heisO ψ S T u g) = heisO ψ S T u (A g)) ∧
      ∀ g, IsThetaFunO ψ S T g → A g = annih (heisO ψ S T) θ τ J z g := by
  obtain ⟨l, hl⟩ := exists_derivForm
  have hex := GlobalTheory.RealLineAt.lineAt_exists D
  unfold LineAtExists at hex
  have hspec : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, IsLineAt θ τ w (lineAt θ τ w) := by
    intro w
    obtain ⟨L, hL⟩ := hex θ hθ T.rank S.rank τ w
    exact Classical.epsilon_spec ⟨L, hL⟩
  have hfin : ∀ (w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), (lineAt θ τ w t).map (finPart D) = 0 := by
    intro w t
    have h := hspec w
    unfold IsLineAt at h
    exact h.2.1 t
  have hcont : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, Continuous (lineAt θ τ w) := by
    intro w
    have h := hspec w
    unfold IsLineAt at h
    exact h.1
  have hdiff : ∀ g, IsThetaFunO ψ S T g → ∀ (w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (x : WO S T),
      DifferentiableAt ℝ (fun t => heisO ψ S T (lineAt θ τ w t) g x) 0 := by
    intro g hg w x
    obtain ⟨-, -, -, hsm⟩ := hg
    have hgL : DifferentiableAt ℝ (fun t => g (x + lineAt θ τ w t)) 0 := by
      let L1 : (Fin 1 → ℝ) →+ WO S T := (lineAt θ τ w).comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)
      have h1 := hsm 1 L1 ((hcont w).comp (continuous_apply 0)) (fun t => hfin w (t 0)) x
      have h2 : (fun t : ℝ => g (x + lineAt θ τ w t)) =
          (fun t : Fin 1 → ℝ => g (x + L1 t)) ∘ (fun t : ℝ => fun _ : Fin 1 => t) := rfl
      rw [h2]
      exact ((h1.differentiable (by simp)) _).comp _ (differentiableAt_pi.2 fun _ => differentiableAt_id)
    have hφ : Differentiable ℝ (fun t => ψ (symplOH S T x (lineAt θ τ w t))) := by
      apply differentiable_of_continuous_additive_char
      · have hc : (fun t => symplOH S T x (lineAt θ τ w t)) =
            fun t => algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x (lineAt θ τ w t) := rfl
        exact hψ.comp (hc ▸ continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO S T continuous_const (hcont w)))
      · rw [map_zero]
        show ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x 0) = 1
        rw [GlobalTheory.SplitScalar.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
      · intro s t
        rw [map_add (f := _), GlobalTheory.SplitScalar.symplOH_add_right, AddChar.map_add_eq_mul]
    exact (hφ 0).mul hgL
  refine ⟨alongLine l ψ S T (lineAt θ τ z) + Complex.I • alongLine l ψ S T (lineAt θ τ (J z)), ?_, ?_⟩
  · intro u hu g
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    rw [alongLine_heisO l ψ S T (hfin z) hu, alongLine_heisO l ψ S T (hfin (J z)) hu]
    funext x
    unfold heisO
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro g hg
    funext x
    unfold annih Datum.dRho
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, alongLine,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [hl _ (hdiff g hg z x), hl _ (hdiff g hg (J z) x)]

theorem infPart_of_isHalf {S T : HSp D} {e : AE D} (he : infPart D e = 0) {u : WO S T} (hu : IsHalf e u) :
    u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply, ← hu i j, map_mul, he, zero_mul]

theorem isFockVacAt_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    {S T : HSp D} {e : AE D} (he : infPart D e = 0) (he' : infPart D (cA D e) = 0) {Λ : AddSubgroup (WO S T)} {c : ℂ}
    {f₀ Φ f : WO S T → ℂ} (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h₀ : IsThetaFunO ψ S T f₀) (hf : IsThetaFunO ψ S T f) {τ : D.what₂.Tau}
    {J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ}
    (hv : IsFockVacAt (heisO ψ S T) θ τ J f₀) : IsFockVacAt (heisO ψ S T) θ τ J f := by
  unfold IsThetaAt AllSome at h
  obtain ⟨⟨Tm, hTm⟩, hU⟩ := h
  unfold IsFockVacAt at hv ⊢
  intro z
  obtain ⟨A, hA, hAθ⟩ := exists_annihLin hψ hθ S T τ J z
  have hadd : ∀ (w : WO S T) (g g' : WO S T → ℂ),
      heisO ψ S T w (g + g') = heisO ψ S T w g + heisO ψ S T w g' :=
    fun _ _ _ => funext fun _ => mul_add _ _ _
  have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) := by
    obtain ⟨htr, hmod, hvac⟩ := hTm
    refine ⟨fun Φ' hΦ x hx => ?_, fun Φ' hΦ y hy => ?_, ?_⟩
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [htr Φ' hΦ x hx, hA x (infPart_of_isHalf he hx), hadd]
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [hmod Φ' hΦ y hy, hA y (infPart_of_isHalf he' hy), hadd]
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [hvac, hAθ f₀ h₀, hv z, add_zero]
  have e1 : f = Tm Φ := hU Tm hTm
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hU _ hTm'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  rw [← hAθ f hf]
  simpa using e2

theorem isFockVacAt_thPVec : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ (f₀ f : WO S T → ℂ), IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f → IsThetaFunO ψ S T f → ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f h hf τ
  obtain ⟨hv, e, he, ht⟩ := h
  unfold IsVacO IsStdChar at hv
  obtain ⟨hs, ⟨hθ, h₀, -, hfock, -⟩⟩ := hv
  have hψ : Continuous ψ := by
    have h1 := hs.1
    unfold IsCharAF at h1
    exact h1.1
  have ho : GlobalTheory.PlaceModelSum.IsOrthSum e := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  exact isFockVacAt_of_isThetaAt hψ hθ ho.conj.infPart_eq ho.conj.conj.infPart_eq ht h₀ hf (hfock τ)

end GlobalTheory.DatumFock

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugate_maximalCompact_mem_parahoricLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, kap X h t k ∈ GfC (Yc D 0) ∧ finE (Yc D 0) (kap X h t k) ∈ Formalism.L2.DIV.parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) := by
  first | exact @GlobalTheory.KapLevel.kap_mem_parLev | exact GlobalTheory.KapLevel.kap_mem_parLev | (intros; apply GlobalTheory.KapLevel.kap_mem_parLev <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KapRed

open Formalism.L2.SG.RowsJoinPinned (castGA)

variable {D : D7}

theorem iotaX_symm_eq {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (x : I.GA) :
    ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm x = (Formalism.IndefR.RationalEmbedding.iota D).symm (castGA h x) := by
  subst h
  rfl

theorem castGA_mem {I I' : Formalism.MainNotions.S.AutInst} (h : I = I') (k : I.Gf) (g : ℕ) :
    (k ∈ I.Kset ↔ (castGA h (1, k)).2 ∈ I'.Kset) ∧ (k ∈ I.Kg g ↔ (castGA h (1, k)).2 ∈ I'.Kg g) := by
  subst h
  exact ⟨Iff.rfl, Iff.rfl⟩

private theorem swapAE_map_sndA_eq_tauF (D : D7)
    (z : TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.host.E) :
    Formalism.IndefR.Lev.swapAE D
              (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) =
      Formalism.L2.SG.AdBridge.tauF (Formalism.IndefR.RationalEmbedding.inst D) z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact (map_zero _).symm
  | tmul a x =>
    exact (Formalism.L2.SG.AdBridge.tauF_tmul (Formalism.IndefR.RationalEmbedding.inst D) a x).symm
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), ha, hb]
    exact (map_add _ a b).symm

private theorem finE_Yc_zero_iota_symm (y : (Formalism.L2.SG.InstExistsPf.instOf D).GA) :
    finE (Yc D 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm y) = y.2.1 := by
  have hb := (Formalism.L2.SG.AdBridge.toHA_isBridge (Formalism.IndefR.RationalEmbedding.inst D)
    (Formalism.L2.SG.Closed.adelic_isomorphism_statement (Formalism.IndefR.RationalEmbedding.inst D)).1 y).2
  apply Units.ext
  ext i j
  have hij := congrFun (congrFun hb i) j
  refine Eq.trans ?_ hij.symm
  show Formalism.IndefR.Lev.swapAE D
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E) _) = _
  exact swapAE_map_sndA_eq_tauF D _

abbrev kmat (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) : GL (Fin (Yc D 0).rank) (EAf D) := x.1

theorem finE_kap (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (k : X.B.I.Gf) :
    finE (Yc D 0) (kap X h t k) = (finE (Yc D 0) t)⁻¹ * kmat (castGA h (1, k)).2 * finE (Yc D 0) t := by
  have e2 : finE (Yc D 0) (id ((iotaX X h).symm (1, k)) : GA D (Yc D 0)) = kmat (castGA h (1, k)).2 :=
    (congrArg (finE (Yc D 0)) (iotaX_symm_eq h (1, k))).trans (finE_Yc_zero_iota_symm _)
  have e3 : finE (Yc D 0) (kap X h t k) =
      (finE (Yc D 0) t)⁻¹ * finE (Yc D 0) (id ((iotaX X h).symm (1, k)) : GA D (Yc D 0)) * finE (Yc D 0) t := by
    rw [← map_inv (finE (Yc D 0)) t, ← map_mul (finE (Yc D 0)), ← map_mul (finE (Yc D 0))]
    rfl
  rw [e3, e2]

section Gen

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frGL_mul_apply (t β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    Formalism.L2.DIV.frGL (t * β) y = t * Formalism.L2.DIV.frGL β y * t⁻¹ := by
  simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, mul_inv_rev]
  group

theorem redFn_conj (β t x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Formalism.L2.DIV.Pl E) :
    Formalism.L2.DIV.redFn β PP (t⁻¹ * x * t) = Formalism.L2.DIV.redFn (t * β) PP x := by
  classical
  by_cases hx : x ∈ Formalism.L2.DIV.St (t * β)
  · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hx
    have hy : t⁻¹ * Formalism.L2.DIV.frGL (t * β) y * t = Formalism.L2.DIV.frGL β y := by
      rw [frGL_mul_apply]
      group
    rw [hy, Formalism.L2.DIV.redFn_frGL, Formalism.L2.DIV.redFn_frGL]
  · have hx' : t⁻¹ * x * t ∉ Formalism.L2.DIV.St β := by
      intro hmem
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hmem
      apply hx
      refine MonoidHom.mem_range.2 ⟨y, ?_⟩
      rw [frGL_mul_apply, hy]
      group
    simp only [Formalism.L2.DIV.redFn, Formalism.L2.DIV.ext1, dif_neg hx, dif_neg hx']

end Gen

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) κ) :
    Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g = 1 := by
  obtain rfl : r = n := le_antisymm hr hn
  have hmem : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
    rw [Formalism.L2.DIV.mem_blockTri]
    intro i j hij
    simp [Formalism.L2.DIV.blk2] at hij
  have hself : Formalism.L2.DIV.upperLeftBlock hr g = g := by
    apply Units.ext
    rw [Formalism.L2.DIV.upper_block_val_submatrix hr hmem]
    ext i j
    rfl
  rw [hself]

end GlobalTheory.KapRed

namespace GlobalTheory.KapRed

theorem core (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (g : ℕ) (hβ : IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (hx : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) (hg : 1 ≤ g) (hrad : (Ideal.span {(g : 𝓞 D.host.E)}).IsRadical)
    (hcov : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (g : 𝓞 D.host.E) ∈ PP.asIdeal → PP ∈ Pg ∨ ∃ PP' ∈ Pg, Formalism.IndefR.Lev.IsConjPl PP' PP)
    (hin : ∀ PP ∈ Pg, (g : 𝓞 D.host.E) ∈ PP.asIdeal) :
    x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kg g ↔ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn β PP x.1 = 1 := by
  rw [GlobalTheory.KgFrame.mem_Kg_iff_redFn D β x g hβ hx hg hrad]
  constructor
  · intro H PP hP
    exact H PP (hin PP hP)
  · intro H PP hgP
    rcases hcov PP hgP with hP | ⟨PP', hP', hc⟩
    · exact H PP hP
    · exact GlobalTheory.ConjPlaceRed.redFn_conj_eq_one D β x PP PP' hβ hx hc (H PP' hP')

theorem rank_lowerChainSpace_zero_le (D : D7) : (Yc D 0).rank ≤ D.R.r := by
  have e : (Yc D 0).rank = D.R.rankY 0 := D.sp.Y_rank 0 (Nat.zero_le _)
  rw [e]
  show D.R.r + 0 * D.R.t ≤ D.R.r
  simp

theorem red_kap_eq_one_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = 1 ↔ k ∈ X.B.I.Kg X.B.g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ cG t _ hplg _ _ _ hfr k hk
  obtain ⟨plg, -, hplgw, -, -, -⟩ := hplg
  have hk' := (castGA_mem h k X.B.g).1.1 hk
  have hpos : 1 ≤ D.host.g 0 * D.host.g 1 :=
    Nat.succ_le_of_lt (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
  have hin : ∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hP
    have hsame := hplgw (plg.symm ⟨PP, hP⟩)
    rw [Equiv.apply_symm_apply] at hsame
    have hq : ((D.host.g (plg.symm ⟨PP, hP⟩).1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have hov := D.naut.plGw_over (plg.symm ⟨PP, hP⟩).1 (plg.symm ⟨PP, hP⟩).2
      simp only at hsame
      have hI : PP.asIdeal =
          (D.naut.plGw (plg.symm ⟨PP, hP⟩).1 (plg.symm ⟨PP, hP⟩).2).asIdeal := by
        rw [← hsame]
      rw [hI]
      exact hov
    have hdvd : ∀ q : Fin 2, D.host.g q ∣ D.host.g 0 * D.host.g 1 := by
      intro q
      fin_cases q
      · first
        | exact dvd_mul_right _ _
        | simp
      · first
        | exact dvd_mul_left _ _
        | simp
    obtain ⟨c, hc⟩ := hdvd (plg.symm ⟨PP, hP⟩).1
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hq
  have hcore := core D R.Pg (finE (Yc D 0) t * R.βY 0) (castGA h (1, k)).2 (D.host.g 0 * D.host.g 1) hfr hk' hpos
    (GlobalTheory.TypePrimesRadical.isRadical_span_g_mul D) (GlobalTheory.TypeProductCover.place_cover_prod D R.Pg plg hplgw) hin
  rw [(castGA_mem h k X.B.g).2, X.g_eq, hcore]
  have hrt : ∀ y, cG y = 1 ↔ y = 1 := fun y =>
    ⟨fun hy => cG.injective (hy.trans (map_one cG).symm), fun hy => by rw [hy]; exact map_one cG⟩
  refine (hrt _).trans ?_
  rw [finE_kap X h t k]
  have key : ∀ PP : R.Pg,
      (rTup (R.βY 0) (R.dat0 R.triv) ((finE (Yc D 0) t)⁻¹ * kmat (castGA h (1, k)).2 * finE (Yc D 0) t) PP = 1 ↔
        Formalism.L2.DIV.redFn (finE (Yc D 0) t * R.βY 0) PP.1 (castGA h (1, k)).2.1 = 1) := by
    intro PP
    show Formalism.L2.DIV.upperLeftBlock (R.dat0 R.triv).hr (Formalism.L2.DIV.redFn (R.βY 0) PP.1 _) = 1 ↔ _
    rw [redFn_conj, upperLeftBlock_eq_one_iff_of_mem_blockTri (R.dat0 R.triv).hr (by exact rank_lowerChainSpace_zero_le D)]
  constructor
  · intro H PP hP
    exact (key ⟨PP, hP⟩).1 (congrFun H ⟨PP, hP⟩)
  · intro H
    funext PP
    exact (key PP).2 (H PP.1 PP.2)

end GlobalTheory.KapRed
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isHarishChandraParam_gridRowRealParameter : ∀ (D : D7), HostHyp D → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkX D j → IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  first | exact @GlobalTheory.GridHC.isHCParam_parXp | exact GlobalTheory.GridHC.isHCParam_parXp | (intros; apply GlobalTheory.GridHC.isHCParam_parXp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_leftMul_unitaryMatrix_addHaar : ∀ (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r)), ν.IsAddHaarMeasure → ∀ Φ : Mx D W.rank r → ℂ, ∫ y, Φ (HMul.hMul (Formalism.L2.Theta.mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) ∂ν = ∫ y, Φ y ∂ν := by
  first | exact @GlobalTheory.Twist.LeftHaar.integral_left_unitary | exact GlobalTheory.Twist.LeftHaar.integral_left_unitary | (intros; apply GlobalTheory.Twist.LeftHaar.integral_left_unitary <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standardChar_trace_single_realPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ → ∀ (τ : D.what₂.Tau) (t : AE D),
  finPart D t = 0 → (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) →
  ψ (Algebra.trace (AF D.host.F) (AE D) t) = Complex.exp (Complex.I * (((-(4 * Real.pi : ℂ)) * θ τ (infPart D t)).re : ℂ)) := by
  first | exact @GlobalTheory.PhaseReal.psi_trace_single | exact GlobalTheory.PhaseReal.psi_trace_single | (intros; apply GlobalTheory.PhaseReal.psi_trace_single <;> assumption)
end
