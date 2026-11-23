module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle279
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle327
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiscreteSeriesModelNegSpaceTransfer
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle229
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle230
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Order.Star.Rat
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
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IotaNorm

theorem iota_norm_of_eq {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) :
    (∀ g ∈ GinfC (D.sp.Y 0), ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm) g).2 = 1) ∧
    (1 ≤ (D.sp.Y 0).rank → ∀ x : I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0),
      (GlobalTheory.Count.tau1 I (x * (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm) g))⁻¹ ≤
        C * normInf θ (D.sp.Y 0) g) := by
  subst h
  set ι := (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm) with hιdef
  have key : ∀ k, (∀ v, Formalism.MainNotions.S.uMat ((ι k).1 v) = Formalism.L2.SG.AdBridge.ofHAInf (Formalism.L2.SG.InstExistsPf.instOf D) k v) ∧ (Formalism.L2.SG.InstExistsPf.instOf D).fmat (ι k).2 = Formalism.L2.SG.AdBridge.ofHAFin _ k := by
    intro k
    have := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D k)
    have e := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply k
    exact ⟨fun v => (this.1 v).trans (congrArg (fun z => Formalism.L2.SG.AdBridge.ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) z v) e),
      this.2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (Formalism.IndefR.RationalEmbedding.inst D)) e)⟩
  have hinf : ∀ k v, Formalism.MainNotions.S.uMat ((ι k).1 v) = ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ *
      Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J (θ ((Formalism.L2.Host.tauPl D).symm v)) k *
      (Formalism.L2.SG.InstExistsPf.instOf D).P v := fun k v =>
    ((key k).1 v).trans (congrArg (fun M => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M * (Formalism.L2.SG.InstExistsPf.instOf D).P v)
      (GlobalTheory.IotaReal.map_thetaV_gen (Formalism.L2.SG.InstExistsPf.instOf D) v (θ ((Formalism.L2.Host.tauPl D).symm v)) (hθ _) k))
  have hfin : ∀ g ∈ GinfC (D.sp.Y 0), (ι g).2 = 1 := by
    intro g hg
    apply Subtype.ext
    apply Units.ext
    refine (key g).2.trans (GlobalTheory.IotaReal.ofHAFin_eq_one _ _ ?_)
    have e3 : (finHom (D.sp.Y 0) g).val = 1 := by
      rw [show finHom (D.sp.Y 0) g = 1 from hg]; rfl
    ext i j
    exact congrFun (congrFun e3 i) j
  refine ⟨hfin, fun hn x => ?_⟩
  choose c hc0 hc using fun v => GlobalTheory.TauNorm.exp_dOp_le ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ ((Formalism.L2.SG.InstExistsPf.instOf D).P v)
  have hC : 0 ≤ ∑ v, c v := Finset.sum_nonneg fun v _ => hc0 v
  have hn' : 1 ≤ (Formalism.L2.SG.InstExistsPf.instOf D).n := hn
  have hp : 0 ≤ (GlobalTheory.Count.tau1 (Formalism.L2.SG.InstExistsPf.instOf D) x)⁻¹ :=
    inv_nonneg.2 ((GlobalTheory.TauLipschitz.tauLip (Formalism.L2.SG.InstExistsPf.instOf D) hn').1 _).le
  refine ⟨(GlobalTheory.Count.tau1 (Formalism.L2.SG.InstExistsPf.instOf D) x)⁻¹ * ∑ v, c v, mul_nonneg hp hC, fun g hg => ?_⟩
  have hv : ∀ v, Real.exp (GlobalTheory.Count.dOp (Formalism.MainNotions.S.uMat ((ι g).1 v))) ≤ (∑ v, c v) * normInf θ (D.sp.Y 0) g := by
    intro v
    have h0 := GlobalTheory.TauNorm.uMat_ne_zero (Formalism.L2.SG.InstExistsPf.instOf D) hn' (ι g) v
    rw [hinf g v] at h0 ⊢
    have h2 := hc v _ h0
    have h3 : c v ≤ ∑ v, c v := Finset.single_le_sum (fun v _ => hc0 v) (Finset.mem_univ _)
    exact h2.trans (mul_le_mul h3 (GlobalTheory.TauNorm.sum_le_normInf θ g ((Formalism.L2.Host.tauPl D).symm v))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hC)
  have hh := GlobalTheory.TauNorm.inv_tau_mul_le (Formalism.L2.SG.InstExistsPf.instOf D) hn' x (ι g) (hfin g hg) _ hv
  rw [← mul_assoc] at hh
  exact hh

theorem iotaX_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ g ∈ GinfC (D.sp.Y 0), (iotaX X h g).2 = 1) ∧ (1 ≤ (D.sp.Y 0).rank → ∀ x : X.B.I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0), (GlobalTheory.Count.tau1 X.B.I (x * iotaX X h g))⁻¹ ≤ C * normInf R.θ (D.sp.Y 0) g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ hMod _
  exact iota_norm_of_eq R.θ hMod.inf X.B.I h

end GlobalTheory.IotaNorm
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.AdSpan

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

def RealScal (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (a : GA D T) (z : ℂ) : Prop :=
  ∀ φ : TF S.rank C.g, SW.IsSB φ → om (1, a) (C.Th (C.xB B) φ) = z • C.Th (C.xB (C.mvB a B)) φ

def HolUpTo (C : Ctx S T) (B : C.Bas) (la : Wt C.X.Ψ T.rank) (z φ : GA D T → ℂ) : Prop :=
  ∀ g : GA D T, ∃ Q : Frame C.X.Ψ T.rank → ℂ, DifferentiableOn ℂ Q C.X.dom ∧
    (∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, Q (rmul x b) = bchar la b * Q x) ∧
    ∀ a ∈ GinfC T, φ (g * a) = z a * Q (C.xB (C.mvB a B))

def detPow (θ : InfFam D) (V : HSp D) (m : D.what₂.Tau → ℤ) (a : GA D V) : ℂ :=
  ∏ ρ, (compAt θ ρ (Formalism.L2.Theta.mt V a)).det ^ m ρ

def torAt (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (ρ : D.what₂.Tau)
    (t : Fin V.rank → ℝ) : GA D V :=
  atTau θ V ρ (B ρ * diagonal (fun a => cexp ((t a : ℂ) * I)) * (B ρ)⁻¹)

def LowKilled (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) : Prop :=
  HolRead.SmoothReal θ V φ ∧ ∀ ρ (c d : Fin V.rank), d < c → RderC θ V ρ (B ρ * Matrix.single c d 1 * (B ρ)⁻¹) φ = 0

def revPos {n : ℕ} (p : ℕ) (a : Fin n) : Fin n :=
  if h : (a : ℕ) < p ∧ p ≤ n then ⟨p - 1 - a, by omega⟩ else a

theorem revPos_revPos {n : ℕ} (p : ℕ) (a : Fin n) : revPos p (revPos p a) = a := by
  by_cases h : (a : ℕ) < p ∧ p ≤ n
  · have h' : p - 1 - (a : ℕ) < p ∧ p ≤ n := ⟨by omega, h.2⟩
    ext
    simp only [revPos, dif_pos h, Fin.val_mk, dif_pos h']
    omega
  · simp only [revPos, dif_neg h]

def revB {ι : Type} {n : ℕ} (p : ℕ) (B : ι → Matrix (Fin n) (Fin n) ℂ) : ι → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => (B τ).submatrix id (revPos p)

def thetaSet (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (u : WO S T → ℂ)
    (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) : Set (GA D T → ℂ) :=
  {φ | ∃ (h : GA D S) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q ∈ Harm.rowHighest ℂ c c' ∧
    φ = fun g => om (h, g) (C.fvec B u Q) 0}

def ContT (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun g : GA D T => om (1, g) f w

abbrev reS (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : HSp D := StdFrame.reframe S b

def frP (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Matrix (Fin S.rank) (Fin S.rank) D.host.E :=
  S.frame.toMatrix b

def frPinv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Matrix (Fin S.rank) (Fin S.rank) D.host.E :=
  b.toMatrix S.frame

def reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x : WO (reS S b) T) : WO S T :=
  HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))

def reF (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : (WO S T → ℂ) →ₗ[ℂ] (WO (reS S b) T → ℂ) :=
  LinearMap.funLeft ℂ ℂ (reW S T b)

theorem reF_apply (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) (x : WO (reS S b) T) :
    reF S T b f x = f (reW S T b x) := rfl

theorem reF_zero (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) : reF S T b f 0 = f 0 := by
  rw [reF_apply]
  congr 1
  exact Matrix.zero_mul _

end GlobalTheory.AdSpan

end
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.LinRed
open scoped InnerProductSpace

namespace GlobalTheory.LeviDense

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

private theorem exists_iteratedDeriv_inner_semigroup_eq {T : ℝ → V →L[ℂ] V} (hT : ∀ s t, T (s + t) = T s ∘L T t)
    {S : Submodule ℂ V} (hd : ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t => T t v) v' 0) (w : V) (k : ℕ) :
    ∀ v ∈ S, ∃ u ∈ S, iteratedDeriv k (fun t => ⟪w, T t v⟫_ℂ) = fun t => ⟪w, T t u⟫_ℂ := by
  induction k with
  | zero => intro v hv; exact ⟨v, hv, by simp⟩
  | succ k ih =>
    intro v hv
    obtain ⟨v', hv', hder⟩ := hd v hv
    have hderiv : deriv (fun t => ⟪w, T t v⟫_ℂ) = fun t => ⟪w, T t v'⟫_ℂ := by
      funext t
      have h3 : HasDerivAt (fun s => T (s - t) v) v' t :=
        HasDerivAt.comp_sub_const (f := fun s => T s v) t t (by rw [sub_self]; exact hder)
      have h2 : HasDerivAt (fun s => T t (T (s - t) v)) (T t v') t :=
        ((T t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h3
      have h1 : HasDerivAt (fun s => T s v) (T t v') t := by
        refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        show T s v = T t (T (s - t) v)
        rw [← ContinuousLinearMap.comp_apply, ← hT, add_sub_cancel]
      exact ((((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1)).deriv
    obtain ⟨u, hu, hk⟩ := ih v' hv'
    exact ⟨u, hu, by rw [iteratedDeriv_succ', hderiv, hk]⟩

theorem oneParameter_mem_closure {T : ℝ → V →L[ℂ] V} (h0 : T 0 = 1) (hT : ∀ s t, T (s + t) = T s ∘L T t)
    {S : Submodule ℂ V} (hd : ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t => T t v) v' 0)
    (ha : ∀ v ∈ S, ∀ w, AnalyticOnNhd ℝ (fun t => ⟪w, T t v⟫_ℂ) Set.univ) (t : ℝ) :
    ∀ v ∈ S.topologicalClosure, T t v ∈ S.topologicalClosure := by
  have key : ∀ v ∈ S, T t v ∈ S.topologicalClosure := by
    intro v hv
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    have hf := ha v hv w
    have hall : ∀ k, iteratedDeriv k (fun s => ⟪w, T s v⟫_ℂ) 0 = 0 := by
      intro k
      obtain ⟨u, hu, hk⟩ := exists_iteratedDeriv_inner_semigroup_eq hT hd w k v hv
      rw [hk]
      simp only [h0, ContinuousLinearMap.one_apply]
      exact Submodule.inner_left_of_mem_orthogonal hu hw
    have htop : analyticOrderAt (fun s => ⟪w, T s v⟫_ℂ) 0 = ⊤ := by
      by_contra hne
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
      have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := m + 1)
        (hf 0 (Set.mem_univ _))).2 (fun i _ => hall i)
      rw [← hm] at hle
      have : m + 1 ≤ m := by exact_mod_cast hle
      omega
    exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
      (analyticOrderAt_eq_top.1 htop) (Set.mem_univ t)
  intro x hx
  have hcl : IsClosed ((T t) ⁻¹' (S.topologicalClosure : Set V)) :=
    S.isClosed_topologicalClosure.preimage (T t).continuous
  have hx' : x ∈ closure (S : Set V) := by rw [← Submodule.topologicalClosure_coe]; exact hx
  exact closure_minimal (fun v hv => key v hv) hcl hx'

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem mul_Jm_comm_of_unitary_of_preserves {n : ℕ} (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ}
    (hu : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (hJ : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) :
    A * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * A := by
  have h2 : A * Aᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.1 hu
  calc A * Formalism.REAL.Jm ε = A * (Aᴴ * Formalism.REAL.Jm ε * A) := by rw [hJ]
    _ = (A * Aᴴ) * Formalism.REAL.Jm ε * A := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * A := by rw [h2, Matrix.one_mul]

end


omit [CompleteSpace V] in
theorem isKFinOn_of_isKFinIn {n : ℕ} {ε : Fin n → Bool} {M : Subgroup (UJ ε)}
    {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} {v : V} (h : IsKFinIn M σ v) : IsKFinOn (mats M) σ v := by
  obtain ⟨U, hU, hv, hk⟩ := h
  refine ⟨U, hU, hv, ?_⟩
  rintro _ ⟨⟨g, hgM, rfl⟩, hgu⟩ w hw
  refine hk g (Subgroup.mem_inf.2 ⟨?_, hgM⟩) w hw
  show toM g ∈ Kset ε
  show toM g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ toM g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * toM g
  exact ⟨hgu, mul_Jm_comm_of_unitary_of_preserves ε hgu g.2⟩

end GlobalTheory.LeviDense

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_discreteSeriesModel_negSpace_transfer : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S), ∃ M₁ : DSModel (GlobalTheory.Grid.sgn true V) (fun τ => (S τ).image fun x => (x.1, !x.2)), (∀ τ, cart M₁ τ = -cart M τ) ∧ (∀ τ, onb M₁ τ = onb M τ) ∧ ∀ {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (θ : InfFam D), IsInfFam θ → ∀ (ω : GlobalTheory.Grid.WRep V W) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It₁ : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M₁), IsItW θ M₁ M' (GlobalTheory.Grid.WRep.toSgn true ω) pt It₁ → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω pt It := by
  first | exact @GlobalTheory.NegModel.exists_negModel_transfer | exact GlobalTheory.NegModel.exists_negModel_transfer | (intros; apply GlobalTheory.NegModel.exists_negModel_transfer <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.Grid

theorem card_weightX_grid : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (j : ℕ), 1 ≤ j → j ≤ D.R.m →
    ((GlobalTheory.Grid.grid D τ).weightX j).card = GlobalTheory.Grid.rkX D j := by
  intro D _ τ j _ hj
  have hcen : GlobalTheory.Grid.cen D τ = GlobalTheory.ChiGrid.cen D 1 τ := by
    funext i
    unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
    rw [GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  have hg : GlobalTheory.Grid.grid D τ = GlobalTheory.ChiGrid.num D 1 τ := by
    unfold GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.ChiGrid.num
    rw [hcen, GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  rw [hg]
  let Γ := GlobalTheory.ChiGrid.num D 1 τ
  have num_e {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).e l : ℤ) : ℚ) = (D.hc τ).e ⟨l - 1, by omega⟩ := by
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    exact GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).e_int ⟨l, by omega⟩
  
  have num_b {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).b l : ℤ) : ℚ) = (D.hc τ).b ⟨l - 1, by omega⟩ := by
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    exact GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).b_int ⟨l, by omega⟩
  
  have num_v {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : (((Γ).v i : ℤ) : ℚ) = (D.hc τ).v ⟨i - 2, by omega⟩ := by
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
    exact GlobalTheory.SignedHC.GridData.extend_cast 2 (D.hc τ).v_int ⟨i, by omega⟩
  
  have num_be {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).e l : ℚ) - (Γ).b l := by
    rw [num_e h1 h2, num_b h1 h2]
    exact (D.hc τ).gap_be _
  
  have num_eb {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).b (l + 1) : ℚ) - (Γ).e l := by
    rw [num_e h1 (by omega), num_b (by omega) h2]
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    exact (D.hc τ).gap_eb ⟨l, by omega⟩ (by simpa using (by omega : l + 1 < D.R.m))
  
  have num_e_lt {l l' : ℕ} (h1 : 1 ≤ l) (h : l < l') (h2 : l' ≤ D.R.m) : (D.R.t : ℚ) + 3 + (Γ).e l ≤ (Γ).e l' := by
    induction l', h using Nat.le_induction with
    | base =>
      linarith [num_be (l := l + 1) (by omega) h2, num_eb h1 h2]
    | succ n hn ih =>
      have := ih (by omega)
      have e1 := num_be (l := n + 1) (by omega) h2
      have e2 := num_eb (l := n) (by omega) h2
      have : (0 : ℚ) ≤ D.R.t := by positivity
      linarith
  
  have num_cloud {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : -((Γ).b 1 : ℚ) + 1 ≤ (Γ).v i := by
    have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    have hk : 2 ≤ D.R.k := by omega
    have base : -((Γ).b 1 : ℚ) < (Γ).v D.R.k := by
      rw [num_v hk le_rfl, num_b le_rfl hm]
      have e1 := (D.hc τ).u_last_gt (by omega) (by omega)
      have e2 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
      have e3 : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
      simp only [e3] at e2
      exact e1.trans e2
    have base' : -((Γ).b 1) < (Γ).v D.R.k := by exact_mod_cast base
    have step : (Γ).v D.R.k ≤ (Γ).v i := by
      rcases h2.eq_or_lt with rfl | h
      · exact le_rfl
      · exact ((Γ).v_anti i D.R.k h1 h le_rfl).le
    have : -((Γ).b 1) + 1 ≤ (Γ).v i := by omega
    exact_mod_cast this
  
  have a_le {i j : ℕ} (h : i ≤ j) : (Γ).a j ≤ (Γ).a i := by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · have : (0 : ℚ) ≤ (Γ).ga := by positivity
      linarith [GlobalTheory.ChiGrid.a_add_le (G := Γ) h]
  
  have hblock {l : ℕ} {x : ℚ} (h : x ∈ (GlobalTheory.ChiGrid.num D 1 τ).blockMPlus l) :
      -((GlobalTheory.ChiGrid.num D 1 τ).e l : ℚ) - (D.R.t : ℚ) / 2 ≤ x ∧ x ≤ -((GlobalTheory.ChiGrid.num D 1 τ).e l : ℚ) + (D.R.t : ℚ) / 2 := by
    have h' := abs_le.1 (GlobalTheory.SignedHC.abs_sub_le_of_mem_block h)
    have e : (((GlobalTheory.ChiGrid.num D 1 τ).t + 1 : ℕ) : ℚ) = D.R.t + 1 := by push_cast; rfl
    rw [e] at h'
    constructor <;> linarith [h'.1, h'.2]
  have habove {j : ℕ} (hj : j + 1 ≤ D.R.m) {x y : ℚ} (hx : x ∈ (GlobalTheory.ChiGrid.num D 1 τ).weightX j) (hy : y ∈ (GlobalTheory.ChiGrid.num D 1 τ).blockMPlus (j + 1)) : y < x := by
    let Γ := GlobalTheory.ChiGrid.num D 1 τ
    have hm : 1 ≤ D.R.m := by omega
    have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    have ht : (0 : ℚ) ≤ D.R.t := by positivity
    have hg : (0 : ℚ) ≤ Γ.ga := by positivity
    obtain ⟨y1, y2⟩ := hblock hy
    have hbe := num_be (l := 1) le_rfl hm
    have he1 : ((Γ.e 1 : ℚ)) ≤ Γ.e (j + 1) := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · exact le_rfl
      · linarith [num_e_lt (l := 1) (l' := j + 1) le_rfl (by omega) hj]
    have hlow : y < -(Γ.b 1 : ℚ) := by linarith
    have hc2 := num_cloud (i := 2) le_rfl hk
    have ham : Γ.a Γ.m = Γ.v 2 + Γ.ga + 1 / 2 := Γ.a_m
    rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩
    · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
      linarith [a_le hi]
    · obtain ⟨i, h1, h2, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
      have := num_cloud h1 h2
      simp only [GlobalTheory.SignedHC.GridData.vHalf]
      linarith
    · have := (GlobalTheory.ChiGrid.blockC'_between (GlobalTheory.ChiGrid.num_nearMid D 1 τ) (GlobalTheory.ChiGrid.odd_sLen D).pos (GlobalTheory.ChiGrid.sLen_lt_gap D 1) h1 h2 h).1
      linarith [a_le h2]
    · have := num_e_lt h1 (by omega : l < j + 1) hj
      have := (hblock h).1
      linarith
  have hcard : ∀ {j : ℕ}, j ≤ D.R.m → ((GlobalTheory.ChiGrid.num D 1 τ).weightX j).card = GlobalTheory.ChiGrid.rankX D j := by
    intro j hj
    induction j with
    | zero =>
      rw [GlobalTheory.ChiGrid.card_weightX_zero (GlobalTheory.ChiGrid.num_nearMid D 1 τ) (GlobalTheory.ChiGrid.odd_sLen D).pos (GlobalTheory.ChiGrid.sLen_lt_gap D 1)]
      simp [GlobalTheory.ChiGrid.rankX]; rfl
    | succ j ih =>
      rw [(GlobalTheory.ChiGrid.num D 1 τ).weightX_succ, Finset.card_union_of_disjoint
        (Finset.disjoint_left.2 fun x hx hy => (habove hj hx hy).ne rfl), ih (by omega)]
      have : ((GlobalTheory.ChiGrid.num D 1 τ).blockMPlus (j + 1)).card = D.R.t + 1 := GlobalTheory.SignedHC.card_block _ _
      rw [this]
      simp only [GlobalTheory.ChiGrid.rankX]
      ring
  rw [hcard hj]
  rfl

end GlobalTheory.Grid
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem _root_.GlobalTheory.T.discreteSeriesModelParamShiftedWeight_of_coverDiscreteSeries : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D → DirectBridge D := by
  first | exact @GlobalTheory.ArchRec.Direct.directBridge | exact GlobalTheory.ArchRec.Direct.directBridge | (intros; apply GlobalTheory.ArchRec.Direct.directBridge <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem _root_.GlobalTheory.T.thetaCorrespondence_pairingLaw_of_tensorLaw : ∀ (p q r s : ℕ) (T₁ : GrpData p q) (σ : Type) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (R₁ : DSRep T₁) (T₂ : GrpData r s) (R₂ : DSRep T₂) (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ), IsGK a₁ → IsGK a₂ → AdmGK R₁.HK → Module.finrank ℂ ↥(hwSub R₁.HK.act Λ₁) = 1 → TensLaw a₁ a₂ R₁ R₂ Λ₁ Λ₂ → PairLaw a₁ a₂ R₁ R₂ Λ₁ Λ₂ := by
  first | exact @GlobalTheory.ArchRec.PairOfTens.pairLaw_of_tensLaw | exact GlobalTheory.ArchRec.PairOfTens.pairLaw_of_tensLaw | (intros; apply GlobalTheory.ArchRec.PairOfTens.pairLaw_of_tensLaw <;> assumption)
end
