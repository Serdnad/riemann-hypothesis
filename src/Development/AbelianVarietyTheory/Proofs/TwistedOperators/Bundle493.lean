module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle458
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle323
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle459
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle359
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
import Std.Tactic.BVDecide.Normalize.Bool
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FockApprox

section

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity GlobalTheory.SquareComm
open scoped ENNReal

variable {D : D7}

theorem cart_frSgn (ε : Bool) (S : GlobalTheory.Grid.Node D) :
    (frSgn ε (Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS ε S := by
  funext τ
  cases ε
  · show (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor false (S.M.ε τ a)) * S.M.fr τ = (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (S.M.ε τ) * S.M.fr τ
    simp only [Bool.false_xor]
  · have e' : Formalism.REAL.Jm (fun a => xor true (S.M.ε τ a)) = -Formalism.REAL.Jm (S.M.ε τ) := by
      ext a b
      by_cases h : a = b
      · subst h; cases h' : S.M.ε τ a <;> simp [Formalism.REAL.Jm, h']
      · simp [Formalism.REAL.Jm, h]
    show (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (S.M.ε τ a)) * S.M.fr τ = -((S.M.fr τ)⁻¹ * Formalism.REAL.Jm (S.M.ε τ) * S.M.fr τ)
    rw [e', Matrix.mul_neg, Matrix.neg_mul]

theorem ptF_eq_fock (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (P : GlobalTheory.Grid.Pol S T) :
    ptF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f P = GlobalTheory.Grid.fock ψ θ ε S T f P := by
  unfold ptF GlobalTheory.Grid.fock
  rw [cart_frSgn]
  rfl

theorem isVacF_iff (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) :
    IsVacF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f ↔ GlobalTheory.Grid.IsFinVec ψ θ ε S T f := by
  unfold IsVacF GlobalTheory.Grid.IsFinVec
  rw [cart_frSgn]
  rfl

end

end GlobalTheory.FockApprox

namespace GlobalTheory.FockApprox

section

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity GlobalTheory.SquareComm
open scoped ENNReal

theorem exists_sum_of_mem_fockSpan {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (U : AddSubgroup (WO S.V T.V)) {g : WO S.V T.V → ℂ}
    (hg : g ∈ fockSpan ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) U) :
    ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T),
      (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ g = ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l) := by
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.1 hg
  choose f₀ P h1 _ h3 using fun l => (x l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => (isVacF_iff ψ θ ε S T _).1 (h1 l), ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h3 l, map_smul, ptF_eq_fock]

end

end GlobalTheory.FockApprox

namespace GlobalTheory.FockApprox

section

open Formalism.IndefR.Mult GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity
open scoped ENNReal

theorem dense_level {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} (A : Fr V) (B : Fr W)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    (hm : IsCovolOne (ratL W V) μ 𝓕) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U) (d : ℕ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ g ∈ fockSpan ψ θ A B U, g ∈ GlobalTheory.Size.thetaLevel ψ V W U ∧ sobO ψ θ μ 𝓕 d (f - g) < δ := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL ψ V W (toB hψ f hf.1) = f := coe_toB hψ f hf.1
  have hF : toB hψ f hf.1 ∈ (GlobalTheory.Size.thetaLevel ψ V W U).comap (coeL ψ V W) := by
    rw [Submodule.mem_comap, e0]
    exact hf
  obtain ⟨g, h1, h2, h3⟩ := dense_vec h hψ A B hU (toL2 _ _ (μ.restrict 𝓕))
    (fun v G => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ μ 𝓕 hm.1 hm.2.1 _ G)
    (fun a : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool =>
      atPl a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) d hF hδ
  refine ⟨coeL ψ V W g, h1, h2, lt_of_eq_of_lt ?_ h3⟩
  have e1 : ∀ G : BB ψ V W, l2O μ 𝓕 (coeL ψ V W G) = ‖toL2 _ _ (μ.restrict 𝓕) G‖ₑ := fun G =>
    (eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (μ.restrict 𝓕) ℂ G.1)).symm.trans (Lp.enorm_def _).symm
  have e2 : f - coeL ψ V W g = coeL ψ V W (toB hψ f hf.1 - g) := by rw [LinearMap.map_sub, e0]
  simp only [sobO, wordSum, e2, coe_word h hψ hU _ (sub_mem hF h2), e1]

end

end GlobalTheory.FockApprox


open scoped ENNReal in
theorem GlobalTheory.FockApprox.theta_approx_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → IsStdChar D ψ (-1) → ∀ (ε : Bool) (S T : GlobalTheory.Grid.Node D) (U : AddSubgroup (WO S.V T.V)), IsOpen (U : Set (WO S.V T.V)) → ∀ Φ, Φ ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U → ∀ (μ : Measure (WO S.V T.V)) (𝓕 : Set (WO S.V T.V)), IsCovolOne (ratL T.V (GlobalTheory.Grid.sgn ε S.V)) μ 𝓕 → ∀ (d : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U ∧ @GlobalTheory.Size.sobO D ψ θ (GlobalTheory.Grid.sgn ε S.V) T.V μ 𝓕 d (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) < ENNReal.ofReal δ := by
  intro D ψ θ hθ hψ ε S T U hU Φ hΦ μ 𝓕 hm d δ hδ
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.FockApprox.dense_level (ψ := ψ) (θ := θ) (V := GlobalTheory.Grid.sgn ε S.V) (W := T.V)
    (GlobalTheory.SquareComm.frSgn ε (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) hψ hθ hm hU hΦ d
    (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨n, f, p, hf, hg⟩ := GlobalTheory.FockApprox.exists_sum_of_mem_fockSpan ψ θ ε S T U h1
  refine ⟨n, f, p, hf, ?_, ?_⟩
  · rw [← hg]
    exact sub_mem hΦ h2
  · rw [← hg]
    exact h3

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar.AtConj

theorem resT_of_mem {D : D7} (PP : Pl D.host.E) {x : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resT PP x = Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ := by
  unfold resT; rw [dite_eq_left hx]

theorem resT_zero {D : D7} (PP : Pl D.host.E) : resT PP (0 : EAf D) = 0 := by
  rw [resT_of_mem PP (zero_mem _)]
  exact map_zero (Formalism.L2.DIV.resS D.host.F PP)

theorem resT_add {D : D7} (PP : Pl D.host.E) {x y : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hy : y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resT PP (x + y) = resT PP x + resT PP y := by
  rw [resT_of_mem PP hx, resT_of_mem PP hy, resT_of_mem PP (add_mem hx hy)]
  exact map_add (Formalism.L2.DIV.resS D.host.F PP) ⟨x, hx⟩ ⟨y, hy⟩

theorem resT_sum {D : D7} (PP : Pl D.host.E) {ι : Type} [Fintype ι] (f : ι → EAf D)
    (hf : ∀ i, f i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resT PP (∑ i, f i) = ∑ i, resT PP (f i) := by
  have hs : (∑ i, f i) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := sum_mem fun i _ => hf i
  rw [resT_of_mem PP hs]
  have e : (⟨∑ i, f i, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ i, (⟨f i, hf i⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) := by
    apply Subtype.ext
    simp

  rw [e, map_sum]
  exact Finset.sum_congr rfl fun i _ => (resT_of_mem PP (hf i)).symm

theorem flagV_f {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ + k < i.1) (h2 : i.1 < 2 * ρ + k + 1) :
    GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = f ⟨2 * ρ + k - i.1, by omega⟩ := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h2]

theorem symmetricFlagBasisVectors_apply_middle {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : i.1 = ρ + k) : GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = z := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h1]

theorem flagV_b {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ ≤ i.1) (h2 : i.1 < ρ + k) : GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = b ⟨i.1 - ρ, by omega⟩ := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_left h2]

end GlobalTheory.SeeConjChar.AtConj

open GlobalTheory.SeeConjChar GlobalTheory.SeeConjChar.AtConj

theorem GlobalTheory.SeeConjChar.resT_cP_argT : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = GlobalTheory.SeeConjChar.conjRes PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wB D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hGrp β hβ hred PP hP κ hS hK2
  classical
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    have e := X.n_eq
    rw [h] at e
    have e2 := Formalism.L2.DIV.ranks_r_sym D
    change (Formalism.L2.SG.InstExistsPf.instOf D).n = _
    omega
  have hrn : D.R.r = (Yc D 0).rank := by
    have e := X.n_eq
    rw [h] at e
    change D.R.r = (Formalism.L2.SG.InstExistsPf.instOf D).n
    omega
  have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ hK2
  have hU : upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unip (kP PP) D.R.r :=
    unipCol_le _ _ _ (((GlobalTheory.T.mem_K2_iff_upperLeftBlock_reductions R F X h hL hGrp β hβ hred κ hK hS).1 hK2) PP hP)
  have hMinv : (finE (Yc D 0) κ)⁻¹ ∈ St β := inv_mem hS
  have hredinv : redFn β PP (finE (Yc D 0) κ)⁻¹ = (redFn β PP (finE (Yc D 0) κ))⁻¹ := extendOne_inv _ hS
  have hC : ∀ a j, hT X h (flagAt X h PP j) (Matrix.mulVec (finE (Yc D 0) κ).val (pairAt X h PP a)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (hT X h (flagAt X h PP j) (Matrix.mulVec (finE (Yc D 0) κ).val (pairAt X h PP a))) =
        conjRes PP ((sgnD D.R.rS D.R.k a : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val a j) := by
    intro a j
    have c1 := GlobalTheory.T.residue_conjugatePlace_hermitianForm_adjoint X h PP κ (flagAt X h PP j) (pairAt X h PP a)
    have c2 := GlobalTheory.T.residue_otherInstanceForm_frameStabilizer_mulVec X h β PP (flagAt X h PP) (hred PP hP) _ hMinv (pairAt X h PP a) (GlobalTheory.T.otherInstanceForm_flagPairing_integral_on_frameLattice X h β hβ PP a) j
    refine ⟨c1.1.2 c2.1, ?_⟩
    rw [c1.2, c2.2, hredinv]
    congr 1
    simp only [GlobalTheory.T.residue_otherInstanceForm_flagPairing_eq_signedDelta R X h hL PP hP a, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

  let fF : Fin D.R.rS → Fin (Yc D 0).rank := fun a => ⟨2 * D.R.rS + D.R.k - a.1, by have := a.2; omega⟩
  let fN : Fin D.R.rS → Fin (Yc D 0).rank := fun a =>
    ⟨if a.1 + 1 < D.R.rS then 2 * D.R.rS + D.R.k - (a.1 + 1) else D.R.rS + D.R.k, by have := a.2; split_ifs <;> omega⟩
  let gB : Fin D.R.k → Fin (Yc D 0).rank := fun i => ⟨D.R.rS + D.R.k - 1 - i.1, by have := i.2; omega⟩
  have hF : ∀ a, f0T X h a = flagAt X h PP (fF a) := by
    intro a
    have ha := a.2
    have e : (fF a).1 = 2 * D.R.rS + D.R.k - a.1 := rfl
    have h1 : D.R.rS + D.R.k < (fF a).1 := by omega
    have h2 : (fF a).1 < 2 * D.R.rS + D.R.k + 1 := by omega
    unfold flagAt
    split_ifs <;> rw [flagV_f _ _ _ _ _ h1 h2] <;> congr 1 <;> ext <;> simp only [e] <;> omega
  have hNx : ∀ a, Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a = pairAt X h PP (fN a) := by
    intro a
    have ha := a.2
    have e : (fN a).1 = if a.1 + 1 < D.R.rS then 2 * D.R.rS + D.R.k - (a.1 + 1) else D.R.rS + D.R.k := rfl
    unfold Formalism.L2.SG.HidaSetting.nxt
    by_cases hlt : a.1 + 1 < D.R.rS
    · rw [dite_eq_left hlt]
      rw [if_pos hlt] at e
      have h1 : D.R.rS + D.R.k < (fN a).1 := by omega
      have h2 : (fN a).1 < 2 * D.R.rS + D.R.k + 1 := by omega
      unfold pairAt
      split_ifs <;> rw [flagV_f _ _ _ _ _ h1 h2] <;> congr 1 <;> ext <;> simp only [e] <;> omega
    · rw [dite_eq_right hlt]
      rw [if_neg hlt] at e
      unfold pairAt
      split_ifs <;> rw [symmetricFlagBasisVectors_apply_middle _ _ _ _ _ e]
  have hBd : GlobalTheory.SeeConjChar.sideAt X h PP ≠ true → ∀ i, bwdT X h i = flagAt X h PP (gB i) := by
    intro hs i
    have hi := i.2
    have e : (gB i).1 = D.R.rS + D.R.k - 1 - i.1 := rfl
    have hs' : ¬ GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by simpa [GlobalTheory.SeeConjChar.sideAt] using hs
    unfold flagAt
    rw [if_neg hs', flagV_b _ _ _ _ _ (by omega) (by omega)]
    congr 1; ext; simp only [e, Fin.val_rev]; omega
  have hBw : GlobalTheory.SeeConjChar.sideAt X h PP ≠ true → ∀ i : Fin D.R.k, bwT X h i = pairAt X h PP (gB i) := by
    intro hs i
    have hi := i.2
    have e : (gB i).1 = D.R.rS + D.R.k - 1 - i.1 := rfl
    have hs' : ¬ GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by simpa [GlobalTheory.SeeConjChar.sideAt] using hs
    unfold pairAt
    rw [if_neg hs', flagV_b _ _ _ _ _ (by omega) (by omega)]
    congr 1; ext; simp only [e, Fin.val_rev]; omega

  have hfterm : ∀ a, hT X h (f0T X h a) (Matrix.mulVec (finE (Yc D 0) κ).val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (hT X h (f0T X h a) (Matrix.mulVec (finE (Yc D 0) κ).val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a))) =
        conjRes PP ((sgnD D.R.rS D.R.k (fN a) : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val (fN a) (fF a)) := by
    intro a
    rw [hF a, hNx a]
    exact hC _ _
  have hbterm : ∀ i : Fin D.R.k, (if hi : i.1 + 1 < D.R.k then hT X h (bwdT X h i) (Matrix.mulVec (finE (Yc D 0) κ).val (bwT X h ⟨i.1 + 1, hi⟩)) else 0) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (if hi : i.1 + 1 < D.R.k then hT X h (bwdT X h i) (Matrix.mulVec (finE (Yc D 0) κ).val (bwT X h ⟨i.1 + 1, hi⟩)) else 0) =
        conjRes PP (if hi : i.1 + 1 < D.R.k then (if GlobalTheory.SeeConjChar.sideAt X h PP then 0 else (sgnD D.R.rS D.R.k (gB ⟨i.1 + 1, hi⟩) : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) := by
    intro i
    by_cases hi : i.1 + 1 < D.R.k
    · rw [dite_eq_left hi, dite_eq_left hi]
      by_cases hs : GlobalTheory.SeeConjChar.sideAt X h PP = true
      · rw [if_pos hs]
        obtain ⟨h1, h2⟩ := GlobalTheory.T.residue_conjugatePlace_hermitian_dualBasis_stabiliser_eq_zero X h β hβ PP hs _ hS i ⟨i.1 + 1, hi⟩
        exact ⟨h1, by rw [h2, map_zero]⟩
      · rw [if_neg hs, hBd hs i, hBw hs ⟨i.1 + 1, hi⟩]
        exact hC _ _
    · rw [dite_eq_right hi, dite_eq_right hi]
      exact ⟨zero_mem _, by rw [map_zero, resT_zero]⟩
  unfold argT

  rw [resT_add _ (sum_mem fun a _ => (hfterm a).1) (sum_mem fun i _ => (hbterm i).1), resT_sum _ _ (fun a => (hfterm a).1),
  resT_sum _ _ (fun i => (hbterm i).1), Finset.sum_congr rfl fun a _ => (hfterm a).2,
  Finset.sum_congr rfl fun i _ => (hbterm i).2, ← map_sum, ← map_sum, ← map_add]
  congr 1
  exact GlobalTheory.T.conjugateResidue_flagTerms_reindex_symmetricEdge (r_le_Y (D := D) 0) D.R.rS D.R.k hn hrn _ hU (GlobalTheory.SeeConjChar.sideAt X h PP) fF fN gB (fun a => rfl) (fun a => rfl) (fun i => rfl)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

namespace GlobalTheory.FlatStepVertex

theorem mul_reindex_gen {k : Type} [Field k] {a c b : ℕ} {ι' ι : Type} (h : a + c = b) (f : ι' ≃ ι) (g : GL (Fin b) k)
    (D : Matrix (Fin a ⊕ Fin c) ι' k) :
    g.val * D.reindex (frame h) f = ((frameGL h g).val * D).reindex (frame h) f := by
  ext i j
  simp only [reindex_apply, submatrix_apply, Matrix.mul_apply, frameGL_val]
  exact (Fintype.sum_equiv (frame h) _ _ (fun x => by simp)).symm

theorem reindex_mul_gen {k : Type} [Field k] {a c b : ℕ} {ι' ι : Type} (h : a + c = b) (f : ι' ≃ ι) (g : GL (Fin b) k)
    (D : Matrix ι' (Fin a ⊕ Fin c) k) :
    D.reindex f (frame h) * g.val = (D * (frameGL h g).val).reindex f (frame h) := by
  ext i j
  simp only [reindex_apply, submatrix_apply, Matrix.mul_apply, frameGL_val]
  exact (Fintype.sum_equiv (frame h) _ _ (fun x => by simp)).symm

end GlobalTheory.FlatStepVertex

theorem GlobalTheory.flatStep_vertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {a₀ a₁ a₂ b c c₀ c' : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure] (hc₀ : c₀ = c + 1) (hc' : c' = c + 1)
    (h₁ : a₁ + c₀ = b) (h₂ : a₁ + (c + 1) = b) (h' : a₁ + c' = b) (g : GL (Fin b) k) (κ : GL (Fin a₁) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin a₁) c', frameGL h' g = v * embX c' κ →
    ∀ (x₀ : Matrix (Fin a₁) (Fin a₀) k) (x₁ : Matrix (Fin a₂) (Fin a₁) k),
    ∃ φ₀ : (StepVar (Fin a₁) c₀ (Fin a₀) → k) ≃ᵐ (StepVar (Fin a₁) c₀ (Fin a₀) → k),
      MeasurePreserving φ₀ (stepVol ν (Fin a₁) c₀ (Fin a₀)) (stepVol ν (Fin a₁) c₀ (Fin a₀)) ∧
    ∃ φ₁ : (StepVar (Fin a₂) c (Fin a₁) → k) ≃ᵐ (StepVar (Fin a₂) c (Fin a₁) → k),
      MeasurePreserving φ₁ (stepVol ν (Fin a₂) c (Fin a₁)) (stepVol ν (Fin a₂) c (Fin a₁)) ∧
    ∀ e₀ e₁,
      (∀ {ι : Type} (f : Fin a₀ ⊕ Fin (c₀ + 1) ≃ ι), (g⁻¹).val * (stepPt x₀ e₀).reindex (frame h₁) f =
        (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)).reindex (frame h₁) f) ∧
      (∀ {ι : Type} (f : Fin a₂ ⊕ Fin c ≃ ι), (stepPt x₁ e₁).reindex f (frame h₂) * g.val =
        (stepPt (x₁ * κ.val) (φ₁ e₁)).reindex f (frame h₂)) ∧
      (ch (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)) + ch (stepPt (x₁ * κ.val) (φ₁ e₁)) + (if Even c₀ then ∑ r : Fin a₁,
          (∑ l : Fin c, if l.val = c / 2 then stepPt (x₁ * κ.val) (φ₁ e₁) (.inr l) (.inl r) else 0) *
            stepPt ((κ⁻¹).val * x₀) (φ₀ e₀) (.inl r) (.inr ⟨c₀ / 2, by omega⟩) else 0) =
        ch (stepPt x₀ e₀) + ch (stepPt x₁ e₁) + (if Even c₀ then ∑ r : Fin a₁,
          (∑ l : Fin c, if l.val = c / 2 then stepPt x₁ e₁ (.inr l) (.inl r) else 0) *
            stepPt x₀ e₀ (.inl r) (.inr ⟨c₀ / 2, by omega⟩) else 0)) ∧
      (Odd c₀ → ∀ (l : Fin c₀) (s : Fin a₀), l.val = c₀ / 2 →
        stepPt ((κ⁻¹).val * x₀) (φ₀ e₀) (.inr l) (.inl s) = stepPt x₀ e₀ (.inr l) (.inl s)) ∧
      (Odd c₀ → ∀ (r : Fin a₂) (i : Fin (c + 1)), i.val = c / 2 →
        stepPt (x₁ * κ.val) (φ₁ e₁) (.inl r) (.inr i) = stepPt x₁ e₁ (.inl r) (.inr i)) := by
  intro k _ _ _ _ _ _ a₀ a₁ a₂ b c c₀ c' ν _ hc₀ hc' h₁ h₂ h' g κ hκ v hv hg x₀ x₁
  subst hc₀ hc'
  obtain ⟨φ₀, hφ₀, H₀⟩ := GlobalTheory.T.fourierJacobiStep_leftChange_measurePreserving (n := Fin a₁) (n' := Fin a₀) (c := c + 1) ν v hv κ hκ x₀
  obtain ⟨φ₁, hφ₁, H₁⟩ := GlobalTheory.T.stepPoint_mul_periodUnipotent_GL_measurePreserving (n := Fin a₂) (n' := Fin a₁) (c := c) ν v hv κ hκ x₁
  refine ⟨φ₀, hφ₀, φ₁, hφ₁, fun e₀ e₁ => ?_⟩
  have hg₁ : frameGL h₁ g = v * embX (c + 1) κ := hg
  have hg₂ : frameGL h₂ g = v * embX (c + 1) κ := hg
  obtain ⟨A, B⟩ := GlobalTheory.T.fourierJacobiPhase_adjacentSteps_invariant_vertex (n₀ := Fin a₀) (n := Fin a₁) (n₂ := Fin a₂) (c := c) v hv κ x₀ e₀ x₁ e₁
    (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)) (stepPt (x₁ * κ.val) (φ₁ e₁)) (H₀ e₀).symm (H₁ e₁).symm
  refine ⟨fun f => ?_, fun f => ?_, A, fun ho l s hl => ?_, fun ho r i hi => ?_⟩
  · rw [GlobalTheory.FlatStepVertex.mul_reindex_gen, map_inv, hg₁, H₀]
  · rw [GlobalTheory.FlatStepVertex.reindex_mul_gen, hg₂, H₁]
  · rw [show l = ⟨(c + 1) / 2, by omega⟩ from Fin.ext hl]
    exact (B ho).1 s
  · rw [show i = ⟨c / 2, by omega⟩ from Fin.ext hi]
    exact (B ho).2 r
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.LineKillV

theorem isDatum_list_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd}
    {ψ : AddChar (AF F) ℂ} {Z : Type} {crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z}
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {ι : Type} (l : List ι) (Ψ : ι → (Fin n × Fin d → AF F) → ℂ) (f : ι → Z → ℂ)
    (h : ∀ i, IsDatum M ψ crd (Ψ i) (f i)) : IsDatum M ψ crd (l.map Ψ).sum (l.map f).sum := by
  induction l with
  | nil => simpa using (GlobalTheory.SquareAgree.CoinvPass.isDatum_zero (M := M) (ψ := ψ) (crd := crd))
  | cons a l ih => simpa [List.map_cons, List.sum_cons] using GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ (h a) ih

end GlobalTheory.LineKillV

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

noncomputable section

namespace GlobalTheory.ThetaTransformInj

theorem thO_injective : ∀ (D : D7) {n k : ℕ} (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → Mo.IsGood ψ' →
    ∀ {d : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (e : Fin k ≃ Fin d), G.det ≠ 0 →
    ∀ F₁ ∈ GlobalTheory.WeilM.schA D.host.F (Fin n × Fin k), ∀ F₂ ∈ GlobalTheory.WeilM.schA D.host.F (Fin n × Fin k),
      GlobalTheory.TripleRead.thO Mo ψ' G e F₁ = GlobalTheory.TripleRead.thO Mo ψ' G e F₂ → F₁ = F₂ := by
  intro D n k Xs Ws Mo ψ' χX χW om τ hH hG d G e hdet F₁ hF₁ F₂ hF₂ h
  obtain ⟨-, hstd, -, hdX, -, hdW, -⟩ := hH
  obtain ⟨T, hT, hTi⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Mo ψ' G e hG hstd hdX hdW hdet
  rw [← hT F₁ hF₁, ← hT F₂ hF₂, ← sub_eq_zero, ← map_sub] at h
  exact sub_eq_zero.1 (hTi _ (Submodule.sub_mem _ hF₁ hF₂) h)

end GlobalTheory.ThetaTransformInj

end
end
