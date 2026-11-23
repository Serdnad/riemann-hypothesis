module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumConjugatePlacesLevelEqCharacters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle283
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle294
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle292
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle234
public import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle291
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaAbsU

theorem hasSum_norm_kerU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∃ α : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α ∧ HasSum (fun a : GU σ r ⧸ KU σ r => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹)) := by
  intro L _ _ _ ϖ σ q r t hU hrt z φ hz hK
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq0 : q ≠ 0 := by omega
  obtain ⟨-, -, hS⟩ := GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivial_hyp hU hq0 r
  obtain ⟨x, hx⟩ := hS.exists_vec
  have bound : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r (GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0) := by
    intro i
    have hi := i.2
    have h2 : 2 * i.val + 2 ≤ r := by omega
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hn : ‖(GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0 i : ℂ)‖ = (q : ℝ) ^ ((r : ℝ) - 1 - 2 * (i.val : ℝ)) := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam, Units.val_zpow_eq_zpow_val, norm_zpow, Units.val_mk0, Complex.norm_natCast,
        ← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    have hlow : ((q : ℝ) ^ 2) ^ (-(((r : ℝ) - 1) / 2)) = (q : ℝ) ^ (-((r : ℝ) - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
      congr 1
      push_cast
      ring
    rw [hn, hlow, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq]
    have h2' : 2 * (i.val : ℝ) + 2 ≤ r := by exact_mod_cast h2
    have h0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    constructor <;> apply Real.rpow_le_rpow_of_exponent_le hq1 <;> linarith
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0, bound, ?_⟩
  have hKψ : KerU ϖ q (r + t) 1 (fun g => ((‖φ g‖ : ℝ) : ℂ)) := by
    intro d g hg k₁ hk₁ k₂ hk₂
    simp only
    rw [hK d g hg k₁ hk₁ k₂ hk₂]
    simp [norm_zpow, hz]
  have h := GlobalTheory.T.hasSum_unramifiedZetaSum_unitary_inert L ϖ σ q r t hU hrt 1 _ (by simp) hKψ ℂ (GlobalTheory.LGrp.charRep 1) x _ hx bound LinearMap.id
    ⟨‖x‖, fun g => by simp⟩
  have hx0 : x ≠ 0 := hx.1
  have h' := h.mul_right x⁻¹
  simpa [mul_assoc, mul_inv_cancel₀ hx0] using h'

end GlobalTheory.ZetaAbsU
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KerLe {A B Z₁ Z₂ : Type} [AddCommMonoid Z₁] [AddCommMonoid Z₂] (q₁ : A → B → Z₁) (q₂ : A → B → Z₂) : Prop :=
  ∀ (n : ℕ) (a : Fin n → A) (b : Fin n → B), ∑ i, q₁ (a i) (b i) = 0 → ∑ i, q₂ (a i) (b i) = 0

def AbsIrr {G K : Type} [AddCommGroup K] [Module ℂ K] (a : G → Module.End ℂ K) : Prop :=
  (∀ N : Submodule ℂ K, (∀ g, ∀ x ∈ N, a g x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
    ∀ T : Module.End ℂ K, (∀ g, T ∘ₗ a g = a g ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id

def intersection_update_fsHerm_neg_one {ι : Type} {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (i : ι) (f : Module.End ℂ (K i)) :
    Module.End ℂ (⨂[ℂ] j, K j) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : K j →ₗ[ℂ] K j)) i f)

theorem position_tprod {ι : Type} {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (i : ι)
    (f : Module.End ℂ (K i)) (v : ∀ j, K j) :
    intersection_update_fsHerm_neg_one i f (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v i (f (v i))) := by
  unfold intersection_update_fsHerm_neg_one
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp
  · simp [hji]

section Cover

variable {p q r s : ℕ}

def AdjRule {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z) : Prop :=
  ∀ (X : Mat p q) P P' y y', ⟪B (fockAct1 p q r s X P) y, B P' y'⟫_ℂ = ⟪B P y, B (fockAct1 p q r s (adjZ X) P') y'⟫_ℂ

def InvRule (N : GKMod r s) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z) : Prop :=
  ∀ (Y : Mat r s) P y, B (fockAct2 p q r s Y P) y = B P (N.act (adjZ Y) y)


variable (p q r s) in
def UnitaryImage : Prop :=
  ∀ (Y Z : Type) [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z), AdjRule B →
    ∃ (A : UGKMod p q) (j : A.M.V →ₗ[ℂ] Z) (B' : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V),
      Function.Injective j ∧ (∀ P y, j (B' P y) = B P y) ∧ Submodule.span ℂ {x | ∃ P y, B' P y = x} = ⊤ ∧
        ∀ X P y, B' (fockAct1 p q r s X P) y = A.M.act X (B' P y)

def contr {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H) (y : V) : A ⊗[ℂ] V →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap ∘ₗ LinearMap.lTensor A (innerₛₗ ℂ (ι y) ∘ₗ ι)


variable (p q) in
def FiniteSupport {T : GrpData r s} (R : DSRep T) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (B : Pol p q r s →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] A), InvRule R.HK B →
    ∀ P, ∃ E : Submodule ℂ R.HK.V, FiniteDimensional ℂ E ∧ ∀ y, (∀ e ∈ E, ⟪R.ι y, R.ι e⟫_ℂ = 0) → B P y = 0

def TensorForm : Prop :=
  ∀ (U A V H : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι →
    (∀ t : A ⊗[ℂ] V, (∀ y, contr ι y t = 0) → t = 0) ∧
    ∀ B : U →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] A,
      (∀ P, ∃ E : Submodule ℂ V, FiniteDimensional ℂ E ∧ ∀ y, (∀ e ∈ E, ⟪ι y, ι e⟫_ℂ = 0) → B P y = 0) →
      ∃ f : U →ₗ[ℂ] A ⊗[ℂ] V, ∀ P y, contr ι y (f P) = B P y

structure IsCoverPair (N : GKMod r s) {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z) : Prop where
  skew : ∀ X ∈ upq p q, ∀ P P' y y',
    ⟪B (fockAct1 p q r s X P) y, B P' y'⟫_ℂ + ⟪B P y, B (fockAct1 p q r s X P') y'⟫_ℂ = 0
  inv : ∀ Y ∈ upq r s, ∀ P y, B (fockAct2 p q r s Y P) y + B P (N.act Y y) = 0


variable (p q) in
def CoverKer (N : GKMod r s) : Prop :=
  ∀ (Z₁ Z₂ : Type) [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z₁) (B₂ : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z₂),
    IsCoverPair N B₁ → IsCoverPair N B₂ → B₁ ≠ 0 → KerLe (fun P y => B₁ P y) fun P y => B₂ P y

end Cover

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure IsKAct (τ : D.what₂.Tau) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)) : Prop where
  der : ∀ X ∈ lieAt V τ, ∀ v : kFin M τ,
    HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (a X v : M.H τ) 0
  skew : ∀ X ∈ lieAt V τ, ∀ v w : kFin M τ, ⟪a X v, w⟫_ℂ + ⟪v, a X w⟫_ℂ = 0

def KSm : Prop := ∀ τ, kFin M τ ≤ M.sm τ

abbrev KT : Type := ⨂[ℂ] τ, kFin M τ


variable {M} in
def inclK (h : KSm M) : KT M →ₗ[ℂ] SmT M := PiTensorProduct.map fun τ => Submodule.inclusion (h τ)

def kOp (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ maxCpt M τ) : Module.End ℂ (kFin M τ) :=
  (M.rep τ k : M.H τ →ₗ[ℂ] M.H τ).restrict fun _ hv => rep_mem_kFin M τ hk hv

def sOp (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (LPol W.rank V.rank) :=
  locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) + (-((aT : ℂ) * X.trace)) • 1

def tOp (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) : Module.End ℂ (LPol W.rank V.rank) :=
  locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) + ((aS : ℂ) * Y.trace) • 1

structure IsLocPair (τ : D.what₂.Tau) (aS aT : ℚ) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ))
    {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z) :
    Prop where
  skew : ∀ X ∈ lieAt V τ, ∀ P P' y y', ⟪B (sOp M M' τ aT X P) y, B P' y'⟫_ℂ + ⟪B P y, B (sOp M M' τ aT X P') y'⟫_ℂ = 0
  inv : ∀ Y ∈ lieAt W τ, ∀ P y, B (tOp M M' τ aS Y P) y + B P (a' Y y) = 0

def LocKer (τ : D.what₂.Tau) (aS aT : ℚ) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) : Prop :=
  ∀ (Z₁ Z₂ : Type) [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z₁) (B₂ : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z₂),
    IsLocPair M M' τ aS aT a' B₁ → IsLocPair M M' τ aS aT a' B₂ → B₁ ≠ 0 →
      KerLe (fun P y => B₁ P y) fun P y => B₂ P y

def IsCuspGrow (θ : InfFam D) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  IsAutFun V φ ∧ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ IsCuspFun V φ ∧ GlobalTheory.Grow.UnifModGrowth V θ φ

def kMean (τ : D.what₂.Tau) (e : Formalism.REAL.KG (M.ε τ) → ℂ) (w : M.H τ) : M.H τ :=
  ∫ k, e k • M.σ τ (Formalism.REAL.toMK k) w ∂(Formalism.REAL.muK (M.ε τ))

def IsCoefFam {G : Type} [Group G] [TopologicalSpace G] {n : ℕ} (c : Fin n → G → ℂ) : Prop :=
  (∀ i, Continuous (c i)) ∧ ∀ (k₀ : G) (i : Fin n), ∃ d : Fin n → ℂ, ∀ k, c i (k₀ * k) = ∑ j, d j * c j k

end GlobalTheory.Chain.IoLift

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.levelDatum_conjugatePlacesLevel_eq_characters : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (h1 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤) (h2 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥) (h3 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q))) (h4 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2})) (β : Fin T.rank → Fin T.rank → D.host.E) (hβ : ∀ i, β i ∈ C.X.Λ) (hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) (Lv0 : GlobalTheory.SW.Level C.X), (∀ d : Fin T.rank → 𝓞 D.host.E, GlobalTheory.SW.Cong C.X (GlobalTheory.LiftLevel.liftI Pg Q) (∑ j, d j • β j) 0 → ∀ j, d j ∈ GlobalTheory.LiftLevel.liftI Pg Q) → ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (c : Fin S.rank → Fin T.rank → 𝓞 D.host.E), (∀ i, y i - ∑ j, c i j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) → ∀ Y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP), (∀ PP ∈ Pg ∪ Q, ∀ i j, Y PP i j = Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c i j))) → (GlobalTheory.LiftDat.mkLevel C Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0).dat hn y = omegaK Pg Y * omegaQ Q T.rank ξ (-1) Y := by
  first | exact @GlobalTheory.LiftDat.dat_mkLevel_eq | exact GlobalTheory.LiftDat.dat_mkLevel_eq | (intros; apply GlobalTheory.LiftDat.dat_mkLevel_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.conjInstanceCharacter_eq_prod_residueField_addChars : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, GlobalTheory.SeeConjChar.chiS X h c = ∏ PP ∈ Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP c) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) c) := by
  first | exact @GlobalTheory.SeeConjProd.chiS_eq_prod | exact GlobalTheory.SeeConjProd.chiS_eq_prod | (intros; apply GlobalTheory.SeeConjProd.chiS_eq_prod <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.flagPairingTable_diagonal_modSmall : ∀ {M A : Type} [Zero M] [Ring A] (p : M → M → A) (sm : A → Prop) (ρ k n : ℕ), n = 2 * ρ + k + 1 → ∀ (e f : Fin ρ → M) (b b' : Fin k → M) (z : M), PairTable p sm e f b b' z → ∀ a c : Fin n, sm (p (flagV ρ k n f e b' z a) (flagV ρ k n e f b z c) - if a = c then sgnD ρ k a else 0) := by
  first | exact @GlobalTheory.SeeConjRead.flagV_pair_table | exact GlobalTheory.SeeConjRead.flagV_pair_table | (intros; apply GlobalTheory.SeeConjRead.flagV_pair_table <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.standard_frame_integrality_conditions : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (J U W : Matrix (Fin n) (Fin n) (EAf D)) (Q : Pl D.host.E) (d : Fin n → EAf D), (∀ i j, (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * U) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * W) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ a, Valued.v (GlobalTheory.StdFrames.cpt Q (d a)) = 1) → (∀ a b, SmallAt Q ((Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a b - if a = b then d a else 0)) → Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * W).det) = 1 := by
  first | exact @GlobalTheory.SeeConjRead.DetUnit.det_unit | exact GlobalTheory.SeeConjRead.DetUnit.det_unit | (intros; apply GlobalTheory.SeeConjRead.DetUnit.det_unit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem hT_eq_hY {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (x y : Fin (Yc D 0).rank → EAf D) : hT X h x y = hY D x y := by
  rcases X with ⟨⟨I⟩⟩
  dsimp only at h ⊢
  subst h
  rfl

theorem hY_pair_flag_int {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (PP : Pl D.host.E) (a c : Fin (Yc D 0).rank) :
    hY D (pairAt X h PP a) (flagAt X h PP c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨β₀, h₀⟩ := GlobalTheory.StdFrames.exists_base (Yc D 0)
  have hU := GlobalTheory.StdFrames.unimod_of_isSD (GlobalTheory.StdFrames.isSD_one h₀)
  have hF : ∀ i j, ((β₀⁻¹).val * colMat (flagAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ ((β₀⁻¹).val * colMat (pairAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    have hF : Formalism.L2.DIV.IsFrame β₀ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := h₀ ▸ GlobalTheory.StdFrames.isFrame_lat β₀
    have hLf := GlobalTheory.KgFrame.Lf_eq D
    have key : ∀ v : Fin (Yc D 0).rank → EAf D, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf →
        Matrix.mulVec (β₀⁻¹).val v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro v hv
      rw [hLf] at hv
      exact (hF v).1 hv i
    set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf}
    have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
      show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
      exact zero_mem _
    obtain ⟨hef, hz, hbw⟩ := X.vectorsInLattice
    have he : ∀ a, e0T X h a ∈ S := cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
    have hf : ∀ a, f0T X h a ∈ S := cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
    have hb : ∀ a, bwT X h a ∈ S := cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
    have hbd : ∀ a, bwdT X h a ∈ S := cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
    have hzz : z0T X h ∈ S := cast_mem_Lf h X.z0 hz
    refine ⟨?_, ?_⟩
    · rw [colMat_entry]
      apply key
      unfold flagAt
      split_ifs
      · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf hb hzz j
      · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf (fun a => hbd _) hzz j
    · rw [colMat_entry]
      apply key
      unfold pairAt
      split_ifs
      · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz j
      · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun a => hb _) hzz j
  set U := colMat (pairAt X h PP) with hUdef
  set W := colMat (flagAt X h PP) with hWdef
  set J := GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram with hJ
  have e1 : hY D (pairAt X h PP a) (flagAt X h PP c) = (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a c := by
    simp only [Matrix.mul_apply, Formalism.UG.hform, Formalism.UG.cT, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply, hY]
    rw [Finset.sum_comm]
    rfl
  set A' := (β₀⁻¹).val * U with hAdef
  set B' := (β₀⁻¹).val * W with hBdef
  set G' := Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val with hGdef
  have hU' : U = β₀.val * A' := by rw [hAdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hW' : W = β₀.val * B' := by rw [hBdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hX' : Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W = Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A' * G' * B' := by
    rw [hGdef, hU', hW', GlobalTheory.StdFrames.cT_mul']
    simp only [Matrix.mul_assoc]
  rw [e1, hX']
  simp only [Matrix.mul_apply]
  refine sum_mem fun j _ => mul_mem (sum_mem fun i _ => mul_mem ?_ ?_) ?_
  · exact Formalism.UG.P.csDual_sig_mem _ (hF i a).2
  · exact hU.1 i j
  · exact (hF j c).1

end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem resT_hT_pair_flag : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → ∀ PP ∈ R.Pg, ∀ a c : Fin (Yc D 0).rank, GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) (flagAt X h PP c)) = if a = c then sgnD D.R.rS D.R.k a else 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R X h hL PP hPP a c
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    obtain ⟨l, hl⟩ := (hL.Pg PP).1 hPP
    have := R.C.P.overP hl
    rw [Nat.cast_mul]
    fin_cases l
    · exact PP.asIdeal.mul_mem_right _ this
    · exact PP.asIdeal.mul_mem_left _ this
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    have e := X.n_eq
    rw [h] at e
    have e2 := Formalism.L2.DIV.ranks_r_sym D
    change (Formalism.L2.SG.InstExistsPf.instOf D).n = _
    omega
  have hsm : SmallAt PP (hY D (pairAt X h PP a) (flagAt X h PP c) - if a = c then sgnD D.R.rS D.R.k a else 0) := by
    by_cases he : GlobalTheory.StdFrames.cpt PP (ewT X h) = 1
    · unfold pairAt flagAt
      rw [if_pos he, if_pos he]
      exact flagV_pair_table (hY D) (SmallAt PP) _ _ _ hn _ _ _ _ _ (pairTable_of_cpt_one X h PP hg he) a c
    · unfold pairAt flagAt
      rw [if_neg he, if_neg he]
      exact flagV_pair_table (hY D) (SmallAt PP) _ _ _ hn _ _ _ _ _ (pairTable_rev X h PP hg he) a c
  have hint := hY_pair_flag_int X h PP a c
  have hs : (if a = c then sgnD D.R.rS D.R.k a else 0 : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    unfold sgnD
    split_ifs
    exacts [neg_mem (one_mem _), one_mem _, zero_mem _]
  have key : Formalism.L2.DIV.resS D.host.F PP ⟨_, hint⟩ - Formalism.L2.DIV.resS D.host.F PP ⟨_, hs⟩ = 0 := by
    rw [← map_sub]
    exact (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).2 hsm
  have hres : Formalism.L2.DIV.resS D.host.F PP ⟨_, hs⟩ = if a = c then sgnD D.R.rS D.R.k a else 0 := by
    by_cases hac : a = c
    · subst hac
      by_cases hz : a.1 = D.R.rS + D.R.k
      · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = -1 := Subtype.ext (by simp [sgnD, hz])
        rw [e, map_neg, map_one]
        simp [sgnD, hz]
      · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 := Subtype.ext (by simp [sgnD, hz])
        rw [e, map_one]
        simp [sgnD, hz]
    · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 0 := Subtype.ext (by simp [hac])
      rw [e, map_zero]
      simp [hac]
  unfold resT
  rw [hT_eq_hY, dite_eq_left hint, ← hres]
  exact sub_eq_zero.1 key

end GlobalTheory.SeeConjChar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.conjugateResidue_flagTerms_reindex_symmetricEdge : ∀ {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (ρ k : ℕ), n = 2 * ρ + k + 1 → r = n → ∀ U : GL (Fin n) κ, upperLeftBlock hr U ∈ unip κ r → ∀ (s : Bool) (fF fN : Fin ρ → Fin n) (gB : Fin k → Fin n), (∀ a, (fF a).1 = 2 * ρ + k - a.1) → (∀ a, (fN a).1 = if a.1 + 1 < ρ then 2 * ρ + k - (a.1 + 1) else ρ + k) → (∀ i, (gB i).1 = ρ + k - 1 - i.1) → (∑ a, (sgnD ρ k (fN a) : κ) * (U⁻¹).val (fN a) (fF a)) + (∑ i : Fin k, if hi : i.1 + 1 < k then (if s then 0 else (sgnD ρ k (gB ⟨i.1 + 1, hi⟩) : κ) * (U⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) = ∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then ((GlobalTheory.SeeConjChar.wB ρ k s i j : ℤ) : κ) * (upperLeftBlock hr U).val i j else 0 := by
  first | exact @GlobalTheory.SeeConjComb.conj_residue_reindex | exact GlobalTheory.SeeConjComb.conj_residue_reindex | (intros; apply GlobalTheory.SeeConjComb.conj_residue_reindex <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix


theorem _root_.GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), IsFrame β Λ → ∀ PP : Pl E, (∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ w ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP (v + w) = redV β PP v + redV β PP w) ∧ (∀ (c : Formalism.L2.Herm.intAf F E), ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) = resS F PP c • redV β PP v) ∧ (∀ M ∈ St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) = ((redFn β PP M : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) *ᵥ redV β PP v) := by
  exact @GlobalTheory.SeeConjGroup.redV_add_smul_stab
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.residue_otherInstanceForm_frameStabilizer_mulVec : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D), RedIs β PP w → ∀ N ∈ St β, ∀ y : Fin (Yc D 0).rank → EAf D, (∀ z : Fin (Yc D 0).rank → EAf D, (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h y z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ j, GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j))) = ∑ l, GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (w l)) * (redFn β PP N).val l j := by
  first | exact @GlobalTheory.SeeConjChar.resT_hT_mulVec_stab | exact GlobalTheory.SeeConjChar.resT_hT_mulVec_stab | (intros; apply GlobalTheory.SeeConjChar.resT_hT_mulVec_stab <;> assumption)
end
