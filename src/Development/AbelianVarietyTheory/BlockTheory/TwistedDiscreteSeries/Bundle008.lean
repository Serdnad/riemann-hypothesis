module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

open scoped TensorProduct Topology
open NumberField IsDedekindDomain Filter GlobalTheory.LFun

section Defs

variable {K : Type} [Field K] [NumberField K]

def liftFam (c : Fam K) (m x : HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) : Fam K :=
  _root_.GlobalTheory.LFun.twist c (x * m⁻¹) + segFam x t

def IsZetaCont (T : Set (HeightOneSpectrum (𝓞 K))) (Z : ℂ → ℂ) : Prop :=
  MeromorphicOn Z Set.univ ∧ ∀ s : ℂ, 1 < s.re → Z s = zetaOff T s

def HasSimplePole (Λ : ℂ → ℂ) (s₀ : ℂ) : Prop :=
  MeromorphicAt Λ s₀ ∧ meromorphicOrderAt Λ s₀ = ((-1 : ℤ) : WithTop ℤ) ∧
    ∃ ρ : ℂ, ρ ≠ 0 ∧ Tendsto (fun s => (s - s₀) * Λ s) (𝓝[≠] s₀) (𝓝 ρ)

end Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rhs (S : Set (HeightOneSpectrum (𝓞 F))) (c : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ)
    (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  LSTw S c m s * ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i)

def Hyp (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) : Prop :=
  S.Finite ∧ r + 5 ≤ t ∧
    ∀ w ∉ above E S, (c w).card = r ∧
      (∀ b ∈ c w, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧
      ‖(m w : ℂ)‖ = 1 ∧ ‖(x w : ℂ)‖ = 1 ∧ P w = liftFam c m x t w

def Concl (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) :
    Prop :=
  (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re →
    Converges (above E S) (_root_.GlobalTheory.LFun.twist P x⁻¹) s ∧
      (∀ i < t, Converges (above E S) (fun _ => {1}) (s + ((t : ℂ) - 1) / 2 - i)) ∧
      LSTw S P x s = rhs S c m t (zetaOff (above E S)) s) ∧
  ((∀ s : ℂ, ((r : ℝ) + 1) / 2 < s.re → Converges (above E S) (_root_.GlobalTheory.LFun.twist c m⁻¹) s ∧ LSTw S c m s ≠ 0) ∧
    DifferentiableOn ℂ (LSTw S c m) {s | ((r : ℝ) + 1) / 2 < s.re}) ∧
  (∃ Z, IsZetaCont (above E S) Z) ∧
  ∀ Z, IsZetaCont (above E S) Z →
    MeromorphicOn (rhs S c m t Z) {s | ((r : ℝ) + 1) / 2 < s.re} ∧
      ((r : ℝ) + 1) / 2 < ((1 + (t : ℂ)) / 2).re ∧
      (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re → rhs S c m t Z s = LSTw S P x s) ∧
      HasSimplePole (rhs S c m t Z) ((1 + (t : ℂ)) / 2)

def SimplePole : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ),
    Hyp S r t c P m x → Concl S r t c P m x

section Rep

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU

end Rep

theorem twist_liftFam (c : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ) :
    _root_.GlobalTheory.LFun.twist (liftFam c m x t) x⁻¹ = _root_.GlobalTheory.LFun.twist c m⁻¹ + segFam 1 t := by
  rw [liftFam, _root_.GlobalTheory.LFun.twist_add, _root_.GlobalTheory.LFun.twist_twist, _root_.GlobalTheory.LFun.twist_segFam, inv_mul_cancel_left, inv_mul_cancel]

end GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Chain

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ


open Classical in
def typePl : Finset (HeightOneSpectrum (𝓞 D.host.F)) := R.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def Differ (P : LevelP R.Pg D.R.r ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c c' : Sys D) : Prop :=
  ∃ w d Rp, Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) Sb w d Rp ∧
    c w (dualLab d) ≠ c' w (dualLab d)

variable (t : T)

variable (P : LevelP R.Pg D.R.r ℂ)

def GoodTypes : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k ∧
      (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∀ (v : D.nd.PlG k) (j : Fin D.R.m) (PP : Pl D.host.E), R.C.P.Div k PP →
        ∀ (a : ℕ) (u : (kP PP)ˣ), (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = L.gen 1 → (u : kP PP) = (a : kP PP) →
          L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
              ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
            ((R.chi ((j : ℕ) + 1) PP u : ℂˣ) : ℂ) ∨
          L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
              ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
            (((R.chi ((j : ℕ) + 1) PP u)⁻¹ : ℂˣ) : ℂ)

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Arith

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

abbrev pS : ℕ := ((Wc D i).sig (tauE D τ)).1

abbrev qS : ℕ := ((Wc D i).sig (tauE D τ)).2

abbrev eS : ℚ := (D.hc τ).e i

abbrev aP (a : ℕ) : ℕ := aPl D i (pS D i τ) τ a

abbrev aM (a : ℕ) : ℕ := aMi D i (pS D i τ) (qS D i τ) τ a

def centred (a : ℕ) : ℚ := Formalism.L2.NTheta.lamAt (D.hc τ) a + eS D i τ

def aPlusQ (a : ℕ) : ℚ := centred D i τ a - ((pS D i τ : ℚ) - ((a : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2

def dRowQ (c : ℕ) : ℚ := centred D i τ (pS D i τ + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2

def dShift : ℚ := ((pS D i τ : ℚ) - (qS D i τ : ℚ)) / 2 - eS D i τ - 1 / 2

def thetaWt (a : ℕ) : ℤ :=
  if a < pS D i τ then (aP D i τ a : ℤ)
  else if a < pS D i τ + D.R.t then 0
  else -(aM D i τ (qS D i τ - 1 - (a - (pS D i τ + D.R.t))) : ℤ)

def IsDataOf (w : IndefiniteWeightData.WeightData) : Prop :=
  w.k = D.R.k ∧ w.m = D.R.m ∧ w.t = D.R.t ∧ w.j = (i : ℕ) + 1 ∧ (w.e : ℚ) = eS D i τ ∧
    (∀ a : Fin (D.R.k - 1), (w.v (a + 2) : ℚ) = (D.hc τ).v a) ∧ ∀ a : Fin D.R.m, (w.b (a + 1) : ℚ) = (D.hc τ).b a

structure ArithAt : Prop where

  sig : pS D i τ = D.R.k + i ∧ qS D i τ = D.R.m - ((i : ℕ) + 1)

  rank : pS D i τ + qS D i τ = D.R.r ∧ (Vc D i).rank = D.R.r + D.R.t

  aP_eq_rat : ∀ a < pS D i τ, (aP D i τ a : ℚ) = aPlusQ D i τ a

  aM_eq : ∀ c < qS D i τ, (aM D i τ (qS D i τ - 1 - c) : ℚ) = -dRowQ D i τ c

  aPlus_antitone : ∀ a b, a ≤ b → b < pS D i τ → aP D i τ b ≤ aP D i τ a

  aM_anti : ∀ a b, a ≤ b → b < qS D i τ → aM D i τ b ≤ aM D i τ a

  aPlus_pos : ∀ a < pS D i τ, 1 ≤ aP D i τ a

  aM_pos : ∀ a < qS D i τ, 1 ≤ aM D i τ a

  kap_plus : ∀ a : Fin (pS D i τ),
    (Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl a) : ℚ) =
      (aP D i τ a : ℚ) + ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ

  kap_minus : ∀ c : Fin (qS D i τ),
    (Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) : ℚ) =
      -(aM D i τ (qS D i τ - 1 - c) : ℚ) - ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ

  d_int : ∃ z : ℤ, dShift D i τ = z

  lamPrime_eq : ∀ w : IndefiniteWeightData.WeightData, IsDataOf D i τ w → ∀ a < D.R.r + D.R.t,
    w.lamPrime (a + 1) = (thetaWt D i τ a : ℚ) + dShift D i τ

  coef_isLamPrime : Bridge.IsLamPrime (D := D) (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ) ((i : ℕ) + 1) τ

  coef_eq : ∀ a : Fin (Vc D i).rank,
    ((Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w a : ℚ) = (thetaWt D i τ a : ℚ) + dShift D i τ

end Arith

structure InfTypesAt {D : D7} {T : Type} (L : LevCh D T) (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) : Prop where

  mu : HasInfExp D (L.mu t ((i : ℕ) + 1)) τ (-eS D i τ)

  eta : HasInfExp D L.eta τ (1 / 2)

  chiV : HasInfExp D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 τ (-eS D i τ)

  chiW : HasInfExp D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 τ (-eS D i τ - 1 / 2)

end GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NcGapGt (S : SPar) (h : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h < |((x.1 - y.1 : ℚ) : ℝ)|

def NcGapGe (S : SPar) (h : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h ≤ |((x.1 - y.1 : ℚ) : ℝ)|

def minSig (S : SPar) : ℕ :=
  min (S.filter fun x => x.2 = true).card (S.filter fun x => x.2 = false).card

def shiftPar (c : ℚ) (S : SPar) : SPar := S.image fun x => (x.1 + c, x.2)

variable (D : D7)

def alV (i : Fin D.R.m) (τ : D.what₂.Tau) : ℚ :=
  if Odd ((i : ℕ) + 1) then -(D.hc τ).e i - 1 / 2 else -(D.hc τ).e i

def alW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℚ :=
  if Odd ((i : ℕ) + 1) then -(D.hc τ).e i else -(D.hc τ).e i - 1 / 2

def lamS (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar := shiftPar (-alW D i τ) (parA (Ptw D) i τ)

def lamT (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar := shiftPar (-alV D i τ) (parA (Ptw D) ((i : ℕ) + 1) τ)

def StepGap (i : Fin D.R.m) : Prop :=
  ∀ τ, NcGapGt (lamS D i τ) ((D.R.rankY ((i : ℕ) + 1) : ℝ) ^ 3) ∧
    NcGapGt (lamT D i τ) ((D.R.rankY ((i : ℕ) + 1) : ℝ) ^ 3) ∧
    NcGapGe (lamS D i τ) (120 * (D.R.rankY i : ℝ) * (minSig (lamS D i τ) : ℝ) ^ ((3 : ℝ) / 2))

variable {D}

def StepWeil (ψ : AddChar (AF D.host.F) ℂ) (i : Fin D.R.m) (V W : HSp D)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) : Prop :=
  ∃ χV χW : (AE D)ˣ →* Circle, IsWeilDatumO ψ V W χV χW ω ∧
    ∀ τ, HasInfExp D χV τ (alV D i τ) ∧ HasInfExp D χW τ (alW D i τ)

def VacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f

def fockOf {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) : PolF D W.rank V.rank → (WO V W → ℂ) :=
  pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f

end GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def dimQ (b : Bool) : ℕ := (lv (F.fc (R.toCx F).zs) b).dQ A.μ0

theorem dimQ_eq (b : Bool) :
    dimQ R F b = Module.finrank D.what₂.LL ((A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0)) := by
  cases b <;> rfl

theorem pos_iff (b : Bool) : (lv (F.fc (R.toCx F).zs) b).Pos ↔ 0 < dimQ R F b := Iff.rfl

theorem pos_iff_ne_bot (b : Bool) :
    (lv (F.fc (R.toCx F).zs) b).Pos ↔ (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ := by
  rw [pos_iff, dimQ_eq, pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]

end

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

section Interface

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}

def withLift (X : CxData A) (θ : ∀ j t, X.FLC j t →ₗ[ℂ] X.W j) : CxData A := { X with θ' := θ }

end Interface

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def cxPhase (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : CxData A.fam.amb :=
  withLift (R.toCx F) fun j t =>
    Tw.map (E := (R.HV j t).H) (F := (R.HW j (sg0 D A)).H) (twAt D.what₂.embLL A.v0) (ph j • R.thG j t)

theorem liftWeight_complexPoint_eq_twist (R : RealDat D A Ks) (F : Face D A) (b : Bool) (j : Fin D.R.m)
    (y : Fin (Module.finrank D.what₂.LL (R.WL F b j)) → D.what₂.LL) :
    Tw.out (s := twAt D.what₂.embLL A.v0) (E := (R.HW j (sg0 D A)).H) ((R.toCx F).w0C b j (cpt A.v0.embedding y)) =
      (R.FW j).j (sg0 D A) (∑ k, y k • R.bL F b j k) := by
  have hn : (((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)) * (((Real.sqrt (RealDat.nP F b))⁻¹ : ℝ) : ℂ) = 1 := by
    have h0 : 0 < RealDat.nP F b := by
      unfold RealDat.nP
      exact_mod_cast Nat.card_pos
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 h0).ne', Complex.ofReal_one]
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : (R.toCx F).w0C b j (cpt A.v0.embedding y) =
      ∑ k, A.v0.embedding (y k) • (R.toCx F).eW b j ((R.toCx F).bW b j A.v0 k) := by

    simp only [CxData.w0C, CxData.wC, lin, LinearMap.comp_apply, Fintype.linearCombination_apply, map_sum, map_smul]
    rfl

  rw [h1, map_sum]
  have h2 : ∀ (s : Bool) (f : Fin (Module.finrank D.what₂.LL (R.WL F b j)) → Tw s (R.HW j (sg0 D A)).H),
      Tw.out (∑ k, f k) = ∑ k, Tw.out (f k) := fun _ _ => rfl
  refine (h2 _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [map_smulₛₗ]
  show cj (twAt D.what₂.embLL A.v0) (A.v0.embedding (y k)) •
    ((((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)) • ((((Real.sqrt (RealDat.nP F b))⁻¹ : ℝ) : ℂ) •
      (R.FW j).j (sg0 D A) (R.bL F b j k))) = _
  rw [smul_smul (((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)), hn, one_smul, R.emb0, cj_cj]
  congr 1
  exact (DFunLike.congr_fun hs (y k)).symm

theorem twMap_smul {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    (s : Bool) (c : ℂ) (f : E →ₗ[ℂ] E') : Tw.map s (c • f) = cj s c • Tw.map s f := by
  ext u
  show c • f (Tw.out u) = cj s (cj s c) • f (Tw.out u)
  rw [cj_cj]

theorem cxPhase_eq (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) :
    cxPhase R F ph = withLift (R.toCx F) fun j t => cj (twAt D.what₂.embLL A.v0) (ph j) • (R.toCx F).θ' j t :=
  congrArg (withLift (R.toCx F)) (funext fun j => funext fun t => twMap_smul _ (ph j) (R.thG j t))

end GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem principalLevelCharacter_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (R.toLevCh.datWp i R.toLevCh.triv) k = 1 := by
  have h : ∀ x, Formalism.L2.DIV.ext1 (R.toLevCh.datWp i R.toLevCh.triv).P.H (R.toLevCh.datWp i R.toLevCh.triv).P.chi x = 1 :=
    fun x => subgroupCharExtension_one_apply _ x
  unfold levChi Formalism.L2.DIV.levFn
  rw [h]
  simp [LevCh.datWp, datY]

end

end GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters

end
end
