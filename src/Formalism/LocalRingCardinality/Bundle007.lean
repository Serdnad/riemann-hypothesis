module

public import Formalism.LocalRingCardinality.Bundle005
public import Formalism.LocalRingCardinality.Bundle006
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Formalism.LocalRingCardinality.DataForced
public import Formalism.LocalRingCardinality.Bundle003
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.BasicNotions.DV

open Formalism.BasicNotions

def logHook (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, Real.log (Real.Gamma (a i + n - i))) -
    ∑ i ∈ Finset.range n, ∑ l ∈ Finset.Ioo i n, Real.log (a i - a l + l - i)

def Lprime (D : D7) (L : SizeData₂ D) : ℝ :=
  Real.log (L.sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

def L6lo (D : D7) (L : SizeData₂ D) (C : ℝ) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, logHook (D.R.sigW j).1 (aPlus D j ρ)) -
    C * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lprime D L

def kernelPlaceMeanBound (D : D7) (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, kerPlace D L u j ρ) +
    C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L

def hExpl6 (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (u : D.what₂.Word) : ℝ :=
  SZbP D L C u + (∑ j ∈ SizeData₂.lifts D, kernelPlaceMeanBound D L C u j) - (∑ j ∈ SizeData₂.lifts D, L6lo D L C j) -
    meanE D (fun e => Real.log (X.kapR e))

end Formalism.BasicNotions.DV

end
end

section

namespace Formalism.BasicNotions

theorem ParamsT.nV_eq {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    D.R.nV = T.TO * T.nWn + (8 * D.R.f * D.R.r + 4) := by
  have h1 := T.split
  have h2 := T.nP_eq
  unfold Ranks.nV
  omega

theorem ParamsT.nV_ge {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    8 * D.R.f * D.R.r + 4 ≤ D.R.nV := by
  rw [T.nV_eq]; exact Nat.le_add_left _ _

end Formalism.BasicNotions
end

section

open Formalism.MainNotions.G NumberField

noncomputable section

namespace Formalism.BasicNotions

structure TwForms (D : D7) where
  A : ∀ u μ, ColumnsAtT D.R (D.chTw u μ)
  A_T : ∀ u μ, (A u μ).T = (D.mem u).A.T
  fm : ∀ u μ, MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) (D.chTw u μ) (A u μ) (D.PTw u μ)

  e0 : ∀ u μ, ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] ((fm u μ).lat 0).V
  twist_preserves_base_lattice : ∀ u μ (x : ((D.fm u).lat 0).V), x ∈ ((D.fm u).lat 0).L ↔ e0 u μ x ∈ ((fm u μ).lat 0).L
  embed_mul_block_embedding : ∀ u μ (x : ((D.fm u).lat 0).V), (fm u μ).emb 0 (e0 u μ x) = D.e0Tw u μ ((D.fm u).emb 0 x)

  eMu0 : ∀ u j, j ≤ D.R.m → (((D.fm u).lat j).V ≃ₗ[D.what₂.LL] ((fm u D.what₂.mu0).lat j).V)
  eMu0_lat : ∀ u j (hj : j ≤ D.R.m) (x : ((D.fm u).lat j).V),
    x ∈ ((D.fm u).lat j).L ↔ eMu0 u j hj x ∈ ((fm u D.what₂.mu0).lat j).L
  eMu0_emb : ∀ u j (hj : j ≤ D.R.m) (x : ((D.fm u).lat j).V),
    HEq ((fm u D.what₂.mu0).emb j (eMu0 u j hj x)) ((D.fm u).emb j x)

structure LocalToGlobal₂ (D : D7) (Gt : GatTies D) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    [Fact (D.what₂.places.resChar w).Prime]
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (Ch : Chain Lv) where

  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m

  lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]

  iK : (D.gat u w h).Kf →+* ℂ_[D.what₂.places.resChar w]
  iLL_lam : ∀ (x : D.what₂.LL) (hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ),
    iK (c.embW u w h x) = lam ⟨D.what₂.embLL x, hx⟩

  iw : ∀ j (v : Fin (Fl.Pj j).nV), D.host.E →+* (Fl.Pj j).Qq v

  glob : ∀ j, Lv.comp j → (Fl.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((Fl.Pj j).m + 1) → D.host.E)

  glob_loc : ∀ j, j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L → ∀ v,
    L v = Submodule.span ((Fl.Pj j).W v) {y | ∃ x ∈ glob j a L, y = fun i => iw j v (x i)}

  cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u (D.what₂.muAt w)).cls j

  cls_iff : ∀ j, j ≤ D.R.m → ∀ (a a' : Lv.comp j) (L L' : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    (Fl.Pj j).IsLatTup L' →
    (cls j a L = cls j a' L' ↔ a = a' ∧ ∃ γ : (Lv.lev j a).Γ, L' = (Lv.lev j a).smul γ L)
  cls_surj : ∀ j, j ≤ D.R.m → ∀ x : (D.chTw u (D.what₂.muAt w)).cls j, ∃ a L, (Fl.Pj j).IsLatTup L ∧ cls j a L = x

  Th : ∀ j, Lv.comp j × (Fl.Pj j).Tup → Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup →
    MvPowerSeries (D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w]

  cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j
  cmp_inj : ∀ j, j ≤ D.R.m → Function.Injective (cmp j)

  cmp_zero : ∀ x : ((D.fm u).lat 0).V, cmp 0 (Tw.e0 u (D.what₂.muAt w) x) = c.cmp u w h x

  cmp_int : Submodule.span (D.gat u w h).O
    (cmp 0 '' (((Tw.fm u (D.what₂.muAt w)).lat 0).L : Set ((Tw.fm u (D.what₂.muAt w)).lat 0).V)) = Lv.Int 0

  cmp_K : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (y : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V),
    (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y = (D.chTw u (D.what₂.muAt w)).K j ((Tw.fm u (D.what₂.muAt w)).emb j x) →
    cmp (j + 1) y = Ch.Kz j (cmp j x)

end Formalism.BasicNotions
end
end

section

noncomputable section

namespace Formalism.BasicNotions

open Formalism.FrobeniusOrbits Formalism.MainNotions.G NumberField IsDedekindDomain
open scoped BigOperators

structure ErrC where
  c6 : ℝ
  dig : ℝ
  g : ℝ

def ErrC.Large (c : ErrC) : Prop := 12 ≤ c.c6 ∧ 3 ≤ c.dig ∧ 10 ≤ c.g

structure ErrX (D : D7) where

  piG : Fin 2 → 𝓞 D.host.E
  piG_K : ∀ i, ((piG i : 𝓞 D.host.E) : D.host.E) ∈ D.host.K
  piG_norm : ∀ i, ((piG i : 𝓞 D.host.E) : D.host.E) * D.host.conj (piG i : D.host.E) = (D.host.g i : D.host.E)

  piT : D.what₂.Word → 𝓞 D.host.E
  piT_K : ∀ u, ((piT u : 𝓞 D.host.E) : D.host.E) ∈ D.host.K
  piT_norm : ∀ u, ((piT u : 𝓞 D.host.E) : D.host.E) * D.host.conj (piT u : D.host.E) = ((D.mem u).A.T : D.host.E)
  piT_cong : ∀ u, (piT u - 1) ∈
    Ideal.span {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)}

  vPl : ∀ u, (D.mem u).A.vT → HeightOneSpectrum (𝓞 D.host.F)
  vPl_inj : ∀ u, Function.Injective (vPl u)
  norm_mem_place_ideal : ∀ u v, ((D.mem u).A.T : 𝓞 D.host.F) ∈ (vPl u v).asIdeal

def tauLL (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.LL :=
  D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)


open scoped TensorProduct in
def PiGLevel (D : D7) (lev : LevelData D) (X : ErrX D) : Prop :=
  letI := D.host.cmStar
  ∀ u (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal),
    Valued.v (((lev u).splitG i v h) ((D.host.conj (X.piG i : D.host.E)) ⊗ₜ[D.host.F] (1 : v.adicCompletion D.host.F))).1 < 1


open scoped TensorProduct in
def PiTLevel (D : D7) (lev : LevelData D) (X : ErrX D) : Prop :=
  letI := D.host.cmStar
  ∀ u (v : (D.mem u).A.vT) (z : intV D.host.E (X.vPl u v)),
    (z : D.host.E ⊗[D.host.F] (X.vPl u v).adicCompletion D.host.F) =
      ((X.piT u : 𝓞 D.host.E) : D.host.E) ⊗ₜ[D.host.F] (1 : (X.vPl u v).adicCompletion D.host.F) →
    ∀ y : (lev u).fM (X.vPl u v) (X.norm_mem_place_ideal u v), z • y = 0


def SeenDef (D : D7) (X : ErrX D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ((D.fm u).seenP w = true ↔ ∀ τ : D.what₂.Tau, (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D τ (X.piT u : D.host.E)))

def TauOfDef (D : D7) (X : ErrX D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ (v : (D.mem u).A.vT) (x : 𝓞 D.host.F),
    x ∈ (X.vPl u v).asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D ((D.fm u).tauOf w v) (algebraMap D.host.F D.host.E (x : D.host.F)))

def GamMult (D : D7) (n : ℕ) : Prop :=
  ∀ u μ i, i ≤ D.R.m → ∀ c : (D.chTw u μ).cls i, Nat.card ((D.chTw u μ).stab i c) ∣ n

def DGamDef (D : D7) : Prop :=
  ∀ u μ, GamMult D (D.chTw u μ).DGam ∧ (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam

theorem DGamDef.one {D : D7} (h : DGamDef D) (u u' : D.what₂.Word) (μ : D.what₂.Tup) :
    (D.chTw u' μ).DGam = (D.mem u).C.DGam := by
  rw [← D.memberColumns_twistedChain_base u]
  exact (h u' μ).2.trans (h u D.what₂.mu0).2.symm

def nuAbs (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  ∑ i ∈ Finset.range (D.R.N (j - 1)), DV.nuRow D u j τ i

def tauPib {D : D7} (X : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) : D.what₂.LL :=
  tauLL D τ (D.host.conj (X.piG i : D.host.E))

def vNN {D : D7} (X : ErrX D) (i : Fin 2) (u : D.what₂.Word) (j : ℕ) (w : D.what₂.places.Pl) : ℝ :=
  (∑ τ : D.what₂.Tau, nuAbs D u j τ * (vAdd (D.plEq w) (tauPib X i τ) : ℝ)) / (D.what₂.places.ramIdx w : ℝ)

def EatG {D : D7} (L : SizeData₂ D) (X : ErrX D) (c : ErrC) (i : Fin 2) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) : ℝ :=
  FTypeG D j + vNN X i u j w +
    c.g * (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz)


open Classical in
def Wtau (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℕ :=
  (Finset.range (D.R.m + 1)).sup fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else (((D.fm u).lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs

def EatT (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ℝ :=
  if (D.fm u).seenP w then
    2 * (∑ τ : D.what₂.Tau, (Wtau D u τ : ℝ)) + (D.R.f : ℝ) * Nm D +
      ((topsOf D.host D.eTau).card : ℝ) * ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) / 4
  else 0


open Classical in
def ctD (D : D7) (u : D.what₂.Word) (j : ℕ) (t : HH D) : ℝ :=
  nuAbs D u j (tauPl D (false, t)) -
    (if t ∈ D.host.TT then DV.nuRow D u j (tauPl D (false, t)) 0 - DV.nuRow D u j (tauPl D (false, t)) 1 else 0) +
    (if t ∈ D.host.TT then DV.nuRow D u j (tauPl D (true, t)) 0 else 0)

def EatD (D : D7) (j : ℕ) : ℝ :=
  FRamD D j + (Finset.univ.sup' ⟨D.u₀, Finset.mem_univ _⟩ fun u : D.what₂.Word => ∑ t : HH D, ctD D u j t) / 2

def exch (D : D7) : ℝ := (D.R.f : ℝ) * D.R.k * Nm D

def EatC {D : D7} (L : SizeData₂ D) (c : ErrC) (j p : ℕ) : ℝ :=
  c.dig * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a +
    (∑ τ : D.what₂.Tau, wj D j τ) / ((p : ℝ) ^ 2 - 1)


open Classical in
def kindA (D : D7) (p : ℕ) : Finset (Bool × HH D) := Finset.univ.filter fun z => ¬ IsSg D p ∧ z.1 = false


open Classical in
def kindBC (D : D7) (p : ℕ) : Finset (Bool × HH D) := Finset.univ.filter fun z => IsSg D p ∨ z.1 = true


open Classical in
def topsBC (D : D7) (p : ℕ) : Finset (Bool × HH D) := (kindBC D p).filter fun z => IsTopPl D z


open Classical in
def EatX {D : D7} (L : SizeData₂ D) (c : ErrC) (j p : ℕ) : ℝ :=
  if IsCs D p then
    ((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ) ^ 3 +
      c.c6 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a
  else 0

theorem EatX_of_not {D : D7} (L : SizeData₂ D) (c : ErrC) (j : ℕ) {p : ℕ} (h : ¬ IsCs D p) : EatX L c j p = 0 := if_neg h

def EatI {D : D7} (L : SizeData₂ D) (K : Consts) (c : ErrC) (j p : ℕ) : ℝ :=
  max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ)) +
    gam p * ((topsBC D p).card : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
    c.c6 * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ) +
    ((kindBC D p).card : ℝ) * (D.R.N (j - 1) : ℝ) * (D.R.N j : ℝ) *
      (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
    (K.dl1 * ((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
      K.dl2 * ((topsBC D p).card : ℝ) * Real.logb p (2 * L.sc.a) ^ 2) +
    EatX L c j p


open Classical in
def Eval {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) : ℝ :=
  let p := D.what₂.places.resChar w
  if p = (D.mem u).A.T then EatT D u w else
  (padicValNat p (D.mem u).C.DGam : ℝ) +
    (if p = D.host.g 0 then EatG L X c 0 u j w
     else if p = D.host.g 1 then EatG L X c 1 u j w
     else if D.host.cls p = PrimeClass.ramD then EatD D j
     else if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then
       (if IsResidueClassZero D p ∧ hP D p = 0 then EatC L c j p else EatI L K c j p)
     else 0)

def SizeData₂.EDef {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D, ∀ w, L.E u j w = Eval L X K c u j w

theorem Eval_above {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) (hX : L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ))
    (hT : D.what₂.places.resChar w ≠ (D.mem u).A.T)
    (hg : D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ))
    (hd : D.what₂.places.resChar w ≠ D.host.d) (hG : ¬ D.what₂.places.resChar w ∣ (D.mem u).C.DGam) :
    Eval L X K c u j w = 0 := by
  have h0 : D.what₂.places.resChar w ≠ D.host.g 0 := fun h => hg (by simp [h])
  have h1 : D.what₂.places.resChar w ≠ D.host.g 1 := fun h => hg (by simp [h])
  have h2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := fun h => hd (cls_ramD h)
  have h3 : ¬ ((IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
      (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n) := fun h => absurd h.2 (not_le.2 hX)
  unfold Eval
  simp only [if_neg h0, if_neg h1, if_neg hT, if_neg h2, if_neg h3]
  simp
  rw [Nat.padicValNat_def]
  exact multiplicity_eq_zero_of_not_dvd hG

theorem SizeData₂.EDef.zeroAbove {D : D7} {L : SizeData₂ D} {X : ErrX D} {K : Consts} {c : ErrC} (h : L.EDef X K c)
    (u : D.what₂.Word) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (w : D.what₂.places.Pl)
    (hX : L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)) (hT : D.what₂.places.resChar w ≠ (D.mem u).A.T)
    (hg : D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ))
    (hd : D.what₂.places.resChar w ≠ D.host.d) (hG : ¬ D.what₂.places.resChar w ∣ (D.mem u).C.DGam) :
    L.E u j w = 0 := by
  rw [h u j hj w]; exact Eval_above L X K c u j w hX hT hg hd hG

structure ErrDefs (D : D7) (L : SizeData₂ D) (X : ErrX D) (lev : LevelData D) (K : Consts) (c : ErrC) : Prop where
  large : c.Large
  piG_lev : PiGLevel D lev X
  piT_lev : PiTLevel D lev X
  seen : SeenDef D X
  tauOf : TauOfDef D X
  dgam : DGamDef D
  edef : L.EDef X K c

end Formalism.BasicNotions

end
end
