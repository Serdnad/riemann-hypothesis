module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.TestLat

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Numbers

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T)
  {K K' : Type} [Field K] [Field K']

def BottomsWith (Q : ℂ → Prop) : Prop :=
  ∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
    IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P' ∧ Q (P.norm : ℂ) ∧ Q (P'.norm : ℂ)

structure SqIn (σ : K →+* ℂ) : Prop where

  norms : BottomsWith G μ₀ (fun _ => True) → BottomsWith G μ₀ fun z => z ∈ Set.range σ

  toric : ∀ (i j : Fin D.R.m) (s : ℕ) (c : Bool) (x y : ℂ), 1 ≤ s → s ≤ halfRank D i j → IsTor G i j s (nuH G μ₀ i j) x →
    IsTor G i j s (nuH G μ₀ i j * delOf Lc c) y → y / x ∈ Set.range σ

variable {G μ₀}

theorem SqIn.mono {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : SqIn G μ₀ σ) (hσ : Set.range σ ⊆ Set.range σ') : SqIn G μ₀ σ' :=
  ⟨fun a => let ⟨δ, t0, b⟩ := h.norms a
    ⟨δ, t0, fun ij => let ⟨P, P', c⟩ := b ij; ⟨P, P', c.1, hσ c.2.1, hσ c.2.2⟩⟩,
    fun i j s c x y a b d e => hσ (h.toric i j s c x y a b d e)⟩

end Numbers

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure SlopeTestRemainingChoices (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) (W : G.Weil) (n : ℕ) where

  M : Vol G

  ρ : G.RealVec

  ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W

  cv : ChainVec p.R.toRealDat

  rm : RealMatch W

  S : SumChoice W Set.univ

  rp : ClassReps G

  e : Fin n ≃ TestIx G × VVIdx (LaP G)

  c : Fin D.R.m → Fin D.R.m → p.P.T → ℂ

def SlopeTestRemainingChoices.ch {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) : Choice p.R.toRealDat :=
  ⟨⟨1, CF, p.Z.b⟩, G, W, a.M, a.ρ, a.ξ, a.cv, a.rm, a.S, a.rp, n, a.e, a.c⟩

theorem SlopeTestRemainingChoices.atScale {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) :
    a.ch.AtScale CF p.Z.b := rfl

structure SlopeTestRemainingChoices.OK {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) : Prop where

  is : a.ch.Is

  eser : GlobalTheory.GLq.ESerTie D

  field : a.ch.FieldOK

  sq : SqIn G p.P.A3.A.μ0 D.what₂.embLL

def Fld : FldT := fun p _ G W => ∃ (n : ℕ) (a : SlopeTestRemainingChoices p G W n), a.OK

end GlobalTheory.BigTop.Fun

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic

namespace GlobalTheory.Discrepancy

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

abbrev fnPull (s : Y ⟶ X) [IsDominant s] : X.functionFieldˣ →* Y.functionFieldˣ :=
  Units.map (functionFieldMap s).toMonoidHom

def pullCart (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X) : CartierDiv Y :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose

theorem isEqn_pullCart (s : Y ⟶ X) [IsDominant s] {D : CartierDiv X} {y : Y} {g : X.functionFieldˣ}
    (h : D.IsEqn (s y) g) : (pullCart s D).IsEqn y (fnPull s g) :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose_spec.2 y g h

theorem toPic_pullCart (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X) :
    toPic (pullCart s D) = CechPic.pull s (toPic D) :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose_spec.1

theorem pullCart_add (s : Y ⟶ X) [IsDominant s] (D E : CartierDiv X) :
    pullCart s (D + E) = pullCart s D + pullCart s E :=
  CartierDiv.ext_of_isEqn fun y =>
    have ⟨g, hg⟩ := D.exists_isEqn (s y)
    have ⟨g', hg'⟩ := E.exists_isEqn (s y)
    ⟨_, isEqn_pullCart s (hg.add hg'),
      (map_mul (fnPull s) g g').symm ▸ (isEqn_pullCart s hg).add (isEqn_pullCart s hg')⟩

def pullCartHom (s : Y ⟶ X) [IsDominant s] : CartierDiv X →+ CartierDiv Y :=
  AddMonoidHom.mk' (pullCart s) (pullCart_add s)

variable {k : Type} [Field k]

def DivOver.Over {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] (E' : DivOver (s ≫ p)) (E : DivOver p) :
    Prop :=
  ∀ f, f ∈ E.ring ↔ functionFieldMap s f ∈ E'.ring

structure IsLogRes (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X)
    (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) : Prop where

  smooth : SmoothOfRelativeDimension n (s ≫ p)

  proj : IsProjOver (s ≫ p)

  bir : Function.Bijective (functionFieldMap s)

  div : IsDivOfForm K (EtaleKlt.ratPull p s n η)

  snc : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)

  supp : (pullCart s G - m • K).supp ≤ B

structure IsLogMult (p : X ⟶ Sp k) (n : ℕ) (Δ : X → ℚ) (η : RatForms p n) (m : ℕ)
    (G : CartierDiv X) : Prop where

  ne_zero : η ≠ 0

  pos : 0 < m

  eqn : ∀ x g, G.IsEqn x g → IsLogEqn p Δ η x m g

theorem IsLogCanonicalMultiple.exists_isLogMult {p : X ⟶ Sp k} {n : ℕ} {Δ : X → ℚ} {m : ℕ}
    {G : CartierDiv X} (h : IsLogCanonicalMultiple p n Δ m G) (hm : 0 < m) :
    ∃ η, IsLogMult p n Δ η m G :=
  have ⟨η, h₁, h₂⟩ := h; ⟨η, h₁, hm, h₂⟩

def InMultAt (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (x : X)
    (u : X.functionFieldˣ) : Prop :=
  ∀ g, G.IsEqn x g → ∀ E : DivOver p, E.Through x → -1 < (E.ord u : ℚ) + discrep E η m g

def IsMultIdeal (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X)
    (J : X.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔
    ∀ (x : X) (hx : x ∈ U.1) (u : X.functionFieldˣ),
      (u : X.functionField) = fnOf U.1 (gen_mem hx) f → InMultAt p n η m G x u

structure IsSncChart [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) (B : Closeds Y) (y : Y)
    (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
    (u : Fin n → Y.functionFieldˣ) : Prop where

  frame : IsFrame (dOn q z)

  val : ∀ j ∈ J, (u j : Y.functionField) = fnOf U (gen_mem hy) (z j)

  spec : ∀ j ∈ J, w j ⤳ y

  coheight : ∀ j ∈ J, Order.coheight (w j) = 1

  inj : Set.InjOn w J

  ord_self : ∀ j ∈ J, Scheme.ord (u j : Y.functionField) (w j) = 1

  ord_other : ∀ j ∈ J, ∀ v, v ⤳ y → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0

  mem : ∀ v, v ⤳ y → Order.coheight v = 1 → (v ∈ B ↔ ∃ j ∈ J, v = w j)

end GlobalTheory.Discrepancy
end
end
