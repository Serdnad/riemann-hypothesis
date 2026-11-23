module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StdEx' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ), IsStdChar (I.rec7 l Z) ψ (-1) →
    ∀ L : ∀ j, Lat ((I.rec7 l Z).sp.X j), (∀ j, j ≤ B.R.m → ∀ z, z ∈ L j ↔ z ∈ intVec (I.rec7 l Z) _) →
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
      (p : ι → SplitPt (I.rec7 l Z) k) (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle)
      (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
      (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)),
      Places p J (fun x => ∃ i, x = (p i).v) ∧ (∀ i, HasConductor (χ i) 1 ∧ (p i).IsChar ψ (χ i)) ∧ resCard k = B.T u ∧
      (∀ i, valuation k ((p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (X.piT u : B.fields.E)))) =
          valuation k ((q.1 : 𝒪[k]) : k) ∧
        valuation k ((p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E)))) = 1) ∧
      (∀ x : Pl (I.rec7 l Z), (∃ i, x = (p i).v) ↔ ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ x.asIdeal) ∧
      (∀ j i, (β j i).b = 1) ∧ StdT I l Z u p β Q L

def TwLev' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) k) (β : ∀ j i, Frame (p i) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank)) (L : ∀ j, Lat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ j, j ≤ B.R.m → ∀ b,
      (∀ i g, g • Q j i = Q j i → ∃ h : (β j i).gl g ∈ A.U j b, A.chi j b ⟨_, h⟩ = 1) ∧
      ∀ κ ∈ A.U j b, ∃ g : ι → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ i, g i • Q j i = Q j i) ∧
        ∃ κ' ∈ grpOff ((I.rec7 l Z).sp.X j) (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β j i).gl (g i)).prod * κ'

def TwRam' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) k) (β : ∀ j i, Frame (p i) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank)) (L : ∀ j, Lat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y, IsContAut _ (A.rd θ j hj b φ y)) ∧ (RamT (I := I) (l := l) (u := u) (a := a) j φ ↔ ∀ b y i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y))

def TwTrans' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∃ φ' ∈ (I.fm l u a).Fi j, ∀ b y, A.rd θ j hj b φ' y = trc c (A.rd θ j hj b φ y)

def TwS' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) k) (β : ∀ j i, Frame (p i) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank)) (L : ∀ j, Lat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j)),
    StdT I l Z u p β Q L → ∀ (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1),
    ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → ColT I l u a j → ColT I l u a j, ∀ j (hj : j ≤ B.R.m) φ, RamT (I := I) (l := l) (u := u) (a := a) j φ →
      (∀ b y, IsContAut _ (A.rd θ j hj b φ y) ∧ ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y)) ∧
      ∀ η, RamT (I := I) (l := l) (u := u) (a := a) j (S j η φ) ∧ ∀ b y, A.rd θ j hj b (S j η φ) y =
        J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y)

def TwVec' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ ψ θ x vac c₀, PinX I l Z ψ θ x vac c₀ →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)),
    StdT I l Z u p β Q (fun j => (x j).L) → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) α γ (cT : WO _ _ →₀ ℂ),
      Reps ψ (β j) (β (j + 1)) (x j).L (x (j + 1)).L (fun i => phiOne (Q j i) (Q (j + 1) i)) J (fun v => ∃ i, v = (p i).v) cT →
      ∀ e : AE (I.rec7 l Z), IsIdemSum e ((B.primes X).vT u) →
        IsRatDatum ψ _ _ e (fun z => B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z))) (vac j)
          (comb ψ _ _ cT (vac j))

end GlobalTheory.AdForm

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {c : Comm D} {ρ : RealD c} {t : Tup c} (A : ClsK ρ t)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι)

def ClsK.IsFam (j : ℕ) (hj : j ≤ D.R.m) (Φ : t.Ch j → c.Fr j → GA D (c.X j) → ℂ) : Prop :=
  ∃ val : ∀ β, A.cl j β → FrN D (ρ.N j) → ℂ, (∀ β a, val β a ∈ ValC _ (ρ.lam j)) ∧
    ∀ β y, ∀ γ ∈ GQ (c.X j), ∀ a, ∀ x ∈ GinfC (c.X j), ∀ (κ : A.U j β) y',
      IsTr (ρ.r j hj x) (ρ.fr j y) y' → Φ β y (γ * (A.h j β a * x) * κ.1) = (A.chi j β κ : ℂ) * val β a y'

structure ClsK.LevT : Prop where
  stab : ∀ j, j ≤ D.R.m → ∀ β i g, g • o.Q j i = o.Q j i → ∃ h : (o.β j i).gl g ∈ A.U j β, A.chi j β ⟨_, h⟩ = 1
  dec : ∀ j, j ≤ D.R.m → ∀ β, ∀ κ ∈ A.U j β, ∃ g : ι → GL (Fin (c.X j).rank) k, (∀ i, g i • o.Q j i = o.Q j i) ∧
    ∃ κ' ∈ grpOff (c.X j) (fun x => ∃ i, x = (o.p i).v), κ = (o.I.map fun i => (o.β j i).gl (g i)).prod * κ'

structure ClsK.FullT : Prop where
  ram : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ β y, t.rd j β ψ y ∈ o.Ram j
  full : ∀ j hj Φ, A.IsFam j hj Φ → (∀ β y, Φ β y ∈ o.Ram j) → ∃ ψ ∈ t.Ram j, ∀ β y, t.rd j β ψ y = Φ β y

def SOnCols (D : D7) : Prop :=
  ∀ (c : Comm D) (ρ : RealD c) (t : Tup c) (A : ClsK ρ t) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → ρ.Is → A.Forms →
    o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → A.LevT o → A.FullT o →
    ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → t.Col j → t.Col j, ∀ j, j ≤ D.R.m → ∀ η, ∀ ψ ∈ t.Ram j,
      S j η ψ ∈ t.Ram j ∧ ∀ β y, t.rd j β (S j η ψ) y = o.S (fun _ => η) j (t.rd j β ψ y)

def RamIff (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S : HSp D) (β : Frame p S n) (P : Pair k n)
    (g : 𝓀[k]ˣ → GL n k), (∀ s, g s • P = s • P) → ∀ φ : GA D S → ℂ,
      RamAt β P φ ↔ IsContAut S φ ∧ (∀ x, x • P = P → rTrans (β.gl x) φ = φ) ∧ ∑ᶠ s, rTrans (β.gl (g s)) φ = 0

end GlobalTheory.SeeSaw

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw

variable {D : D7} {c : Comm D}

def Tup.col (t : Tup c) (i : ℕ) (ψ : t.Col 0) : t.Col i := Nat.rec (motive := fun i => t.Col i) ψ (fun i φ => t.K i φ) i

def iterS {α β : Type} (S : β → α → α) (ε : ℕ → β) (n : ℕ) (x : α) : α :=
  Nat.rec (motive := fun _ => α) x (fun i y => S (ε (2 * i)) y) n

def Tup.KBack (t : Tup c) : Prop :=
  ∀ j, j < D.R.m → t.cK j ≠ 0 ∧ ∀ y', ∃ (n : ℕ) (y : Fin n → c.Fr j) (P : Fin n → PolF D (c.X (j + 1)).rank (c.X j).rank),
    ∀ ψ ∈ t.Ram j, ∀ γ, t.cK j • t.rd (j + 1) γ (t.K j ψ) y' =
      ∑ a, ∑ α, (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P a) (t.rd j α ψ (y a))

def Tup.TailRd (t : Tup c) : Prop :=
  ∀ n (h : n = D.R.m), ∀ ψ ∈ t.Ram n, ∀ ψ' ∈ t.Ram n, ∀ a : ℂ, (∀ β y, t.rd n β ψ y = a • t.rd n β ψ' y) →
    ∀ F, t.tail n h ψ F = a * t.tail n h ψ' F

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι)

def TDat.cL (o : TDat c k ι) (j : ℕ) : ℂ :=
  ((((resCard k : ℝ) ^ ((((c.X (j + 1)).rank : ℝ) - (c.X j).rank) / 2) : ℝ) : ℂ)) ^ o.I.length

def LiftS (t : Tup c) : Prop :=
  ∀ j, j < D.R.m → ∀ α γ P, ∀ φ ∈ o.Ram j, (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P φ ∈ o.Ram (j + 1) ∧
    ∀ η : ι → 𝓀[k]ˣ, o.S (fun _ => η) (j + 1) ((t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P φ) =
      o.cL j • (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P (o.S (fun _ => η) j φ)

structure ReadS (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0) : Prop where
  ram : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ α y, t.rd j α ψ y ∈ o.Ram j
  S : ∀ j, j + 2 ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ α y, t.rd j α (t.S j ψ) y = o.S ε j (t.rd j α ψ y)
  S₀ : ∀ η, ∀ ψ ∈ t.Ram 0, S₀ η ψ ∈ t.Ram 0 ∧ ∀ α y, t.rd 0 α (S₀ η ψ) y = o.S (fun _ => η) 0 (t.rd 0 α ψ y)

def TDat.cS (o : TDat c k ι) (n : ℕ) : ℂ := ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range (2 * i), o.cL j

def CommX (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0) : Prop :=
  ∀ n (h : 2 * n = D.R.m), ∀ ψ ∈ t.Ram 0, ∀ F,
    t.tail (2 * n) h (t.up n ψ) F = o.cS n * t.tail (2 * n) h (t.col (2 * n) (iterS S₀ ε n ψ)) F

end GlobalTheory.SeeSaw

end
end
