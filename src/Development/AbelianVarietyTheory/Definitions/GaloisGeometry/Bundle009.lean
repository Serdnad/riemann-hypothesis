module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsBlockVec {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (χ : kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W) : Prop :=
  ∀ h ∈ KO k (Fin (r + t)),
    (∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1) →
    (∀ i j : Fin r, valuation k (h.val (Fin.castAdd t i) (Fin.castAdd t j) - if i = j then 1 else 0) < 1) →
    ∀ u : kˣ, (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det → π h v = (χ u : ℂ) • v


variable (k) in
def BlockSplit : Prop := ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), IsSmoothChar χ → IsTame χ →
  v ≠ 0 → IsBlockVec χ π.π v →
  (∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSpherical π₂.π ∧
    Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin t) χ))))) ∨
  ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) ∧
    t < Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))}

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def RecSupp (rc : ∀ n, Irr k n → WD h) : Prop :=
  ∀ (n s : ℕ) (π : Irr k n) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) →
    ∀ g : Weil h, (rc n π).charPol g = ∏ a, (rc (d a) (σ a)).charPol g

def RecUnit (rc : ∀ n, Irr k n → WD h) : Prop :=
  ∀ (χ : kˣ →* ℂˣ) (c : Irr k 1), IsUnitaryChar χ → Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    ∀ g : Weil h, ∀ α ∈ (rc 1 c).eig g, ‖α‖ = 1

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  {T : WDTie N A} (S : Reading T)

def SuppLaws : Prop := ∀ i w hw, RecSupp (S i w hw).rc

def TypeBlock (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w) : Prop :=
  IsTame (S i w hw).mu ∧ ∀ P, ∃ v, v ≠ 0 ∧ IsBlockVec (S i w hw).mu ((S i w hw).rep P).π v

def BlockSplitAll (E : Type) [Field E] [NumberField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), BlockSplit (w.adicCompletion E)

variable (N A)

def MuInt : Prop := ∀ (i : N.Loc) (τ : H.E →+* ℂ), ∀ z ∈ A.infG (A.muC i) τ, ∃ m : ℤ, z = (m : ℂ)

def ChiIne : Prop := ∀ (i : N.Loc) (w : PlE H), w ∉ placesOver H.E (N.l i) →
  ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))

def XiOverO : Prop := ∀ i : N.Loc, ∃ ξ : G H.E N.Om →* (N.O i)ˣ, Continuous (fun g => ((ξ g : (N.O i)ˣ) : N.O i)) ∧
  ∀ w : PlE H, w ∉ placesOver H.E (N.l i) → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), ξ σ = 1) ∧
    ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      A.frobEig (A.lpTw (A.locG A.etaTinv w) (-(R.t : ℝ) / 2)) = {iotaO N A i ((ξ σ : (N.O i)ˣ) : N.O i)}

def RowPoint : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
  ∃ i' : N.Loc, N.j i' = N.j i ∧ N.l i' = N.l i ∧ (∀ w, IsSplitPl H w → A.locW i' σ w = A.locW i σ w) ∧
    (∃ φ : N.O i' ≃+* N.O i, Continuous φ ∧ ∀ z, iotaO N A i (φ z) = iotaO N A i' z) ∧
    ∃ (P : A.AV i') (x : N.X i'), thetaOf N A i' σ P ∧ A.ptV i' P = some x

end GlobalTheory.SplitRead
end
end

section

noncomputable section

namespace GlobalTheory.HTW

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def Alternates {n : ℕ} (up : ZMod n → Bool) : Prop := ∀ i, up (i + 1) = !up i

def NoThree {n : ℕ} (th : ZMod n → Prop) : Prop := ∀ i, ¬ (th i ∧ th (i + 1) ∧ th (i + 2))

def WindowTwo {n : ℕ} (th : ZMod n → Prop) (L : ℕ) : Prop :=
  ∀ (i : ZMod n) (a b c : ℕ), a < b → b < c → c < L → ¬ (th (i + a) ∧ th (i + b) ∧ th (i + c))

def Clusters {n : ℕ} (th : ZMod n → Prop) (j : ℕ) : Prop :=
  ∃ (F : Set (ZMod n)) (sp : ZMod n → ℕ),
    (∀ x ∈ F, th x ∧ sp x ≤ j ∧ sp x < n ∧ th (x + sp x) ∧
      (∀ q : ℕ, 0 < q → q < sp x → ¬ th (x + q)) ∧ (∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x - q))) ∧
    ∀ y, th y → ∃! x, x ∈ F ∧ (y = x ∨ y = x + sp x)

structure WordData (n : ℕ) where
  up : ZMod n → Bool
  sz : ZMod n → ℤ
  b : ℕ
  w : ℕ
  S : ℕ
  η : ℕ
  m : ℕ
  J1 : ZMod n → Set ℤ
  J2 : ZMod n → Multiset ℤ

namespace WordData

variable {n : ℕ} (W : WordData n)

def thick (i : ZMod n) : Prop := (W.b : ℤ) ≤ W.sz i ∧ W.sz i ≤ W.b + W.η

def T1 : Prop := ∀ i, ∀ u ∈ W.J1 i,
  (if W.up i then W.sz i ≤ u ∧ u ≤ W.sz i + W.S else -W.sz i - W.S ≤ u ∧ u ≤ -W.sz i) ∨ |u| ≤ W.η

def T2 : Prop := ∀ i, (∀ u ∈ W.J2 i, u ∈ W.J1 i) ∧ ((W.J2 i).filter fun u : ℤ => |u| ≤ (W.η : ℤ)).card ≤ W.m

def ThickOr : Prop := ∀ i, W.thick i ∨ W.sz i ≤ W.w

def G : ℕ := W.w + W.S + W.η

def Mi (i : ZMod n) : ℕ := if W.up i then W.η else max W.η (W.sz i + W.S).toNat

def hi (i : ZMod n) : ℕ := if W.up i then max W.η (W.sz i + W.S).toNat else W.η

def HypA (j : ℕ) : Prop :=
  (∀ i, 0 ≤ W.sz i) ∧ 1 ≤ j ∧ j + 1 ≤ n ∧ ((∃ i, W.thick i) → 40 * (j + 1) * (W.G + 1) ≤ W.b) ∧
    Clusters W.thick j

def Box : Prop :=
  1 ≤ W.b ∧ 1 ≤ W.w ∧ 20 * W.w ≤ W.b ∧ 20 * W.η ≤ W.b ∧ 20 * W.S ≤ W.b ∧ ∀ i, (W.η : ℤ) < W.sz i

def HypNT : Prop := Alternates W.up ∧ (∃ i, ¬ W.thick i) ∧ NoThree W.thick

def HypAT (l : ℕ) : Prop :=
  Even n ∧ Alternates W.up ∧ ∀ M : ℤ, IsGreatest (Set.range W.sz) M → ∀ i,
    1 ≤ W.sz i ∧ ((M : ℝ) + W.S) / 2 ≤ W.sz i ∧
    2 * (((M : ℝ) + W.S + W.η) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 +
      (Real.logb l (2 * ((M : ℝ) + W.S + W.η)) + 1)) + W.η + 1 ≤ W.sz i

end WordData

def plc {fr : Formalism.HC.Frame} (g : fr.GG) : fr.GG := if g.1.2 = 1 then g else fr.cc * g

theorem plc_mem {fr : Formalism.HC.Frame} (g : fr.GG) : plc g ∈ fr.Psi := by
  rw [Formalism.HC.Frame.mem_Psi_iff]
  unfold plc
  split_ifs with h
  · exact h
  · have h' : g.1.2 = -1 := (Int.units_eq_one_or g.1.2).resolve_left h
    simp [Formalism.HC.Frame.cc, c0, h']

def Thick {R : Ranks} (H : Host R) (g : R.GG) : Prop := plc g ∈ H.thickPlaces

def letter {fr : Formalism.HC.Frame} (τ φ : fr.GG) (i : ZMod (orderOf φ)) : fr.GG := τ * φ ^ i.val

def pos {fr : Formalism.HC.Frame} (ε : ℤˣ) (g : fr.GG) : Bool := decide (g.1.2 = ε)

section Jumps

variable {R : Ranks} (P : HCParam R) (j : Fin R.m)

def cloud : Multiset ℤ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map fun i => ⌊P.e j⌋ + ⌊P.v i⌋ + ((R.t : ℤ) - 1) / 2

def lows : Multiset ℤ :=
  (Finset.univ : Finset (Fin R.m)).val.map fun i => ⌊P.e j⌋ - ⌊P.b i⌋ + ((R.t : ℤ) - 1) / 2

def block (R : Ranks) : Multiset ℤ := (Multiset.range R.t).map fun c : ℕ => (c : ℤ)

def jW (s : Bool) : Multiset ℤ :=
  if s then cloud P j + lows P j else (cloud P j + lows P j).map fun u => (R.t : ℤ) - 1 - u

def jR (s : Bool) : Multiset ℤ := jW P j s + block R

def jT2 (s : Bool) : Multiset ℤ := (jW P j s).map fun u => -u - 1

def jT1 (s : Bool) : Multiset ℤ := (jR P j s).map fun u => -u - 1

def szT (s : Bool) : ℤ := if s then ⌊P.e j⌋ + ((R.t : ℤ) + 1) / 2 else ⌊P.e j⌋ - ((R.t : ℤ) + 1) / 2

end Jumps

section Page

variable {D : D7} (L : SizeData₂ D)

def hcAt (D : D7) (g : D.R.GG) : HCParam D.R := D.hc (D.eTau.symm ⟨plc g, plc_mem g⟩)

def bHat : ℕ := ⌈L.sc.b⌉₊ - (D.R.t + 1) / 2

def etaHat : ℕ := ⌊L.etaSz⌋₊ + D.R.t + 2

def sHat : ℕ := ⌊L.Sc⌋₊

def wMax (D : D7) : ℕ :=
  sSup {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat}

def wHat (D : D7) : ℕ := wMax D + (D.R.t + 1) / 2

def hPage : ℝ := L.sc.b + L.Sc + L.etaSz + D.R.t

def depth (l : ℕ) : ℕ := sInf {j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j}

def pageWord (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) : WordData (orderOf φ) where
  up i := !pos ε (letter τ φ i)
  sz i := szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i))
  b := bHat L
  w := wHat D
  S := sHat L
  η := etaHat L
  m := D.R.m
  J1 i := {u | u ∈ jT1 (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i))}
  J2 i := jT2 (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i))

def Roomy (C : ℝ) : Prop :=
  100 ≤ C ∧ (100 : ℝ) ≤ L.sc.w'' D.R.n ∧
  100 * (L.etaSz + L.Sc + D.R.t + 2) ≤ L.sc.w'' D.R.n ∧
  L.sc.w'' D.R.n ≤ L.sc.b' ∧
  (∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b') ∧
  C * ((D.host.Lw : ℝ) + 1) * L.sc.b' ≤ L.sc.b

end Page

end GlobalTheory.HTW
end
end

section

noncomputable section

namespace GlobalTheory.StringRepresentationDecomposition

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal

def epsQ (D : D7) (i : D.nd.Loc) (g : G D.host.E D.nd.Om) : Qbar (D.nd.l i) :=
  iotaOQ D.nd D.naut i ((Formalism.MainNotions.N.Glob.epsO D.nd i g : (D.nd.O i)ˣ) : D.nd.O i)

def IsStringRep (D : D7) (i : D.nd.Loc) (p : Part D.naut.CG)
    (R : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i))) : Prop :=
  Continuous (fun g => ((R g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i)))) ∧ IsSSRep R ∧
    ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i R w = D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2)

def SSList : Prop :=
  ∀ (k : Type) [Field k] (Γ : Type) [Group Γ] (n : ℕ) (ρ : Γ →* GL (Fin n) k),
    ∃ L : List (Σ m : ℕ, Γ →* GL (Fin m) k), (∀ p ∈ L, 1 ≤ p.1 ∧ IsIrrSub p.2 ⊤) ∧
      ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly =
        (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) k).charpoly).prod

def SSRankUnique : Prop :=
  ∀ (k : Type) [Field k] (Γ : Type) [Group Γ] (L L' : List (Σ m : ℕ, Γ →* GL (Fin m) k)),
    (∀ p ∈ L, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤) → (∀ p ∈ L', 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤) →
    (∀ g, (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) k).charpoly).prod =
      (L'.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) k).charpoly).prod) →
    ((L.map fun p => p.1 : List ℕ) : Multiset ℕ) = ((L'.map fun p => p.1 : List ℕ) : Multiset ℕ)

def EigenCharTwist : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] (n : ℕ) (ρ : Γ →* GL (Fin n) K)
    (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (χ : Γ →* Kˣ),
    IsSSRep ρ → (∀ p ∈ L, IsSSRep p.2) →
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod) →
    (∃ v : Fin n → K, v ≠ 0 ∧ ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).mulVec v = ((χ g : Kˣ) : K) • v) →
    ∃ p ∈ L, ∃ v : Fin p.1 → K, v ≠ 0 ∧
      ∀ g, ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).mulVec v = ((χ g : Kˣ) : K) • v

def ValRingModel : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsAlgClosed (IsLocalRing.ResidueField A))
      (j : A →+* Qbar l), Function.Injective j ∧ Set.range j = {x : Qbar l | ‖x‖ ≤ 1} ∧
      (∀ x : A, x ∈ IsLocalRing.maximalIdeal A ↔ ‖j x‖ < 1) ∧
      ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
        (n : ℕ) (ρ : Γ →* GL (Fin n) (Qbar l)),
        Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l))) →
        ∃ (ρ0 : Γ →* GL (Fin n) A) (P : GL (Fin n) (Qbar l)), ∀ g,
          ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l)) =
            (P : Matrix (Fin n) (Fin n) (Qbar l)) * ((ρ0 g : GL _ _) : Matrix (Fin n) (Fin n) A).map j *
              ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))

def RbEx (D : D7) : Prop := ∀ i : D.nd.Loc, HG D.nd D.naut i → ∃ rb, IsRhoBar D.nd i rb

def Numerics : Prop :=
  ∀ (r t d n a : ℕ) (A : Multiset ℕ), 1 < r → 2 ≤ t → a < d → (d : ℤ) - 1 - 2 * a = (t : ℤ) - 1 → A.sum = n → (∀ x ∈ A, 1 ≤ x) →
    1 ≤ n → d • A ≤ r ::ₘ Multiset.replicate t 1 → n = 1 ∧ d = t

def Rest : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (A : ι → Multiset ℕ) (r : ℕ), (∀ k, 1 ≤ d k) → (∀ k, A k ≠ 0) →
    ∑ k, d k • A k = {r} → Fintype.card ι = 1 ∧ ∀ k, d k = 1 ∧ A k = {r}

def EigPd (D : D7) : Prop :=
  ∀ i : D.nd.Loc, HG D.nd D.naut i → ∀ w ∈ D.nd.S i,
      w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) →
      ∀ rb, IsRhoBar D.nd i rb →
      ¬ (((rb (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
        (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))

def HOneTwo (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (rb : G D.host.E D.nd.Om →* GL (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) (w : PlE D.host),
    w ∈ D.nd.S i → IsRhoBar D.nd i rb →
    ¬ (((rb (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) →
    ∀ e : ℤ, Formalism.MainNotions.SumRepresentations.At.HOneTwoZero D.nd i w
      (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e))

end GlobalTheory.StringRepresentationDecomposition

end
end
