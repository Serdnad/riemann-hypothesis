module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Formalism.RealPlaceAnalysis.Bundle004
public import Formalism.RealPlaceAnalysis.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def ipow (𝔡 : Ideal (𝓞 K)) (n : ℤ) : Submodule (𝓞 K) K :=
  (((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

def line (A : Submodule (𝓞 K) K) (v : V) : Submodule (𝓞 K) V :=
  A.map ((LinearMap.toSpanSingleton K V v).restrictScalars (𝓞 K))

def GenBy (A B : Submodule (𝓞 K) V) (e : ℕ) : Prop :=
  ∃ t : Finset V, t.card ≤ e ∧ A = B ⊔ Submodule.span (𝓞 K) (t : Set V)

def cf (K : Type) [Field K] [NumberField K] : ℝ := 1 + Real.logb 2 (Module.finrank ℚ K)

def HasOrtho (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → GlobalTheory.Mass.PD k →
    (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ Formalism.HermitianLatticesTheory.IsUnimodular k L) →
    ∃ I : Submodule (𝓞 K) W, Formalism.HermitianLatticesTheory.IsOrthoLattice k I (Module.finrank K W)

structure NF (H : HermSpace K V) (r : ℕ) where
  F : FlagD H r
  F' : FlagD H r
  j : ℕ
  j_le : j ≤ r
  c : K
  c_norm : c * star c = 1
  T : ℕ
  hT : F.T = T
  hT' : F'.T = T
  same : ∀ a : Fin (r + 1), j ≤ a.val → F'.e a = c • F.e a
  w : Formalism.MainNotions.S.Loc.Pt K j
  sgn : Fin j → ℤˣ
  pair : ∀ a b : Fin j, H.B (F.e (Fin.castLE (j_le.trans (Nat.le_succ r)) a))
    (F'.e (Fin.castLE (j_le.trans (Nat.le_succ r)) b)) = w.mat a b * ((sgn b : ℤ) : K)
  ist : Fin r → V
  ist_e : ∀ a b : Fin r, j ≤ b.val → H.B (F.e a.castSucc) (ist b) = if a = b then 1 else 0
  ist_e' : ∀ a b : Fin r, a.val < j → j ≤ b.val → H.B (F'.e a.castSucc) (ist b) = 0
  normalForm_dual_orthogonal_last : ∀ b : Fin r, j ≤ b.val → H.B F.z (ist b) = 0
  ist_iso : ∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (ist a) (ist b) = 0
  posdef : ∀ σ : K →+* ℂ, F.PosDefAt σ
  𝔡 : Ideal (𝓞 K)
  𝔡_ne : 𝔡 ≠ ⊥
  𝔡_star : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)

namespace NF

variable {H : HermSpace K V} {r : ℕ} (N : NF H r)

def aa (a : Fin r) : Submodule (𝓞 K) K := ipow N.𝔡 (-((r : ℤ) - a.val))

def Ist : Submodule K V := Submodule.span K (N.ist '' {b | N.j ≤ b.val})

def Wt : Submodule K V := perp H (V0 N.F N.F' ⊔ N.Ist)

def Wn : Submodule K V := perp H (N.F.X ⊔ N.F'.X ⊔ N.Ist)

def Pi : Submodule K V := perp H N.Wt

def P0 : Submodule (𝓞 K) V :=
  (⨆ a : Fin r, line (N.aa a) (N.F.e a.castSucc)) ⊔
    (⨆ a : Fin r, ⨆ _ : a.val < N.j, line (N.aa a) (N.F'.e a.castSucc)) ⊔ line 1 N.F.z ⊔
    ⨆ a : Fin r, ⨆ _ : N.j ≤ a.val, line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a)

def Ref (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V := N.P0 ⊔ (L ⊓ rs (𝓞 K) N.Wn)

def nD (l : ℕ) : ℝ :=
  if h : l ≤ r + 1 then |((Algebra.norm ℚ (Dl N.F N.F' l h) : ℚ) : ℝ)| *
    (Ideal.absNorm N.𝔡 : ℝ) ^ (-(2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a))) else 0

def Del : ℝ := N.nD N.j

def Db : ℝ := ∏ l ∈ (Finset.Icc 1 N.j).filter (fun l => N.nD l ≠ 0), N.nD l

def NT : ℝ := (N.T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K

def R : Subgroup (V ≃ₗ[K] V) := Subgroup.closure {s | N.F.InN (s : V →ₗ[K] V) ∧ N.F'.InN (s : V →ₗ[K] V)}

def fixing (_ : NF H r) (S : Submodule K V) : Subgroup (V ≃ₗ[K] V) := fixingSubgroup (V ≃ₗ[K] V) (S : Set V)

def R1 : Subgroup (V ≃ₗ[K] V) := N.R ⊓ N.fixing (V0 N.F N.F')

def ZI : Subgroup (V ≃ₗ[K] V) := N.R1 ⊓ N.fixing N.Wt

def Rs : Subgroup (V ≃ₗ[K] V) := N.R ⊓ N.fixing N.Wt

def Gam (Λ : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) := N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ

def IsTerm (g : ℕ) (Λ : Submodule (𝓞 K) V) : Prop :=
  IsFramed N.F N.F' Λ N.aa ∧ IsAdm N.F N.F' Λ (g : 𝓞 K)

def gI (g : ℕ) (Λ : Submodule (𝓞 K) V) : ℕ := idx (flagPairDefinitePartLattice N.F N.F' Λ) (latLa N.F N.F' Λ (g : 𝓞 K))

def iI (g : ℕ) (Λ : Submodule (𝓞 K) V) : ℕ := idx (latLa N.F N.F' Λ (g : 𝓞 K)) (latTh N.F N.F' Λ)

def bI (Λ : Submodule (𝓞 K) V) : ℕ := bOne N.F N.F' Λ N.j

def om (Λ : Submodule (𝓞 K) V) : ℝ := GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ))) (N.Gam Λ)

def omSum (Q : Submodule (𝓞 K) V → Prop) : ℝ≥0∞ :=
  ∑' o : MulAction.orbitRel.Quotient N.R (Submodule (𝓞 K) V), if Q o.out then ENNReal.ofReal (N.om o.out) else 0

def SameDat (g : ℕ) (Λ₀ Λ : Submodule (𝓞 K) V) : Prop :=
  latL N.F N.F' Λ = latL N.F N.F' Λ₀ ∧ latL N.F' N.F Λ = latL N.F' N.F Λ₀ ∧
    iotaGraph N.F N.F' Λ (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)

def Split (Λ : Submodule (𝓞 K) V) : Prop :=
  latTh N.F N.F' Λ = (Λ ⊓ rs (𝓞 K) N.Wt) ⊔ rs (𝓞 K) (II N.F N.F')

def Near (𝔠 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V) : Prop :=
  𝔠 • N.P0 ≤ Λ ⊓ rs (𝓞 K) N.Pi ∧ 𝔠 • (Λ ⊓ rs (𝓞 K) N.Pi) ≤ N.P0

end NF

def IsDat (H : HermSpace K V) (g : ℕ) (L₀ : Submodule (𝓞 K) V) (j x : ℕ)
    (d : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) : Prop :=
  GlobalTheory.Mass.IsIntLat H.B.flip d.1 ∧ GlobalTheory.Mass.discN H.B.flip d.1 = GlobalTheory.Mass.discN H.B.flip L₀ ∧
    IsModIso H (g : 𝓞 K) d.1 L₀ d.2 ∧ idx L₀ (fixLat d.2) = x ∧ GenBy L₀ (fixLat d.2) j

def Trip (H : HermSpace K V) (g : ℕ) (L₀ : Submodule (𝓞 K) V) (j x x' : ℕ) :
    Set ((Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V)) :=
  {p | IsDat H g L₀ j x p.1 ∧ IsDat H g L₀ j x' p.2.1 ∧ p.2.2 ∈ isomGrp H ∧ imLat p.2.2 p.2.1.1 = p.1.1 ∧
    ∀ y y' : V, (y, y') ∈ p.2.1.2 ↔ (p.2.2 y, y') ∈ p.1.2}

def fixSp (η : V ≃ₗ[K] V) : Submodule K V := LinearMap.ker ((η : V →ₗ[K] V) - LinearMap.id)

end GlobalTheory.DegCnt
end
end

section

noncomputable section

namespace GlobalTheory.GLm

open Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def InMir {n : ℕ} (M : Mt g n) : Prop := ∀ i j : Fin n, (i : ℕ) + 1 = n → M i j = (1 : Mt g n) i j

def IsMirClass {n : ℕ} (F : Gn g n → ℂ) : Prop :=
  ∀ p x : Gn g n, InMir (p : Mt g n) → InMir (x : Mt g n) → F (p * x * p⁻¹) = F x

def InR (i : ℕ) {n : ℕ} (M : Mt g n) : Prop := InPar i M ∧ IsUniUp (br i (n - i) M)

def supFrom (i : ℕ) {n : ℕ} (M : Mt g n) : ZMod g := ∑ j ∈ Finset.Ico i (n - 1), entN M j (j + 1)

def diag1 {k : ℕ} (h : Gn g k) (n : ℕ) : Gn g n :=
  toG fun i j : Fin n => if (i : ℕ) < k ∧ (j : ℕ) < k then entN (h : Mt g k) i j else (1 : Mt g n) i j

def tail (ψ₀ : AddChar (ZMod g) ℂ) (m : ℕ) {n : ℕ} (F : Gn g n → ℂ) : Gn g m → ℂ := fun p =>
  ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2))⁻¹ * ∑ x : Gn g n,
    if InR m (x : Mt g n) ∧ tl m (x : Mt g n) = (p : Mt g m) then
      F x * (ψ₀ (supFrom (m - 1) (x : Mt g n)))⁻¹ else 0

def indR (ψ₀ : AddChar (ZMod g) ℂ) (i n : ℕ) (ρ : Gn g i → ℂ) : Gn g n → ℂ := fun x =>
  ((Finset.univ.filter fun p : Gn g n => InR i (p : Mt g n)).card : ℂ)⁻¹ *
    ∑ y : Gn g n, if InMir (y : Mt g n) ∧ InR i ((y⁻¹ * x * y : Gn g n) : Mt g n) then
      ρ (toG (tl i ((y⁻¹ * x * y : Gn g n) : Mt g n))) * ψ₀ (supFrom i ((y⁻¹ * x * y : Gn g n) : Mt g n)) else 0

def indV (ψ₀ : AddChar (ZMod g) ℂ) (m : ℕ) (f : Gn g m → ℂ) : Gn g (m + 1) → ℂ := fun x =>
  ((Finset.univ.filter fun p : Gn g (m + 1) =>
      InMir (p : Mt g (m + 1)) ∧ InMir (tl m (p : Mt g (m + 1)))).card : ℂ)⁻¹ *
    ∑ y : Gn g (m + 1), if InMir (y : Mt g (m + 1)) ∧ InMir ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)) ∧
        InMir (tl m ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1))) then
      f (toG (tl m ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)))) *
        ψ₀ (entN ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)) (m - 1) m) else 0

def InPat {N : ℕ} (Φ : Fin N → Fin N → Prop) (M : Mt g N) : Prop := ∀ a b, ¬ Φ a b → M a b = (1 : Mt g N) a b

def sumAt {N : ℕ} (E : Fin N → Fin N → Prop) (M : Mt g N) : ZMod g := ∑ a, ∑ b, if E a b then M a b else 0

def ePat (g N : ℕ) [Fact g.Prime] (Φ E : Fin N → Fin N → Prop) (ψ₀ : AddChar (ZMod g) ℂ) :
    MonoidAlgebra ℂ (Gn g N) :=
  eDat g N (InPat Φ) (sumAt E) ψ₀

def IsW (k s a : ℕ) : Prop := s ≤ a ∧ a < s + k

def phI (k s i : ℕ) {N : ℕ} (a b : Fin N) : Prop :=
  (IsW k s a ∧ IsW k s b ∧ a < b) ∨ (¬ IsW k s a ∧ ¬ IsW k s b ∧ a < b) ∨ ((a : ℕ) < i ∧ IsW k s b) ∨
    (IsW k s a ∧ ((i < (b : ℕ) ∧ (b : ℕ) < s) ∨ ((b : ℕ) = s + k ∧ i < s) ∨ s + k < (b : ℕ)))

def eeI (k s : ℕ) {N : ℕ} (a b : Fin N) : Prop :=
  ((b : ℕ) = a + 1 ∧ (b : ℕ) < s) ∨ ((a : ℕ) + 1 = s ∧ (b : ℕ) = s + k) ∨ ((b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ)) ∨
    ((b : ℕ) = a + 1 ∧ IsW k s a ∧ IsW k s b)

def pm (g : ℕ) [Fact g.Prime] {n : ℕ} (σ : Equiv.Perm (Fin n)) : Gn g n :=
  toG fun r j : Fin n => if r = σ j then 1 else 0

def sigI (a c i j : ℕ) : ℕ := if j < i then j else if j < a then c + (j - i) else if j < a + (c - i) then i + (j - a) else j

def wI (g : ℕ) [Fact g.Prime] (a c i n : ℕ) : Gn g n :=
  toG fun r j : Fin n => if (r : ℕ) = sigI a c i j then 1 else 0

def mean {G : Type} [Fintype G] (f : G → ℂ) : ℂ := (Fintype.card G : ℂ)⁻¹ * ∑ x, f x

theorem inMir_one (n : ℕ) : InMir (1 : Mt g n) := fun _ _ _ => rfl

end GlobalTheory.GLm
end
end

section

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Count.Test

open Formalism.MainNotions.S GlobalTheory.Count

variable (I : AutInst)

theorem mem_lamX (x : I.GA) (y : Fin I.n → I.E) : y ∈ lamX I x ↔
    I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := by
  constructor
  · intro hy
    unfold lamX at hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hz
    | zero =>
      have e0 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by
        ext i; simp
      rw [e0, Matrix.mulVec_zero]
      exact zero_mem _
    | add z₁ z₂ _ _ h₁ h₂ =>
      have e2 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((z₁ + z₂) i)) =
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z₁ i)) +
            (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z₂ i)) := by
        ext i; simp
      rw [e2, Matrix.mulVec_add]
      exact add_mem h₁ h₂
    | smul a z _ hz =>
      have hc : Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a) ∈ IntAf I.F I.E :=
        Subring.subset_closure (Or.inl ⟨⟨_, a, rfl⟩, rfl⟩)
      have e1 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((a • z) i)) =
          Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a) •
            (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z i)) := by
        ext i; simp [Algebra.smul_def]
      rw [e1, Matrix.mulVec_smul]
      exact I.Lf.smul_mem ⟨_, hc⟩ hz
  · intro hy
    exact Submodule.subset_span hy

theorem le_lamX_one : I.L ≤ lamX I 1 := by
  intro y hy
  rw [mem_lamX]
  have h1 : I.fmat (1 : I.GA).2⁻¹ = 1 := by simp [AutInst.fmat]
  rw [h1, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩

theorem one_mem_GF : (1 : I.GA) ∈ I.GFset := by
  simp only [AutInst.GFset, Set.mem_ofPred_eq]
  refine ⟨1, one_mem _, fun v => ?_, ?_⟩
  · have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    simp [uMat, Matrix.nonsing_inv_mul _ hdet]
  · simp [AutInst.fmat]

theorem lamX_equivariant (g x : I.GA) (γ : GL (Fin I.n) I.E)
    (h : I.fmat g.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (y : Fin I.n → I.E) :
    (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I (g * x) ↔ y ∈ lamX I x := by
  have hm : ∀ a b : I.Gf, I.fmat (a * b) = I.fmat a * I.fmat b := fun a b => by
    simp [AutInst.fmat]
  have h1 : I.fmat 1 = 1 := by simp [AutInst.fmat]
  have hinc : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F)
      (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) i)) =
      I.fmat g.2 *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) := by
    ext i
    rw [h, RingHom.map_mulVec]
    rfl
  rw [mem_lamX, mem_lamX, hinc, Prod.snd_mul, _root_.mul_inv_rev, hm, Matrix.mulVec_mulVec, mul_assoc,
    ← hm g.2⁻¹ g.2, inv_mul_cancel, h1, mul_one]

theorem embedding_cases (w : InfinitePlace I.E) :
    w.embedding = I.φ (w.comap (algebraMap I.F I.E)) ∨
      w.embedding = ComplexEmbedding.conjugate (I.φ (w.comap (algebraMap I.F I.E))) := by
  have hcm := I.cm.cmUnram.2.1
  have hF : ∀ a : I.F, w.embedding (algebraMap I.F I.E a) =
      I.φ (w.comap (algebraMap I.F I.E)) (algebraMap I.F I.E a) := by
    have := I.cm.totReal
    have hv : w.comap (algebraMap I.F I.E) =
        InfinitePlace.mk (w.embedding.comp (algebraMap I.F I.E)) := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    have hψ : (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) =
        (w.comap (algebraMap I.F I.E)).embedding := RingHom.ext (I.φ_over _)
    have hreal : ComplexEmbedding.conjugate (w.embedding.comp (algebraMap I.F I.E)) =
        w.embedding.comp (algebraMap I.F I.E) :=
      ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _))
    have hmk : InfinitePlace.mk (w.embedding.comp (algebraMap I.F I.E)) =
        InfinitePlace.mk ((I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E)) := by
      rw [hψ, InfinitePlace.mk_embedding, hv]
    have key : w.embedding.comp (algebraMap I.F I.E) =
        (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) := by
      rcases InfinitePlace.mk_eq_iff.mp hmk with h | h
      · exact h
      · rwa [hreal] at h
    intro a
    exact RingHom.congr_fun key a
  set ψ := I.φ (w.comap (algebraMap I.F I.E)) with hψdef
  have hpt : ∀ e : I.E, w.embedding e = ψ e ∨ w.embedding e = starRingEnd ℂ (ψ e) := by
    intro e
    obtain ⟨s, hs⟩ := (I.cm.fixed (e + star e)).1 (by rw [star_add, star_star, add_comm])
    obtain ⟨t, ht⟩ := (I.cm.fixed (e * star e)).1 (by rw [star_mul, star_star])
    have h1 : w.embedding e + starRingEnd ℂ (w.embedding e) = ψ e + starRingEnd ℂ (ψ e) := by
      rw [← hcm w.embedding, ← hcm ψ, ← map_add (f := _), ← map_add (f := _), ← hs, hF]
    have h2 : w.embedding e * starRingEnd ℂ (w.embedding e) = ψ e * starRingEnd ℂ (ψ e) := by
      rw [← hcm w.embedding, ← hcm ψ, ← map_mul, ← map_mul, ← ht, hF]
    have h3 : (w.embedding e - ψ e) * (w.embedding e - starRingEnd ℂ (ψ e)) = 0 := by
      linear_combination (w.embedding e) * h1 - h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  obtain ⟨a, ha⟩ : ∃ a, w.embedding a ≠ ψ a := by
    by_contra hc
    push Not at hc
    exact hne1 (RingHom.ext hc)
  obtain ⟨b, hb⟩ : ∃ b, w.embedding b ≠ starRingEnd ℂ (ψ b) := by
    by_contra hc
    push Not at hc
    exact hne2 (RingHom.ext fun x => (hc x).trans (ComplexEmbedding.conjugate_coe_eq ψ x).symm)
  have ha' := (hpt a).resolve_left ha
  have hb' := (hpt b).resolve_right hb
  rcases hpt (a + b) with h | h
  · apply ha
    rw [map_add (f := _), map_add (f := _)] at h
    linear_combination h - hb'
  · apply hb
    rw [map_add (f := _), map_add (f := _), map_add (f := _)] at h
    linear_combination h - ha'

theorem frm_frame (x : I.GA) (w : InfinitePlace I.E) :
    (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) := by
  have hU : (uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ * Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) *
      uMat (x.1 (w.comap (algebraMap I.F I.E))) = Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) :=
    (x.1 (w.comap (algebraMap I.F I.E))).2
  have key : (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ *
      I.J.map (I.φ (w.comap (algebraMap I.F I.E))) *
      (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))) =
      Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ *
          ((I.P (w.comap (algebraMap I.F I.E)))ᴴ * I.J.map (I.φ (w.comap (algebraMap I.F I.E))) *
            I.P (w.comap (algebraMap I.F I.E))) * uMat (x.1 (w.comap (algebraMap I.F I.E))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [I.P_spec]; exact hU
  have hc : ∀ A : Matrix (Fin I.n) (Fin I.n) ℂ,
      (A.map (starRingEnd ℂ))ᴴ = Aᴴ.map (starRingEnd ℂ) := by
    intro A; ext i j; simp [Matrix.conjTranspose_apply]
  simp only [frm]
  split_ifs with h
  · rw [h]; exact key
  · rw [(embedding_cases I w).resolve_left h]
    have hJ : I.J.map (ComplexEmbedding.conjugate (I.φ (w.comap (algebraMap I.F I.E)))) =
        (I.J.map (I.φ (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ) := by
      ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [hJ, hc, ← Matrix.map_mul, ← Matrix.map_mul, key]
    ext i j
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, apply_ite (starRingEnd ℂ)]

theorem one_mem_nearSet (x : I.GA) {δ : ℝ} (hδ : 0 ≤ δ) : (1 : I.GA) ∈ nearSet I x δ := by
  simp only [nearSet, Set.mem_ofPred_eq]
  refine ⟨one_mem_GF I, ?_, fun v => ?_⟩
  · rw [mul_one, inv_mul_cancel]
    exact one_mem (Formalism.UG.stabGL I.Lf)
  · simp [uMat, Formalism.REAL.hs, hδ]

end GlobalTheory.Count.Test
end
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Jet

def IsDer {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  GlRel E ∧ IsUnitary ε E ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∀ v : V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) ((∑ a, ∑ b, X a b • E a b v : V) : H) 0) ∧
    ∀ (v : V) (y : H), SmoothOnG ε (fun g => ⟪y, σ g (v : H)⟫_ℂ)

def at1 {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (G : Arr V n 1) (a b : Fin n) : V :=
  arrOf V n 1 G (fun _ => (a, b))


namespace StdDer


end StdDer

end GlobalTheory.Jet
end
end
