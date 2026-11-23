module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

section

noncomputable section

open NumberField nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

def traceDual (M : FractionalIdeal (𝓞 F)⁰ F) : Set F :=
  {y | ∀ a ∈ M, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n}

def covol (M : FractionalIdeal (𝓞 F)⁰ F) : ℝ :=
  Real.sqrt |(discr F : ℝ)| * (FractionalIdeal.absNorm M : ℝ)

def dualCone (M : FractionalIdeal (𝓞 F)⁰ F) (z : (F →+* ℝ) → ℂ) : Set F :=
  {ν | ν ∈ traceDual M ∧ ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν}

def lhsTerm (k : ℕ) (z : (F →+* ℝ) → ℂ) (a : F) : ℂ :=
  (∏ τ : F →+* ℝ, (z τ + ((τ a : ℝ) : ℂ))) ^ (-(k : ℤ))

def rhsTerm (k : ℕ) (z : (F →+* ℝ) → ℂ) (ν : F) : ℂ :=
  ((|∏ τ : F →+* ℝ, τ ν| ^ (k - 1) : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * ∑ τ : F →+* ℝ, ((τ ν : ℝ) : ℂ) * z τ)

def lipConst (k : ℕ) (M : FractionalIdeal (𝓞 F)⁰ F) : ℂ :=
  (2 * Real.pi * Complex.I) ^ (k * Module.finrank ℚ F) /
    ((((k - 1).factorial : ℕ) : ℂ) ^ Module.finrank ℚ F * (covol M : ℂ))

def Lipschitz : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 →
    ∀ (k : ℕ), 2 ≤ k → Even k →
    ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) →
      Summable (fun a : (M : Set F) => lhsTerm k z a) ∧
      Summable (fun ν : dualCone M z => rhsTerm k z ν) ∧
      ∑' a : (M : Set F), lhsTerm k z a = lipConst k M * ∑' ν : dualCone M z, rhsTerm k z ν


open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) (y : F) :
    y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.traceDual M ↔ y ∈ FractionalIdeal.dual ℤ ℚ M := by
  change (∀ a ∈ M, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n) ↔ _
  rw [FractionalIdeal.mem_dual hM]
  refine forall₂_congr fun a _ => ?_
  simp [Algebra.traceForm_apply, eq_comm]


open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_pos {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) :
    0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol M := by
  refine mul_pos (Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F)))) ?_
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg M)
    (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.2 hM))


open scoped Classical in
open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
open Classical in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_eq_covolume [IsTotallyReal F]
    (M : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol (M : FractionalIdeal (𝓞 F)⁰ F) =
      ZLattice.covolume (E := mixedEmbedding.mixedSpace F)
        (mixedEmbedding.idealLattice F M) MeasureTheory.volume := by
  rw [mixedEmbedding.covolume_idealLattice, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero,
    mul_one, mul_comm]
  rfl


open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb [IsTotallyReal F] :
    Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
  classical
  rw [IsTotallyReal.finrank, ← InfinitePlace.card_real_embeddings]
  convert Fintype.card_congr
    { toFun := fun φ => ⟨Complex.ofRealHom.comp φ, ?_⟩
      invFun := fun φ => φ.2.embedding
      left_inv := ?_
      right_inv := ?_ : (F →+* ℝ) ≃ { φ : F →+* ℂ // ComplexEmbedding.IsReal φ } }
  · rw [ComplexEmbedding.isReal_iff]; ext x; simp [ComplexEmbedding.conjugate]
  · intro φ; ext x
    simpa using ComplexEmbedding.IsReal.coe_embedding_apply (φ := Complex.ofRealHom.comp φ) _ x
  · intro φ; ext x; simp [ComplexEmbedding.IsReal.coe_embedding_apply]

end GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
end
end

section

open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms

def dirDeriv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) (F : V → ℂ) : V → ℂ :=
  fun z => fderiv ℂ F z v

def wordDeriv {κ V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : κ → V) (w : List κ)
    (F : V → ℂ) : V → ℂ :=
  w.foldr (fun x G => dirDeriv (v x) G) F

def IsSpelling {κ : Type} [DecidableEq κ] (w : (κ → ℕ) → List κ) : Prop :=
  ∀ e x, (w e).count x = e x

def lineForm (a : ℝ) (D D' : ℂ) : ℂ := 2 * (a : ℂ) * (D * conj D')

def omega (a : ℝ) (D : ℂ) : ℝ := 1 / (π * (lineForm a D D).re)

section OnePlace

variable {X X' : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [FiniteDimensional ℂ X'] {n₀ n₁ : ℕ}

end OnePlace

section Places

variable {Pl : Type} [Fintype Pl] [DecidableEq Pl] {X X' : Pl → Type}
  [∀ τ, NormedAddCommGroup (X τ)] [∀ τ, InnerProductSpace ℂ (X τ)] [∀ τ, FiniteDimensional ℂ (X τ)]
  [∀ τ, NormedAddCommGroup (X' τ)] [∀ τ, InnerProductSpace ℂ (X' τ)] [∀ τ, FiniteDimensional ℂ (X' τ)]
  {n₀ n₁ : ℕ}

end Places

def coordVec {κ : Type} [DecidableEq κ] (p : κ) : κ → ℂ := Pi.single p 1

end GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms
end
end

section

open scoped NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

noncomputable section Defs

variable {C : Type} [Field C] (w : Valuation C ℝ≥0)

noncomputable def addVal (ℓ c : C) : ℝ := Real.log (w c : ℝ) / Real.log (w ℓ : ℝ)

def HasVal (ℓ c : C) (y : ℝ) : Prop := c ≠ 0 ∧ addVal w ℓ c = y

def IsLatticeBasis {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n : ℕ} (x : Fin n → W)
    (X : Submodule w.valuationSubring W) : Prop :=
  LinearIndependent C x ∧ Submodule.span w.valuationSubring (Set.range x) = X

def HasLength (ℓ : C) {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] (X X' : Submodule w.valuationSubring W) (t : ℝ) :
    Prop :=
  X' ≤ X ∧ ∃ (n : ℕ) (x x' : Fin n → W) (M : Matrix (Fin n) (Fin n) C),
    IsLatticeBasis w x X ∧ IsLatticeBasis w x' X' ∧ (∀ i, x' i = ∑ j, M i j • x j) ∧
      HasVal w ℓ M.det t

def DetRel (ℓ : C) {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (X : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) : Prop :=
  ∃ (x : Fin (p + q) → Fin (p + q) → C) (u : Fin p → Fin (p + q) → C)
    (m : Fin q → Fin (p + q) → C) (c : C),
    IsLatticeBasis w x X ∧ IsLatticeBasis w (fun i => F.mkQ (u i)) L ∧ IsLatticeBasis w m M ∧
      (∀ i, m i ∈ F) ∧ HasVal w ℓ c y ∧
      (Matrix.of x).det = c * (Matrix.of (Fin.append u m)).det

variable {w}

def eigenSub {S : Type} [DecidableEq S] {W : S → Type} [∀ s, AddCommGroup (W s)]
    [∀ s, Module w.valuationSubring (W s)] (X : Submodule w.valuationSubring (∀ s, W s))
    (τ : S) : Submodule w.valuationSubring (W τ) :=
  X.comap (LinearMap.single w.valuationSubring W τ)

def eigenQuot {S : Type} {W : S → Type} [∀ s, AddCommGroup (W s)]
    [∀ s, Module w.valuationSubring (W s)] (X : Submodule w.valuationSubring (∀ s, W s))
    (τ : S) : Submodule w.valuationSubring (W τ) :=
  X.map (LinearMap.proj τ)

def freeLattice {S : Type} (a : S → w.valuationSubring) (r : ℕ) :
    Submodule w.valuationSubring (S → Fin r → C) where
  carrier := {x | ∀ i, ∃ f : Polynomial w.valuationSubring, ∀ s,
    x s i = ((f.eval (a s) : w.valuationSubring) : C)}
  zero_mem' := fun _ => ⟨0, fun _ => by simp⟩
  add_mem' := by
    intro x y hx hy i
    obtain ⟨f, hf⟩ := hx i
    obtain ⟨g, hg⟩ := hy i
    exact ⟨f + g, fun s => by simp [hf s, hg s]⟩
  smul_mem' := by
    intro c x hx i
    obtain ⟨f, hf⟩ := hx i
    exact ⟨Polynomial.C c * f, fun s => by simp [hf s, Algebra.smul_def]⟩

def unif {S : Type} {r : ℕ} (a : S → w.valuationSubring) (x : S → Fin r → C) :
    S → Fin r → C := fun s => (a s : C) • x s

def filSpace {S : Type} {r : ℕ} (Fil : Submodule w.valuationSubring (S → Fin r → C)) (s : S) :
    Submodule C (Fin r → C) :=
  Submodule.span C (eigenQuot (W := fun _ => Fin r → C) Fil s : Set (Fin r → C))

def quotMap {r : ℕ} (F : Submodule C (Fin r → C)) :
    (Fin r → C) →ₗ[w.valuationSubring] ((Fin r → C) ⧸ F) :=
  F.mkQ.restrictScalars w.valuationSubring

def lie {S : Type} {r : ℕ} (H Fil : Submodule w.valuationSubring (S → Fin r → C)) :
    Submodule w.valuationSubring (∀ s, (Fin r → C) ⧸ filSpace Fil s) :=
  H.map (LinearMap.pi fun s => quotMap (filSpace Fil s) ∘ₗ LinearMap.proj s)

def dualLie {S : Type} [DecidableEq S] {r : ℕ}
    (β : (S → Fin r → C) →ₗ[C] (S → Fin r → C) →ₗ[C] C)
    (Fil H' Fil' : Submodule w.valuationSubring (S → Fin r → C)) (τ : S) :
    Submodule w.valuationSubring (Fin r → C) where
  carrier := {x | x ∈ filSpace Fil τ ∧ ∀ y : Fin r → C,
    (filSpace Fil' τ).mkQ y ∈ eigenSub (lie H' Fil') τ →
      β (Pi.single τ x) (Pi.single τ y) ∈ w.valuationSubring}
  zero_mem' := ⟨zero_mem _, fun y _ => by simp⟩
  add_mem' := by
    rintro x x' ⟨hx, h⟩ ⟨hx', h'⟩
    refine ⟨add_mem hx hx', fun y hy => ?_⟩
    rw [Pi.single_add, map_add (f := _), LinearMap.add_apply]
    exact add_mem (h y hy) (h' y hy)
  smul_mem' := by
    rintro c x ⟨hx, h⟩
    refine ⟨Submodule.smul_mem _ (c : C) hx, fun y hy => ?_⟩
    have : (Pi.single τ (c • x) : S → Fin r → C) = (c : C) • (Pi.single τ x : S → Fin r → C) :=
      Pi.single_smul' τ (c : C) x
    rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_mem c.2 (h y hy)

structure IsFiltration {S : Type} {r : ℕ} (a : S → w.valuationSubring)
    (Fil : Submodule w.valuationSubring (S → Fin r → C)) : Prop where
  le : Fil ≤ freeLattice a r
  stable : ∀ x ∈ Fil, unif a x ∈ Fil
  saturated : ∀ x ∈ freeLattice a r, ∀ c : w.valuationSubring, c ≠ 0 → c • x ∈ Fil → x ∈ Fil

structure IsDualDatum {S : Type} {r : ℕ} (a : S → w.valuationSubring)
    (β : (S → Fin r → C) →ₗ[C] (S → Fin r → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin r → C)) : Prop where
  fil : IsFiltration a Fil
  fil' : IsFiltration a Fil'
  adjoint : ∀ x y, β (unif a x) y = β x (unif a y)
  perfect_left : ∀ x, x ∈ freeLattice a r ↔
    ∀ y ∈ freeLattice a r, β x y ∈ w.valuationSubring
  perfect_right : ∀ y, y ∈ freeLattice a r ↔
    ∀ x ∈ freeLattice a r, β x y ∈ w.valuationSubring
  ann_left : ∀ x ∈ freeLattice a r, (x ∈ Fil ↔ ∀ y ∈ Fil', β x y = 0)
  ann_right : ∀ y ∈ freeLattice a r, (y ∈ Fil' ↔ ∀ x ∈ Fil, β x y = 0)

def diffGen {S : Type} [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (τ : S) :
    w.valuationSubring := ∏ s ∈ Finset.univ.erase τ, (a τ - a s)

def flatLattice {S : Type} {r : ℕ} (a : S → w.valuationSubring) (τ : S)
    (d : w.valuationSubring) : Submodule w.valuationSubring (Fin r → C) :=
  (eigenQuot (W := fun _ => Fin r → C) (freeLattice a r) τ).map
    (LinearMap.lsmul w.valuationSubring (Fin r → C) d)

end Defs

section Stmt

variable {C : Type} [Field C] (w : Valuation C ℝ≥0) (ℓ : C)

def TypeOne : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S),
    Function.Injective a → IsDualDatum a β Fil Fil' →
    (∀ s, Module.finrank C (filSpace Fil s) = q) →
    let H := freeLattice a (p + q)
    let vd := addVal w ℓ (diffGen a τ : C)
    let HH := flatLattice (r := p + q) a τ (diffGen a τ)
    let FilSub := eigenSub (W := fun _ => Fin (p + q) → C) Fil τ
    let FilQuot := eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ
    HH = eigenSub (W := fun _ => Fin (p + q) → C) H τ ∧
    DetRel w ℓ (filSpace Fil τ) HH (eigenSub (lie H Fil) τ) (dualLie β Fil H Fil' τ)
      ((q : ℝ) * vd) ∧
    HH ⊓ LinearMap.ker (quotMap (filSpace Fil τ)) = FilSub ∧
    ∃ t : ℝ, HasLength w ℓ FilQuot FilSub t ∧
      HasLength w ℓ (eigenSub (lie H Fil) τ) (HH.map (quotMap (filSpace Fil τ)))
        ((q : ℝ) * vd - t) ∧
      0 ≤ (q : ℝ) * vd - t ∧ (q : ℝ) * vd - t ≤ (q : ℝ) * vd

def TypeTwo : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ τ' : S),
    τ ≠ τ' → (∀ s, s = τ ∨ s = τ') →
    HasVal w ℓ ((a τ : C) - (a τ' : C)) (1 / 2) → IsDualDatum a β Fil Fil' →
    Module.finrank C (filSpace Fil τ) = q → Module.finrank C (filSpace Fil τ') = p →
    let H := freeLattice a (p + q)
    let HH := flatLattice (r := p + q) a τ 1
    let FilSub := eigenSub (W := fun _ => Fin (p + q) → C) Fil τ
    let FilQuot := eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ
    HH = eigenQuot (W := fun _ => Fin (p + q) → C) H τ ∧
    DetRel w ℓ (filSpace Fil τ) HH (eigenSub (lie H Fil) τ) (dualLie β Fil H Fil' τ)
      (-((q : ℝ) / 2)) ∧
    HH.map (quotMap (filSpace Fil τ)) = eigenQuot (lie H Fil) τ ∧
    (∃ la : ℝ, HasLength w ℓ (eigenQuot (lie H Fil) τ) (eigenSub (lie H Fil) τ) la ∧
      0 ≤ la ∧ la ≤ (q : ℝ) / 2 ∧
      HasLength w ℓ (HH ⊓ LinearMap.ker (quotMap (filSpace Fil τ))) FilQuot
        ((q : ℝ) / 2 - la)) ∧
    ∃ t : ℝ, HasLength w ℓ FilQuot FilSub t ∧ t ≤ (q : ℝ) / 2

def Unramified : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S),
    (∀ s, s = τ) → IsDualDatum a β Fil Fil' →
    Module.finrank C (filSpace Fil τ) = q →
    let H := freeLattice a (p + q)
    DetRel w ℓ (filSpace Fil τ) (flatLattice (r := p + q) a τ 1) (eigenSub (lie H Fil) τ)
      (dualLie β Fil H Fil' τ) 0

def ValuedFieldThreeCases : Prop := TypeOne w ℓ ∧ TypeTwo w ℓ ∧ Unramified w ℓ

end Stmt

def Stmt : Prop :=
  ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ValuedFieldThreeCases w ℓ

noncomputable section Example

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

end Example

end GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference
end

section

open NumberField IsDedekindDomain TensorProduct

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IdeleNormTraceForm

abbrev Af : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

def Zhat : Subring Af where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => (v.adicCompletionIntegers ℚ).mul_mem _ _ (ha v) (hb v)
  one_mem' := fun v => (v.adicCompletionIntegers ℚ).one_mem
  add_mem' := fun {a b} ha hb v => (v.adicCompletionIntegers ℚ).add_mem _ _ (ha v) (hb v)
  zero_mem' := fun v => (v.adicCompletionIntegers ℚ).zero_mem
  neg_mem' := fun {a} ha v => (v.adicCompletionIntegers ℚ).neg_mem _ (ha v)

def ZhatUnits : Subgroup Afˣ := Zhat.toSubmonoid.units

abbrev Adelic (V : Type) [AddCommGroup V] [Module ℚ V] : Type := Af ⊗[ℚ] V

def ideleNorm (K : Type) [Field K] [NumberField K] : (Adelic K)ˣ →* Afˣ :=
  Units.map (Algebra.norm Af : Adelic K →* Af)

def ratIdele : ℚˣ →* Afˣ := Units.map (algebraMap ℚ Af : ℚ →+* Af).toMonoidHom

def IsNormScale {K : Type} [Field K] [NumberField K] (s : (Adelic K)ˣ) (q : ℚˣ) : Prop :=
  0 < (q : ℚ) ∧ (ideleNorm K s)⁻¹ * ratIdele q ∈ ZhatUnits

section Groups

variable (E : Type) [Field E] [NumberField E]
variable {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]

def IsHermitian [IsCMField E] (h : W →ₗ[ℚ] W →ₗ[ℚ] E) : Prop :=
  (∀ (a : E) (x y : W), h (a • x) y = a * h x y) ∧
    ∀ x y : W, h y x = IsCMField.complexConj E (h x y)

def traceForm (ξ₀ : E) (h : W →ₗ[ℚ] W →ₗ[ℚ] E) : LinearMap.BilinForm ℚ W :=
  h.compr₂ (Algebra.trace ℚ E ∘ₗ LinearMap.mulLeft ℚ ξ₀)



variable [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

end Groups

end GlobalTheory.IndefiniteRowSideFullHecke.IdeleNormTraceForm
end
end
