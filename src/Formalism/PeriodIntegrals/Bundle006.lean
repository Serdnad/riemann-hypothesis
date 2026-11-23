module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace PI

def PrimeLogOverP : Prop :=
  ∀ Y : ℝ, 1 < Y → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y

def PrimeLogOverPSqTail : Prop :=
  ∀ X : ℝ, 0 < X → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X < (p : ℝ)) →
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X

end PI
end

section

namespace PI

section Heis

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def HfG (A : ℝ) (z w : T → I → J → ℂ) : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ)

noncomputable def UG (A : ℝ) (x : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ) : (T → I → J → ℂ) → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * HfG A z x - (Real.pi : ℂ) * HfG A x x / 2)

end Heis

end PI
end

section

open NumberField IsDedekindDomain Module MvPolynomial

noncomputable section

namespace PI.OneCosetSharp

namespace Loc

section Groups

variable (k : Type) [CommRing k] (n c : ℕ)

def atN {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (i : ℕ) : k := if h : i < N then v ⟨i, h⟩ else 0

def eN (N i : ℕ) : Fin N → k := fun l => if l.1 = i then 1 else 0

def supp (N : ℕ) (s : Set ℕ) : Submodule k (Fin N → k) where
  carrier := {v | ∀ l : Fin N, l.1 ∉ s → v l = 0}
  add_mem' := fun {a b} ha hb l hl => by simp [ha l hl, hb l hl]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r a ha l hl => by simp [ha l hl]

def Ufl (i : ℕ) : Submodule k (Fin (n + c) → k) := supp k (n + c) {l | l < n + i}

def inX : (Fin n → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj ⟨l.1, h⟩ else 0

def R1cond (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ i, ∀ v ∈ Ufl k n c i, r v ∈ Ufl k n c i) ∧ r (eN k (n + c) n) = eN k (n + c) n ∧
    ∀ i, r (eN k (n + c) (n + i)) - eN k (n + c) (n + i) ∈ Ufl k n c i

variable {k n c} in
theorem R1cond.mul {r s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hs : R1cond k n c s) :
    R1cond k n c (r * s) := by
  refine ⟨fun i v hv => hr.1 i _ (hs.1 i v hv), ?_, fun i => ?_⟩
  · show r (s _) = _
    rw [hs.2.1, hr.2.1]
  · have h1 := hr.1 i _ (hs.2.2 i)
    have h2 := hr.2.2 i
    have key : (r * s) (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i) =
        r (s (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) +
          (r (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) := by
      show r (s _) - _ = _
      rw [map_sub]
      abel
    rw [key]
    exact Submodule.add_mem _ h1 h2

theorem R1cond_one : R1cond k n c 1 := by
  refine ⟨fun i v hv => hv, rfl, fun i => ?_⟩
  show eN k (n + c) (n + i) - eN k (n + c) (n + i) ∈ _
  rw [sub_self]
  exact Submodule.zero_mem _

def R1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | R1cond k n c r ∧ R1cond k n c r⁻¹}
  one_mem' := ⟨R1cond_one k n c, by rw [inv_one]; exact R1cond_one k n c⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, by rw [mul_inv_rev]; exact hb.2.mul ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

variable {k n c}

end Groups

section Data

variable {k K : Type} [CommRing k] [Field K]

abbrev SF (k K : Type) [CommRing k] (a b : ℕ) : Type := ((Fin a → k) →ₗ[k] (Fin b → k)) → K

def om {a b : ℕ} (mu : k → K) (v : k → ℤ) (sq : K) (g₀ : (Fin a → k) ≃ₗ[k] (Fin a → k))
    (h : (Fin b → k) ≃ₗ[k] (Fin b → k)) (Φ : SF k K a b) : SF k K a b := fun x =>
  mu (LinearEquiv.det g₀ : kˣ) * (mu (LinearEquiv.det h : kˣ))⁻¹ * sq ^ (-(v (LinearEquiv.det g₀ : kˣ)) * b) *
    sq ^ (v (LinearEquiv.det h : kˣ) * a) * Φ (h.symm.toLinearMap ∘ₗ x ∘ₗ g₀.toLinearMap)

variable (n' c' n c : ℕ)

def IsFree (l s : ℕ) : Prop := n' ≤ s ∧ (s - n' = c ∨ (1 ≤ s - n' ∧ (l < n ∨ l - n < s - n')))

instance (l s : ℕ) : Decidable (IsFree n' n c l s) := by unfold IsFree; infer_instance

abbrev FC : Type := {p : Fin (n + c) × Fin (n' + c') // IsFree n' n c p.1.1 p.2.1}

variable {n' c' n c}

def xx1 (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' c' n c → k) : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
    else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
    else if l.1 = n + (s.1 - n') then 1 else 0)

def chArg (x : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range c, atN (x (eN k (n' + c') (n' + i + 1))) (n + i)

def E1 (psi : k → K) (vals : Finset k) (wt : K) (Φ : SF k K (n' + c') (n + c)) : SF k K n' n := fun xj =>
  wt ^ Fintype.card (FC n' c' n c) *
    ∑ t ∈ Fintype.piFinset fun _ : FC n' c' n c => vals, Φ (xx1 xj t) * psi (-chArg (xx1 xj t))

end Data

end Loc

namespace LocE

def fIdx (k₀ c n s : ℕ) : ℕ := if s < k₀ then s else if s < k₀ + c then n + (s - k₀) else s - c

end LocE

open Loc LocE

def chiV {k : Type} [Field k] [DecidableEq k] (χ : kˣ →* ℂˣ) (x : k) : ℂ := if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)

def ent {k : Type} [Field k] {A B : ℕ} (k₀ cA nA cB nB : ℕ) (x : (Fin A → k) →ₗ[k] (Fin B → k)) (p p' : ℕ) : k :=
  atN (x (eN k A (fIdx k₀ cA nA p'))) (fIdx k₀ cB nB p)

def Allow (k₀ m t N p p' : ℕ) : Prop :=
  if p' < k₀ then p < p' ∨ (k₀ ≤ p ∧ p < k₀ + (m / 2 - 1))
  else if p' < k₀ + m - 1 then (k₀ ≤ p ∧ p < p') ∨ (m / 2 < p' + 1 - k₀ ∧ p < k₀)
  else p < k₀ + m - 1 ∨ (p < N ∧ (p - (k₀ + m - 1)) / t ≤ (p' - (k₀ + m - 1)) / t)


open Classical in
def PhiS {k : Type} [Field k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ) : SF k ℂ (n' + (c + 1)) (n + c) := by
  classical
  exact fun x =>
    let M := ent k₀ (c + 1) n' c n x
    let r := k₀ + m - 1
    let a := r + (j - 1) * t
    if (∀ p', p' < r → M p' p' = 1) ∧ (∀ p p', p < n + c → p' < a → p ≠ p' → M p p' ≠ 0 → Allow k₀ m t a p p')
    then ψ₀ (∑ i ∈ Finset.range (r - 1), M i (i + 1)) *
        (∏ i ∈ Finset.range (j - 1),
          chiV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1)))) *
        (chiV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin a => M s.1 s'.1)))⁻¹
    else 0

def InJS {k : Type} [Field k] (k₀ m t c n : ℕ) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ p', p' < k₀ + m - 1 → ent k₀ c n c n κ.toLinearMap p' p' = 1) ∧
    ∀ p p', p < n + c → p' < n + c → p ≠ p' → ent k₀ c n c n κ.toLinearMap p p' ≠ 0 → Allow k₀ m t (n + c) p p'

def OneCosetSharp : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ),
    1 ≤ k₀ → Even m → 4 ≤ m → 1 ≤ j → j ≤ m - 2 → c = m - 1 - j →
    n' + (c + 1) = k₀ + m - 1 + (j - 1) * t → n + c = k₀ + m - 1 + j * t →
    (∀ h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
        (∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
          E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1
            (om (fun _ => 1) (fun _ => 0) 1 (LinearEquiv.refl k _) h (PhiS ψ₀ χ k₀ m t j n' c n)) xj ≠ 0) →
        ∃ ρ ∈ R1 k n c, ∃ κ, InJS k₀ m t c n κ ∧ h = ρ * κ) ∧
    ∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
      E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1 (PhiS ψ₀ χ k₀ m t j n' c n) xj ≠ 0

end PI.OneCosetSharp

end
end

section

open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal

def colW (r n : ℕ) : Fin r × Fin n → (Fin n → ℕ) := fun v => Pi.single v.2 1

def colAddGen (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)

def dualWeyl (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  weightedHomogeneousSubmodule R (colW r n) ν ⊓
    ⨅ (l : Fin n) (j : Fin n) (_ : l < j),
      LinearMap.ker ((colAddGen R (r := r) l j).toLinearMap -
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).toLinearMap)

def rowGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => Polynomial.C (X v) +
    (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)

def rowDiv (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  (rowGen R a b f).coeff k

def lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s =>
    (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)).det

def nuNext {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ :=
  if h : s.val + 1 < n then ν ⟨s.val + 1, h⟩ else 0

def hw (R : Type*) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    MvPolynomial (Fin r × Fin n) R :=
  ∏ s : Fin n, (lpMinor R (s.val + 1) (by omega) (by omega)) ^ (ν s - nuNext ν s)

def applyWord (R : Type*) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  w.foldr (fun x g => rowDiv R x.1 x.2.1 x.2.2 g) f

def weyl (R : Type*) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord R w (hw R hn ν))

def detShift {N : ℕ} (w : Fin N → ℤ) : ℤ := if h : 0 < N then w ⟨N - 1, by omega⟩ else 0

def natW {N : ℕ} (w : Fin N → ℤ) : Fin N → ℕ := fun i => (w i - detShift w).toNat

def delSq (R : Type) [CommRing R] (N : ℕ) (w : Fin N → ℤ) : Submodule R (MvPolynomial (Fin N × Fin N) R) :=
  weyl R N N le_rfl (natW w)

def nuOf {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℕ :=
  fun t => (lam t - lam (Fin.last m)).toNat

def lamAt {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') : Fin (m + 1) → ℤ :=
  if Even s.val then lam0 s else fun i => -lam0 s i.rev

def Frames {ι : Type} {n : ℕ} (_G : ι → Matrix (Fin n) (Fin n) ℂ) : Type :=
  {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}

section Blocks

variable {nV : ℕ} {n' : Fin nV → ℕ} {m : ℕ} {Tau : Type} [Fintype Tau] {n : ℕ}

def reM (h : m + 1 = n) (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  A.submatrix (finCongr h) (finCongr h)

def zAt (h : m + 1 = n) (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau) (M y : Tau → Matrix (Fin n) (Fin n) ℂ)
    (v : Fin nV) (s : Fin (n' v)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  if Even s.val then reM h (M (pos ⟨v, s⟩) * y (pos ⟨v, s⟩))
  else ((reM h (M (pos ⟨v, s⟩) * y (pos ⟨v, s⟩)))⁻¹)ᵀ.submatrix id Fin.rev

def eAt (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) (v : Fin nV) (s : Fin (n' v)) : ℤ :=
  lamAt (lam0 v) s (Fin.last m)

def blkMod (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) (R : Type) [Field R] (v : Fin nV) (s : Fin (n' v)) :
    Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
  if Antitone (lamAt (lam0 v) s) then dualWeyl R (m + 1) (m + 1) (nuOf (lamAt (lam0 v) s)) else ⊥

def WtTie (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) (h : m + 1 = n)
    (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau) (lam : Tau → Fin n → ℤ) : Prop :=
  ∀ v (s : Fin (n' v)) (i : Fin (m + 1)), lam0 v s i = lam (pos ⟨v, s⟩) (finCongr h i)

def BlockRational (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) {LL : Type} [Field LL] (h : m + 1 = n)
    (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau) (G M : Tau → Matrix (Fin n) (Fin n) ℂ)
    (embLL : LL →+* ℂ) (lam : Tau → Fin n → ℤ) : Prop :=
  ∀ v (s : Fin (n' v)) (f : MvPolynomial (Fin n × Fin n) ℤ), f ∈ delSq ℤ n (lam (pos ⟨v, s⟩)) →
    ∃ F ∈ blkMod lam0 LL v s, ∀ y : Frames G,
      (zAt h pos M y.1 v s).det ^ (eAt lam0 v s) *
          eval (fun x => zAt h pos M y.1 v s x.1 x.2) (MvPolynomial.map embLL F) =
        (y.1 (pos ⟨v, s⟩)).det ^ detShift (lam (pos ⟨v, s⟩)) *
          eval (fun x => y.1 (pos ⟨v, s⟩) x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) f)

end Blocks

def Stmt : Prop :=
  ∀ {nV : ℕ} {n' : Fin nV → ℕ} {m : ℕ} (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) {Tau : Type} [Fintype Tau]
    {n : ℕ} {LL : Type} [Field LL] (h : m + 1 = n) (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau)
    (G M : Tau → Matrix (Fin n) (Fin n) ℂ) (embLL : LL →+* ℂ) (lam : Tau → Fin n → ℤ), (∀ τ, Antitone (lam τ)) →
    WtTie lam0 h pos lam → (∀ τ, ∃ M0 : GL (Fin n) LL, M τ = M0.1.map embLL) →
    BlockRational lam0 h pos G M embLL lam

end PI.BlockRatReal
end
end

section

namespace PI

def EmbTraceSum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (φ₀ : E →+* ℂ) (S : Type) [Fintype S]
    (emb : S → E →+* ℂ), Function.Injective emb → (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) →
    Fintype.card S = Module.finrank K E →
    ∀ y : E, ∑ s, emb s y = φ₀ ((Algebra.trace K E y : K) : E)

end PI
end

section

noncomputable section

open Matrix NumberField

namespace PI.FlagGramNonneg

def cT {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)

def HasSignature {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n ℂ) (p q : ℕ) : Prop :=
  ∃ e : n ≃ Fin p ⊕ Fin q, ∃ P : GL (Fin p ⊕ Fin q) ℂ,
    cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * J.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q

def leadMinorE {E : Type} [Field E] {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (l : ℕ) : E := by
  classical
  exact if h : l ≤ N then (A.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def gram {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) : Matrix (Fin N) (Fin N) E :=
  fun i j => hT (b i) (b j)

def IsFlag {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (T : E) (e : Fin r → V) (z : V) : Prop :=
  LinearIndependent E e ∧ (∀ a b, hT (e a) (e b) = 0) ∧ (∀ a, hT (e a) z = 0) ∧ hT z z = -T

def fvec {V : Type} {r : ℕ} (e : Fin r → V) (z : V) : Fin (r + 1) → V :=
  Fin.snoc (α := fun _ => V) e z

def zhat {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (f f' : Fin (r + 1) → V) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun a b => hT (f a) (f' b)

def gval {E : Type} [Field E] [StarRing E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : E :=
  leadMinorE Z (r + 1) * star (leadMinorE Z (r + 1)) - T * T' * (leadMinorE Z r * star (leadMinorE Z r))

end PI.FlagGramNonneg

namespace PI

open PI.FlagGramNonneg

def FlagGramNonneg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (hT : V →ₗ⋆[E] V →ₗ[E] E), hT.IsSymm → hT.Nondegenerate →
    ∀ (N : ℕ) (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ),
    (∀ a, τ (star a) = starRingEnd ℂ (τ a)) →
    ∀ (p r T T' : ℕ), HasSignature ((gram hT b).map τ) p (r + 1) → 0 < T → 0 < T' →
    ∀ (e e' : Fin r → V) (z z' : V), IsFlag hT (T : E) e z → IsFlag hT (T' : E) e' z' →
      ∃ c : ℝ, 0 ≤ c ∧ τ (gval (zhat hT (fvec e z) (fvec e' z')) (T : E) (T' : E)) = c

end PI
end
end

section

open CategoryTheory

namespace PI.CharIdem

variable {G : Type} [Group G] [Fintype G]

noncomputable def charIdem (V : FDRep ℂ G) : MonoidAlgebra ℂ G :=
  ∑ g : G, MonoidAlgebra.single g (((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) * V.character g⁻¹)

noncomputable def act (V : FDRep ℂ G) : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V :=
  MonoidAlgebra.lift ℂ (Module.End ℂ V) G V.ρ

def CharIdem : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V W : FDRep ℂ G), Simple V → Simple W →
    act V (charIdem V) = 1 ∧
    (IsEmpty (V ≅ W) → act W (charIdem V) = 0) ∧
    IsIdempotentElem (charIdem V) ∧
    (∀ x : MonoidAlgebra ℂ G, charIdem V * x = x * charIdem V) ∧
    (IsEmpty (V ≅ W) → charIdem V * charIdem W = 0)

end PI.CharIdem
end

section

namespace PI.ScGapBig

def rk48 (k r : ℕ) : ℕ := 2 * r + k + 1

def GapBig (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ 1801 ≤ rk48 k r + t ∧
    ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j

def ScGapBig : Prop :=
  ∀ (k r : ℕ) (b : Fin (2 * r + 2) → ℝ), 1801 ≤ rk48 k r →
    (∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      16 * (rk48 k r : ℝ) ^ 19 ≤ b ⟨j.val + 1, hj⟩ - b j) →
    GapBig k r b

end PI.ScGapBig
end

section

noncomputable section

namespace PI

def minorX (R : Type) [CommRing R] (N p : ℕ) (I : Fin p ↪o Fin N) : MvPolynomial (ℕ × Fin N) R :=
  Matrix.det (Matrix.of fun i k : Fin p => MvPolynomial.X ((i : ℕ), I k))

def nablaSpan (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram) :
    Submodule R (MvPolynomial (ℕ × Fin N) R) :=
  Submodule.span R (Set.range fun I : ∀ c : Fin (nu.rowLen 0), Fin (nu.colLen c) ↪o Fin N =>
    ∏ c : Fin (nu.rowLen 0), minorX R N (nu.colLen c) (I c))

def MinorSpanCompl : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram),
    ∃ Cm : Submodule R (MvPolynomial (ℕ × Fin N) R), IsCompl (nablaSpan R N nu) Cm

end PI
end
end
