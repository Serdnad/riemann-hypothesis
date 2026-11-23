module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem tval_coe (Q : Polynomial (Qbar l)) {N : ℕ} (hN : Q.natDegree < N) (z : Qbar l) :
    tval (Q : PowerSeries (Qbar l)) N z = Q.eval (z - 1) := by
  rw [Polynomial.eval_eq_sum_range' hN]
  simp only [tval, Polynomial.coeff_coe]

theorem tval_dirac {y N : ℕ} (hN : y < N) (z : Qbar l) : tval ((1 + PowerSeries.X) ^ y) N z = z ^ y := by
  have h : (((1 + Polynomial.X) ^ y : Polynomial (Qbar l)) : PowerSeries (Qbar l)) = (1 + PowerSeries.X) ^ y := by simp
  rw [← h, tval_coe _ (lt_of_le_of_lt _ hN)]
  · simp
  · refine Polynomial.natDegree_pow_le.trans ?_
    rw [add_comm, ← Polynomial.C_1, Polynomial.natDegree_X_add_C, mul_one]

theorem mass_dirac {r : ℕ} {ξ : Qbar l} (hξ : IsPrimitiveRoot ξ (l ^ r)) {x y : ℕ} (hx : x < l ^ r) (hy : y < l ^ r) :
    mass ((1 + PowerSeries.X) ^ y) r ξ x = if x = y then ((l : ℕ) : Qbar l) ^ r else 0 := by
  have h0 : ξ ≠ 0 := hξ.ne_zero (by omega)
  have hy' : y < l ^ (3 * r) := hy.trans_le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos (by omega))
  have e : ∀ k, ξ ^ (l ^ r - (k * x) % l ^ r) * tval ((1 + PowerSeries.X) ^ y) (l ^ (3 * r)) (ξ ^ k) = (ξ ^ y / ξ ^ x) ^ k := by
    intro k
    rw [tval_dirac hy', pow_sub₀ _ h0 (Nat.mod_lt _ (by omega)).le, hξ.pow_eq_one,
      ← pow_eq_pow_mod _ hξ.pow_eq_one, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm x k, mul_comm y k]
    field_simp
  simp only [mass, e]
  split_ifs with h1
  · subst h1; simp [h0]
  · have hne : ξ ^ y / ξ ^ x ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq (pow_ne_zero _ h0)] at h
      exact h1 (hξ.pow_inj hx hy h.symm)
    have := mul_geom_sum (ξ ^ y / ξ ^ x) (l ^ r)
    rw [div_pow, ← pow_mul, ← pow_mul, mul_comm x, mul_comm y, pow_mul, pow_mul, hξ.pow_eq_one, one_pow, one_pow, div_one,
      sub_self] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

end GlobalTheory.KZ
end
end

section

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def AdmissibleNewformZetaData {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l)
    (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
    (ψ : ZMod l → Qbar l) (cf : Coef l) : Prop :=
  1 < c ∧ 1 < d ∧ Nat.Coprime c (6 * l * N) ∧ Nat.Coprime d (6 * l * N) ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
    (∃ δ : ℕ → Qbar l, ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b ∧ pr (X.diam N l q b) = δ q • pr b) ∧
    (∀ r₀ : (ZMod l)ˣ, ∃ t : (ZMod l)ˣ,
      (![0, 1] : Fin 2 → ZMod l) ᵥ* ((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod l))) =
        (t : ZMod l) • ![(r₀ : ZMod l), -1]) ∧
    (∀ r₀ : (ZMod l)ˣ, (N : ℤ) ∣ (gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ∧
    ∃ χ : G ℚ Ω →* (Qbar l)ˣ, KillsMu l χ ∧
      (∀ s ∈ Ine (F := ℚ) A, mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l)) = 1) ∧
      ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)

def AdmWn {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l)
    (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
    (ψ : ZMod l → Qbar l) (cf : Coef l) : Prop :=
  (∀ x, cw x ≠ 0 → AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf) ∧ ∀ x, cw x ∈ cf.O

end GlobalTheory.K4
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def HTPresNuOfPolys (A : ValuationSubring Ω) (c : Coef l) (m c₀ : ℕ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (ζ : Ω)
    {ι : Type} [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) : Prop :=
  IsPrimitiveRoot ζ (l ^ m) ∧ (∀ i, ∀ x ∈ (P i).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ (∀ i, o i ∈ c.O) ∧
    (∀ i, (P i).eval ζ ≠ 0) ∧ GlobalTheory.Col.KumPres A (m - c₀) m (ζ ^ l ^ c₀) (Z m) (fun i => (P i).eval ζ) o

def HTLawCsOfCoef (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (j : Ω →+* Qbar l)
    (m₀ c₀ : ℕ) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l) : Prop :=
  ∃ ζ : ℕ → Ω, (∀ m, IsPrimitiveRoot (ζ m) (l ^ m) ∧ ζ (m + 1) ^ l = ζ m) ∧
    ∀ m, m₀ ≤ m → ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
      HTPresNuOfPolys A c m c₀ Z (ζ m) P o ∧ ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive →
        Cg (m - c₀) (∑ b : (ZMod (l ^ m))ˣ, ψ b * htv j (ζ m) P o (b : ZMod (l ^ m)).val) (Rhs m ψ (j (ζ m)))

def Pin7 (e : ℕ) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (ν : G ℚ Ω → (Qbar l)ˣ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  ∃ (a a' κ : Qbar l) (v : ℕ → Qbar l) (j : Ω →+* Qbar l) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l)
    (L : PowerSeries (Qbar l)) (φ : DirichletCharacter (Qbar l) l) (m₀ c₀ n₀ : ℕ),
    (∀ s ∈ Ine (F := ℚ) A, ν s = 1) ∧ (∃ σ ∈ Dec (F := ℚ) A, IsFrob A l σ ∧ (ν σ : Qbar l) = a) ∧
    ‖a‖ = 1 ∧ ‖a'‖ = 1 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧ κ ≠ 0 ∧ (∀ x ∈ A, ‖j x‖ ≤ 1) ∧
    (∀ n, L.coeff n ∈ c.O) ∧ HTLawCsOfCoef A c Z j m₀ c₀ Rhs ∧
    (∀ m, m₀ ≤ m → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) →
      Cg (m - c₀) (Rhs m ψ z) (v m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) ∧
    (∀ r, 1 ≤ r → ∀ x : (ZMod (l ^ r))ˣ, χ r x = (φ ((x : ZMod (l ^ r)).val : ZMod l))⁻¹) ∧
    ∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) →
      ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
          φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0

end GlobalTheory.KZ
end
end

section

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def IsZetaSystemFixedExponent (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ : ℕ)
    (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∀ r n : ℕ, ∃ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
    (∀ σ ∈ fixMu Ω (topMu l n r N), LiftB X l N (k - 2) n c₀ (clsBmu X l n r N x c d k g σ) (bB σ)) ∧
    ∃ b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
      Cv n (Y r s y) (YfB X l pr W e ψ n r N bB s y +
        (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))

def IsZTc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N l' : ℕ) [NeZero N] [NeZero l'] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ : ℕ)
    (YT : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∀ r n : ℕ, ∃ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
    (∀ σ ∈ fixMu Ω (topMT l n r N l'), LiftB X l N (k - 2) n c₀ (clsBTmu X l n r N l' x c d k g σ) (bB σ)) ∧
    ∃ b : (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
      Cv n (YT r s y) (YfBT X l pr W e ψ n r N l' bB s (y.1 * lsqInv l l' (r + n), y.2) + (rhoK W e ψ s *ᵥ b (y * cycT l r l' s) - b y))

def IsZWc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ : ℕ)
    (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∃ Yx : ZMod N → ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
    (∀ x, IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf c₀ (Yx x)) ∧ ∀ r s y, Y r s y = ∑ x, cw x • Yx x r s y

end GlobalTheory.K4
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.LambdaValuationPowers

namespace GlobalTheory.KummerEisensteinGalois

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def IsLamFR2 (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (χ : ℕ → ℤ_[l]) (j : Ω →+* Qbar l)
    (pr : X.Fn l → Fin 2 → Qbar l) (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  (∀ d : ℕ, Nat.Coprime d N → ∀ b ∈ X.B N l w, pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
    IsLamFR X A N w χ j pr c lam

section Induced

variable {X : Tower Ω ε} {A : ValuationSubring Ω} {N w : ℕ} {χ : ℕ → ℤ_[l]} {j : Ω →+* Qbar l}
  {pr : X.Fn l → Fin 2 → Qbar l} {c : Coef l} {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l}

end Induced

end GlobalTheory.KummerEisensteinGalois

end
end
