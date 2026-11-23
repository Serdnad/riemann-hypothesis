module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.ZMod.Units

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Glue

open GlobalTheory.KZ GlobalTheory.K5 Polynomial

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

theorem IsNTr.isPrimitiveRoot_zt (ε : Ω →+* ℂ) (l n : ℕ) [NeZero l] : IsPrimitiveRoot (zt ε l n) (l ^ n) := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ ε.injective
  have he : ε (zt ε l n) = Complex.exp (2 * Real.pi * Complex.I / ((l ^ n : ℕ) : ℂ)) := by
    rw [zt, (eOm_props ε ε.injective).1]
    congr 1; push_cast; ring
  rw [he]
  exact Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ (NeZero.ne l))

theorem IsNTr.zt_pow (ε : Ω →+* ℂ) (l m k : ℕ) [NeZero l] : zt ε l (m + k) ^ l ^ k = zt ε l m := by
  have hl : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  apply ε.injective
  rw [map_pow, zt, zt, (eOm_props ε ε.injective).1, (eOm_props ε ε.injective).1, ← Complex.exp_nat_mul]
  congr 1; push_cast; field_simp; ring


open Classical in
theorem IsNTr.card_filter (l n m : ℕ) [hl : Fact l.Prime] (hm : 1 ≤ m) (hmn : m ≤ n) :
    (Finset.univ.filter (fun a : (ZMod (l ^ n))ˣ => (a : ZMod (l ^ n)).val ≡ 1 [MOD l ^ m])).card = l ^ (n - m) := by
  have hd : l ^ m ∣ l ^ n := pow_dvd_pow l hmn
  have hk : (Finset.univ.filter (fun a : (ZMod (l ^ n))ˣ => (a : ZMod (l ^ n)).val ≡ 1 [MOD l ^ m])).card =
      Nat.card (ZMod.unitsMap hd).ker := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    refine Finset.filter_congr fun a _ => ?_
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, Nat.cast_one,
      Units.val_one]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (ZMod.unitsMap hd).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (ZMod.unitsMap_surjective hd)).toEquiv,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := (ZMod (l ^ m))ˣ), ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient, Nat.totient_prime_pow hl.out (by omega), Nat.totient_prime_pow hl.out (by omega), ← hk] at h1
  have hpos : 0 < l ^ (m - 1) * (l - 1) := Nat.mul_pos (pow_pos hl.out.pos _) (by have := hl.out.two_le; omega)
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← h1, mul_right_comm, ← pow_add]
  congr 2; omega

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

end GlobalTheory.Glue
end
end

section

noncomputable section

namespace GlobalTheory.Cyc

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

def IsActC (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) : Prop :=
  (∀ (g : GQ l) (x : Om l), act g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l)) ∧
    ∀ (g : GQ l) (y : PadicComplex l), ‖act g y‖ = ‖y‖

def IsCyc (χ : GQ l →* ℚ_[l]ˣ) : Prop :=
  ∀ (g : GQ l) (m : ℕ) (ζ : Om l), ζ ^ (l ^ m) = 1 →
    ∃ a : ℕ, ‖(χ g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a

def chiC (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g : GQ l) : PadicComplex l :=
  algebraMap ℚ_[l] (PadicComplex l) ((χ g ^ i : ℚ_[l]ˣ) : ℚ_[l])

def Kinf (K : FinExt l) : IntermediateField ℚ_[l] (Om l) :=
  K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x | ∃ j : ℕ, x ^ (l ^ j) = 1}

def Hinf (K : FinExt l) : Subgroup (GQ l) := (Kinf K).fixingSubgroup

def Gj (K : FinExt l) (j : ℕ) : Subgroup (GQ l) := (Ks K j).fixingSubgroup

def Lev (l j : ℕ) : Prop := 1 ≤ j ∧ (l = 2 → 2 ≤ j)

def IsGen (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (j : ℕ) (g : GQ l) : Prop :=
  g ∈ Gj K j ∧ ‖(χ g : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(j : ℤ))

def inC (F : IntermediateField ℚ_[l] (Om l)) : Set (PadicComplex l) :=
  (fun x : Om l => (x : PadicComplex l)) '' (F : Set (Om l))

def intC (F : IntermediateField ℚ_[l] (Om l)) : Set (PadicComplex l) := {y | y ∈ inC F ∧ ‖y‖ ≤ 1}

def Ohat (K : FinExt l) : Set (PadicComplex l) := closure (intC (Kinf K))

def Xlev (K : FinExt l) (i : ℕ) : AddSubgroup (PadicComplex l) :=
  AddSubgroup.closure {z | ∃ ζ y : PadicComplex l, IsPrimitiveRoot ζ (l ^ i) ∧
    y ∈ intC (Ks K (i - 1)) ∧ z = ζ * y}

def Xj (K : FinExt l) (j : ℕ) : AddSubgroup (PadicComplex l) :=
  (⨆ (i : ℕ) (_ : j < i), Xlev K i).topologicalClosure

def rho1 (l : ℕ) : ℝ := (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) - 1))

def twAct (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
    (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (y : Fin r → PadicComplex l) :
    Fin r → PadicComplex l :=
  chiC χ i g • (U g).mulVec (fun a => act g (y a))

def CocOn {X : Type} [AddCommGroup X] [TopologicalSpace X] (G : Subgroup (GQ l)) (A : GQ l → X → X)
    (M : Set X) (c : GQ l → X) : Prop :=
  ContinuousOn c G ∧ (∀ g ∈ G, c g ∈ M) ∧ ∀ g ∈ G, ∀ h ∈ G, c (g * h) = c g + A g (c h)

def CobOn {X : Type} [AddCommGroup X] (G : Subgroup (GQ l)) (A : GQ l → X → X) (M : Set X)
    (c : GQ l → X) : Prop :=
  ∃ x ∈ M, ∀ g ∈ G, c g = A g x - x

def ball (l : ℕ) [Fact l.Prime] (r : ℕ) : Set (Fin r → PadicComplex l) := {y | ∀ a, ‖y a‖ ≤ 1}

def Frame (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m : ℕ) {r : ℕ}
    (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) : Prop :=
  IsGen χ K m g ∧ (∀ a b, ContinuousOn (fun σ => U σ a b) (Gj K m)) ∧
    (∀ σ ∈ Gj K m, ∀ a b, U σ a b ∈ intC (Ks K m)) ∧
    (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, U (σ * τ) = U σ * U τ) ∧ (∀ σ ∈ Hinf K, U σ = 1) ∧
    ∀ a b, ‖(U g - 1) a b‖ < rho1 l

def HTBasis (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (G : Subgroup (GQ l)) {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (J : Set ℤ) : Prop :=
  ∃ (e : Fin r → Fin r → PadicComplex l) (u : Fin r → ℤ), LinearIndependent (PadicComplex l) e ∧
    (∀ k, u k ∈ J) ∧ ∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k

end GlobalTheory.Cyc
end
end
