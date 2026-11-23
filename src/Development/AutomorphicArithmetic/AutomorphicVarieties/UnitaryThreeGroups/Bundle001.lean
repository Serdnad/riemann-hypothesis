module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

open Matrix UpperTheory.V.U3

private theorem UpperTheory.V.U3.theta_lie_apply {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R)
    (a b : Fin 3) : thetaLie X a b = -X b.rev a.rev := by
  simp only [thetaLie, Matrix.neg_apply, Matrix.mul_apply, Jmat, Matrix.transpose_apply]
  congr 1
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single b.rev]
  · simp
  · intro x _ hx
    rw [if_neg]
    intro h
    exact hx (by rw [h, Fin.rev_rev])
  · simp

theorem UpperTheory.V.U3.adRep_baseLift_apply :
    ∀ {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G) (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
    adRep (r0 η Ψ) g X a b = ((Ψ g ^ wt a b : Rˣ) : R) * (if η g = 1 then X a b else -X b.rev a.rev) := by
  intro G R _ _ η Ψ g X a b
  have hR : (r0 η Ψ g).right = η g := rfl
  have hL : ((r0 η Ψ g).left : Matrix (Fin 3) (Fin 3) R) = diagonal fun i => ((Ψ g ^ wt1 i : Rˣ) : R) := by
    rw [unitaryThreeReflection_left, tor_val]
  have hLi : (((r0 η Ψ g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
      = diagonal fun i => (((Ψ g ^ wt1 i)⁻¹ : Rˣ) : R) := by
    rw [unitaryThreeReflection_left, ← map_inv, tor_val]
    simp only [_root_.inv_zpow]
  have e : adRep (r0 η Ψ) g X
      = (((r0 η Ψ g).left : Matrix (Fin 3) (Fin 3) R) * (if (r0 η Ψ g).right = 1 then X else thetaLie X))
        * (((r0 η Ψ g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := rfl
  rw [e, hR, hL, hLi, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hw : Ψ g ^ wt a b = Ψ g ^ wt1 a * (Ψ g ^ wt1 b)⁻¹ := by
    rw [wt, _root_.zpow_sub]
  rw [hw, Units.val_mul]
  split_ifs with h
  · ring
  · rw [theta_lie_apply]
    ring
end

section

open Matrix UpperTheory.V.U3

theorem UpperTheory.V.U3.mat_gstar :
    ∀ {G R : Type} [Group G] [CommRing R] {m : ℕ} (r : G →* GG (m := m) (R := R)) (c g : G),
      (r c).mat = 1 → (r c).right = -1 → (r g).right = 1 →
      (r (gstar c g)).mat = Jmat (R := R) m * (r g).matᵀ * Jmat (R := R) m ∧
        (r (gstar c g)).right = 1 := by
  intro G R _ _ m r c g h1 h2 h3
  have hc : r c = SemidirectProduct.mk 1 (-1) := by
    apply SemidirectProduct.ext
    · exact Units.ext (by simpa [GG.mat] using h1)
    · exact h2
  have hg : r g = SemidirectProduct.mk (r g).left 1 := SemidirectProduct.ext rfl h3
  have hs : r (gstar c g) = r c * (r g)⁻¹ * r c := by
    simp only [gstar, map_mul, map_inv]
  rw [hs, hc, hg]
  simp only [GG.mat, SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    SemidirectProduct.inv_right, inv_one, map_one, mul_one, one_mul, MulAut.one_apply, map_inv,
    sgnAct_neg_one, theta_inv_val]
  refine ⟨?_, ?_⟩
  · simp
  · norm_num
end

section

namespace UpperTheory.V.U3

open Matrix

section Shape

variable {G : Type*} [Group G] {R : Type*} [CommRing R]

def HasMult {m : ℕ} (η : G →* ℤˣ) (r : G →* GG (m := m) (R := R)) : Prop := ∀ g, (r g).right = η g

def zeta (c g₁ : G) (r : G →* GG (m := 3) (R := R)) : R := zmat c g₁ r 0 0

def MatIrr {m : ℕ} (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) R) : Prop :=
  ∀ W : Submodule R (Fin m → R), (∀ g ∈ H, ∀ v ∈ W, a g *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

def mats {m : ℕ} (r : G →* GG (m := m) (R := R)) (g : G) : Matrix (Fin m) (Fin m) R := (r g).mat

def TypeI (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := R)) : Prop := MatIrr η.ker (mats r)

def Upper (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := R)) : Prop := ∀ g ∈ η.ker, ∀ a b, wt a b < 0 → (r g).mat a b = 0

def Lower (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := R)) : Prop := ∀ g ∈ η.ker, ∀ a b, 0 < wt a b → (r g).mat a b = 0

def Block (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := R)) : Prop := ∀ g ∈ η.ker, ∀ a b, Odd (wt a b) → (r g).mat a b = 0

def corner (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 2) (Fin 2) R := X.submatrix ![0, 2] ![0, 2]

def TypeII (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := R)) : Prop :=
  Block η r ∧ MatIrr η.ker fun g => corner (r g).mat

def Wfun (r : G →* GG (m := 3) (R := R)) (g : G) : Matrix (Fin 2) (Fin 2) R :=
  if (r g).right = 1 then corner (r g).mat else corner (r g).mat * Matrix.diagonal ![-1, 1]

def MatIso {m : ℕ} (H : Subgroup G) (a a' : G → Matrix (Fin m) (Fin m) R) : Prop :=
  ∃ M : GL (Fin m) R, ∀ g ∈ H, (M : Matrix (Fin m) (Fin m) R) * a g = a' g * M

end Shape

section Deform

variable {G : Type*} [Group G] {C : Type*} [CommRing C] {m : ℕ}

def IsCoc (r : G →* GG (m := m) (R := C)) (γ : G → Matrix (Fin m) (Fin m) C) : Prop :=
  ∀ g h, γ (g * h) = γ g + adRep r g (γ h)

def EntIn (I : Ideal C) (X : Matrix (Fin m) (Fin m) C) : Prop := ∀ a b, X a b ∈ I

def IsDeform (r : G →* GG (m := m) (R := C)) (γ : G → Matrix (Fin m) (Fin m) C) (r' : G →* GG (m := m) (R := C)) : Prop :=
  ∀ g, (r' g).right = (r g).right ∧ (r' g).mat = (1 + γ g) * (r g).mat

def zvar (c g₁ : G) (r : G →* GG (m := 3) (R := C)) (γ : G → Matrix (Fin 3) (Fin 3) C) : Matrix (Fin 3) (Fin 3) C :=
  γ g₁ * (r g₁).mat - γ (gstar c g₁) * (r (gstar c g₁)).mat

structure NormCoc (c g₁ : G) (r : G →* GG (m := 3) (R := C)) (γ : G → Matrix (Fin 3) (Fin 3) C) : Prop where
  atc : γ c = 0
  z12 : zvar c g₁ r γ 0 1 = 0
  z21 : zvar c g₁ r γ 1 0 = 0

def cob (r : G →* GG (m := m) (R := C)) (X : Matrix (Fin m) (Fin m) C) (g : G) : Matrix (Fin m) (Fin m) C :=
  X - adRep r g X

def CongOne (I : Ideal C) (h : GL (Fin m) C) : Prop := EntIn I ((h : Matrix (Fin m) (Fin m) C) - 1)

end Deform

structure Marks {G : Type*} [Group G] {k : Type*} [CommRing k] (η : G →* ℤˣ) (Ψ : G →* kˣ) (c g₁ : G) : Prop where
  csq : c * c = 1
  ηc : η c = -1
  Ψc : Ψ c = 1
  ηg : η g₁ = 1
  Ψg : IsUnit (((Ψ g₁ : kˣ) : k) ^ 2 - 1)

theorem hasSimilitudeFactor_diagonalRepr {G : Type*} [Group G] {R : Type*} [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) :
    HasMult η (r0 η Ψ) := fun _ => rfl

theorem baseRepGL3_normalised_of_psi_eq_one {G : Type*} [Group G] {R : Type*} [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ)
    {c : G} (g₁ : G) (hc : Ψ c = 1) : Normalised c g₁ (r0 η Ψ) := by
  refine ⟨?_, ?_, ?_⟩
  · show Matrix.diagonal (fun i => ((Ψ c ^ wt1 i : Rˣ) : R)) = 1
    rw [hc]
    simp
  · show Matrix.diagonal _ 0 1 - Matrix.diagonal _ 0 1 = (0 : R)
    simp
  · show Matrix.diagonal _ 1 0 - Matrix.diagonal _ 1 0 = (0 : R)
    simp

end UpperTheory.V.U3
end

section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

theorem UpperTheory.not_prime_dvd_relIndex_ker_inducedUnitaryRep :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l], l ≠ 2 → ∀ {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* kˣ) (I : Subgroup Γ),
          ¬ l ∣ (I ⊓ (r0 η Ψ).ker).relIndex I := by
  intro l _ k _ _ _ hl2 Γ _ η Ψ I
  haveI := Fintype.ofFinite k
  have hp : l.Prime := Fact.out
  obtain ⟨n, -, hcard⟩ := FiniteField.card k l
  let φ : Γ →* kˣ × ℤˣ := Ψ.prod η
  let ψ : kˣ × ℤˣ →* GG (m := 3) (R := k) := r0 (MonoidHom.snd kˣ ℤˣ) (MonoidHom.fst kˣ ℤˣ)
  have hle : (φ.domRestrict I).ker ≤ ((r0 η Ψ).domRestrict I).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    show ψ (φ.domRestrict I g) = 1
    rw [hg, map_one]
  have h1 : (I ⊓ (r0 η Ψ).ker).relIndex I ∣ (φ.domRestrict I).ker.index := by
    rw [inf_comm, Subgroup.inf_relIndex_right, Subgroup.relIndex, ← MonoidHom.ker_restrict]
    exact Subgroup.index_dvd_of_le hle
  have h2 : (φ.domRestrict I).ker.index ∣ (Nat.card k - 1) * 2 := by
    rw [Subgroup.index_ker]
    have hd := Subgroup.card_subgroup_dvd_card (φ.domRestrict I).range
    rwa [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card (α := ℤˣ),
      Fintype.card_units_int] at hd
  rw [Nat.card_eq_fintype_card, hcard] at h2
  intro hdvd
  have h3 := dvd_trans hdvd (dvd_trans h1 h2)
  rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
  · have h5 : l ∣ l ^ (n : ℕ) := dvd_pow_self l n.ne_zero
    have hpos : 1 ≤ l ^ (n : ℕ) := Nat.one_le_pow _ _ hp.pos
    have he : l ^ (n : ℕ) = (l ^ (n : ℕ) - 1) + 1 := by omega
    rw [he] at h5
    have h6 := (Nat.dvd_add_right h4).mp h5
    exact hp.one_lt.ne' (Nat.dvd_one.mp h6)
  · have h7 := Nat.le_of_dvd (by norm_num) h4
    have h8 := hp.two_le
    omega
end
