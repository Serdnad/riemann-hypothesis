module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ τ : K}

theorem sigL_mul (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by ext <;> simp [sigL] <;> ring

theorem sigL_sigL (x : EL Δ τ) : sigL (sigL x) = x := by ext <;> simp [sigL]

theorem sigL_one : sigL (1 : EL Δ τ) = 1 := by ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem sigL_star (x : EL Δ τ) : sigL (star x) = star (sigL x) := by ext <;> simp [sigL]

theorem sigL_ofE (x : Etau K τ) : sigL (ofE Δ x) = ofE Δ x := by ext <;> simp [sigL, ofE]

theorem ofE_mul (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by ext <;> simp [ofE]

theorem ofE_one : ofE Δ (1 : Etau K τ) = 1 := by ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem ofE_star (x : Etau K τ) : ofE Δ (star x) = star (ofE Δ x) := by ext <;> simp [ofE]

theorem quo_mul_star (z : (Etau K τ)ˣ) : quo z * star (quo z) = 1 := by
  rw [quo, star_mul', star_star]
  calc _ = ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * star ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
        rw [star_mul']; ring
    _ = 1 := by simp


variable (O) in
def mulE (y : (EL Δ τ)ˣ) : Sp Δ τ ≃ₗ[O] Sp Δ τ where
  toFun x := (x.1, y * x.2)
  invFun x := (x.1, (y⁻¹ : (EL Δ τ)ˣ) * x.2)
  map_add' a b := by simp [mul_add]
  map_smul' a b := by
    refine Prod.ext rfl ?_
    change (y : EL Δ τ) * (a • b.2) = a • ((y : EL Δ τ) * b.2)
    rw [← algebraMap_smul K a b.2, ← algebraMap_smul K a, mul_smul_comm]
  left_inv x := by simp
  right_inv x := by simp

theorem isFix_map {c : K} {d m d' m' : EL Δ τ} (ψ : Sp Δ τ ≃ₗ[O] Sp Δ τ) (h1 : ∀ x y, herm c m (ψ x) (ψ y) = herm c m' x y)
    (h2 : ∀ x, semi d (ψ x) = ψ (semi d' x)) {S : Set (Sp Δ τ)} (h : IsFix O c d' m' S) : IsFix O c d m (ψ '' S) := by
  classical
  refine ⟨?_, fun y => ?_, ?_⟩
  · obtain ⟨s, rfl⟩ := h.fg
    refine ⟨s.image ψ, ?_⟩
    rw [Finset.coe_image, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.map_coe]
  · obtain ⟨y, rfl⟩ := ψ.surjective y
    rw [ψ.injective.mem_set_image, h.dual, Set.forall_mem_image]
    simp only [h1]
  · rw [← Set.image_comp]
    conv_rhs => rw [← h.stab, ← Set.image_comp]
    exact congrArg (· '' S) (funext h2)

theorem isFix_map_iff {c : K} {d m d' m' : EL Δ τ} (ψ : Sp Δ τ ≃ₗ[O] Sp Δ τ) (h1 : ∀ x y, herm c m (ψ x) (ψ y) = herm c m' x y)
    (h2 : ∀ x, semi d (ψ x) = ψ (semi d' x)) (S : Set (Sp Δ τ)) : IsFix O c d m (ψ '' S) ↔ IsFix O c d' m' S := by
  refine ⟨fun h => ?_, isFix_map ψ h1 h2⟩
  have := isFix_map (d := d') (m := m') ψ.symm (fun x y => by rw [← h1]; simp) (fun x => ψ.injective (by rw [← h2]; simp)) h
  rwa [← Set.image_comp, show (ψ.symm ∘ ψ : Sp Δ τ → Sp Δ τ) = id from funext ψ.symm_apply_apply, Set.image_id] at this

theorem isFix_mulE (c : K) (d m : EL Δ τ) (y : (EL Δ τ)ˣ) (S : Set (Sp Δ τ)) : IsFix O c d m ((mulE (O := O) y) '' S) ↔
    IsFix O c (d * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ)) (m * (y : EL Δ τ) * star (sigL (y : EL Δ τ))) S := by
  refine isFix_map_iff _ (fun a b => ?_) (fun a => Prod.ext rfl ?_) S
  · change herm c m (a.1, (y : EL Δ τ) * a.2) (b.1, (y : EL Δ τ) * b.2) = _
    simp only [herm, sigL_mul, star_mul']
    congr 2
    ring
  · change d * sigL ((y : EL Δ τ) * a.2) = (y : EL Δ τ) * (d * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) * sigL a.2)
    rw [sigL_mul]
    linear_combination (-d * sigL (y : EL Δ τ) * sigL a.2) * y.mul_inv

theorem isFix_tor (c : K) (d m : EL Δ τ) (z : (Etau K τ)ˣ) (S : Set (Sp Δ τ)) : IsFix O c d m (tor Δ z '' S) ↔ IsFix O c d m S := by
  have h : ofE Δ (quo z) * star (ofE Δ (quo z)) = 1 := by rw [← ofE_star, ← ofE_mul, quo_mul_star, ofE_one]
  let Y : (EL Δ τ)ˣ := Units.mkOfMulEqOne _ _ h
  have := isFix_mulE (O := O) c d m Y S
  rw [show sigL (Y : EL Δ τ) = Y from sigL_ofE _, mul_assoc d, Units.mul_inv, mul_one, mul_assoc m,
    show (Y : EL Δ τ) * star (Y : EL Δ τ) = 1 from h, mul_one] at this
  exact this

end UpperTheory.V.Z.Sym.Loc
end

section

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra

def dLam {K : Type} [Field K] {Δ τ : K} (lam : Lsq K Δ) (z : (Etau K τ)ˣ) : EL Δ τ :=
  lam • ofE Δ (star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ))

abbrev jU {K : Type} [Field K] {τ : K} (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) : (Etau K τ)ˣ →* GL (Fin 2) K :=
  Units.map (j : Etau K τ →* Matrix (Fin 2) (Fin 2) K)

def LcountNorm : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ t ∈ NE τ, lcount O c d ((t : K) • m) = lcount O c d m

def OrbEq : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)), Models c d m δ ι P →
    uOrb O ι δ = lcount O c d m

def Vanish : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → lcount O c d m ≠ 0 → τ ∈ (algebraMap O K).range ∧ EvenVal O (c * (2 - τ))

def GVanish : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → ∀ (χ : Kˣ →* ℂˣ) (z : (Etau K τ)ˣ), ((z : Etau K τ) = ω ∨ (z : Etau K τ) = 1 + ω) → gOrb O j χ z ≠ 0 → τ ∈ (algebraMap O K).range

def Stable : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → EvenVal O (c * (2 - τ)) → ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → ∀ (χ : Kˣ →* ℂˣ), Unr O χ →
    ∀ a : (Etau K τ)ˣ, (a : Etau K τ) = ω → stabSum O c d m = gOrb O j χ a

def Kappa : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ c : K, EvenVal O (c * (2 - τ)) →
    ∀ lam : Lsq K Δ, QuadraticAlgebra.norm lam = 2 + τ → 2 + τ + QuadraticAlgebra.trace lam ≠ 0 →
    ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (χ : Kˣ →* ℂˣ), (j ω).trace = τ →
    (∀ (x : Kˣ) (x₀ : O), algebraMap O K x₀ = x → (χ x : ℂ) = hs Δ (x : K) / (Nat.card (O ⧸ Ideal.span {x₀}) : ℂ)) →
    kapSum O c (dLam lam z) 1 =
      hs (τ ^ 2 - 4) (2 + τ + QuadraticAlgebra.trace lam) * hs Δ (2 + τ + QuadraticAlgebra.trace lam) * hs (τ ^ 2 - 4) (-c) * gOrb O j χ z

def KappaZero : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → (¬ ∃ lam : Lsq K Δ, QuadraticAlgebra.norm lam = 2 + τ) →
    kapSum O c d m = 0 ∧ ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → ∀ (χ : Kˣ →* ℂˣ) (z : (Etau K τ)ˣ), (z : Etau K τ) = 1 + ω → gOrb O j χ z = 0

def DatLam : Prop :=
  ∀ (K : Type) [Field K] (Δ τ c : K), τ ^ 2 - 4 ≠ 0 → c ≠ 0 → ∀ lam : Lsq K Δ, QuadraticAlgebra.norm lam = 2 + τ →
    ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → IsDat c (dLam lam z) 1

def DatSmul : Prop :=
  ∀ (K : Type) [Field K] (Δ τ c : K) (d m : EL Δ τ), IsDat c d m → ∀ t : Kˣ, IsDat c d ((t : K) • m)

def LocNorm : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ∈ (algebraMap O K).range → ∃ d : EL Δ τ, d * sigL d = ofE Δ (ω : Etau K τ)

def FinU : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)), Models c d m δ ι P →
    ∃ s : Finset (U3 Δ), ∀ y : U3 Δ, y⁻¹ * δ * theta Δ y ∈ KU O Δ → ∃ z, ∃ x ∈ s, ∃ k ∈ KU O Δ, y = ι z * x * k

def StabU : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)), Models c d m δ ι P →
    ∀ y : U3 Δ, ((KU O Δ).comap (MulAut.conj y⁻¹).toMonoidHom).comap ι ≤ Cint O τ ∧
      (((KU O Δ).comap (MulAut.conj y⁻¹).toMonoidHom).comap ι).relIndex (Cint O τ) ≠ 0

def OneU : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)), Models c d m δ ι P →
    δ ∈ KU O Δ → (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) →
    (∀ y : U3 Δ, y⁻¹ * δ * theta Δ y ∈ KU O Δ ↔ ∃ z, ∃ k ∈ KU O Δ, y = ι z * k) ∧ (KU O Δ).comap ι = Cint O τ

def FinG : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → ∀ z : (Etau K τ)ˣ, (z : Etau K τ).im ≠ 0 →
    ∃ s : Finset (GL (Fin 2) K), ∀ y : GL (Fin 2) K, y⁻¹ * jU j z * y ∈ ZK O K → ∃ t, ∃ x ∈ s, ∃ k ∈ ZK O K, y = jU j t * x * k

def StabG : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → ∀ y : GL (Fin 2) K,
    ((ZK O K).comap (MulAut.conj y⁻¹).toMonoidHom).comap (jU j) ≤ Cint O τ ∧
      (((ZK O K).comap (MulAut.conj y⁻¹).toMonoidHom).comap (jU j)).relIndex (Cint O τ) ≠ 0

def OneG : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → (∀ s t, j ω s t ∈ (algebraMap O K).range) → (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) →
    (ZK O K).comap (jU j) = Cint O τ ∧ ∀ z : (Etau K τ)ˣ, ((z : Etau K τ) = ω ∨ (z : Etau K τ) = 1 + ω) →
      jU j z ∈ KG O K ∧ ∀ y : GL (Fin 2) K, y⁻¹ * jU j z * y ∈ ZK O K ↔ ∃ t, ∃ k ∈ ZK O K, y = jU j t * k

def FzkLaw : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∀ χ : Kˣ →* ℂˣ, Unr O χ → (∀ g, g ∉ ZK O K → fZK O χ g = 0) ∧
    ∀ (z : Kˣ), ∀ k ∈ KG O K, fZK O χ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * k) = (((χ z)⁻¹ : ℂˣ) : ℂ)

def HsMul : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∀ D x y : K, D ≠ 0 → x ≠ 0 → y ≠ 0 → hs D (x * y) = hs D x * hs D y

def HsLaw : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    (∀ x y : K, x ≠ 0 → y ≠ 0 → hs x y = hs y x) ∧ (∀ x y : K, EvenVal O x → EvenVal O y → hs x y = 1) ∧
    (∀ D : K, D ≠ 0 → ¬ IsSquare D → ∃ x : K, x ≠ 0 ∧ hs D x = -1) ∧ ∀ D x : K, D ≠ 0 → IsSquare D → hs D x = 1

def HsNE : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ t : Kˣ, t ∈ NE τ ↔ hs (τ ^ 2 - 4) (t : K) = 1

def SplitJ : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∃ P : GL (Fin 2) (Lsq K Δ), (∀ s t, IsInt O ((P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) s t) ∧ IsInt O (((P⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) s t)) ∧
      ∀ X : Matrix (Fin 2) (Fin 2) (Lsq K Δ), !![0, 1; -1, 0] * X.map star = X * !![0, 1; -1, 0] ↔
        ((P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * X * (P⁻¹ : GL (Fin 2) (Lsq K Δ))).map star = (P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * X * (P⁻¹ : GL (Fin 2) (Lsq K Δ))

end UpperTheory.V.Z.Sym.Loc
end
end
