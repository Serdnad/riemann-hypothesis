module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle115
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem xs_cast {d M : ℕ} [NeZero M] (h : d ∣ M) (z : ZMod M) :
    ((z.val : ℕ) : ZMod d) = ZMod.castHom h (ZMod d) z := by
  rw [ZMod.castHom_apply, ZMod.natCast_val]

private theorem xs_eval {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (k k' : ℤ_[l]) (a : X.Khat l) (h : PadicInt.toZModPow n k = PadicInt.toZModPow n k') :
    AdicCompletion.eval (idl l) (X.Kl l) n (k • a - k' • a) = 0 := by
  have h1 : k - k' ∈ (idl l) ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]
  rw [← sub_smul, map_smul]
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n a)
  rw [← hv, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul h1 Submodule.mem_top

private theorem xs_cD (N M₀ M : ℕ) [NeZero N] [NeZero M] (hM : M = N * M₀) (c : ZMod M)
    (m : Matrix (Fin 2) (Fin 2) (ZMod M)) (h : ((m 1 0).val : ZMod N) = 0) :
    cD N M₀ (c • m) = ((c.val : ℕ) : ZMod M₀) • cD N M₀ m := by
  have hM₀ : M₀ ∣ M := ⟨N, by rw [hM, mul_comm]⟩
  have key : ∀ z : ZMod M, ((c * z).val : ZMod M₀) = (c.val : ZMod M₀) * (z.val : ZMod M₀) := by
    intro z
    rw [xs_cast hM₀, xs_cast hM₀, xs_cast hM₀, map_mul]
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h10 : (c * m 1 0).val / N = c.val * q % M₀ := by
    rw [ZMod.val_mul, hq]
    generalize c.val = cv
    rw [hM, mul_left_comm, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ hN]
  have hq' : (m 1 0).val / N = q := by
    rw [hq, Nat.mul_div_cancel_left _ hN]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Nat.cast_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
    ring
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, h10, hq', ZMod.natCast_mod, Nat.cast_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]

private theorem xs_Cnd (l N M : ℕ) [Fact l.Prime] [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g : SL(2, ℤ)) (ν : (ZMod M)ˣ)
    (hν : ((ν : ZMod M).val : ZMod N) = 1) (m : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    Cnd l N g ((ν : ZMod M) • m) ↔ Cnd l N g m := by
  have key : ∀ z : ZMod M, (((ν : ZMod M) * z).val : ZMod N) = (z.val : ZMod N) := by
    intro z
    rw [xs_cast hN, xs_cast hN, map_mul, ← xs_cast hN, hν, one_mul]
  have key' : ∀ z : ZMod M, (((ν : ZMod M) * z).val : ZMod l) = ZMod.castHom hl (ZMod l) (ν : ZMod M) * (z.val : ZMod l) := by
    intro z
    rw [xs_cast hl, xs_cast hl, map_mul]
  have hu : IsUnit (ZMod.castHom hl (ZMod l) (ν : ZMod M)) := (ν.isUnit).map _
  simp only [Cnd, Matrix.smul_apply, smul_eq_mul, key, key']
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [mul_left_comm, mul_left_comm (↑(en g 0 0) : ZMod l)]
  exact hu.mul_right_inj

private theorem xs_sum {R ι A B : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (L : A →ₗ[R] B) (e : ι ≃ ι) (s t : Finset ι) (f g : ι → A) (h : ∀ i, i ∈ s ↔ e i ∈ t)
    (h' : ∀ i ∈ s, L (f i - g (e i)) = 0) : L (∑ i ∈ s, f i - ∑ i ∈ t, g i) = 0 := by

  rw [← Finset.sum_equiv e (t := t) (g := g) h (fun _ _ => rfl), ← Finset.sum_sub_distrib, map_sum]
  exact Finset.sum_eq_zero h'

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sXiScal :
    UpperTheory.V.Z.Kato.Nb.SXiScal := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL x y P a ν hν
  have hM := hL.eq
  have hNM : N ∣ M := ⟨M₀, hM⟩
  have hM₀M : M₀ ∣ M := ⟨N, by rw [hM, mul_comm]⟩
  have hlM₀ : l ^ n ∣ M₀ := hL.dl
  have hlM : l ∣ M := (dvd_pow_self l (by have := hL.pos; omega)).trans (hlM₀.trans hM₀M)
  have hlnM : l ^ n ∣ M := hlM₀.trans hM₀M
  let U : GL (Fin 2) (ZMod M) := Units.map (Matrix.scalar (Fin 2) : ZMod M →+* Matrix (Fin 2) (Fin 2) (ZMod M)).toMonoidHom ν
  have hU : ∀ m : GL (Fin 2) (ZMod M), ((U * m : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = (ν : ZMod M) • (m : Matrix _ _ _) := by
    intro m
    ext i j
    simp [U]
  have hdet : ∀ m : GL (Fin 2) (ZMod M), Matrix.GeneralLinearGroup.det (U * m) = ν ^ 2 * Matrix.GeneralLinearGroup.det m := by
    intro m
    ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hU, Matrix.det_smul, Fintype.card_fin]
  unfold CgF
  intro u
  simp only [Xi, Pi.smul_apply, Finset.smul_sum, smul_smul]
  refine xs_sum (AdicCompletion.eval (idl l) (X.Kl l) n) (Equiv.mulLeft U) _ _ _ _ ?_ ?_
  · intro m
    have hP : ν ^ 2 * Matrix.GeneralLinearGroup.det m * ν⁻¹ ^ 2 = Matrix.GeneralLinearGroup.det m := by
      rw [inv_pow, mul_right_comm, mul_inv_cancel, one_mul]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulLeft, hU, hdet, hP, xs_Cnd l N M hNM hlM g ν hν]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    simp only [Equiv.coe_mulLeft, hU, hdet]
    rw [xs_cD N M₀ M hM _ _ hm.1.1, Matrix.vecMul_smul, Matrix.vecMul_smul, Matrix.smul_vecMul, Matrix.smul_vecMul]
    apply xs_eval
    simp only [map_mul, map_pow, map_add (f := _), map_natCast, Matrix.smul_apply, smul_eq_mul, xs_cast hlnM]
    rw [mul_inv, Units.val_mul, map_mul, ← inv_pow, Units.val_pow_eq_pow_val, map_pow]
    have hee : ZMod.castHom hlnM (ZMod (l ^ n)) (ν : ZMod M) * ZMod.castHom hlnM (ZMod (l ^ n)) ((ν⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    set e := ZMod.castHom hlnM (ZMod (l ^ n)) (ν : ZMod M)
    set e' := ZMod.castHom hlnM (ZMod (l ^ n)) ((ν⁻¹ : (ZMod M)ˣ) : ZMod M)
    rw [mul_assoc e, mul_assoc e, ← mul_add, mul_pow]
    set D := ZMod.castHom hlnM (ZMod (l ^ n)) ((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ)
    set A := ZMod.castHom hlnM (ZMod (l ^ n)) ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 0) * PadicInt.toZModPow n (u 0) + ZMod.castHom hlnM (ZMod (l ^ n)) ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1)
    linear_combination (-(e ^ w * D * A ^ w * (e * e' + 1))) * hee
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb

def Rel {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l)
    (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (N : ℕ) (cf : Coef l) (c n : ℕ) {T : Type} [Mul T] (κ : (Ω ≃ₐ[ℚ] Ω) → T)
    (Y : (Ω ≃ₐ[ℚ] Ω) → T → Fin 2 → Qbar l) (z : (Ω ≃ₐ[ℚ] Ω) → T → X.Fn l) : Prop :=
  ∃ (β : (Ω ≃ₐ[ℚ] Ω) → T → X.Fn l) (b : T → Fin 2 → Qbar l), (∀ s y, LiftB X l N (2 * e - 1) n c (z s y) (β s y)) ∧
    (∀ y i, b y i ∈ cf.O) ∧ ∀ s y, Cv n (Y s y) (pr (β s y) + (rhoK W e ψ s *ᵥ b (y * κ s) - b y))

def eul (l : ℕ) [Fact l.Prime] (e p : ℕ) (a δ : Qbar l) : Qbar l := 1 - a * ((p : Qbar l) ^ (e + 1))⁻¹ + δ * ((p : Qbar l) ^ 2)⁻¹

def SRel0 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (c₀ : ℕ) Y, IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y → ∀ r n : ℕ,
    Rel X l pr W e ψ N cf c₀ n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (Y r) fun s y => ∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) s y

def SRelT : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (p : ℕ) [NeZero p], Nat.Coprime p l → ∀ (c₀ : ℕ) Y, IsZTc X l pr W e ψ N p x c d (2 * e + 1) gm cf c₀ Y → ∀ r n : ℕ,
    Rel X l pr W e ψ N cf c₀ n (kT l r p) (Y r) fun s y => ∑ r₀, YT X l n r N p x c d (2 * e - 1) (gm r₀) s y

def SN2rho : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → ∃ m : ℕ, ∀ (p : ℕ) [NeZero p], p.Prime → Nat.Coprime p (l * N) → ∀ a δ : Qbar l, a ∈ cf.O → δ ∈ cf.O →
    (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeT N l p b) = a • pr b ∧ pr (X.diam N l p b) = δ • pr b) →
    ∀ (c₀ c₁ r n : ℕ) (Y : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (Y' : (Ω ≃ₐ[ℚ] Ω) → (ZMod p)ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) z z',
      Rel X l pr W e ψ N cf c₀ n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) Y z → Rel X l pr W e ψ N cf (c₀ + c₁) n (kT l r p) Y' z' →
      CohB X l N (2 * e - 1) n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (fun s y => (p : ℤ_[l]) • ∑ t, z' s (t, y))
        (fun s y => (p : ℤ_[l]) • z s y - X.heckeT N l p (z s (y * inv1 (l ^ r) p)) +
          (p : ℤ_[l]) ^ (2 * e - 1) • X.diam N l p (z s (y * inv1 (l ^ r) p ^ 2))) →
      ∃ b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
        Cv n ((((l : ℕ) : Qbar l) ^ m * (p : Qbar l)) • ∑ t, Y' s (t, y))
          (((l : ℕ) : Qbar l) ^ (m + c₁) • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
            ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
            (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))

def SInteg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → (∀ s : G ℚ Ω, ‖thK l e ψ s‖ = 1) ∧ ψ 1 = 1 ∧ (∀ u v : (ZMod l)ˣ, ψ ((u * v : (ZMod l)ˣ) : ZMod l) = ψ u * ψ v) ∧
    (∀ u : (ZMod l)ˣ, ψ u ∈ cf.O) ∧ (∀ s i k, rhoK W e ψ s i k ∈ cf.O) ∧ (∀ s t, rhoK W e ψ (s * t) = rhoK W e ψ s * rhoK W e ψ t) ∧
    ∀ (c₀ : ℕ) Y, IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y → ∀ r s y i, ‖Y r s y i‖ ≤ 1

def SSpec : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → ∀ (p r : ℕ), p.Prime → l ∣ p - 1 → ∀ (a δ k : Qbar l), ‖a‖ ≤ 1 → ‖δ‖ ≤ 1 → ‖k‖ ≤ 1 →
    ∀ (Y V : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), (∀ s y i, ‖Y s y i‖ ≤ 1) → (∀ y i, b y i ∈ cf.O) →
      (∀ s y, Cv r ((p : Qbar l) • V s y) (k • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
          ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))) →
      ∃ b' : Fin 2 → Qbar l, (∀ i, b' i ∈ cf.O) ∧ ∀ s, Cv r (spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) V s)
        (eul l e p a δ • (k • spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) Y s) + (mat W s *ᵥ b' - b'))

def SDetChar : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (χ : G ℚ Ω →* (Qbar l)ˣ),
    Continuous ρ → Continuous χ → (∃ s, ∀ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) ≠ t • 1) → ∀ S : Finset ℕ,
    (∀ (v : Pl) (B : ValuationSubring Ω) (σ : G ℚ Ω), normV v ∉ S → IsPlaceOver B v → IsFrob B (normV v) σ → ∃ a : Qbar l,
      (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)) ^ 2 - a • (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)) + (χ σ : Qbar l) • 1 = 0) →
    ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s

def SDiamChar : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → Nat.Coprime l N → (∃ b ∈ X.B N l (2 * e - 1), pr b ≠ 0) → ∃ δ : (ZMod N)ˣ →* (Qbar l)ˣ, ∀ (q : ℕ) (u : (ZMod N)ˣ), q.Prime → ¬ q ∣ l * N →
    (u : ZMod N) = q → ∀ b ∈ X.B N l (2 * e - 1), pr (X.diam N l q b) = (δ u : Qbar l) • pr b

def SEuler : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → Nat.Coprime l N → ∀ S : Finset Pl, Nf e S A W → (∀ s i k, mat W s i k ∈ cf.O) → ∃ S' : Finset Pl, S ⊆ S' ∧ ∀ w : Pl, w ∉ S' →
    (normV w).Prime ∧ Nat.Coprime (normV w) (l * N * c * d) ∧ ∃ a δ : Qbar l, a ∈ cf.O ∧ δ ∈ cf.O ∧
      (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeT N l (normV w) b) = a • pr b ∧ pr (X.diam N l (normV w) b) = δ • pr b) ∧
      ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ →
        eps l σ = (normV w : Qbar l) ∧ (rhoK W e ψ σ).trace = a ∧ (rhoK W e ψ σ).det = (normV w : Qbar l) ^ (2 * e) * δ

def SEulCg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (p n : ℕ), p.Prime → 1 ≤ n → l ^ n ∣ p - 1 → ∀ a δ : Qbar l, a ∈ cf.O → δ ∈ cf.O → eul l e p a δ ∈ cf.O ∧
    ∀ σ : G ℚ Ω, ψ 1 = 1 → eps l σ = (p : Qbar l) → (rhoK W e ψ σ).trace = a → (rhoK W e ψ σ).det = (p : Qbar l) ^ (2 * e) * δ →
      Cg n (eul l e p a δ) (1 * (mat W σ - 1).det)

def SPushPsi : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (cf : Coef l) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (p n : ℕ) [NeZero p] (ψw : G ℚ Ω →* Multiplicative (ZMod (l ^ n))), KillsMu p ψw →
    ∀ Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod p)ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
      (∀ r s s' y, Y r (s * s') y = Y r s y + ρ s *ᵥ Y r s' (y * cycT l r p s)) →
      (∀ r, Y r = GlobalTheory.KA.push (Prod.map id (redL l r)) (Y (r + 1))) → (∀ r y i, Continuous fun s => Y r s y i) → (∀ r s u i, Y r s u i ∈ cf.O) →
      ∃ Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
        (∀ r, ShCoc ρ (ψw.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) ∧ (∀ r x i, Continuous fun s => Yw r s x i) ∧ (∀ r s x i, Yw r s x i ∈ cf.O) ∧
        (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) ∧
        ∀ r s y, ∑ a, Yw r s (a, y) = ∑ t, Y r s (t, y)

def KatoTameRelationProjected : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
  (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
  (ψ : ZMod l → Qbar l) (cf : Coef l) (S : Finset Pl),
  Nf e S A W → (∀ s i k, mat W s i k ∈ cf.O) → (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e → (∃ x, cw x ≠ 0) →
  (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → AdmWn ι e gN A W X pr N cw c d gm ψ cf →
  ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y →
  ∃ (k : ℕ) (S' : Finset Pl), (∀ w : Pl, w ∉ S' → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) ∧
  ∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψw : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
    KillsMu (normV w) ψw → Function.Surjective ψw →
    ∃ (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (P u : Qbar l)
      (b : ℕ → Fin 2 → Qbar l),
      (∀ r, ShCoc (rhoK W e ψ) (ψw.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) ∧ (∀ r x i, Continuous fun s => Yw r s x i) ∧
      (∀ r s x i, Yw r s x i ∈ cf.O) ∧
      (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) ∧
      P ∈ cf.O ∧ ‖u‖ = 1 ∧ (∀ r i, b r i ∈ cf.O) ∧
      (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) (fun s x => Yw r s (a, x)) s) i -
          (P • (((l : ℕ) : Qbar l) ^ k • spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) (Y r) s) + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
      (∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ → Cg n P (u * (mat W σ - 1).det))

end UpperTheory.V.Z.Kato.Nb

end
end

section

noncomputable section

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

theorem sCls : SCls := by
  intro Ω _ _ _ ε X l _ n
  obtain ⟨hsurj, hinj, hmul, hone, hsmul, hmap, hsucc⟩ := H3.cls_props Ω ε X l n
  have hdiv : ∀ f f' : X.Kˣ, X.cls l n (f / f') = X.cls l n f - X.cls l n f' := by
    intro f f'
    have h := hmul (f / f') f'
    rw [div_mul_cancel] at h
    rw [h]
    abel
  have hpow : ∀ (f : X.Kˣ) (k : ℕ), X.cls l n (f ^ k) = k • X.cls l n f := by
    intro f k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ, hmul, ih, succ_nsmul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    have hf : (f : X.K) ≠ 0 := f.ne_zero
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (clsK X l n (f : X.K)) = X.cls l n f
    unfold clsK
    rw [dite_eq_left hf, Units.mk0_val]
    unfold liftK
    exact Classical.epsilon_spec (p := fun b => (AdicCompletion.eval (idl l) (X.Kl l) n) b = X.cls l n f)
      (AdicCompletion.eval_surjective (idl l) (X.Kl l) n (X.cls l n f))
  · intro f f' a a' ha ha'
    refine ⟨?_, ?_⟩
    · show (AdicCompletion.eval (idl l) (X.Kl l) n) (a + a') = X.cls l n (f * f')
      rw [map_add (f := _), hmul]
      rw [ha, ha']
    · show (AdicCompletion.eval (idl l) (X.Kl l) n) (a - a') = X.cls l n (f / f')
      rw [map_sub, hdiv]
      rw [ha, ha']
  · intro f a k ha
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ k)
    rw [map_nsmul, hpow]
    rw [ha]
  · intro f f' a a' ha ha' hc
    obtain ⟨g, hg⟩ := hc
    rw [map_sub]
    rw [ha, ha', (hinj f f').2 ⟨g, hg⟩, sub_self]
  · intro φ f a ha
    exact hmap φ a f ha
  · intro f a ha
    exact hsucc a f ha
  · intro f k a ha
    refine ⟨((PadicInt.toZModPow n) k).val, ?_⟩
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ ((PadicInt.toZModPow n) k).val)
    rw [map_smul]
    rw [ha, hsmul]

end UpperTheory.V.Z.Kato.Nb

end
end
