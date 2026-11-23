module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle047
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle003
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
public import Lean.Meta.ExprDefEq
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem cols_zero {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (A W : Matrix (Fin n) (Fin n) O) (al : Fin n → O)
    (ha : Function.Injective al) (h : A * W = W * diagonal al) (h1 : W *ᵥ (fun _ => 1) = 0) : W = 0 := by
  have hk : ∀ k : ℕ, W *ᵥ (fun j => al j ^ k) = 0 := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      have e : (fun j => al j ^ (k + 1)) = diagonal al *ᵥ (fun j => al j ^ k) := by
        funext j
        rw [mulVec_diagonal, pow_succ']
      rw [e, mulVec_mulVec, ← h, ← mulVec_mulVec, ih, mulVec_zero]
  have hv : W * vandermonde al = 0 := by
    ext i k
    have := congrFun (hk k) i
    simpa [Matrix.mul_apply, vandermonde_apply, mulVec, dotProduct] using this
  have hd : (vandermonde al).det ≠ 0 := det_vandermonde_ne_zero_iff.mpr ha
  have h2 : W * vandermonde al * adjugate (vandermonde al) = 0 := by rw [hv, Matrix.zero_mul]
  rw [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
  exact (smul_eq_zero.mp h2).resolve_left hd

private theorem exists_cyc {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O)
    (ha : Function.Injective al) (hc : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i))) :
    ∃ v : Fin n → O, ∀ Y : Matrix (Fin n) (Fin n) O, A * Y = Y * A → Y *ᵥ v = 0 → Y = 0 :=
  _root_.UpperTheory.Reformulated.B.ExistsCyclic.exists_cyc A al ha hc

private theorem red_mul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_sub' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A - B) = red m A - red m B :=
  _root_.UpperTheory.Reformulated.B.OmegaConstruction.red_sub m A B

theorem UpperTheory.V.Th.h0qO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (σ : G0.G₀) (al : Fin n → O), Function.Injective al → (mat y.ρ σ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → ∃ C : ℕ, ∀ m, {Y : Mm O n m | y.ρ0 m σ * Y * y.ρ0 m σ⁻¹ = Y}.ncard ≤ Nat.card (ResidueField O) ^ (m * n + C) := by
  intro l _ L G0 O _ _ _ hO _ n y σ al ha hc
  obtain ⟨v, hv⟩ := exists_cyc _ al ha hc
  let Φ : Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O :=
    (LinearMap.mulRight O (mat y.ρ σ⁻¹)).comp (LinearMap.mulLeft O (mat y.ρ σ)) - LinearMap.id
  have hΦ : ∀ Y, Φ Y = mat y.ρ σ * Y * mat y.ρ σ⁻¹ - Y := fun _ => rfl
  obtain ⟨C, hC⟩ := fixCnt l O n Unit (fun _ => Φ)
  have hinv : mat y.ρ σ⁻¹ * mat y.ρ σ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hr : Module.finrank O (⨅ _ : Unit, LinearMap.ker Φ : Submodule O (Matrix (Fin n) (Fin n) O)) ≤ n := by
    let f : (⨅ _ : Unit, LinearMap.ker Φ : Submodule O (Matrix (Fin n) (Fin n) O)) →ₗ[O] (Fin n → O) :=
      { toFun := fun Y => Y.1 *ᵥ v
        map_add' := fun a b => by simp [add_mulVec]
        map_smul' := fun c a => by simp [smul_mulVec] }
    have hf : Function.Injective f := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro Y e
      apply Subtype.ext
      refine hv Y.1 ?_ e
      have h1 : Φ Y.1 = 0 := (Submodule.mem_iInf _).mp Y.2 ()
      rw [hΦ, sub_eq_zero] at h1
      calc mat y.ρ σ * Y.1 = mat y.ρ σ * Y.1 * mat y.ρ σ⁻¹ * mat y.ρ σ := by
            rw [Matrix.mul_assoc _ _ (mat y.ρ σ), hinv, Matrix.mul_one]
        _ = _ := by rw [h1]
    simpa using LinearMap.finrank_le_finrank_of_injective hf
  refine ⟨C, fun m => ?_⟩
  have hs : {Y : Mm O n m | y.ρ0 m σ * Y * y.ρ0 m σ⁻¹ = Y} =
      {Y : Mm O n m | ∃ Y', red m Y' = Y ∧ ∀ _ : Unit, red m (Φ Y') = 0} := by
    ext Y
    constructor
    · intro hY
      choose Y' hY' using fun i j => Ideal.Quotient.mk_surjective (Y i j)
      have e : red m (Matrix.of Y') = Y := by
        ext i j
        exact hY' i j
      refine ⟨Matrix.of Y', e, fun _ => ?_⟩
      rw [hΦ, red_sub', red_mul', red_mul', e]
      exact sub_eq_zero.mpr hY
    · rintro ⟨Y', e, h⟩
      have h1 := h ()
      rw [hΦ, red_sub', red_mul', red_mul', e] at h1
      exact sub_eq_zero.mp h1
  rw [hs]
  refine (hC m).trans ?_
  obtain ⟨-, hfin, -⟩ := hO
  exact Nat.pow_le_pow_right Nat.card_pos (Nat.add_le_add_right (Nat.mul_le_mul_left m hr) C)
end

section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem cases_c {l : ℕ} [Fact l.Prime] (F : GFrame l) (γ : F.Γ) :
    (∃ g : F.G₀, γ = g) ∨ ∃ g : F.G₀, γ = g * F.c := by
  by_cases h : γ ∈ F.η.ker
  · exact Or.inl ⟨⟨γ, h⟩, rfl⟩
  · refine Or.inr ⟨⟨γ * F.c, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker] at h ⊢
      rw [map_mul, F.η_c, (Int.units_eq_one_or (F.η γ)).resolve_left h]
      simp
    · show γ = γ * F.c * F.c
      rw [mul_assoc, F.c_sq, mul_one]

private theorem tr_c {R : Type} [CommRing R] {n : ℕ} (P Q X Y A B : Matrix (Fin n) (Fin n) R) (e : R) (h1 : Q * P = 1) (h2 : P * Q = 1)
    (hA : P * A = -((1 : R) • (Xᵀ * P))) (hB : P * B = -(e • (Yᵀ * P))) : (A * B).trace = e * (X * Y).trace := by
  have a : A = -(Q * Xᵀ * P) := by
    rw [← Matrix.one_mul A, ← h1, Matrix.mul_assoc, hA, one_smul, Matrix.mul_neg, Matrix.mul_assoc]
  have b : B = -(e • (Q * Yᵀ * P)) := by
    rw [← Matrix.one_mul B, ← h1, Matrix.mul_assoc, hB, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_assoc]
  have c : Q * Xᵀ * P * (Q * Yᵀ * P) = Q * (Xᵀ * Yᵀ * P) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P Q, h2, Matrix.one_mul]
  rw [a, b, neg_mul_neg, Matrix.mul_smul, c, trace_smul, smul_eq_mul, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one,
    ← transpose_mul, trace_transpose, trace_mul_comm]

private theorem tr_g {R : Type} [CommRing R] {n : ℕ} (a a' X Y : Matrix (Fin n) (Fin n) R) (e : R) (h1 : a' * a = 1) :
    (((1 : R) • (a * X * a')) * (e • (a * Y * a'))).trace = e * (X * Y).trace := by
  have c : a * X * a' * (a * Y * a') = a * (X * Y * a') := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc a' a, h1, Matrix.one_mul]
  rw [one_smul, Matrix.mul_smul, c, trace_smul, smul_eq_mul, trace_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) : red m (1 : Matrix (Fin n) (Fin n) O) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem UpperTheory.V.Th.pairP :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ), G.ε G.c = -1 → ∃ (k : ℕ) (b : Mm O n m →+ Mm O n m →+ ZMod (l ^ k)), 0 < k ∧ ∀ rep rep', IsAd0 h y m rep → IsAd1 h y m rep' → DualPair k G.ε rep rep' b := by
  intro l _ L G G0 h O _ _ _ _ _ n y m hc
  obtain ⟨k, τ, hk, hnd, hlin⟩ := pairO l O m
  let b : Mm O n m →+ Mm O n m →+ ZMod (l ^ k) :=
    { toFun := fun X =>
        { toFun := fun Y => τ (X * Y).trace
          map_zero' := by simp
          map_add' := fun Y Y' => by rw [Matrix.mul_add, trace_add, map_add (f := _)] }
      map_zero' := by ext Y; simp
      map_add' := fun X X' => by ext Y; simp [Matrix.add_mul] }
  have hb : ∀ X Y, b X Y = τ (X * Y).trace := fun _ _ => rfl
  have hl : ∀ X : Mm O n m, (∀ Y, b X Y = 0) → X = 0 := fun X hX => by
    ext i j
    refine hnd _ fun z => ?_
    have := hX (Matrix.single j i z)
    rw [hb, Matrix.trace_mul_single] at this
    simpa [mul_comm] using this
  refine ⟨k, b, hk, fun rep rep' hr hr' => ⟨hl, fun Y hY => hl Y fun X => by rw [hb, trace_mul_comm]; exact hY X, ?_⟩⟩
  have hg : ∀ (g : G.G₀) X Y, b (rep g X) (rep' g Y) = PadicInt.toZModPow k ((G.ε g : ℤ_[l]ˣ) : ℤ_[l]) * b X Y := by
    intro g X Y
    have e : y.ρm h m g⁻¹ * y.ρm h m g = 1 := by
      show red m _ * red m _ = 1
      rw [← red_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, red_one]
    rw [hb, hr.1 g X, hr'.1 g Y, tr_g _ _ _ _ _ e, hb]
    exact hlin _ _
  have hcc : ∀ X Y, b (rep G.c X) (rep' G.c Y) = PadicInt.toZModPow k ((G.ε G.c : ℤ_[l]ˣ) : ℤ_[l]) * b X Y := by
    intro X Y
    have e1 : red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * red m (y.P : Matrix (Fin n) (Fin n) O) = 1 := by
      rw [← red_mul, Units.inv_mul, red_one]
    have e2 : red m (y.P : Matrix (Fin n) (Fin n) O) * red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
      rw [← red_mul, Units.mul_inv, red_one]
    rw [hb, hb]
    exact (congrArg τ (tr_c _ _ X Y _ _ _ e1 e2 (hr.2 X) (hr'.2 Y))).trans (hlin _ _)
  intro γ X Y
  rcases cases_c G.frame γ with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact hg g X Y
  · show b (rep ((g : G.Γ) * G.c) X) (rep' ((g : G.Γ) * G.c) Y) = PadicInt.toZModPow k ((G.ε ((g : G.Γ) * G.c) : ℤ_[l]ˣ) : ℤ_[l]) * b X Y
    rw [map_mul rep, map_mul rep', Module.End.mul_apply, Module.End.mul_apply, hg, hcc, map_mul, Units.val_mul, map_mul, mul_assoc]
end
