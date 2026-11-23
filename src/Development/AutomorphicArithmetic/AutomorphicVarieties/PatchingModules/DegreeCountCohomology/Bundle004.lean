module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootEquality
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem conj_eq_transpose_conj_of_transpose_mul_eq_smul_one {n : ℕ} {R : Type} [CommRing R] (P Q P' Q' X : Matrix (Fin n) (Fin n) R) (a b : R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hPQ' : P' * Q' = 1) (ha : Pᵀ * P' = a • 1) (hb : Qᵀ * Q' = b • 1) :
    P' * (X * Q') = Qᵀ * (X * Pᵀ) := by
  have h1 : P' = a • Qᵀ := by
    calc P' = (Qᵀ * Pᵀ) * P' := by rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one, Matrix.one_mul]
      _ = Qᵀ * (Pᵀ * P') := Matrix.mul_assoc _ _ _
      _ = a • Qᵀ := by rw [ha, Matrix.mul_smul, Matrix.mul_one]
  have h2 : Q' = b • Pᵀ := by
    calc Q' = (Pᵀ * Qᵀ) * Q' := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one, Matrix.one_mul]
      _ = Pᵀ * (Qᵀ * Q') := Matrix.mul_assoc _ _ _
      _ = b • Pᵀ := by rw [hb, Matrix.mul_smul, Matrix.mul_one]
  have h3 : P' * Q' = (a * b) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [h1, h2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  rw [hPQ'] at h3
  rw [h1, h2]
  calc a • Qᵀ * (X * b • Pᵀ) = ((a * b) • (1 : Matrix (Fin n) (Fin n) R)) * (Qᵀ * (X * Pᵀ)) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_comm]
    _ = Qᵀ * (X * Pᵀ) := by rw [← h3, Matrix.one_mul]

theorem UpperTheory.V.Pa.adEx :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n : ℕ) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), AdOk F ρ χ V → ∃ rep : Representation A F.Γ V, IsAd F ρ χ V rep := by
  intro l _ F A R _ _ _ n ρ χ V hV
  obtain ⟨h1, hmul, hform, hχ1, hχmul, had, htr⟩ := hV
  have hcinv : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  have hχc : χ F.c * χ F.c = 1 := by rw [← hχmul, F.c_sq, hχ1]
  have hρr : ∀ g : F.G₀, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, h1]
  have hρl : ∀ g : F.G₀, ρ g⁻¹ * ρ g = 1 := fun g => by rw [← hmul, inv_mul_cancel, h1]
  have hcc' : ∀ x : F.Γ, F.c * (F.c * x) = x := fun x => by rw [← mul_assoc, F.c_sq, one_mul]
  have hcc : ∀ g : F.G₀, F.conj (F.conj g) = g := fun g => by
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = g
    simp only [hcinv, mul_assoc, F.c_sq, mul_one, hcc']
  have hχconj : ∀ g : F.G₀, χ (F.conj g : F.Γ) = χ g := fun g => by
    show χ (F.c * (g : F.Γ) * F.c⁻¹) = χ g
    rw [hcinv, hχmul, hχmul]
    linear_combination (χ (g : F.Γ)) * hχc
  let adV : F.G₀ → (V →ₗ[A] V) := fun g =>
    { toFun := fun Z => ⟨χ g • (ρ g * Z * ρ g⁻¹), had g Z Z.2⟩
      map_add' := fun Z W => by
        apply Subtype.ext
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a Z => by
        apply Subtype.ext
        show χ g • (ρ g * (a • (Z : Matrix (Fin n) (Fin n) R)) * ρ g⁻¹) = a • (χ g • (ρ g * (Z : Matrix (Fin n) (Fin n) R) * ρ g⁻¹))
        rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm] }
  let τV : V →ₗ[A] V :=
    { toFun := fun Z => ⟨-(χ F.c • (Z : Matrix (Fin n) (Fin n) R)ᵀ), V.neg_mem (htr Z Z.2)⟩
      map_add' := fun Z W => by
        apply Subtype.ext
        simp [add_comm]
      map_smul' := fun a Z => by
        apply Subtype.ext
        show -(χ F.c • (a • (Z : Matrix (Fin n) (Fin n) R))ᵀ) = a • -(χ F.c • (Z : Matrix (Fin n) (Fin n) R)ᵀ)
        rw [Matrix.transpose_smul, smul_comm, smul_neg] }
  have hadEq : ∀ g g' : F.G₀, (g : F.Γ) = g' → ∀ Z, adV g Z = adV g' Z := by
    intro g g' h Z
    rw [Subtype.ext h]
  have hadone : ∀ Z, adV 1 Z = Z := by
    intro Z
    apply Subtype.ext
    simp [adV, h1, hχ1]
  have hadmul : ∀ g h Z, adV (g * h) Z = adV g (adV h Z) := by
    intro g h Z
    apply Subtype.ext
    simp [adV, hmul, _root_.mul_inv_rev, hχmul, Matrix.mul_assoc, smul_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hττ : ∀ Z, τV (τV Z) = Z := by
    intro Z
    apply Subtype.ext
    simp [τV, smul_smul, hχc]
  have hτad : ∀ g Z, τV (adV g Z) = adV (F.conj g) (τV Z) := by
    intro g Z
    apply Subtype.ext
    obtain ⟨a, ha⟩ := hform g
    obtain ⟨b, hb⟩ := hform g⁻¹
    rw [map_inv] at hb
    have hm := conj_eq_transpose_conj_of_transpose_mul_eq_smul_one (ρ g) (ρ g⁻¹) (ρ (F.conj g)) (ρ (F.conj g)⁻¹) (Z : Matrix (Fin n) (Fin n) R)ᵀ a b
      (hρr g) (hρl g) (hρr _) ha hb
    simp only [adV, τV, LinearMap.coe_mk, AddHom.coe_mk, hχconj]
    simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_neg, smul_smul, hm, mul_comm]
  have hswap : ∀ g W, adV g (τV W) = τV (adV (F.conj g) W) := by
    intro g W
    rw [hτad, hcc]
  have hηc : ∀ h : F.Γ, F.η h ≠ 1 → F.η h = -1 := fun h hh => (Int.units_eq_one_or _).resolve_left hh
  have hmemc : ∀ h : F.Γ, F.η h ≠ 1 → F.c * h ∈ F.η.ker := fun h hh => by
    rw [MonoidHom.mem_ker, map_mul, F.η_c, hηc h hh]
    rfl
  let f : F.Γ → (V →ₗ[A] V) := fun h =>
    if hh : F.η h = 1 then adV ⟨h, hh⟩ else τV ∘ₗ adV ⟨F.c * h, hmemc h hh⟩
  have hcne : F.η F.c ≠ 1 := by
    rw [F.η_c]
    decide
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩
  · apply LinearMap.ext
    intro Z
    simp only [f, dif_pos (map_one F.η)]
    exact hadone Z
  · intro x y
    apply LinearMap.ext
    intro Z
    rw [Module.End.mul_apply]
    by_cases hx : F.η x = 1 <;> by_cases hy : F.η y = 1
    · have hxy : F.η (x * y) = 1 := by rw [map_mul, hx, hy, one_mul]
      simp only [f, dif_pos hxy, dif_pos hx, dif_pos hy]
      rw [← hadmul]
      rfl
    · have hxy : F.η (x * y) ≠ 1 := by rw [map_mul, hx, one_mul]; exact hy
      simp only [f, dif_neg hxy, dif_pos hx, dif_neg hy, LinearMap.comp_apply]
      rw [hswap, ← hadmul]
      congr 1
      apply hadEq
      simp only [Subgroup.coe_mul, MulMemClass.coe_mul]
      show F.c * (x * y) = F.c * x * F.c⁻¹ * (F.c * y)
      simp only [hcinv, mul_assoc, hcc']
    · have hxy : F.η (x * y) ≠ 1 := by rw [map_mul, hy, mul_one]; exact hx
      simp only [f, dif_neg hxy, dif_neg hx, dif_pos hy, LinearMap.comp_apply]
      rw [← hadmul]
      congr 1
      apply hadEq
      simp only [Subgroup.coe_mul, MulMemClass.coe_mul]
      show F.c * (x * y) = F.c * x * y
      rw [mul_assoc]
    · have hxy : F.η (x * y) = 1 := by
        rw [map_mul, hηc x hx, hηc y hy]
        rfl
      simp only [f, dif_pos hxy, dif_neg hx, dif_neg hy, LinearMap.comp_apply]
      rw [hswap, hττ, ← hadmul]
      apply hadEq
      simp only [Subgroup.coe_mul, MulMemClass.coe_mul]
      show x * y = F.c * (F.c * x) * F.c⁻¹ * (F.c * y)
      simp only [hcinv, mul_assoc, hcc']
  · intro g Z
    show ((f (g : F.Γ)) Z : Matrix (Fin n) (Fin n) R) = _
    simp only [f, dif_pos (show F.η (g : F.Γ) = 1 from g.2)]
    rfl
  · intro Z
    show ((f F.c) Z : Matrix (Fin n) (Fin n) R) = _
    simp only [f, dif_neg hcne, LinearMap.comp_apply]
    rw [hadEq _ 1 (by show F.c * F.c = 1; exact F.c_sq) Z, hadone]
    rfl
end

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem card_ker_mul_card_range_eq_card {G H : Type} [AddGroup G] [AddGroup H] (f : G →+ H) :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

theorem UpperTheory.V.Pa.cCount :
    ∀ (R Γ M : Type) [CommRing R] [Group Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M) (c : Γ), c * c = 1 → IsUnit (2 : R) → (∀ Z : AddSubgroup (Γ → M), Finite Z → (Bl ρ).toAddSubgroup ≤ Z → (∀ z ∈ Z, ∀ g h, z (g * h) = z g + ρ g (z h)) → Nat.card Z * Nat.card {m : M // ρ c m = m} = {z | z ∈ Z ∧ z c = 0}.ncard * Nat.card M) ∧ Nat.card (Bl ρ) * Nat.card ρ.invariants = Nat.card M ∧ {z | z ∈ Bl ρ ∧ z c = 0}.ncard * Nat.card ρ.invariants = Nat.card {m : M // ρ c m = m} := by
  intro R Γ M _ _ _ _ _ ρ c hc h2
  let f : M →+ (Γ → M) :=
    { toFun := fun m g => ρ g m - m
      map_zero' := by ext g; simp
      map_add' := by intro a b; ext g; simp; abel }
  have hf : ∀ m g, f m g = ρ g m - m := fun _ _ => rfl
  have hBl : ∀ z, z ∈ Bl ρ ↔ z ∈ f.range := by
    intro z
    simp only [Bl, LinearMap.mem_range, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, by ext g; simp [hf]⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, by ext g; simp [hf]⟩
  have hker : ∀ m, m ∈ f.ker ↔ m ∈ ρ.invariants := by
    intro m
    rw [AddMonoidHom.mem_ker, Representation.mem_invariants]
    constructor
    · intro h g
      have := congrFun h g
      rw [hf] at this
      simpa [sub_eq_zero] using this
    · intro h
      ext g
      simp [hf, h g]
  have cardBl : Nat.card (Bl ρ) = Nat.card f.range :=
    Nat.card_congr (Equiv.subtypeEquivRight hBl)
  have cardInv : Nat.card ρ.invariants = Nat.card f.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => (hker m).symm))
  let d : M →+ M :=
    { toFun := fun m => ρ c m - m
      map_zero' := by simp
      map_add' := by intro a b; simp; abel }
  have hd : ∀ m, d m = ρ c m - m := fun _ => rfl
  have cardFix : Nat.card {m : M // ρ c m = m} = Nat.card d.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => by
      rw [AddMonoidHom.mem_ker, hd, sub_eq_zero]))
  have hdM : Nat.card d.range * Nat.card {m : M // ρ c m = m} = Nat.card M := by
    rw [cardFix, mul_comm]
    exact card_ker_mul_card_range_eq_card d
  let Mc : AddSubgroup M :=
    { carrier := {m | ρ c m = m}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_add (f := _), ha, hb]
      zero_mem' := by simp
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        rw [map_neg, ha] }
  have cardMc : Nat.card {m : M // ρ c m = m} = Nat.card Mc :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => Iff.rfl))
  let f' : Mc →+ (Γ → M) := f.comp Mc.subtype
  have hf' : ∀ x, f' x = f x.1 := fun _ => rfl
  have cardKer' : Nat.card f'.ker = Nat.card ρ.invariants := by
    rw [cardInv]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, by
          have := AddMonoidHom.mem_ker.1 x.2
          rw [hf'] at this
          exact AddMonoidHom.mem_ker.2 this⟩
        invFun := fun v => ⟨⟨v.1, ((hker _).1 v.2 |> (Representation.mem_invariants ρ _).1) c⟩, by
          apply AddMonoidHom.mem_ker.2
          rw [hf']
          exact AddMonoidHom.mem_ker.1 v.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hRange' : ∀ z, z ∈ f'.range ↔ z ∈ {z | z ∈ Bl ρ ∧ z c = 0} := by
    intro z
    simp only [Set.mem_setOf_eq, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(hBl _).2 ⟨x.1, (hf' x).symm⟩, ?_⟩
      rw [hf', hf, sub_eq_zero]
      exact x.2
    · rintro ⟨hz, hzc⟩
      obtain ⟨m, rfl⟩ := (hBl z).1 hz
      rw [hf, sub_eq_zero] at hzc
      exact ⟨⟨m, hzc⟩, rfl⟩
  have cardR' : Nat.card f'.range = {z | z ∈ Bl ρ ∧ z c = 0}.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight hRange')
  refine ⟨?_, ?_, ?_⟩
  · intro Z _ hle hcoc
    let ev : Z →+ M :=
      { toFun := fun z => z.1 c
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hev : ∀ z, ev z = z.1 c := fun _ => rfl
    have kerEv : Nat.card ev.ker = {z | z ∈ Z ∧ z c = 0}.ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2, by
            have := AddMonoidHom.mem_ker.1 x.2
            rwa [hev] at this⟩
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, AddMonoidHom.mem_ker.2 (by rw [hev]; exact y.2.2)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have rangeEv : ∀ x, x ∈ ev.range ↔ x ∈ d.range := by
      intro x
      simp only [AddMonoidHom.mem_range]
      constructor
      · rintro ⟨⟨z, hz⟩, rfl⟩
        rw [hev]
        have h1 := hcoc z hz 1 1
        simp only [mul_one, map_one, Module.End.one_apply] at h1
        have hz1 : z 1 = 0 := by
          have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h1.symm
          exact add_left_cancel this
        have h2c := hcoc z hz c c
        rw [hc, hz1] at h2c
        obtain ⟨u, hu⟩ := h2
        refine ⟨-((↑u⁻¹ : R) • z c), ?_⟩
        rw [hd, map_neg, map_smul]
        have hneg : ρ c (z c) = -z c := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact h2c.symm
        rw [hneg, smul_neg, neg_neg, sub_neg_eq_add, ← add_smul]
        have : (↑u⁻¹ : R) + ↑u⁻¹ = 1 := by
          rw [← Units.inv_mul u, hu]
          ring
        rw [this, one_smul]
      · rintro ⟨m, rfl⟩
        have hmem : f m ∈ Z := hle ((Submodule.mem_toAddSubgroup _).2 ((hBl _).2 ⟨m, rfl⟩))
        refine ⟨⟨f m, hmem⟩, ?_⟩
        show f m c = d m
        rw [hf, hd]
    have cardRangeEv : Nat.card ev.range = Nat.card d.range :=
      Nat.card_congr (Equiv.subtypeEquivRight rangeEv)
    rw [← kerEv, ← card_ker_mul_card_range_eq_card ev, cardRangeEv, mul_assoc, hdM]
  · rw [cardBl, cardInv, mul_comm]
    exact card_ker_mul_card_range_eq_card f
  · rw [← cardR', ← cardKer', cardMc, mul_comm]
    exact card_ker_mul_card_range_eq_card f'
end

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem polZ_mem {l : ℕ} [Fact l.Prime] (F : GFrame l) {γ : F.Γ} (h : γ ∉ F.η.ker) : γ * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at h ⊢
  rw [map_mul, F.η_c]
  rcases Int.units_eq_one_or (F.η γ) with h1 | h1
  · exact absurd h1 h
  · rw [h1]
    decide

private theorem polZ_nmem {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : (g : F.Γ) * F.c ∉ F.η.ker := by
  rw [MonoidHom.mem_ker, map_mul, MonoidHom.mem_ker.mp g.2, F.η_c, one_mul]
  decide

private theorem polZ_proj {l : ℕ} [Fact l.Prime] (F : GFrame l) :
    ∃ p : F.Γ → F.G₀, Continuous p ∧ (∀ g : F.G₀, p g = g) ∧ ∀ g : F.G₀, p (g * F.c) = g := by
  have hK : IsClopen (F.η.ker : Set F.Γ) :=
    ⟨Subgroup.isClosed_of_isOpen _ F.η_open, F.η_open⟩
  have hfr : frontier {a : F.Γ | a ∈ F.η.ker} = ∅ := hK.frontier_eq
  have hf : Continuous fun γ : F.Γ => if γ ∈ F.η.ker then (1 : F.Γ) else F.c := by
    refine continuous_if ?_ continuousOn_const continuousOn_const
    intro a ha
    rw [hfr] at ha
    exact ha.elim
  refine ⟨fun γ => ⟨γ * (if γ ∈ F.η.ker then 1 else F.c), by
    split_ifs with hγ
    · simpa using hγ
    · exact polZ_mem F hγ⟩, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_id.mul hf) _
  · intro g
    apply Subtype.ext
    show (g : F.Γ) * (if (g : F.Γ) ∈ F.η.ker then 1 else F.c) = g
    rw [if_pos g.2, mul_one]
  · intro g
    apply Subtype.ext
    show (g : F.Γ) * F.c * (if (g : F.Γ) * F.c ∈ F.η.ker then 1 else F.c) = g
    rw [if_neg (polZ_nmem F g), mul_assoc, F.c_sq, mul_one]

private theorem polZ_cases {l : ℕ} [Fact l.Prime] (F : GFrame l) (γ : F.Γ) :
    (∃ g : F.G₀, γ = g) ∨ ∃ g : F.G₀, γ = g * F.c := by
  by_cases h : γ ∈ F.η.ker
  · exact Or.inl ⟨⟨γ, h⟩, rfl⟩
  · refine Or.inr ⟨⟨γ * F.c, polZ_mem F h⟩, ?_⟩
    show γ = γ * F.c * F.c
    rw [mul_assoc, F.c_sq, mul_one]

private theorem polZ_conj {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) :
    (F.conj g : F.Γ) = F.c * g * F.c := by
  show F.c * g * F.c⁻¹ = _
  rw [inv_eq_of_mul_eq_one_right F.c_sq]

private theorem polZ_ext {l : ℕ} [Fact l.Prime] (F : GFrame l) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (rep : Representation A F.Γ M) (Z : F.G₀ → M) (hl : IsLocallyConstant Z)
    (hm : ∀ g h, Z (g * h) = Z g + rep g (Z h)) (hc : ∀ g, Z (F.conj g) = rep F.c (Z g)) :
    ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, y g = Z g := by
  classical
  obtain ⟨p, hp, hp1, hp2⟩ := polZ_proj F
  have hZ1 : Z 1 = 0 := by
    have h1 := hm 1 1
    simpa using h1
  have hpc : p F.c = 1 := by
    have h2 := hp2 1
    simpa using h2
  have hmem : (fun γ => Z (p γ)) ∈ Zl rep := by
    show IsLocallyConstant (fun γ => Z (p γ)) ∧
      ∀ g h : F.Γ, Z (p (g * h)) = Z (p g) + rep g (Z (p h))
    refine ⟨hl.comp_continuous hp, ?_⟩
    intro γ δ
    rcases polZ_cases F γ with ⟨g, rfl⟩ | ⟨g, rfl⟩ <;>
      rcases polZ_cases F δ with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · rw [← Subgroup.coe_mul]
      simp only [hp1]
      exact hm g h
    · rw [show (g : F.Γ) * (h * F.c) = ((g * h : F.G₀) : F.Γ) * F.c by
        simp only [Subgroup.coe_mul, mul_assoc]]
      simp only [hp1, hp2]
      exact hm g h
    · rw [show (g : F.Γ) * F.c * h = ((g * F.conj h : F.G₀) : F.Γ) * F.c by
        simp only [Subgroup.coe_mul, polZ_conj, mul_assoc, F.c_sq, mul_one]]
      simp only [hp1, hp2]
      rw [hm, hc, map_mul, Module.End.mul_apply]
    · rw [show (g : F.Γ) * F.c * (h * F.c) = ((g * F.conj h : F.G₀) : F.Γ) by
        simp only [Subgroup.coe_mul, polZ_conj, mul_assoc]]
      simp only [hp1, hp2]
      rw [hm, hc, map_mul, Module.End.mul_apply]
  refine ⟨fun γ => Z (p γ), hmem, ?_, fun g => ?_⟩
  · show Z (p F.c) = 0
    rw [hpc, hZ1]
  · show Z (p g) = Z g
    rw [hp1]

theorem UpperTheory.V.Pa.polZ :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n : ℕ) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) (rep : Representation A F.Γ V), IsAd F ρ χ V rep → (∀ z : F.G₀ → Matrix (Fin n) (Fin n) R, (∀ g, z g ∈ V) → IsLocallyConstant z → (∀ g h, z (g * h) = z g + χ g • (ρ g * z h * ρ g⁻¹)) → (∀ g, z (F.conj g) = -(χ F.c • (z g)ᵀ)) → ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, (y g : Matrix (Fin n) (Fin n) R) = z g) ∧ (∀ y ∈ Zl rep, y F.c = 0 → (∀ g : F.G₀, (y (F.conj g) : Matrix (Fin n) (Fin n) R) = -(χ F.c • (y g : Matrix (Fin n) (Fin n) R)ᵀ)) ∧ ((∀ g : F.G₀, y g = 0) → y = 0)) := by
  intro l _ F A R _ _ _ n ρ χ V rep hAd
  obtain ⟨hA1, hA2⟩ := hAd
  refine ⟨fun z hz hzl hzm hzc => ?_, fun y hy hyc => ?_⟩
  · obtain ⟨y, hy, hyc, hyg⟩ := polZ_ext F rep (fun g => (⟨z g, hz g⟩ : V))
      (IsLocallyConstant.desc _ Subtype.val hzl Subtype.val_injective)
      (fun g h => Subtype.ext (by simp only [Submodule.coe_add, hA1]; exact hzm g h))
      (fun g => Subtype.ext (by rw [hA2]; exact hzc g))
    exact ⟨y, hy, hyc, fun g => by rw [hyg g]⟩
  · obtain ⟨-, hyc'⟩ := hy
    refine ⟨fun g => ?_, fun h0 => ?_⟩
    · rw [polZ_conj, hyc', hyc', hyc, map_zero, add_zero, zero_add, hA2]
    · funext γ
      rcases polZ_cases F γ with ⟨g, rfl⟩ | ⟨g, rfl⟩
      · exact h0 g
      · rw [Pi.zero_apply, hyc', h0 g, hyc, map_zero, add_zero]
end

section

noncomputable section

namespace UpperTheory.V.Pa

section Abstract

variable {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M] (ρ : Representation R G M)

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [Finite M]

end Abstract

theorem unrBare : ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (C : Type) [CommGroup C] [Finite C] (χ : ReciprocityTheory.Gal.Dec (F := F) A →* C), Formalism.ConjugateSelfDual.IsPlaceOver A v →
    IsOpen (χ.ker : Set (ReciprocityTheory.Gal.Dec (F := F) A)) → (Nat.card C).Coprime l →
    UnrCount l (ReciprocityTheory.Gal.Dec (F := F) A) ((ReciprocityTheory.Gal.Ine A).subgroupOf (ReciprocityTheory.Gal.Dec A) ⊓ χ.ker) :=
  _root_.UpperTheory.Reformulated.B.RootEquality.unrBare

end UpperTheory.V.Pa
end
end
