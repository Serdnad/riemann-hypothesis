module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.cocycle_normal_form :
    ∀ (k Γ M : Type) [CommRing k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M] (F : Frame Γ) (ρ : Representation k Γ M), (∀ m : M, IsLocallyConstant fun s => ρ s m) → (∀ q, ∀ n ∈ F.N q, ∀ m, ρ (F.ψ q n) m = m) →
          ∀ x ∈ F.framedTwoCoboundaries ρ, ∃ (h : Γ → M) (y : F.T → M), IsLocallyConstant h ∧ y F.v0 = 0 ∧ x.1 = dOne ρ h ∧ (∀ v s, x.2.1 v s = h (F.φ v s) - (ρ (F.φ v s) (y v) - y v)) ∧ ∀ q, ∀ n ∈ F.N q, x.2.2 q n = h (F.ψ q n) := by
  intro k Γ M _ _ _ _ _ F ρ hρ hN x hx
  unfold Frame.framedTwoCoboundaries at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, y, e, h1, h2, h3, h4, h5⟩ := hx
    refine ⟨fun s => h s - (ρ s (y F.v0) - y F.v0), fun v => y v - y F.v0,
      h1.sub ((hρ _).sub (IsLocallyConstant.const _)), sub_self _, ?_, fun v s => ?_, fun q n hn => ?_⟩
    · rw [h3]
      funext p
      simp only [dOne, map_sub, map_mul, Module.End.mul_apply]
      abel
    · rw [h4]
      simp only [map_sub]
      abel
    · rw [h5, (h2 q).2.2 n hn]
      simp only [hN q n hn, sub_self]
  | zero =>
    refine ⟨0, 0, IsLocallyConstant.const 0, rfl, ?_, by simp, by simp⟩
    funext p
    simp [dOne]
  | add x x' _ _ ih ih' =>
    obtain ⟨h, y, a1, a2, a3, a4, a5⟩ := ih
    obtain ⟨h', y', b1, b2, b3, b4, b5⟩ := ih'
    refine ⟨h + h', y + y', a1.add b1, by simp [a2, b2], ?_, fun v s => ?_, fun q n hn => ?_⟩
    · funext p
      simp only [Prod.fst_add, Pi.add_apply, a3, b3, dOne, map_add (f := _)]
      abel
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a4, b4, map_add (f := _)]
      abel
    · simp only [Prod.snd_add, Pi.add_apply, a5 q n hn, b5 q n hn]
  | smul c x _ ih =>
    obtain ⟨h, y, a1, a2, a3, a4, a5⟩ := ih
    refine ⟨c • h, c • y, a1.comp (c • ·), by simp [a2], ?_, fun v s => ?_, fun q n hn => ?_⟩
    · funext p
      simp [a3, dOne, smul_sub]
    · simp [a4, smul_sub]
    · simp [a5 q n hn]
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Matrix in
private theorem expand_small {O : Type} [CommRing O] [IsLocalRing O] {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (p : R →ₐ[O] R') (hs : maximalIdeal R * RingHom.ker p = ⊥) (J h Z : Matrix ι ι R)
    (hh : h.map (res O R) = 1) (hZ : Z.map p = 0) :
    (h + Z)ᵀ * J * (h + Z) = hᵀ * J * h + (Zᵀ * J + J * Z) ∧ (h + Z).map (res O R) = 1 := by
  have k : ∀ x y : R, res O R x = 0 → p y = 0 → x * y = 0 := fun x y hx hy => by
    have : x * y ∈ maximalIdeal R * RingHom.ker p :=
      Ideal.mul_mem_mul ((res_eq_zero_iff O R x).1 hx) hy
    rwa [hs, Ideal.mem_bot] at this
  have z1 : ∀ a b, p (Z a b) = 0 := fun a b => congrFun (congrFun hZ a) b
  have z2 : ∀ a b, res O R (Z a b) = 0 := fun a b => by rw [← res_map p, z1, map_zero]
  have h1 : ∀ a b, res O R ((h - 1) a b) = 0 := fun a b => by
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases e : a = b
    · subst e; simp
    · simp [one_apply_ne e]
  have K : ∀ A B : Matrix ι ι R, (∀ a b, res O R (A a b) = 0) → (∀ a b, p (B a b) = 0) →
      Aᵀ * J * B = 0 ∧ Bᵀ * J * A = 0 := fun A B hA hB => by
    constructor
    · ext a b
      simp only [Matrix.mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, k _ _ (hA _ _) (hB _ _), zero_mul]
    · ext a b
      simp only [Matrix.mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, mul_comm (B _ _), k _ _ (hA _ _) (hB _ _), zero_mul]
  constructor
  · obtain ⟨e1, e2⟩ := K (h - 1) Z h1 z1
    obtain ⟨e3, -⟩ := K Z Z z2 z1
    rw [transpose_sub, transpose_one, sub_mul, sub_mul, one_mul, sub_eq_zero] at e1
    rw [mul_sub, mul_one, sub_eq_zero] at e2
    rw [transpose_add, add_mul, add_mul, mul_add, mul_add, e1, e2, e3]
    abel
  · ext a b
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [map_apply, Matrix.add_apply, map_add (f := _), z2, add_zero, this]

open Matrix in
theorem UpperTheory.V.Alg.hh_small :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ →
      (∀ h' : Matrix ι ι R', Φ.HH h' → ∃ h : Matrix ι ι R, Φ.HH h ∧ h.map p = h') ∧
      (∀ h₁ h₂ : Matrix ι ι R, Φ.HH h₁ → Φ.HH h₂ → h₁.map p = h₂.map p → h₂ - h₁ ∈ Φ.g R) ∧
      ∀ h Y : Matrix ι ι R, Φ.HH h → Y ∈ Φ.g R → Y.map p = 0 → Φ.HH (h + Y) := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 R _ _ _ R' _ _ _ p hp hs
  refine ⟨?_, ?_, ?_⟩
  · classical
    rintro h' ⟨a1, a2, a3⟩
    choose s hs' using hp
    obtain ⟨h0, b1, b2⟩ : ∃ h0 : Matrix ι ι R, h0.map p = h' ∧ ∀ a b, Φ.blk a ≠ Φ.blk b → h0 a b = 0 := by
      refine ⟨Matrix.of fun a b => if Φ.blk a = Φ.blk b then s (h' a b) else 0, ?_, fun a b e => by simp [e]⟩
      ext a b
      by_cases e : Φ.blk a = Φ.blk b
      · simp [e, hs']
      · simp [e, a2 a b e]
    have b3 : h0.map (res O R) = 1 := by
      rw [← a3, ← b1]
      ext a b
      simp [res_map]
    have jp : (Φ.JR R).map p = Φ.JR R' := by
      ext a b
      simp [FormData.JR]
    have jb : ∀ a b, Φ.JR R a b ≠ 0 → Φ.blk b = Φ.σ (Φ.blk a) := fun a b e =>
      Φ.hblk a b fun n => e (by simp [FormData.JR, n])
    obtain ⟨K, hK⟩ : ∃ K : Matrix ι ι R, Φ.JR R * K = 1 :=
      (Φ.unit.map (algebraMap O R).mapMatrix).exists_right_inv
    obtain ⟨u, hu⟩ : ∃ u : R, 2 * u = 1 := by
      have := (h2.map (algebraMap O R)).exists_right_inv
      rwa [map_ofNat] at this
    obtain ⟨ε, hε, hε2⟩ : ∃ ε : R, (Φ.JR R)ᵀ = ε • Φ.JR R ∧ ε * ε = 1 := by
      rcases Φ.sym with e | e
      · refine ⟨1, ?_, by simp⟩
        ext a b
        have := congrFun (congrFun e a) b
        simp only [transpose_apply] at this
        simp [FormData.JR, this]
      · refine ⟨-1, ?_, by simp⟩
        ext a b
        have := congrFun (congrFun e a) b
        simp only [transpose_apply] at this
        simp [FormData.JR, this]
    set E := h0ᵀ * Φ.JR R * h0 - Φ.JR R with hE
    have E1 : E.map p = 0 := by
      rw [hE, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, transpose_map, b1, jp, a1, sub_self]
    have E2 : Eᵀ = ε • E := by
      rw [hE, transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hε, smul_sub]
      simp [mul_assoc]
    have E3 : ∀ a b, Φ.blk b ≠ Φ.σ (Φ.blk a) → E a b = 0 := fun a b e => by
      have : Φ.JR R a b = 0 := by_contra fun n => e (jb a b n)
      rw [hE, Matrix.sub_apply, this, sub_zero]
      simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      by_cases e1 : Φ.blk d = Φ.blk a
      · by_cases e2 : Φ.blk c = Φ.blk b
        · have : Φ.JR R d c = 0 := by_contra fun n => e (by rw [← e2, ← e1]; exact jb d c n)
          simp [this]
        · simp [b2 _ _ e2]
      · simp [b2 _ _ e1]
    set Z0 : Matrix ι ι R := K * ((-u) • E) with hZ0
    have Z1 : Φ.JR R * Z0 = (-u) • E := by rw [hZ0, ← mul_assoc, hK, one_mul]
    have Z2 : ∀ a b, p (Z0 a b) = 0 := fun a b => by

      rw [hZ0, Matrix.mul_apply, map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      have : p (E c b) = 0 := congrFun (congrFun E1 c) b
      simp [this]
    let Z : Matrix ι ι R := Matrix.of fun a b => if Φ.blk a = Φ.blk b then Z0 a b else 0
    have Z3 : Z.map p = 0 := by
      ext a b
      by_cases e : Φ.blk a = Φ.blk b <;> simp [Z, e, Z2]
    have Z4 : Φ.JR R * Z = (-u) • E := by
      ext a b
      by_cases e : Φ.blk b = Φ.σ (Φ.blk a)
      · rw [← Z1, Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases n : Φ.JR R a c = 0
        · simp [n]
        · have : Φ.blk c = Φ.blk b := by rw [e]; exact jb a c n
          simp [Z, this]
      · rw [Matrix.smul_apply, E3 a b e, smul_zero, Matrix.mul_apply]
        refine Finset.sum_eq_zero fun c _ => ?_
        by_cases n : Φ.JR R a c = 0
        · simp [n]
        · have : ¬ Φ.blk c = Φ.blk b := fun m => e (by rw [← m]; exact jb a c n)
          simp [Z, this]
    have Z5 : Zᵀ * Φ.JR R = (-u) • E := by
      have := congrArg (fun M => ε • Mᵀ) Z4
      simp only [transpose_mul, transpose_smul, hε, E2, Matrix.mul_smul, smul_smul] at this
      rw [hε2, one_smul, mul_left_comm, hε2, mul_one] at this
      exact this
    obtain ⟨c1, c2⟩ := expand_small p hs (Φ.JR R) h0 Z b3 Z3
    refine ⟨h0 + Z, ⟨?_, fun a b e => by simp [Z, e, b2 a b e], c2⟩, ?_⟩
    · rw [c1, Z4, Z5, ← add_smul, show -u + -u = -1 by rw [← hu]; ring, neg_one_smul, hE]
      abel
    · rw [Matrix.map_add _ (map_add p), b1, Z3, add_zero]
  · rintro h₁ h₂ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ e
    have hZ : (h₂ - h₁).map p = 0 := by rw [Matrix.map_sub _ (map_sub p), e, sub_self]
    obtain ⟨c1, -⟩ := expand_small p hs (Φ.JR R) h₁ (h₂ - h₁) a3 hZ
    rw [add_sub_cancel, a1, b1, left_eq_add] at c1
    exact ⟨c1, fun a b n => by simp [a2 a b n, b2 a b n]⟩
  · rintro h Y ⟨a1, a2, a3⟩ ⟨b1, b2⟩ e
    obtain ⟨c1, c2⟩ := expand_small p hs (Φ.JR R) h Y a3 e
    exact ⟨by rw [c1, a1, b1, add_zero], fun a b n => by simp [a2 a b n, b2 a b n], c2⟩
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem lift_map_map' {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    [CommRing R''] [Algebra O R''] [IsCO O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'')
    (r : Lift O rbar R) : Lift.map g (Lift.map f r) = Lift.map (g.comp f) r := by
  apply Lift.ext
  ext x a b
  rfl

theorem UpperTheory.V.Alg.univ_cond :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R) (P₀ P : Cond O rbar), Represents P₀ r → P.IsClosed → (∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra O R₁) (_ : IsCO O R₁) (r₁ : Lift O rbar R₁), P₀ R₁ r₁ ∧ P R₁ r₁) →
      ∃ (R' : Type) (_ : CommRing R') (_ : Algebra O R') (_ : IsCO O R') (p : R →ₐ[O] R'), Function.Surjective p ∧ Represents (fun C _ _ _ s => P₀ C s ∧ P C s) (r.map p) := by
  intro O _ _ Γ ι _ _ _ _ rbar R _ _ _ r P₀ P hrep hcl hex
  obtain ⟨I, hI⟩ := hcl R r
  obtain ⟨R₁, _, _, _, r₁, h0, h1⟩ := hex
  obtain ⟨f, hf, -⟩ := (hrep R₁).2 r₁ h0
  have hf1 : P R₁ (Lift.map f r) := hf ▸ h1
  have hfI : ∀ x ∈ I, f x = 0 := (hI R₁ f).1 hf1
  set J : Ideal R := Ideal.span I
  have hJf : ∀ x ∈ J, f x = 0 := by
    intro x hx
    have hle : J ≤ RingHom.ker f.toRingHom := Ideal.span_le.2 (fun y hy => hfI y hy)
    exact hle hx
  have hJ : J ≠ ⊤ := by
    intro htop
    have h1mem : (1 : R) ∈ J := htop ▸ Submodule.mem_top
    have := hJf 1 h1mem
    simp at this
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI hco : IsCO O (R ⧸ J) := co_quot O R (R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hpI : ∀ x ∈ I, Ideal.Quotient.mkₐ O J x = 0 := by
    intro x hx
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span hx
  refine ⟨R ⧸ J, inferInstance, inferInstance, hco, Ideal.Quotient.mkₐ O J, Ideal.Quotient.mkₐ_surjective O J, ?_⟩
  intro R'' _ _ _
  refine ⟨fun g => ?_, fun r' hr' => ?_⟩
  · rw [lift_map_map']
    refine ⟨(hrep R'').1 _, (hI R'' _).2 ?_⟩
    intro x hx
    rw [AlgHom.comp_apply, hpI x hx, map_zero]
  · obtain ⟨f', hf', huniq⟩ := (hrep R'').2 r' hr'.1
    have hf'I : ∀ x ∈ I, f' x = 0 := (hI R'' f').1 (hf' ▸ hr'.2)
    have hf'J : ∀ x ∈ J, f' x = 0 := by
      intro x hx
      have hle : J ≤ RingHom.ker f'.toRingHom := Ideal.span_le.2 (fun y hy => hf'I y hy)
      exact hle hx
    refine ⟨Ideal.Quotient.liftₐ J f' hf'J, ?_, ?_⟩
    · show Lift.map _ (Lift.map _ r) = r'
      rw [lift_map_map', Ideal.Quotient.liftₐ_comp]
      exact hf'
    · intro g hg
      apply Ideal.Quotient.algHom_ext O
      rw [Ideal.Quotient.liftₐ_comp]
      apply huniq
      show Lift.map _ r = r'
      rw [← lift_map_map']
      exact hg
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.framed_origin :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (WB : WPres O X B) (hB : WB.HasOrigin), (∀ v s a b, WB.origin hB ((ρ v).hom s a b) = r0.hom (F.φ v s) a b) →
      ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (i : B →ₐ[O] R) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α → ∀ (W : WPres O X R) (τ : Type) (e : WB.σ ⊕ τ ≃ W.σ), (∀ s, W.z (e (.inl s)) = i (WB.z s)) →
      (∀ t, ∃ a b, (∃ s, W.z (e (.inr t)) = r.hom s a b - algebraMap O R (r0.hom s a b)) ∨ ∃ v, W.z (e (.inr t)) = (α v - 1) a b) →
      ∃ h : W.HasOrigin, r.map (W.origin h) = r0 ∧ (∀ v, (α v).map (W.origin h) = 1) ∧ (W.origin h).comp i = WB.origin hB := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar hr0 F L hN hLoc hL0 B _ _ _ ρ hρ WB hB hWB R _ _ _ i r α hU W τ e hWl hWr
  have hHH1 : ∀ (S : Type) [CommRing S] [Algebra O S] [IsCO O S], Φ.HH (1 : Matrix ι ι S) := by
    intro S _ _ _
    refine ⟨by simp, fun a b hab => ?_, ?_⟩
    · exact Matrix.one_apply_ne (fun h => hab (h ▸ rfl))
    · simp
  have hF : IsFramed Φ r0.hom F L ρ (WB.origin hB) r0 (fun _ => (1 : Matrix ι ι O)) := by
    refine ⟨fun s => ?_, fun q => hL0 q, fun v => hHH1 O, rfl, fun v s => ?_⟩
    · have hm : (r0.hom s⁻¹).map (algebraMap O O) = r0.hom s⁻¹ := by
        ext a b
        simp
      rw [hm, ← map_mul, mul_inv_cancel, map_one]
      exact hHH1 O
    · ext a b
      simp [Matrix.map_apply, hWB]
  obtain ⟨f, ⟨hfi, hfr, hfα⟩, -⟩ := hU.2 O (WB.origin hB) r0 (fun _ => 1) hF
  have hz : ∀ s, f (W.z s) = 0 := by
    intro s
    obtain ⟨s', rfl⟩ := e.surjective s
    rcases s' with s' | t
    · rw [hWl, ← AlgHom.comp_apply, hfi]
      simp [WPres.z, WPres.origin_π]
    · obtain ⟨a, b, ⟨s, hs⟩ | ⟨v, hv⟩⟩ := hWr t
      · rw [hs, map_sub, AlgHom.commutes, ← Lift.map_hom, hfr]
        simp
      · have hab := congrFun (congrFun (hfα v) a) b
        rw [Matrix.map_apply] at hab
        rw [hv, Matrix.sub_apply, map_sub, hab, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
  have hC : ∀ x : O, (C x : MvPowerSeries W.σ O) = algebraMap O (MvPowerSeries W.σ O) x := by
    intro x
    simp [MvPowerSeries.algebraMap_apply]
  let cc : MvPowerSeries W.σ O →ₐ[O] O :=
    AlgHom.mk (MvPowerSeries.constantCoeff (R := O) (σ := W.σ)) (fun x => by simp [MvPowerSeries.algebraMap_apply])
  have hcc : ∀ g, f (W.π g) = constantCoeff g := by
    obtain ⟨G, -, huniq⟩ := co_ev O O O W.σ (AlgHom.id O O) (fun _ => 0) (fun _ => Ideal.zero_mem _)
    have h1 : f.comp W.π = G := huniq _ ⟨fun x => by
      rw [AlgHom.comp_apply, hC, AlgHom.commutes, AlgHom.commutes]
      rfl, fun s => hz s⟩
    have h2' : cc = G := huniq _ ⟨fun x => by simp [cc], fun s => by simp [cc]⟩
    intro g
    have := congrArg (fun φ => φ g) (h1.trans h2'.symm)
    simpa [cc] using this
  have hO : W.HasOrigin := by
    intro g hg
    rw [← hcc, hg, map_zero]
  have horig : W.origin hO = f := by
    ext x
    obtain ⟨g, rfl⟩ := W.surj x
    rw [WPres.origin_π, hcc]
  refine ⟨hO, ?_, ?_, ?_⟩
  · rw [horig, hfr]
  · intro v
    rw [horig, hfα]
  · rw [horig, hfi]
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem ker_gen_closed {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A)
    (f : A) (h : ∀ N : ℕ, ∃ g ∈ I, f - g ∈ maximalIdeal A ^ N) : f ∈ I := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ I) (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
  have hmem : Ideal.Quotient.mk I f ∈ ⨅ i, (maximalIdeal A) ^ i • (⊤ : Submodule A (A ⧸ I)) := by
    rw [Submodule.mem_iInf]
    intro N
    obtain ⟨g, hg, hfg⟩ := h N
    have heq : Ideal.Quotient.mk I f = (f - g) • (1 : A ⧸ I) := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one, map_sub,
        Ideal.Quotient.eq_zero_iff_mem.mpr hg, sub_zero]
    rw [heq]
    exact Submodule.smul_mem_smul hfg Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

private theorem ker_gen_approx {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X]
    {σ : Type} [Finite σ] (wt : σ → X) (f : MvPowerSeries σ O) (N : ℕ) :
    ∃ T : Finset X, f - ∑ j ∈ T, wcomp O wt j f ∈ maximalIdeal (MvPowerSeries σ O) ^ N := by
  classical
  set D := (Finsupp.finite_of_degree_lt (σ := σ) N).toFinset with hD
  refine ⟨D.image (Finsupp.weight wt), ?_⟩
  have hX : ∀ i : σ, (AlgHom.id O (MvPowerSeries σ O)) (MvPowerSeries.X i) ∈ maximalIdeal (MvPowerSeries σ O) := by
    intro i
    rw [AlgHom.id_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hord : ((N : ℕ) : ℕ∞) ≤ (f - ∑ j ∈ D.image (Finsupp.weight wt), wcomp O wt j f).order := by
    apply MvPowerSeries.nat_le_order
    intro d hd

    rw [map_sub, map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq, if_pos, sub_self]
    exact Finset.mem_image_of_mem _ (by simpa [hD] using hd)
  have key := GlobalTheory.algHom_mem_pow_of_le_order (AlgHom.id O (MvPowerSeries σ O)) hX hord
  simpa using key

theorem UpperTheory.V.Alg.ker_gen :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] (σ : Type) [Finite σ] (wt : σ → X) (J : Ideal (MvPowerSeries σ O)), IsHomog O wt J →
      ∃ (n : ℕ) (f : Fin n → MvPowerSeries σ O) (c : Fin n → X), (∀ i, f i ∈ wtPart O wt (c i)) ∧ J = Ideal.span (Set.range f) := by
  intro O _ _ _ _ X _ σ _ wt J hJ
  classical
  set G : Set (MvPowerSeries σ O) := {g | ∃ f ∈ J, ∃ j : X, g = wcomp O wt j f} with hG
  have hGJ : Ideal.span G ≤ J := by
    rw [Ideal.span_le]
    rintro g ⟨f, hf, j, rfl⟩
    exact hJ f hf j
  have hJG : J ≤ Ideal.span G := by
    intro f hf
    apply ker_gen_closed (Ideal.span G) f
    intro N
    obtain ⟨T, hT⟩ := ker_gen_approx wt f N
    exact ⟨_, Ideal.sum_mem _ (fun j _ => Ideal.subset_span ⟨f, hf, j, rfl⟩), hT⟩
  have hfg : (Submodule.span (MvPowerSeries σ O) G).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
  have hchoice : ∀ g : s, ∃ j : X, g.1 ∈ wtPart O wt j := by
    rintro ⟨g, hg⟩
    obtain ⟨f, _, j, rfl⟩ := hsG hg
    exact ⟨j, wcomp_mem O wt j f⟩
  choose c hc using hchoice
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, fun i => c (s.equivFin.symm i), fun i => hc _, ?_⟩
  have hrange : Set.range (fun i => (s.equivFin.symm i).1) = (s : Set (MvPowerSeries σ O)) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hg
      exact ⟨s.equivFin ⟨g, hg⟩, by simp⟩
  rw [hrange]
  calc J = Ideal.span G := le_antisymm hJG hGJ
    _ = Ideal.span (s : Set (MvPowerSeries σ O)) := hspan
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.co_sqz :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module O M] [IsScalarTower O R M] [Module.Finite R M] [Algebra O (TrivSqZeroExt R M)],
      (∀ c : O, algebraMap O (TrivSqZeroExt R M) c = TrivSqZeroExt.inl (algebraMap O R c)) → IsCO O (TrivSqZeroExt R M) := by
  intro O _ _ R _ _ _ M _ _ _ _ _ _ _ _ hO
  haveI : IsLocalRing (TrivSqZeroExt R M) :=
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
      exact IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst
  haveI hST := IsScalarTower.of_algebraMap_eq (R := O) (S := R) (A := TrivSqZeroExt R M) fun c => by
    rw [hO, TrivSqZeroExt.algebraMap_eq_inl]
  haveI : Module.Finite R (TrivSqZeroExt R M) := inferInstanceAs (Module.Finite R (R × M))
  refine co_finite O R (TrivSqZeroExt R M) ?_
  intro x
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x.fst
  refine ⟨a, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, hO,
    TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl]
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
end
