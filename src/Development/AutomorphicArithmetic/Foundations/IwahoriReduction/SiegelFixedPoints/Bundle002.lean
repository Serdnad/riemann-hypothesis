module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem exists_finite_residue_reps_mod_natCast (M K : ℕ) (hK : K ∣ M) (L γ : SL(2, ℤ))
    (h : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) L =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ) (i j : Fin 2) :
    ((L i j : ℤ) : ZMod K) = ((γ i j : ℤ) : ZMod K) := by
  have h1 : ((L i j : ℤ) : ZMod M) = ((γ i j : ℤ) : ZMod M) :=
    congrArg (fun g : SL(2, ZMod M) => g i j) h
  have h2 := congrArg (ZMod.castHom hK (ZMod K)) h1
  simpa only [map_intCast] using h2

private theorem exists_mem_mul_or_neg_mul_symm (M : ℕ) (a b : ℕ) : Tm M (a + b) = Tm M a * Tm M b := by
  simp only [Tm, pow_add, map_mul]

private theorem tm_apply_eq_cast_upper_unipotent (M k : ℕ) (i j : Fin 2) :
    (Tm M k) i j = (((!![1, (k : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod M) := by
  rw [← ModularGroup.coe_T_zpow, zpow_natCast]
  rfl

private theorem exists_mem_mul_or_neg_mul_trans (M : ℕ) (j : ℕ) : Tm M (M * j) = 1 := by
  ext i k
  rw [tm_apply_eq_cast_upper_unipotent]
  fin_cases i <;> fin_cases k <;> simp

private theorem tm_mod_eq (M : ℕ) (k : ℕ) : Tm M (k % M) = Tm M k := by
  conv_rhs => rw [← Nat.mod_add_div k M]
  rw [exists_mem_mul_or_neg_mul_symm, exists_mem_mul_or_neg_mul_trans, mul_one]

private theorem eq_of_tm_eq_of_lt (M : ℕ) (a b : ℕ) (ha : a < M) (hb : b < M) (h : Tm M a = Tm M b) : a = b := by
  have h1 := congrArg (fun g : SL(2, ZMod M) => g 0 1) h
  simp only [tm_apply_eq_cast_upper_unipotent] at h1
  simp at h1
  rw [ZMod.natCast_eq_natCast_iff'] at h1
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1

private theorem tm_mem_map_gam (N l M : ℕ) (k : ℕ) :
    Tm M k ∈ Subgroup.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))) (Gam N l) := by
  refine Subgroup.mem_map_of_mem _ (Subgroup.pow_mem _ ?_ k)
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.coe_T]

private theorem liftSL_mem_gam_and_map_eq_of_mem_gs (N l M : ℕ) [NeZero M] (hM : N * l ∣ M) (γ : SL(2, ZMod M)) (hγ : γ ∈ Gs N l M) :
    liftSL M γ ∈ Gam N l ∧ Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M γ) = γ := by
  have hγ' : γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))) (Gam N l) := by
    simpa [Gs] using hγ
  obtain ⟨γ', hg', rfl⟩ := Subgroup.mem_map.1 hγ'
  have hL : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ')) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ' :=
    Classical.epsilon_spec (p := fun g => Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ') ⟨γ', rfl⟩
  refine ⟨?_, hL⟩
  have eN := exists_finite_residue_reps_mod_natCast M N (dvd_trans (dvd_mul_right N l) hM) _ _ hL
  have el := exists_finite_residue_reps_mod_natCast M l (dvd_trans (dvd_mul_left l N) hM) _ _ hL
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.1 hg'
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem] at h1 ⊢
    rw [eN, eN, eN]
    exact h1
  · rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
    rw [el]
    exact h0

theorem UpperTheory.Kd.L.reps :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (M : ℕ) [NeZero M], N * l ∣ M → (∃ R, IsReps N l M R) ∧ ∀ γ ∈ Gs N l M, ∀ r₀, Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M γ) = γ ∧ gm r₀ * liftSL M γ ∈ CongruenceSubgroup.Gamma0 N ∧ ((en (gm r₀ * liftSL M γ) 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) ∧ ¬ (l : ℤ) ∣ en (gm r₀ * liftSL M γ) 0 0 ∧ ¬ (l : ℤ) ∣ en (gm r₀ * liftSL M γ) 1 0 := by
  intro l _ N _ c d gm hP M _ hM
  classical
  refine ⟨?_, ?_⟩
  · let orb : SL(2, ZMod M) → Set (SL(2, ZMod M)) := fun γ => Set.range (fun k : ℕ => γ * Tm M k)
    let rep : SL(2, ZMod M) → SL(2, ZMod M) := fun γ => Classical.epsilon (fun x => x ∈ orb γ)
    have h0 : Tm M 0 = 1 := by simpa using exists_mem_mul_or_neg_mul_trans M 0
    have self_mem : ∀ γ, γ ∈ orb γ := fun γ => ⟨0, show γ * Tm M 0 = γ by rw [h0, mul_one]⟩
    have rep_mem : ∀ γ, rep γ ∈ orb γ := fun γ => Classical.epsilon_spec ⟨γ, self_mem γ⟩
    have orb_eq : ∀ γ x, x ∈ orb γ → orb x = orb γ := by
      rintro γ _ ⟨j, rfl⟩
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨j + k, show γ * Tm M (j + k) = γ * Tm M j * Tm M k by rw [mul_assoc, ← exists_mem_mul_or_neg_mul_symm]⟩
      · rintro ⟨k, rfl⟩
        refine ⟨k + (M - 1) * j, ?_⟩
        have hM1 : j + (k + (M - 1) * j) = k + M * j := by
          have : 1 ≤ M := NeZero.one_le
          obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        show γ * Tm M j * Tm M (k + (M - 1) * j) = γ * Tm M k
        rw [mul_assoc, ← exists_mem_mul_or_neg_mul_symm, hM1, exists_mem_mul_or_neg_mul_symm, exists_mem_mul_or_neg_mul_trans, mul_one]
    have rep_eq : ∀ γ x, x ∈ orb γ → rep x = rep γ := by
      intro γ x hx
      simp only [rep]
      rw [orb_eq γ x hx]
    have hGs : ∀ γ, γ ∈ Gs N l M ↔ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))) (Gam N l) := by
      intro γ
      simp [Gs]
    refine ⟨(Gs N l M).image rep, ?_, ?_⟩
    · intro x hx
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, hj⟩ := rep_mem γ
      rw [← hj, hGs]
      exact Subgroup.mul_mem _ ((hGs γ).1 hγ) (tm_mem_map_gam N l M j)
    · intro γ hγ
      have hin : γ ∈ orb (rep γ) := by
        rw [orb_eq γ (rep γ) (rep_mem γ)]
        exact self_mem γ
      obtain ⟨k, hk⟩ := hin
      have hk : rep γ * Tm M k = γ := hk
      refine ⟨(rep γ, k % M), ⟨Finset.mem_image_of_mem _ hγ, Nat.mod_lt _ (NeZero.pos M), ?_⟩, ?_⟩
      · show γ = rep γ * Tm M (k % M)
        rw [tm_mod_eq, hk]
      · rintro ⟨r, k'⟩ ⟨hr, hk', hγr⟩
        dsimp only at hr hk' hγr
        obtain ⟨γ1, -, rfl⟩ := Finset.mem_image.1 hr
        have hin1 : γ ∈ orb γ1 := by
          rw [← orb_eq γ1 (rep γ1) (rep_mem γ1)]
          exact ⟨k', hγr.symm⟩
        have hr1 : rep γ = rep γ1 := rep_eq γ1 γ hin1
        have hT : Tm M k' = Tm M (k % M) := by
          have e : rep γ1 * Tm M k' = rep γ1 * Tm M (k % M) := by
            rw [← hγr, tm_mod_eq, ← hr1, hk]
          exact mul_left_cancel e
        have := eq_of_tm_eq_of_lt M k' (k % M) hk' (Nat.mod_lt _ (NeZero.pos M)) hT
        simp only [Prod.mk.injEq]
        exact ⟨hr1.symm, this⟩
  · intro γ hγ r₀
    obtain ⟨hLG, hL⟩ := liftSL_mem_gam_and_map_eq_of_mem_gs N l M hM γ hγ
    obtain ⟨hL1, hL0⟩ := Subgroup.mem_inf.1 hLG
    rw [CongruenceSubgroup.Gamma1_mem] at hL1
    rw [CongruenceSubgroup.Gamma0_mem] at hL0
    have detL : (((liftSL M γ) 0 0 : ℤ) : ZMod l) * (((liftSL M γ) 1 1 : ℤ) : ZMod l) = 1 := by
      have h1 := (liftSL M γ).2
      rw [Matrix.det_fin_two] at h1
      have h2 := congrArg (Int.cast : ℤ → ZMod l) h1
      push_cast at h2
      rw [hL0, mul_zero, sub_zero] at h2
      exact h2
    have hL00 : (((liftSL M γ) 0 0 : ℤ) : ZMod l) ≠ 0 := left_ne_zero_of_mul_eq_one detL
    have hg00 : (((gm r₀) 0 0 : ℤ) : ZMod l) ≠ 0 := by
      intro h0
      have hc := hP.col r₀
      rw [h0, mul_zero] at hc
      have h1 := (gm r₀).2
      rw [Matrix.det_fin_two] at h1
      have h2 := congrArg (Int.cast : ℤ → ZMod l) h1
      push_cast at h2
      rw [h0, hc] at h2
      simp at h2
    refine ⟨hL, ?_, ?_, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (hP.g0 r₀) (by rw [CongruenceSubgroup.Gamma0_mem]; exact hL1.2.2)
    · have ga := hP.ga r₀
      simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at ga ⊢
      push_cast
      rw [hL1.1, hL1.2.2, mul_one, mul_zero, add_zero]
      exact ga
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      rw [hL0, mul_zero, add_zero]
      exact mul_ne_zero hg00 hL00
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      rw [hL0, mul_zero, add_zero, hP.col r₀]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 r₀.ne_zero) hg00) hL00
end

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem gal_mul' {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (s t : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal (s * t) f = X.gal s (X.gal t f) := by
  apply X.exp.toRingHom.injective
  show X.exp _ = X.exp _
  ext r
  simp [X.gal_exp]

private theorem kmap_comp' {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (φ ψ χ : X.K ≃+* X.K) (h : ∀ f, χ f = φ (ψ f)) (a : X.Khat l) : X.kmap l χ a = X.kmap l φ (X.kmap l ψ a) := by
  unfold Tower.kmap
  have e : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map χ.toMonoidHom))) =
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))) ∘ₗ
        (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map ψ.toMonoidHom))) := by
    ext u
    exact h _
  show AdicCompletion.map (idl l) _ a = AdicCompletion.map (idl l) _ (AdicCompletion.map (idl l) _ a)
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp, e]

theorem UpperTheory.Kd.L.witalg :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N n : ℕ), 1 ≤ N → (∀ (b b' : X.Fn l) (f f' : X.Kˣ), IsWit X N l n b f → IsWit X N l n b' f' → IsWit X N l n (b + b') (f * f')) ∧ IsWit X N l n 0 1 ∧ (∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (f : X.Kˣ), IsWit X N l n b f → IsWit X N l n (X.galB l s b) (Units.map (X.gal s).toMonoidHom f)) ∧ ∀ s t : Ω ≃ₐ[ℚ] Ω, ∀ b : X.Fn l, X.galB l (s * t) b = X.galB l s (X.galB l t b) := by
  intro Ω _ _ _ _ ε X l _ N n _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro b b' f f' ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun γ hγ => ?_, ?_, fun δ a c => ?_⟩
    · rw [Units.val_mul, map_mul, h1 γ hγ, k1 γ hγ]
    · rw [Pi.add_apply, map_add (f := _), h2, k2]
      unfold Tower.cls
      rw [← Submodule.Quotient.mk_add, ← TensorProduct.tmul_add, ofMul_mul]
    · obtain ⟨g, hg, e⟩ := h3 δ a c
      obtain ⟨g', hg', e'⟩ := k3 δ a c
      refine ⟨g * g', fun γ hγ => by rw [map_mul, hg γ hγ, hg' γ hγ], ?_⟩
      rw [Units.val_mul, map_mul, mul_pow, ← e, ← e']
      ring
  · refine ⟨fun γ _ => by simp, ?_, fun δ _ _ => ⟨1, fun γ _ => by simp, by simp⟩⟩
    simp [Tower.cls]
  · rintro s b f ⟨hfI, hcls, hδ⟩
    have hf : ((Units.map (X.gal s).toMonoidHom f : X.Kˣ) : X.K) = X.gal s f := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hf]; exact GlobalTheory.ThGal.inv_gal X s _ _ hfI
    · have hu : (![(![1, 0] : Fin 2 → ℤ_[l]) 0,
          (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1] : Fin 2 → ℤ_[l]) = ![1, 0] := by
        funext i; fin_cases i <;> simp
      have hg : X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![(![1, 0] : Fin 2 → ℤ_[l]) 0,
          (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1]) := rfl
      rw [hu] at hg
      rw [AdicCompletion.eval_apply] at hcls
      rw [hg, AdicCompletion.eval_apply, Tower.kmap]
      erw [AdicCompletion.map_val_apply]
      rw [hcls]
      simp [Tower.cls, LinearMap.reduceModIdeal_apply]
    · intro δ hδ1 hδ2
      obtain ⟨δ', h1, h2, hrec⟩ := GlobalTheory.ThGal.exists_twist X s N l n hl f hfI δ hδ1 hδ2
      obtain ⟨g, hg, hfg⟩ := hδ δ' h1 h2
      refine ⟨X.gal s g, GlobalTheory.ThGal.inv_gal X s _ _ hg, ?_⟩
      rw [hf, ← hrec, ← map_mul, hfg, map_pow]
  · intro s t b
    funext u
    show X.kmap l (X.gal (s * t)) (b ![u 0, (cyclotomicCharacter Ω l (s * t).toRingEquiv : ℤ_[l]) * u 1]) =
      X.kmap l (X.gal s) (X.kmap l (X.gal t) (b ![u 0, (cyclotomicCharacter Ω l t.toRingEquiv : ℤ_[l]) *
        ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1)]))
    have hm : (s * t).toRingEquiv = s.toRingEquiv * t.toRingEquiv := rfl
    rw [kmap_comp' X l _ _ _ (gal_mul' X s t), hm, map_mul, Units.val_mul, mul_left_comm, mul_assoc]
end
