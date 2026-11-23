module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle058
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle316
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
import Mathlib.Algebra.AffineMonoid.Basic
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
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
import Mathlib.NumberTheory.RamificationInertia.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017

@[expose] public section

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.BetaUniq

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem keeps_orth {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (P : Submodule E S.V)
    (hP : ∀ x ∈ P, γ x ∈ P) : ∀ x ∈ orth S P, γ x ∈ orth S P := by
  have hle : P.map (γ : S.V →ₗ[E] S.V) ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hP x hx
  have heq : P.map (γ : S.V →ₗ[E] S.V) = P :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq γ P)
  have hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y := hγ
  intro x hx
  rw [Formalism.MainNotions.mem_orth_iff] at hx ⊢
  intro y hy
  rw [← heq] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  exact (hiso y x).trans (hx y hy)

theorem exists_of_mem_gsmul {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {a : S.V}
    (h : a ∈ Ideal.span {(g : 𝓞 E)} • Λ) : ∃ l ∈ Λ, a = (g : E) • l := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨b, hb, rfl⟩ := h
  refine ⟨b, hb, ?_⟩
  rw [← algebraMap_smul E (g : 𝓞 E) b, map_natCast]

theorem gsmul_mem {Λ : Submodule (𝓞 E) S.V} (g : ℕ) {l : S.V} (hl : l ∈ Λ) :
    (g : E) • l ∈ Ideal.span {(g : 𝓞 E)} • Λ := by
  rw [← map_natCast (algebraMap (𝓞 E) E) g, algebraMap_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl

theorem int_pair {Λ : Submodule (𝓞 E) S.V} (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) :
    ∀ x ∈ Λ, ∀ y ∈ Λ, S.hT x y ∈ (1 : Submodule (𝓞 E) E) := fun x hx y hy => by
  rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hy
  exact hy x hx

theorem exists_sub_smul_mem_orth {r : ℕ} {T' : E} (A : LFlag S r T') (hT : T' ≠ 0) :
    ∀ x ∈ orth S (Xsp A), ∃ a : E, x - a • A.fl.z ∈ orth S (Xplus A) := by
  intro x hx
  rw [Formalism.MainNotions.mem_orth_iff] at hx
  refine ⟨S.hT A.fl.z x / (-T'), ?_⟩
  rw [Formalism.MainNotions.mem_orth_iff]
  refine Formalism.MainNotions.hT_zero_of_mem_Xplus A.fl (fun a => ?_) ?_
  · rw [map_sub, map_smul, A.fl.z_orth, smul_zero, sub_zero]
    exact hx _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [map_sub, map_smul, A.fl.z_norm, smul_eq_mul, div_mul_cancel₀ _ (neg_ne_zero.2 hT), sub_self]

end GlobalTheory.LoopC.BetaUniq

namespace GlobalTheory.LoopC.BetaUniq

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (A B : LFlag S r T')
    (β₁ β₂ : S.V ≃ₗ[E] S.V), Submodule.IsLattice E Λ → Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → 3 ≤ g → T' ≠ 0 →
    (∀ x ∈ orth S (Xplus A), x ∉ Xsp A → 0 < Algebra.trace ℚ E (S.hT x x)) →
    XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ A →
    XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B →
    IsAutLam S Λ β₁ → (Xsp A).map (β₁ : S.V →ₗ[E] S.V) = Xsp B → β₁ A.fl.z - B.fl.z ∈ Xsp B →
    IotaCompat Λ F A B β₁ g →
    IsAutLam S Λ β₂ → (Xsp A).map (β₂ : S.V →ₗ[E] S.V) = Xsp B → β₂ A.fl.z - B.fl.z ∈ Xsp B →
    IotaCompat Λ F A B β₂ g → ∀ x ∈ orth S (Xsp A), β₁ x - β₂ x ∈ Xsp B := by
  intro E _ _ _ S r T T' Λ g F A B β₁ β₂ hΛ hu hg hT' hpos hFA hFB h1a h1X h1z h1ι h2a h2X h2z h2ι
  have hg0 : (g : E) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hΛ₁ : ∀ x, β₁ x ∈ Λ ↔ x ∈ Λ := FrEqv.aut_mem_iff h1a
  have hΛ₂ : ∀ x, β₂ x ∈ Λ ↔ x ∈ Λ := FrEqv.aut_mem_iff h2a
  have hΛ₁' : ∀ x, β₁.symm x ∈ Λ ↔ x ∈ Λ := fun x => by
    rw [← hΛ₁ (β₁.symm x), LinearEquiv.apply_symm_apply]
  have hX₁ : ∀ x ∈ Xsp A, β₁ x ∈ Xsp B := fun x hx => h1X ▸ Submodule.mem_map_of_mem hx
  have hX₂ : ∀ x ∈ Xsp A, β₂ x ∈ Xsp B := fun x hx => h2X ▸ Submodule.mem_map_of_mem hx
  have hX₁' : ∀ y ∈ Xsp B, β₁.symm y ∈ Xsp A := fun y hy => by
    rw [← h1X] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  set δ : S.V ≃ₗ[E] S.V := β₁⁻¹ * β₂ with hδ_def
  have hδ_apply : ∀ x, δ x = β₁.symm (β₂ x) := fun x => by
    rw [hδ_def, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  have hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT := mul_mem (inv_mem h1a.1) h2a.1
  have hδX : ∀ x ∈ Xsp A, δ x ∈ Xsp A := fun x hx => by
    rw [hδ_apply]; exact hX₁' _ (hX₂ x hx)
  have hδz : δ A.fl.z - A.fl.z ∈ Xsp A := by
    have e : δ A.fl.z - A.fl.z = β₁.symm (β₂ A.fl.z - β₁ A.fl.z) := by
      rw [hδ_apply, map_sub, LinearEquiv.symm_apply_apply]
    rw [e]
    refine hX₁' _ ?_
    have := (Xsp B).sub_mem h2z h1z
    convert this using 1; abel
  have hδXp : ∀ x ∈ Xplus A, δ x ∈ Xplus A := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [map_add (f := _), map_smul]
    refine (Xplus A).add_mem (Submodule.mem_sup_left (hδX a ha)) ?_
    have e : c • δ A.fl.z = c • (δ A.fl.z - A.fl.z) + c • A.fl.z := by rw [← smul_add]; congr 1; abel
    rw [e]
    exact (Xplus A).add_mem (Submodule.mem_sup_left ((Xsp A).smul_mem c hδz))
      (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)))
  set U : Submodule E S.V := orth S (Xplus A) with hU_def
  have hδU : ∀ x ∈ U, δ x ∈ U := keeps_orth hδ _ hδXp
  have hXU : Xsp A ≤ U := Formalism.MainNotions.X_le_orth_Xplus A.fl
  have hrad : ∀ x ∈ Xsp A, ∀ y ∈ U, S.hT x y = 0 := fun x hx y hy =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 hy x (Submodule.mem_sup_left hx)
  have hrad' : ∀ y ∈ U, ∀ x ∈ Xsp A, S.hT y x = 0 := fun y hy x hx =>
    Formalism.MainNotions.hT_swap_zero (hrad x hx y hy)
  set M : Submodule (𝓞 E) S.V := Λ ⊓ toO S U with hM_def
  have hM : ∀ x, x ∈ M ↔ x ∈ Λ ∧ x ∈ U := fun x => Iff.rfl
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ.fg
  have hMfg : M.FG := Submodule.FG.of_le_of_isNoetherian (T := Λ) inf_le_left
  have hint := int_pair hu
  have hUXA : U ≤ orth S (Xsp A) := fun y hy => by
    rw [Formalism.MainNotions.mem_orth_iff] at hy ⊢
    exact fun x hx => hy x (Submodule.mem_sup_left hx)

  have hcong : ∀ x ∈ M, ∃ y ∈ M, δ x - x - (g : E) • y ∈ Xsp A := by
    intro x hx
    obtain ⟨hxΛ, hxU⟩ := (hM x).1 hx

    obtain ⟨l', hl'Λ, hl'⟩ := GlobalTheory.Mass.RowPerp.exists_sub_mem S.herm S.nondeg hΛ hu (orth S (Xsp F))
      ((g : E)⁻¹ • x) (fun y hyΛ hy => by
        have hyX : y ∈ Xsp F := GlobalTheory.Mass.RowPerp.mem_of_perp_perp S.nondeg (Xsp F) y fun w hw =>
          Formalism.MainNotions.hT_swap_zero (hy w ((Formalism.MainNotions.mem_orth_iff _ _).2 hw))
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hFA (Submodule.mem_inf.2 ⟨hyΛ, hyX⟩))
        obtain ⟨l, hlΛ, rfl⟩ := exists_of_mem_gsmul ha
        obtain ⟨t, ht⟩ := Submodule.mem_one.1 (hint x hxΛ l hlΛ)
        refine Submodule.mem_one.2 ⟨t, ?_⟩
        rw [LinearMap.map_smulₛₗ S.hT, LinearMap.smul_apply, map_add (f := _), map_smul,
          hrad' x hxU b (Submodule.mem_inf.1 hb).2, add_zero, starRingEnd_apply, star_inv₀, star_natCast,
          smul_eq_mul, smul_eq_mul, ht, inv_mul_cancel_left₀ hg0])
    set l : S.V := x - (g : E) • l' with hl_def
    have hlΛ : l ∈ Λ := by
      rw [hl_def, ← map_natCast (algebraMap (𝓞 E) E) g, algebraMap_smul]
      exact Λ.sub_mem hxΛ (Λ.smul_mem _ hl'Λ)
    have hlF : l ∈ Lrep Λ F := by
      refine Submodule.mem_inf.2 ⟨hlΛ, ?_⟩
      have e : l = (g : E) • ((g : E)⁻¹ • x - l') := by
        rw [hl_def, smul_sub, smul_smul, mul_inv_cancel₀ hg0, one_smul]
      rw [e]
      exact (orth S (Xsp F)).smul_mem _ hl'
    have hlx : l - x ∈ NgX Λ g F A := by
      have e : l - x = (g : E) • (-l') := by rw [hl_def, smul_neg]; abel
      rw [e]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (gsmul_mem g (Λ.neg_mem hl'Λ)))
    have hxA : x ∈ Lrep Λ A := Submodule.mem_inf.2 ⟨hxΛ, hUXA hxU⟩
    have hb1 : l - β₁ x ∈ NgX Λ g F B := (h1ι x hxA l hlF).1 hlx
    have hb2 : l - β₂ x ∈ NgX Λ g F B := (h2ι x hxA l hlF).1 hlx
    have hdiff : β₂ x - β₁ x ∈ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B := by
      have hle : NgX Λ g F B ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B :=
        sup_le (sup_le le_sup_left hFB) le_sup_right
      have := (NgX Λ g F B).sub_mem hb1 hb2
      refine hle ?_
      convert this using 1; abel
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hdiff
    obtain ⟨lam, hlam, rfl⟩ := exists_of_mem_gsmul ha
    have hbA : β₁.symm b ∈ Xsp A := hX₁' b (Submodule.mem_inf.1 hb).2
    have key : δ x - x - (g : E) • β₁.symm lam = β₁.symm b := by
      have e : b = (β₂ x - β₁ x) - (g : E) • lam := by rw [← hab]; abel
      rw [e, map_sub, map_sub, map_smul, LinearEquiv.symm_apply_apply, hδ_apply]
    refine ⟨β₁.symm lam, (hM _).2 ⟨(hΛ₁' lam).2 hlam, ?_⟩, ?_⟩
    · have e : β₁.symm lam = (g : E)⁻¹ • (δ x - x - β₁.symm b) := by
        rw [← key, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hg0, one_smul]
      rw [e]
      exact U.smul_mem _ (U.sub_mem (U.sub_mem (hδU x hxU) hxU) (hXU hbA))
    · rw [key]; exact hbA
  have hmain : ∀ x ∈ M, δ x - x ∈ Xsp A :=
    GlobalTheory.isom_sub_mem_of_congr E S.V S.hT U (Xsp A) M δ g S.herm hXU hrad hpos hMfg
      (fun x hx => ((hM x).1 hx).2) hδ hδX hg hcong

  have hext : ∀ x ∈ orth S (Xsp A), δ x - x ∈ Xsp A := by
    intro x hx
    obtain ⟨a, hy⟩ := exists_sub_smul_mem_orth A hT' x hx
    set y := x - a • A.fl.z with hy_def
    have hfull : Submodule.IsFullLattice E Λ :=
      { toIsLattice := hΛ, span_eq_top := GlobalTheory.LoopC.FunIdx.span_eq_top_of_unimodular Λ hΛ hu }
    obtain ⟨d, hd0, hd⟩ := GlobalTheory.Mass.RowPerp.exists_smul_mem hfull y
    have hdM : d • y ∈ M := (hM _).2 ⟨hd, by
      rw [← algebraMap_smul E d y]; exact U.smul_mem _ hy⟩
    have h1 := hmain _ hdM
    rw [← algebraMap_smul E d y, map_smul, ← smul_sub] at h1
    have hyX : δ y - y ∈ Xsp A :=
      (Submodule.smul_mem_iff _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)).1 h1
    have e : δ x - x = a • (δ A.fl.z - A.fl.z) + (δ y - y) := by
      rw [hy_def, map_sub, map_smul, smul_sub]; abel
    rw [e]
    exact (Xsp A).add_mem ((Xsp A).smul_mem a hδz) hyX
  intro x hx
  have e : β₁ x - β₂ x = -(β₁ (δ x - x)) := by
    rw [hδ_apply, map_sub, LinearEquiv.apply_symm_apply, neg_sub]
  rw [e]
  exact (Xsp B).neg_mem (hX₁ _ (hext x hx))

end GlobalTheory.LoopC.BetaUniq
end

section

namespace GlobalTheory.RankSplit

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

private lemma span_prime_isMaximal' {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
private lemma liesOver_span_of_prime_natCast_mem {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (P : Ideal A) [hP : P.IsPrime]
    (h : (p : A) ∈ P) : P.LiesOver (Ideal.span {(p : ℤ)}) := by
  refine ⟨(span_prime_isMaximal' hp).eq_of_le (Ideal.IsPrime.comap (algebraMap ℤ A)).ne_top ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
  simpa using h

theorem ncard_primesOver_of_norm {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) → Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  classical
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
  haveI := span_prime_isMaximal' hp
  rw [← Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 E) ℚ E hp0,
    ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at hP
  obtain ⟨hPp, hPl⟩ := hP
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  haveI hPm : P.IsMaximal := hPp.isMaximal hPne
  have hpP : (p : 𝓞 E) ∈ P := by
    have := (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using this
  obtain ⟨hn, hsq⟩ := h P hPm hpP
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have he : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmap, pow_one, Ideal.span_singleton_le_iff_mem]
      exact hpP
    · rw [hmap, Ideal.span_singleton_le_iff_mem]
      exact hsq
  have hf : Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) P = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    have h1 := Ideal.pow_inertiaDeg p P
    rw [hn] at h1
    exact (Nat.pow_eq_self_iff hp.one_lt).mp h1
  rw [he, hf]

theorem splitsF_of_norm : ∀ (D : D7) (p : ℕ), p.Prime →
    (∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ((p : 𝓞 D.host.E) ∈ P) →
      Ideal.absNorm P = p ∧ (p : 𝓞 D.host.E) ∉ P ^ 2) → StandardLattice.SplitsF D p := by
  intro D p hp h
  have hE := ncard_primesOver_of_norm hp h
  have hF := GlobalTheory.ColClassCompare.ncard_primesOver_of_split (F := D.host.F) hp hE
  rw [GlobalTheory.ColClassCompare.finrank_F] at hF
  refine ⟨?_, fun v hv => (GlobalTheory.ColClassCompare.unram_card_of_split (F := D.host.F) hp hE v.asIdeal hv).2⟩
  rw [← hF, ← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun v => ⟨v.1.asIdeal, v.1.isPrime, liesOver_span_of_prime_natCast_mem hp v.1.asIdeal v.2⟩
      invFun := fun P => ⟨⟨P.1, P.2.1, ?_⟩, ?_⟩
      left_inv := fun v => rfl
      right_inv := fun P => rfl }
  · have := P.2.2
    have h0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
    exact Ideal.ne_bot_of_liesOver_of_ne_bot h0 P.1
  · have := P.2.2
    have h2 := (Ideal.mem_of_liesOver P.1 (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using h2

end GlobalTheory.RankSplit
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitUniq

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem le_one_iff_frac {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (ν : Valuation K Γ) (P : Ideal R)
    [P.IsPrime] (hP0 : P ≠ ⊥) (hle : ∀ r : R, ν (algebraMap R K r) ≤ 1)
    (hlt : ∀ r : R, ν (algebraMap R K r) < 1 ↔ r ∈ P) (x : K) :
    ν x ≤ 1 ↔ ∃ y s : R, s ∉ P ∧ x = algebraMap R K y / algebraMap R K s := by
  have hunit : ∀ s : R, s ∉ P → ν (algebraMap R K s) = 1 := fun s hs =>
    le_antisymm (hle s) (not_lt.mp fun h => hs ((hlt s).1 h))
  constructor
  · intro hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hq0 : algebraMap R K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP0 (Localization.AtPrime P)
    have hinj : Function.Injective (algebraMap R (Localization.AtPrime P)) :=
      IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
    have key : ∀ a b : R, ∀ (y : R) (s : P.primeCompl),
        algebraMap R (Localization.AtPrime P) a * IsLocalization.mk' (Localization.AtPrime P) y s =
          algebraMap R (Localization.AtPrime P) b → a * y = b * s := by
      intro a b y s h
      apply hinj
      have h2 := congrArg (· * algebraMap R (Localization.AtPrime P) (s : R)) h
      simp only [mul_assoc, IsLocalization.mk'_spec] at h2
      simpa [map_mul] using h2
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime P) p)
      (algebraMap R (Localization.AtPrime P) q)
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    rcases hc with hc | hc
    ·
      have e := key p q y s hc
      by_cases hy : y ∈ P
      · by_cases hp : p = 0
        · exact ⟨0, 1, P.ne_top_iff_one.mp (Ideal.IsPrime.ne_top inferInstance), by simp [hp]⟩
        · exfalso
          have hp0 : ν (algebraMap R K p) ≠ 0 := by
            rw [Valuation.ne_zero_iff]
            exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hp
          have hq' : ν (algebraMap R K q) ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
          have e2 : ν (algebraMap R K p) * ν (algebraMap R K y) = ν (algebraMap R K q) := by
            rw [← map_mul, ← map_mul, e, map_mul, map_mul, hunit _ s.2, mul_one]
          rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hq')] at hx
          have : ν (algebraMap R K p) * ν (algebraMap R K y) < ν (algebraMap R K p) * 1 :=
            mul_lt_mul_of_pos_left ((hlt y).2 hy) (zero_lt_iff.mpr hp0)
          rw [e2, mul_one] at this
          exact absurd hx (not_le.mpr this)
      · refine ⟨s, y, hy, ?_⟩
        have hy0 : algebraMap R K y ≠ 0 := by
          intro h0
          apply hy
          rw [(map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h0]
          exact P.zero_mem
        rw [div_eq_div_iff hq0 hy0, ← map_mul, ← map_mul, e, mul_comm]
    ·
      have e := key q p y s hc
      refine ⟨y, s, s.2, ?_⟩
      have hs0 : algebraMap R K (s : R) ≠ 0 := by
        intro h0
        apply s.2
        rw [(map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h0]
        exact P.zero_mem
      rw [div_eq_div_iff hq0 hs0, ← map_mul, ← map_mul, ← e, mul_comm]
  · rintro ⟨y, s, hs, rfl⟩
    rw [map_div₀, hunit s hs, div_one]
    exact hle y

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem exists_approx (v : HeightOneSpectrum (𝓞 L⁺)) (y d : v.adicCompletion L⁺) (hd : d ≠ 0) :
    ∃ a : L⁺, Valued.v (y - algebraMap L⁺ (v.adicCompletion L⁺) a) < Valued.v d := by
  have hU : IsOpen {z : v.adicCompletion L⁺ | Valued.v (z - y) < Valued.v d} := by
    have h := (Valued.isOpen_ball (v.adicCompletion L⁺) (Valued.v.restrict d)).preimage (continuous_sub_right y)
    convert h using 2 with z
    simp [Valuation.restrict_lt_iff]
  have hy : y ∈ {z : v.adicCompletion L⁺ | Valued.v (z - y) < Valued.v d} := by
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hd)
  obtain ⟨z, hz, a, rfl⟩ := mem_closure_iff_nhds.mp (denseRange_algebraMap L⁺ v y) _ (hU.mem_nhds hy)
  refine ⟨a, ?_⟩
  rw [← Valuation.map_neg, neg_sub]
  exact hz

theorem eq_of_le_one_iff (v : HeightOneSpectrum (𝓞 L⁺)) (i i' : L →ₐ[L⁺] v.adicCompletion L⁺)
    (h : ∀ x : L, Valued.v (i x) ≤ 1 ↔ Valued.v (i' x) ≤ 1) : i = i' := by
  refine AlgHom.ext fun x => ?_
  by_contra hne
  set δ := i x - i' x with hδ
  have hδ0 : Valued.v δ ≠ 0 := (Valuation.ne_zero_iff _).mpr (sub_ne_zero.mpr hne)
  obtain ⟨a, ha⟩ := exists_approx v (i x) δ (sub_ne_zero.mpr hne)
  obtain ⟨b, hb⟩ := exists_approx v δ δ (sub_ne_zero.mpr hne)
  set b' := algebraMap L⁺ (v.adicCompletion L⁺) b
  set a' := algebraMap L⁺ (v.adicCompletion L⁺) a
  have hbv : Valued.v b' = Valued.v δ := by
    have : b' = δ - (δ - b') := by ring
    rw [this, Valuation.map_sub_eq_of_lt_left _ hb]
  have hb0 : Valued.v b' ≠ 0 := hbv ▸ hδ0
  have hbne : b' ≠ 0 := (Valuation.ne_zero_iff _).mp hb0
  set z : L := (x - algebraMap L⁺ L a) / algebraMap L⁺ L b
  have hiz : i z = (i x - a') / b' := by simp [z, a', b', map_div₀, map_sub, AlgHom.commutes]
  have hi'z : i' z = (i' x - a') / b' := by simp [z, a', b', map_div₀, map_sub, AlgHom.commutes]
  have hlt : Valued.v (i z) < 1 := by
    rw [hiz, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hb0), hbv]
    exact ha
  have heq : Valued.v (i' z) = 1 := by
    have : i' x - a' = (i x - a') - δ := by rw [hδ]; ring
    rw [hi'z, map_div₀, this, Valuation.map_sub_eq_of_lt_right _ ha, hbv, div_self hδ0]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at heq
    exact zero_ne_one heq
  have hinv : Valued.v (i' z⁻¹) ≤ 1 := by rw [map_inv₀, map_inv₀, heq, inv_one]
  have h2 := (h z⁻¹).2 hinv
  have h3 : Valued.v (i z) * Valued.v (i z⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hz0, map_one, map_one]
  have h4 : Valued.v (i z) * Valued.v (i z⁻¹) < 1 := mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at h4
  exact lt_irrefl _ h4

theorem splitPlace_eq_of_w_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (s s' : ReciprocityTheory.Aut.SplitPlace L), s.w = s'.w → s = s' := by
  intro L _ _ _ s s' h
  have hv : s.v = s'.v := by
    apply HeightOneSpectrum.ext
    rw [← s.w_under, ← s'.w_under, h]
  have hid : s.ideal = s'.ideal := congrArg HeightOneSpectrum.asIdeal h
  obtain ⟨v, i⟩ := s
  obtain ⟨v', i'⟩ := s'
  simp only at hv
  subst hv
  congr 1
  haveI : (ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, i⟩).IsPrime := ReciprocityTheory.Aut.SplitPlace.ideal_isPrime _
  have hP0 := ReciprocityTheory.Aut.SplitPlace.ideal_ne_bot (⟨v, i⟩ : ReciprocityTheory.Aut.SplitPlace L)
  have H := fun (j : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
      (hj : ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, j⟩ = ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, i⟩) (x : L) =>
    le_one_iff_frac (R := 𝓞 L) (Valued.v.comap (j : L →+* v.adicCompletion (maximalRealSubfield L)))
      (ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, i⟩) hP0
      (fun r => ReciprocityTheory.Aut.SplitPlace.split_le_one ⟨v, j⟩ r)
      (fun r => by rw [← hj]; exact (ReciprocityTheory.Aut.SplitPlace.split_mem_ideal ⟨v, j⟩ r).symm) x
  apply eq_of_le_one_iff v i i'
  intro x
  have h1 := H i rfl x
  have h2 := H i' hid.symm x
  simp only [Valuation.comap_apply] at h1 h2
  exact h1.trans h2.symm

end GlobalTheory.SplitUniq
end
end
