module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersOfGenerators
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle348
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.EpiMono
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.SplitFlip.FourierDepth

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type*} [DecidableEq D]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem setCols_add (P : Finset D) (Y Z : Matrix A D k) (T : Matrix A P k) :
    setCols P (Y + Z) T = setCols P Y T + setCols P Z 0 := by
  ext i j
  by_cases h : j ∈ P <;> simp [setCols, h]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D] in
theorem pairCols_add [Fintype A] (P : Finset D) (Y Z : Matrix A D k) (T : Matrix A P k) :
    pairCols P (Y + Z) T = pairCols P Y T + pairCols P Z T := by
  simp [pairCols, mul_add, Finset.sum_add_distrib]


omit [DecidableEq D] in
theorem mem_matLat_diagLat {c : D → kˣ} {X : Matrix A D k} :
    X ∈ matLat A (diagLat c) ↔ ∀ i j, valuation k (X i j) ≤ valuation k (c j : k) := Iff.rfl


omit [DecidableEq D] in
theorem mem_matLat_smul_stdLat {c : kˣ} {X : Matrix A D k} :
    X ∈ matLat A (c • stdLat k D) ↔ ∀ i j, valuation k (X i j) ≤ valuation k (c : k) := by
  rw [stdLat, smul_diagLat, mem_matLat_diagLat]
  simp

theorem mem_matLat_blockLat {ϖ : kˣ} {e : ℕ} {P : Finset D} {X : Matrix A D k} :
    X ∈ matLat A (blockLat ϖ e P) ↔
      (∀ i, ∀ j ∈ P, ((ϖ ^ e : kˣ) : k) * X i j ∈ 𝒪[k]) ∧ ∀ i, ∀ j ∉ P, X i j ∈ 𝒪[k] := by
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  have h1 : ∀ x : k, ((ϖ ^ e : kˣ) : k) * x ∈ 𝒪[k] ↔
      valuation k x ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k) := fun x => by
    rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, mul_comm, ← le_mul_inv_iff₀ h0, one_mul]
  rw [blockLat, mem_matLat_diagLat]
  simp only [h1]
  constructor
  · intro h
    exact ⟨fun i j hj => by simpa only [blockUnits, if_pos hj] using h i j,
      fun i j hj => by simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j⟩
  · rintro ⟨h, h'⟩ i j
    by_cases hj : j ∈ P
    · simpa only [blockUnits, if_pos hj] using h i j hj
    · simpa [blockUnits, hj, Valuation.mem_integer_iff] using h' i j hj

theorem mem_matLat_smul_blockLat {ϖ : kˣ} {e : ℕ} {P : Finset D} {X : Matrix A D k} :
    X ∈ matLat A (ϖ ^ e • blockLat ϖ e P) ↔
      (∀ i, ∀ j ∈ P, X i j ∈ 𝒪[k]) ∧ ∀ i, ∀ j ∉ P, valuation k (X i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  rw [blockLat, smul_diagLat, mem_matLat_diagLat]
  constructor
  · intro h
    exact ⟨fun i j hj => by simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j,
      fun i j hj => by simpa only [blockUnits, if_neg hj, mul_one] using h i j⟩
  · rintro ⟨h, h'⟩ i j
    by_cases hj : j ∈ P
    · simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j hj
    · simpa only [blockUnits, if_neg hj, mul_one] using h' i j hj

variable [Fintype A] [DecidableEq A]

theorem hasDepth_fourierSum {ψ : AddChar k Circle} {ϖ : kˣ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) {Φ : Matrix A D k → ℂ} (hΦ : IsNatDatum ϖ e Φ) :
    HasDepth ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hc : ((ϖ ^ e : kˣ) : k) ∈ 𝒪[k] := by
    rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem e
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · rw [fourierSum_apply]
    split_ifs with h
    · rw [Finset.sum_eq_zero, mul_zero]
      intro T _
      rw [hΦ.1, zero_mul]
      intro H
      refine hY (mem_matLat_blockLat.2 ⟨h, fun i j hj => ?_⟩)
      simpa [setCols, hj] using mem_matLat_stdLat.1 H i j
    · rfl
  · obtain ⟨h1, h2⟩ := mem_matLat_smul_blockLat.1 hZ
    rw [fourierSum_apply, fourierSum_apply]
    refine if_congr (forall_congr' fun i => forall₂_congr fun j hj => ?_) ?_ rfl
    · rw [Matrix.add_apply, mul_add, add_mem_cancel_right (mul_mem hc (h1 i j hj))]
    · congr 1
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [setCols_add, pairCols_add, hΦ.2, AddChar.map_add_eq_mul, triv (pairCols P Z _), mul_one]
      · exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (liftRes_mem T i j) (h1 i j j.2)
      · refine mem_matLat_smul_stdLat.2 fun i j => ?_
        by_cases hj : j ∈ P
        · simp [setCols, hj]
        · simpa only [setCols, of_apply, dif_neg hj] using h2 i j hj

theorem isNatDatum_invFourierSum {ψ : AddChar k Circle} {ϖ : kˣ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) {Ψ : Matrix A D k → ℂ} (hΨ : HasDepth ϖ e (blockLat ϖ e P) Ψ) :
    IsNatDatum ϖ e (invFourierSum ψ ϖ e P Ψ) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hc : ((ϖ ^ e : kˣ) : k) ∈ 𝒪[k] := by
    rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem e
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · rw [invFourierSum_apply]
    split_ifs with h
    · refine Finset.sum_eq_zero fun S _ => ?_
      rw [hΨ.1, zero_mul]
      intro H
      refine hY (mem_matLat_stdLat.2 fun i j => ?_)
      by_cases hj : j ∈ P
      · exact h i j hj
      · simpa only [setCols, of_apply, dif_neg hj] using (mem_matLat_blockLat (ϖ := ϖ) (e := e) (P := P) |>.1 H).2 i j hj
    · rfl
  · have h1 := mem_matLat_smul_stdLat.1 hZ
    rw [invFourierSum_apply, invFourierSum_apply]
    refine if_congr (forall_congr' fun i => forall₂_congr fun j _ => ?_) ?_ rfl
    · rw [Matrix.add_apply, add_mem_cancel_right (show Z i j ∈ 𝒪[k] from (Valuation.mem_integer_iff _ _).2
        ((h1 i j).trans ((Valuation.mem_integer_iff _ _).1 hc)))]
    · refine Finset.sum_congr rfl fun S _ => ?_
      rw [setCols_add, pairCols_add, hΨ.2, neg_add, AddChar.map_add_eq_mul, triv (-pairCols P Z _), mul_one]
      · refine neg_mem (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_)
        have h2 : (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j ∈ 𝒪[k] := by
          rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
          exact h1 i j
        convert mul_mem (liftRes_mem S i j) h2 using 1
        simp only [Matrix.smul_apply, Units.smul_def, smul_eq_mul]
        ring
      · refine mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
        · simp [setCols, hj]
        · simpa only [setCols, of_apply, dif_neg hj] using h1 i j

end GlobalTheory.SplitFlip.FourierDepth

theorem GlobalTheory.SplitFlip.FourierDepth.fourier_exchange (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) :
    (∀ Φ : Matrix A D k → ℂ, IsNatDatum ϖ e Φ → HasDepth ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ)) ∧
      ∀ Ψ : Matrix A D k → ℂ, HasDepth ϖ e (blockLat ϖ e P) Ψ → IsNatDatum ϖ e (invFourierSum ψ ϖ e P Ψ) :=
  ⟨fun _ h => hasDepth_fourierSum hϖ hψ e P h, fun _ h => isNatDatum_invFourierSum hϖ hψ e P h⟩
end
end

section

noncomputable section

open GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lact {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ) :
    Matrix (Fin n) (Fin d) k → ℂ :=
  fun Y => (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2) * Ψ ((g.1)ᵀ * Y)


variable (k) in
def fullRk (n d : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) where
  carrier := {Ψ | Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) ∧ ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ Y = 0}
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => rfl⟩
  add_mem' := fun ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun Y hY => by simp [ha.2 Y hY, hb.2 Y hY]⟩
  smul_mem' := fun c _ ha => ⟨Submodule.smul_mem _ c ha.1, fun Y hY => by simp [ha.2 Y hY]⟩

def augRk (n d : ℕ) (ν : kˣ →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ g : GL (Fin n) k, ∃ Ψ ∈ fullRk k n d, z = lact ν g Ψ - Ψ}


variable (k) in
def Y0 (n d : ℕ) : Matrix (Fin n) (Fin d) k := Matrix.of fun i j => if (j : ℕ) = d - n + i then 1 else 0


variable (k) in
def indSp (n d : ℕ) (ν : kˣ →* ℂˣ) : Submodule ℂ (GL (Fin d) k → ℂ) where
  carrier := {f | (∃ U ∈ nhds (1 : GL (Fin d) k), ∀ h, ∀ u ∈ U, f (h * u) = f h) ∧
    ∀ (b h : GL (Fin d) k) (D : GL (Fin n) k), Y0 k n d * b.1 = D.1 * Y0 k n d →
      f (b * h) = (((ν (gdet D))⁻¹ : ℂˣ) : ℂ) * apow (gdet D) (-(d : ℂ) / 2) * f h}
  zero_mem' := ⟨⟨Set.univ, Filter.univ_mem, fun _ _ _ => rfl⟩, fun _ _ _ _ => by simp⟩
  add_mem' := by
    rintro f g ⟨⟨U, hU, hf⟩, hf'⟩ ⟨⟨V, hV, hg⟩, hg'⟩
    refine ⟨⟨U ∩ V, Filter.inter_mem hU hV, fun h u hu => ?_⟩, fun b h D hD => ?_⟩
    · simp [hf h u hu.1, hg h u hu.2]
    · simp [hf' b h D hD, hg' b h D hD, mul_add]
  smul_mem' := by
    rintro c f ⟨⟨U, hU, hf⟩, hf'⟩
    refine ⟨⟨U, hU, fun h u hu => ?_⟩, fun b h D hD => ?_⟩
    · simp [hf h u hu]
    · simp [hf' b h D hD]; ring

end GlobalTheory.FullRankCoinv
end
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.exists_dividedPowers_of_comp_on_generators : ∀ (B : Type) [CommRing B] (J : Ideal B) (γ : ℕ → B → B) (s : Set B), IsPreDP J γ → J = Ideal.span s → (∀ x ∈ s, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) → ∃ δ : DividedPowers J, δ.dpow = γ := by
  first | exact @GlobalTheory.PDA.exists_dividedPowers_of_comp_on_gens | exact GlobalTheory.PDA.exists_dividedPowers_of_comp_on_gens | (intros; apply GlobalTheory.PDA.exists_dividedPowers_of_comp_on_gens <;> assumption)
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.exists_lift_and_augmentation_map : ∀ (B : Type) [CommRing B] (Q : PDPoly B), (∀ (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C), c 0 = 1 → (∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) → ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n) ∧ ∃ ε : Q.P →ₐ[B] B, ∀ p, p ∈ Q.aug ↔ ε p = 0 := by
  first | exact @GlobalTheory.PDA.PDPoly.exists_lift_and_aug | exact GlobalTheory.PDA.PDPoly.exists_lift_and_aug | (intros; apply GlobalTheory.PDA.PDPoly.exists_lift_and_aug <;> assumption)
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.exists_isPreDividedPowers_augmentationIdeal : ∀ (B : Type) [CommRing B] (Q : PDPoly B), ∃ η : ℕ → Q.P → Q.P, IsPreDP Q.aug η ∧ ∀ n k : ℕ, η n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
  first | exact @GlobalTheory.PDA.exists_isPreDividedPowers_augmentation | exact GlobalTheory.PDA.exists_isPreDividedPowers_augmentation | (intros; apply GlobalTheory.PDA.exists_isPreDividedPowers_augmentation <;> assumption)
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.exists_isPreDividedPowers_of_generators : ∀ (B ι : Type) [CommRing B] (x : ι → B) (g : ι → ℕ → B), (∀ i, g i 0 = 1) → (∀ i, g i 1 = x i) → (∀ i n, n ≠ 0 → g i n ∈ Ideal.span (Set.range x)) → (∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n)) → (∀ c : ι →₀ B, (c.sum fun i a ↦ a * x i) = 0 → (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * g i n) = 1) → ∃ γ : ℕ → B → B, IsPreDP (Ideal.span (Set.range x)) γ ∧ ∀ i n, γ n (x i) = g i n := by
  first | exact @GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ | exact GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ | (intros; apply GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ <;> assumption)
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.derivation_dividedPowerFiltration_succ_le : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J) (D : Derivation R B M) (N₀ : Submodule B M), (∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) → ∀ N, ∀ x ∈ fil δ (N + 1), D x ∈ fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  first | exact @GlobalTheory.DerFil.deriv_fil_succ_le | exact GlobalTheory.DerFil.deriv_fil_succ_le | (intros; apply GlobalTheory.DerFil.deriv_fil_succ_le <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KumRoots

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  choose R hR hRQ using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h V g (hSP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => R V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hR V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hRQ V g hg W k hk

abbrev unitsP : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} ℤ) := Scheme.Γ ⋙ unitsF

theorem unitSec_eq {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) :
    unitSec u = ((toSheafify Scheme.etaleTopology unitsP).app (op U)).hom (ULift.up (Additive.ofMul u)) := rfl

theorem res_unitSec {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  have := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology unitsP).naturality g.op)
    (ULift.up (Additive.ofMul u))
  exact this.symm

theorem unitSec_pow {U : Scheme.{0}} (q : ℕ) (v : (Γ(U, ⊤))ˣ) :
    unitSec (v ^ q) = Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec v) := by
  have h1 : (ULift.up (Additive.ofMul (v ^ q)) : unitsP.obj (op U)) = (q : ℤ) • ULift.up (Additive.ofMul v) := by
    apply ULift.ext
    change Additive.ofMul (v ^ q) = (q : ℤ) • Additive.ofMul v
    rw [natCast_zsmul, ofMul_pow]
  change _ = (q : ℤ) • unitSec v
  rw [unitSec_eq, unitSec_eq, h1]
  exact map_zsmul ((toSheafify Scheme.etaleTopology unitsP).app (op U)).hom (q : ℤ) _

end GlobalTheory.EtC.KumRoots

namespace GlobalTheory.EtC.KumRoots

theorem res_comp {V W U : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (x : Sec Gm U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  change (Gm.obj.map (k ≫ g).op).hom x = (Gm.obj.map k.op).hom ((Gm.obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem units_map_comp {X W U : Scheme.{0}} (k : X ⟶ W) (f : W ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ f).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map f.appTop.hom.toMonoidHom u) := by
  apply Units.ext
  change (k ≫ f).appTop.hom (u : Γ(U, ⊤)) = k.appTop.hom (f.appTop.hom u)
  rw [Scheme.Hom.comp_appTop]; rfl

theorem roots : ∀ (q : ℕ) [NeZero q],
    (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
      Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  intro q _ hyp U hq u
  refine loc_bind (hyp U hq (unitSec u)) ?_
  rintro V g ⟨c, hc⟩
  refine loc_bind (P := fun W h => ∃ v : (Γ(W, ⊤))ˣ, unitSec v = Sec.res h c)
    ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology unitsP) (U := op V) c, ?_⟩ ?_
  · rintro W h ⟨t, ht⟩
    exact ⟨Additive.toMul t.down, ht⟩
  · rintro W h ⟨v, hv⟩
    have heq : unitSec (v ^ q) = unitSec (Units.map (h ≫ g).appTop.hom.toMonoidHom u) :=
      calc unitSec (v ^ q) = Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec v) := unitSec_pow q v
        _ = Sec.map ((q : ℤ) • 𝟙 Gm) (Sec.res h c) := by rw [hv]
        _ = Sec.res h (Sec.map ((q : ℤ) • 𝟙 Gm) c) :=
          ConcreteCategory.congr_hom ((((q : ℤ) • 𝟙 Gm : Gm ⟶ Gm)).hom.naturality h.op) c
        _ = Sec.res h (Sec.res g (unitSec u)) := by rw [hc]
        _ = Sec.res (h ≫ g) (unitSec u) := (res_comp g h _).symm
        _ = unitSec (Units.map (h ≫ g).appTop.hom.toMonoidHom u) := res_unitSec _ _
    rw [unitSec_eq, unitSec_eq] at heq
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology unitsP)
      (X := op W) _ _ heq, ?_⟩
    intro X k hk
    have hk' : Units.map k.appTop.hom.toMonoidHom (v ^ q) =
        Units.map k.appTop.hom.toMonoidHom (Units.map (h ≫ g).appTop.hom.toMonoidHom u) :=
      congrArg (fun z : ULift.{1} (Additive (Γ(X, ⊤))ˣ) => Additive.toMul z.down) hk
    refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
    rw [← map_pow, hk', Category.assoc, units_map_comp k (h ≫ g)]

end GlobalTheory.EtC.KumRoots
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KumCoker

instance instWLBKumCoker (R : Type) [CommRing R] :
    (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

theorem isSheaf_forget {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)

theorem sec_res_zero {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero _

theorem sec_eq_zero {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x : Sec F U)
    (h : Loc U fun _ g => Sec.res g x = 0) : x = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  refine ((isSheaf_forget F) S hS).isSeparatedFor.ext (fun V g hg => ?_)
  change Sec.res g x = Sec.res g 0
  rw [hP V g hg, sec_res_zero]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem sec_nat {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have e := congrArg (fun φ => φ.hom x) (f.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  exact e.symm

theorem sec_res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem unit_res {q : ℕ} {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hU.map g.appTop.hom

end GlobalTheory.EtC.KumCoker

open GlobalTheory.EtC.KumCoker in
theorem GlobalTheory.EtC.kumCoker_bijective : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0),
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U)) := by
  intro q _ κ h0 H1 H2
  set qb := cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0 with hqb
  have key : ∀ {V : Scheme.{0}} (b : Sec Gm V), Sec.map qb (Sec.map (cokernel.π κ) b) = Sec.map ((q : ℤ) • 𝟙 Gm) b := by
    intro V b
    rw [← sec_map_comp, hqb, cokernel.π_desc]
  have hls : Sheaf.IsLocallySurjective (cokernel.π κ) := (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  have inj : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Injective (Sec.map qb (U := U)) := by
    intro U hU
    refine (injective_iff_map_eq_zero ((qb.hom.app (op U)).hom)).2 (fun c hc => ?_)
    have hc' : Sec.map qb c = 0 := hc
    apply sec_eq_zero
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (cokernel.π κ).hom c, fun V g hg => ?_⟩
    obtain ⟨b, hb⟩ := hg
    have hb' : Sec.map (cokernel.π κ) b = Sec.res g c := hb
    have hz : Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 := by
      rw [← key, hb', ← sec_nat, hc', sec_res_zero]
    obtain ⟨a, rfl⟩ := H1 V (unit_res hU g) b hz
    rw [← hb', ← sec_map_comp, cokernel.condition, sec_map_zero]
  intro U hU
  refine ⟨inj U hU, fun b => ?_⟩
  obtain ⟨S, hS, hP⟩ := H2 U hU b
  choose c hc using hP
  let x : Presieve.FamilyOfElements ((cokernel κ).obj ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) S.arrows :=
    fun V g hg => Sec.map (cokernel.π κ) (c V g hg)
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z f₁ f₂ g₁ g₂ hg₁ hg₂ w
    apply inj Z (unit_res hU (f₁ ≫ g₁))
    change Sec.map qb (Sec.res f₁ (Sec.map (cokernel.π κ) (c _ g₁ hg₁))) =
      Sec.map qb (Sec.res f₂ (Sec.map (cokernel.π κ) (c _ g₂ hg₂)))
    rw [← sec_nat, ← sec_nat, key, key, hc, hc, sec_res_comp, sec_res_comp, w]
  obtain ⟨t, ht, -⟩ := isSheaf_forget (cokernel κ) S hS x hx
  refine ⟨t, sub_eq_zero.1 (sec_eq_zero Gm _ ⟨S, hS, fun V g hg => ?_⟩)⟩
  have ht' : Sec.res g t = Sec.map (cokernel.π κ) (c V g hg) := ht g hg
  change (Gm.obj.map g.op).hom (Sec.map qb t - b) = 0
  rw [map_sub]
  change Sec.res g (Sec.map qb t) - Sec.res g b = 0
  rw [sec_nat, ht', key, hc, sub_self]
end
end
