module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle168
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle149
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle144
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle608
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle179
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

def frobSlice {K : Type} [Field K] (l i : ℕ) (z : K⟦X⟧) : K⟦X⟧ := PowerSeries.mk fun n => coeff (l * n + i) z

theorem coeff_frobSlice {K : Type} [Field K] (l i : ℕ) (z : K⟦X⟧) (n : ℕ) :
    coeff n (frobSlice l i z) = coeff (l * n + i) z := by
  simp [frobSlice]

namespace Hom

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

def rdivSet (F : Hom P Q) (τ : ZMod a) : Set K⟦X⟧ :=
  {h | (∃ c : ℝ, ∀ n, ‖coeff n h‖ ≤ c) ∧ ∃ Y : Matrix ι κ K⟦X⟧,
    (∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) ∧ F.mat τ * Y = h • (1 : Matrix κ κ K⟦X⟧)}

def ldivSet (F : Hom P Q) (τ : ZMod a) : Set K⟦X⟧ :=
  {h | (∃ c : ℝ, ∀ n, ‖coeff n h‖ ≤ c) ∧ ∃ Y : Matrix ι κ K⟦X⟧,
    (∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) ∧ Y * F.mat τ = h • (1 : Matrix ι ι K⟦X⟧)}

theorem bdd_mul {f g : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) (hg : ∃ c : ℝ, ∀ n, ‖coeff n g‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (f * g)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  exact ⟨a * b, fun n => by
    simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) ha0 hb0
      (f := f) (g := g) (by simpa using ha) (by simpa using hb) n⟩

theorem bdd_add {f g : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) (hg : ∃ c : ℝ, ∀ n, ‖coeff n g‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (f + g)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨max a b, fun n => by
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (ha n) (hb n))⟩

theorem bdd_smul_matrix {μ ν : Type} {b : K⟦X⟧} {Y : Matrix μ ν K⟦X⟧} (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c)
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) : ∃ c : ℝ, ∀ i j n, ‖coeff n ((b • Y) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hb
  obtain ⟨c, hc⟩ := hY
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  refine ⟨a * max c 0, fun i j n => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul]
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) ha0
    (le_max_right c 0) (f := b) (g := Y i j) (by simpa using ha)
    (fun m => by rw [mul_one]; exact (hc i j m).trans (le_max_left _ _)) n

theorem rdivSet_add (F : Hom P Q) (τ : ZMod a) {x y : K⟦X⟧} (hx : x ∈ F.rdivSet τ) (hy : y ∈ F.rdivSet τ) :
    x + y ∈ F.rdivSet τ := by
  obtain ⟨hxb, Y₁, ⟨c₁, hc₁⟩, h₁⟩ := hx
  obtain ⟨hyb, Y₂, ⟨c₂, hc₂⟩, h₂⟩ := hy
  refine ⟨bdd_add hxb hyb, Y₁ + Y₂, ⟨max c₁ c₂, fun i j n => ?_⟩, ?_⟩
  · rw [Matrix.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hc₁ i j n) (hc₂ i j n))
  · rw [Matrix.mul_add, h₁, h₂, add_smul]

theorem ldivSet_add (F : Hom P Q) (τ : ZMod a) {x y : K⟦X⟧} (hx : x ∈ F.ldivSet τ) (hy : y ∈ F.ldivSet τ) :
    x + y ∈ F.ldivSet τ := by
  obtain ⟨hxb, Y₁, ⟨c₁, hc₁⟩, h₁⟩ := hx
  obtain ⟨hyb, Y₂, ⟨c₂, hc₂⟩, h₂⟩ := hy
  refine ⟨bdd_add hxb hyb, Y₁ + Y₂, ⟨max c₁ c₂, fun i j n => ?_⟩, ?_⟩
  · rw [Matrix.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hc₁ i j n) (hc₂ i j n))
  · rw [Matrix.add_mul, h₁, h₂, add_smul]

theorem rdivSet_mul (F : Hom P Q) (τ : ZMod a) {x : K⟦X⟧} (hx : x ∈ F.rdivSet τ) (b : K⟦X⟧)
    (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) : b * x ∈ F.rdivSet τ := by
  obtain ⟨hxb, Y, hY, h⟩ := hx
  refine ⟨bdd_mul hb hxb, b • Y, bdd_smul_matrix hb hY, ?_⟩
  rw [Matrix.mul_smul, h, smul_smul]

theorem ldivSet_mul (F : Hom P Q) (τ : ZMod a) {x : K⟦X⟧} (hx : x ∈ F.ldivSet τ) (b : K⟦X⟧)
    (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) : b * x ∈ F.ldivSet τ := by
  obtain ⟨hxb, Y, hY, h⟩ := hx
  refine ⟨bdd_mul hb hxb, b • Y, bdd_smul_matrix hb hY, ?_⟩
  rw [Matrix.smul_mul, h, smul_smul]

end Hom

end GlobalTheory.BK
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open Classical

theorem frame_exists (K : UQ) (B : InvAlg K) (hs : B.P.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (e π : ι → B.A) (S : Finset ι), IsFrame B e π S := by
  obtain ⟨ι, _, e, S, hP⟩ := GlobalTheory.T.involutionIdempotentDecomposition_of_separable_charpoly K B hs
  have : ∀ i, ∃ y : B.A, i ∈ S → B.Plus y ∧ y * (1 - e i) = 1 - e i ∧ K.eta (Algebra.norm K.E y) = -1 := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨f, hf, hf0, hfld, hS, -⟩ := hP.2 i
      obtain ⟨he, hσ⟩ := hS hi
      obtain ⟨y, hy⟩ := GlobalTheory.T.exists_plus_element_eta_norm_neg_one K B f hf hf0 hfld hσ
      exact ⟨y, fun _ => by rw [he]; exact hy⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose π hπ using this
  exact ⟨ι, inferInstance, e, π, S, hP, fun i hi => hπ i hi⟩

theorem plus_mul {K : UQ} (B : InvAlg K) {x y : B.A} (hx : B.Plus x) (hy : B.Plus y) : B.Plus (x * y) :=
  ⟨hx.1.mul hy.1, by rw [map_mul, hx.2, hy.2]⟩

theorem plus_one {K : UQ} (B : InvAlg K) : B.Plus 1 := ⟨isUnit_one, map_one _⟩

theorem plus_prod {K : UQ} (B : InvAlg K) {ι : Type} (π : ι → B.A) (J : Finset ι) (h : ∀ j ∈ J, B.Plus (π j)) :
    B.Plus (∏ j ∈ J, π j) :=
  Finset.prod_induction _ B.Plus (fun _ _ => plus_mul B) (plus_one B) h

theorem isUnit_a {K : UQ} (B : InvAlg K) (a : K.O) (ha : K.Small a) : IsUnit (algebraMap K.O B.A a) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
  refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
  intro h
  exact ha.1 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))

theorem lim_HH {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O)
    (hB : B.LieReg) (ha : K.Small a) (hF : IsFrame B e π S) (ℓ : B.A → ℝ)
    (hℓ : ∀ x, B.Plus x → B.LinLim a x (ℓ x)) (I : Finset ι) (hI : I ⊆ S) (x : B.A) (hx : B.Plus x) :
    Tendsto (fun k : ℕ => ((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop
      (𝓝 (∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x))) := by
  have hπ : ∀ J ∈ S.powerset, B.Plus ((∏ j ∈ J, π j) * x) := fun J hJ =>
    plus_mul B (plus_prod B π J fun j hj => (hF.2 j (Finset.mem_powerset.1 hJ hj)).1) hx
  have hu : ∀ k : ℕ, IsUnit (x * algebraMap K.O B.A a ^ (2 * k)) := fun k => hx.1.mul ((isUnit_a B a ha).pow _)
  have heq : ∀ k : ℕ, ((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ) = ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card *
        ((B.GG ((∏ j ∈ J, π j) * x * algebraMap K.O B.A a ^ (2 * k)) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) := by
    intro k
    rw [GlobalTheory.T.signedInvolutionStableLatticeSum_eq_alternating_sum K B ι e π S hB hF I hI _ (hu k)]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [mul_assoc, mul_div_assoc]
  simp_rw [heq]
  exact tendsto_finsetSum _ fun J hJ => (hℓ _ (hπ J hJ)).const_mul _

theorem sum_formula {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O)
    (hB : B.LieReg) (ha : K.Small a) (hF : IsFrame B e π S) (ℓ : B.A → ℝ)
    (hℓ : ∀ x, B.Plus x → B.LinLim a x (ℓ x)) (I : Finset ι) (hI : I ⊆ S) :
    Tendsto (fun k : ℕ => ((HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop
      (𝓝 (∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j))) ∧
    ∑ᶠ k : B.Cl, (chi B e I k.rep : ℝ) * ℓ k.rep = (Nat.card B.Cl : ℝ) / 2 ^ S.card *
      ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j) := by
  set h : Finset ι → ℝ := fun I => ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j) with hh
  have lim1 : ∀ I ⊆ S, Tendsto (fun k : ℕ => ((HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop (𝓝 (h I)) := by
    intro I hI
    have := lim_HH B e π S a hB ha hF ℓ hℓ I hI 1 (plus_one B)
    simp only [one_mul, mul_one] at this
    exact this
  have key : ∀ I ⊆ S, ∀ x, B.Plus x → ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) =
      (chi B e I x : ℝ) * h I := by
    intro I hI x hx
    have t1 := lim_HH B e π S a hB ha hF ℓ hℓ I hI x hx
    have t2 := GlobalTheory.T.tendsto_signedLatticeSum_sub_normCharacter_mul K B ι e π S a hB ha hF I hI x hx
    have t3 := (lim1 I hI).const_mul (chi B e I x : ℝ)
    have t4 := t2.add t3
    rw [zero_add] at t4
    refine tendsto_nhds_unique t1 (t4.congr fun k => ?_)
    push_cast
    ring
  refine ⟨lim1 I hI, ?_⟩
  haveI : Finite B.Cl := GlobalTheory.T.finite_classes_of_separable_charPoly K B hB.2
  exact GlobalTheory.T.normCharacterOnIdempotentPart_orthogonality_classes K B ι e π S hF this ℓ h key I hI

theorem linearDescent : LinearDescent := by
  intro K B₁ B₂ hg₁ hg₂ hsep a ha ℓ ℓ₁ ℓ₂ hℓ hℓ₁ hℓ₂
  have hs₁ : B₁.P.Separable := hsep.of_mul_left
  have hs₂ : B₂.P.Separable := hsep.of_mul_right
  have hP : (B₁.prod B₂).P = B₁.P * B₂.P := by
    have h1 : LinearMap.mulLeft K.E (B₁.prod B₂).g =
        (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) := by
      exact LinearMap.ext fun _ => rfl
    have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
    rw [← h1] at h2
    exact h2
  obtain ⟨ι₁, _, e₁, π₁, S₁, hF₁⟩ := frame_exists K B₁ hs₁
  obtain ⟨ι₂, _, e₂, π₂, S₂, hF₂⟩ := frame_exists K B₂ hs₂
  have hF := GlobalTheory.T.isUniformizerIdempotentFrame_prod K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ hF₁ hF₂
  have hL₁ : B₁.LieReg := ⟨hg₁, hs₁⟩
  have hL₂ : B₂.LieReg := ⟨hg₂, hs₂⟩
  have hL : (B₁.prod B₂).LieReg := ⟨by
    show ((B₁.σ B₁.g, B₂.σ B₂.g) : B₁.A × B₂.A) = (B₁.g, B₂.g)
    rw [hg₁, hg₂], hP ▸ hsep⟩
  have hΛ : (S₁.disjSum S₂) \ S₁.map Function.Embedding.inl = S₂.map Function.Embedding.inr := by
    ext x; cases x <;> simp
  have hΛS : S₁.map Function.Embedding.inl ⊆ S₁.disjSum S₂ := by
    intro x; cases x <;> simp
  obtain ⟨l₁, c₁⟩ := sum_formula B₁ e₁ π₁ S₁ a hL₁ ha hF₁ ℓ₁ hℓ₁ S₁ subset_rfl
  obtain ⟨l₂, c₂⟩ := sum_formula B₂ e₂ π₂ S₂ a hL₂ ha hF₂ ℓ₂ hℓ₂ ∅ (Finset.empty_subset _)
  obtain ⟨l, c⟩ := sum_formula (B₁.prod B₂) _ _ _ a hL ha hF ℓ hℓ _ hΛS
  rw [Finset.sdiff_self] at l₁
  rw [Finset.sdiff_empty] at l₂
  rw [hΛ] at l
  change Tendsto (fun k : ℕ => ((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 : ℚ) : ℝ) / ((B₁.prod B₂).rho (algebraMap K.O (B₁.A × B₂.A) a ^ k) : ℝ)) atTop _ at l
  set h₁ := ∑ J ∈ S₁.powerset, (-1 : ℝ) ^ (J ∩ S₁).card * ℓ₁ (∏ j ∈ J, π₁ j)
  set h₂ := ∑ J ∈ S₂.powerset, (-1 : ℝ) ^ (J ∩ ∅).card * ℓ₂ (∏ j ∈ J, π₂ j)
  set h := ∑ J ∈ (S₁.disjSum S₂).powerset, (-1 : ℝ) ^ (J ∩ S₁.map Function.Embedding.inl).card *
    ℓ (∏ j ∈ J, Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) j)
  have hd := GlobalTheory.T.tendsto_signedLatticeSum_product_sub_factors K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ a hL₁ hL₂ hsep ha hF₁ hF₂
  set v := val K.O (resultant B₁.P B₂.P)
  have hrho : ∀ k : ℕ, (B₁.prod B₂).rho (algebraMap K.O (B₁.A × B₂.A) a ^ k) =
      B₁.rho (algebraMap K.O B₁.A a ^ k) * B₂.rho (algebraMap K.O B₂.A a ^ k) := fun k =>
    GlobalTheory.T.rho_prod_finiteAlgebraWithInvolution K B₁ B₂ _ _
  have hh : h = (-(K.q : ℝ)) ^ v * (h₁ * h₂) := by
    have t1 := (l₁.mul l₂).const_mul ((-(K.q : ℝ)) ^ v)
    have t2 := hd.add t1
    rw [zero_add] at t2
    refine tendsto_nhds_unique l (t2.congr fun k => ?_)
    rw [hrho k]
    push_cast
    ring
  have e₁' : ∑ᶠ k : B₁.Cl, (K.eta (Algebra.norm K.E k.rep) : ℝ) * ℓ₁ k.rep =
      ∑ᶠ k : B₁.Cl, (chi B₁ e₁ S₁ k.rep : ℝ) * ℓ₁ k.rep := by
    refine finsum_congr fun k => ?_
    rw [((GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties K B₁ ι₁ e₁ π₁ S₁ hF₁).2.2.2 (InvAlg.Cl.rep k) ⟨Units.isUnit _, (Quot.out k).2⟩)]
  have e₂' : ∑ᶠ k : B₂.Cl, ℓ₂ k.rep = ∑ᶠ k : B₂.Cl, (chi B₂ e₂ ∅ k.rep : ℝ) * ℓ₂ k.rep := by
    refine finsum_congr fun k => ?_
    simp [chi, eS, UQ.eta, val]
  have e' : ∑ᶠ k : (B₁.prod B₂).Cl, (K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) : ℝ) * ℓ k.rep =
      ∑ᶠ k : (B₁.prod B₂).Cl, (chi (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A))
        (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) k.rep : ℝ) * ℓ k.rep := by
    refine finsum_congr fun k => ?_
    rw [GlobalTheory.T.normCharacterOnIdempotentPart_prod_inl K B₁ B₂ ι₁ ι₂ e₁ e₂ S₁ (InvAlg.Cl.rep k)]
    have hk : (B₁.prod B₂).Plus k.rep := ⟨Units.isUnit _, (Quot.out k).2⟩
    have hk1 : B₁.Plus (InvAlg.Cl.rep k).1 :=
      ⟨(Prod.isUnit_iff.1 hk.1).1, congrArg Prod.fst hk.2⟩
    rw [((GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties K B₁ ι₁ e₁ π₁ S₁ hF₁).2.2.2 (InvAlg.Cl.rep k).1 hk1)]
  rw [e₁', e₂', e', c, c₁, c₂, hh, GlobalTheory.T.card_cl_prod_finiteAlgebraWithInvolution, Finset.card_disjSum]
  push_cast
  ring

end GlobalTheory.UnitLemma.Desc
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem lattice_basis_exists : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V), IsLatBasis T b := by
  intro l _ G _ _ LL T
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI hfr : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI := T.L.free
  haveI : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let e0 := Module.Free.chooseBasis ↥(OL LL) ↥T.L.T
  let e := e0.reindex (Fintype.equivFin _)
  let v : Fin (Fintype.card (Module.Free.ChooseBasisIndex ↥(OL LL) ↥T.L.T)) → T.V := fun i => (e i : T.V)
  have hliO : LinearIndependent ↥(OL LL) v := e.linearIndependent.map' T.L.T.subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent ↥LL.1 v := (LinearIndependent.iff_fractionRing ↥(OL LL) ↥LL.1).1 hliO

  have hexp : ∀ (x : T.V) (hx : x ∈ T.L.T), x = ∑ i, (((e.repr ⟨x, hx⟩ i : ↥(OL LL)) : ↥LL.1)) • v i := by
    intro x hx
    have h1 := e.sum_repr ⟨x, hx⟩
    have h2 := congrArg (fun y : ↥T.L.T => (y : T.V)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    conv_lhs => rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (algebraMap_smul ↥LL.1 (e.repr ⟨x, hx⟩ i) (v i)).symm
  have hsp : ⊤ ≤ Submodule.span ↥LL.1 (Set.range v) := by
    rw [← T.L.span]
    refine Submodule.span_le.2 fun x hx => ?_
    rw [hexp x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨_, Module.Basis.mk hli hsp, fun i => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.mk_apply]; exact (e i).2
  · have h3 : (Module.Basis.mk hli hsp).repr x = fun j => (((e.repr ⟨x, hx⟩ j : ↥(OL LL)) : ↥LL.1)) := by
      conv_lhs => rw [hexp x hx]
      simp_rw [← Module.Basis.mk_apply hli hsp]
      exact (Module.Basis.mk hli hsp).repr_sum_self _
    rw [h3]
    exact (e.repr ⟨x, hx⟩ i).2

end GlobalTheory.BaseCoef
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef




theorem extHom_onto : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L), F.Onto → (extHom hL hb₁ hb₂ F).Onto := by
  intro l _ G _ _ LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F hF
  choose x hx hfx using fun i => hF (b₂ i) (hb₂.1 i)
  have key : ∀ i j, ∑ m, LinearMap.toMatrix b₁ b₂ F.f i m * b₁.repr (x j) m =
      (1 : Matrix (Fin k₂) (Fin k₂) ↥LL.1) i j := by
    intro i j
    have h1 := congrFun (LinearMap.toMatrix_mulVec_repr b₁ b₂ F.f (x j)) i
    rw [hfx j, Module.Basis.repr_self] at h1
    rw [Matrix.one_apply, ← show _ = ∑ m, LinearMap.toMatrix b₁ b₂ F.f i m * b₁.repr (x j) m from rfl.symm]
    refine Eq.trans h1 ?_
    rw [Finsupp.single_apply]
    simp only [eq_comm]
  let X : Matrix (Fin k₁) (Fin k₂) ↥LL'.1 := fun m j => incl hL (b₁.repr (x j) m)
  have hX : extMat hL b₁ b₂ F * X = 1 := by
    refine Matrix.ext fun i j => ?_
    have := congrArg (incl hL) (key i j)

    rw [map_sum] at this
    simp only [map_mul] at this
    rw [Matrix.mul_apply]
    refine Eq.trans this ?_
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  intro y hy
  refine ⟨X.mulVec y, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.mul_mem _ (incl_integral hL (hb₁.2 _ (hx j) i)) (hy j)
  · change (extMat hL b₁ b₂ F).mulVec (X.mulVec y) = y
    rw [Matrix.mulVec_mulVec, hX, Matrix.one_mulVec]

end GlobalTheory.BaseCoef
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem mem_mapSig {I LL LL' : Type} [Group I] [Field LL] [Field LL'] (f : LL →+* LL')
    (Sig : Finset (I →* LLˣ)) (x : I →* LL'ˣ) :
    x ∈ mapSig f Sig ↔ ∃ a ∈ Sig, (Units.map (f : LL →* LL')).comp a = x := by
  classical
  unfold mapSig
  exact Finset.mem_image

theorem orbLen_map {G LL LL' : Type} [Group G] [Field LL] [Field LL'] (f : LL →+* LL')
    (I : Subgroup G) (Fr : G) (a b : I →* LLˣ) :
    Formalism.MainNotions.ElementDenominator.orbLen I Fr ((Units.map (f : LL →* LL')).comp a * ((Units.map (f : LL →* LL')).comp b)⁻¹) =
      Formalism.MainNotions.ElementDenominator.orbLen I Fr (a * b⁻¹) := by
  set φ : LLˣ →* LL'ˣ := Units.map (f : LL →* LL') with hφ
  have hinj : Function.Injective φ := by
    intro u v huv
    apply Units.ext
    have := congrArg Units.val huv
    simpa [hφ] using f.injective this
  have hcomp : φ.comp a * (φ.comp b)⁻¹ = φ.comp (a * b⁻¹) := by
    ext x
    simp
  rw [hcomp]
  unfold Formalism.MainNotions.ElementDenominator.orbLen
  congr 1
  ext k
  simp only [Set.mem_setOf_eq, MonoidHom.comp_apply]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun g g' hg => hinj (h g g' hg)⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun g g' hg => congrArg φ (h g g' hg)⟩

theorem mapSig_props : ∀ {G LL LL' : Type} [Group G] [Field LL] [Field LL'] (f : LL →+* LL') (I : Subgroup G) (Fr : G) (Sig : Finset (I →* LLˣ)), (FrobStable I Fr Sig → FrobStable I Fr (mapSig f Sig)) ∧ Formalism.MainNotions.ElementDenominator.rPrime I Fr (mapSig f Sig) = Formalism.MainNotions.ElementDenominator.rPrime I Fr Sig ∧ (mapSig f Sig).card ≤ Sig.card ∧ (1 ∈ Sig → 1 ∈ mapSig f Sig) := by
  intro G LL LL' _ _ _ f I Fr Sig
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hS a' ha'
    obtain ⟨a, ha, rfl⟩ := (mem_mapSig f Sig a').1 ha'
    obtain ⟨b, hb, hab⟩ := hS a ha
    refine ⟨(Units.map (f : LL →* LL')).comp b, (mem_mapSig f Sig _).2 ⟨b, hb, rfl⟩, ?_⟩
    intro g h hgh
    simp [hab g h hgh]
  · unfold Formalism.MainNotions.ElementDenominator.rPrime
    apply le_antisymm
    · apply Finset.sup_le
      rintro ⟨p, q⟩ hpq
      rw [Finset.mem_product] at hpq
      obtain ⟨a, ha, rfl⟩ := (mem_mapSig f Sig p).1 hpq.1
      obtain ⟨b, hb, rfl⟩ := (mem_mapSig f Sig q).1 hpq.2
      rw [orbLen_map f I Fr a b]
      exact Finset.le_sup (s := Sig ×ˢ Sig)
        (f := fun p : (↥I →* LLˣ) × (↥I →* LLˣ) => Formalism.MainNotions.ElementDenominator.orbLen I Fr (p.1 * p.2⁻¹)) (b := (a, b))
        (Finset.mem_product.2 ⟨ha, hb⟩)
    · apply Finset.sup_le
      rintro ⟨a, b⟩ hab
      rw [Finset.mem_product] at hab
      have := Finset.le_sup (s := mapSig f Sig ×ˢ mapSig f Sig)
        (f := fun p : (↥I →* LL'ˣ) × (↥I →* LL'ˣ) => Formalism.MainNotions.ElementDenominator.orbLen I Fr (p.1 * p.2⁻¹))
        (b := ((Units.map (f : LL →* LL')).comp a, (Units.map (f : LL →* LL')).comp b))
        (Finset.mem_product.2 ⟨(mem_mapSig f Sig _).2 ⟨a, hab.1, rfl⟩, (mem_mapSig f Sig _).2 ⟨b, hab.2, rfl⟩⟩)
      simpa only [orbLen_map f I Fr a b] using this
  · classical
    unfold mapSig
    exact Finset.card_image_le
  · intro h1
    exact (mem_mapSig f Sig 1).2 ⟨1, h1, MonoidHom.comp_one _⟩

end GlobalTheory.BaseCoef
end
