module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexCj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle415
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option synthInstance.maxSize 1000

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic.GJMatrix GlobalTheory.ThetaPoisson

open scoped Classical

namespace GlobalTheory.SchwartzBruhatMoments

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem pInfPi_eq (x : Fin m → Ad E) :
    (fun i => pInf E (x i)) = (toMixedPi E m).symm (infPartPi x) := by
  rw [← toMixedPi_pInf, ContinuousLinearEquiv.symm_apply_apply]

theorem one_add_pow_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : (1 + t) ^ k ≤ 2 ^ k * (1 + t ^ k) := by
  first
  | exact @_root_.GlobalTheory.OneAddPowBound.one_add_pow_le
  | exact _root_.GlobalTheory.OneAddPowBound.one_add_pow_le
  | (apply _root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneAddPowBound.one_add_pow_le ..)

theorem integrable_arch (φ : SchwartzMap (Fin m → mixedEmbedding.mixedSpace E) ℂ) (k : ℕ) :
    Integrable (fun u => ‖φ u‖ * (1 + ‖(toMixedPi E m).symm u‖) ^ k) (mixedMeasurePi E) := by
  set S := (toMixedPi E m).symm
  set C := ‖(S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E))‖
  have hC : 0 ≤ C := norm_nonneg _
  have hint : Integrable (fun u => ((1 + C) ^ k * 2 ^ k) * (‖φ u‖ + ‖u‖ ^ k * ‖φ u‖))
      (mixedMeasurePi E) :=
    ((φ.integrable (μ := mixedMeasurePi E)).norm.add
      (φ.integrable_pow_mul (mixedMeasurePi E) k)).const_mul _
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact (φ.continuous.norm.mul ((continuous_const.add S.continuous.norm).pow k)).aestronglyMeasurable
  · have h1 : ‖S u‖ ≤ C * ‖u‖ := (S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E)).le_opNorm u
    have h2 : 1 + ‖S u‖ ≤ (1 + C) * (1 + ‖u‖) := by nlinarith [norm_nonneg u, norm_nonneg (S u)]
    have h3 : (1 + ‖S u‖) ^ k ≤ (1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k)) := by
      calc (1 + ‖S u‖) ^ k ≤ ((1 + C) * (1 + ‖u‖)) ^ k := pow_le_pow_left₀ (by positivity) h2 k
        _ = (1 + C) ^ k * (1 + ‖u‖) ^ k := mul_pow _ _ _
        _ ≤ (1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_le (norm_nonneg u) k) (by positivity)
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖φ u‖ * (1 + ‖S u‖) ^ k ≤ ‖φ u‖ * ((1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k))) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = ((1 + C) ^ k * 2 ^ k) * (‖φ u‖ + ‖u‖ ^ k * ‖φ u‖) := by ring

theorem aestronglyMeasurable_weight (k : ℕ) :
    AEStronglyMeasurable (fun x : Fin m → Ad E => (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (adeleMeasurePi E) := by
  have h : (fun x : Fin m → Ad E => (1 + ‖fun i => pInf E (x i)‖) ^ k) =
      (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) =>
        (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) ∘ splitEquivPi E (Fin m) := by
    funext x
    simp only [Function.comp_apply, splitEquivPi_apply]
    rw [pInfPi_eq]
  rw [h]
  exact ((((continuous_const.add (toMixedPi E m).symm.continuous.norm).pow k).measurable.comp
    measurable_fst).comp (splitEquivPi E (Fin m)).measurable).aestronglyMeasurable

theorem integrable_tensor (φ : SchwartzMap (Fin m → mixedEmbedding.mixedSpace E) ℂ)
    {g : (Fin m → Af E) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi E) (k : ℕ) :
    Integrable (fun x => ‖schwartzBruhatTensorPi φ g x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (adeleMeasurePi E) := by
  have h : (fun x : Fin m → Ad E => ‖schwartzBruhatTensorPi φ g x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k) =
      (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) =>
        (‖φ p.1‖ * (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) * ‖g p.2‖) ∘ splitEquivPi E (Fin m) := by
    funext x
    simp only [Function.comp_apply, splitEquivPi_apply, schwartzBruhatTensorPi, norm_mul]
    rw [pInfPi_eq]
    ring
  rw [h, measurePreserving_splitEquivPi.integrable_comp_emb (splitEquivPi E (Fin m)).measurableEmbedding]
  exact (integrable_arch φ k).mul_prod (integrable_of_mem_finiteSchwartzBruhatPi hg).norm

theorem compactSupport_and_integrable_moments :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (F : (Fin m → Ad E) → ℂ),
    F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin m) →
    (∃ L : Set (Fin m → Af E), IsCompact L ∧ ∀ x, F x ≠ 0 → (fun i => pFin E (x i)) ∈ L) ∧
    ∀ k : ℕ, Integrable (fun x => ‖F x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E) := by
  intro E _ _ _ m F hF
  refine ⟨?_, fun k => ?_⟩
  · induction hF using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ, g, hg, rfl⟩ := hG
      refine ⟨tsupport g, hg.2, fun x hx => ?_⟩
      have e : (fun i => pFin E (x i)) = finPartPi x := rfl
      rw [e]
      apply subset_tsupport
      intro h0
      apply hx
      simp only [schwartzBruhatTensorPi, h0, mul_zero]
    | zero => exact ⟨∅, isCompact_empty, fun x hx => absurd rfl hx⟩
    | add G H _ _ hG hH =>
      obtain ⟨L1, h1, hL1⟩ := hG
      obtain ⟨L2, h2, hL2⟩ := hH
      refine ⟨L1 ∪ L2, h1.union h2, fun x hx => ?_⟩
      by_cases hGx : G x = 0
      · right
        apply hL2
        intro hH0
        apply hx
        simp [hGx, hH0]
      · left
        exact hL1 x hGx
    | smul c G _ hG =>
      obtain ⟨L, hL, hLx⟩ := hG
      exact ⟨L, hL, fun x hx => hLx x fun h0 => hx (by simp [h0])⟩
  · induction hF using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ, g, hg, rfl⟩ := hG
      exact integrable_tensor φ hg k
    | zero => simp
    | add G H hGm hHm hG hH =>
      refine (hG.add hH).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (integrable_of_mem_schwartzBruhatPi (K := E) (ι := Fin m)
          (Submodule.add_mem _ hGm hHm)).aestronglyMeasurable.norm.mul (aestronglyMeasurable_weight k)
      · have hw : 0 ≤ (1 + ‖fun i => pInf E (x i)‖) ^ k := by positivity
        simp only [Pi.add_apply]
        rw [Real.norm_of_nonneg (by positivity), ← add_mul]
        exact mul_le_mul_of_nonneg_right (norm_add_le _ _) hw
    | smul c G _ hG =>
      refine (hG.const_mul ‖c‖).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      ring

end GlobalTheory.SchwartzBruhatMoments
end
end

section

open GlobalTheory.ClassRefine GlobalTheory.ClassPet

noncomputable section

namespace GlobalTheory.TwoLattices

open scoped Classical

variable {G : Type} [Group G]

theorem finite_stab_mono {Γ Γ' K K' : Subgroup G} (h : Γ' ≤ Γ) (hK : K' ≤ K) (t : G) (hf : Finite (stabQ Γ K t)) :
    Finite (stabQ Γ' K' t) :=
  Finite.of_injective (fun γ : stabQ Γ' K' t => (⟨⟨γ.1, h γ.1.2⟩, mem_stabQ.2 (hK (mem_stabQ.1 γ.2))⟩ : stabQ Γ K t))
    fun _ _ e => Subtype.ext (Subtype.ext (congrArg (fun z : stabQ Γ K t => (z.1 : G)) e))

theorem Cover.of_finite {Γ Γ' K : Subgroup G} (hc : Cover Γ K) {α : Type} [Finite α] (r : Γ → α)
    (hr : ∀ a b, r a = r b → (a : G) * (b : G)⁻¹ ∈ Γ') : Cover Γ' K := by
  obtain ⟨S, hS⟩ := hc
  haveI := Fintype.ofFinite α
  refine ⟨(Finset.univ ×ˢ S).image fun p : α × G => ((Function.invFun r p.1 : Γ) : G) * p.2, fun g => ?_⟩
  obtain ⟨s, hs, γ, κ, hκ, e⟩ := hS g
  exact ⟨_, Finset.mem_image.2 ⟨(r γ, s), Finset.mem_product.2 ⟨Finset.mem_univ _, hs⟩, rfl⟩,
    ⟨_, hr γ _ (Function.invFun_eq ⟨γ, rfl⟩).symm⟩, κ, hκ, by rw [e]; simp [mul_assoc]⟩

def Kn (G X : Type) : Type := G × G → X → X → ℂ

variable {W X : Type} [AddCommGroup W] [Module ℂ W]

instance : MulAction G (Kn G X) where
  smul δ k := fun p => k (δ⁻¹ * p.1, δ⁻¹ * p.2)
  one_smul k := funext fun p => by
    show k (1⁻¹ * p.1, 1⁻¹ * p.2) = k p
    simp
  mul_smul a b k := funext fun p => by
    show k ((a * b)⁻¹ * p.1, (a * b)⁻¹ * p.2) = k (b⁻¹ * (a⁻¹ * p.1), b⁻¹ * (a⁻¹ * p.2))
    simp [mul_assoc]

theorem smul_kn (δ : G) (k : Kn G X) (p : G × G) : (δ • k) p = k (δ⁻¹ * p.1, δ⁻¹ * p.2) := rfl

def kn (f : X → G → W) (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Kn G X := fun p x x' => b (f x p.1) (f x' p.2)

def acts (f : X → G → W) : Subgroup G where
  carrier := {δ | (∃ A : W →ₗ[ℂ] W, ∀ x g, f x (δ * g) = A (f x g)) ∧ ∃ A : W →ₗ[ℂ] W, ∀ x g, f x (δ⁻¹ * g) = A (f x g)}
  one_mem' := ⟨⟨LinearMap.id, by simp⟩, ⟨LinearMap.id, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨⟨A, hA⟩, A', hA'⟩ ⟨⟨B, hB⟩, B', hB'⟩
    exact ⟨⟨A.comp B, fun x g => by rw [mul_assoc, hA, hB]; rfl⟩,
      ⟨B'.comp A', fun x g => by rw [mul_inv_rev, mul_assoc, hB', hA']; rfl⟩⟩
  inv_mem' := by
    rintro a ⟨h, h'⟩
    exact ⟨h', by simpa using h⟩

theorem le_acts {f : X → G → W} {Γ : Subgroup G} (h : ∀ γ ∈ Γ, ∃ A : W →ₗ[ℂ] W, ∀ x g, f x (γ * g) = A (f x g)) : Γ ≤ acts f :=
  fun γ hγ => ⟨h γ hγ, h _ (Γ.inv_mem hγ)⟩

def IsPos (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Prop := (∀ x y, b x y = starRingEnd ℂ (b y x)) ∧ ∀ x, x ≠ 0 → 0 < (b x x).re

section Span

variable {f : X → G → W} {ι : Type} {p : ι → X × G} (hs : Submodule.span ℂ (Set.range fun i => f (p i).1 (p i).2) = ⊤)
include hs

theorem smul_kn_pos {δ : G} (hδ : δ ∈ acts f) {b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (hb : IsPos b) : ∃ b', IsPos b' ∧ kn f b' = δ • kn f b := by
  obtain ⟨⟨A, hA⟩, A', hA'⟩ := hδ
  have h : A.comp A' = LinearMap.id := LinearMap.ext_on_range hs fun i => by
    rw [LinearMap.comp_apply, ← hA', ← hA]
    simp
  refine ⟨(b.comp A').compl₂ A', ⟨fun x y => hb.1 _ _, fun x hx => hb.2 _ fun h0 => hx ?_⟩, funext fun q => ?_⟩
  · have := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply, h0, map_zero] at this
    exact this.symm
  · funext x x'
    show b (A' _) (A' _) = b _ _
    rw [hA', hA']

theorem fix_of_mem {K : Subgroup G} (hr : ∀ κ ∈ K, ∀ x g, f x (g * κ) = f x g) {δ : G} (hδ : δ ∈ acts f)
    (h : ∀ i, δ ∈ cj K (p i).2) (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : δ • kn f b = kn f b := by
  obtain ⟨-, A, hA⟩ := hδ
  have e : A = LinearMap.id := LinearMap.ext_on_range hs fun i => by
    rw [← hA, LinearMap.id_apply, ← hr _ (mem_cj.1 (h i))]
    simp [mul_assoc]
  funext q x x'
  show b _ _ = b _ _
  rw [hA, hA, e]
  rfl

theorem finite_orbit [Finite ι] {K Γ : Subgroup G} (hK : ∀ x, (cj K x).relIndex K ≠ 0) (hr : ∀ κ ∈ K, ∀ x g, f x (g * κ) = f x g)
    (hΓ : Γ ≤ acts f) (hc : Cover Γ K) {b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (hb : IsPos b) (hinv : ∀ γ ∈ Γ, γ • kn f b = kn f b) :
    Finite (MulAction.orbit (acts f) (kn f b)) := by
  obtain ⟨S, hS⟩ := hc.of_relIndex (Subgroup.relIndex_iInf_ne_zero fun i => hK (p i).2)
  choose s hs' γ κ hκ e using hS
  choose δ hδ using fun k : MulAction.orbit (acts f) (kn f b) => k.2
  refine Finite.of_injective (fun k => (⟨s (δ k : G)⁻¹, hs' _⟩ : S)) fun k k' h => Subtype.ext ?_
  have h1 : s (δ k : G)⁻¹ = s (δ k' : G)⁻¹ := congrArg Subtype.val h
  have h2 := e (δ k : G)⁻¹
  have h3 := e (δ k' : G)⁻¹
  rw [h1] at h2
  rw [← hδ k, ← hδ k']
  generalize γ (δ k : G)⁻¹ = a at h2
  generalize γ (δ k' : G)⁻¹ = a' at h3
  have h4 := hκ (δ k : G)⁻¹
  have h5 := hκ (δ k' : G)⁻¹
  generalize κ (δ k : G)⁻¹ = c at h2 h4
  generalize κ (δ k' : G)⁻¹ = c' at h3 h5
  generalize s (δ k' : G)⁻¹ = t at h2 h3
  have h6 : c⁻¹ * c' = δ k * (a * (a' : G)⁻¹) * (δ k' : G)⁻¹ := by
    rw [h3, inv_eq_iff_eq_inv.1 h2]; group
  have h7 : (δ k : G) = c⁻¹ * c' * δ k' * (a' * (a : G)⁻¹) := by rw [h6]; group
  obtain ⟨b', -, hb'⟩ := smul_kn_pos hs (δ k').2 hb
  show (δ k : G) • kn f b = (δ k' : G) • kn f b
  rw [h7, mul_smul, mul_smul, hinv _ (Γ.mul_mem a'.2 (Γ.inv_mem a.2)), ← hb']
  refine fix_of_mem hs hr ?_ (fun i => Subgroup.mem_iInf.1 (Subgroup.mul_mem _ (Subgroup.inv_mem _ h4) h5) i) b'
  rw [h6]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (δ k).2 (hΓ (Γ.mul_mem a.2 (Γ.inv_mem a'.2)))) (Subgroup.inv_mem _ (δ k').2)

theorem exists_form [Finite ι] {K Γ₁ Γ₂ : Subgroup G} (hK : ∀ x, (cj K x).relIndex K ≠ 0)
    (hr : ∀ κ ∈ K, ∀ x g, f x (g * κ) = f x g) (h₁ : Γ₁ ≤ acts f) (h₂ : Γ₂ ≤ acts f) (hc₁ : Cover Γ₁ K) (hc₂ : Cover Γ₂ K)
    (hf₁ : ∀ t, Finite (stabQ Γ₁ K t)) (hf₂ : ∀ t, Finite (stabQ Γ₂ K t)) {b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (hb : IsPos b)
    (hinv : ∀ γ ∈ Γ₂, ∀ x x' g g', b (f x (γ * g)) (f x' (γ * g')) = b (f x g) (f x' g')) :
    ∃ (β : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (c : ℝ), IsPos β ∧ 0 < c ∧
      (∀ γ ∈ Γ₁, ∀ x x' g g', β (f x (γ * g)) (f x' (γ * g')) = β (f x g) (f x' g')) ∧
      ∀ x x', dsum Γ₂ K (fun g => b (f x g) (f x' g)) = c * dsum Γ₁ K fun g => β (f x g) (f x' g) := by
  have hinv' : ∀ γ ∈ Γ₂, γ • kn f b = kn f b := fun γ hγ => funext fun q => funext fun x => funext fun x' =>
    hinv _ (Γ₂.inv_mem hγ) x x' q.1 q.2
  haveI := finite_orbit hs hK hr h₂ hc₂ hb hinv'
  set O := MulAction.orbit (acts f) (kn f b) with hO
  haveI := Fintype.ofFinite O
  have hk₀ : kn f b ∈ O := MulAction.mem_orbit_self _
  choose δ hδ using fun k : O => k.2
  choose B hB eB using fun k : O => smul_kn_pos hs (δ k).2 hb
  have eB' : ∀ k, kn f (B k) = k := fun k => (eB k).trans (hδ k)
  have hβ : ∀ x x' g g', (∑ k, B k) (f x g) (f x' g') = ∑ k : O, (k : Kn G X) (g, g') x x' := fun x x' g g' => by
    rw [LinearMap.sum_apply, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [← eB' k]; rfl
  have hβinv : ∀ γ ∈ acts f, ∀ x x' g g', (∑ k, B k) (f x (γ * g)) (f x' (γ * g')) = (∑ k, B k) (f x g) (f x' g') := by
    intro γ hγ x x' g g'
    rw [hβ, hβ, ← Equiv.sum_comp (MulAction.toPerm (⟨γ, hγ⟩ : acts f))]
    refine Finset.sum_congr rfl fun k _ => ?_
    show (γ • (k : Kn G X)) (γ * g, γ * g') x x' = _
    simp [smul_kn]
  let Δ : Subgroup G := fixingSubgroup G O
  have hΔ : ∀ a, a ∈ Δ ↔ ∀ k ∈ O, a • k = k := fun a => mem_fixingSubgroup_iff G
  have hst : ∀ a ∈ acts f, ∀ k ∈ O, a • k ∈ O := fun a ha k hk => (((⟨a, ha⟩ : acts f) • (⟨k, hk⟩ : O) : O)).2
  have hc₃ : Cover (Γ₂ ⊓ Δ) K := hc₂.of_finite (fun γ (k : O) => (⟨(γ : G)⁻¹ • (k : Kn G X), hst _ (h₂ (Γ₂.inv_mem γ.2)) _ k.2⟩ : O))
    fun a a' e => ⟨Γ₂.mul_mem a.2 (Γ₂.inv_mem a'.2), (hΔ _).2 fun k hk => by
      have : (a : G)⁻¹ • k = (a' : G)⁻¹ • k := congrArg Subtype.val (congrFun e ⟨k, hk⟩)
      rw [mul_smul, ← this, smul_inv_smul]⟩
  have hf₃ : ∀ t, Finite (stabQ (Γ₂ ⊓ Δ) K t) := fun t => finite_stab_mono inf_le_left le_rfl t (hf₂ t)
  have hl₀ : ∀ x x', ∀ γ ∈ Γ₂, ∀ g, b (f x (γ * g)) (f x' (γ * g)) = b (f x g) (f x' g) := fun x x' γ hγ g => hinv γ hγ x x' g g
  have hr₀ : ∀ (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) x x', ∀ κ ∈ K, ∀ g, b (f x (g * κ)) (f x' (g * κ)) = b (f x g) (f x' g) :=
    fun b x x' κ hκ g => by rw [hr κ hκ, hr κ hκ]
  have hk : ∀ k : O, ∃ c : ℝ, 0 < c ∧ ∀ x x', dsum (Γ₂ ⊓ Δ) K (fun g => (k : Kn G X) (g, g) x x') =
      c * dsum (Γ₂ ⊓ Δ) K fun g => b (f x g) (f x' g) := by
    intro k
    obtain ⟨T, hT⟩ := hc₃.reps
    have hc₄ := (reps_conj hT (δ k) 1).cover
    rw [cj_one] at hc₄
    obtain ⟨c, hc, e⟩ := dsum_prop (Δ := Δ) hK inf_le_right (fun a ha => (hΔ _).2 fun k' hk' => by
        have := (hΔ _).1 (mem_cj.1 ha).2 _ (hst _ (Subgroup.inv_mem _ (δ k).2) _ hk')
        rw [mul_smul, smul_inv_smul, mul_smul] at this
        exact smul_left_cancel _ this) hc₃ hc₄ hf₃ (fun t => by
        have := (stabConj (Γ₂ ⊓ Δ) K (δ k) 1 ((δ k : G)⁻¹ * t)).finite_iff.2 (hf₃ _)
        rwa [cj_one, inv_one, mul_one, mul_inv_cancel_left] at this)
    refine ⟨c, hc, fun x x' => ?_⟩
    rw [e _ (fun a ha g => ?_) (fun κ hκ g => ?_), ← dsum_conj hc₃ (fun γ => hl₀ x x' γ γ.2.1) (hr₀ b x x') (δ k) 1, cj_one]
    · congr 2
      funext g
      rw [← hδ k, mul_one]
      rfl
    · conv_rhs => rw [← (hΔ _).1 (Δ.inv_mem ha) k k.2]
      simp [smul_kn]
    · rw [← eB' k]
      exact hr₀ _ x x' κ hκ g
  choose c hc ec using hk
  obtain ⟨c₁, hc₁', e₁⟩ := dsum_prop hK (inf_le_left.trans h₂) h₁ hc₃ hc₁ hf₃ hf₁
  obtain ⟨c₂, hc₂', e₂⟩ := dsum_prop hK le_rfl inf_le_left hc₂ hc₃ hf₂ hf₃
  have hpos : 0 < ∑ k, c k := Finset.sum_pos (fun k _ => hc k) ⟨⟨_, hk₀⟩, Finset.mem_univ _⟩
  refine ⟨∑ k, B k, c₂ * c₁ / ∑ k, c k, ⟨fun x y => ?_, fun x hx => ?_⟩, by positivity, fun γ hγ => hβinv γ (h₁ hγ), fun x x' => ?_⟩

  · simp only [LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => (hB k).1 x y
  · simp only [LinearMap.sum_apply, Complex.re_sum]
    exact Finset.sum_pos (fun k _ => (hB k).2 x hx) ⟨⟨_, hk₀⟩, Finset.mem_univ _⟩
  · have e₃ := e₁ (fun g => (∑ k, B k) (f x g) (f x' g)) (fun a ha g => hβinv a ha x x' g g) (hr₀ _ x x')
    have e₄ : dsum (Γ₂ ⊓ Δ) K (fun g => (∑ k, B k) (f x g) (f x' g)) =
        ((∑ k, c k : ℝ) : ℂ) * dsum (Γ₂ ⊓ Δ) K fun g => b (f x g) (f x' g) := by
      simp_rw [hβ]
      rw [dsum_sum, Complex.ofReal_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => ec k x x'
    have hne : ((∑ k, c k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
    rw [e₂ _ (hl₀ x x') (hr₀ b x x'), Complex.ofReal_div, Complex.ofReal_mul, div_mul_eq_mul_div, mul_assoc, ← e₃, e₄]
    field_simp

end Span

end GlobalTheory.TwoLattices

end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.HerrClassUniq

theorem cocycle_eq {l : ℕ} [Fact l.Prime] {G V LL : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [T2Space LL]
    [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    (a : G → V → V) (c c' : G → V) (hc : Continuous c) (hc' : Continuous c')
    (ha : ∀ x, a 1 x = x)
    (hcc : ∀ g h, c (g * h) = c g + a g (c h)) (hcc' : ∀ g h, c' (g * h) = c' g + a g (c' h))
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1) (hker : ∀ h, lam h = 1 → c h = c' h) (hg₀ : c g₀ = c' g₀) :
    c = c' := by
  have h1 : c 1 = 0 := by
    have := hcc 1 1
    simpa [ha] using this
  have h1' : c' 1 = 0 := by
    have := hcc' 1 1
    simpa [ha] using this
  let S : Subgroup G :=
    { carrier := {g | c g = c' g}
      mul_mem' := fun {a b} ha hb => by
        change c (a * b) = c' (a * b)
        rw [hcc, hcc', show c a = c' a from ha, show c b = c' b from hb]
      one_mem' := by
        change c 1 = c' 1
        rw [h1, h1']
      inv_mem' := fun {a} ha => by
        change c a⁻¹ = c' a⁻¹
        have e1 := hcc a⁻¹ a
        have e2 := hcc' a⁻¹ a
        rw [inv_mul_cancel, h1, show c a = c' a from ha] at e1
        rw [inv_mul_cancel, h1'] at e2
        exact add_right_cancel (e1.symm.trans e2) }
  have hS : IsClosed (S : Set G) := by
    have : {g | c g = c' g} = ⋂ f : Module.Dual LL V, {g | f (c g) = f (c' g)} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      refine ⟨fun h f => by rw [h], fun h => ?_⟩
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff LL]
      intro f
      rw [map_sub, h f, sub_self]
    change IsClosed {g | c g = c' g}
    rw [this]
    refine isClosed_iInter fun f => ?_
    have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
    exact isClosed_eq (hf.comp hc) (hf.comp hc')
  funext g
  have hcl : IsClosed (lam '' (S : Set G)) := (hS.isCompact.image hlam).isClosed
  have hsub : Set.range (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) ⊆ lam '' (S : Set G) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨g₀ ^ n, S.zpow_mem (show g₀ ∈ S from hg₀) n, ?_⟩
    rw [map_zpow, h₀, ← ofAdd_zsmul]
    simp
  have hd : DenseRange (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) :=
    PadicInt.denseRange_intCast
  have hmem : lam g ∈ lam '' (S : Set G) := hcl.closure_subset_iff.2 hsub (hd (lam g))
  obtain ⟨x, hx, hxg⟩ := hmem
  have h2 : g * x⁻¹ ∈ S := hker _ (by rw [map_mul, map_inv, hxg, mul_inv_cancel])
  have h3 : g ∈ S := by simpa using S.mul_mem h2 hx
  exact h3

variable {l : ℕ} [Fact l.Prime]




theorem val_eq_of_Zf {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} (T : Lt K LL) (H : Subgroup ↥(GK K))
    (c c' : ↥(latticeCocycles (resLat T H))) (b : TW (RW LL) T) (g : ↥H) (e : Zf AI T H c b g = Zf AI T H c' b g) :
    (c : ↥H → T.V) g = (c' : ↥H → T.V) g := by
  unfold Zf at e
  exact congrArg Subtype.val ((GlobalTheory.WittTensorFixed.main l K LL T).2.2 (add_right_cancel e))



theorem cocycle_eq_lat {K LL : FinExt l} (T : Lt K LL) (H : Subgroup ↥(GK K)) (hH : IsClosed (H : Set ↥(GK K)))
    (c c' : ↥(latticeCocycles (resLat T H)))
    (lam : ↥H →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : ↥H)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1)
    (hker : ∀ h, lam h = 1 → (c : ↥H → T.V) h = (c' : ↥H → T.V) h)
    (hg₀ : (c : ↥H → T.V) g₀ = (c' : ↥H → T.V) g₀) : c = c' := by
  haveI := GlobalTheory.HerrClassMaps.compact_GK K
  haveI : CompactSpace ↥H := isCompact_iff_compactSpace.1 hH.isCompact
  haveI := T.mtop
  exact Subtype.ext (cocycle_eq (LL := ↥LL.1) (V := T.V) (fun (g : ↥H) (x : T.V) => T.ρ (g : ↥(GK K)) x) c c' c.2.1.1 c'.2.1.1
    (fun x => by simp) c.2.1.2 c'.2.1.2 lam hlam g₀ h₀ hker hg₀)



theorem class_of_values : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ := by
  intro D HW F l _ K s LL h T c b y z hyz g₀ hg₀ hb hk hz
  refine (cl_fit D HW F K s LL h T y z hyz b hb).elim fun cW hW => ?_
  refine (lam_exists D HW K s LL h).elim fun lam hl => ?_
  have e : c = cW := cocycle_eq_lat T _ hl.2.2.2.2 c cW lam hl.1 g₀ ((hl.2.2.1 g₀).2 hg₀)
    (fun g hg => val_eq_of_Zf (D.locA l) T _ c cW b g
      ((hk g ((hl.2.1 g).1 hg)).trans (hW.2.1 g ((hl.2.1 g).1 hg)).symm))
    (val_eq_of_Zf (D.locA l) T _ c cW b g₀ (hz.trans (hW.2.2 g₀ hg₀).symm))
  exact (congrArg Submodule.Quotient.mk e).trans hW.1

end GlobalTheory.NL.HerrClassUniq
end
