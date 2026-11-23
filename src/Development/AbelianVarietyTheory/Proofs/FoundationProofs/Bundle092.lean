module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle059
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle061
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle065
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle064
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hasQExpansionSumAbove_mul : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), HS ε C φ h → HS ε C ψ h' → HS ε C (φ * ψ) (h * h') := by
  first | exact @GlobalTheory.FNProd.hs_mul | exact GlobalTheory.FNProd.hs_mul | (intros; apply GlobalTheory.FNProd.hs_mul <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem dd_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ) :=
  (CuspForm.discriminant).holo'

theorem inR_mdifferentiable : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  intro E f ⟨N, w, hN, _, hq⟩
  obtain ⟨a, ha, _⟩ := hq 1
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ)) :=
    ha.mdifferentiable hN
  have hD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w) := fun τ => (dd_mdifferentiable τ).pow w
  have hdiv := hg.div hD (fun τ => pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ))
  have heq : ((fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ)) / fun τ : ℍ => DD τ ^ w) = f := by
    funext τ
    have h0 : DD τ ^ w ≠ 0 := pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
    simp only [Pi.div_apply, one_smul]
    field_simp
  rwa [heq] at hdiv

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict : (∃ A : (ℍ → ℂ) →+* Mero, ∀ f, A f = germ f) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔ DifferentiableOn ℂ (up f) Hs) ∧ (∀ a b : ℂ → ℂ, (∀ z ∈ Hs, a z = b z) → (a : Mero) = (b : Mero)) ∧ (∀ a : ℂ → ℂ, germ (fun τ : ℍ => a τ) = (a : Mero)) ∧ ∀ τ : ℍ, (τ : ℂ) ∈ Hs := by
  first | exact @GlobalTheory.FN.germ_ringHom_and_restrict | exact GlobalTheory.FN.germ_ringHom_and_restrict | (intros; apply GlobalTheory.FN.germ_ringHom_and_restrict <;> assumption)
end

section

open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.edgeClass_eq_kummerCharacter_of_chosen_root_function_field : ∀ (k K Ω F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[F] Ω, g ζ = ζ) →
  (∀ τ : K ≃ₐ[F] K, ∀ x ∈ FunctionField.ringOfIntegers k K, τ x ∈ FunctionField.ringOfIntegers k K) →
  ∀ (a b : F) (α β : Ω), a ≠ 0 → b ≠ 0 → algebraMap F K a ∈ FunctionField.ringOfIntegers k K → (algebraMap F K a)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    algebraMap F K b ∈ FunctionField.ringOfIntegers k K → (algebraMap F K b)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    α ^ N = algebraMap F Ω a → β ^ N = algebraMap F Ω b →
  ∀ (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)), (∀ g, (x g).toAdd = kum (N := N) ζ α g) → (∀ g, (y g).toAdd = kum (N := N) ζ β g) →
  ∀ η : (Ω ≃ₐ[F] Ω) → ZMod N, CobOn (geo F K Ω) x y η →
    IsLocallyConstant (fun g : geo F K Ω => η g) →
    (∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω), Over (FunctionField.ringOfIntegers k K).toSubring B →
      (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo F K Ω → η g = 0) →
  ∀ σ : Ω ≃ₐ[F] Ω, IsTopW (K := K) ζ x y η σ (topW (K := K) ζ x y η σ) := by
  first | exact @GlobalTheory.K4.isTopW_topW | exact GlobalTheory.K4.isTopW_topW | (intros; apply GlobalTheory.K4.isTopW_topW <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ev_one' (χ : kˣ →* ℂˣ) : ev χ (1 : k) = 1 := by
  unfold ev
  simp

theorem minor_one' {n : ℕ} (m : Fin n) : minor (1 : GL (Fin n) k) m = 1 := by
  unfold minor
  simp [Matrix.toSquareBlockProp]

theorem continuous_minor' {n : ℕ} (m : Fin n) : Continuous fun g : GL (Fin n) k => minor g m := by
  unfold minor
  exact (Units.continuous_val.matrix_submatrix _ _).matrix_det

theorem ev_eventually_one (χ : kˣ →* ℂˣ) (S : Set k) (hS : S ∈ nhds (0 : k)) (hT : ∀ x ∈ S, Triv χ x) :
    ∀ᶠ x in nhds (1 : k), ev χ x = 1 := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := triv_ev_props k
  have hball : {x : k | valuation k (x - 1) < 1} ∈ nhds (1 : k) :=
    (IsValuativeTopology.hasBasis_nhds' (1 : k)).mem_of_mem one_ne_zero
  have hpre : (fun x : k => x - 1) ⁻¹' S ∈ nhds (1 : k) :=
    (continuous_sub_right (1 : k)).continuousAt.preimage_mem_nhds (by simpa using hS)
  filter_upwards [hball, hpre] with x hx hxS
  have hv : valuation k x = 1 := by
    have : x = 1 + (x - 1) := by ring
    rw [this]
    exact Valuation.map_one_add_of_lt _ hx
  rw [h8 χ x 1 hv (by simp) (hT _ hxS), ev_one']

theorem theta_one_and_near : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) →
    theta ψ 1 = 1 ∧ ∃ U ∈ nhds (1 : GL (Fin n) k), ∀ g ∈ U, theta ψ g = 1 := by
  intro k _ _ _ _ n ψ hψ
  obtain ⟨-, -, h3, h4, h5, h6, -, -, -⟩ := triv_ev_props k
  have hset : ∀ χ : kˣ →* ℂˣ, IsSmoothChar χ → {x : k | Triv χ x} ∈ nhds (0 : k) := fun χ hχ =>
    (h6 χ hχ).1.mem_nhds (h3 χ)
  have hnxt : ∀ m, {x : k | Triv (nxt ψ m) x} ∈ nhds (0 : k) := by
    intro m
    unfold nxt
    split_ifs with h
    · exact hset _ (hψ _)
    · refine Filter.univ_mem' fun x => ?_
      intro u _ _
      rfl
  have hev : ∀ m, ∀ᶠ x in nhds (1 : k), ev (ψ m / nxt ψ m) x = 1 := fun m =>
    ev_eventually_one _ _ (Filter.inter_mem (hset _ (hψ m)) (hnxt m)) fun x hx => by
      rw [div_eq_mul_inv]
      exact h4 _ _ x hx.1 (h5 _ x hx.2)
  refine ⟨?_, ?_⟩
  · unfold theta
    exact Finset.prod_eq_one fun m _ => by rw [minor_one', ev_one']
  · have hall : ∀ᶠ g in nhds (1 : GL (Fin n) k), ∀ m, ev (ψ m / nxt ψ m) (minor g m) = 1 := by
      rw [Filter.eventually_all]
      intro m
      have hc := (continuous_minor' (k := k) m).continuousAt (x := 1)
      rw [ContinuousAt, minor_one'] at hc
      exact hc.eventually (hev m)
    exact ⟨_, hall, fun g hg => Finset.prod_eq_one fun m _ => hg m⟩

end

end GlobalTheory.PsType
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

noncomputable section
namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_zero' (χ : kˣ →* ℂˣ) : Triv χ (0 : k) := by
  intro u _ h
  rw [map_zero] at h
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm h zero_le'
  rw [(valuation k).zero_iff, sub_eq_zero] at h0
  have : u = 1 := Units.ext h0
  rw [this, map_one]

section Blocks

variable {r t : ℕ}

theorem castAdd_eq_stdSum (i : Fin r) : Fin.castAdd t i = stdSum (rfl : r + t = r + t) (Sum.inl i) := by
  ext; simp

theorem natAdd_eq_stdSum (j : Fin t) : Fin.natAdd r j = stdSum (rfl : r + t = r + t) (Sum.inr j) := by
  ext; simp

theorem emb₂_std_apply (a : GL (Fin r) k) (b : GL (Fin t) k) (x y : Fin r ⊕ Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (stdSum rfl x) (stdSum rfl y) =
      fromBlocks a.val 0 0 b.val x y := by
  exact (congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) _) _).trans (by
    simp [Matrix.reindex_apply, Matrix.submatrix_apply])

theorem emb₂_std_inv (a : GL (Fin r) k) (b : GL (Fin t) k) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))⁻¹ = emb₂ k (stdSum (rfl : r + t = r + t)) (a⁻¹, b⁻¹) := by
  rw [← map_inv]; rfl

theorem emb₂_mem_KO_iff (a : GL (Fin r) k) (b : GL (Fin t) k) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ KO k (Fin (r + t)) ↔
      a ∈ KO k (Fin r) ∧ b ∈ KO k (Fin t) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff, emb₂_std_inv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, ⟨fun i j => ?_, fun i j => ?_⟩⟩
    · have := h1 (stdSum rfl (.inl i)) (stdSum rfl (.inl j))
      rwa [emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h2 (stdSum rfl (.inl i)) (stdSum rfl (.inl j))
      rwa [emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h1 (stdSum rfl (.inr i)) (stdSum rfl (.inr j))
      rwa [emb₂_std_apply, fromBlocks_apply₂₂] at this
    · have := h2 (stdSum rfl (.inr i)) (stdSum rfl (.inr j))
      rwa [emb₂_std_apply, fromBlocks_apply₂₂] at this
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    refine ⟨fun p q => ?_, fun p q => ?_⟩
    · obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
      obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
      rw [emb₂_std_apply]
      rcases x with x | x <;> rcases y with y | y
      · rw [fromBlocks_apply₁₁]; exact a1 x y
      · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₂]; exact b1 x y
    · obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
      obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
      rw [emb₂_std_apply]
      rcases x with x | x <;> rcases y with y | y
      · rw [fromBlocks_apply₁₁]; exact a2 x y
      · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₂]; exact b2 x y

theorem ordered_castAdd {ψ : Fin (r + t) → kˣ →* ℂˣ} (hψ : Ordered ψ) :
    Ordered (fun i : Fin r => ψ (Fin.castAdd t i)) := by
  intro i a b j hia hab hbj x hx
  exact hψ (Fin.castAdd t i) (Fin.castAdd t a) (Fin.castAdd t b) (Fin.castAdd t j)
    (Fin.le_def.2 (Fin.le_def.1 hia)) (Fin.le_def.2 (Fin.le_def.1 hab)) (Fin.le_def.2 (Fin.le_def.1 hbj)) x hx

theorem ordered_natAdd {ψ : Fin (r + t) → kˣ →* ℂˣ} (hψ : Ordered ψ) :
    Ordered (fun i : Fin t => ψ (Fin.natAdd r i)) := by
  intro i a b j hia hab hbj x hx
  exact hψ (Fin.natAdd r i) (Fin.natAdd r a) (Fin.natAdd r b) (Fin.natAdd r j)
    ((Fin.natAdd_le_natAdd_iff r).2 hia) ((Fin.natAdd_le_natAdd_iff r).2 hab) ((Fin.natAdd_le_natAdd_iff r).2 hbj) x hx

theorem emb₂_mem_grp_iff (ψ : Fin (r + t) → kˣ →* ℂˣ) (a : GL (Fin r) k) (b : GL (Fin t) k) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ grp ψ ↔
      a ∈ grp (fun i => ψ (Fin.castAdd t i)) ∧ b ∈ grp (fun i => ψ (Fin.natAdd r i)) := by
  unfold grp
  simp only [Set.mem_setOf_eq]
  rw [emb₂_mem_KO_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    refine ⟨⟨ha, fun i j hij => ?_⟩, ⟨hb, fun i j hij => ?_⟩⟩
    · have := h (Fin.castAdd t i) (Fin.castAdd t j) (Fin.lt_def.2 (Fin.lt_def.1 hij))
      rwa [castAdd_eq_stdSum i, castAdd_eq_stdSum j, emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h (Fin.natAdd r i) (Fin.natAdd r j) ((Fin.natAdd_lt_natAdd_iff r).2 hij)
      rwa [natAdd_eq_stdSum i, natAdd_eq_stdSum j, emb₂_std_apply, fromBlocks_apply₂₂] at this
  · rintro ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩
    refine ⟨⟨ha, hb⟩, fun p q hpq => ?_⟩
    obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
    obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
    rw [emb₂_std_apply]
    rcases x with x | x <;> rcases y with y | y
    · rw [fromBlocks_apply₁₁]
      have hxy : x < y := by
        rw [← castAdd_eq_stdSum, ← castAdd_eq_stdSum] at hpq
        exact Fin.lt_def.2 (Fin.lt_def.1 hpq)
      have := ha' x y hxy
      rwa [castAdd_eq_stdSum x, castAdd_eq_stdSum y] at this
    · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact triv_zero' _
    · exfalso
      have := Fin.lt_def.1 hpq
      rw [stdSum_inr, stdSum_inl] at this
      omega
    · rw [fromBlocks_apply₂₂]
      have hxy : x < y := by
        rw [← natAdd_eq_stdSum, ← natAdd_eq_stdSum] at hpq
        exact (Fin.natAdd_lt_natAdd_iff r).1 hpq
      have := hb' x y hxy
      rwa [natAdd_eq_stdSum x, natAdd_eq_stdSum y] at this

end Blocks

theorem block_diag_mem_grp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → Cut ψ r → Ordered (fun i => ψ (Fin.castAdd t i)) ∧ Ordered (fun i => ψ (Fin.natAdd r i)) ∧ ∀ (a : GL (Fin r) k) (b : GL (Fin t) k), emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ grp ψ ↔ a ∈ grp (fun i => ψ (Fin.castAdd t i)) ∧ b ∈ grp (fun i => ψ (Fin.natAdd r i)) :=
  fun _ _ _ _ _ _ _ ψ hψ _ => ⟨ordered_castAdd hψ, ordered_natAdd hψ, emb₂_mem_grp_iff ψ⟩

end GlobalTheory.PsType
end
end

section

open GlobalTheory.AlmostEt

theorem _root_.GlobalTheory.T.derivationOn_vanishing_on_subalgebra_killed_sq : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S), IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → (∀ β ∈ B, D β = 0) → ∀ x ∈ C, (e * e) • D x = 0 := by
  first | exact @GlobalTheory.AlmostEt.derOn_killed_sq | exact GlobalTheory.AlmostEt.derOn_killed_sq | (intros; apply GlobalTheory.AlmostEt.derOn_killed_sq <;> assumption)
end

section

open GlobalTheory.AlmostEt

theorem _root_.GlobalTheory.T.kaehler_relation_of_derivation_on_large_subalgebra : ∀ (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (n : ℕ) (x y : Fin n → S), ∑ i, x i • KaehlerDifferential.D A S (y i) = 0 → ∃ T : Finset S, ∀ C : Subalgebra A S, (↑T : Set S) ⊆ C → (∀ i, y i ∈ C) → ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D → ∑ i, x i • D (y i) = 0 := by
  first | exact @GlobalTheory.AlmostEt.kaehler_rel_local | exact GlobalTheory.AlmostEt.kaehler_rel_local | (intros; apply GlobalTheory.AlmostEt.kaehler_rel_local <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.towerPadicCompletionMap_eval_depends_on_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.Khat l) (n : ℕ), ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K, (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0, X.sl (ofSL γ) f = f) → φ f = ψ f) → AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ a) = AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l ψ a) := by
  first | exact @GlobalTheory.KZ.Tower.eval_kmap_levelRed | exact GlobalTheory.KZ.Tower.eval_kmap_levelRed | (intros; apply GlobalTheory.KZ.Tower.eval_kmap_levelRed <;> assumption)
end

section

open GlobalTheory.AlmostEt

theorem _root_.GlobalTheory.T.exists_derivationOn_extension_cube_defect : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S), IsTrData B C tr a b e → ∀ D : S → M, IsDerOn B D → ∃ D' : S → M, IsDerOn C D' ∧ ∀ β ∈ B, D' β = (e ^ 3) • D β := by
  first | exact @GlobalTheory.AlmostEt.exists_derOn_ext | exact GlobalTheory.AlmostEt.exists_derOn_ext | (intros; apply GlobalTheory.AlmostEt.exists_derOn_ext <;> assumption)
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.mem_towerUnionAdjoinIntegralClosure_iff : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (s : (integralClosure (O0 p) Ω)), s ∈ towerAlg T ↔ (s : Ω) ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  first | exact @GlobalTheory.towerAlg_mem_iff | exact GlobalTheory.towerAlg_mem_iff | (intros; apply GlobalTheory.towerAlg_mem_iff <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_dilate : ∀ (j L N : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ τ' : ℍ), 0 < N → (τ' : ℂ) = N * τ →
    lat j 0 L v Φ τ' = lat j 0 L ((N : ℤ) * v.1, v.2) (fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0) τ := by
  first | exact @GlobalTheory.EisM.lat_dilate | exact GlobalTheory.EisM.lat_dilate | (intros; apply GlobalTheory.EisM.lat_dilate <;> assumption)
end
