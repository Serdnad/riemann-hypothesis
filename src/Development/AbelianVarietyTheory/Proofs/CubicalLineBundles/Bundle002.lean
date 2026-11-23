module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem isIntegral_eigenvalue_sub_one_div {E : Type} [Field E] [NumberField E] {r M : ℕ}
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ)
    (hM : (M : ℂ) ≠ 0) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hγ : ∀ x ∈ Λ, ∃ y ∈ Λ, γ *ᵥ x - x = (M : E) • y)
    (w : Fin r → ℂ) (hw : w ≠ 0) (l : ℂ) (hl : w ᵥ* γ.map τ = l • w) :
    IsIntegral ℤ ((l - 1) / M) := by
  let φ : (Fin r → E) →+ ℂ :=
    { toFun := fun x => w ⬝ᵥ (τ ∘ x)
      map_zero' := by simp [dotProduct]
      map_add' := fun x y => by simp [dotProduct, mul_add, Finset.sum_add_distrib] }
  have hφ : ∀ x, φ x = w ⬝ᵥ (τ ∘ x) := fun _ => rfl
  have hsm : ∀ (c : E) x, φ (c • x) = τ c * φ x := by
    intro c x
    simp only [hφ, dotProduct, Finset.mul_sum, Function.comp, Pi.smul_apply, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmul : ∀ x, φ (γ *ᵥ x) = l * φ x := by
    intro x
    have : τ ∘ (γ *ᵥ x) = γ.map τ *ᵥ (τ ∘ x) := funext fun i => RingHom.map_mulVec τ γ x i
    rw [hφ, this, Matrix.dotProduct_mulVec, hl, smul_dotProduct, hφ, smul_eq_mul]
  refine isIntegral_of_smul_mem_submodule
    ((Λ.restrictScalars ℤ).map φ.toIntLinearMap) ?_ (hfg.restrictScalars.map _) _ ?_
  · intro h0
    have h1 : ∀ x ∈ Λ, φ x = 0 := by
      intro x hx
      have : φ.toIntLinearMap x ∈ (Λ.restrictScalars ℤ).map φ.toIntLinearMap :=
        Submodule.mem_map_of_mem hx
      rw [h0] at this
      simpa using this
    have h2 : ∀ x ∈ Submodule.span E (Λ : Set (Fin r → E)), φ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact h1 x hx
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul c x _ hx => rw [hsm, hx, mul_zero]
    apply hw
    funext i
    have h3 := h2 (Pi.single i 1) (hsp ▸ Submodule.mem_top)
    have h4 : τ ∘ (Pi.single i 1 : Fin r → E) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hφ, h4] at h3
    simpa using h3
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hγ x hx
    refine ⟨y, hy, ?_⟩
    have h := congrArg φ hxy
    rw [map_sub, hmul, hsm, map_natCast] at h
    simp only [AddMonoidHom.coe_toIntLinearMap, smul_eq_mul]
    field_simp
    linear_combination -h

theorem root_of_unity_eq_one_of_isIntegral_div {E : Type} [Field E] [NumberField E] {M n : ℕ}
    (hM : 3 ≤ M) (hn : 0 < n) {u : E} (hu : u ^ n = 1) (h : IsIntegral ℤ ((u - 1) / M)) :
    u = 1 := by
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hlt : ∀ φ : E →+* ℂ, ‖φ ((u - 1) / M)‖ < 1 := by
    intro φ
    have h1 : ‖φ u‖ = 1 := by
      have : ‖φ u‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hu, map_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    have h2 : ‖φ u - 1‖ ≤ 2 := by
      have := norm_sub_le (φ u) 1
      rw [h1, norm_one] at this
      linarith
    rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by linarith)]
    linarith
  by_contra hne
  have hx : (u - 1) / M ≠ 0 := div_ne_zero (sub_ne_zero.2 hne) hM0
  obtain ⟨k, hk, hk1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx h
    fun φ => (hlt φ).le
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 : ‖φ ((u - 1) / M)‖ ^ k = 1 := by rw [← norm_pow, ← map_pow, hk1, map_one, norm_one]
  exact (hlt φ).ne ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h3)

theorem root_of_unity_eq_one_of_conj_congruence :
    ∀ (E : Type) [Field E] [NumberField E] (r M n : ℕ) (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (γ δ : Matrix (Fin r) (Fin r) E) (u : E) (τ : E →+* ℂ) (Q : Matrix (Fin r) (Fin r) ℂ), 0 < r → 3 ≤ M → 0 < n → u ^ n = 1 → Λ.FG → Λ'.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → (∀ x ∈ Λ', ∃ y ∈ Λ', Matrix.mulVec (δ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → Q.det ≠ 0 → (u • γ).map τ * Q = Q * δ.map τ → u = 1 := by
  intro E _ _ r M n Λ Λ' γ δ u τ Q hr hM hn hu hfg hfg' hsp hsp' hγ hδ hQ hconj
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (γ.map τ)ᵀ)
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  have hw0 : w ≠ 0 := hw.2
  have hw1 : w ᵥ* γ.map τ = l • w := by
    have := hw.apply_eq_smul
    rwa [Matrix.toLin'_apply, Matrix.mulVec_transpose] at this
  have hwQ : w ᵥ* Q ≠ 0 := fun h => hw0 (Matrix.eq_zero_of_vecMul_eq_zero hQ h)
  have hs : (u • γ).map τ = τ u • γ.map τ := by
    ext i j; simp
  have hw2 : (w ᵥ* Q) ᵥ* δ.map τ = (τ u * l) • (w ᵥ* Q) := by
    rw [Matrix.vecMul_vecMul, ← hconj, ← Matrix.vecMul_vecMul, hs, Matrix.vecMul_smul, hw1,
      smul_smul, Matrix.smul_vecMul]
  have ha := isIntegral_eigenvalue_sub_one_div Λ γ τ hM0 hfg hsp hγ w hw0 l hw1
  have hb := isIntegral_eigenvalue_sub_one_div Λ' δ τ hM0 hfg' hsp' hδ _ hwQ _ hw2
  have hui : IsIntegral ℤ (τ u) := by
    apply IsIntegral.of_pow hn
    rw [← map_pow, hu, map_one]
    exact isIntegral_one
  have hc : τ ((u - 1) / M) = (τ u * l - 1) / M - τ u * ((l - 1) / M) := by
    rw [map_div₀, map_sub, map_one, map_natCast]
    field_simp
    ring
  refine root_of_unity_eq_one_of_isIntegral_div hM hn hu ?_
  refine (isIntegral_algHom_iff τ.toIntAlgHom τ.injective).1 ?_
  change IsIntegral ℤ (τ ((u - 1) / M))
  rw [hc]
  exact hb.sub (hui.mul ha)

end GlobalTheory
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.CM.TenExp

theorem mem_of_countable {V : Type*} [AddCommGroup V] [Module ℂ V] {Λ : Set V} (hΛ : Λ.Countable)
    (W : Submodule ℂ V) {v : V} (h : ∀ z : ℂ, ∃ l ∈ Λ, z • v - l ∈ W) : v ∈ W := by
  choose l hl hW using h
  have := hΛ.to_subtype
  obtain ⟨z, z', hne, e⟩ : ∃ z z' : ℂ, z ≠ z' ∧ l z = l z' := by
    by_contra hc
    push Not at hc
    have hi : Function.Injective fun z => (⟨l z, hl z⟩ : Λ) := fun z z' e => by
      by_contra h0
      exact hc z z' h0 (congrArg Subtype.val e)
    exact not_countable (α := ℝ) (hi.comp Complex.ofReal_injective).countable
  have h1 := W.sub_mem (hW z) (hW z')
  rw [e, sub_sub_sub_cancel_right, ← sub_smul] at h1
  exact (W.smul_mem_iff (sub_ne_zero.2 hne)).1 h1

theorem linear_eq_of_countable {U V : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    {Λ : Set V} (hΛ : Λ.Countable) {F F' : U →ₗ[ℂ] V} (h : ∀ u, F u - F' u ∈ Λ) : F = F' := by
  ext u
  rw [← sub_eq_zero, ← Submodule.mem_bot ℂ]
  refine mem_of_countable hΛ ⊥ fun z => ⟨_, h (z • u), ?_⟩
  simp [smul_sub]

section Tensor

variable {O M : Type} [CommRing O] [Algebra O ℂ] [AddCommGroup M] [Module O M]

theorem exists_lift {V : Type} [AddCommGroup V] [Module ℂ V] (f : M →+ V)
    (hf : ∀ (o : O) a, f (o • a) = algebraMap O ℂ o • f a) :
    ∃ F : ℂ ⊗[O] M →ₗ[ℂ] V, ∀ z a, F (z ⊗ₜ a) = z • f a := by
  letI : Module O V := Module.compHom V (algebraMap O ℂ)
  haveI : IsScalarTower O ℂ V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f' : M →ₗ[O] V := { f with map_smul' := hf }
  exact ⟨f'.liftBaseChange ℂ, fun z a => rfl⟩

theorem tensor_unif {X Y V : Type} [AddCommGroup X] [Module O X]
    [AddCommGroup Y] [Module O Y] [AddCommGroup V] [Module ℂ V] (eqv : M ⊗[O] X ≃ₗ[O] Y) (e₀ : ℂ →ₗ[O] X)
    (hs : Function.Surjective e₀) (hk : ∀ z, e₀ z = 0 ↔ z ∈ Set.range (algebraMap O ℂ)) (ex : V →+ Y)
    (hΛ : Set.Countable {v | ex v = 0}) (P : M →+ V) (hP : ∀ (o : O) a, P (o • a) = algebraMap O ℂ o • P a)
    (hi : Function.Injective P) (hex : ∀ (z : ℂ) a, ex (z • P a) = eqv (a ⊗ₜ e₀ z)) :
    Submodule.span ℂ (Set.range P) = ⊤ ∧ (∀ v, ex v = 0 ↔ v ∈ P.range) ∧
      ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (f : M →+ V'), (∀ (o : O) a, f (o • a) = algebraMap O ℂ o • f a) →
        ∃ F : V →ₗ[ℂ] V', ∀ a, F (P a) = f a := by
  obtain ⟨Φ, hΦ⟩ := exists_lift P hP
  have hc : ∀ t, ex (Φ t) = eqv (TensorProduct.comm O X M (e₀.rTensor M t)) := fun t => by
    induction t with
    | tmul z a => simp [hΦ, hex]
    | add x y hx hy => simp [hx, hy]
  have hker : ∀ t, ex (Φ t) = 0 → ∃ a, t = 1 ⊗ₜ a := fun t ht => by
    rw [hc, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at ht
    obtain ⟨s, rfl⟩ := (rTensor_exact M (f := Algebra.linearMap O ℂ) hk hs t).1 ht
    obtain ⟨a, rfl⟩ := (TensorProduct.lid O M).symm.surjective s
    exact ⟨a, by simp⟩
  have hsurj : Function.Surjective Φ := fun v => by
    refine mem_of_countable hΛ (LinearMap.range Φ) fun z => ?_
    obtain ⟨t, ht⟩ := (eqv.surjective.comp ((TensorProduct.comm O X M).surjective.comp
      (LinearMap.rTensor_surjective M hs))) (ex (z • v))
    refine ⟨z • v - Φ t, ?_, t, by simp⟩
    simp only [Set.mem_setOf_eq, map_sub, hc, ← ht]
    exact sub_self _
  have hinj : Function.Injective Φ := (injective_iff_map_eq_zero _).2 fun t ht => by
    obtain ⟨a, rfl⟩ := hker t (by rw [ht, map_zero])
    rw [hΦ, one_smul, map_eq_zero_iff _ hi] at ht
    simp [ht]
  refine ⟨eq_top_iff.2 fun v _ => ?_, fun v => ⟨fun hv => ?_, ?_⟩, fun V' _ _ f hf => ?_⟩
  · obtain ⟨t, rfl⟩ := hsurj v
    induction t with
    | tmul z a => rw [hΦ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  · obtain ⟨t, rfl⟩ := hsurj v
    obtain ⟨a, rfl⟩ := hker t hv
    exact ⟨a, by rw [hΦ, one_smul]⟩
  · rintro ⟨a, rfl⟩
    rw [← one_smul ℂ (P a), hex, (hk 1).2 ⟨1, map_one _⟩]
    simp
  · obtain ⟨F, hF⟩ := exists_lift f hf
    refine ⟨F ∘ₗ (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm.toLinearMap, fun a => ?_⟩
    have : P a = LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩ (1 ⊗ₜ a) :=
      ((hΦ 1 a).trans (one_smul _ _)).symm
    rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hF, one_smul]

end Tensor

variable {E : Type} [Field E] [NumberField E]

theorem exists_diagonal_coordinates {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (r : 𝓞 E →+* Module.End ℂ V) :
    ∃ (g : ℕ) (B : V ≃ₗ[ℂ] (Fin g → ℂ)) (ty : Fin g → (E →+* ℂ)), ∀ (a : 𝓞 E) v j, B (r a v) j = ty j (a : E) * B v j := by
  classical
  have hs : EigenSplit.IsSplitting fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E) := by
    obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E ℂ)
    exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  let b := (EigenSplit.isInternal_eigenSub hs r).collectedBasis
    fun φ => Module.finBasis ℂ (EigenSplit.eigenSub r (φ.comp (algebraMap (𝓞 E) E)))
  let e := Fintype.equivFin (Σ φ : E →+* ℂ,
    Fin (Module.finrank ℂ (EigenSplit.eigenSub r (φ.comp (algebraMap (𝓞 E) E)))))
  have hb : ∀ a j, r a (b.reindex e j) = (e.symm j).1 (a : E) • b.reindex e j := fun a j => by
    rw [Module.Basis.reindex_apply]
    exact EigenSplit.mem_eigenSub.1 ((EigenSplit.isInternal_eigenSub hs r).collectedBasis_mem _ (e.symm j)) a
  refine ⟨_, (b.reindex e).equivFun, fun j => (e.symm j).1, fun a v j => ?_⟩
  generalize b.reindex e = b' at hb
  obtain ⟨z, rfl⟩ := b'.equivFun.symm.surjective v
  have : r a (b'.equivFun.symm z) = b'.equivFun.symm fun j => (e.symm j).1 (a : E) * z j := by

    simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, hb, smul_smul, mul_comm]
  rw [this]
  simp only [LinearEquiv.apply_symm_apply]

theorem card_type {M : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P : M →+ (Fin g → ℂ)} (hP : ∀ (s : 𝓞 E) a i, P (s • a) i = ty i (s : E) * P a i)
    (hs : Submodule.span ℂ (Set.range P) = ⊤) {w : 𝓞 E} {ω : ℂ} (hw : ∀ a, P (w • a) = ω • P a)
    (hu : ∀ f : M →+ ℂ, (∀ a, f (w • a) = ω • f a) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ a, F (P a) = f a)
    (τ : E →+* ℂ) : (τ w = ω → Nat.card {i // ty i = τ} = Module.finrank (𝓞 E) M) ∧
      (τ w ≠ ω → Nat.card {i // ty i = τ} = 0) := by
  classical
  have ext : ∀ F F' : (Fin g → ℂ) →ₗ[ℂ] ℂ, (∀ a, F (P a) = F' (P a)) → F = F' := fun F F' h =>
    LinearMap.ext_on_range hs h
  refine ⟨fun hτ => ?_, fun hτ => ?_⟩
  · letI : Algebra (𝓞 E) ℂ := (τ.comp (algebraMap (𝓞 E) E)).toAlgebra
    have hsm : ∀ (s : 𝓞 E) (z : ℂ), s • z = τ s * z := fun _ _ => rfl
    haveI : FaithfulSMul (𝓞 E) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2
      (τ.injective.comp (IsFractionRing.injective (𝓞 E) E))
    let f : {i // ty i = τ} → (M →ₗ[𝓞 E] ℂ) := fun i =>
      { toFun := fun a => P a i, map_add' := fun a b => by simp, map_smul' := fun s a => by simp [hP, hsm, i.2] }
    have hli : LinearIndependent ℂ f := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have := ext (∑ j : {i // ty i = τ}, c j • LinearMap.proj j.1) 0 fun a => by
        simpa [f] using DFunLike.congr_fun hc a
      have := DFunLike.congr_fun this (Pi.single i.1 1)
      simpa [Pi.single_apply, Subtype.val_inj] using this
    have hsp : ⊤ ≤ Submodule.span ℂ (Set.range f) := fun φ _ => by
      obtain ⟨F, hF⟩ := hu φ.toAddMonoidHom fun a => by simp [hsm, hτ]
      have h0 : ∀ i, ty i ≠ τ → F (Pi.single i 1) = 0 := fun i hi => by
        obtain ⟨s, hs⟩ : ∃ s : 𝓞 E, ty i s ≠ τ s := by
          by_contra hc
          push Not at hc
          exact hi (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))
        have := ext (F ∘ₗ LinearMap.pi fun j => ty j (s : E) • LinearMap.proj j) (τ s • F) fun a => by
          have e : (LinearMap.pi fun j => ty j (s : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) j) (P a) =
              P (s • a) := funext fun j => by simp [hP]
          rw [LinearMap.comp_apply, e, hF, LinearMap.smul_apply, hF]
          simp [hsm]
        have := DFunLike.congr_fun this (Pi.single i 1)
        have e : (LinearMap.pi fun j => ty j (s : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) j)
            (Pi.single i 1) = ty i s • Pi.single i 1 := funext fun j => by
          by_cases h : j = i <;> simp [h]
        rw [LinearMap.comp_apply, e, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at this
        exact (mul_eq_mul_right_iff.1 this).resolve_left hs
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => F (Pi.single i.1 1), LinearMap.ext fun a => ?_⟩
      have e := hF a
      rw [LinearMap.pi_apply_eq_sum_univ, ← Fintype.sum_subtype_add_sum_subtype (fun i => ty i = τ),
        Finset.sum_eq_zero (s := Finset.univ (α := {i // ¬ ty i = τ})) fun i _ => by
          have := h0 i.1 i.2
          rw [show (fun j => if i.1 = j then (1 : ℂ) else 0) = Pi.single i.1 1 from by
            funext j; simp [Pi.single_apply, eq_comm], this, smul_zero], add_zero] at e
      refine Eq.trans ?_ e
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
      congr 2
      funext j; simp [Pi.single_apply, eq_comm]
    rw [Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis (Module.Basis.mk hli hsp),
      (LinearMap.liftBaseChangeEquiv ℂ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) M ℂ).finrank_eq]
    exact Subspace.dual_finrank_eq
  · rw [Nat.card_eq_zero]
    refine Or.inl ⟨fun i => hτ ?_⟩
    have := ext (τ w • LinearMap.proj i.1) (ω • LinearMap.proj i.1) fun a => by
      have := congrFun (hw a) i.1
      rw [hP, i.2] at this
      simpa using this
    simpa using DFunLike.congr_fun this (Pi.single i.1 1)

end GlobalTheory.CM.TenExp
end
