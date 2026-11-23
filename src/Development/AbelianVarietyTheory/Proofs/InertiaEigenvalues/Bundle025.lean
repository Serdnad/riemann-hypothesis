module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Data.Nat.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

section

open Matrix

namespace GlobalTheory

theorem frobenius_matrix_comatrix_divisible {R : Type} [CommRing R] [IsDomain R] (d N N₀ q : ℕ) (p : Fin d → ℕ) (ξ : R)
    (A A' B B' c c' V₀ V₀' : Matrix (Fin d) (Fin d) R) (hξ : ξ ≠ 0) (hB : B * B' = 1) (hc : c * c' = 1)
    (hV : V₀ * V₀' = 1) (hA : A * A' = ξ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hid : ξ ^ q • (A * B * c) = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j)))
    (hN : N₀ ≤ N) (hp : ∀ i, |(p i : ℤ) - q| ≤ N₀) :
    (∀ i j, ξ ^ (N - N₀) ∣ A i j) ∧ ∀ i j, ξ ^ (N - N₀) ∣ A' i j := by
  have hp1 : ∀ k, q ≤ p k + N₀ := fun k => by
    have := (abs_le.mp (hp k)).1; omega
  have hp2 : ∀ k, p k ≤ q + N₀ := fun k => by
    have := (abs_le.mp (hp k)).2; omega
  have hq0 : ξ ^ q ≠ 0 := pow_ne_zero _ hξ
  have cancel : ∀ (s : R), s ≠ 0 → ∀ M M' : Matrix (Fin d) (Fin d) R, s • M = s • M' → M = M' := by
    intro s hs M M' h
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hs this
  have hA1 : ξ ^ q • A = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j) * (c' * B')) := by
    have : A = A * B * c * (c' * B') := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (A * B) c c', hc, Matrix.mul_one, Matrix.mul_assoc, hB,
        Matrix.mul_one]
    conv_lhs => rw [this]
    rw [← Matrix.smul_mul, hid, Matrix.smul_mul]
  constructor
  · intro i j
    have e := congrFun (congrFun hA1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    rw [Matrix.mul_apply] at e
    simp only [Matrix.mul_diagonal] at e
    have hdiv : ξ ^ q * ξ ^ (N - N₀) ∣ ξ ^ q * A i j := by
      rw [e, Finset.mul_sum]
      apply Finset.dvd_sum
      intro k _
      have h1 : ξ ^ q * ξ ^ (N - N₀) ∣ ξ ^ N * ξ ^ p k := by
        rw [← pow_add, ← pow_add]; exact pow_dvd_pow _ (by have := hp1 k; omega)
      exact h1.trans ⟨V₀ i k * (c' * B') k j, by ring⟩
    exact (mul_dvd_mul_iff_left hq0).mp hdiv
  · set D' : Matrix (Fin d) (Fin d) R := Matrix.diagonal (fun k => ξ ^ (N₀ + q - p k)) with hD'
    have hDD : Matrix.diagonal (fun j => ξ ^ p j) * D' = ξ ^ (N₀ + q) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [hD', Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        rw [← pow_add]; congr 1; have := hp2 i; omega
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    set Z := B * c * D' * V₀' with hZ
    have hAZ : ξ ^ q • (A * Z) = ξ ^ (N + (N₀ + q)) • (1 : Matrix (Fin d) (Fin d) R) := by
      have : A * Z = A * B * c * D' * V₀' := by simp only [hZ, Matrix.mul_assoc]
      rw [this, Matrix.mul_assoc (A * B * c), ← Matrix.smul_mul, hid, Matrix.smul_mul,
        Matrix.mul_assoc V₀, ← Matrix.mul_assoc _ D', hDD, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, hV, smul_smul, ← pow_add]
    have hAZ2 : A * (ξ ^ (N - N₀) • Z) = A * A' := by
      apply cancel _ hq0
      rw [Matrix.mul_smul, smul_comm, hAZ, smul_smul, hA, smul_smul, ← pow_add, ← pow_add]
      congr 2; omega
    have hdetA : A.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hA
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
      exact pow_ne_zero _ (pow_ne_zero _ hξ) this.symm
    have hA' : A' = ξ ^ (N - N₀) • Z := by
      apply cancel _ hdetA
      rw [← Matrix.one_mul A', ← Matrix.one_mul (ξ ^ (N - N₀) • Z), ← Matrix.smul_mul, ← Matrix.smul_mul,
        ← Matrix.adjugate_mul, Matrix.mul_assoc, Matrix.mul_assoc, hAZ2]
    intro i j
    rw [hA', Matrix.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _

end GlobalTheory
end

section

namespace GlobalTheory


open Matrix in
theorem blockDecomposition_baseChange {K L : Type} [Field K] [Field L] (φ : K →+* L) {n r t : ℕ}
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) :
    ∃ e' : (Fin n → L) ≃ₗ[L] ((Fin r → L) × (Fin t → L)),
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin r) (Fin r) K) (d : Fin t → K),
        (∀ u, e (M.mulVec u) = (P.mulVec (e u).1, fun c => d c * (e u).2 c)) →
        ∀ u, e' ((M.map φ).mulVec u) =
          ((P.map φ).mulVec (e' u).1, fun c => φ (d c) * (e' u).2 c) := by
  classical

  have hext : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) K), (∀ v, X *ᵥ v = Y *ᵥ v) → X = Y :=
    fun X Y h => Matrix.toLin'.injective (LinearMap.ext fun v => by
      simpa only [Matrix.toLin'_apply] using h v)

  obtain ⟨A₁, hA₁⟩ : ∃ A : Matrix (Fin r) (Fin n) K, ∀ v, A *ᵥ v = (e v).1 :=
    ⟨LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ e.toLinearMap), fun v => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A : Matrix (Fin t) (Fin n) K, ∀ v, A *ᵥ v = (e v).2 :=
    ⟨LinearMap.toMatrix' (LinearMap.snd K _ _ ∘ₗ e.toLinearMap), fun v => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B : Matrix (Fin n) (Fin r) K, ∀ p, B *ᵥ p = e.symm (p, 0) :=
    ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl K _ _), fun p => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B : Matrix (Fin n) (Fin t) K, ∀ q, B *ᵥ q = e.symm (0, q) :=
    ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inr K _ _), fun q => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩

  have h11 : A₁ * B₁ = 1 := hext _ _ fun p => by
    rw [← Matrix.mulVec_mulVec, hB₁, hA₁, LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have h12 : A₁ * B₂ = 0 := hext _ _ fun q => by
    rw [← Matrix.mulVec_mulVec, hB₂, hA₁, LinearEquiv.apply_symm_apply, Matrix.zero_mulVec]
  have h21 : A₂ * B₁ = 0 := hext _ _ fun p => by
    rw [← Matrix.mulVec_mulVec, hB₁, hA₂, LinearEquiv.apply_symm_apply, Matrix.zero_mulVec]
  have h22 : A₂ * B₂ = 1 := hext _ _ fun q => by
    rw [← Matrix.mulVec_mulVec, hB₂, hA₂, LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have hBA : B₁ * A₁ + B₂ * A₂ = 1 := hext _ _ fun u => by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₁, hA₂, hB₁, hB₂,
      ← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, LinearEquiv.symm_apply_apply,
      Matrix.one_mulVec]

  have h11' : A₁.map φ * B₁.map φ = 1 := by
    rw [← Matrix.map_mul, h11, Matrix.map_one _ φ.map_zero φ.map_one]
  have h12' : A₁.map φ * B₂.map φ = 0 := by
    rw [← Matrix.map_mul, h12, Matrix.map_zero _ φ.map_zero]
  have h21' : A₂.map φ * B₁.map φ = 0 := by
    rw [← Matrix.map_mul, h21, Matrix.map_zero _ φ.map_zero]
  have h22' : A₂.map φ * B₂.map φ = 1 := by
    rw [← Matrix.map_mul, h22, Matrix.map_one _ φ.map_zero φ.map_one]
  have hBA' : B₁.map φ * A₁.map φ + B₂.map φ * A₂.map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add φ φ.map_add, hBA,
      Matrix.map_one _ φ.map_zero φ.map_one]

  refine ⟨LinearEquiv.ofLinearMap ((Matrix.toLin' (A₁.map φ)).prod (Matrix.toLin' (A₂.map φ)))
    ((Matrix.toLin' (B₁.map φ)).coprod (Matrix.toLin' (B₂.map φ))) ?_ ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨p, q⟩ := x
    refine Prod.ext ?_ ?_ <;>
      simp [Matrix.mulVec_add, Matrix.mulVec_mulVec, h11', h12', h21', h22']
  · refine LinearMap.ext fun u => ?_
    have key : (B₁.map φ * A₁.map φ) *ᵥ u + (B₂.map φ * A₂.map φ) *ᵥ u = u := by
      rw [← Matrix.add_mulVec, hBA', Matrix.one_mulVec]
    simpa [Matrix.mulVec_mulVec] using key
  · intro M P d h u

    have hM₁ : A₁ * M = P * A₁ := hext _ _ fun v => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₁, hA₁, h v]
    have hM₂ : A₂ * M = Matrix.diagonal d * A₂ := hext _ _ fun v => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₂, hA₂, h v]
      funext c
      rw [Matrix.mulVec_diagonal]
    have hM₁' : A₁.map φ * M.map φ = P.map φ * A₁.map φ := by
      rw [← Matrix.map_mul, hM₁, Matrix.map_mul]
    have hM₂' : A₂.map φ * M.map φ = Matrix.diagonal (fun c => φ (d c)) * A₂.map φ := by
      rw [← Matrix.map_mul, hM₂, Matrix.map_mul, Matrix.diagonal_map φ.map_zero]
    refine Prod.ext ?_ (funext fun c => ?_)
    · change A₁.map φ *ᵥ (M.map φ *ᵥ u) = P.map φ *ᵥ (A₁.map φ *ᵥ u)
      rw [Matrix.mulVec_mulVec, hM₁', ← Matrix.mulVec_mulVec]
    · change (A₂.map φ *ᵥ (M.map φ *ᵥ u)) c = φ (d c) * (A₂.map φ *ᵥ u) c
      rw [Matrix.mulVec_mulVec, hM₂', ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

end GlobalTheory
end

section

namespace GlobalTheory

open Matrix

theorem exists_adapted_frame_of_isotropic_columns :
    ∀ (E : Type) [Field E] (r : ℕ) (Y : Submodule E ((Fin r → E) × (Fin r → E))),
      Module.finrank E Y = r →
      ∀ (C : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E),
        Submodule.span E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y →
        ∀ (s : ℕ) (I : Matrix (Fin r) (Fin s) E), LinearIndependent E I.transpose →
          (∀ j, ((fun a => I a j), (0 : Fin r → E)) ∈ Y) →
          ∃ (t : ℕ) (J : Matrix (Fin r) (Fin s) E) (K : Matrix (Fin r) (Fin t) E)
            (L : Matrix (Fin s) (Fin r) E) (M : Matrix (Fin t) (Fin r) E),
            C.1 * J = I ∧ C.2 * J = 0 ∧ L * J = 1 ∧ L * K = 0 ∧ M * J = 0 ∧ M * K = 1 ∧
              J * L + K * M = 1 := by
  intro E _ r Y _ C hspan s I hI hmem

  have hc : ∀ j, ∃ c : Fin r → E,
      ∑ k, c k • ((fun a => C.1 a k), (fun a => C.2 a k)) = ((fun a => I a j), (0 : Fin r → E)) := by
    intro j
    have := hmem j
    rw [← hspan] at this
    exact (Submodule.mem_span_range_iff_exists_fun E).mp this
  choose c hc using hc
  let J : Matrix (Fin r) (Fin s) E := Matrix.of fun k j => c j k
  have h1 : C.1 * J = I := by
    ext a j
    have := congrFun (congrArg Prod.fst (hc j)) a
    simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h2 : C.2 * J = 0 := by
    ext a j
    have := congrFun (congrArg Prod.snd (hc j)) a
    simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply, Matrix.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

  have hIinj : Function.Injective I.mulVec := Matrix.mulVec_injective_iff.mpr hI
  have hJinj : Function.Injective J.mulVec := by
    intro x y hxy
    apply hIinj
    rw [← h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
  let jL : (Fin s → E) →ₗ[E] (Fin r → E) := Matrix.toLin' J
  have hker : LinearMap.ker jL = ⊥ := LinearMap.ker_eq_bot.mpr (by
    intro x y hxy; exact hJinj (by simpa [jL, Matrix.toLin'_apply] using hxy))
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective jL hker
  let Wk := LinearMap.ker g
  let b := Module.finBasis E Wk
  let kL : (Fin (Module.finrank E Wk) → E) →ₗ[E] (Fin r → E) :=
    Wk.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hgP : ∀ x, g (x - jL (g x)) = 0 := by
    intro x
    rw [map_sub]
    have := LinearMap.congr_fun hg (g x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let ψ : (Fin r → E) →ₗ[E] Wk :=
    LinearMap.codRestrict Wk (LinearMap.id - jL ∘ₗ g) (fun x => by
      simpa [Wk, LinearMap.mem_ker] using hgP x)
  let mL : (Fin r → E) →ₗ[E] (Fin (Module.finrank E Wk) → E) := b.equivFun.toLinearMap ∘ₗ ψ
  have hJ : J = LinearMap.toMatrix' jL := by simp [jL]
  refine ⟨Module.finrank E Wk, J, LinearMap.toMatrix' kL, LinearMap.toMatrix' g,
    LinearMap.toMatrix' mL, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp]
    have : g ∘ₗ kL = 0 := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, kL]
      exact (b.equivFun.symm y).2
    rw [this, map_zero]
  · rw [hJ, ← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ jL = 0 := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, mL]
      have : ψ (jL x) = 0 := by
        apply Subtype.ext
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, ZeroMemClass.coe_zero]
        have := LinearMap.congr_fun hg x
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
        rw [this, sub_self]
      rw [this, map_zero]
    rw [this, map_zero]
  · rw [← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ kL = LinearMap.id := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_apply, mL]
      have : ψ (kL y) = b.equivFun.symm y := by
        apply Subtype.ext
        have hk : g (kL y) = 0 := (b.equivFun.symm y).2
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, hk, map_zero, sub_zero]
        rfl
      rw [this]
      exact b.equivFun.apply_symm_apply y
    rw [this, LinearMap.toMatrix'_id]
  · rw [hJ, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, ← map_add (f := _),
      ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, mL, kL]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.coe_subtype, ψ,
      LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel

end GlobalTheory
end

section

namespace GlobalTheory.UnipotentDecomposition

open Matrix

theorem udl_apply {O : Type} [CommRing O] {m : ℕ} (A B : Matrix (Fin m) (Fin m) O) (d : Fin m → O) (i j : Fin m) :
    (A * Matrix.diagonal d * B) i j = ∑ k, A i k * d k * B k j := by
  rw [Matrix.mul_apply]; simp_rw [Matrix.mul_diagonal]

theorem key {O : Type} [CommRing O] [IsLocalRing O] {α β : O} (hab : ¬ IsUnit (α * β)) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O),
      (∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)) → (∀ i, IsUnit (g i i)) →
      ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O),
        (∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1) ∧ (i < j → α ∣ u i j)) ∧
        (∀ i j, (i < j → l i j = 0) ∧ (i = j → l i j = 1) ∧ (j < i → β ∣ l i j)) ∧
        g = (u * Matrix.diagonal fun i => (d i : O)) * l ∧ ∀ i, α * β ∣ (d i : O) - g i i := by
  intro n
  induction n with
  | zero =>
    intro g _ _
    refine ⟨1, fun i => i.elim0, 1, fun i => i.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    ext i; exact i.elim0
  | succ n ih =>
    intro g hg hu
    set a : Oˣ := (hu (Fin.last n)).unit with ha
    have haa : (a : O) = g (Fin.last n) (Fin.last n) := IsUnit.unit_spec _
    have hinv : (↑a⁻¹ : O) * ↑a = 1 := Units.inv_mul a
    set r : Fin n → O := fun i => g i.castSucc (Fin.last n) with hr_def
    set c : Fin n → O := fun j => g (Fin.last n) j.castSucc with hc_def
    set G : Matrix (Fin n) (Fin n) O := fun i j => g i.castSucc j.castSucc - r i * ↑a⁻¹ * c j with hG_def
    have hr : ∀ i, α ∣ r i := fun i => (hg i.castSucc (Fin.last n)).1 (Fin.castSucc_lt_last i)
    have hc : ∀ j, β ∣ c j := fun j => (hg (Fin.last n) j.castSucc).2 (Fin.castSucc_lt_last j)
    have hG : ∀ i j, (i < j → α ∣ G i j) ∧ (j < i → β ∣ G i j) := by
      intro i j
      constructor
      · intro h
        exact dvd_sub ((hg _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_right (Dvd.dvd.mul_right (hr i) _) _)
      · intro h
        exact dvd_sub ((hg _ _).2 (Fin.castSucc_lt_castSucc_iff.2 h)) (Dvd.dvd.mul_left (hc j) _)
    have hrc : ∀ i, α * β ∣ r i * ↑a⁻¹ * c i := by
      intro i
      rw [show r i * ↑a⁻¹ * c i = r i * c i * ↑a⁻¹ by ring]
      exact Dvd.dvd.mul_right (mul_dvd_mul (hr i) (hc i)) _
    have hGu : ∀ i, IsUnit (G i i) := by
      intro i
      by_contra h
      have h1 : r i * ↑a⁻¹ * c i ∈ nonunits O := fun hu' => hab (isUnit_of_dvd_unit (hrc i) hu')
      have h2 := IsLocalRing.nonunits_add (show G i i ∈ nonunits O from h) h1
      have h3 : G i i + r i * ↑a⁻¹ * c i = g i.castSucc i.castSucc := sub_add_cancel _ _
      rw [h3] at h2
      exact h2 (hu _)
    obtain ⟨U, D, L, hU, hL, hUDL, hD⟩ := ih G hG hGu
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun _ => 0) j)
              (fun i' => Fin.lastCases (motive := fun _ => O) (r i' * ↑a⁻¹) (fun j' => U i' j') j) i,
            fun i => Fin.lastCases (motive := fun _ => Oˣ) a D i,
            Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun j' => ↑a⁻¹ * c j') j)
              (fun i' => Fin.lastCases (motive := fun _ => O) 0 (fun j' => L i' j') j) i,
            ?_, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
        first | exact hr i | exact (hr i).mul_right _
      · simpa using hU i j
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
        first | exact hc j | exact (hc j).mul_left _
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
      · simpa using hL i j
    · ext i j
      rw [udl_apply, Fin.sum_univ_castSucc]
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [haa]
      · simp [c]
        done
      · simp [r]
        done
      · have e := congrFun (congrFun hUDL i) j
        rw [udl_apply] at e
        simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero, mul_one]
        rw [← e]
        simp only [G]
        linear_combination (-(r i * ↑a⁻¹ * c j)) * hinv
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [haa]
      · have e : ((D i : O)) - g i.castSucc i.castSucc = ((D i : O) - G i i) - r i * ↑a⁻¹ * c i := by
          simp [G]; ring
        simpa [e] using dvd_sub (hD i) (hrc i)

theorem main : (let d1 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (β : O) (l : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → l i j = (0 : O)) ∧ (i = j → l i j = (1 : O)) ∧ (j < i → β ∣ l i j)); let d2 : {O : Type} → [CommRing O] → {n : ℕ} → O → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α β : O) (g : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)); let d3 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α : O) (u : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (j < i → u i j = (0 : O)) ∧ (i = j → u i j = (1 : O)) ∧ (i < j → α ∣ u i j)); ∀ {O : Type} [inst : CommRing O] [IsLocalRing O] {α β : O}, ¬IsUnit (α * β) → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), d2 α β g → (∀ (i : Fin n), IsUnit (g i i)) → ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O), d3 α u ∧ d1 β l ∧ g = (u * Matrix.diagonal fun (i : Fin n) ↦ (↑(d i) : O)) * l ∧ ∀ (i : Fin n), α * β ∣ (↑(d i) : O) - g i i) := by
  intro d1 d2 d3 O _ _ α β hab n g hg hu
  exact key hab n g hg hu

end GlobalTheory.UnipotentDecomposition
end

section

namespace GlobalTheory.HarmLine

def zR (m n p : ℕ) : Fin (min p m) × Fin n → Fin m × Fin n :=
  fun u => (⟨u.1, lt_of_lt_of_le u.1.2 (min_le_right _ _)⟩, u.2)

def yR (m n p : ℕ) : Fin (m - p) × Fin n → Fin m × Fin n :=
  fun u => (⟨m - 1 - u.1, by have := u.1.2; omega⟩, u.2)

theorem zR_inj (m n p : ℕ) : Function.Injective (zR m n p) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [zR, Prod.mk.injEq, Fin.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) h.2

theorem yR_inj (m n p : ℕ) : Function.Injective (yR m n p) := by
  rintro ⟨⟨a, ha⟩, b⟩ ⟨⟨c, hc⟩, d⟩ h
  simp only [yR, Prod.mk.injEq, Fin.mk.injEq] at h
  exact Prod.ext (Fin.ext (by simp only; omega)) h.2

theorem zR_ne_yR (m n p : ℕ) (u : Fin (min p m) × Fin n) (v : Fin (m - p) × Fin n) : zR m n p u ≠ yR m n p v := by
  intro h
  simp only [zR, yR, Prod.mk.injEq, Fin.mk.injEq] at h
  have := u.1.2; have := v.1.2
  have := min_le_left p m
  omega

theorem zR_yR_cover (m n p : ℕ) (s : Fin m × Fin n) : (∃ u, zR m n p u = s) ∨ ∃ v, yR m n p v = s := by
  rcases s with ⟨i, a⟩
  by_cases h : (i : ℕ) < p
  · left
    exact ⟨(⟨i, lt_min h i.2⟩, a), rfl⟩
  · right
    refine ⟨(⟨m - 1 - i, by have := i.2; omega⟩, a), ?_⟩
    simp only [yR, Prod.mk.injEq, and_true]
    ext
    simp only
    have := i.2
    omega

end GlobalTheory.HarmLine
end
