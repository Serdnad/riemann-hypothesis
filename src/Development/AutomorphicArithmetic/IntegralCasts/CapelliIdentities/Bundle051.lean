module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

section

theorem UpperTheory.measurable_matrix_inv :
    ∀ n : ℕ, Measurable (fun x : Fin n → Fin n → ℂ => (Matrix.of.symm ((Matrix.of x : Matrix (Fin n) (Fin n) ℂ)⁻¹) : Fin n → Fin n → ℂ)) := by
  intro n
  have hc : Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ)) :=
    continuous_id
  have hdet : Measurable (fun x : Fin n → Fin n → ℂ =>
      (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).det) := hc.matrix_det.measurable
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hadj : Measurable (fun x : Fin n → Fin n → ℂ =>
      (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).adjugate i j) :=
    (hc.matrix_adjugate.matrix_elem i j).measurable
  have h := hdet.inv.mul hadj
  convert h using 1
  funext x
  simp only [Matrix.of_symm_apply, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv,
    smul_eq_mul, Pi.mul_apply, Pi.inv_apply]
end

section

theorem UpperTheory.Reformulated.B.Qm10.exists_rows_linearIndependent.{u, u_1, u_2} :
    ∀ {K : Type u_1} [inst : Field K] {r : Type u} {c : Type u_2} [Fintype r] [inst_2 : Fintype c]
    (P : Matrix r c K) {k : ℕ}, k ≤ P.rank → ∃ (I : Fin k → r), LinearIndependent K fun (p : Fin k) ↦ P (I p) := by
  intro K _ r c _ _ P k hk
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K P.row
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card (Fin k) ≤ Fintype.card κ := by
    rw [Fintype.card_fin, ← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row]
    exact hk
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨fun p ↦ a (e p), hli.comp e e.injective⟩
end

section

theorem UpperTheory.span_linear_independent_base :
    ∀ {A Ω C E V I : Type} [CommRing A] [Field Ω] [Field C] [AddCommGroup E] [Module Ω E] [AddCommGroup V]
          [Module C V] [Fintype I] {n : ℕ} (φ : A →+* Ω) (ψ : A →+* C) (κ : E ≃ₗ[Ω] (Fin n → Ω)) (κ' : V ≃ₗ[C] (Fin n → C))
          (F : I → E), Function.Injective φ → LinearIndependent Ω F →
          Submodule.span (↥φ.range) {e : E | ∃ a : Fin n → A, κ e = fun i => φ (a i)} =
            Submodule.span (↥φ.range) (Set.range F) →
          ∃ y : Module.Basis I C V, ∀ j, ∃ a : Fin n → A, (κ (F j) = fun i => φ (a i)) ∧ κ' (y j) = fun i => ψ (a i) := by
  intro A Ω C E V I _ _ _ _ _ _ _ _ n φ ψ κ κ' F hφ hF hspan
  classical
  have hlat : ∀ e ∈ Submodule.span (↥φ.range) {e : E | ∃ a : Fin n → A, κ e = fun i => φ (a i)},
      ∃ a : Fin n → A, κ e = fun i => φ (a i) := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, by ext i; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by ext i; simp [ha, hb]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, r, rfl⟩ := c
      refine ⟨r • a, ?_⟩
      change κ (φ r • x) = _
      ext i
      simp [ha]
  have ha : ∀ j, ∃ a : Fin n → A, κ (F j) = fun i => φ (a i) := fun j =>
    hlat _ (hspan ▸ Submodule.subset_span ⟨j, rfl⟩)
  choose a ha using ha
  have hb : ∀ k : Fin n, ∃ b : I → A, ∀ i, ∑ j, a j i * b j = (1 : Matrix (Fin n) (Fin n) A) i k := by
    intro k
    have hk : κ.symm (fun i => φ ((1 : Matrix (Fin n) (Fin n) A) i k)) ∈
        Submodule.span (↥φ.range) (Set.range F) := by
      rw [← hspan]
      exact Submodule.subset_span ⟨fun i => (1 : Matrix (Fin n) (Fin n) A) i k, by simp⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hk
    choose b hb using fun j => (c j).2
    refine ⟨b, fun i => hφ ?_⟩
    have h1 : ∑ j, φ (b j) • F j = κ.symm (fun i => φ ((1 : Matrix (Fin n) (Fin n) A) i k)) := by
      rw [← hc]
      exact Finset.sum_congr rfl fun j _ => by rw [hb j]; rfl
    have h2 := congrFun (congrArg κ h1) i
    rw [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    simp [ha, mul_comm]
  choose b hb using hb
  set P : Matrix (Fin n) I A := Matrix.of fun i j => a j i with hP
  set Q : Matrix I (Fin n) A := Matrix.of fun j k => b k j with hQ
  have hPQ : P * Q = 1 := by
    ext i k
    simpa [Matrix.mul_apply, hP, hQ] using hb k i
  have hQP : Q * P = 1 := by
    have hD : P * (Q * P - 1) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_one, sub_self]
    rw [← sub_eq_zero]
    generalize Q * P - 1 = D at hD
    ext l j
    have h0 : ∑ l, φ (D l j) • F l = 0 := by
      apply κ.injective
      ext i
      have h3 := congrArg φ (congrFun (congrFun hD i) j)
      simpa [Matrix.mul_apply, hP, ha, mul_comm] using h3
    apply hφ
    simpa using Fintype.linearIndependent_iff.1 hF _ h0 l
  have h1 : Q.map ψ * P.map ψ = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have h2 : P.map ψ * Q.map ψ = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  refine ⟨(Pi.basisFun C I).map ((Matrix.toLin'OfInv h1 h2).trans κ'.symm), fun j => ⟨a j, ha j, ?_⟩⟩
  ext i
  simp [Matrix.toLin'OfInv, hP]
end

section

theorem UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim.{u_1} :
    ∀ {K : Type u_1}
    [inst : Field K] (r : ℕ) (N : Matrix (Fin r) (Fin r) K),
    (∀ (k : ℕ), (1 : ℕ) ≤ k → k ≤ r → (N ^ k).trace = (0 : K)) → ∀ (k : ℕ), (1 : ℕ) ≤ k → (N ^ k).trace = (0 : K) := by
  intro K _ r N h k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hkr : k ≤ r
    · exact h k hk hkr
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 + r := ⟨k - r - 1, by omega⟩
      have hd : N.charpoly.natDegree = r := by
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      have hc : N.charpoly.coeff r = 1 := by
        have := (Matrix.charpoly_monic N).coeff_natDegree
        rwa [hd] at this
      have hCH := Matrix.aeval_self_charpoly N
      rw [Polynomial.aeval_eq_sum_range, hd, Finset.sum_range_succ, hc, one_smul] at hCH
      have h2 := congrArg (fun A => Matrix.trace (N ^ (m + 1) * A)) hCH
      simp only [mul_add, Finset.mul_sum, Matrix.mul_smul, ← pow_add, mul_zero, Matrix.trace_zero,
        Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul] at h2
      rw [Finset.sum_eq_zero, zero_add] at h2
      · exact h2
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [ih (m + 1 + i) (by omega) (by omega), smul_zero]
end

section

theorem UpperTheory.divisibility_filtration :
    ∀ {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] (l f ϖ : A) (σ R : ℕ) (E e : ℕ → ℕ)
        (r s : ℕ → A) (S : Set D) (Z : Submodule A D),
        (∀ a : A, f ∣ l * a → f ∣ a) →
        (∀ a b, E a + E b ≤ E (a + b)) → (∀ y, E y ≤ e y) → e 0 = 0 →
        (∀ y, f ∣ ϖ ^ y - r y) → (∀ y, l ^ e y * s y = l ^ σ * r y) → (∀ y, R < y → f ∣ ϖ ^ y) →
        (∀ x ∈ S, ∃ c : ℕ → D, c 0 = 0 ∧ (∀ y, c y ∈ S) ∧
          l ^ σ • x - ∑ y ∈ Finset.range (R + 1), (s y * l ^ (e y - E y)) • c y ∈ Z) →
        ∀ p ∈ Submodule.span A S, ∃ p' ∈ Submodule.span A S, l ^ (2 * σ) • p - f • p' ∈ Z := by
  intro A D _ _ _ l f ϖ σ R E e r s S Z hl hE hEe he0 hr hs hR hS
  classical
  let N : Submodule A D := Z ⊔ (Submodule.span A S).map (LinearMap.lsmul A D f)
  have hZN : ∀ z ∈ Z, z ∈ N := fun z hz => Submodule.mem_sup_left hz
  have hfN : ∀ w ∈ Submodule.span A S, f • w ∈ N := fun w hw =>
    Submodule.mem_sup_right (Submodule.mem_map.2 ⟨w, hw, rfl⟩)
  have hpow : ∀ (n : ℕ) (a : A), f ∣ l ^ n * a → f ∣ a := by
    intro n
    induction n with
    | zero => intro a h; simpa using h
    | succ n ih =>
      intro a h
      exact ih a (hl _ (by rwa [← mul_assoc, ← pow_succ']))
  obtain ⟨t, ht_def⟩ : ∃ t : ℕ → A, ∀ y, t y = s y * l ^ (e y - E y) := ⟨_, fun _ => rfl⟩
  have ht : ∀ y, l ^ E y * t y = l ^ σ * r y := by
    intro y
    rw [ht_def, ← hs y]
    calc l ^ E y * (s y * l ^ (e y - E y))
        = (l ^ E y * l ^ (e y - E y)) * s y := by ring
      _ = l ^ e y * s y := by rw [← pow_add, Nat.add_sub_cancel' (hEe y)]
  have hS' : ∀ x ∈ S, ∃ c : ℕ → D, c 0 = 0 ∧ (∀ y, c y ∈ S) ∧
      l ^ σ • x - ∑ y ∈ Finset.range (R + 1), t y • c y ∈ Z := by
    intro x hx
    obtain ⟨c, h0, h1, h2⟩ := hS x hx
    refine ⟨c, h0, h1, ?_⟩
    simpa only [ht_def] using h2
  have hbig : ∀ y, R < y → f ∣ t y := by
    intro y hy
    refine hpow (E y) _ ?_
    rw [ht]
    exact Dvd.dvd.mul_left ((dvd_sub_right (hR y hy)).1 (hr y)) _
  have hprod : ∀ y z, ∃ u, t y * t z =
      f * u + l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z) := by
    intro y z
    have hd : f ∣ t y * t z - l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z) := by
      refine hpow (E y + E z) _ ?_
      obtain ⟨a, ha⟩ := hr y
      obtain ⟨b, hb⟩ := hr z
      obtain ⟨c, hc⟩ := hr (y + z)
      have hy : r y = ϖ ^ y - f * a := by rw [← ha]; ring
      have hz : r z = ϖ ^ z - f * b := by rw [← hb]; ring
      have hyz : r (y + z) = ϖ ^ (y + z) - f * c := by rw [← hc]; ring
      have e1 : l ^ (E y + E z) * (t y * t z) = (l ^ σ * r y) * (l ^ σ * r z) := by
        rw [← ht y, ← ht z]; ring
      have e2 : l ^ (E y + E z) * (l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z))
          = l ^ σ * (l ^ σ * r (y + z)) := by
        rw [← ht (y + z)]
        calc l ^ (E y + E z) * (l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z))
            = l ^ σ * ((l ^ (E y + E z) * l ^ (E (y + z) - (E y + E z))) * t (y + z)) := by
              rw [pow_add l σ]; ring
          _ = l ^ σ * (l ^ E (y + z) * t (y + z)) := by
              rw [← pow_add, Nat.add_sub_cancel' (hE y z)]
      rw [mul_sub, e1, e2, hy, hz, hyz]
      refine ⟨l ^ σ * l ^ σ * (c - a * ϖ ^ z - b * ϖ ^ y + f * a * b), ?_⟩
      rw [pow_add ϖ y z]
      ring
    obtain ⟨u, hu⟩ := hd
    exact ⟨u, by rw [← hu]; ring⟩
  have hkey : ∀ (n y : ℕ), R + 1 ≤ y + n → ∀ w ∈ S, (l ^ σ * t y) • w ∈ N := by
    intro n
    induction n with
    | zero =>
      intro y hy w hw
      obtain ⟨u, hu⟩ := hbig y (by omega)
      have : (l ^ σ * t y) • w = f • ((l ^ σ * u) • w) := by
        rw [hu, smul_smul]; congr 1; ring
      rw [this]
      exact hfN _ (Submodule.smul_mem _ _ (Submodule.subset_span hw))
    | succ n ih =>
      intro y hy w hw
      obtain ⟨c, hc0, hcS, hcZ⟩ := hS' w hw
      have hsplit : (l ^ σ * t y) • w =
          t y • (l ^ σ • w - ∑ z ∈ Finset.range (R + 1), t z • c z)
            + ∑ z ∈ Finset.range (R + 1), (t y * t z) • c z := by
        rw [smul_sub, Finset.smul_sum, smul_smul, mul_comm (t y) (l ^ σ)]
        simp only [smul_smul, sub_add_cancel]
      rw [hsplit]
      refine N.add_mem (hZN _ (Z.smul_mem _ hcZ)) (N.sum_mem ?_)
      intro z _
      rcases Nat.eq_zero_or_pos z with rfl | hz
      · rw [hc0, smul_zero]
        exact N.zero_mem
      · obtain ⟨u, hu⟩ := hprod y z
        have hsum : (t y * t z) • c z = f • (u • c z)
            + l ^ (E (y + z) - (E y + E z)) • ((l ^ σ * t (y + z)) • c z) := by
          rw [hu, add_smul, smul_smul, smul_smul, pow_add]
          congr 2
          ring
        rw [hsum]
        exact N.add_mem (hfN _ (Submodule.smul_mem _ _ (Submodule.subset_span (hcS z))))
          (N.smul_mem _ (ih (y + z) (by omega) _ (hcS z)))
  have hgen : ∀ x ∈ S, l ^ (2 * σ) • x ∈ N := by
    intro x hx
    obtain ⟨c, _, hcS, hcZ⟩ := hS' x hx
    have hsplit : l ^ (2 * σ) • x =
        l ^ σ • (l ^ σ • x - ∑ z ∈ Finset.range (R + 1), t z • c z)
          + ∑ z ∈ Finset.range (R + 1), (l ^ σ * t z) • c z := by
      rw [smul_sub, Finset.smul_sum, two_mul, pow_add, smul_smul]
      simp only [smul_smul, sub_add_cancel]
    rw [hsplit]
    exact N.add_mem (hZN _ (Z.smul_mem _ hcZ))
      (N.sum_mem fun z _ => hkey (R + 1) z (by omega) _ (hcS z))
  have hall : Submodule.span A S ≤ N.comap (LinearMap.lsmul A D (l ^ (2 * σ))) :=
    Submodule.span_le.2 fun x hx => hgen x hx
  intro p hp
  obtain ⟨z, hz, v, hv, hzv⟩ := Submodule.mem_sup.1 (hall hp)
  obtain ⟨p', hp', rfl⟩ := Submodule.mem_map.1 hv
  refine ⟨p', hp', ?_⟩
  have : l ^ (2 * σ) • p - f • p' = z := by
    have h2 : l ^ (2 * σ) • p = z + f • p' := hzv.symm
    rw [h2, add_sub_cancel_right]
  rw [this]
  exact hz
end

section

theorem UpperTheory.Reformulated.B.Qi35.torsSat_mult :
    ∀ {M : Type} [inst : AddCommGroup M] (L : Set M)
    (N : Submodule ℤ M),
    (∀ x ∈ L, ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ n • x ∈ N) → ∀ x ∈ Submodule.span ℤ L, ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ n • x ∈ N := by
  intro M _ L N h x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hay
    · rw [mul_smul]
      exact N.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]
    exact N.smul_mem c hay
end

section

theorem UpperTheory.closure_span_coefficients :
    ∀ {R M L : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup L] (O : AddSubgroup R) (f : L →+ M) {m : ℕ} (x : Fin m → L),
        Submodule.span ℤ (Set.range x) = ⊤ → ∀ z : M,
          z ∈ AddSubgroup.closure {z : M | ∃ a ∈ O, ∃ l : L, z = a • f l} ↔
            ∃ a : Fin m → R, (∀ i, a i ∈ O) ∧ ∑ i, a i • f (x i) = z := by
  intro R M L _ _ _ _ O f m x hx z
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, l, rfl⟩ := hz
      have hl : l ∈ Submodule.span ℤ (Set.range x) := hx ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hl
      refine ⟨fun i => c i • a, fun i => O.zsmul_mem ha _, ?_⟩

      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, smul_assoc, smul_comm]
    | zero => exact ⟨0, fun _ => O.zero_mem, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      exact ⟨a + b, fun i => O.add_mem (ha i) (hb i), by
        simp [add_smul, Finset.sum_add_distrib]⟩
    | neg u _ hu =>
      obtain ⟨a, ha, rfl⟩ := hu
      exact ⟨-a, fun i => O.neg_mem (ha i), by simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨a i, ha i, x i, rfl⟩
end

section

noncomputable def UpperTheory.Reformulated.B.Qi34.flagSub :
    {F : Type} →
      [inst : Field F] →
        {N : Type} →
          [inst_1 : AddCommGroup N] → [inst_2 : _root_.Module F N] → {n : ℕ} → Module.Basis (Fin n) F N → ℕ → Submodule F N :=
    fun {F : Type} [Field F] {N : Type} [AddCommGroup N] [_root_.Module F N] {n : ℕ} (b : Module.Basis (Fin n) F N)
        (i : ℕ) ↦
      Submodule.span F ((⇑b : Fin n → N) '' {j : Fin n | (↑j : ℕ) < i})

theorem UpperTheory.Reformulated.B.Qi34.mem_flagSub_iff :
    ∀ {F : Type} [inst : Field F] {n : ℕ} (i : ℕ) (x : Fin n → F),
      x ∈ UpperTheory.Reformulated.B.Qi34.flagSub (Pi.basisFun F (Fin n)) i ↔ ∀ (j : Fin n), i ≤ (↑j : ℕ) → x j = (0 : F) := by
  intro F _ n i x
  unfold UpperTheory.Reformulated.B.Qi34.flagSub
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h j hj
    by_contra hx
    have hmem : j ∈ ((Pi.basisFun F (Fin n)).repr x).support := by
      rw [Finsupp.mem_support_iff, Pi.basisFun_repr]
      exact hx
    have hlt : (j : ℕ) < i := h (Finset.mem_coe.mpr hmem)
    omega
  · intro h j hj
    have hx : x j ≠ 0 := by
      have := Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hj)
      rwa [Pi.basisFun_repr] at this
    show (j : ℕ) < i
    by_contra hlt
    exact hx (h j (not_lt.mp hlt))
end

section

theorem UpperTheory.Reformulated.B.Qn17.tensor_sub_right.{u} :
    ∀ {R : Type} [inst : CommRing R] (M N : Type u) [inst_1 : AddCommMonoid M]
    [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M] [inst_4 : _root_.Module R N] [Subsingleton N],
    Subsingleton (TensorProduct R M N) := by
  intro R _ M N _ _ _ _ _
  have h : ∀ x : TensorProduct R M N, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => (h x).trans (h y).symm⟩
end

section

theorem UpperTheory.Reformulated.B.Qj4.tmul_surjective_rank_one :
    ∀ {O T X : Type} [inst : CommRing O]
    [inst_1 : AddCommGroup T] [inst_2 : _root_.Module O T] [inst_3 : AddCommGroup X] [inst_4 : _root_.Module O X]
    (x₀ : X), (∀ (x : X), ∃ (c : O), x = c • x₀) → ∀ (m : TensorProduct O T X), ∃ (t : T), t ⊗ₜ[O] x₀ = m := by
  intro O T X _ _ _ _ _ x₀ h m
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.zero_tmul T x₀⟩
  | tmul t x =>
    obtain ⟨c, rfl⟩ := h x
    exact ⟨c • t, TensorProduct.smul_tmul c t x₀⟩
  | add a b ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, TensorProduct.add_tmul s t x₀⟩
end

section

theorem UpperTheory.involution_map_compact_finite :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : MeasureTheory.Measure X) (U : Set X) (ι : X → X), Measurable ι → IsClosed U → ContinuousOn ι U → (∀ x ∈ U, ι x ∈ U) → (∀ x ∈ U, ι (ι x) = x) → μ Uᶜ = 0 → (∀ K : Set X, IsCompact K → μ K < ⊤) → ∀ K : Set X, IsCompact K → (μ.map ι) K < ⊤ := by
  intro X _ _ _ _ μ U ι hm hU hc hmaps hinv h0 hfin K hK
  rw [MeasureTheory.Measure.map_apply hm hK.measurableSet]
  have hcomp : IsCompact (ι '' (K ∩ U)) :=
    (hK.inter_right hU).image_of_continuousOn (hc.mono Set.inter_subset_right)
  have hsub : ι ⁻¹' K ⊆ ι '' (K ∩ U) ∪ Uᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl ⟨ι x, ⟨hx, hmaps x hxU⟩, hinv x hxU⟩
    · exact Or.inr hxU
  calc μ (ι ⁻¹' K) ≤ μ (ι '' (K ∩ U) ∪ Uᶜ) := MeasureTheory.measure_mono hsub
    _ ≤ μ (ι '' (K ∩ U)) + μ Uᶜ := MeasureTheory.measure_union_le _ _
    _ = μ (ι '' (K ∩ U)) := by rw [h0, add_zero]
    _ < ⊤ := hfin _ hcomp
end
