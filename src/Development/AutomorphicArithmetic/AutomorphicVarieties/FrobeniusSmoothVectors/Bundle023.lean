module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle020
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle038
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContMap
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

open MvPowerSeries in
private theorem ev_decomp {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O) :
    ∃ h : σ → MvPowerSeries σ O, f = C (constantCoeff f) + ∑ i, MvPowerSeries.X i * h i ∧
      ∀ i, constantCoeff (h i) = coeff (Finsupp.single i 1) f :=
  _root_.UpperTheory.Reformulated.B.Qf39.ev_decomp f

private theorem ev_max {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R]
    [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {x : R} :
    f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem ev_sg_map {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    (f : A →ₐ[O] B) (j : ZMod 2) : f (sg A j) = sg B j := by
  simp [sg]

private theorem ev_sg_sq (A : Type) [CommRing A] (j : ZMod 2) : sg A j * sg A j = 1 := by
  rw [sg, ← mul_pow]; simp

theorem UpperTheory.V.Fr.ep_vars :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∃ (a g : ℕ) (p : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R), Function.Surjective p ∧ (∀ s, p (MvPowerSeries.X s) ∈ maximalIdeal R) ∧ (∀ j, (wtPart O (Space.Loc.par a g) j).map p.toLinearMap = evp σ j) ∧ IsHomog O (Space.Loc.par a g) (RingHom.ker p) ∧ ∀ h ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) h ∈ maximalIdeal O := by
  intro O _ _ _ _ h2 R _ _ _ σ hσ
  have h2R : IsUnit (2 : R) := by
    have := h2.map (algebraMap O R)
    rwa [map_ofNat] at this
  obtain ⟨a, g, z, hz, hspan, hind⟩ := ep_basis O h2 R σ hσ (maximalIdeal R)
    ((maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2) (fun y hy => (ev_max σ).2 hy)
    (by
      have : (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 ≤
          ((maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2).comap σ := by
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap]
          intro c hc
          rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
          exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc)
        · refine le_trans ?_ (Ideal.comap_mono le_sup_right)
          refine le_trans (Ideal.pow_right_mono ?_ 2) (Ideal.le_comap_pow σ 2)
          exact fun y hy => (ev_max σ).2 hy
      exact fun y hy => this hy)
    (by rw [← pow_two]; exact le_sup_right)
  obtain ⟨τ, -, hτe, hτw⟩ := ep_ps O h2 (Fin a ⊕ Fin g) (Space.Loc.par a g)
  haveI := co_mvps O O (Fin a ⊕ Fin g)
  obtain ⟨p, ⟨-, hpX⟩, -⟩ := co_ev O O R (Fin a ⊕ Fin g) (Algebra.ofId O R) z fun s => (hz s).1
  have hC : ∀ (H : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R) (x : O),
      H (MvPowerSeries.C x) = Algebra.ofId O R x := fun H x => by
    have := H.commutes x
    rw [MvPowerSeries.algebraMap_apply] at this
    exact this
  have hsurj : Function.Surjective p := by
    refine co_surj O _ R p (hspan.trans (sup_le (le_sup_of_le_left ?_) (sup_le_sup_right ?_ _)))
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      rw [← hpX]
      refine Ideal.mem_map_of_mem p ((ev_max p).1 ?_)
      rw [hpX]
      exact (hz s).1
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, ← p.commutes]
      refine Ideal.mem_map_of_mem p ?_
      exact (ev_max (Algebra.ofId O _)).2 hc
  have heq : p.comp τ = σ.comp p := by
    refine (co_ev O O R (Fin a ⊕ Fin g) (Algebra.ofId O R) (fun s => σ (z s))
      fun s => (ev_max σ).2 (hz s).1).unique ⟨hC _, fun s => ?_⟩ ⟨hC _, fun s => ?_⟩
    · have h1 : (MvPowerSeries.X s : MvPowerSeries (Fin a ⊕ Fin g) O) ∈ evp τ (Space.Loc.par a g s) := by
        rw [hτe]; exact X_mem_wtPart O _ s
      have h3 : τ (MvPowerSeries.X s) = _ := h1
      have h4 : σ (z s) = _ := (hz s).2
      rw [AlgHom.comp_apply, h3, h4, map_mul, ev_sg_map, hpX]
    · rw [AlgHom.comp_apply, hpX]
  have heq' : ∀ y, p (τ y) = σ (p y) := fun y => DFunLike.congr_fun heq y
  have hw : ∀ j y, 2 * p (wcomp O (Space.Loc.par a g) j y) = p y + sg R j * σ (p y) := fun j y => by
    have := congrArg p (hτw j y)
    rwa [map_mul, map_ofNat, map_add, map_mul, ev_sg_map, heq'] at this
  refine ⟨a, g, p, hsurj, fun s => by rw [hpX]; exact (hz s).1, fun j => le_antisymm ?_ fun x hx => ?_,
    fun f hf j => ?_, fun h hh => ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    have h1 : f ∈ evp τ j := by rw [hτe]; exact hf
    have h3 : τ f = _ := h1
    show σ (p f) = sg R j * p f
    rw [← heq', h3, map_mul, ev_sg_map]
  · obtain ⟨y, rfl⟩ := hsurj x
    have h1 : σ (p y) = _ := hx
    refine ⟨_, wcomp_mem O _ j y, ?_⟩
    show p _ = p y
    refine h2R.mul_left_cancel ?_
    rw [hw, h1, ← mul_assoc, ev_sg_sq, one_mul, two_mul]
  · have h1 : p f = 0 := hf
    show p _ = 0
    refine h2R.mul_left_cancel ?_
    rw [hw, h1]
    simp
  · obtain ⟨u, hu, hu0⟩ := ev_decomp h
    have h0 : p h = 0 := hh
    have h1 : algebraMap O R (MvPowerSeries.constantCoeff h) + ∑ i, z i * p (u i) = 0 := by

      rw [hu, map_add (f := _), map_sum, hC] at h0
      simp only [map_mul, hpX] at h0
      exact h0
    have h3 : MvPowerSeries.constantCoeff h ∈ maximalIdeal O := by
      rw [← ev_max (Algebra.ofId O R)]
      show algebraMap O R _ ∈ _
      rw [eq_neg_of_add_eq_zero_left h1]
      exact neg_mem (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hz i).1)
    refine hind (fun s => MvPowerSeries.coeff (Finsupp.single s 1) h) ?_
    have h4 : ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) h • z s =
        -algebraMap O R (MvPowerSeries.constantCoeff h) +
          ∑ s, z s * p (MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single s 1) h) - u s) := by
      rw [eq_neg_of_add_eq_zero_left h1, neg_neg, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_sub, hC, Algebra.smul_def, Algebra.ofId_apply]
      ring
    rw [h4]
    refine Submodule.add_mem_sup (neg_mem (Ideal.mem_map_of_mem _ h3)) (Ideal.sum_mem _ fun s _ => ?_)
    rw [pow_two]
    refine Ideal.mul_mem_mul (hz s).1 ((ev_max p).2 fun hU => ?_)
    have h5 := MvPowerSeries.isUnit_constantCoeff _ hU
    rw [map_sub, hu0, MvPowerSeries.constantCoeff_C, sub_self] at h5
    exact not_isUnit_zero h5
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem db_inv {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (a b : Fin 3) (e : π a ≠ pq b) :
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) b a = 0 := by
  set u : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hu
  have h1 : u * g = 1 := g.inv_mul
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) * u = 1 := g.mul_inv
  let P : Matrix (Fin 3) (Fin 3) K := diagonal fun i => if π i = π a then 1 else 0
  let Q : Matrix (Fin 3) (Fin 3) K := diagonal fun i => if pq i = π a then 1 else 0
  have hc : P * g = g * Q := by
    ext i j
    simp only [P, Q, diagonal_mul, mul_diagonal]
    by_cases c : π i = pq j
    · rw [c, mul_comm]
    · rw [h i j c, mul_zero, zero_mul]
  have hd : u * P = Q * u := by
    calc u * P = u * (P * g) * u := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = Q * u := by rw [hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have := congrFun (congrFun hd b) a
  simpa [P, Q, diagonal_mul, mul_diagonal, e.symm] using this

private theorem db_ex {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (b : Fin 3) : ∃ a, π a = pq b := by
  by_contra c
  push Not at c
  have h1 : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g = 1 := g.inv_mul
  have := congrFun (congrFun h1 b) b
  rw [Matrix.mul_apply, Finset.sum_eq_zero fun a _ => by rw [h a b (c a), mul_zero]] at this
  simp at this

private theorem db_card {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (j : ZMod 2) :
    Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = j} ≤
      Module.finrank K ((bor g).comap (adp K j).subtype) := by
  have h' := db_inv g π h
  set u : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hu
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) * u = 1 := g.mul_inv
  have hc : ∀ X : Matrix (Fin 3) (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K) * (u * X * g) * u = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  let f : {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = j} → (bor g).comap (adp K j).subtype := fun p =>
    ⟨⟨u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K), fun a b e => by
      have : (u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K)) a b =
          u a p.1.1 * (g : Matrix (Fin 3) (Fin 3) K) p.1.2 b := by
        rw [Matrix.mul_apply, Finset.sum_eq_single p.1.2]
        · simp
        · intro c _ hc
          rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, zero_mul]
        · simp
      rw [this]
      by_cases c : π p.1.1 = pq a
      · rw [h p.1.2 b fun c' => e (by rw [pw_eq, ← c, ← c', p.2.2]), mul_zero]
      · rw [h' _ _ c, zero_mul]⟩, by
      show UpT ((g : Matrix (Fin 3) (Fin 3) K) * (u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K)) * u)
      rw [hc]
      intro a b e
      refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
      rintro ⟨rfl, rfl⟩
      exact absurd p.2.1 (not_le.2 e)⟩
  refine LinearIndependent.fintype_card_le_finrank (b := f) ?_
  let L : (bor g).comap (adp K j).subtype →ₗ[K] Matrix (Fin 3) (Fin 3) K :=
    (LinearMap.mulRight K u) ∘ₗ (LinearMap.mulLeft K (g : Matrix (Fin 3) (Fin 3) K)) ∘ₗ (adp K j).subtype ∘ₗ
      Submodule.subtype _
  refine LinearIndependent.of_comp L ?_
  have : L ∘ f = (Matrix.stdBasis K (Fin 3) (Fin 3)) ∘ Subtype.val := by
    funext p
    have := Matrix.stdBasis_eq_single (R := K) p.1.1 p.1.2
    exact (hc _).trans this.symm
  rw [this]
  exact (Matrix.stdBasis K (Fin 3) (Fin 3)).linearIndependent.comp _ Subtype.val_injective

private theorem db_counts : ∀ π : Fin 3 → ZMod 2, (∃ a, π a = 0) → (∃ a, π a = 1) →
    4 ≤ Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = 0} ∧
    2 ≤ Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = 1} := by
  decide +kernel

theorem UpperTheory.V.Fr.ep_dimb :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), ∀ v, 4 ≤ Module.finrank K (B.bp 0 v) ∧ 2 ≤ Module.finrank K (B.bp 1 v) := by
  intro l _ k _ F K _ _ B π h v
  have h0 : pq 1 = 0 := by decide
  have h1 : pq 0 = 1 := by decide
  obtain ⟨c0, c1⟩ := db_counts (π v) (h0 ▸ db_ex (B.g v) (π v) (h.g v) 1) (h1 ▸ db_ex (B.g v) (π v) (h.g v) 0)
  exact ⟨c0.trans (db_card (B.g v) (π v) (h.g v) 0), c1.trans (db_card (B.g v) (π v) (h.g v) 1)⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_add (K : Type) [CommRing K] (i j : ZMod 2) : sg K (i + j) = sg K i * sg K j := by
  simp only [sg, ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

private theorem sg_sub (K : Type) [CommRing K] (i j : ZMod 2) : sg K (i - j) = sg K i * sg K j := by
  have h : i - j = i + j := by revert i j; decide
  rw [h, sg_add]

private theorem sg_sq (K : Type) [CommRing K] (i : ZMod 2) : sg K i * sg K i = 1 := by
  have h : i + i = 0 := by revert i; decide
  rw [← sg_add, h]
  simp [sg]

private theorem sg_ne (K : Type) [CommRing K] (i j : ZMod 2) (e : i ≠ j) : sg K i * sg K j = -1 := by
  have h : i + j = 1 := by revert i j; decide
  rw [← sg_add, h]
  show (-1 : K) ^ (1 : ZMod 2).val = -1
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

private theorem lin_sg {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup K] [Module O K]
    (D : R →ₗ[O] K) (i : ZMod 2) (x : R) : D (sg R i * x) = sg ℤ i • D x := by
  have h : i = 0 ∨ i = 1 := by revert i; decide
  rcases h with rfl | rfl
  · simp [sg]
  · show D ((-1 : R) ^ (1 : ZMod 2).val * x) = (-1 : ℤ) ^ (1 : ZMod 2).val • D x
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, pow_one, neg_one_mul, map_neg, neg_one_zsmul]

private theorem gl_inv_apply_eq_zero_of_forall_pw_ne_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (G : GL (Fin 3) K)
    (hG : ∀ a b, pw a b ≠ 0 → (G : Matrix (Fin 3) (Fin 3) K) a b = 0) :
    ∀ a b, pw a b ≠ 0 → ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
  set E : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal (fun a => sg K (pq a)) with hE
  have hEE : E * E = 1 := by
    rw [hE, Matrix.diagonal_mul_diagonal]
    simp only [sg_sq]
    exact Matrix.diagonal_one
  have hconj : ∀ (A : Matrix (Fin 3) (Fin 3) K) a b, (E * A * E) a b = sg K (pw a b) * A a b := by
    intro A a b
    rw [hE, Matrix.mul_diagonal, Matrix.diagonal_mul, pw_eq, sg_sub]
    ring
  have hEG : E * (G : Matrix (Fin 3) (Fin 3) K) * E = G := by
    ext a b
    rw [hconj]
    by_cases h : pw a b = 0
    · rw [h]
      simp [sg]
    · rw [hG a b h, mul_zero]
  have hinv1 : (G : Matrix (Fin 3) (Fin 3) K) * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv2 : ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (G : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E = ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h1 : (G : Matrix (Fin 3) (Fin 3) K) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E) = 1 := by
      calc (G : Matrix (Fin 3) (Fin 3) K) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E)
          = (E * (G : Matrix (Fin 3) (Fin 3) K) * E) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E) := by
            rw [hEG]
        _ = E * ((G : Matrix (Fin 3) (Fin 3) K) * ((E * E) * (((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E))) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [hEE, Matrix.one_mul, ← Matrix.mul_assoc (G : Matrix (Fin 3) (Fin 3) K), hinv1, Matrix.one_mul, hEE]
    calc E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E
        = (((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * G) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E) := by
          rw [hinv2, Matrix.one_mul]
      _ = ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((G : Matrix (Fin 3) (Fin 3) K) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E)) := by
          rw [Matrix.mul_assoc]
      _ = ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [h1, Matrix.mul_one]
  intro a b hab
  have e := congrFun (congrFun key a) b
  rw [hconj] at e
  have hp : pw a b = 1 := by
    revert hab
    generalize pw a b = p
    revert p
    decide
  have s1 : sg K 1 = -1 := by
    show (-1 : K) ^ (1 : ZMod 2).val = -1
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]
  rw [hp, s1] at e
  have e' : (2 : K) * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
    linear_combination -e
  exact (mul_eq_zero.mp e').resolve_left h2

theorem UpperTheory.V.Fr.ep_dproj :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), B.Gr σ π → ∀ j, ∀ D ∈ Tan O R, ∃ D' ∈ derp O σ j, ∀ s, B.tanCo O D' s = prp (ResidueField O) j (B.tanCo O D s) := by
  intro l _ k _ F O _ _ h2 R _ _ _ σ hσ B π hB j D hD
  have h2k : (2 : ResidueField O) ≠ 0 := by
    have := h2.map (residue O)
    rw [map_ofNat] at this
    exact this.ne_zero
  have zs : ∀ (p : ZMod 2) (v : ResidueField O), sg ℤ p • v = sg (ResidueField O) p * v := by
    intro p v
    rw [zsmul_eq_mul]
    simp [sg]
  let D' : R →ₗ[O] ResidueField O :=
    (2 : ResidueField O)⁻¹ • (D + sg (ResidueField O) j • D.comp σ.toLinearMap)
  have hD' : ∀ x, D' x = (2 : ResidueField O)⁻¹ * (D x + sg (ResidueField O) j * D (σ x)) := by
    intro x
    simp [D', smul_eq_mul, mul_add]
  refine ⟨D', Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · intro f g
    have e1 := hD f g
    have e2 := hD (σ f) (σ g)
    rw [res_map, res_map] at e2
    rw [hD', hD', hD', map_mul σ f g, e1, e2]
    simp only [smul_eq_mul]
    ring
  · intro x
    show D' (σ x) = sg (ResidueField O) j * D' x
    rw [hD', hD', hσ]
    linear_combination (-(2 : ResidueField O)⁻¹ * D (σ x)) * sg_sq (ResidueField O) j
  · intro s
    have hM : ∀ a c, σ ((B.r s).mat a c) = sg R (pw a c) * (B.r s).mat a c := by
      intro a c
      rw [pw_eq]
      exact hB.r s a c
    have hDp : ∀ a c, D' ((B.r s).mat a c) = if pw a c = j then D ((B.r s).mat a c) else 0 := by
      intro a c
      rw [hD', hM, lin_sg, zs]
      split_ifs with hp
      · rw [hp]
        field_simp
        linear_combination D ((B.r s).mat a c) * sg_sq (ResidueField O) j
      · rw [← mul_assoc, sg_ne _ _ _ (Ne.symm hp)]
        ring
    have hbar : ∀ a c, pw a c ≠ 0 →
        (((Box.bar O B).r s).left : Matrix (Fin 3) (Fin 3) (ResidueField O)) a c = 0 := by
      intro a c hac
      show res O R ((B.r s).mat a c) = 0
      have hp : pw a c = 1 := by
        revert hac
        generalize pw a c = p
        revert p
        decide
      have e := congrArg (res O R) (hM a c)
      rw [res_map, hp, map_mul] at e
      have s1R : sg R 1 = -1 := by
        show (-1 : R) ^ (1 : ZMod 2).val = -1
        rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]
      rw [s1R, map_neg, map_one] at e
      have e' : (2 : ResidueField O) * res O R ((B.r s).mat a c) = 0 := by
        linear_combination e
      exact (mul_eq_zero.mp e').resolve_left h2k
    have hN := gl_inv_apply_eq_zero_of_forall_pw_ne_zero h2k ((Box.bar O B).r s).left hbar
    ext a b
    show ((B.r s).mat.map D' * (((Box.bar O B).r s).left⁻¹ : GL (Fin 3) (ResidueField O))) a b =
      if pw a b = j then ((B.r s).mat.map D * (((Box.bar O B).r s).left⁻¹ : GL (Fin 3) (ResidueField O))) a b else 0
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have hsame : ∀ c, pw c b = 0 → pw a c = pw a b := by
      intro c hcb
      rw [pw_eq] at hcb
      rw [pw_eq, pw_eq, sub_eq_zero.mp hcb]
    split_ifs with hab
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Matrix.map_apply, Matrix.map_apply, hDp]
      by_cases hcb : pw c b = 0
      · rw [if_pos ((hsame c hcb).trans hab)]
      · rw [hN c b hcb, mul_zero, mul_zero]
    · refine Finset.sum_eq_zero (fun c _ => ?_)
      rw [Matrix.map_apply, hDp]
      by_cases hcb : pw c b = 0
      · rw [if_neg (fun h => hab ((hsame c hcb).symm.trans h)), zero_mul]
      · rw [hN c b hcb, mul_zero]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.co_B :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∃ h : IsCO O S.B, @maximalIdeal _ _ h.toIsLocalRing = S.mB := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, -, hB, -, -⟩ := UpperTheory.V.Fr.wpres hF hn S
  haveI h0 : IsCO O (W.gr 0) := UpperTheory.V.Alg.wPres_gr_zero_isCO_of_mem_maximalIdeal O ℤ S.R W hz
  let p : W.gr 0 →ₐ[O] S.B :=
    { toFun := fun b => ⟨((b : W.A) : S.R), (hB _).2 b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hp : Function.Surjective p := fun y =>
    ⟨⟨⟨y.1, W.part_le_A ((hB _).1 y.2)⟩, (hB _).1 y.2⟩, rfl⟩
  haveI h : IsCO O S.B := UpperTheory.V.Alg.co_quot O (W.gr 0) S.B p hp
  refine ⟨h, ?_⟩
  ext b
  show _ ↔ S.B.val b ∈ maximalIdeal S.R
  rw [← res_eq_zero_iff O, ← res_eq_zero_iff O, res_map]
end
