module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

namespace UpperTheory.V.Ws.Bl

private def blockAdjointFin2 (R : Type) [CommRing R] : Matrix (Fin 2) (Fin 2) R →ₗ[R] Matrix (Fin 2) (Fin 2) R where
  toFun Y := Matrix.of fun a b => (sgn (ixB a) * sgn (ixB b)) • Y b.rev a.rev
  map_add' X Y := by ext a b; simp only [Matrix.of_apply, Matrix.add_apply, smul_add]
  map_smul' c X := by
    ext a b
    simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
    rw [smul_comm]

private theorem adjoint_block_submatrix_eq {R : Type} [CommRing R] (X : M4 R) :
    blockAdjointFin2 R (X.submatrix ixA ixA) = (adj X).submatrix ixB ixB := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

private theorem adjoint_block_surjective {R : Type} [CommRing R] : Function.Surjective (blockAdjointFin2 R) := by
  intro Y
  refine ⟨blockAdjointFin2 R Y, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockAdjointFin2, ixB, sgn]

end UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.spanB :
    ∀ (R Γ : Type) [CommRing R] [Group Γ] (r : Γ →* M4 R), BG r → Submodule.span R (Set.range fun g => (r g).submatrix ixA ixA) = ⊤ → Submodule.span R (Set.range fun g => (r g).submatrix ixB ixB) = ⊤ := by
  intro R Γ _ _ r hr hA
  have hadj : ∀ g, (adj (r g)).submatrix ixB ixB ∈ Submodule.span R (Set.range fun g => (r g).submatrix ixB ixB) := by
    intro g
    obtain ⟨ν, hν⟩ := hr.gsp g
    have hinv : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [(grp R).2.2.2.2.2.2.1 ν _ _ hν hinv]
    have hs : (ν • r g⁻¹).submatrix ixB ixB = ν • (r g⁻¹).submatrix ixB ixB := rfl
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, rfl⟩)
  rw [eq_top_iff]
  calc (⊤ : Submodule R (Matrix (Fin 2) (Fin 2) R))
        = Submodule.map (blockAdjointFin2 R) ⊤ := by
          rw [Submodule.map_top, LinearMap.range_eq_top.mpr adjoint_block_surjective]
    _ = Submodule.map (blockAdjointFin2 R) (Submodule.span R (Set.range fun g => (r g).submatrix ixA ixA)) := by rw [hA]
    _ = Submodule.span R (blockAdjointFin2 R '' Set.range fun g => (r g).submatrix ixA ixA) := Submodule.map_span _ _
    _ ≤ _ := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      rw [adjoint_block_submatrix_eq]
      exact hadj g
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem ent_eq {R : Type} [CommRing R] {X Z : M4 R} (hX : IsBlock X) (hZ : Z ∈ hAB R) (i j : Fin 4)
    (h : ¬ lamW i < lamW j) : ((1 + Z) * X) i j = X i j := by
  have hZX : (Z * X) i j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : lamW i < lamW k
    · rw [hX k j (fun e => h (e ▸ hik)), mul_zero]
    · rw [hZ i k hik, zero_mul]
  rw [add_mul, one_mul, Matrix.add_apply, hZX, add_zero]

theorem UpperTheory.V.Ws.Bl.twistPt :
    ∀ (R : Type) [CommRing R] (X Z : M4 R), IsBlock X → Z ∈ uM R → (∀ ν Y, IsGSp ν Y → IsGSp ν ((1 + Z) * Y)) ∧ (∀ i j, lamW j < lamW i → ((1 + Z) * X) i j = 0) ∧
          ((1 + Z) * X).submatrix ixB ixB = X.submatrix ixB ixB ∧ ((1 + Z) * X).charpoly = X.charpoly := by
  intro R _ X Z hX hZ
  have hZa : Z ∈ hAB R := hZ.1
  have hZs : adj Z = -Z := hZ.2
  have hZZ : Z * Z = 0 := hAB_mul_hAB hZa hZa
  have hlow : ∀ i j, lamW j < lamW i → ((1 + Z) * X) i j = 0 := by
    intro i j hij
    rw [ent_eq hX hZa i j (fun h => lt_asymm h hij)]
    exact hX i j hij.ne'
  refine ⟨?_, hlow, ?_, ?_⟩
  · intro ν Y hY
    have g := grp R
    have h1 : (1 + -Z) * (1 + Z) = 1 := by
      rw [add_mul, one_mul, neg_mul, mul_add, mul_one, hZZ, add_zero]
      abel
    show adj ((1 + Z) * Y) * ((1 + Z) * Y) = ν • 1
    rw [g.1, g.2.2.1, g.2.2.2.2.1, hZs, mul_assoc, ← mul_assoc (1 + -Z), h1, one_mul]
    exact hY
  · ext a b
    exact ent_eq hX hZa _ _ (by fin_cases a <;> fin_cases b <;> decide)
  · have hT : ((1 + Z) * X).BlockTriangular lamW := fun _ _ h => hlow _ _ h
    have hTX : X.BlockTriangular lamW := fun _ _ h => hX _ _ h.ne'
    rw [hT.charpoly, hTX.charpoly]
    refine Finset.prod_congr rfl fun a _ => ?_
    congr 1
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    exact ent_eq hX hZa _ _ (by rw [i.2, j.2]; exact lt_irrefl a)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem UpperTheory.V.Ws.Bl.sup_mul_up {R : Type} [CommRing R] {N U : M4 R} (hN : IsSUp N) (hU : IsUp U) :
    IsSUp (N * U) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases e : k ≤ i
  · rw [hN i k e, zero_mul]
  · rw [hU k j (lt_of_le_of_lt h (not_le.mp e)), mul_zero]

theorem UpperTheory.V.Ws.Bl.twistFlag :
    ∀ (R : Type) [CommRing R] (X X' Z y u : M4 R), IsBlock X → IsBlock X' → X' * X = 1 → Z ∈ uM R → y ∈ uM R → IsGSp 1 u → IsUp (adj u * X * u) → IsSUp (adj u * (Z - (X * y * X' - y)) * u) →
          IsUp (adj ((1 - y) * u) * ((1 + Z) * X) * ((1 - y) * u)) ∧ ∀ i, (adj ((1 - y) * u) * ((1 + Z) * X) * ((1 - y) * u) : M4 R) i i = (adj u * X * u : M4 R) i i := by
  intro R _ X X' Z y u hX hX' hX'X hZM hyM hu hUp hS
  have g := grp R
  have hZ : Z ∈ hAB R := hZM.1
  have hy : y ∈ hAB R := hyM.1
  have hys : adj y = -y := hyM.2
  have hP : X * y * X' ∈ hAB R := hAB_mul_mul hX hy hX'
  have hyZ : y * Z = 0 := hAB_mul_hAB hy hZ
  have hyP : y * (X * y * X') = 0 := hAB_mul_hAB hy hP
  have hZP : Z * (X * y * X') = 0 := hAB_mul_hAB hZ hP
  have adjneg : ∀ W : M4 R, adj (-W) = -adj W := by
    intro W
    rw [← neg_one_smul R W, g.2.2.2.1, neg_one_smul]
  have huu : u * adj u = 1 := by
    have h : adj u * u = 1 := by
      have h0 : adj u * u = (1 : R) • 1 := hu
      rw [h0, one_smul]
    exact mul_eq_one_comm.mp h
  have e0 : (1 + y) * (1 + Z) = 1 + y + Z := by
    rw [add_mul, one_mul, mul_add, mul_one, hyZ, add_zero]
    abel
  have e1 : X * (1 + -y) = (1 - X * y * X') * X := by
    rw [sub_mul, one_mul, mul_assoc (X * y), hX'X, mul_one, mul_add, mul_one, mul_neg, sub_eq_add_neg]
  have e2 : (1 + y + Z) * (1 - X * y * X') = 1 + (Z - (X * y * X' - y)) := by
    rw [mul_sub, mul_one, add_mul, add_mul, one_mul, hyP, hZP]
    abel
  have hmid : (1 + y) * ((1 + Z) * X) * (1 + -y) = (1 + (Z - (X * y * X' - y))) * X := by
    calc (1 + y) * ((1 + Z) * X) * (1 + -y) = ((1 + y) * (1 + Z)) * (X * (1 + -y)) := by
          simp only [mul_assoc]
      _ = (1 + y + Z) * ((1 - X * y * X') * X) := by rw [e0, e1]
      _ = ((1 + y + Z) * (1 - X * y * X')) * X := (mul_assoc _ _ _).symm
      _ = (1 + (Z - (X * y * X' - y))) * X := by rw [e2]
  have key : adj ((1 - y) * u) * ((1 + Z) * X) * ((1 - y) * u)
      = adj u * X * u + (adj u * (Z - (X * y * X' - y)) * u) * (adj u * X * u) := by
    rw [show (1 : M4 R) - y = 1 + -y from sub_eq_add_neg 1 y, g.1, g.2.2.1, g.2.2.2.2.1, adjneg, hys, neg_neg]
    calc adj u * (1 + y) * ((1 + Z) * X) * ((1 + -y) * u)
          = adj u * ((1 + y) * ((1 + Z) * X) * (1 + -y)) * u := by simp only [mul_assoc]
      _ = adj u * ((1 + (Z - (X * y * X' - y))) * X) * u := by rw [hmid]
      _ = adj u * X * u + adj u * ((Z - (X * y * X' - y)) * X) * u := by
          rw [add_mul, one_mul, mul_add, add_mul]
      _ = adj u * X * u + (adj u * (Z - (X * y * X' - y)) * u) * (adj u * X * u) := by
          congr 1
          simp only [mul_assoc]
          rw [← mul_assoc u (adj u), huu, one_mul]
  rw [key]
  constructor
  · intro i j hji
    rw [Matrix.add_apply, hUp i j hji, sup_mul_up hS hUp i j hji.le, add_zero]
  · intro i
    rw [Matrix.add_apply, sup_mul_up hS hUp i i le_rfl, add_zero]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.cardP :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (P : Submodule A T), (∀ (a : A) (x : T), a ≠ 0 → a • x ∈ P → x ∈ P) → P ≠ ⊥ →
          ∀ n, Finite (T ⧸ lev A T n) ∧ n ≤ Nat.card (P.map (lev A T n).mkQ) := by
  intro A _ _ _ _ T _ _ _ _ P hsat hP n
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hm : maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hL : ∀ (k : ℕ) (z : T), z ∈ lev A T k ↔ ∃ t, ϖ ^ k • t = z := by
    intro k z
    show z ∈ maximalIdeal A ^ k • (⊤ : Submodule A T) ↔ _
    rw [hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hfin : ∀ k, Finite (T ⧸ lev A T k) := by
    intro k
    have h1 : (maximalIdeal A).FG := IsNoetherian.noetherian _
    haveI : Finite (A ⧸ maximalIdeal A) := (inferInstance : Finite (ResidueField A))
    haveI := Ideal.finite_quotient_pow h1 k
    haveI : Finite (T ⧸ (⊤ : Submodule A T)) := inferInstance
    exact Submodule.finite_quotient_smul _ (Module.finite_def.mp inferInstance)
  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hx : ∃ x ∈ P, x ∉ lev A T 1 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ k : ℕ, ∀ z ∈ P, z ∈ lev A T k := by
      intro k
      induction k with
      | zero =>
        intro z _
        exact (hL 0 z).mpr ⟨z, by simp⟩
      | succ k ih =>
        intro z hz
        obtain ⟨t, rfl⟩ := (hL 1 z).mp (hcon z hz)
        have htP : t ∈ P := hsat _ _ (pow_ne_zero 1 hϖ0) hz
        obtain ⟨s, rfl⟩ := (hL k t).mp (ih t htP)
        exact (hL (k + 1) _).mpr ⟨s, by rw [smul_smul, ← pow_add, add_comm 1 k]⟩
    have hmem : y ∈ (⨅ i : ℕ, maximalIdeal A ^ i • (⊤ : Submodule A T)) :=
      Submodule.mem_iInf _ |>.mpr (fun i => hall i y hyP)
    rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top] at hmem
    exact hy0 ((Submodule.mem_bot A).mp hmem)
  obtain ⟨x, hxP, hx1⟩ := hx
  refine ⟨hfin n, ?_⟩
  haveI := hfin n
  have key : ∀ i j : ℕ, i < j → j < n → ϖ ^ i • x - ϖ ^ j • x ∉ lev A T n := by
    intro i j hij hjn hmem
    obtain ⟨s, hs⟩ := (hL n _).mp hmem
    have e1 : ϖ ^ i • (ϖ ^ (n - i) • s) = ϖ ^ i • (x - ϖ ^ (j - i) • x) := by
      rw [smul_smul, ← pow_add, Nat.add_sub_cancel' (by omega), hs, smul_sub, smul_smul,
        ← pow_add, Nat.add_sub_cancel' hij.le]
    have e2 : ϖ ^ (n - i) • s = x - ϖ ^ (j - i) • x :=
      smul_right_injective T (pow_ne_zero i hϖ0) e1
    apply hx1
    rw [hL 1]
    refine ⟨ϖ ^ (n - i - 1) • s + ϖ ^ (j - i - 1) • x, ?_⟩
    rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add,
      Nat.add_sub_cancel' (by omega : 1 ≤ n - i), Nat.add_sub_cancel' (by omega : 1 ≤ j - i),
      e2, sub_add_cancel]
  let f : Fin n → P.map (lev A T n).mkQ := fun i =>
    ⟨(lev A T n).mkQ (ϖ ^ (i : ℕ) • x), Submodule.mem_map_of_mem (P.smul_mem _ hxP)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h' : (lev A T n).mkQ (ϖ ^ (i : ℕ) • x) = (lev A T n).mkQ (ϖ ^ (j : ℕ) • x) :=
      congrArg Subtype.val hij
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h'
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact absurd h' (key _ _ h j.2)
    · exact Fin.ext h
    · have h'' := (lev A T n).neg_mem h'
      rw [neg_sub] at h''
      exact absurd h'' (key _ _ h i.2)
  calc n = Nat.card (Fin n) := by simp
    _ ≤ _ := Nat.card_le_card_of_injective f hf
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem blk_one {R : Type} [CommRing R] : IsBlock (1 : M4 R) := fun i j h =>
  Matrix.one_apply_ne fun e => h (by rw [e])

private theorem key {R : Type} [CommRing R] {X Z Y : M4 R} (hX : IsBlock X) (hZ : Z ∈ hAB R) (hY : Y ∈ hAB R)
    (h : IsBlock ((1 - Y) * ((1 + Z) * X) * (1 + Y))) : Z * X + X * Y - Y * X = 0 := by
  have hZX : Z * X ∈ hAB R := by
    have h0 := hAB_mul_mul blk_one hZ hX
    rwa [one_mul] at h0
  have hXY : X * Y ∈ hAB R := by
    have h0 := hAB_mul_mul hX hY blk_one
    rwa [mul_one] at h0
  have hYX : Y * X ∈ hAB R := by
    have h0 := hAB_mul_mul blk_one hY hX
    rwa [one_mul] at h0
  have hN : Z * X + X * Y - Y * X ∈ hAB R := (hAB R).sub_mem ((hAB R).add_mem hZX hXY) hYX
  have h1 : ∀ W : M4 R, Y * (Z * W) = 0 := by
    intro W
    rw [← mul_assoc, hAB_mul_hAB hY hZ, zero_mul]
  have h2 : Y * (X * Y) = 0 := by rw [← mul_assoc, hAB_mul_hAB hYX hY]
  have h3 : Z * (X * Y) = 0 := by rw [← mul_assoc, hAB_mul_hAB hZX hY]
  have e : (1 - Y) * ((1 + Z) * X) * (1 + Y) = X + (Z * X + X * Y - Y * X) := by
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, mul_assoc, h1, h2, h3, zero_mul, mul_zero]
    abel
  ext i j
  rw [Matrix.zero_apply]
  by_cases hij : lamW i = lamW j
  · exact hN i j (by rw [hij]; exact lt_irrefl _)
  · have hb := h i j hij
    rw [e, Matrix.add_apply, hX i j hij, zero_add] at hb
    exact hb

theorem UpperTheory.V.Ws.Bl.noCompl :
    ∀ (R Γ : Type) [CommRing R] [Group Γ] (r : Γ →* M4 R) (z : Γ → M4 R) (c : Γ) (Y : M4 R), IsUnit (2 : R) → (∀ g, IsBlock (r g)) → (∀ g, z g ∈ hAB R) → r c = eAB R → z c = 0 → Y ∈ hAB R →
          (∀ g, IsBlock ((1 - Y) * ((1 + z g) * r g) * (1 + Y))) → ∀ g, z g = 0 := by
  intro R Γ _ _ r z c Y h2u hrb hz hrc hzc hY hB g
  have hc := key (hrb c) (hz c) hY (hB c)
  rw [hzc, hrc, zero_mul, zero_add] at hc
  have hY0 : Y = 0 := by
    ext i j
    by_cases hij : lamW i < lamW j
    · have hd : (![-1, 1, -1, 1] : Fin 4 → R) i = 1 ∧ (![-1, 1, -1, 1] : Fin 4 → R) j = -1 := by
        fin_cases i <;> fin_cases j <;> simp [lamW] at hij ⊢
      have h2 : (2 : R) * Y i j = 0 := by
        have h0 := congrFun (congrFun hc i) j
        simp only [eAB, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply] at h0
        rw [hd.1, hd.2] at h0
        linear_combination h0
      exact h2u.mul_right_eq_zero.mp h2
    · exact hY i j hij
  have hg := key (hrb g) (hz g) hY (hB g)
  rw [hY0, mul_zero, zero_mul, sub_zero, add_zero] at hg
  calc z g = z g * (r g * r g⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = 0 := by rw [← mul_assoc, hg, zero_mul]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private def uMat {R : Type} [CommRing R] (v : Fin 3 → R) : UpperTheory.V.GradeZeroInterpolatingElement.M4 R :=
  !![0, 0, 0, 0; v 0, 0, v 1, 0; 0, 0, 0, 0; v 2, 0, -v 0, 0]

private theorem uMat_mem {R : Type} [CommRing R] (v : Fin 3 → R) : uMat v ∈ uM R := by
  show uMat v ∈ hAB R ⊓ sp4 R
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · show ∀ i j, ¬ lamW i < lamW j → uMat v i j = 0
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [uMat, lamW]
  · show adj (uMat v) = -uMat v
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, uMat, Fin.rev]

private theorem uMat_eq {R : Type} [CommRing R] (Y : uM R) : uMat ![Y.1 1 0, Y.1 1 2, Y.1 3 0] = Y.1 := by
  obtain ⟨Y, hY⟩ := Y
  have hA := (Submodule.mem_inf.mp hY).1
  have hS := (Submodule.mem_inf.mp hY).2
  change ∀ i j, ¬ lamW i < lamW j → Y i j = 0 at hA
  change adj Y = -Y at hS
  have h32 := congrFun (congrFun hS 3) 2
  simp [adj_apply, sgn, Fin.rev] at h32
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat] <;> first
    | exact (hA _ _ (by decide)).symm
    | (rw [h32]; ring)
    | skip

private theorem uMat_add {R : Type} [CommRing R] (v w : Fin 3 → R) : uMat (v + w) = uMat v + uMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat] <;> ring

private theorem uMat_smul {R : Type} [CommRing R] (c : R) (v : Fin 3 → R) : uMat (c • v) = c • uMat v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

private def uEq (R : Type) [CommRing R] : (Fin 3 → R) ≃ₗ[R] uM R where
  toFun v := ⟨uMat v, uMat_mem v⟩
  map_add' v w := Subtype.ext (uMat_add v w)
  map_smul' c v := Subtype.ext (uMat_smul c v)
  invFun Y := ![Y.1 1 0, Y.1 1 2, Y.1 3 0]
  left_inv v := by
    ext i
    fin_cases i <;> rfl
  right_inv Y := Subtype.ext (uMat_eq Y)

theorem UpperTheory.V.Ws.Bl.uMFacts :
    ∀ (R : Type) [CommRing R], Module.Finite R (uM R) ∧ Module.Free R (uM R) ∧ ∀ (I : Ideal R) (Y : uM R), Y ∈ (I • ⊤ : Submodule R (uM R)) ↔ ∀ i j, Y.1 i j ∈ I := by
  intro R _
  refine ⟨Module.Finite.equiv (uEq R), Module.Free.of_equiv (uEq R), ?_⟩
  intro I Y
  constructor
  · intro hY i j
    refine Submodule.smul_induction_on hY ?_ ?_
    · intro r hr n _
      simpa using I.mul_mem_right (n.1 i j) hr
    · intro x y hx hy
      simpa using I.add_mem hx hy
  · intro h
    have hv : (uEq R).symm Y = ∑ k : Fin 3, ((uEq R).symm Y k) • Pi.single k 1 := by
      simpa using ((Pi.basisFun R (Fin 3)).sum_repr ((uEq R).symm Y)).symm
    have hY : Y = ∑ k : Fin 3, ((uEq R).symm Y k) • (uEq R) (Pi.single k 1) := by
      calc Y = uEq R ((uEq R).symm Y) := ((uEq R).apply_symm_apply Y).symm
        _ = _ := by
          conv_lhs => rw [hv]

          rw [map_sum]
          simp only [map_smul]
    rw [hY]
    refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem_smul ?_ Submodule.mem_top)
    fin_cases k
    · exact h 1 0
    · exact h 1 2
    · exact h 3 0
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.redMem :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T) (n : ℕ) z y, IsZn ρ c N H P (n + 1) z y → IsZn ρ c N H P n (fun g => redn A T n (z g)) (redn A T n y) ∧
          (Prim z → 0 < n → Prim fun g => redn A T n (z g)) ∧ (Prim (fun g => redn A T n (z g)) → Prim z) := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P n z y hz
  have eqv : ∀ (g : Γ) (w : T ⧸ lev A T (n + 1)),
      redn A T n (modRep ρ (n + 1) g w) = modRep ρ n g (redn A T n w) := by
    intro g w
    obtain ⟨x, rfl⟩ := (lev A T (n + 1)).mkQ_surjective w
    rw [modRep_mk, redn_mk, redn_mk, modRep_mk]
  have img : ∀ (Q : Submodule A T) (w : T ⧸ lev A T (n + 1)), w ∈ Q.map (lev A T (n + 1)).mkQ →
      redn A T n w ∈ Q.map (lev A T n).mkQ := by
    rintro Q _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  refine ⟨⟨hz.lc.comp (redn A T n), fun g h => ?_, ?_, fun g hg => ?_, fun h hh => ?_⟩, ?_, ?_⟩
  · rw [hz.coc, map_add (f := _), eqv]
  · rw [hz.cz, map_zero]
  · rw [hz.kill g hg, map_zero]
  · have := img P _ (hz.loc h hh)
    rw [map_sub, map_sub, eqv] at this
    exact this
  · rintro ⟨g, hg⟩ hn
    refine ⟨g, fun hm => hg ?_⟩
    obtain ⟨x, hx⟩ := (lev A T (n + 1)).mkQ_surjective (z g)
    obtain ⟨x', hx', e⟩ := hm
    have e' : (lev A T n).mkQ x' = (lev A T n).mkQ x := by rw [e, ← redn_mk, hx]
    have hd : x' - x ∈ lev A T n := (Submodule.Quotient.eq _).1 e'
    have hle : lev A T n ≤ lev A T 1 := Submodule.smul_mono_left (Ideal.pow_le_pow_right hn)
    refine ⟨x, ?_, hx⟩
    have := (lev A T 1).sub_mem hx' (hle hd)
    rwa [sub_sub_cancel] at this
  · rintro ⟨g, hg⟩
    exact ⟨g, fun hm => hg (img _ _ hm)⟩
end
