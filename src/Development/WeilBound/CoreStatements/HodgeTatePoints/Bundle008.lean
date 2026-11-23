module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Span
public import ReciprocityTheory.DualLattices.Bundle007
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle004
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.BigOperators
public import ReciprocityTheory.DualLattices.IsLocalOfIntegers
public import ReciprocityTheory.DualLattices.Bundle013
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import ReciprocityTheory.DualLattices.UpSmith

@[expose] public section

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace PositivityTheory.HtPt.Gf

theorem minor_mul_upper {B : Type} [CommRing B] {N i : ℕ} (hi : i ≤ N) (g U : Matrix (Fin N) (Fin N) B)
    (J : Fin i → Fin N) (hU : ∀ a b, b < a → U a b = 0) :
    ((g * U).submatrix J (Fin.castLE hi)).det =
      (g.submatrix J (Fin.castLE hi)).det * ∏ l : Fin i, U (Fin.castLE hi l) (Fin.castLE hi l) := by
  have h : (g * U).submatrix J (Fin.castLE hi) =
      g.submatrix J (Fin.castLE hi) * U.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin i)).map (Fin.castLEEmb hi))) ?_,
      Finset.sum_map]
    · rfl
    · intro k _ hk
      have hki : i ≤ (k : ℕ) := by
        by_contra hlt
        push_neg at hlt
        exact hk (Finset.mem_map.2 ⟨⟨k, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      have hlt : Fin.castLE hi b < k := by
        rw [Fin.lt_def, Fin.coe_castLE]
        omega
      rw [hU k (Fin.castLE hi b) hlt, mul_zero]
  have hT : (U.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsUpperTriangular := by
    intro a b hab
    have hab' : Fin.castLE hi b < Fin.castLE hi a := by
      rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
      exact hab
    exact hU _ _ hab'
  rw [h, Matrix.det_mul, Matrix.det_of_upperTriangular hT]
  rfl

private theorem cb_lemma {B : Type} [CommRing B] {i N : ℕ} (A : Matrix (Fin i) (Fin N) B)
    (C : Matrix (Fin N) (Fin i) B) :
    (A * C).det = ∑ p : Fin i → Fin N, (∏ a, A a (p a)) * (C.submatrix p id).det := by
  have key : ∀ p : Fin i → Fin N, (C.submatrix p id).det =
      ∑ σ : Equiv.Perm (Fin i), Equiv.Perm.sign σ • ∏ a, C (p a) (σ a) := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  simp_rw [key]
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.smul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_smul_comm]

private theorem matAct_of_span_residue_spans {B : Type} [CommRing B] {N i : ℕ} (hi : i ≤ N) (g : Matrix (Fin N) (Fin N) B)
    (hg : IsUnit g.det) :
    Ideal.span (Set.range fun J : Fin i → Fin N => (g.submatrix J (Fin.castLE hi)).det) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : g⁻¹.submatrix (Fin.castLE hi) id * g.submatrix id (Fin.castLE hi) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul g hg]
    exact Matrix.submatrix_one _ (Fin.castLE_injective hi)
  have h2 := cb_lemma (g⁻¹.submatrix (Fin.castLE hi) id) (g.submatrix id (Fin.castLE hi))
  rw [h1, Matrix.det_one] at h2
  rw [h2]
  exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, rfl⟩)

theorem lead_minor : ∀ (B : Type) [CommRing B] (N i : ℕ) (hi : i ≤ N), (∀ (g U : Matrix (Fin N) (Fin N) B) (J : Fin i → Fin N), (∀ a b, b < a → U a b = 0) → ((g * U).submatrix J (Fin.castLE hi)).det = (g.submatrix J (Fin.castLE hi)).det * ∏ l : Fin i, U (Fin.castLE hi l) (Fin.castLE hi l)) ∧ ∀ g : Matrix (Fin N) (Fin N) B, IsUnit g.det → Ideal.span (Set.range fun J : Fin i → Fin N => (g.submatrix J (Fin.castLE hi)).det) = ⊤ := by
  intro B _ N i hi
  exact ⟨fun g U J hU => minor_mul_upper hi g U J hU, fun g hg => matAct_of_span_residue_spans hi g hg⟩

theorem abel_nat (lam x : ℕ → ℝ) (n : ℕ) (hl : ∀ i, i + 1 ≤ n → lam (i + 1) ≤ lam i)
    (hx : ∀ i, i ≤ n → 0 ≤ ∑ l ∈ Finset.range i, x l) :
    lam n * ∑ l ∈ Finset.range (n + 1), x l ≤ ∑ l ∈ Finset.range (n + 1), lam l * x l := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hl j (by omega)) (fun j hj => hx j (by omega))
    have hs := hx (n + 1) le_rfl
    have hln := hl n le_rfl
    rw [Finset.sum_range_succ x (n + 1), Finset.sum_range_succ (fun l => lam l * x l) (n + 1)]
    nlinarith [mul_nonneg (sub_nonneg.2 hln) hs]

theorem abel_sum : ∀ (N : ℕ) (lam x : Fin N → ℝ), (∀ i j, i ≤ j → lam j ≤ lam i) → (∀ i : ℕ, i ≤ N → 0 ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin N => (l : ℕ) < i), x l) → ∑ l, x l = 0 → 0 ≤ ∑ l, lam l * x l := by
  intro N lam x hl hx hsum
  cases N with
  | zero => simp
  | succ n =>
    obtain ⟨x', hx'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = x l :=
      ⟨fun k => if h : k < n + 1 then x ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩
    obtain ⟨lam', hlam'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = lam l :=
      ⟨fun k => if h : k < n + 1 then lam ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩
    have hsx : ∀ i, i ≤ n + 1 → ∑ l ∈ Finset.range i, x' l =
        ∑ l ∈ Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < i), x l := by
      intro i hi
      have e : ∀ l : Fin (n + 1), (if (l : ℕ) < i then x l else 0) =
          (fun k => if k < i then x' k else 0) (l : ℕ) := by
        intro l
        simp only [hx']
      rw [Finset.sum_filter, Finset.sum_congr rfl (fun l _ => e l),
        Fin.sum_univ_eq_sum_range (fun k => if k < i then x' k else 0), ← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    have htot : ∑ l ∈ Finset.range (n + 1), x' l = 0 := by
      rw [← Fin.sum_univ_eq_sum_range x' (n + 1)]
      simp only [hx']
      exact hsum
    have hprod : ∑ l ∈ Finset.range (n + 1), lam' l * x' l = ∑ l, lam l * x l := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => lam' k * x' k) (n + 1)]
      simp only [hx', hlam']
    have hl' : ∀ i, i + 1 ≤ n → lam' (i + 1) ≤ lam' i := by
      intro i hi
      have h1 := hlam' ⟨i + 1, by omega⟩
      have h2 := hlam' ⟨i, by omega⟩
      simp only at h1 h2
      rw [h1, h2]
      exact hl _ _ (Fin.mk_le_mk.2 (by omega))
    have hx'' : ∀ i, i ≤ n → 0 ≤ ∑ l ∈ Finset.range i, x' l := by
      intro i hi
      rw [hsx i (by omega)]
      exact hx i (by omega)
    have key := abel_nat lam' x' n hl' hx''
    rw [htot, hprod, mul_zero] at key
    exact key

end PositivityTheory.HtPt.Gf
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

theorem det_updateRow_diagonal {R : Type} [CommRing R] {m : ℕ} (c r : Fin m → R) (i : Fin m) :
    ((Matrix.diagonal c).updateRow i r).det = (∏ j ∈ Finset.univ.erase i, c j) * r i := by
  rw [← Matrix.cramer_transpose_apply, Matrix.diagonal_transpose, Matrix.cramer_eq_adjugate_mulVec,
    Matrix.adjugate_diagonal, Matrix.mulVec_diagonal]

theorem len_eq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (ι : Type) [Fintype ι] (L L' : Submodule R (ι → R)), L ≤ L' → ∀ x y : NNReal, x ≠ 0 → HasLen v R ((ι → R) ⧸ L) x → HasLen v R ((ι → R) ⧸ L') y → x ≤ y ∧ (x = y → L = L') := by
  intro C _ v R _ _ hv ι _ L L' hL x y hx0 hx hy
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := hx
  obtain ⟨n, d, ⟨e'⟩, rfl⟩ := hy
  haveI := isLocal_of_integers hv
  let π : ((i : Fin m) → R ⧸ Ideal.span {c i}) →ₗ[R] ((i : Fin n) → R ⧸ Ideal.span {d i}) :=
    e'.toLinearMap ∘ₗ (Submodule.factor hL) ∘ₗ e.symm.toLinearMap
  have hπ : Function.Surjective π :=
    e'.surjective.comp ((Submodule.factor_surjective hL).comp e.symm.surjective)
  let s : Fin m → ((i : Fin m) → R ⧸ Ideal.span {c i}) :=
    fun i => Pi.single i (1 : R ⧸ Ideal.span {c i})
  have hsp : Submodule.span R (Set.range fun i => π (s i)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨w, rfl⟩ := hπ z

    rw [eq_sum_single c w, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdiag : ∀ k, ∑ i, Matrix.diagonal c k i • π (s i) = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq, ← map_smul, single_smul_self c k, map_zero]
    · intro i _ hi
      rw [Matrix.diagonal_apply_ne' _ hi, zero_smul]
    · simp
  have key : ∀ T : Matrix (Fin m) (Fin m) R, (∀ k, ∑ i, T k i • π (s i) = 0) →
      v (algebraMap R C T.det) ≤ ∏ i, v (algebraMap R C (d i)) := by
    intro T hT
    have h := det_mem_span_prod n d m _ hsp T hT
    rw [Ideal.mem_span_singleton] at h
    have h2 := hv.le_of_dvd h
    rwa [map_prod, map_prod] at h2
  refine ⟨?_, fun hxy => le_antisymm hL fun l hl => ?_⟩
  · have := key _ hdiag
    rwa [Matrix.det_diagonal, map_prod, map_prod] at this
  · set w := e (Submodule.Quotient.mk l) with hw
    have hπw : π w = 0 := by
      have : (Submodule.Quotient.mk l : (ι → R) ⧸ L') = 0 := (Submodule.Quotient.mk_eq_zero _).2 hl
      simp [π, hw, this]
    have hw0 : w = 0 := by
      funext i
      have hrel : ∑ k, (Quotient.out (w k) : R) • π (s k) = 0 := by
        rw [← hπw]

        conv_rhs => rw [eq_sum_single c w, map_sum]
        simp only [map_smul, s]
      have h := key ((Matrix.diagonal c).updateRow i fun k => (Quotient.out (w k) : R)) (by
        intro k
        by_cases hk : k = i
        · subst hk
          simpa only [Matrix.updateRow_self] using hrel
        · simpa only [Matrix.updateRow_ne hk] using hdiag k)
      rw [det_updateRow_diagonal, ← hxy, map_mul, map_mul, map_prod, map_prod,
        ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at h
      have hne : ∏ j ∈ Finset.univ.erase i, v (algebraMap R C (c j)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ =>
          Finset.prod_ne_zero_iff.1 hx0 j (Finset.mem_univ j)
      have h2 := le_of_mul_le_mul_left h (pos_iff_ne_zero.2 hne)
      have h3 := hv.dvd_of_le h2
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out] at h3
      exact h3
    have : (Submodule.Quotient.mk l : (ι → R) ⧸ L) = 0 := e.injective (by rw [← hw, hw0, map_zero])
    exact (Submodule.Quotient.mk_eq_zero _).1 this

end PositivityTheory.HtPt.Rh
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rb

theorem triang_strong (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (n : ℕ) (L : Submodule R (Fin n → R)) (hL : L.FG) :
    ∃ d : Fin n → R, (∀ i c, c ∈ Ideal.span {d i} ↔ ∃ l ∈ L, (∀ j, j < i → l j = 0) ∧ l i = c) ∧
      HasLen v R ((Fin n → R) ⧸ L) (∏ i, v (algebraMap R C (d i))) := by
  classical
  haveI : IsDomain R := hv.hom_inj.isDomain
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  obtain ⟨m, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let ψ : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R w
  have hψ : LinearMap.range ψ = L := by rw [Fintype.range_linearCombination, hw]
  have key : ∀ i : Fin n, ∃ d : R,
      ∀ c, c ∈ Ideal.span {d} ↔ ∃ l ∈ L, (∀ j, j < i → l j = 0) ∧ l i = c := by
    intro i
    let π : (Fin n → R) →ₗ[R] ({j : Fin n // j < i} → R) := LinearMap.funLeft R R Subtype.val
    have h1 := comap_fg_of_valuationRing R (Fin m) {j : Fin n // j < i} (π ∘ₗ ψ) ⊥
      Submodule.fg_bot
    have h2 : Ideal.FG (R := R) (((⊥ : Submodule R _).comap (π ∘ₗ ψ)).map
        (LinearMap.proj i ∘ₗ ψ)) := h1.map _
    obtain ⟨d, hd⟩ := (IsBezout.isPrincipal_of_FG _ h2).principal
    refine ⟨d, fun c => ?_⟩
    have : Ideal.span {d} = ((⊥ : Submodule R _).comap (π ∘ₗ ψ)).map
        (LinearMap.proj i ∘ₗ ψ) := hd.symm
    rw [this]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨ψ a, hψ ▸ LinearMap.mem_range_self ψ a, fun j hj => ?_, rfl⟩
      exact congrFun (show π (ψ a) = 0 from ha) ⟨j, hj⟩
    · rintro ⟨l, hl, h0, rfl⟩
      rw [← hψ] at hl
      obtain ⟨a, rfl⟩ := hl
      refine ⟨a, ?_, rfl⟩
      show π (ψ a) = 0
      funext j
      exact h0 j.1 j.2
  choose d hd using key
  refine ⟨d, hd, ?_⟩
  choose u huL hu0 hud using fun i => (hd i (d i)).1 (Ideal.mem_span_singleton_self _)
  let X : Matrix (Fin n) (Fin n) R := Matrix.of fun j i => u i j
  have hcol : ∀ i, u i ∈ LinearMap.range X.mulVecLin := fun i =>
    ⟨Pi.single i 1, by ext j; simp [X]⟩
  have hrange : LinearMap.range X.mulVecLin = L := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      have : X.mulVecLin a = ∑ i, a i • u i := by
        ext j
        simp [X, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [this]
      exact L.sum_mem fun i _ => L.smul_mem _ (huL i)
    · have hind : ∀ t : ℕ, ∀ l ∈ L, (∀ j : Fin n, (j : ℕ) + t < n → l j = 0) →
          l ∈ LinearMap.range X.mulVecLin := by
        intro t
        induction t with
        | zero =>
          intro l _ h0
          have : l = 0 := funext fun j => h0 j (by simp)
          rw [this]
          exact Submodule.zero_mem _
        | succ t ih =>
          intro l hl h0
          by_cases ht : t < n
          · let i : Fin n := ⟨n - 1 - t, by omega⟩
            have hi : (i : ℕ) = n - 1 - t := rfl
            have hlow : ∀ j, j < i → l j = 0 := fun j hj => h0 j (by
              have := Fin.lt_def.1 hj
              omega)
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((hd i (l i)).2 ⟨l, hl, hlow, rfl⟩)
            have h3 := ih (l - c • u i) (L.sub_mem hl (L.smul_mem _ (huL i))) (fun j hj => by
              rcases lt_or_eq_of_le (show j ≤ i from Fin.le_def.2 (by omega)) with h | h
              · simp [hlow j h, hu0 i j h]
              · subst h
                simp [hud, hc])
            have h4 := Submodule.add_mem _ h3 (Submodule.smul_mem _ c (hcol i))
            simpa using h4
          · exact ih l hl fun j hj => by omega
      intro l hl
      exact hind n l hl fun j hj => by omega
  have hdet : X.det = ∏ i, d i := by
    rw [Matrix.det_of_lowerTriangular X (fun j i h => hu0 i j h)]
    exact Finset.prod_congr rfl fun i _ => hud i
  have := Smith.hasLen_coker_det hv X
  rw [hrange, hdet, map_prod, map_prod] at this
  exact this

end PositivityTheory.HtPt.Rb
end
