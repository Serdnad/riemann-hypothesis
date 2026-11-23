module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem flagF_diag_mul {F : Type} [Field F] {n : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA (show id k < id i from h), zero_mul]
    · rw [hB (show id i < id k from h), mul_zero]
  · simp

private theorem flagF_tri {F H : Type} [Field F] {n : ℕ} (T : H → Matrix (Fin n) (Fin n) F)
    (E : Matrix (Fin n) (Fin n) F) (hT : ∀ s, (T s).BlockTriangular id)
    (hsep : ∀ i j, i ≠ j → ∃ s, T s i i ≠ T s j j) (hc : ∀ s, T s * E = E * T s) :
    E.BlockTriangular id := by
  have key : ∀ m : ℕ, ∀ i j : Fin n, j < i → n + (j : ℕ) ≤ i + m → E i j = 0 := by
    intro m
    induction m with
    | zero => intro i j _ h; have := i.2; omega
    | succ m ih =>
      intro i j hji h
      obtain ⟨s, hs⟩ := hsep i j hji.ne'
      have h1 : (T s * E) i j = T s i i * E i j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · intro k _ hk
          rcases lt_or_gt_of_ne hk with h' | h'
          · rw [hT s (show id k < id i from h'), zero_mul]
          · rw [ih k j (hji.trans h') (by rw [Fin.lt_def] at h'; omega), mul_zero]
        · simp
      have h2 : (E * T s) i j = E i j * T s j j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j]
        · intro k _ hk
          rcases lt_or_gt_of_ne hk with h' | h'
          · rw [ih i k (h'.trans hji) (by rw [Fin.lt_def] at h'; omega), zero_mul]
          · rw [hT s (show id j < id k from h'), mul_zero]
        · simp
      rw [hc, h2, mul_comm] at h1
      by_contra h0
      exact hs (mul_right_cancel₀ h0 h1).symm
  intro i j hji
  exact key n i j hji (by have : (j : ℕ) < i := hji; omega)

private theorem flagF_diagonalise {F : Type} [Field F] {n : ℕ} (E : Matrix (Fin n) (Fin n) F)
    (hE : E.BlockTriangular id) (hEE : E * E = E) :
    ∃ U : Matrix (Fin n) (Fin n) F, U.BlockTriangular id ∧ (∀ i, U i i = 1) ∧
      E * U = U * diagonal (fun i => E i i) := by
  have hd : ∀ i, E i i * E i i = E i i := fun i => by rw [← flagF_diag_mul hE hE, hEE]
  have hDD : diagonal (fun i => E i i) * diagonal (fun i => E i i) = diagonal (fun i => E i i) := by
    rw [diagonal_mul_diagonal]; simp only [hd]
  have hD : (diagonal (fun i => E i i)).BlockTriangular id := blockTriangular_diagonal _
  have h1 : (1 : Matrix (Fin n) (Fin n) F).BlockTriangular id := blockTriangular_one
  refine ⟨E * diagonal (fun i => E i i) + (1 - E) * (1 - diagonal (fun i => E i i)),
    (hE.mul hD).add ((h1.sub hE).mul (h1.sub hD)), fun i => ?_, ?_⟩
  · rw [Matrix.add_apply, flagF_diag_mul hE hD, flagF_diag_mul (h1.sub hE) (h1.sub hD)]
    simp only [Matrix.sub_apply, diagonal_apply_eq, one_apply_eq]
    linear_combination 2 * hd i
  · generalize diagonal (fun i => E i i) = D at hDD
    have a1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hEE, sub_self]
    have a2 : (1 - D) * D = 0 := by rw [sub_mul, one_mul, hDD, sub_self]
    rw [mul_add, add_mul, ← mul_assoc, ← mul_assoc, hEE, a1, zero_mul, mul_assoc, mul_assoc, hDD, a2,
      mul_zero]

theorem UpperTheory.V.Pa.Det.flagF :
    ∀ {F H : Type} [Field F] [Infinite F] [Group H] {n a : ℕ} (r : H →* GL (Fin n) F) (ψ : Fin n → H →* Fˣ), (∀ g, mat r g ∈ Ev F F n a) → Function.Injective ψ → HasFlag r ψ → ∃ (w : GL (Fin n) F) (ty : Fin n → Bool), (∀ i j : Fin n, decide ((i : ℕ) < a) ≠ ty j → w i j = 0) ∧ ∀ g, (∀ i j, j < i → (w⁻¹ * r g * w : GL (Fin n) F) i j = 0) ∧ ∀ i, (w⁻¹ * r g * w : GL (Fin n) F) i i = (ψ i g : F) := by
  intro F H _ _ _ n a r ψ hev hinj ⟨g, hg⟩
  classical
  set e : Matrix (Fin n) (Fin n) F := diagonal fun i => if (i : ℕ) < a then 1 else 0 with he
  have hee : e * e = e := by
    rw [he, diagonal_mul_diagonal]; congr 1; ext i; split_ifs <;> simp
  have hce : ∀ s, (r s : Matrix (Fin n) (Fin n) F) * e = e * r s := by
    intro s
    ext i j
    rw [he, mul_diagonal, diagonal_mul]
    have h : ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → (r s : Matrix (Fin n) (Fin n) F) i j = 0 :=
      fun h => (Submodule.mem_bot F).1 ((hev s i j).2 h)
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] at h ⊢ <;> simp [h]
  set E : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) * e * (g⁻¹ : GL (Fin n) F) with hE
  have hEE : E * E = E := by
    simp only [hE, mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc e, hee]
  have hT : ∀ s, ((g * r s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id :=
    fun s i j h => (hg s).1 i j h
  have hEt : E.BlockTriangular id := by
    refine flagF_tri (fun s => ((g * r s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) E hT ?_ ?_
    · intro i j hij
      by_contra hcon
      push Not at hcon
      refine hij (hinj (MonoidHom.ext fun s => Units.ext ?_))
      rw [← (hg s).2 i, ← (hg s).2 j]
      exact hcon s
    · intro s
      simp only [hE, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
      rw [← mul_assoc (r s : Matrix (Fin n) (Fin n) F), hce, mul_assoc]
  obtain ⟨U, hU, hU1, hEU⟩ := flagF_diagonalise E hEt hEE
  have hdet : U.det ≠ 0 := by rw [det_of_upperTriangular hU]; simp [hU1]
  obtain ⟨u, rfl⟩ : ∃ u : GL (Fin n) F, (u : Matrix (Fin n) (Fin n) F) = U :=
    ⟨GeneralLinearGroup.mkOfDetNeZero U hdet, rfl⟩
  have hUi : ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id := by
    letI := u.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hU
  refine ⟨g⁻¹ * u, fun j => decide (E j j = 1), fun i j hij => ?_, fun s => ?_⟩
  · have h : e * ((g⁻¹ * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((g⁻¹ * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * diagonal (fun i => E i i) := by
      rw [Units.val_mul, mul_assoc, ← hEU]
      simp only [hE, mul_assoc, Units.inv_mul_cancel_left]
    have h2 := congrFun (congrFun h i) j
    rw [he, mul_diagonal, diagonal_mul, mul_comm] at h2
    by_contra h0
    have h3 := mul_left_cancel₀ h0 h2
    apply hij
    by_cases hi : (i : ℕ) < a
    · simp [hi] at h3 ⊢; exact h3.symm
    · simp [hi] at h3 ⊢; simp [← h3]
  · have e1 : (g⁻¹ * u)⁻¹ * r s * (g⁻¹ * u) = u⁻¹ * ((g * r s * g⁻¹) * u) := by group
    have t1 : ((u⁻¹ * ((g * r s * g⁻¹) * u) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id := by
      rw [Units.val_mul, Units.val_mul]
      exact hUi.mul ((hT s).mul hU)
    rw [e1]
    refine ⟨fun i j h => t1 h, fun i => ?_⟩
    have h1 := flagF_diag_mul hU t1 i
    rw [← Units.val_mul, mul_inv_cancel_left, Units.val_mul, flagF_diag_mul (hT s) hU, hU1, mul_one,
      one_mul] at h1
    rw [← (hg s).2 i]
    exact h1.symm
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem sd_map_ev {F F' : Type} [Field F] [Field F'] (f : F →+* F') {n a : ℕ}
    {Z : Matrix (Fin n) (Fin n) F} (hZ : Z ∈ Ev F F n a) : Z.map f ∈ Ev F' F' n a := by
  intro i j
  refine ⟨fun _ => trivial, fun e => ?_⟩
  have h0 : Z i j = 0 := (hZ i j).2 e
  rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]

private theorem sd_up {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ}
    (r : ι → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F)
    (hY : Y ∈ Submodule.span F (Set.range r)) :
    Y.map f ∈ Submodule.span F' (Set.range fun i => (r i).map f) := by
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero =>
    have : (0 : Matrix (Fin n) (Fin n) F).map f = 0 := by ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have : (y + z).map f = y.map f + z.map f := by ext i j; simp
    rw [this]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have : (c • y).map f = f c • y.map f := by ext i j; simp
    rw [this]; exact Submodule.smul_mem _ _ hy

private theorem sd_down {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ}
    (r : ι → Matrix (Fin n) (Fin n) F) (p : F' →+ F) (hp : ∀ (c : F') (x : F), p (c * f x) = p c * x)
    (Y : Matrix (Fin n) (Fin n) F')
    (hY : Y ∈ Submodule.span F' (Set.range fun i => (r i).map f)) :
    ∀ c : F', (c • Y).map p ∈ Submodule.span F (Set.range r) := by
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    intro c
    have : (c • (r i).map f).map p = p c • r i := by
      ext s t; simp [hp]
    show (c • (r i).map f).map p ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero =>
    intro c
    have : (c • (0 : Matrix (Fin n) (Fin n) F')).map p = 0 := by ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    intro c
    have : (c • (y + z)).map p = (c • y).map p + (c • z).map p := by ext i j; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ (hy c) (hz c)
  | smul d y _ hy =>
    intro c
    rw [smul_smul]; exact hy _

theorem UpperTheory.V.Pa.Det.spanDesc :
    ∀ {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n a : ℕ} (r : ι → Matrix (Fin n) (Fin n) F), (∀ i, r i ∈ Ev F F n a) → (Submodule.span F (Set.range r) = Ev F F n a ↔ Submodule.span F' (Set.range fun i => (r i).map f) = Ev F' F' n a) := by
  intro F F' ι _ _ f n a r hr
  constructor
  · intro h
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact sd_map_ev f (hr i)
    · intro Z hZ
      have hZ' : Z = ∑ i, ∑ j, single i j (Z i j) := matrix_eq_sum_single Z
      rw [hZ']
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
      · have h1 : (single i j 1 : Matrix (Fin n) (Fin n) F) ∈ Ev F F n a :=
          fun p q => ⟨fun _ => trivial, fun e' => by
            rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
            rintro ⟨rfl, rfl⟩
            exact e' e⟩
        rw [← h] at h1
        have h2 := Submodule.smul_mem _ (Z i j) (sd_up f r _ h1)
        convert h2 using 1
        ext p q
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
        split_ifs <;> simp
      · have : Z i j = 0 := (hZ i j).2 e
        simp [this]
  · intro h
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hr i
    · intro Z hZ
      letI : Algebra F F' := f.toAlgebra
      obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F F')
        (LinearMap.ker_eq_bot.2 f.injective)
      have hp1 : ∀ x : F, p (f x) = x := fun x => LinearMap.congr_fun hp x
      have hp2 : ∀ (c : F') (x : F), p.toAddMonoidHom (c * f x) = p.toAddMonoidHom c * x := by
        intro c x
        have h3 : c * f x = x • c := by rw [mul_comm]; rfl
        show p (c * f x) = p c * x
        rw [h3, map_smul, smul_eq_mul, mul_comm]
      have h1 := sd_map_ev f hZ
      rw [← h] at h1
      have h2 := sd_down f r p.toAddMonoidHom hp2 _ h1 1
      convert h2 using 1
      ext s t
      simp [hp1]
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa.Det

open Polynomial

private noncomputable def dsc {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : R :=
  resultant M.charpoly (derivative M.charpoly) n n

private theorem dsc_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    dsc (M.map φ) = φ (dsc M) := by
  unfold dsc
  rw [Matrix.charpoly_map, derivative_map, resultant_map_map]

private theorem dsc_ne_iff {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    dsc M ≠ 0 ↔ M.charpoly.Separable := by
  have hm : M.charpoly.Monic := Matrix.charpoly_monic M
  have hd : M.charpoly.natDegree = n := by simp [Matrix.charpoly_natDegree_eq_dim]
  have hle : (derivative M.charpoly).natDegree ≤ n :=
    (natDegree_derivative_le _).trans (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have hc : M.charpoly.coeff n = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  have h1 : dsc M = resultant M.charpoly (derivative M.charpoly) := by
    unfold dsc
    have := resultant_add_right_deg M.charpoly (derivative M.charpoly) n (derivative M.charpoly).natDegree k le_rfl
    rw [← hk, hc, one_pow, one_mul] at this
    rw [this, hd]
  rw [h1, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hm]
  rfl

private theorem sep_iff {A : Type} [CommRing A] [IsDomain A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) :
    (M.charpoly.map (algebraMap A (FractionRing A))).Separable ↔ dsc M ≠ 0 := by
  rw [← Matrix.charpoly_map, ← dsc_ne_iff, dsc_map]
  exact (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A)))

private theorem sep_open {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) :
    IsOpen {σ : F.G₀ | ((mat x.ρ σ).charpoly.map (algebraMap x.A (FractionRing x.A))).Separable} := by
  simp only [sep_iff]
  rw [isOpen_iff_mem_nhds]
  intro s hs
  have hN : ∃ N : ℕ, dsc (mat x.ρ s) ∉ maximalIdeal x.A ^ N := by
    by_contra hc
    push Not at hc
    have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal x.A) (maximalIdeal.isMaximal _).ne_top
    have h2 : dsc (mat x.ρ s) ∈ ⨅ N : ℕ, maximalIdeal x.A ^ N := Submodule.mem_iInf _ |>.2 hc
    rw [this] at h2
    exact hs (by simpa using h2)
  obtain ⟨N, hN⟩ := hN
  have hev : ∀ᶠ g in nhds s, ∀ i j, Ideal.Quotient.mk (maximalIdeal x.A ^ N) (mat x.ρ g i j)
      = Ideal.Quotient.mk (maximalIdeal x.A ^ N) (mat x.ρ s i j) := by
    simp only [Filter.eventually_all]
    intro i j
    exact (x.cont i j N).eventually_eq s
  filter_upwards [hev] with g hg h0
  apply hN
  have hM : (mat x.ρ g).map (Ideal.Quotient.mk (maximalIdeal x.A ^ N))
      = (mat x.ρ s).map (Ideal.Quotient.mk (maximalIdeal x.A ^ N)) := by
    ext i j; exact hg i j
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← dsc_map, ← hM, dsc_map, h0, map_zero]

end UpperTheory.V.Pa.Det

theorem UpperTheory.V.Pa.Det.omDense :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n h : ℕ} (x : Fin h → NP F n), (∀ i, (x i).N3) → (F.G' : Set F.G₀) ⊆ closure {σ : F.G₀ | σ ∈ F.G' ∧ ∀ i, ((mat (x i).ρ σ).charpoly.map (algebraMap (x i).A (FractionRing (x i).A))).Separable} := by
  intro l _ F n h x hx σ hσ
  rw [mem_closure_iff]
  intro U hU hσU
  have key : ∀ S : Finset (Fin h), ∃ τ ∈ U ∩ (F.G' : Set F.G₀), ∀ i ∈ S,
      ((mat (x i).ρ τ).charpoly.map (algebraMap (x i).A (FractionRing (x i).A))).Separable := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨σ, ⟨hσU, hσ⟩, by simp⟩
    | insert a S ha ih =>
      obtain ⟨τ, ⟨h1, h2⟩, h3⟩ := ih
      have ho : IsOpen (U ∩ ⋂ i ∈ S, {σ : F.G₀ | ((mat (x i).ρ σ).charpoly.map
          (algebraMap (x i).A (FractionRing (x i).A))).Separable}) :=
        hU.inter (isOpen_biInter_finset fun i _ => UpperTheory.V.Pa.Det.sep_open (x i))
      obtain ⟨τ', ⟨⟨g1, g2⟩, g3⟩, g4⟩ := hx a _ ho ⟨τ, ⟨h1, Set.mem_iInter₂.2 h3⟩, h2⟩
      refine ⟨τ', ⟨g1, g3⟩, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact g4
      · exact Set.mem_iInter₂.1 g2 i hi
  obtain ⟨τ, ⟨h1, h2⟩, h3⟩ := key Finset.univ
  exact ⟨τ, h1, h2, fun i => h3 i (Finset.mem_univ i)⟩
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem single_mem_ev_of_same_block {F : Type} [CommRing F] {n a : ℕ} (p q : Fin n) (c : F)
    (h : ((p : ℕ) < a ↔ (q : ℕ) < a)) : Matrix.single p q c ∈ Ev F F n a := by
  intro i j
  refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
  rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hij h

theorem UpperTheory.V.Pa.Det.derEv :
    ∀ {F : Type} [CommRing F] {n a : ℕ} (d : Matrix (Fin n) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F), (∀ x ∈ Ev F F n a, ∀ y ∈ Ev F F n a, d (x * y) = d x * y + x * d y) → ∃ Y, ∀ x ∈ Ev F F n a, d x = Y * x - x * Y := by
  intro F _ n a d hd
  let β : Fin n → Fin n := fun i =>
    if h : (i : ℕ) < a then ⟨0, lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩
    else ⟨a, lt_of_le_of_lt (not_lt.mp h) i.isLt⟩
  have hβ : ∀ i : Fin n, ((i : ℕ) < a ↔ (β i : ℕ) < a) := by
    intro i
    by_cases h : (i : ℕ) < a
    · simp only [β, dif_pos h]
      exact ⟨fun _ => Nat.zero_lt_of_lt h, fun _ => h⟩
    · simp only [β, dif_neg h]
      exact ⟨fun h' => absurd h' h, fun h' => absurd h' (lt_irrefl _)⟩
  have hβeq : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → β i = β j := by
    intro i j h
    by_cases hi : (i : ℕ) < a
    · have hj := h.mp hi
      simp only [β, dif_pos hi, dif_pos hj]
    · have hj : ¬ (j : ℕ) < a := fun hj => hi (h.mpr hj)
      simp only [β, dif_neg hi, dif_neg hj]
  let E : Fin n → Fin n → Matrix (Fin n) (Fin n) F := fun i j => Matrix.single i j 1
  let u : Fin n → Matrix (Fin n) (Fin n) F := fun k => E k (β k)
  let v : Fin n → Matrix (Fin n) (Fin n) F := fun k => E (β k) k
  have hu : ∀ k, u k ∈ Ev F F n a := fun k => single_mem_ev_of_same_block _ _ _ (hβ k)
  let Y := ∑ k, d (u k) * v k
  have hsum : ∑ k, u k * v k = 1 := by
    simp only [u, v, E, Matrix.single_mul_single_same, mul_one]
    exact Matrix.sum_single_one
  have key : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) →
      d (E i j) = Y * E i j - E i j * Y := by
    intro i j hij
    have hE : E i j ∈ Ev F F n a := single_mem_ev_of_same_block i j 1 hij
    have h1 : Y * E i j = d (u i) * v j := by
      simp only [Y, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_eq_single i]
      · simp only [v, E, u]
        rw [Matrix.single_mul_single_same, mul_one, hβeq i j hij]
      · intro k _ hk
        simp only [v, E]
        rw [Matrix.single_mul_single_of_ne _ _ _ _ hk _, mul_zero]
      · simp
    have hk : ∀ k, E i j * d (u k) = d (E i j * u k) - d (E i j) * u k := by
      intro k
      rw [hd _ hE _ (hu k)]
      abel
    have hEu : ∀ k, E i j * u k = if j = k then u i else 0 := by
      intro k
      split_ifs with h
      · subst h
        simp only [E, u]
        rw [Matrix.single_mul_single_same, mul_one, hβeq i j hij]
      · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
    have h2 : E i j * Y = d (u i) * v j - d (E i j) := by
      calc E i j * Y = ∑ k, (d (E i j * u k) * v k - d (E i j) * (u k * v k)) := by
            simp only [Y, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← mul_assoc, hk, sub_mul, mul_assoc]
        _ = d (u i) * v j - d (E i j) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
            congr 1
            rw [Finset.sum_eq_single j]
            · rw [hEu, if_pos rfl]
            · intro k _ hk
              rw [hEu, if_neg (Ne.symm hk), map_zero, zero_mul]
            · simp
    rw [h1, h2]
    abel
  refine ⟨Y, fun x hx => ?_⟩
  let D' : Matrix (Fin n) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F :=
    d - (LinearMap.mulLeft F Y - LinearMap.mulRight F Y)
  have hD : D' x = 0 := by

    rw [Matrix.matrix_eq_sum_single x, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_

    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : ((i : ℕ) < a ↔ (j : ℕ) < a)
    · have hs : Matrix.single i j (x i j) = x i j • E i j := by
        simp only [E, Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul]
      simp only [D', LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        key i j hij, sub_self, smul_zero]
    · have h0 : x i j = 0 := (Submodule.mem_bot F).mp ((hx i j).2 hij)
      rw [h0, Matrix.single_zero, map_zero]
  simp only [D', LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    sub_eq_zero] at hD
  exact hD
end
