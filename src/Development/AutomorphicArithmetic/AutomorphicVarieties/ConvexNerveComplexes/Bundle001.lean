module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

open Set UpperTheory.V.ConeExtensionAcyclic

private noncomputable def kap {I : Type} (a : I) (n : ℕ) : Ch I n →ₗ[ℤ] Ch I (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun t : Fin n → I => (Fin.cons a t : Fin (n + 1) → I))

private theorem kap_single {I : Type} (a : I) (n : ℕ) (t : Fin n → I) (m : ℤ) :
    kap a n (Finsupp.single t m) = Finsupp.single (Fin.cons a t : Fin (n + 1) → I) m := by
  simp [kap, Finsupp.mapDomain_single]

private theorem bd_single {I : Type} (n : ℕ) (t : Fin (n + 1) → I) :
    bd I n (Finsupp.single t 1) =
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (t ∘ j.succAbove) (1 : ℤ) := by
  simp only [bd, Finsupp.linearCombination_single, one_smul]

private theorem cons_zero_succAbove {I : Type} (a : I) (n : ℕ) (t : Fin n → I) :
    (Fin.cons a t : Fin (n + 1) → I) ∘ (0 : Fin (n + 1)).succAbove = t := by
  funext i
  simp

private theorem cons_succ_succAbove {I : Type} (a : I) (n : ℕ) (t : Fin (n + 1) → I)
    (j : Fin (n + 1)) :
    (Fin.cons a t : Fin (n + 2) → I) ∘ (j.succ).succAbove =
      (Fin.cons a (t ∘ j.succAbove) : Fin (n + 1) → I) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp

private theorem bd_kap_zero {I : Type} (a : I) (c : Ch I 0) : bd I 0 (kap a 0 c) = c := by
  have hlin : (bd I 0).comp (kap a 0) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro t m
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [kap_single]
    have e1 : Finsupp.single (Fin.cons a t : Fin 1 → I) m = m • Finsupp.single (Fin.cons a t : Fin 1 → I) 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e1, map_smul, bd_single, Fin.sum_univ_one, cons_zero_succAbove]
    simp [Finsupp.smul_single]
  exact LinearMap.congr_fun hlin c

private theorem bd_kap_succ {I : Type} (a : I) (n : ℕ) (c : Ch I (n + 1)) :
    bd I (n + 1) (kap a (n + 1) c) = c - kap a n (bd I n c) := by
  have hlin : (bd I (n + 1)).comp (kap a (n + 1)) = LinearMap.id - (kap a n).comp (bd I n) := by
    apply Finsupp.lhom_ext
    intro t m
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
    rw [kap_single]
    have e1 : Finsupp.single (Fin.cons a t : Fin (n + 2) → I) m = m • Finsupp.single (Fin.cons a t : Fin (n + 2) → I) 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have e2 : Finsupp.single t m = m • Finsupp.single t 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]

    rw [e1, e2, map_smul, map_smul, map_smul, bd_single, bd_single, Fin.sum_univ_succ, map_sum]
    simp only [map_smul, kap_single, cons_zero_succAbove, cons_succ_succAbove, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ]
    simp only [mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, smul_add, smul_neg, sub_eq_add_neg]
  exact LinearMap.congr_fun hlin c

private theorem kap_mem {I : Type} (S : ∀ n, Set (Fin n → I)) (a : I) (n : ℕ)
    (h : ∀ t : Fin n → I, t ∈ S n → (Fin.cons a t : Fin (n + 1) → I) ∈ S (n + 1))
    (c : Ch I n) (hc : c ∈ Finsupp.supported ℤ ℤ (S n)) :
    kap a n c ∈ Finsupp.supported ℤ ℤ (S (n + 1)) := by
  classical
  rw [Finsupp.mem_supported] at hc ⊢
  intro u hu
  have hu' := Finsupp.mapDomain_support (Finset.mem_coe.1 hu)
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu'
  exact h t (hc ht)

theorem UpperTheory.V.ConeExtensionAcyclic.acyc_cone :
    ∀ {I : Type} (S : ∀ n, Set (Fin n → I)) (a : I), (∀ (n : ℕ) (t : Fin n → I), t ∈ S n → (Fin.cons a t : Fin (n + 1) → I) ∈ S (n + 1)) → Acyc S := by
  intro I S a h
  refine ⟨fun c hc => ⟨kap a 0 c, kap_mem S a 0 (h 0) c hc, bd_kap_zero a c⟩,
    fun n c hc h0 => ⟨kap a (n + 1) c, kap_mem S a (n + 1) (h (n + 1)) c hc, ?_⟩⟩
  rw [bd_kap_succ, h0, map_zero, sub_zero]
end

section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.perturb :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ}, LocFin q → ∀ h ∈ poly q, ∀ k : E, (∀ y, q y h = 1 → q y k = 0) → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s| ≤ ε → h + s • k ∈ poly q := by
  intro E Y _ _ q hq h hh k hk
  have hh' : ∀ y, 1 ≤ q y h := hh
  obtain ⟨S, hS, hU⟩ := hq h hh
  have hc : Continuous fun s : ℝ => h + s • k :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hT : Filter.Tendsto (fun s : ℝ => h + s • k) (nhds 0) (nhds h) := by
    have := hc.tendsto 0
    simpa using this
  have A : ∀ᶠ s in nhds (0:ℝ), ∀ y ∉ S, 1 < q y (h + s • k) := hT.eventually hU
  have B : ∀ᶠ s in nhds (0:ℝ), ∀ y ∈ S, 1 ≤ q y (h + s • k) := by
    refine (Filter.eventually_all_finite hS).2 fun y _ => ?_
    by_cases hy : q y h = 1
    · refine Filter.Eventually.of_forall fun s => ?_
      simp [hy, hk y hy]
    · have hlt : 1 < q y h := lt_of_le_of_ne (hh' y) (Ne.symm hy)
      have hcy : Continuous fun s : ℝ => q y (h + s • k) := (q y).continuous.comp hc
      have ht := hcy.tendsto 0
      simp only [zero_smul, add_zero] at ht
      exact (ht.eventually (lt_mem_nhds hlt)).mono fun s hs => hs.le
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 (A.and B)
  refine ⟨δ / 2, half_pos hδ, fun s hs => ?_⟩
  have hd : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    linarith
  obtain ⟨h1, h2⟩ := hP hd
  show ∀ y, 1 ≤ q y (h + s • k)
  intro y
  by_cases hyS : y ∈ S
  · exact h2 y hyS
  · exact (h1 y hyS).le
end

section

open Set UpperTheory.V.ConeExtensionAcyclic

private theorem UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((i.succAbove j : ℕ) = if (j : ℕ) < i then (j : ℕ) else j + 1) ∧
      ((j.predAbove i : ℕ) = if (j : ℕ) < i then (i : ℕ) - 1 else i) := by
  by_cases h : (j : ℕ) < i
  · have h' : j.castSucc < i := by
      rw [Fin.lt_def, Fin.coe_castSucc]
      exact h
    rw [Fin.succAbove_of_castSucc_lt _ _ h', Fin.predAbove_of_castSucc_lt _ _ h']
    simp [h]
  · have h' : i ≤ j.castSucc := by
      rw [Fin.le_def, Fin.coe_castSucc]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ h', Fin.predAbove_of_le_castSucc _ _ h']
    simp [h]

private theorem UpperTheory.V.ConeExtensionAcyclic.alt_double_sum {M : Type*} [AddCommGroup M] [IsAddTorsionFree M]
    (n : ℕ) (f : Fin (n + 2) → Fin (n + 1) → M)
    (hf : ∀ i j, f (i.succAbove j) (j.predAbove i) = f i j) :
    ∑ i : Fin (n + 2), ∑ j : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • f i j = 0 := by
  let φ : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1) :=
    fun p => (p.1.succAbove p.2, p.2.predAbove p.1)
  have hinv : ∀ p, φ (φ p) = p := by
    rintro ⟨i, j⟩
    obtain ⟨h1, h2⟩ := UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n i j
    obtain ⟨h3, h4⟩ := UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n (i.succAbove j) (j.predAbove i)
    simp only [φ, Prod.mk.injEq, Fin.ext_iff]
    have hi := i.isLt
    have hj := j.isLt
    split_ifs at h1 h2 h3 h4 <;> omega
  have hsign : ∀ p : Fin (n + 2) × Fin (n + 1),
      ((-1 : ℤ) ^ (((φ p).1 : ℕ) + ((φ p).2 : ℕ))) = -((-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ))) := by
    rintro ⟨i, j⟩
    obtain ⟨h1, h2⟩ := UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n i j
    simp only [φ]
    rw [h1, h2]
    split_ifs with h
    · have e : (j : ℕ) + ((i : ℕ) - 1) + 1 = (i : ℕ) + j := by omega
      rw [← neg_one_mul ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))), ← e, pow_succ]
      ring
    · rw [show (j : ℕ) + 1 + i = (i : ℕ) + j + 1 by omega, pow_succ]
      ring
  let e : Fin (n + 2) × Fin (n + 1) ≃ Fin (n + 2) × Fin (n + 1) :=
    { toFun := φ, invFun := φ, left_inv := hinv, right_inv := hinv }
  set S := ∑ i : Fin (n + 2), ∑ j : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • f i j with hS
  have hneg : S = -S := by
    rw [hS, ← Finset.sum_neg_distrib]
    simp only [← Finset.sum_neg_distrib]
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv e _ _ ?_
    intro p
    show _ = -(((-1 : ℤ) ^ (((φ p).1 : ℕ) + ((φ p).2 : ℕ))) • f (φ p).1 (φ p).2)
    rw [hsign p]
    have hfp : f (φ p).1 (φ p).2 = f p.1 p.2 := hf p.1 p.2
    rw [hfp, neg_smul, neg_neg]
  have h2 : (2 : ℕ) • S = (2 : ℕ) • (0 : M) := by
    rw [two_nsmul, smul_zero]
    nth_rewrite 1 [hneg]
    exact neg_add_cancel S
  exact eq_of_nsmul_eq_nsmul_of_addCommute (by norm_num) (AddCommute.all _ _) h2

theorem UpperTheory.V.ConeExtensionAcyclic.bd_bd :
    ∀ (I : Type) (n : ℕ) (c : Ch I (n + 2)), bd I n (bd I (n + 1) c) = 0 := by
  intro I n c
  have hlin : (bd I n).comp (bd I (n + 1)) = 0 := by
    apply Finsupp.lhom_ext
    intro t a

    simp only [LinearMap.comp_apply, LinearMap.zero_apply, bd, Finsupp.linearCombination_single,
    map_smul, map_sum, one_smul, smul_smul, Finset.smul_sum]
    have hterm : ∀ (i : Fin (n + 2)) (j : Fin (n + 1)),
        (a * (-1) ^ (i : ℕ) * (1 * (-1) ^ (j : ℕ))) •
            (Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)) =
          a • (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
            Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)) := by
      intro i j
      rw [smul_smul, pow_add]
      congr 1
      ring
    simp only [hterm, ← Finset.smul_sum]
    rw [UpperTheory.V.ConeExtensionAcyclic.alt_double_sum n (fun i j => Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)), smul_zero]
    intro i j
    congr 1
    funext k
    simp only [Function.comp_apply]
    rw [Fin.succAbove_succAbove_succAbove_predAbove]
  exact LinearMap.congr_fun hlin c
end

section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.simp_smul :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E} (g : E ≃L[ℝ] E) (π : Y ≃ Y), (∀ y h, q (π y) (g h) = q y h) → (∀ k, g k ∈ T ↔ k ∈ T) → (∀ h, IsVert q h → IsVert q (g h)) ∧ ∀ (n : ℕ) (t t' : Fin n → Vert q), (∀ j, (t' j).1 = g (t j).1) → t ∈ simp q T n → t' ∈ simp q T n := by
  intro E Y _ _ q T g π hq hT
  have hpoly : ∀ h, h ∈ poly q → g.symm h ∈ poly q := by
    intro h hh
    show ∀ y, 1 ≤ q y (g.symm h)
    intro y
    have h1 := (hh : ∀ y, 1 ≤ q y h) (π y)
    rw [← hq y (g.symm h), g.apply_symm_apply]
    exact h1
  refine ⟨fun h hv => ⟨?_, ?_⟩, ?_⟩
  · show ∀ y, 1 ≤ q y (g h)
    intro y
    have h1 := (hv.1 : ∀ y, 1 ≤ q y h) (π.symm y)
    rw [← hq (π.symm y) h, π.apply_symm_apply] at h1
    exact h1
  · intro k hk
    have h0 : g.symm k = 0 := by
      refine hv.2 _ fun y hy => ?_
      have h1 : q (π y) (g h) = 1 := by
        rw [hq]
        exact hy
      have h2 := hk (π y) h1
      rw [← hq y (g.symm k), g.apply_symm_apply]
      exact h2
    simpa using congrArg g h0
  · intro n t t' ht ht0
    obtain ⟨x, hx, hxj⟩ : ∃ x ∈ posDual T, ∀ j, x ∈ normalCone q (t j).1 := ht0
    show ∃ x ∈ posDual T, ∀ j, x ∈ normalCone q (t' j).1
    refine ⟨x.comp (g.symm : E →L[ℝ] E), ?_, fun j => ?_⟩
    · show ∀ k ∈ T, k ≠ 0 → 0 < (x.comp (g.symm : E →L[ℝ] E)) k
      intro k hk hk0
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      refine (hx : ∀ k ∈ T, k ≠ 0 → 0 < x k) (g.symm k) ?_ ?_
      · rw [← hT, g.apply_symm_apply]
        exact hk
      · intro h0
        exact hk0 (by simpa using congrArg g h0)
    · show ∀ h' ∈ poly q, (x.comp (g.symm : E →L[ℝ] E)) (t' j).1 ≤ (x.comp (g.symm : E →L[ℝ] E)) h'
      intro h' hh'
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ht j,
        g.symm_apply_apply]
      exact (hxj j : ∀ h' ∈ poly q, x (t j).1 ≤ x h') (g.symm h') (hpoly h' hh')
end

section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.vert_finite :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ}, LocFin q → ∀ K : Set E, IsCompact K → K ⊆ poly q → {h | h ∈ K ∧ IsVert q h}.Finite := by
  intro E Y _ _ q hq K hK hKp
  choose S hSf hSU using fun x (hx : x ∈ K) => hq x (hKp hx)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx => {h' : E | ∀ y ∉ S x hx, 1 < q y h'})
    (fun x hx => hSU x hx)
  have hfin : (⋃ x ∈ (t : Set K), S x.1 x.2).Finite :=
    t.finite_toSet.biUnion fun x _ => hSf x.1 x.2
  refine Set.Finite.of_finite_image (f := fun v : E => {y : Y | q y v = 1}) ?_ ?_
  · refine hfin.finite_subsets.subset ?_
    rintro _ ⟨v, ⟨hvK, hvV⟩, rfl⟩
    have hv := ht hvK
    simp only [Set.mem_iUnion] at hv
    obtain ⟨x, hxt, hvx⟩ := hv
    show {y : Y | q y v = 1} ⊆ _
    intro y hy
    simp only [Set.mem_iUnion, Finset.mem_coe]
    refine ⟨x, hxt, ?_⟩
    by_contra hyS
    have h1 := (hvx : ∀ y ∉ S x.1 x.2, 1 < q y v) y hyS
    simp only [Set.mem_setOf_eq] at hy
    linarith
  · rintro v ⟨_, hvV⟩ w ⟨_, hwV⟩ hvw
    have key : w - v = 0 := by
      refine hvV.2 (w - v) fun y hy => ?_
      have hy' : y ∈ {y : Y | q y w = 1} := by
        have e : {y : Y | q y v = 1} = {y : Y | q y w = 1} := hvw
        rw [← e]
        exact hy
      simp only [Set.mem_setOf_eq] at hy'
      simp [map_sub, hy, hy']
    exact (sub_eq_zero.1 key).symm
end

section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.acyc_directed :
    ∀ {I : Type} (S : ∀ n, Set (Fin n → I)), (∀ (n : ℕ) (s : Finset (Fin n → I)), (↑s : Set (Fin n → I)) ⊆ S n → ∃ S' : ∀ k, Set (Fin k → I), (∀ k, S' k ⊆ S k) ∧ (↑s : Set (Fin n → I)) ⊆ S' n ∧ Acyc S') → Acyc S := by
  intro I S h
  refine ⟨fun c hc => ?_, fun n c hc h0 => ?_⟩
  · obtain ⟨S', hS, hs, hA⟩ := h 0 c.support ((Finsupp.mem_supported ℤ c).1 hc)
    obtain ⟨b, hb, e⟩ := hA.1 c ((Finsupp.mem_supported ℤ c).2 hs)
    exact ⟨b, Finsupp.supported_mono (hS 1) hb, e⟩
  · obtain ⟨S', hS, hs, hA⟩ := h (n + 1) c.support ((Finsupp.mem_supported ℤ c).1 hc)
    obtain ⟨b, hb, e⟩ := hA.2 n c ((Finsupp.mem_supported ℤ c).2 hs) h0
    exact ⟨b, Finsupp.supported_mono (hS (n + 2)) hb, e⟩
end

section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.bd_mem :
    ∀ {I : Type} {S : ∀ n, Set (Fin n → I)}, FaceClosed S → ∀ (n : ℕ) (c : Ch I (n + 1)), c ∈ Finsupp.supported ℤ ℤ (S (n + 1)) → bd I n c ∈ Finsupp.supported ℤ ℤ (S n) := by
  intro I S hS n c hc
  rw [bd, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
  exact Finsupp.single_mem_supported ℤ _ (hS n t (hc (Finset.mem_coe.2 ht)) j)
end

section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.nerve_cut :
    ∀ {I F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Set F) (A : I → Set F) (f : F →L[ℝ] ℝ) (u : ℝ), Convex ℝ X → (∀ i, Convex ℝ (A i)) → (nerve X A = fun n => nerve (X ∩ {x | f x ≤ u}) A n ∪ nerve (X ∩ {x | u ≤ f x}) A n) ∧ (nerve (X ∩ {x | f x = u}) A = fun n => nerve (X ∩ {x | f x ≤ u}) A n ∩ nerve (X ∩ {x | u ≤ f x}) A n) := by
  intro I F _ _ X A f u hX hA
  constructor
  · funext n
    ext t
    simp only [nerve, Set.mem_union, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hx, ht⟩
      rcases le_total (f x) u with h | h
      · exact Or.inl ⟨x, ⟨hx, h⟩, ht⟩
      · exact Or.inr ⟨x, ⟨hx, h⟩, ht⟩
    · rintro (⟨x, ⟨hx, _⟩, ht⟩ | ⟨x, ⟨hx, _⟩, ht⟩) <;> exact ⟨x, hx, ht⟩
  · funext n
    ext t
    simp only [nerve, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨hx, hfx⟩, ht⟩
      exact ⟨⟨x, ⟨hx, hfx.le⟩, ht⟩, ⟨x, ⟨hx, hfx.ge⟩, ht⟩⟩
    · rintro ⟨⟨x, ⟨hx, h1⟩, ht⟩, ⟨y, ⟨hy, h2⟩, ht'⟩⟩
      rcases lt_or_ge (f x) (f y) with hd | hd
      · have hd' : 0 < f y - f x := sub_pos.2 hd
        have hne : f y - f x ≠ 0 := hd'.ne'
        have ha0 : 0 ≤ (f y - u) / (f y - f x) := div_nonneg (by linarith) hd'.le
        have hb0 : 0 ≤ (u - f x) / (f y - f x) := div_nonneg (by linarith) hd'.le
        have hab : (f y - u) / (f y - f x) + (u - f x) / (f y - f x) = 1 := by
          rw [← add_div, div_eq_one_iff_eq hne]
          ring
        refine ⟨((f y - u) / (f y - f x)) • x + ((u - f x) / (f y - f x)) • y,
          ⟨hX hx hy ha0 hb0 hab, ?_⟩, fun j => hA _ (ht j) (ht' j) ha0 hb0 hab⟩
        rw [map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        field_simp
        ring
      · exact ⟨x, ⟨hx, le_antisymm h1 (h2.trans hd)⟩, ht⟩
end

section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.sublevel :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, Good q T → ∀ x ∈ posDual T, ∀ c : ℝ, IsCompact {h | h ∈ poly q ∧ x h ≤ c} := by
  intro E Y _ _ _ q T hG x hx c
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hpoly : IsClosed (poly q) := by
    have e : poly q = ⋂ y, {h : E | 1 ≤ q y h} := by
      ext h
      simp [poly]
    rw [e]
    exact isClosed_iInter fun y => isClosed_le continuous_const (q y).continuous
  have hcl : IsClosed {h : E | h ∈ poly q ∧ x h ≤ c} :=
    hpoly.inter (isClosed_le x.continuous continuous_const)
  have hK : IsCompact (Metric.sphere (0 : E) 1 ∩ T) :=
    (isCompact_sphere 0 1).inter_right hG.closed
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ k ∈ Metric.sphere (0 : E) 1 ∩ T, m ≤ x k := by
    rcases (Metric.sphere (0 : E) 1 ∩ T).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, ?_⟩
      rw [he]
      intro k hk
      exact absurd hk (Set.notMem_empty k)
    · obtain ⟨k0, hk0, hmin⟩ := hK.exists_isMinOn hne x.continuous.continuousOn
      refine ⟨x k0, ?_, fun k hk => hmin hk⟩
      have hk0n : k0 ≠ 0 := by
        intro h0
        have hs := hk0.1
        rw [h0] at hs
        simp at hs
      exact hx k0 hk0.2 hk0n
  apply Metric.isCompact_of_isClosed_isBounded hcl
  refine (Metric.isBounded_closedBall (x := (0 : E)) (r := |c| / m)).subset ?_
  intro h hh
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases h0 : h = 0
  · rw [h0, norm_zero]
    positivity
  · have hn : 0 < ‖h‖ := norm_pos_iff.mpr h0
    have hT : h ∈ T := hG.sub hh.1
    have hk : ‖h‖⁻¹ • h ∈ Metric.sphere (0 : E) 1 ∩ T := by
      refine ⟨?_, hG.smul_mem _ (inv_pos.mpr hn) h hT⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h2 := hm _ hk
    rw [map_smul, smul_eq_mul] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hn.le
    rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at h3
    rw [le_div_iff₀ hm0]
    nlinarith [hh.2, le_abs_self c]
end
