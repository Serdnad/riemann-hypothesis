module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle019
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

private theorem cw_skew {K : Type} [CommRing K] (x : GG (m := 3) (R := K)) (hx : x * x = 1) (hr : x.right = -1)
    (X : Matrix (Fin 3) (Fin 3) K) (hX : x.adFun X = X) :
    (X * x.mat * Jmat (R := K) 3)ᵀ = -(X * x.mat * Jmat (R := K) 3) := by
  have h1 : x.left * theta x.left = 1 := by
    have := congrArg SemidirectProduct.left hx
    simpa [hr, sgnAct_neg_one] using this
  have hX' : x.mat * thetaLie X * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = X := by
    simpa [GG.adFun, hr] using hX
  have h2 : (theta x.left)⁻¹ = x.left := inv_eq_of_mul_eq_one_left h1
  have hg : x.mat = Jmat (R := K) 3 * x.matᵀ * Jmat (R := K) 3 := by
    show ((x.left : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    conv_lhs => rw [← h2]
    rw [theta_inv_val]
    rfl
  have hgJ : x.mat * Jmat (R := K) 3 = Jmat (R := K) 3 * x.matᵀ := by
    conv_lhs => rw [hg]
    rw [Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]
  have hXg : X * x.mat = x.mat * thetaLie X := by
    conv_lhs => rw [← hX']
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    have : ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x.mat = 1 := by
      show ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (x.left : Matrix (Fin 3) (Fin 3) K) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.mul_one]
  calc (X * x.mat * Jmat (R := K) 3)ᵀ = Jmat (R := K) 3 * x.matᵀ * Xᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Jmat_transpose, Matrix.mul_assoc]
    _ = x.mat * Jmat (R := K) 3 * Xᵀ := by rw [hgJ]
    _ = -(X * x.mat * Jmat (R := K) 3) := by
        rw [hXg, thetaLie]
        simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]

private theorem cw_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (x : GG (m := 3) (R := K)) (hx : x * x = 1) (hr : x.right = -1)
    (X : Matrix (Fin 3) (Fin 3) K) (hX : x.adFun X = X) (a : (X * x.mat) 0 0 = 0) (b : (X * x.mat) 0 1 = 0)
    (c : (X * x.mat) 1 0 = 0) : X = 0 := by
  have hs := cw_skew x hx hr X hX
  have e : ∀ i j, (X * x.mat * Jmat (R := K) 3) i j = (X * x.mat) i (Fin.rev j) := by
    intro i j
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat]
  have sk : ∀ i j, (X * x.mat * Jmat (R := K) 3) j i = -(X * x.mat * Jmat (R := K) 3) i j := by
    intro i j
    have := congrFun (congrFun hs i) j
    simpa [Matrix.transpose_apply] using this
  have dg : ∀ i, (X * x.mat * Jmat (R := K) 3) i i = 0 := by
    intro i
    have h := sk i i
    have h' : (2 : K) * (X * x.mat * Jmat (R := K) 3) i i = 0 := by rw [two_mul]; nth_rewrite 1 [h]; ring
    exact (mul_eq_zero.mp h').resolve_left h2
  have m01 : (X * x.mat * Jmat (R := K) 3) 0 1 = 0 := by rw [e]; exact b
  have m02 : (X * x.mat * Jmat (R := K) 3) 0 2 = 0 := by rw [e]; exact a
  have m12 : (X * x.mat * Jmat (R := K) 3) 1 2 = 0 := by rw [e]; exact c
  have m10 : (X * x.mat * Jmat (R := K) 3) 1 0 = 0 := by rw [sk, m01, neg_zero]
  have m20 : (X * x.mat * Jmat (R := K) 3) 2 0 = 0 := by rw [sk, m02, neg_zero]
  have m21 : (X * x.mat * Jmat (R := K) 3) 2 1 = 0 := by rw [sk, m12, neg_zero]
  have hM : X * x.mat * Jmat (R := K) 3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.zero_apply]
    all_goals first
      | exact dg _
      | exact m01
      | exact m02
      | exact m12
      | exact m10
      | exact m20
      | exact m21
  have hY : X * x.mat = 0 := by
    have : X * x.mat = X * x.mat * Jmat (R := K) 3 * Jmat (R := K) 3 := by
      rw [Matrix.mul_assoc (X * x.mat), Jmat_mul_Jmat, Matrix.mul_one]
    rw [this, hM, Matrix.zero_mul]
  have hinv : x.mat * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    show (x.left : Matrix (Fin 3) (Fin 3) K) * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc X = X * x.mat * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = 0 := by rw [hY, Matrix.zero_mul]

theorem UpperTheory.V.Fr.ep_cw :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), ∀ c : F.Γ, c * c = 1 → F.del c = -1 → Module.finrank K (LinearMap.ker (h.ad 0 c - 1)) ≤ 1 ∧ Module.finrank K (LinearMap.ker (h.ad 1 c - 1)) ≤ 2 := by
  intro l _ k _ F K _ h2 B π h c hc hd
  have hx : B.r c * B.r c = 1 := by rw [← map_mul, hc, map_one]
  have hr : (B.r c).right = -1 := by rw [B.nu, hd]
  have hg : ∀ a b, pw a b ≠ 0 → (B.r c).mat a b = 0 := fun a b hab => h.r c a b hab
  have key : ∀ j (v : LinearMap.ker (h.ad j c - 1)),
      (B.r c).adFun ((v : adp K j) : Matrix (Fin 3) (Fin 3) K) = ((v : adp K j) : Matrix (Fin 3) (Fin 3) K) := by
    intro j v
    have hv := v.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
    have := congrArg Subtype.val hv
    simpa [Box.Ev.ad, Box.ad, adRep, GG.ad_apply] using this
  constructor
  · let f : LinearMap.ker (h.ad 0 c - 1) →ₗ[K] K :=
      { toFun := fun v => (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 0
        map_add' := by intro v w; simp [Matrix.add_mul]
        map_smul' := by intro a v; simp [Matrix.smul_mul] }
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have hX : ∀ a b, pw a b ≠ 0 → ((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) a b = 0 :=
        fun a b hab => (v : adp K 0).2 a b hab
      have e01 : (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 1 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hg 0 1 (by decide), hX 0 1 (by decide), hg 2 1 (by decide)]
        ring
      have e10 : (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 1 0 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hX 1 0 (by decide), hg 1 0 (by decide), hX 1 2 (by decide)]
        ring
      have h0 := cw_zero h2 (B.r c) hx hr _ (key 0 v) hv e01 e10
      exact Subtype.ext (Subtype.ext h0)
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
  · let f : LinearMap.ker (h.ad 1 c - 1) →ₗ[K] K × K :=
      { toFun := fun v => ((((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 1,
          (((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 1 0)
        map_add' := by intro v w; simp [Matrix.add_mul]
        map_smul' := by intro a v; simp [Matrix.smul_mul] }
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have hX : ∀ a b, pw a b ≠ 1 → ((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) a b = 0 :=
        fun a b hab => (v : adp K 1).2 a b hab
      have e00 : (((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 0 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hX 0 0 (by decide), hg 1 0 (by decide), hX 0 2 (by decide)]
        ring
      have hv' := Prod.mk.inj hv
      have h0 := cw_zero h2 (B.r c) hx hr _ (key 1 v) e00 hv'.1 hv'.2
      exact Subtype.ext (Subtype.ext h0)
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem z2 (j : ZMod 2) : j = 0 ∨ j = 1 := by revert j; decide

private theorem sg_zero (K : Type) [CommRing K] : sg K 0 = 1 := pow_zero _

private theorem sg_one (K : Type) [CommRing K] : sg K 1 = -1 := pow_one _

private theorem pw_rev (a b : Fin 3) : pw b.rev a.rev = pw a b := by
  revert a b; decide

private theorem zero_of_neg {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {x : K} (h : x = -x) : x = 0 := by
  have : 2 * x = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left h2

private def Dm (K : Type) [CommRing K] : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal fun a => sg K (pq a)

private theorem mem_iff {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K) :
    X ∈ adp K j ↔ Dm K * X = sg K j • (X * Dm K) := by
  have hsq : ∀ y : ZMod 2, sg K y * sg K y = 1 := by
    intro y
    rcases z2 y with rfl | rfl <;> simp [sg_zero, sg_one]
  have hsub : ∀ x y : ZMod 2, sg K (x - y) = sg K x * sg K y := by
    intro x y
    rcases z2 x with rfl | rfl <;> rcases z2 y with rfl | rfl
    · simp [sg_zero]
    · rw [show (0 : ZMod 2) - 1 = 1 from rfl, sg_zero, sg_one, one_mul]
    · rw [show (1 : ZMod 2) - 0 = 1 from rfl, sg_zero, mul_one]
    · rw [show (1 : ZMod 2) - 1 = 0 from rfl, sg_zero, sg_one]
      norm_num
  constructor
  · intro hX
    ext a b
    simp only [Dm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    by_cases hab : pw a b = j
    · rw [← hab, pw_eq, hsub]
      linear_combination (-(sg K (pq a) * X a b)) * hsq (pq b)
    · have h0 : X a b = 0 := hX a b hab
      rw [h0]
      simp
  · intro h
    show ∀ a b, pw a b ≠ j → X a b = 0
    intro a b hab
    have e := congrFun (congrFun h a) b
    simp only [Dm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at e
    have hj : sg K j = -(sg K (pq a) * sg K (pq b)) := by
      rw [pw_eq] at hab
      generalize pq a = x at hab ⊢
      generalize pq b = y at hab ⊢
      rcases z2 x with rfl | rfl <;> rcases z2 y with rfl | rfl <;> rcases z2 j with rfl | rfl <;>
        first | exact absurd (by decide) hab | simp [sg_zero, sg_one]
    rw [hj] at e
    apply zero_of_neg h2
    linear_combination (sg K (pq a)) * e - (X a b + X a b * (sg K (pq b) * sg K (pq b))) * hsq (pq a) -
      X a b * hsq (pq b)

private theorem theta_mem {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K)
    (h : X ∈ adp K j) : thetaLie X ∈ adp K j := by
  show ∀ a b, pw a b ≠ j → thetaLie X a b = 0
  intro a b hab
  have hX : X b.rev a.rev = 0 := h b.rev a.rev (by rw [pw_rev]; exact hab)
  have ht : thetaLie X a b = -X b.rev a.rev := by
    simp only [thetaLie, Matrix.neg_apply, Matrix.mul_apply, Jmat, Matrix.transpose_apply, ite_mul, one_mul,
      zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    rw [Finset.sum_eq_single b.rev]
    · simp
    · intro c _ hc
      rw [if_neg]
      intro hb
      exact hc (by rw [hb, Fin.rev_rev])
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  rw [ht, hX, neg_zero]

private theorem conj_mem {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (g : GL (Fin 3) K)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) ∈ adp K 0) (j : ZMod 2) (Y : Matrix (Fin 3) (Fin 3) K)
    (h : Y ∈ adp K j) :
    (g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∈ adp K j := by
  rw [mem_iff h2] at hg h ⊢
  rw [sg_zero, one_smul] at hg
  have hgi : Dm K * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Dm K := by
    have e := congrArg (fun M => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hg
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left] at e
    exact e.symm
  calc Dm K * ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        = (Dm K * (g : Matrix (Fin 3) (Fin 3) K)) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          simp only [mul_assoc]
    _ = (g : Matrix (Fin 3) (Fin 3) K) * (Dm K * Y) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [hg]
          simp only [mul_assoc]
    _ = (g : Matrix (Fin 3) (Fin 3) K) * (sg K j • (Y * Dm K)) *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [h]
    _ = sg K j • ((g : Matrix (Fin 3) (Fin 3) K) * Y *
          (Dm K * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
          simp only [mul_assoc]
    _ = sg K j • ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          Dm K) := by
          rw [hgi]
          simp only [mul_assoc]

theorem UpperTheory.V.Fr.ep_ev :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), B.Gr σ π → (B.bar O).Ev π := by
  intro l _ k _ F O _ _ _ _ h2O R _ _ _ σ B π hG
  have h2 : (2 : ResidueField O) ≠ 0 := by
    have hu := h2O.map (IsLocalRing.residue O)
    rw [map_ofNat] at hu
    exact hu.ne_zero
  have key : ∀ x : R, ∀ j : ZMod 2, j ≠ 0 → x ∈ evp σ j → res O R x = 0 := by
    intro x j hj hx
    have hj1 : j = 1 := (z2 j).resolve_left hj
    subst hj1
    have e : σ x = sg R 1 * x := hx
    rw [sg_one, neg_one_mul] at e
    apply zero_of_neg h2
    have hm := UpperTheory.V.Alg.res_map (O := O) σ x
    rw [e, map_neg] at hm
    exact hm.symm
  have hr : ∀ s, ((B.bar O).r s).mat ∈ adp (ResidueField O) 0 := by
    intro s
    show ∀ a b, pw a b ≠ 0 → ((B.bar O).r s).mat a b = 0
    intro a b hab
    rw [pw_eq] at hab
    have := key _ _ hab (hG.r s a b)
    simpa [Box.bar, Box.map, GG.mat, GG.map] using this
  refine ⟨hr, ?_, ?_⟩
  · intro v a b hab
    have := key _ _ (sub_ne_zero.mpr hab) (hG.g v a b)
    simpa [Box.bar, Box.map] using this
  · intro j s X hX
    rw [Submodule.mem_comap]
    simp only [Box.ad, adRep, GG.ad, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk, GG.adFun]
    apply conj_mem h2 _ (hr s) j
    split_ifs
    · exact hX
    · exact theta_mem j X hX
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_sub (R : Type) [CommRing R] (i j : ZMod 2) : sg R (i - j) = sg R i * sg R j := by
  have h : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  have s0 : sg R 0 = 1 := pow_zero _
  have s1 : sg R 1 = -1 := pow_one _
  have e : (0 : ZMod 2) - 1 = 1 := by decide
  rcases h i with rfl | rfl <;> rcases h j with rfl | rfl
  · rw [sub_self, s0, one_mul]
  · rw [e, s0, one_mul]
  · rw [sub_zero, s0, mul_one]
  · rw [sub_self, s0, s1, neg_mul_neg, one_mul]

private theorem sg_sq (R : Type) [CommRing R] (i : ZMod 2) : sg R i * sg R i = 1 := by
  rw [← sg_sub, sub_self]
  exact pow_zero _

private def sgM (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal fun a => sg R (α a)

private theorem sgM_sq (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) : sgM R α * sgM R α = 1 := by
  simp only [sgM, Matrix.diagonal_mul_diagonal, sg_sq, Matrix.diagonal_one]

private theorem grM_iff {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) :
    GrM σ α β M ↔ (σ : R →+* R).mapMatrix M = sgM R α * M * sgM R β := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [sgM, sgM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  show σ (M a b) = sg R (α a - β b) * M a b ↔ σ (M a b) = _
  rw [sg_sub, mul_right_comm]

private theorem grM_mul {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β γ : Fin 3 → ZMod 2) (M N : Matrix (Fin 3) (Fin 3) R) (h : GrM σ α β M) (h' : GrM σ β γ N) :
    GrM σ α γ (M * N) := by
  rw [grM_iff] at h h' ⊢
  rw [map_mul, h, h']
  calc sgM R α * M * sgM R β * (sgM R β * N * sgM R γ)
      = sgM R α * M * (sgM R β * sgM R β) * N * sgM R γ := by simp only [Matrix.mul_assoc]
    _ = sgM R α * (M * N) * sgM R γ := by rw [sgM_sq, Matrix.mul_one, Matrix.mul_assoc _ M]

private theorem grM_inv {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (g : GL (Fin 3) R) (h : GrM σ α β (g : Matrix (Fin 3) (Fin 3) R)) :
    GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [grM_iff] at h ⊢
  have h1 : (σ : R →+* R).mapMatrix (g : Matrix (Fin 3) (Fin 3) R) *
      (σ : R →+* R).mapMatrix ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : sgM R β * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * sgM R α *
      (σ : R →+* R).mapMatrix (g : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [h]
    calc _ = sgM R β * (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (sgM R α * sgM R α) *
          (g : Matrix (Fin 3) (Fin 3) R)) * sgM R β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [sgM_sq, Matrix.mul_one, Units.inv_mul, Matrix.mul_one, sgM_sq]
  exact (left_inv_eq_right_inv h2 h1).symm

private theorem grM_J {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) :
    GrM σ pq pq (Jmat (R := R) 3) := by
  intro a b
  unfold Jmat
  split_ifs with e
  · have : pq a - pq b = 0 := by
      subst e
      revert a
      decide
    rw [this]
    show σ 1 = sg R 0 * 1
    rw [map_one, mul_one]
    exact (pow_zero _).symm
  · exact Submodule.zero_mem _

private theorem grM_tr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) (h : GrM σ α β M) : GrM σ β α Mᵀ := by
  intro a b
  have e : σ (M b a) = sg R (α b - β a) * M b a := h b a
  show σ (M b a) = sg R (β a - α b) * M b a
  rw [e, sg_sub, sg_sub, mul_comm (sg R (α b))]

theorem UpperTheory.V.Fr.ep_grm :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R), (∀ α, GrM σ α α 1) ∧ (∀ α β M N, GrM σ α β M → GrM σ α β N → GrM σ α β (M - N)) ∧ (∀ α β γ M N, GrM σ α β M → GrM σ β γ N → GrM σ α γ (M * N)) ∧ (∀ α β (g : GL (Fin 3) R), GrM σ α β (g : Matrix (Fin 3) (Fin 3) R) → GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) ∧ ∀ (e : ℤˣ) (g : GL (Fin 3) R), GrM σ pq pq (g : Matrix (Fin 3) (Fin 3) R) → GrM σ pq pq ((sgnAct (m := 3) (R := R) e g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  intro O R _ _ _ σ
  refine ⟨fun α => ?_, fun α β M N h h' a b => Submodule.sub_mem _ (h a b) (h' a b), grM_mul σ, grM_inv σ,
    fun e g h => ?_⟩
  · rw [grM_iff, map_one, Matrix.mul_one, sgM_sq]
  · rcases Int.units_eq_one_or e with rfl | rfl
    · rwa [sgnAct_one]
    · rw [sgnAct_neg_one, theta_val]
      exact grM_mul σ _ pq _ _ _ (grM_mul σ _ pq _ _ _ (grM_J σ) (grM_tr σ _ _ _ (grM_inv σ _ _ g h))) (grM_J σ)
end
