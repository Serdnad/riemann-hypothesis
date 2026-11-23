module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle219
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle177
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory.GlueBlocks

theorem isIntV_det {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {d : ℕ}
    (X : Matrix (Fin d) (Fin d) C) (hX : ∀ a b, IsIntV v (X a b)) : IsIntV v X.det := by
  let A' : Matrix (Fin d) (Fin d) (PTb.intRing v) := Matrix.of fun a b => ⟨X a b, hX a b⟩
  have hA : (PTb.intRing v).subtype.mapMatrix A' = X := by ext a b; rfl
  have : X.det = (PTb.intRing v).subtype A'.det := by
    rw [RingHom.map_det, hA]
  rw [this]
  exact (A'.det).2

theorem glue_mul_glue_inv : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (ι : Type) (lab : Fin d → ι)
    (S : ι → Finset (Fin d)) (x y : ι → Matrix (Fin d) (Fin d) C),
    (∀ i a, a ∈ S i → lab a = i) →
    (∀ i a b, x i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) → (∀ i a b, y i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) →
    (∀ i a b, IsIntV v (x i a b)) → (∀ i a b, IsIntV v (y i a b)) →
    (∀ i a c, a ∈ S i → c ∈ S i → ∑ b, x i a b * y i b c = if a = c then 1 else 0) →
    (∀ a b, IsIntV v (glue lab S x a b)) ∧ glue lab S x * glue lab S y = 1 ∧
      v (glue lab S x).det = 0 := by
  intro C _ v d ι lab S x y hlab hx hy hxi hyi hinv
  have hint : ∀ z : ι → Matrix (Fin d) (Fin d) C, (∀ i a b, IsIntV v (z i a b)) →
      ∀ a b, IsIntV v (glue lab S z a b) := by
    intro z hz a b
    simp only [glue, Matrix.of_apply]
    split_ifs
    · exact hz _ _ _
    · unfold IsIntV; rw [v.map_one]
    · unfold IsIntV; rw [v.map_zero]; exact le_top
  have hmul : glue lab S x * glue lab S y = 1 := by
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply]
    by_cases ha : a ∈ S (lab a)
    · have hterm : ∀ b, glue lab S x a b * glue lab S y b c = x (lab a) a b * y (lab a) b c := by
        intro b
        simp only [glue, Matrix.of_apply, if_pos ha]
        by_cases hxb : x (lab a) a b = 0
        · rw [hxb, zero_mul, zero_mul]
        · have hb := (hx _ _ _ hxb).2
          have hl : lab b = lab a := hlab _ _ hb
          rw [if_pos (hl ▸ hb), hl]
      simp_rw [hterm]
      by_cases hc : c ∈ S (lab a)
      · exact hinv _ _ _ ha hc
      · have h0 : ∀ b, y (lab a) b c = 0 := by
          intro b; by_contra hne; exact hc (hy _ _ _ hne).2
        simp only [h0, mul_zero, Finset.sum_const_zero]
        rw [if_neg]
        rintro rfl; exact hc ha
    · have hterm : ∀ b, glue lab S x a b * glue lab S y b c =
          if a = b then glue lab S y b c else 0 := by
        intro b
        simp only [glue, Matrix.of_apply, if_neg ha]
        split_ifs <;> simp
      simp_rw [hterm]
      rw [Finset.sum_ite_eq Finset.univ a (fun b => glue lab S y b c), if_pos (Finset.mem_univ _)]
      simp only [glue, Matrix.of_apply, if_neg ha]
  refine ⟨hint x hxi, hmul, ?_⟩
  have hd : (glue lab S x).det * (glue lab S y).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  have h1 : v (glue lab S x).det + v (glue lab S y).det = 0 := by
    rw [← v.map_mul, hd, v.map_one]
  have hX : (0 : WithTop ℝ) ≤ v (glue lab S x).det := isIntV_det v _ (hint x hxi)
  have hY : (0 : WithTop ℝ) ≤ v (glue lab S y).det := isIntV_det v _ (hint y hyi)
  exact ((add_eq_zero_iff_of_nonneg hX hY).1 h1).1

end GlobalTheory.GlueBlocks
end

section

open GlobalTheory.CasimirOrder

namespace GlobalTheory.CasimirOrder

open Matrix

theorem casimir_mul_pos {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O)
    (φ : O →+ ℤ) (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a)
    (_hφc : ∀ a b, φ (a * b) = φ (b * a)) (hφs : ∀ a, φ (s a) = φ a)
    (hp : ∀ a, a ≠ 0 → 0 < φ (s a * a)) :
    ∀ u, u ≠ 0 → 0 < φ (s (casimir (⇑x) s φ * u) * u) := by
  intro u hu
  classical
  set A := (gram (⇑x) s φ).adjugate with hA
  set y : Fin r → O := fun i => x i * u with hy
  set H : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => ((form s φ (y i) (y j) : ℤ) : ℝ) with hHdef
  have key : φ (s (casimir (⇑x) s φ * u) * u) = ∑ i, ∑ j, A i j * form s φ (y j) (y i) := by
    rw [hs]
    unfold casimir

    simp only [map_sum, map_zsmul, hs, hss, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc, form_apply, hy, smul_eq_mul, hA]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc]
  have hnn : ∀ w, 0 ≤ form s φ w w := by
    intro w
    by_cases hw : w = 0
    · simp [hw]
    · exact (hp w hw).le
  have hHpsd : H.PosSemidef := GlobalTheory.gram_posSemidef_of_int_form (form s φ) (form_symm hs hss hφs) hnn y
  have hP : (A.map (Int.cast : ℤ → ℝ)).PosDef := by
    have h1 := posDef_gram x (form s φ) (form_symm hs hss hφs) (fun w hw => by simpa using hp w hw)
    have e : A.map (Int.cast : ℤ → ℝ) = ((Matrix.of fun i j : Fin r => form s φ (x i) (x j)).map (Int.cast : ℤ → ℝ)).adjugate := by
      rw [hA, gram_eq]
      exact (RingHom.map_adjugate (Int.castRingHom ℝ) (Matrix.of fun i j : Fin r => form s φ (x i) (x j)))
    rw [e]
    exact adjugate_posDef h1
  have hy0 : ∃ i, y i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu
    calc u = (∑ i, x.repr 1 i • x i) * u := by rw [x.sum_repr, one_mul]
      _ = ∑ i, x.repr 1 i • y i := by rw [Finset.sum_mul]; simp only [hy, smul_mul_assoc]
      _ = 0 := by simp [h]
  have hH0 : H ≠ 0 := by
    obtain ⟨i, hi⟩ := hy0
    intro h
    have h3 := hp _ hi
    have h2 := congrFun (congrFun h i) i
    rw [hHdef] at h2
    simp only [of_apply, form_apply, Matrix.zero_apply, Int.cast_eq_zero] at h2
    omega
  have ht := trace_mul_pos_real hP hHpsd hH0
  have e : (A.map (Int.cast : ℤ → ℝ) * H).trace = ((∑ i, ∑ j, A i j * form s φ (y j) (y i) : ℤ) : ℝ) := by
    simp [Matrix.trace, Matrix.mul_apply, hHdef]
  rw [e] at ht
  rw [key]
  exact_mod_cast ht

end GlobalTheory.CasimirOrder
end

section

open GlobalTheory.CasimirOrder

namespace GlobalTheory.CasimirOrder

open Matrix

theorem casimir_central : ∀ {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ),
    (∀ a b, s (a * b) = s b * s a) → (∀ a, s (s a) = a) → (∀ a b, φ (a * b) = φ (b * a)) →
    (∀ a, φ (s a) = φ a) → (∀ a, a ≠ 0 → 0 < φ (s a * a)) →
    ∀ a, a * casimir (⇑x) s φ = casimir (⇑x) s φ * a := by
  intro O _ r x s φ hs hss hφc hφs hpos a
  classical
  set b := form s φ with hbdef
  have hb : ∀ u v, b u v = b v u := form_symm hs hss hφs
  set G := gram (⇑x) s φ with hGdef
  have hA : ∀ i j, G.adjugate i j = G.adjugate j i := adjugate_gram_symm hs hss hφs
  have hds : ∀ v, G.det • v = ∑ i, ∑ j, (G.adjugate i j * b (x i) v) • x j :=
    det_smul_eq_sum x b hb
  have hδ : G.det ≠ 0 := by
    have h := (posDef_gram x b hb (fun w hw => hpos w hw)).det_pos
    rw [← Int.cast_det] at h
    exact_mod_cast h.ne'
  haveI : Module.Free ℤ O := Module.Free.of_basis x
  have htf : Function.Injective (fun v : O => G.det • v) := smul_right_injective O hδ
  have hbid : ∀ u v, b u (v * s a) = b v (u * a) := by
    intro u v
    rw [hb v]
    simp only [hbdef, form_apply]
    rw [hs, ← mul_assoc, hφc, ← mul_assoc]
  set A := G.adjugate with hAdef
  set F : Fin r → Fin r → Fin r → Fin r → O :=
    fun i j k l => (A i j * (A k l * b (x k) (x i * s a))) • (s (x l) * x j) with hF
  have key1 : ∀ i j, G.det • (A i j • (a * (s (x i) * x j))) = ∑ k, ∑ l, F i j k l := by
    intro i j
    have e : a * (s (x i) * x j) = s (x i * s a) * x j := by rw [hs, hss, mul_assoc]

    rw [e, smul_comm, show G.det • (s (x i * s a) * x j) = s (G.det • (x i * s a)) * x j by
    rw [map_zsmul, smul_mul_assoc], hds, map_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_

    rw [map_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, smul_mul_assoc, smul_smul]
  have key2 : ∀ p q, G.det • (A p q • (s (x p) * x q * a)) = ∑ i, ∑ j, F i j q p := by
    intro p q
    rw [smul_comm, mul_assoc, ← mul_smul_comm, hds, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_smul, hF, hA p q, ← hbid]
    ring_nf
  apply htf
  simp only
  have L : G.det • (a * casimir (⇑x) s φ) = ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by
    unfold casimir
    rw [← hGdef, ← hAdef, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, key1]
  have R : G.det • (casimir (⇑x) s φ * a) = ∑ l, ∑ k, ∑ i, ∑ j, F i j k l := by
    unfold casimir
    rw [← hGdef, ← hAdef, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_mul_assoc, key2]
  rw [L, R]
  calc ∑ i, ∑ j, ∑ k, ∑ l, F i j k l = ∑ i, ∑ k, ∑ j, ∑ l, F i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, F i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, F i j k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ i, ∑ j, F i j k l := Finset.sum_comm

end GlobalTheory.CasimirOrder
end

section

open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin

theorem foldr_iterate_of_kills {A ι : Type} [Zero A] (ds : ι → A → A) (α : ι → ℕ) (c : A)
    (hc : ∀ i, ds i c = 0) (h0 : ∀ i, ds i 0 = 0) (l : List ι) :
    ((∀ i ∈ l, α i = 0) → l.foldr (fun i g => (ds i)^[α i] g) c = c) ∧
    (¬ (∀ i ∈ l, α i = 0) → l.foldr (fun i g => (ds i)^[α i] g) c = 0) := by
  induction l with
  | nil => exact ⟨fun _ => rfl, fun h => absurd (fun i hi => by simp at hi) h⟩
  | cons j l ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [List.foldr_cons, h j (by simp), ih.1 (fun i hi => h i (by simp [hi]))]
      rfl
    · rw [List.foldr_cons]
      by_cases hl : ∀ i ∈ l, α i = 0
      · rw [ih.1 hl]
        have hj : α j ≠ 0 := by
          intro hj
          apply h
          intro i hi
          rcases List.mem_cons.1 hi with rfl | hi
          · exact hj
          · exact hl i hi
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
        rw [hk, Function.iterate_succ_apply, hc j]
        exact Function.iterate_fixed (h0 j) k
      · rw [ih.2 hl]
        exact Function.iterate_fixed (h0 j) _

theorem taylor_const :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (c : A), (∀ i, ds i c = 0) → taylor ev (fun i => ⇑(ds i)) c = MvPowerSeries.C (ev c) := by
  intro A B _ _ _ n ev ds c hc
  ext α
  rw [MvPowerSeries.coeff_C]
  change (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) α c) = _
  split_ifs with h
  · subst h
    rw [iterOp_zero]
    simp
  · have : iterOp (fun i => ⇑(ds i)) α c = 0 := by
      refine (foldr_iterate_of_kills (fun i => ⇑(ds i)) α c hc (fun i => map_zero _) _).2 ?_
      intro h'
      apply h
      ext i
      exact h' i (List.mem_finRange i)
    rw [this, map_zero, smul_zero]

end GlobalTheory.FormalOrigin
end

section

open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin.TaylorDeriv

theorem foldr_iterate_comm {A ι : Type} (ds : ι → A → A) (h : ∀ a b f, ds a (ds b f) = ds b (ds a f))
    (α : ι → ℕ) (a : ι) (f : A) (l : List ι) :
    l.foldr (fun i g => (ds i)^[α i] g) (ds a f) = ds a (l.foldr (fun i g => (ds i)^[α i] g) f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, ih]
    have : Function.Commute (ds i) (ds a) := fun x => h i a x
    exact (this.iterate_left (α i)) _

theorem foldr_iterate_add_single {A ι : Type} (ds : ι → A → A) (h : ∀ a b f, ds a (ds b f) = ds b (ds a f))
    (α : ι →₀ ℕ) (a : ι) (f : A) (l : List ι) (hl : l.Nodup) (ha : a ∈ l) :
    l.foldr (fun i g => (ds i)^[(α + Finsupp.single a 1 : ι →₀ ℕ) i] g) f
      = ds a (l.foldr (fun i g => (ds i)^[α i] g) f) := by
  classical
  induction l with
  | nil => simp at ha
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons]
    by_cases hi : i = a
    · subst hi
      have : l.foldr (fun j g => (ds j)^[(α + Finsupp.single i 1 : ι →₀ ℕ) j] g) f
          = l.foldr (fun j g => (ds j)^[α j] g) f := by
        apply List.foldr_ext
        intro j hj b
        have : j ≠ i := fun e => hl.1 (e ▸ hj)
        simp [Finsupp.single_apply, this.symm]
      rw [this]
      simp [Function.iterate_succ_apply']
    · have ha' : a ∈ l := by
        rcases List.mem_cons.1 ha with e | e
        · exact absurd e.symm hi
        · exact e
      rw [ih hl.2 ha']
      have e : (α + Finsupp.single a 1 : ι →₀ ℕ) i = α i := by
        simp [Finsupp.single_apply, Ne.symm hi]
      rw [e]
      have : Function.Commute (ds i) (ds a) := fun x => h i a x
      exact (this.iterate_left (α i)) _

theorem iterOp_apply_eq_add_single {A : Type} {n : ℕ} (ds : Fin n → A → A)
    (h : ∀ a b f, ds a (ds b f) = ds b (ds a f)) (α : Fin n →₀ ℕ) (a : Fin n) (f : A) :
    iterOp ds α (ds a f) = iterOp ds (α + Finsupp.single a 1) f := by
  unfold iterOp
  rw [foldr_iterate_comm ds h, foldr_iterate_add_single ds h α a f _ (List.nodup_finRange n) (List.mem_finRange a)]

theorem prod_factorial_add_single {n : ℕ} (α : Fin n →₀ ℕ) (a : Fin n) :
    ∏ i, (((α + Finsupp.single a 1 : Fin n →₀ ℕ) i).factorial : ℚ)
      = (∏ i, ((α i).factorial : ℚ)) * ((α a : ℚ) + 1) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ (fun i => ((α i).factorial : ℚ)) (Finset.mem_univ a)]
  have : ∏ i ∈ Finset.univ.erase a, (((α + Finsupp.single a 1 : Fin n →₀ ℕ) i).factorial : ℚ)
      = ∏ i ∈ Finset.univ.erase a, ((α i).factorial : ℚ) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.ne_of_mem_erase hi
    simp [Finsupp.single_apply, this.symm]
  rw [this]
  simp [Nat.factorial_succ]
  ring

theorem taylor_deriv_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv (R := B) a (taylor ev (fun i => ⇑(ds i)) f) := by
  intro A B _ _ _ n ev ds h a f
  ext α
  rw [MvPowerSeries.coeff_pderiv]
  simp only [MvPowerSeries.coeff_apply, taylor]
  rw [prod_factorial_add_single, ← iterOp_apply_eq_add_single (fun i => ⇑(ds i)) h]
  have e : ((α a : B) + 1) = algebraMap ℚ B ((α a : ℚ) + 1) := by simp
  have hp : ((α a : ℚ) + 1) ≠ 0 := by positivity
  rw [e, mul_comm _ (algebraMap ℚ B _), ← Algebra.smul_def, smul_smul]
  congr 1
  field_simp

end GlobalTheory.FormalOrigin.TaylorDeriv
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

theorem preimage_spMap_comp_eq_top {Y : Scheme.{0}} {V : Y.Opens} {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') {u : Sp S ⟶ Y} (h : u ⁻¹ᵁ V = ⊤) : (spMap g ≫ u) ⁻¹ᵁ V = ⊤ := by
  rw [Scheme.Hom.comp_preimage, h, Scheme.Hom.preimage_top]

theorem chartHom_spMap_comp {Y : Scheme.{0}} (V : Y.Opens) {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') (u : Sp S ⟶ Y) (h : u ⁻¹ᵁ V = ⊤) (h' : (spMap g ≫ u) ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V (spMap g ≫ u) h' x = g (chartHom V u h x) := by
  have e1 : ((spMap g ≫ u).appLE V ⊤ h'.ge).hom x = (spMap g).appTop.hom ((u.appLE V ⊤ h.ge).hom x) := by
    have e : (spMap g).appTop = (spMap g).appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [e]
    exact (congrArg (fun q => q.hom x) (Scheme.Hom.appLE_comp_appLE (spMap g) u V ⊤ ⊤ h.ge le_top)).symm
  have e2 := congrArg (fun q => q.hom ((u.appLE V ⊤ h.ge).hom x))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g))
  simp only [chartHom, RingHom.comp_apply]
  rw [e1]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e2
  exact e2

theorem isCombIn_spMap_comp (Y : Scheme.{0}) (V : Y.Opens) (S S' : Type) [CommRing S] [CommRing S']
    (g : S →+* S') (ι : Type) [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S) (hC : IsCombIn V u c w a) :
    IsCombIn V (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  obtain ⟨hu, hc, hw, hx⟩ := hC
  refine ⟨preimage_spMap_comp_eq_top g hu, preimage_spMap_comp_eq_top g hc,
    fun i => preimage_spMap_comp_eq_top g (hw i), fun x => ?_⟩

  rw [chartHom_spMap_comp V g c hc, chartHom_spMap_comp V g u hu, hx x, map_add (f := _), map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [chartHom_spMap_comp V g (w i) (hw i), map_mul, map_sub]

end GlobalTheory.SecGlue
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory

theorem sep_of_factoring_cover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) := by
  intro R _ C _ C' _ F G H hcov T x hx
  obtain ⟨n, b, hb, h⟩ := hcov T
  refine Desc.sep_std (H := H) (hb := hb) x fun S u ⟨i, hi⟩ ↦ ?_
  obtain ⟨t, v, w, rfl⟩ := h i S u hi
  rw [mp_comp, hx t v, map_zero]

end GlobalTheory
end

section

open GlobalTheory
open scoped Pointwise

namespace GlobalTheory.NakAug

theorem surj : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by
  first
  | exact @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | (apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective ..)

end GlobalTheory.NakAug
end
