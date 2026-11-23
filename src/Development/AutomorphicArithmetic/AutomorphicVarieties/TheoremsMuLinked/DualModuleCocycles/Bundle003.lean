module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem lc_mat {Γ K : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) K)
    (h : ∀ a b, IsLocallyConstant fun g => f g a b) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : ∀ a b, ∀ᶠ y in nhds x, f y a b = f x a b := fun a b =>
    (IsLocallyConstant.iff_eventually_eq _).mp (h a b) x
  filter_upwards [Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr (hx a)] with y hy
  ext a b
  exact hy a b

theorem UpperTheory.V.Th.Coc.lc :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c c₀ : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X), (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → IsLift x δ (repR x ρ) τ c d → (IsLocallyConstant fun g => bar X (ρ g)) → (IsLocallyConstant fun g => δ (τ (MonoidAlgebra.single g 1))) → IsLocallyConstant fun g => c₀ • d (MonoidAlgebra.single g 1) := by
  intro O R X _ _ _ _ _ n G _ _ _ x δ ρ τ c c₀ d hspan hL hρ hτ
  have hsingle : ∀ g : G, repR x ρ (MonoidAlgebra.single g 1) = ρ g := by
    intro g
    rw [repR_single, map_one, one_smul]
  have hmulD : ∀ g h : G, d (MonoidAlgebra.single (g * h) 1) =
      d (MonoidAlgebra.single g 1) * bar X (ρ h) + bar X (ρ g) * d (MonoidAlgebra.single h 1) := by
    intro g h
    have e := hL.mul (MonoidAlgebra.single g 1) (MonoidAlgebra.single h 1)
    rw [MonoidAlgebra.single_mul_single, mul_one, hsingle, hsingle] at e
    exact e
  have hgen : ∀ h : G, IsLocallyConstant fun g => (d (MonoidAlgebra.single g 1) * bar X (ρ h)).trace := by
    intro h
    have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (ρ h)).trace) =
        fun g => c • δ (τ (MonoidAlgebra.single (g * h) 1)) -
          (bar X (ρ g) * d (MonoidAlgebra.single h 1)).trace := by
      funext g
      rw [← hL.tr, hmulD, Matrix.trace_add, add_sub_cancel_right]
    rw [e]
    refine IsLocallyConstant.sub ?_ ?_
    · exact (hτ.comp_continuous (continuous_mul_const h)).comp (fun y => c • y)
    · exact hρ.comp fun M => (M * d (MonoidAlgebra.single h 1)).trace
  have hspanLC : ∀ Z ∈ Submodule.span O (Set.range ρ),
      IsLocallyConstant fun g => (d (MonoidAlgebra.single g 1) * bar X Z).trace := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨h, rfl⟩ := hZ
      exact hgen h
    | zero =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (0 : Matrix (Fin n) (Fin n) O)).trace) =
          fun _ => 0 := by
        funext g
        have hb : bar X (0 : Matrix (Fin n) (Fin n) O) = 0 := by
          ext i j
          simp [bar]
        rw [hb, Matrix.mul_zero, Matrix.trace_zero]
      rw [e]
      exact IsLocallyConstant.const 0
    | add Z W _ _ hZ hW =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (Z + W)).trace) =
          fun g => (d (MonoidAlgebra.single g 1) * bar X Z).trace +
            (d (MonoidAlgebra.single g 1) * bar X W).trace := by
        funext g
        have hb : bar X (Z + W) = bar X Z + bar X W := by
          ext i j
          simp [bar]
        rw [hb, Matrix.mul_add, Matrix.trace_add]
      rw [e]
      exact hZ.add hW
    | smul k Z _ hZ =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (k • Z)).trace) =
          fun g => algebraMap O X k * (d (MonoidAlgebra.single g 1) * bar X Z).trace := by
        funext g
        have hb : bar X (k • Z) = algebraMap O X k • bar X Z := by
          ext i j
          simp [bar, Matrix.smul_apply, smul_eq_mul]
        rw [hb, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      rw [e]
      exact hZ.comp fun y => algebraMap O X k * y
  apply lc_mat
  intro a b
  have key : ∀ M : Matrix (Fin n) (Fin n) X,
      (M * bar X (c₀ • Matrix.of fun i j => if i = b ∧ j = a then (1:O) else 0)).trace = (c₀ • M) a b := by
    intro M
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, bar, Matrix.map_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_ite, smul_zero, smul_eq_mul, mul_one, ite_and]
    simp only [apply_ite (algebraMap O X), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Algebra.smul_def, mul_one]
    rw [mul_comm]
  have e : (fun g => (c₀ • d (MonoidAlgebra.single g 1)) a b) =
      fun g => (d (MonoidAlgebra.single g 1) *
        bar X (c₀ • Matrix.of fun i j => if i = b ∧ j = a then (1:O) else 0)).trace := by
    funext g
    rw [key]
  rw [e]
  exact hspanLC _ (hspan _)
end

section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem k0 {O G : Type} [CommRing O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O)
    (hs : ∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) (X : Type) [CommRing X] [Algebra O X]
    (W : Matrix (Fin n) (Fin n) X) (h : ∀ g, (bar X (ρ g) * W).trace = 0) : c₀ • W = 0 := by
  have key : ∀ M ∈ Submodule.span O (Set.range ρ), (bar X M * W).trace = 0 := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact h g
    | zero => simp [bar]
    | add x y _ _ hx hy =>
      have e : bar X (x + y) = bar X x + bar X y := by
        ext i j
        simp [bar]
      rw [e, add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul a x _ hx =>
      have e : bar X (a • x) = a • bar X x := by
        ext i j
        simp only [bar]
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul,
          Algebra.smul_def]
      rw [e, Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  ext i j
  have t := key _ (hs (Matrix.single j i 1))
  have e : bar X (c₀ • Matrix.single j i (1 : O)) = Matrix.single j i (algebraMap O X c₀) := by
    ext a b
    simp [bar, Matrix.single_apply]
    split_ifs <;> simp
  rw [e] at t
  simpa [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Algebra.smul_def] using t

theorem UpperTheory.V.Th.Coc.kill0 :
    ∀ {O G : Type} [CommRing O] [IsDomain O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O), c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → (∀ W : Matrix (Fin n) (Fin n) O, (∀ g, (ρ g * W).trace = 0) → W = 0) ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (W : Matrix (Fin n) (Fin n) X), (∀ g, (bar X (ρ g) * W).trace = 0) → c₀ • W = 0 := by
  intro O G _ _ _ n ρ c₀ hc hs
  refine ⟨fun W hW => ?_, fun X _ _ W hW => k0 ρ c₀ hs X W hW⟩
  have hb : ∀ g, (bar O (ρ g) * W).trace = 0 := by
    intro g
    have e : bar O (ρ g) = ρ g := by
      ext i j
      simp [bar]
    rw [e]
    exact hW g
  have := k0 ρ c₀ hs O W hb
  ext i j
  have := congrFun (congrFun this i) j
  simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left hc
end

section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem tri_pow {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O)
    (h : ∀ a b, b < a → u a b = 0) (hd : ∀ i, u i i = α i) (k : ℕ) :
    (∀ a b, b < a → (u ^ k) a b = 0) ∧ ∀ i, (u ^ k) i i = α i ^ k := by
  induction k with
  | zero =>
    refine ⟨fun a b hab => ?_, fun i => by simp⟩
    simp [Matrix.one_apply_ne hab.ne']
  | succ k ih =>
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      rcases lt_or_ge c a with hc | hc
      · rw [ih.1 a c hc, zero_mul]
      · rw [h c b (lt_of_lt_of_le hab hc), mul_zero]
    · rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [ih.2, hd, pow_succ]
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · rw [ih.1 i c hc, zero_mul]
        · rw [h c i hc, mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi

private theorem tri_aeval {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O)
    (h : ∀ a b, b < a → u a b = 0) (hd : ∀ i, u i i = α i) (p : Polynomial O) :
    (∀ a b, b < a → (Polynomial.aeval u p) a b = 0) ∧ ∀ i, (Polynomial.aeval u p) i i = p.eval (α i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [map_add (f := _), Matrix.add_apply, hp.1 a b hab, hq.1 a b hab, add_zero]
    · rw [map_add (f := _), Matrix.add_apply, hp.2, hq.2, Polynomial.eval_add]
  | monomial k c =>
    have hk := tri_pow u α h hd k
    rw [Polynomial.aeval_monomial, ← Algebra.smul_def]
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [Matrix.smul_apply, hk.1 a b hab, smul_zero]
    · rw [Matrix.smul_apply, hk.2, Polynomial.eval_monomial, smul_eq_mul]

theorem UpperTheory.V.Th.Coc.flagB :
    ∀ {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O), (∀ a b, b < a → u a b = 0) → (∀ i, u i i = α i) → (∀ a b, b < a → kS u α a b = 0 ∧ kT u α a b = 0) ∧ ∀ i, kS u α i i = ∏ j ∈ Finset.univ.erase i, (α i - α j) ∧ kT u α i i = ∏ j ∈ Finset.univ.erase i, (α i - α j) := by
  intro O _ n u α h hd
  have hev : ∀ i k, (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (α j))).eval (α k) =
      ∏ j ∈ Finset.univ.erase i, (α k - α j) := by
    intro i k
    simp [Polynomial.eval_prod]
  refine ⟨fun a b hab => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · exact (tri_aeval u α h hd _).1 a b hab
  · exact (tri_aeval u α h hd _).1 a b hab
  · show kEl u α i i i = _
    rw [kEl, (tri_aeval u α h hd _).2 i, hev]
  · show kEl u α i i i = _
    rw [kEl, (tri_aeval u α h hd _).2 i, hev]
end

section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]

end

theorem UpperTheory.V.Th.Coc.starFacts :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R : Type} [CommRing O] [Algebra ℤ_[l] O] [CommRing R] [Algebra O R] {n : ℕ}, (∀ a b, F.star O R n (a * b) = F.star O R n b * F.star O R n a) ∧ (∀ a b, F.star O R n (a + b) = F.star O R n a + F.star O R n b) ∧ (∀ (r : R) a, F.star O R n (r • a) = r • F.star O R n a) ∧ (∀ a, F.star O R n (F.star O R n a) = a) ∧ (∀ g, F.star O R n (MonoidAlgebra.single g 1) = MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap O R ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O))) ∧ ∀ (x : R →ₐ[O] O) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O), F.IsForm O n ρ P → ∀ a, repR x (mat ρ) (F.star O R n a) = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (repR x (mat ρ) a)ᵀ * (P : Matrix (Fin n) (Fin n) O) := by
  intro l _ F O R _ _ _ _ n
  have hmul : ∀ a b, F.star O R n (a * b) = F.star O R n b * F.star O R n a := by
    intro a b
    simp [GFrame.star, map_mul]
  have hadd : ∀ a b, F.star O R n (a + b) = F.star O R n a + F.star O R n b := by
    intro a b
    simp [GFrame.star, map_add (f := _)]
  have hsmul : ∀ (r : R) a, F.star O R n (r • a) = r • F.star O R n a := by
    intro r a
    simp [GFrame.star, map_smul]
  have hzero : F.star O R n 0 = 0 := by
    simp [GFrame.star]
  have hsingle : ∀ g (r : R), F.star O R n (MonoidAlgebra.single g r)
      = MonoidAlgebra.single (F.conj g)⁻¹ (r * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
    intro g r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hepsR : ∀ g (k : ℤ), ((F.eps O R g ^ k : Rˣ) : R)
      = algebraMap O R ((F.eps O O g ^ k : Oˣ) : O) := by
    intro g k
    have h : F.eps O R g = Units.map (algebraMap O R).toMonoidHom (F.eps O O g) := by
      ext
      simp [GFrame.eps, pushCh]
    rw [h, ← map_zpow]
    rfl
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  have hcc : ∀ g, F.conj (F.conj g) = g := by
    intro g
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = g
    rw [hci, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]
  have hepsc : ∀ g, F.eps O R (F.conj g) = F.eps O R g := by
    intro g
    have h : F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
      show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = _
      rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_assoc, mul_inv_cancel, mul_one]
    simp [GFrame.eps, pushCh, h]
  refine ⟨hmul, hadd, hsmul, ?_, ?_, ?_⟩
  · intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => rw [hzero, hzero]
    | add f g hf hg => rw [hadd, hadd, hf, hg]
    | single g r =>
      rw [hsingle, hsingle]
      simp only [map_inv, hcc, inv_inv, hepsc]
      congr 1
      rw [mul_assoc, ← Units.val_mul, _root_.inv_zpow', ← _root_.zpow_add, add_neg_cancel, _root_.zpow_zero,
        Units.val_one, mul_one]
  · intro g
    rw [hsingle, one_mul, hepsR]
  · intro x ρ P hP a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp [hzero]
    | add f g hf hg =>
      rw [hadd, map_add (f := _), hf, hg, map_add (f := _), transpose_add, Matrix.mul_add, Matrix.add_mul]
    | single g r =>
      have key : ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
          = ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O) • mat ρ (F.conj g)⁻¹ := by
        have h := hP g
        have hm : mat ρ (F.conj g) * mat ρ (F.conj g)⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel, map_one]
        calc ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
            = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
              * (mat ρ (F.conj g) * mat ρ (F.conj g)⁻¹) := by rw [hm, mul_one]
          _ = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)
              * ((mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O) * mat ρ (F.conj g)) * mat ρ (F.conj g)⁻¹ := by
            simp only [mul_assoc]
          _ = _ := by
            rw [h, Matrix.mul_smul, Units.inv_mul, Matrix.smul_mul, one_mul]
      rw [hsingle, repR_single, repR_single, map_mul, hepsR, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        transpose_smul, Matrix.mul_smul, Matrix.smul_mul, key, mul_smul]
end

section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.liftConj :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ ρ' : E →+* Matrix (Fin n) (Fin n) O) (τ : E → R) (c : O) (Q : GL (Fin n) O) (d : E →+ Matrix (Fin n) (Fin n) X), (∀ a, ρ a = (Q : Matrix (Fin n) (Fin n) O) * ρ' a * ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) → IsLift x δ ρ' τ c d → ∃ d' : E →+ Matrix (Fin n) (Fin n) X, IsLift x δ ρ τ c d' ∧ ∀ a, d' a = bar X (Q : Matrix (Fin n) (Fin n) O) * d a * bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
  intro O R X _ _ _ _ _ n E _ _ x δ ρ ρ' τ c Q d hρ hL
  have hbm : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B := by
    intro A B
    simp [bar, Matrix.map_mul]
  have hbar1 : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := by
    simp [bar]
  have hl : bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * bar X (Q : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← hbm, Units.inv_mul, hbar1]
  have hbρ : ∀ a, bar X (ρ a) = bar X (Q : Matrix (Fin n) (Fin n) O) * bar X (ρ' a) * bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
    intro a
    rw [hρ, hbm, hbm]
  set P := bar X (Q : Matrix (Fin n) (Fin n) O) with hPdef
  set Pi := bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) with hPidef
  refine ⟨AddMonoidHom.mk' (fun a => P * d a * Pi) (fun a b => by rw [map_add (f := _), mul_add, add_mul]), ?_, fun a => rfl⟩
  constructor
  · intro a b
    simp only [AddMonoidHom.mk'_apply]
    rw [hL.mul, hbρ, hbρ]
    have e1 : P * d a * Pi * (P * bar X (ρ' b) * Pi) = P * (d a * bar X (ρ' b)) * Pi := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pi P, hl, Matrix.one_mul]
    have e2 : P * bar X (ρ' a) * Pi * (P * d b * Pi) = P * (bar X (ρ' a) * d b) * Pi := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pi P, hl, Matrix.one_mul]
    rw [e1, e2, mul_add, add_mul]
  · intro r a
    simp only [AddMonoidHom.mk'_apply]
    rw [hL.smul, hbρ, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  · intro a
    simp only [AddMonoidHom.mk'_apply]
    rw [Matrix.trace_mul_cycle, hl, Matrix.one_mul, hL.tr]
end
