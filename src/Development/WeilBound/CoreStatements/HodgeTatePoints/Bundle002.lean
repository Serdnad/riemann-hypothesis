module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

namespace PositivityTheory.HtPt.Pdvr

open Polynomial IsLocalRing

theorem exists_root (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (q : (ResidueField V)[X]) (hm : q.Monic) (hq : Irreducible q) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), Function.Injective f ∧
      ∃ a, (q.map (ResidueField.map f)).IsRoot a := by
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts q).mpr (map_surjective (residue V) residue_surjective q)) hm
  have hPi : Irreducible P :=
    Monic.irreducible_of_irreducible_map (residue V) P hPm (hP ▸ hq)
  have : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime hPi.prime
  have hinj : Function.Injective (AdjoinRoot.of P) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (hdeg ▸ (degree_pos_of_irreducible hq).ne')
  have : Module.Finite V (AdjoinRoot P) := hPm.finite_adjoinRoot
  have hmax : (Ideal.map (AdjoinRoot.of P) (maximalIdeal V)).IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField
    have : Fact (Irreducible (P.map (residue V))) := ⟨hP ▸ hq⟩
    have h1 : IsField (AdjoinRoot (P.map (residue V))) := Field.toIsField _
    exact MulEquiv.isField h1
      (AdjoinRoot.quotEquivQuotMap P (maximalIdeal V)).toRingEquiv.toMulEquiv
  have huniq : ∀ M : Ideal (AdjoinRoot P), M.IsMaximal →
      M = Ideal.map (AdjoinRoot.of P) (maximalIdeal V) := by
    intro M hM
    have h1 : (M.comap (algebraMap V (AdjoinRoot P))).IsMaximal := by
      letI := hM
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (algebraMap V (AdjoinRoot P)) (by
          intro x
          exact Algebra.IsIntegral.isIntegral x) M
    have h2 := eq_maximalIdeal h1
    refine (hmax.eq_of_le hM.ne_top ?_).symm
    rw [Ideal.map_le_iff_le_comap, ← h2]
    exact le_rfl
  have : IsLocalRing (AdjoinRoot P) := .of_unique_max_ideal ⟨_, hmax, huniq⟩
  have hme : maximalIdeal (AdjoinRoot P) = Ideal.map (AdjoinRoot.of P) (maximalIdeal V) :=
    huniq _ inferInstance
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hme' : maximalIdeal (AdjoinRoot P) = Ideal.span {AdjoinRoot.of P π} := by
    rw [hme, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (AdjoinRoot P) := by
    rw [isField_iff_maximalIdeal_eq, hme', Ideal.span_singleton_eq_bot]
    exact fun h => hπ.ne_zero (hinj (h.trans (map_zero _).symm))
  have : IsNoetherianRing (AdjoinRoot P) := IsNoetherianRing.of_finite V _
  have hdvr : IsDiscreteValuationRing (AdjoinRoot P) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot P) hnf).out 1 5).mpr
      (show (maximalIdeal (AdjoinRoot P)).IsPrincipal from ⟨_, hme'⟩)
  have hloc : IsLocalHom (AdjoinRoot.of P) := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have : AdjoinRoot.of P a ∈ maximalIdeal (AdjoinRoot P) :=
      hme ▸ Ideal.mem_map_of_mem _ h
    exact this ha
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, hdvr, AdjoinRoot.of P, hloc, hinj,
    residue _ (AdjoinRoot.root P), ?_⟩
  rw [← hP, Polynomial.map_map, ResidueField.map_comp_residue, IsRoot.def, eval_map,
    ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

theorem exists_splits (n : ℕ) : ∀ (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (q : (ResidueField V)[X]), q.natDegree = n →
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), Function.Injective f ∧
      (q.map (ResidueField.map f)).Splits := by
  induction n with
  | zero =>
    intro V _ _ _ q hq
    exact ⟨V, inferInstance, inferInstance, inferInstance, RingHom.id V, inferInstance,
      Function.injective_id, (Splits.of_natDegree_eq_zero hq).map _⟩
  | succ n ih =>
    intro V _ _ _ q hq
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hq
    have hnu : ¬ IsUnit q := not_isUnit_of_natDegree_pos q (by omega)
    obtain ⟨g, hgm, hgi, hgd⟩ := exists_monic_irreducible_factor q hnu
    obtain ⟨R, _, _, _, f, _, hf, a, ha⟩ := exists_root V g hgm hgi
    have hr : (q.map (ResidueField.map f)).IsRoot a := ha.dvd (Polynomial.map_dvd _ hgd)
    obtain ⟨q', hq'⟩ := dvd_iff_isRoot.mpr hr
    have hq1 : q.map (ResidueField.map f) ≠ 0 := Polynomial.map_ne_zero hq0
    have hd : q'.natDegree = n := by
      have h1 := congrArg natDegree hq'
      have h2 : q' ≠ 0 := by
        rintro rfl
        exact hq1 (by rw [hq', mul_zero])
      rw [natDegree_map, natDegree_mul (X_sub_C_ne_zero a) h2, natDegree_X_sub_C] at h1
      omega
    obtain ⟨S, _, _, _, f', _, hf', hs⟩ := ih R q' hd
    refine ⟨S, inferInstance, inferInstance, inferInstance, f'.comp f, inferInstance,
      hf'.comp hf, ?_⟩
    rw [ResidueField.map_comp, ← Polynomial.map_map, hq', Polynomial.map_mul]
    exact ((Splits.X_sub_C a).map _).mul hs

theorem exists_complete (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), IsAdicComplete (maximalIdeal R) R ∧
      Function.Injective f := by
  classical
  let R := AdicCompletion (maximalIdeal V) V
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let ϖ : R := algebraMap V R π
  have hme : maximalIdeal R = Ideal.span {ϖ} := by
    refine AdicCompletion.maximalIdeal_eq_map.trans ?_
    refine (congrArg (Ideal.map (algebraMap V R)) hπ.maximalIdeal_eq).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  have hreg : ∀ r : V, r ≠ 0 → ∀ x : R, algebraMap V R r * x = 0 → x = 0 := by
    intro r hr x hx
    have h1 : IsSMulRegular R r :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
    apply h1
    change r • x = r • (0 : R)
    rw [smul_zero, Algebra.smul_def, hx]
  have hfac : ∀ x : R, x ≠ 0 → ∃ (n : ℕ) (u : Rˣ), ϖ ^ n * u = x := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ ϖ ^ n ∣ x := by
      by_contra h
      push Not at h
      apply hx
      refine IsHausdorff.haus' (I := maximalIdeal R) x fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hme, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact h n
    have h0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h, pow_zero] at this
      exact this (one_dvd _)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have h1 : ϖ ^ n ∣ x := not_not.mp (Nat.find_min hex (by omega))
    obtain ⟨y, rfl⟩ := h1
    have hy : IsUnit y := by
      by_contra h
      have h2 : y ∈ maximalIdeal R := h
      rw [hme, Ideal.mem_span_singleton] at h2
      have h3 := Nat.find_spec hex
      rw [hn, pow_succ] at h3
      exact h3 (mul_dvd_mul_left _ h2)
    exact ⟨n, hy.unit, rfl⟩
  have : NoZeroDivisors R := ⟨fun {a b} hab => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      obtain ⟨n, u, rfl⟩ := hfac a ha
      have h1 : algebraMap V R (π ^ n) * (u * b) = 0 := by
        rw [map_pow, ← mul_assoc]
        exact hab
      have h2 := hreg _ (pow_ne_zero n hπ.ne_zero) _ h1
      exact (Units.mul_right_eq_zero u).mp h2⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  have hinj : Function.Injective (algebraMap V R) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h
    exact one_ne_zero (hreg a h 1 (by rw [ha, zero_mul]))
  have hϖ0 : ϖ ≠ 0 := fun h => hπ.ne_zero (hinj (h.trans (map_zero _).symm))
  have hϖ : Irreducible ϖ := by
    refine Prime.irreducible ((Ideal.span_singleton_prime hϖ0).mp ?_)
    rw [← hme]
    infer_instance
  have hdvr : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨ϖ, hϖ, fun {x} hx => hfac x hx⟩
  exact ⟨R, inferInstance, inferInstance, hdvr, algebraMap V R, inferInstance,
    (inferInstance : IsAdicComplete (maximalIdeal R) R), hinj⟩

end PositivityTheory.HtPt.Pdvr
end

section

open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Rh

theorem mul_eq_smul_one_symm {R n : Type} [CommRing R] [IsDomain R] [Fintype n] [DecidableEq n]
    {A B : Matrix n n R} {c : R} (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n R)) :
    B * A = c • (1 : Matrix n n R) := by
  have hd : B.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [det_mul, h0, mul_zero, det_smul, det_one, mul_one] at this
    exact pow_ne_zero _ hc this.symm
  have h1 : (B * A - c • (1 : Matrix n n R)) * B = 0 := by
    rw [sub_mul, Matrix.mul_assoc, h]; simp
  have h2 : B.det • (B * A - c • (1 : Matrix n n R)) = 0 := by
    have := congrArg (· * B.adjugate) h1
    simpa only [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.zero_mul]
      using this
  exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hd)

theorem gp_mat : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (g : ℕ) (Ht Bt : Matrix (Fin g) (Fin g ⊕ Fin g) R) (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) (cp : R), cp ≠ 0 → Eᵀ = -E → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E → let φ := algebraMap R C; let intg : (Fin g → C) → Prop := fun w => ∀ k, v (w k) ≤ 1; let hb : Matrix (Fin g ⊕ Fin g) (Fin g) C := ((Eᵀ)⁻¹ * Htᵀ).map φ; v (φ (Matrix.fromRows Ht Bt).det) = v (φ cp) ^ g ∧ (∀ x : Fin g ⊕ Fin g → C, ((Ht.map φ) *ᵥ x = 0 ∧ intg ((Bt.map φ) *ᵥ x)) ↔ ∃ w, intg w ∧ x = (φ cp)⁻¹ • (hb *ᵥ w)) ∧ (∀ w, intg w → ∃ x : Fin g ⊕ Fin g → C, (Ht.map φ) *ᵥ x = w ∧ (Bt.map φ) *ᵥ x = 0) ∧ (∀ l : Fin g ⊕ Fin g → R, cp • l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k)) := by
  intro C _ v R _ _ hv g Ht Bt E cp hcp hE hEu hform φ intg hb
  have : IsDomain R := hv.hom_inj.isDomain _
  have hcp' : φ cp ≠ 0 := fun h => hcp (hv.hom_inj (by rw [map_zero]; exact h))
  have hEt : IsUnit (Eᵀ).det := by rwa [det_transpose]
  set U : Matrix (Fin g ⊕ Fin g) (Fin g) R := -((Eᵀ)⁻¹ * Btᵀ) with hU
  set W : Matrix (Fin g ⊕ Fin g) (Fin g) R := (Eᵀ)⁻¹ * Htᵀ with hW
  have h1 : U * Ht + W * Bt = cp • (1 : Matrix _ _ R) := by
    have : U * Ht + W * Bt = (Eᵀ)⁻¹ * (-(Btᵀ * Ht - Htᵀ * Bt)) := by
      rw [hU, hW, neg_sub, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      abel
    rw [this, hform, ← smul_neg, ← hE, Matrix.mul_smul, nonsing_inv_mul _ hEt]
  have h2 : fromCols U W * fromRows Ht Bt = cp • (1 : Matrix _ _ R) := by
    rw [fromCols_mul_fromRows, h1]
  have h3 := mul_eq_smul_one_symm hcp h2
  rw [fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj] at h3
  obtain ⟨a11, a12, a21, a22⟩ := h3
  rw [smul_zero] at a12 a21
  have hone : ∀ {n : Type} [DecidableEq n], (cp • (1 : Matrix n n R)).map φ = φ cp • (1 : Matrix n n C) := by
    intro n _
    ext i j
    by_cases h : i = j <;> simp [h]
  have b1 := congrArg (·.map φ) h1
  have b11 := congrArg (·.map φ) a11
  have b12 := congrArg (·.map φ) a12
  have b21 := congrArg (·.map φ) a21
  have b22 := congrArg (·.map φ) a22
  simp only [Matrix.map_add _ (map_add φ), Matrix.map_mul, hone, Matrix.map_zero _ (map_zero φ)]
    at b1 b11 b12 b21 b22
  refine ⟨?_, fun x => ⟨fun hx => ⟨_, hx.2, ?_⟩, ?_⟩, fun w _ => ⟨(φ cp)⁻¹ • (U.map φ *ᵥ w), ?_, ?_⟩,
    fun l => ?_⟩
  · have hJ : (fromRows Ht Bt)ᵀ * Matrix.J (Fin g) R * fromRows Ht Bt = cp • E := by
      rw [← hform, Matrix.J, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
      simp [sub_eq_add_neg]
    have hd := congrArg (fun M => v (φ M.det)) hJ
    simp only [det_mul, det_transpose, det_smul, map_mul, map_pow, Fintype.card_sum,
      Fintype.card_fin] at hd
    rw [hv.one_of_isUnit (Matrix.isUnit_det_J (Fin g) R), hv.one_of_isUnit hEu, mul_one, mul_one,
      pow_add] at hd
    exact (mul_self_inj zero_le zero_le).1 hd
  · have := congrArg (· *ᵥ x) b1
    simp only [add_mulVec, ← mulVec_mulVec, hx.1, mulVec_zero, zero_add, smul_mulVec,
      one_mulVec] at this
    change x = (φ cp)⁻¹ • (W.map φ *ᵥ _)
    rw [this, inv_smul_smul₀ hcp']
  · rintro ⟨w, hw, rfl⟩
    change Ht.map φ *ᵥ ((φ cp)⁻¹ • (W.map φ *ᵥ w)) = 0 ∧
      intg (Bt.map φ *ᵥ ((φ cp)⁻¹ • (W.map φ *ᵥ w)))
    rw [mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, b12, b22, zero_mulVec, smul_zero,
      smul_mulVec, one_mulVec, inv_smul_smul₀ hcp']
    exact ⟨rfl, hw⟩
  · rw [mulVec_smul, mulVec_mulVec, b11, smul_mulVec, one_mulVec, inv_smul_smul₀ hcp']
  · rw [mulVec_smul, mulVec_mulVec, b21, zero_mulVec, smul_zero]
  · have : cp • l = (l ᵥ* fromCols U W) ᵥ* fromRows Ht Bt := by
      rw [vecMul_vecMul, h2, vecMul_smul, vecMul_one]
    rw [this, vecMul_eq_sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end PositivityTheory.HtPt.Rh
end

section

open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Rh

theorem epi : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B], (∀ b : B, b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) → Function.Surjective (algebraMap A B) := by
  intro A B _ _ _ _ h
  exact Algebra.isEpi_iff_surjective_algebraMap_of_finite.mp
    ((Algebra.isEpi_iff_forall_one_tmul_eq A B).mpr fun b => (h b).symm)

theorem eq_of_prod_eq {T : Type} [Fintype T] (f g : T → NNReal) (hle : ∀ t, f t ≤ g t)
    (h : ∏ t, f t = ∏ t, g t) (h0 : ∏ t, f t ≠ 0) (t : T) : f t = g t := by
  by_contra hne
  have hpos : ∀ i ∈ Finset.univ, 0 < f i := fun i _ =>
    pos_iff_ne_zero.mpr ((Finset.prod_ne_zero_iff.mp h0) i (Finset.mem_univ i))
  have hlt := Finset.prod_lt_prod₀ hpos (fun i _ => hle i)
    ⟨t, Finset.mem_univ t, lt_of_le_of_ne (hle t) hne⟩
  exact hlt.ne h

theorem grcount : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s := by
  intro T S _ _ a b ha hb x D d r cA cN cO hcN hxD hD hx hA hd hr hdx hOa
  have hab : a * b ≠ 0 := (Nat.mul_pos ha hb).ne'
  have hX : ∏ t, ∏ s, x t s = ∏ t, ∏ s, D t s := by
    rw [hD]
    exact (pow_left_inj₀ (by positivity) (by positivity) hab).mp (hx.trans hA.symm)
  have hX0 : ∏ t, ∏ s, x t s ≠ 0 := by
    intro h0
    rw [h0, zero_pow hab] at hx
    exact pow_ne_zero 2 hcN hx.symm
  have hrow : ∀ t, ∏ s, x t s = ∏ s, D t s :=
    PositivityTheory.HtPt.Rh.eq_of_prod_eq (fun t => ∏ s, x t s) (fun t => ∏ s, D t s)
      (fun t => Finset.prod_le_prod' fun s _ => hxD t s) hX hX0
  have hrow0 : ∀ t, ∏ s, x t s ≠ 0 := fun t =>
    (Finset.prod_ne_zero_iff.mp hX0) t (Finset.mem_univ t)
  have hxD' : ∀ t s, D t s = x t s := fun t s =>
    (PositivityTheory.HtPt.Rh.eq_of_prod_eq (x t) (D t) (hxD t) (hrow t) (hrow0 t) s).symm
  have hO : cO = ∏ t, ∏ s, d t s := by
    rw [hdx]
    apply (pow_left_inj₀ (by positivity) (by positivity) ha.ne').mp
    rw [hOa, ← pow_mul, mul_comm b a, hx]
  have hcol : ∏ s, ∏ t, d t s = ∏ s, r s := by
    rw [hr, hO, Finset.prod_comm]
  have hcol0 : ∏ s, ∏ t, d t s ≠ 0 := by
    rw [Finset.prod_comm, hdx]
    exact pow_ne_zero _ hX0
  exact ⟨hxD', PositivityTheory.HtPt.Rh.eq_of_prod_eq (fun s => ∏ t, d t s) r hd hcol hcol0⟩

end PositivityTheory.HtPt.Rh
end

section

namespace PositivityTheory.HtPt.Gc

theorem dvr_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (h1 : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hdim : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, h1]; rfl
  have hnf : ¬ IsField (Localization.AtPrime q) := fun hf => by
    rw [ringKrullDim_eq_zero_of_isField hf] at hdim
    exact zero_ne_one hdim
  have hic : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hk : Ring.KrullDimLE 1 (Localization.AtPrime q) := by
    rw [Ring.krullDimLE_iff, hdim]; rfl
  have hD : IsDedekindDomain (Localization.AtPrime q) := by
    have : Ring.DimensionLEOne (Localization.AtPrime q) :=
      ⟨fun {P} hP hP' => (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk) P hP hP'⟩
    exact {}
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 1 3).2 hD

end PositivityTheory.HtPt.Gc
end
