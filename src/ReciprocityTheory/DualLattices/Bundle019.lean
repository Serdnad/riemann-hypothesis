module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import ReciprocityTheory.DualLattices.AinfTower
public import ReciprocityTheory.DualLattices.Bundle018
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.DualLattices.ExistsFamilyValuationDetEqOne
public import ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq
public import ReciprocityTheory.DualLattices.Bundle017
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import ReciprocityTheory.DualLattices.Bundle016

@[expose] public section

section

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀) {p : ℕ}

lemma tw_πr (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.π n).comp (Tw.r' n) = (Tw.r n).comp (Tw.π (n + 1)) := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  exact (Tw.r_π n x).symm

lemma tw_qr (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.r n).comp (Tw.q (n + 1)) = Tw.q n := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  exact Tw.r_q n x

lemma lift_down (Tw : ATowerL R₀ p) (n : ℕ) (τ1 : B.G Tw.O) (th1 : B.G (Tw.R' (n + 1)))
    (w1 : B.gg ⊗[R₀] (Tw.R' (n + 1) : Type u)) (h1 : B.map (Tw.π (n + 1)) th1 = B.map (Tw.q (n + 1)) τ1)
    (h2 : (p ^ (n + 1 + 1)) • th1 = B.tg (Tw.π (n + 1)) (Tw.sqZero (n + 1))
      (TensorProduct.map LinearMap.id (ξmul (Tw.π (n + 1)) (Tw.ξ (n + 1)) (Tw.ξ_mem (n + 1))) w1)) :
    B.map (Tw.π n) (p • B.map (Tw.r' n) th1) = B.map (Tw.q n) (p • τ1) ∧
    (p ^ (n + 1)) • (p • B.map (Tw.r' n) th1) = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n))
        (LinearMap.lTensor B.gg (Tw.r' n).1.toLinearMap w1)) ∧
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (LinearMap.lTensor B.gg (Tw.r' n).1.toLinearMap w1) =
      LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap
        (LinearMap.lTensor B.gg (Tw.π (n + 1)).1.toLinearMap w1) := by
  have e1 : B.map (Tw.π n) (B.map (Tw.r' n) th1) = B.map (Tw.q n) τ1 := by
    rw [← B.map_comp, tw_πr Tw n, B.map_comp, h1, ← B.map_comp, tw_qr Tw n]
  have hf : ∀ a ∈ (Tw.π (n + 1)).ker, (Tw.r' n).1.toLinearMap a ∈ (Tw.π n).ker := by
    intro a ha
    simp only [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
    rw [AlgHom.toLinearMap_apply, ← Tw.r_π n a, ha, map_zero]
  have hcomm : ((Tw.r' n).1.toLinearMap.restrict hf) ∘ₗ
      ξmul (Tw.π (n + 1)) (Tw.ξ (n + 1)) (Tw.ξ_mem (n + 1)) =
      ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) ∘ₗ (Tw.r' n).1.toLinearMap := by
    refine LinearMap.ext fun a => Subtype.ext ?_
    show (Tw.r' n).1 (Tw.ξ (n + 1) * a) = Tw.ξ n * (Tw.r' n).1 a
    rw [map_mul, Tw.r'_ξ n]
  have h3 : (Tw.π n).1.toLinearMap ∘ₗ (Tw.r' n).1.toLinearMap =
      (Tw.r n).1.toLinearMap ∘ₗ (Tw.π (n + 1)).1.toLinearMap :=
    LinearMap.ext fun a => (Tw.r_π n a).symm
  refine ⟨by rw [map_nsmul, map_nsmul, e1], ?_, ?_⟩
  · rw [smul_smul, ← pow_succ, ← map_nsmul, h2,
      ← B.tg_nat (Tw.π (n + 1)) (Tw.π n) (Tw.sqZero (n + 1)) (Tw.sqZero n) (Tw.r' n) hf]
    have h := congrArg (fun f => LinearMap.lTensor B.gg f w1) hcomm
    simp only [LinearMap.lTensor_comp, LinearMap.comp_apply] at h
    exact congrArg (B.tg (Tw.π n) (Tw.sqZero n)) h
  · have h := congrArg (fun f => LinearMap.lTensor B.gg f w1) h3
    simpa only [LinearMap.lTensor_comp, LinearMap.comp_apply] using h

def coordK (M : Type u) [AddCommGroup M] [Module R₀ M] (k : Module.Free.ChooseBasisIndex R₀ B.gg) :
    B.gg ⊗[R₀] M →ₗ[R₀] M :=
  (TensorProduct.lid R₀ M).toLinearMap ∘ₗ LinearMap.rTensor M ((Module.Free.chooseBasis R₀ B.gg).coord k)

lemma coordK_lTensor {M M' : Type u} [AddCommGroup M] [Module R₀ M] [AddCommGroup M'] [Module R₀ M']
    (f : M →ₗ[R₀] M') (k : Module.Free.ChooseBasisIndex R₀ B.gg) (x : B.gg ⊗[R₀] M) :
    B.coordK M' k (LinearMap.lTensor B.gg f x) = f (B.coordK M k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul g m => simp [coordK]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

lemma sum_coordK (M : Type u) [AddCommGroup M] [Module R₀ M] (x : B.gg ⊗[R₀] M) :
    ∑ k, (Module.Free.chooseBasis R₀ B.gg k) ⊗ₜ[R₀] B.coordK M k x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul g m =>
    simp only [coordK, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul, Module.Basis.coord_apply]
    simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul, Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

lemma exists_lim_tensor (Tw : ATowerL R₀ p) (wb : ∀ n, B.gg ⊗[R₀] (Tw.R n : Type u))
    (hwb : ∀ n, LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap (wb (n + 1)) = wb n) :
    ∃ bt : B.gg ⊗[R₀] (Tw.O : Type u), ∀ n, LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap bt = wb n := by
  choose a ha using fun k => Tw.complete (fun n => B.coordK (Tw.R n) k (wb n)) (fun n => by
    rw [← hwb n, B.coordK_lTensor]
    rfl)
  refine ⟨∑ k, (Module.Free.chooseBasis R₀ B.gg k) ⊗ₜ[R₀] a k, fun n => ?_⟩

  rw [map_sum]
  simp only [LinearMap.lTensor_tmul]
  conv_rhs => rw [← B.sum_coordK _ (wb n)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← ha k n]
  rfl

end BX

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem quotient_out_add_coe (K : AddSubgroup N) (q : N ⧸ K) (k : K) :
    ((q.out + k : N) : N ⧸ K) = q := by
  rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq',
    (QuotientAddGroup.eq_zero_iff (k : N)).mpr k.2, add_zero]

def quotientProdSubgroupEquiv (K : AddSubgroup N) : (N ⧸ K) × K ≃ N where
  toFun p := p.1.out + p.2
  invFun x := ((x : N ⧸ K),
    ⟨-((x : N ⧸ K).out) + x, QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)⟩)
  left_inv := by
    rintro ⟨q, k⟩
    refine Prod.ext (quotient_out_add_coe K q k) (Subtype.ext ?_)
    show -((((q.out + k : N)) : N ⧸ K).out) + (q.out + k) = k
    rw [quotient_out_add_coe K q k]
    abel
  right_inv := by
    intro x
    show (x : N ⧸ K).out + (-((x : N ⧸ K).out) + x) = x
    abel

private theorem valuation_det_le_one_of_integral_entries (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (E : Matrix X X C) (hE : ∀ i j, ∃ r : R, algebraMap R C r = E i j) : v E.det ≤ 1 := by
  choose M hM using hE
  have hEM : E = (Matrix.of M).map (algebraMap R C) := by
    ext i j
    exact (hM i j).symm
  rw [hEM, det_map_algebraMap]
  exact hv.map_le_one _

theorem hasColength_eq_pow_mul_pow (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)] :
    ∀ c cB cK, HasColen R v AA.carrier c →
      HasColen R v (AA.carrier.comap (pullQ (R := R) K)) cB →
      HasColen R v (AA.carrier.map (resK (R := R) K)) cK →
      c = cB ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) := by
  intro c cB cK hc hcB hcK
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hfA, hfu⟩ := exists_coset_basis hv AA K
  obtain ⟨g, hgA, hgdet⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  obtain ⟨P, hP, rfl⟩ := hc
  obtain ⟨Q, hQ, rfl⟩ := hcB
  obtain ⟨β', hβ', rfl⟩ := hcK
  obtain ⟨P0, hP0, hAP0⟩ := AA.lat
  have hint : ∀ {F : N → C}, F ∈ AA.carrier → ∀ x, ∃ r : R, algebraMap R C r = F x :=
    fun hF x => AA.le_int hF x
  have hK : v β'.det = v β.det := valuation_det_eq_of_span_eq_alt hv hβ (hAK.symm.trans hβ')
  have hmm1 : ∀ x, v (h3mm K β f x).det = 1 := by
    intro x
    have hdec : ∀ l, ∃ e : K → N ⧸ K → C,
        (∀ j, e j ∈ AA.carrier.comap (pullQ (R := R) K)) ∧
          g l = ∑ j, pullQ (R := R) K (e j) * f j := by
      intro l
      obtain ⟨b, ⟨hb, hgb⟩, -⟩ := hfu (g l) (hgA l)
      choose e he hbe using fun j => Submodule.mem_map.mp (hb j)
      refine ⟨e, he, ?_⟩
      rw [hgb]
      exact Finset.sum_congr rfl fun j _ => by rw [hbe j]
    choose e he hge using hdec
    let Bx : Matrix K K C := Matrix.of fun l j => e l j (x : N ⧸ K)
    have hmul : h3mm K β g x = Bx * h3mm K β f x := by
      ext l m
      simp only [h3mm, Matrix.of_apply, Matrix.mul_apply, Bx]
      rw [hge l, cosetCoordinates_sum, Finset.sum_apply]
      simp only [cosetCoordinates_pullbackQuotient_mul, Pi.smul_apply, smul_eq_mul]
    have hB1 : v Bx.det ≤ 1 := valuation_det_le_one_of_integral_entries hv Bx fun l j => by
      obtain ⟨r, hr⟩ := hint (Submodule.mem_comap.mp (he l j)) x
      exact ⟨r, hr⟩
    have hF1 : v (h3mm K β f x).det ≤ 1 := valuation_det_le_one_of_integral_entries hv _ fun j m =>
      hint (cosetCoordinates_mem AA K β hβ hAK (hfA j) m) x
    have h := hgdet x
    rw [hmul, Matrix.det_mul, map_mul, mul_comm] at h
    exact eq_one_of_le_one_of_mul_eq_one hF1 hB1 h
  let e : K × (N ⧸ K) ≃ N := (Equiv.prodComm _ _).trans (quotientProdSubgroupEquiv K)
  have he_apply : ∀ p : K × (N ⧸ K), e p = p.2.out + p.1 := fun p => rfl
  let Φ : Matrix N N C := fun x n => Q (x : N ⧸ K) (e.symm n).2 * f (e.symm n).1 x
  have hspan : AA.carrier = Submodule.span R (Set.range fun n x => Φ x n) := by
    apply le_antisymm
    · intro G hG
      obtain ⟨b, ⟨hb, hGb⟩, -⟩ := hfu G hG
      rw [hGb]
      refine sum_mem fun j _ => ?_
      obtain ⟨b', hb', hbb'⟩ := Submodule.mem_map.mp (hb j)
      rw [hQ] at hb'
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hb'

      rw [← hbb', ← hr, map_sum, Finset.sum_mul]
      refine sum_mem fun s _ => ?_
      rw [map_smul, smul_mul_assoc]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e (j, s), ?_⟩)
      funext x
      simp only [Φ, Equiv.symm_apply_apply]
      rfl
    · rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      have h1 : (fun q : N ⧸ K => Q q (e.symm n).2) ∈ AA.carrier.comap (pullQ (R := R) K) := by
        rw [hQ]
        exact Submodule.subset_span ⟨_, rfl⟩
      exact AA.mul_mem _ _ h1 (hfA _)
  have hdetΦ : v Φ.det = v Q.det ^ Fintype.card K * v β.det ^ Fintype.card (N ⧸ K) := by
    rw [← Matrix.det_submatrix_equiv_self e Φ]
    have hblk : Φ.submatrix e e = Matrix.blockDiagonal (fun q : N ⧸ K =>
        β * (h3mm K β f q.out)ᵀ) * Matrix.kroneckerMap (· * ·) (1 : Matrix K K C) Q := by
      ext ⟨k, q⟩ ⟨j, s⟩
      show Q ((e (k, q) : N) : N ⧸ K) (e.symm (e (j, s))).2 * f (e.symm (e (j, s))).1 (e (k, q)) = _
      rw [Equiv.symm_apply_apply, he_apply]
      dsimp only
      rw [quotient_out_add_coe K q k, cosetCoordinates_expand K β hβ (f j) q.out k, Matrix.mul_apply]
      simp only [Fintype.sum_prod_type, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, ite_mul, zero_mul, mul_ite, mul_one, mul_zero, one_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
      conv_rhs => rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp only [eq_self_iff_true, if_true, Finset.sum_ite_eq, Finset.mem_univ]
      rw [mul_comm]
      rfl
    have hq : ∀ q : N ⧸ K, v (β * (h3mm K β f q.out)ᵀ).det = v β.det := by
      intro q
      rw [Matrix.det_mul, Matrix.det_transpose, map_mul, hmm1, mul_one]
    rw [hblk, Matrix.det_mul, Matrix.det_blockDiagonal, Matrix.det_kronecker, Matrix.det_one,
      one_pow, one_mul, map_mul, map_prod, map_pow]
    simp only [hq, Finset.prod_const, Finset.card_univ]
    ring
  have h1 := valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hP)
  have h2 := valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hspan)
  rw [h1, ← h2, hdetΦ, hK]

end ReciprocityTheory.PGsh.L2
end
end

section

noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

namespace Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)

def r'Alg (n : ℕ) : R'n p O ε (n + 1) →ₐ[R0 p O ε] R'n p O ε n :=
  Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ (R0 p O ε) _) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.2 ⟨b * p, by ring⟩)

def rRing (n : ℕ) : Rn p O (n + 1) →+* Rn p O n :=
  Ideal.Quotient.lift (span {(p : O) ^ (n + 1 + 1)})
    (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton'.2 ⟨b * p, by ring⟩)

def rAlg (n : ℕ) : (LR p O hv ε hε (n + 1) : Type) →ₐ[R0 p O ε] (LR p O hv ε hε n : Type) :=
  { toRingHom := rRing p O n
    commutes' := fun _ => rfl }

lemma r'Alg_surj (n : ℕ) : Function.Surjective (r'Alg p O ε n) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

lemma rAlg_surj (n : ℕ) : Function.Surjective (rAlg p O hv ε hε n) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

lemma sub_mem_of_compat (f : ℕ → O)
    (hf : ∀ n, f (n + 1) - f n ∈ span {(p : O) ^ (n + 1)}) :
    ∀ m k, f (m + k) - f m ∈ span {(p : O) ^ m} := by
  intro m k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : f (m + k + 1) - f (m + k) ∈ span {(p : O) ^ m} := by
      have h := hf (m + k)
      rw [Ideal.mem_span_singleton'] at h ⊢
      obtain ⟨a, ha⟩ := h
      exact ⟨a * p ^ (k + 1), by rw [← ha, mul_assoc, ← pow_add]; ring_nf⟩
    have : f (m + (k + 1)) - f m = (f (m + k + 1) - f (m + k)) + (f (m + k) - f m) := by
      rw [← add_assoc]; ring
    rw [this]
    exact Ideal.add_mem _ h1 ih

lemma complete_O (x : ∀ n, (Rn p O n)) (hx : ∀ n, rRing p O n (x (n + 1)) = x n) :
    ∃ a : O, ∀ n, Ideal.Quotient.mk (span {(p : O) ^ (n + 1)}) a = x n := by
  choose f hf using fun n => Ideal.Quotient.mk_surjective (x n)
  have hc : ∀ n, f (n + 1) - f n ∈ span {(p : O) ^ (n + 1)} := by
    intro n
    have h := hx n
    rw [← hf (n + 1), ← hf n, rRing, Ideal.Quotient.lift_mk, Ideal.Quotient.eq] at h
    exact h
  have hsm : ∀ m, (span {(p : O)} ^ m • ⊤ : Submodule O O) = span {(p : O) ^ m} := by
    intro m
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := span {(p : O)}) (M := O) inferInstance
    (f := f) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have := sub_mem_of_compat p O f hc m k
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).2 this)
  refine ⟨L, fun n => ?_⟩
  rw [← hf n, Ideal.Quotient.eq]
  have h1 := hL (n + 1)
  rw [SModEq.sub_mem, hsm] at h1
  have h2 := hc n
  have : L - f n = (f (n + 1) - f n) - (f (n + 1) - L) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 h1

def ainfTowerL : ATowerL (R0 p O ε) p where
  toATower := ainfTower p O hv ε hε
  r' n := ⟨r'Alg p O ε n, TowerExample.isLocalHom_of_surj _ (r'Alg_surj p O ε n)⟩
  r n := ⟨rAlg p O hv ε hε n, TowerExample.isLocalHom_of_surj _ (rAlg_surj p O hv ε hε n)⟩
  r_π n x := by
    obtain ⟨x0, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x0
    rfl
  r_q n x := rfl
  r'_ξ n := rfl
  complete x hx := complete_O p O x hx

lemma root_succ_pow (k : ℕ) : root p O ε (k + 1) ^ p = root p O ε k := by
  show ((frobeniusEquiv (PreTilt O p) p).symm^[k + 1] ε) ^ p = _
  rw [Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  rfl

lemma root_pow_one (n : ℕ) : root p O ε (n + 1) ^ p ^ n = root p O ε 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, root_succ_pow, ih]

theorem zeta_succ_pow (n : ℕ) : zetaV p O ε (n + 1) ^ p = zetaV p O ε n := by
  rw [zetaV, zetaV, ← map_pow, ← map_pow, root_succ_pow]


include hv hε in
theorem zeta_primitive (n : ℕ) : IsPrimitiveRoot (zetaV p O ε n) (p ^ (n + 1)) := by
  have hz1 : zetaV p O ε n ^ p ^ (n + 1) = 1 := by
    rw [zetaV, ← map_pow, ← map_pow, root_pow, fontaineTheta_teichmuller,
      untilt_eps p O hv ε hε]
  have hzn : zetaV p O ε n ^ p ^ n ≠ 1 := by
    rw [zetaV, ← map_pow, ← map_pow, root_pow_one, fontaineTheta_teichmuller]
    exact hε.ne_one hp.out.one_lt
  have hord : orderOf (zetaV p O ε n) ∣ p ^ (n + 1) := orderOf_dvd_of_pow_eq_one hz1
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp.out).1 hord
  have hjn : j = n + 1 := by
    by_contra hne
    have hle : j ≤ n := by omega
    apply hzn
    have : orderOf (zetaV p O ε n) ∣ p ^ n := by rw [hj']; exact pow_dvd_pow p hle
    exact orderOf_dvd_iff_pow_eq_one.1 this
  rw [← hjn, ← hj']
  exact IsPrimitiveRoot.orderOf _


include hv hε in
theorem c_val : v (algebraMap O C (fontaineTheta O p (nu p O ε))) ^ (p - 1) = v (p : C) := by
  obtain ⟨-, -, -, hX, -, -⟩ := a0 p C v O hv
  exact (hX ε hv hε).2.2.1


end Ainf

end ReciprocityTheory.PGsh
end
end
