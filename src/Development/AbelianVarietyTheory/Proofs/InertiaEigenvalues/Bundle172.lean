module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle137
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle157
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle067
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle144
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle119
public import GroundTheory.AutomorphicForms.FourierWhittaker.UMatColXEqFromBlocks
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle149
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle127
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle150
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle143
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
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.DualLattices.Bundle007
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin

@[expose] public section

section

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.StabIdx

theorem relIndex_ne_zero_of_map {G X : Type} [Group G] [Finite X] (H K : Subgroup G) (f : K → X)
    (hf : ∀ a b : K, f a = f b → (a : G)⁻¹ * b ∈ H) : H.relIndex K ≠ 0 := by
  classical
  haveI : Finite (K ⧸ H.subgroupOf K) := by
    refine Finite.of_injective (fun q : K ⧸ H.subgroupOf K => f q.out) ?_
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using hf _ _ h
  exact Subgroup.index_ne_zero_of_finite

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem mem_stabilizer_of {g : A} (L : stLat O E g) (t : Aˣ)
    (h1 : ∀ y ∈ (L : Submodule O A), (t : A) * y ∈ (L : Submodule O A))
    (h2 : ∀ y ∈ (L : Submodule O A), ((t⁻¹ : Aˣ) : A) * y ∈ (L : Submodule O A)) :
    t ∈ MulAction.stabilizer Aˣ L := by
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  rw [stLat_smul_val]
  ext x
  rw [mem_mulLat_iff]
  constructor
  · intro hx
    have := h1 _ hx
    rwa [← mul_assoc, Units.mul_inv, one_mul] at this
  · intro hx
    exact h2 _ hx

theorem finite_quotient_span [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {c : O} (hc : c ≠ 0) : Finite (O ⧸ Ideal.span {c}) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : Ideal.span {c} ≠ ⊥ := by simpa using hc
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    (inferInstance : Finite (IsLocalRing.ResidueField O))
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal O)) n
  rwa [hm, Ideal.span_singleton_pow, ← hn] at this

variable [IsDomain O] [Algebra O E] [IsFractionRing O E] [IsScalarTower O E A]

theorem exists_smul_mul_mem (C L : Submodule O A) (hC : C.FG) (hL : IsLat O E L) :
    ∃ c : O, c ≠ 0 ∧ ∀ x ∈ C, ∀ y ∈ L, c • (x * y) ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hC
  obtain ⟨t, ht⟩ := hL.1
  have hex : ∀ p : A × A, ∃ r : O, r ≠ 0 ∧ r • (p.1 * p.2) ∈ L := fun p =>
    ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.exists_smul_mem_of_mem_span (C := E) L (by rw [hL.2]; trivial)
  choose r hr0 hrm using hex
  refine ⟨∏ p ∈ s ×ˢ t, r p, Finset.prod_ne_zero_iff.2 fun p _ => hr0 p, ?_⟩
  have hgen : ∀ a ∈ s, ∀ b ∈ t, (∏ p ∈ s ×ˢ t, r p) • (a * b) ∈ L := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem r (Finset.mem_product.2 ⟨ha, hb⟩ : (a, b) ∈ s ×ˢ t)
    rw [hk, mul_comm, mul_smul]
    exact L.smul_mem _ (hrm (a, b))
  intro x hx y hy
  rw [← ht] at hy
  induction hy using Submodule.span_induction with
  | mem b hb =>
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem a ha => exact hgen a ha b hb
    | zero => simp
    | add u v _ _ hu hv => rw [add_mul, smul_add]; exact L.add_mem hu hv
    | smul o u _ hu => rw [smul_mul_assoc, smul_comm]; exact L.smul_mem _ hu
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add, smul_add]; exact L.add_mem hu hv
  | smul o u _ hu => rw [mul_smul_comm, smul_comm]; exact L.smul_mem _ hu

theorem relIndex_ne_zero_of_fg [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {g : A} (hC : (Subalgebra.toSubmodule (integralClosure O A)).FG) (L : stLat O E g) :
    (MulAction.stabilizer Aˣ L).relIndex (intUnits O A) ≠ 0 := by
  classical
  set C := Subalgebra.toSubmodule (integralClosure O A) with hCdef
  obtain ⟨c, hc0, hcL⟩ := exists_smul_mul_mem (E := E) C (L : Submodule O A) hC L.2.1
  haveI := finite_quotient_span hc0
  haveI : Finite (C ⧸ (⊤ : Submodule O C)) := by
    haveI : Subsingleton (C ⧸ (⊤ : Submodule O C)) := Submodule.Quotient.subsingleton_iff.2 rfl
    infer_instance
  haveI : Finite (C ⧸ Ideal.span {c} • (⊤ : Submodule O C)) :=
    Submodule.finite_quotient_smul _ ((Submodule.fg_top C).2 hC)
  have hmemC : ∀ x : A, IsIntegral O x → x ∈ C := fun x hx => hx
  let f : intUnits O A → C ⧸ Ideal.span {c} • (⊤ : Submodule O C) := fun t =>
    Submodule.Quotient.mk ⟨((t : Aˣ) : A), hmemC _ t.2.1⟩
  refine relIndex_ne_zero_of_map _ _ f fun a b hab => ?_
  rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hab
  obtain ⟨n, -, hn⟩ := hab
  have hn' : c • (n : A) = ((a : Aˣ) : A) - ((b : Aˣ) : A) := by
    have := congrArg Subtype.val hn
    simpa using this
  have ha : ((a : Aˣ)⁻¹ : Aˣ).val * (a : Aˣ).val = 1 := Units.inv_mul _
  have hb : ((b : Aˣ)⁻¹ : Aˣ).val * (b : Aˣ).val = 1 := Units.inv_mul _
  have hna : ((a : Aˣ)⁻¹ : Aˣ).val * (n : A) ∈ C := hmemC _ (a.2.2.mul n.2)
  have hnb : ((b : Aˣ)⁻¹ : Aˣ).val * (n : A) ∈ C := hmemC _ (b.2.2.mul n.2)
  apply mem_stabilizer_of L
  · intro y hy
    have e : (((a : Aˣ)⁻¹ * (b : Aˣ) : Aˣ) : A) * y =
        y - c • ((((a : Aˣ)⁻¹ : Aˣ).val * (n : A)) * y) := by
      rw [Units.val_mul]
      rw [Algebra.smul_def] at hn' ⊢
      linear_combination (((a : Aˣ)⁻¹ : Aˣ).val * y) * hn' + y * ha
    rw [e]
    exact L.1.sub_mem hy (hcL _ hna _ hy)
  · intro y hy
    have e : ((((a : Aˣ)⁻¹ * (b : Aˣ))⁻¹ : Aˣ) : A) * y =
        y + c • ((((b : Aˣ)⁻¹ : Aˣ).val * (n : A)) * y) := by
      rw [mul_inv_rev, inv_inv, Units.val_mul]
      rw [Algebra.smul_def] at hn' ⊢
      linear_combination (-(((b : Aˣ)⁻¹ : Aˣ).val * y)) * hn' + y * hb
    rw [e]
    exact L.1.add_mem hy (hcL _ hnb _ hy)

theorem stabilizer_relIndex_intUnits_ne_zero : ∀ (O E A : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E]
    [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A]
    [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable →
    ∀ L : stLat O E g, (MulAction.stabilizer Aˣ L).relIndex (intUnits O A) ≠ 0 := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ _ g hg L
  haveI := GlobalTheory.T.algebraEtale_of_separable_charpoly_mulLeft E A g hg
  exact relIndex_ne_zero_of_fg (GlobalTheory.T.integralClosure_fg_finiteEtale_dvr O E A) L

end GlobalTheory.UnitLemma.StabIdx
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Move

variable {K : UQ} (B : InvAlg K)

theorem det_trace_ne_zero (hP : B.P.Separable)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨b, hb⟩ := exists_basis_pow_of_separable K B hP
  have hk : ∀ k : Fin (Module.finrank K.E B.A),
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * ∑ l, v l • e l) = 0 := by
    intro k
    have := congrFun hMv k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this

    rw [Finset.mul_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hall : ∀ w : B.A, Algebra.trace K.E B.A ((∑ l, v l • e l) * w) = 0 := by
    intro w

    rw [← b.sum_repr w, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_smul_comm, map_smul, hb k, mul_comm, hk k, smul_zero]
  have hz0 : ∑ l, v l • e l = 0 :=
    (Sandwich.traceForm_nondegenerate B hP).1 _ (fun w => by rw [Algebra.traceForm_apply]; exact hall w)
  apply hv
  apply e.equivFun.symm.injective
  rw [Module.Basis.equivFun_symm_apply, hz0, map_zero]

theorem mem_mulLat (M : Submodule K.O B.A) (y : B.Aˣ) (z : B.A) :
    z ∈ mulLat K.O (y : B.A) M ↔ ((y⁻¹ : B.Aˣ) : B.A) * z ∈ M := by
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, by simp⟩

theorem mulLat_inv (M : Submodule K.O B.A) (y : B.Aˣ) :
    mulLat K.O ((y⁻¹ : B.Aˣ) : B.A) (mulLat K.O (y : B.A) M) = M := by
  ext z
  rw [mem_mulLat, mem_mulLat, inv_inv, Units.inv_mul_cancel_left]

theorem mulLat_mem_Lin (y : B.Aˣ) (hy : B.σ (y : B.A) = y) (M : Submodule K.O B.A) (hM : M ∈ B.Lin) :
    mulLat K.O (y : B.A) M ∈ B.Lin := by
  obtain ⟨⟨hfg, hsp⟩, hg, hσ⟩ := hM
  have hyi : B.σ ((y⁻¹ : B.Aˣ) : B.A) = ((y⁻¹ : B.Aˣ) : B.A) := by
    have h1 : B.σ ((y⁻¹ : B.Aˣ) : B.A) * (y : B.A) = 1 := by
      conv_lhs => rw [← hy]
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((y⁻¹ : B.Aˣ) : B.A) = B.σ ((y⁻¹ : B.Aˣ) : B.A) * (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  refine ⟨⟨hfg.map _, ?_⟩, fun z hz => ?_, fun z hz => ?_⟩
  · have h1 : ((mulLat K.O (y : B.A) M : Submodule K.O B.A) : Set B.A) =
        (LinearMap.mulLeft K.E (y : B.A)) '' (M : Set B.A) := by
      rw [mulLat, Submodule.map_coe]
      rfl
    rw [h1, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top]
    intro x
    exact ⟨((y⁻¹ : B.Aˣ) : B.A) * x, by simp⟩
  · rw [mem_mulLat] at hz ⊢
    rw [mul_left_comm]
    exact hg _ hz
  · rw [mem_mulLat] at hz ⊢
    have := hσ _ hz
    rwa [map_mul, hyi] at this

theorem sgnLat_mulLat (hP : B.P.Separable) (M : Submodule K.O B.A) (hM : IsLat K.O K.E M)
    (hσ : ∀ y ∈ M, B.σ y ∈ M) (y : B.Aˣ) :
    B.sgnLat (mulLat K.O (y : B.A) M) = K.eta (Algebra.norm K.E (y : B.A)) * B.sgnLat M := by
  classical
  obtain ⟨e, he, -⟩ := GlobalTheory.GaloisDescentLattice.exists_fixed_basis K B M hM hσ
  let f : B.A ≃ₗ[K.E] B.A := LinearEquiv.ofLinear (LinearMap.mulLeft K.E (y : B.A))
    (LinearMap.mulLeft K.E ((y⁻¹ : B.Aˣ) : B.A)) (by ext x; simp) (by ext x; simp)
  let e' := e.map f
  have he' : ∀ l, e' l = (y : B.A) * e l := fun l => rfl
  have hspan : mulLat K.O (y : B.A) M = Submodule.span K.O (Set.range e') := by
    rw [← he, mulLat, Submodule.map_span, ← Set.range_comp]
    rfl
  have hN : Algebra.norm K.E (y : B.A) ≠ 0 := (y.isUnit.map (Algebra.norm K.E)).ne_zero
  have hmat : (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e' l)) =
      (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)) * Algebra.leftMulMatrix e (y : B.A) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.of_apply, Algebra.leftMulMatrix_eq_repr_mul]
    rw [he' l]
    conv_lhs => rw [← e.sum_repr ((y : B.A) * e l)]

    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rw [hspan, SgnBasis.sgnLat_span_basis, ← he, SgnBasis.sgnLat_span_basis, hmat, Matrix.det_mul,
    ← Algebra.norm_eq_matrix_det, Desc.eta_mul (det_trace_ne_zero B hP e) hN, mul_comm]

theorem inDual_mulLat (M : Submodule K.O B.A) (y : B.Aˣ) (t : B.A) :
    InDual B t (mulLat K.O (y : B.A) M) ↔ InDual B ((y : B.A) * t) M := by
  unfold InDual
  constructor
  · intro h z hz
    have := h ((y : B.A) * z) (by rw [mem_mulLat, Units.inv_mul_cancel_left]; exact hz)
    have e : t * ((y : B.A) * z) = (y : B.A) * t * z := by ring
    rwa [e] at this
  · intro h z hz
    rw [mem_mulLat] at hz
    have := h _ hz
    have e : (y : B.A) * t * (((y⁻¹ : B.Aˣ) : B.A) * z) = t * z := by
      rw [mul_comm (y : B.A) t, mul_assoc, Units.mul_inv_cancel_left]
    rwa [e] at this

theorem term_mulLat {ι : Type} (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A)
    (y : B.Aˣ) :
    term B π I I' ((y : B.A) * u) s (mulLat K.O (y : B.A) M) = term B π I I' u ((y : B.A) * s) M := by
  classical
  unfold term dlt
  congr 1
  · refine Finset.sum_congr rfl fun J _ => ?_
    unfold indM
    have e : ((y⁻¹ : B.Aˣ) : B.A) * ((∏ j ∈ J, π j) * ((y : B.A) * u)) = (∏ j ∈ J, π j) * u := by
      rw [mul_left_comm, Units.inv_mul_cancel_left]
    simp only [mem_mulLat, e]
  · refine Finset.sum_congr rfl fun J _ => ?_
    unfold indD
    have e : (y : B.A) * ((∏ j ∈ J, π j) * s) = (∏ j ∈ J, π j) * ((y : B.A) * s) := by ring
    simp only [inDual_mulLat, e]

theorem HH_mul_unit : ∀ (K : UQ) (B : InvAlg K) (ι : Type) (π : ι → B.A) (I I' : Finset ι) (u s y : B.A),
    B.LieReg → B.Plus y → HH B π I I' (y * u) s = K.eta (Algebra.norm K.E y) * HH B π I I' u (y * s) := by
  intro K B ι π I I' u s y hB hy
  obtain ⟨⟨yu, rfl⟩, hσ⟩ := hy
  have hσ' : B.σ ((yu⁻¹ : B.Aˣ) : B.A) = ((yu⁻¹ : B.Aˣ) : B.A) := by
    have h1 : B.σ ((yu⁻¹ : B.Aˣ) : B.A) * (yu : B.A) = 1 := by
      conv_lhs => rw [← hσ]
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((yu⁻¹ : B.Aˣ) : B.A) = B.σ ((yu⁻¹ : B.Aˣ) : B.A) * (yu : B.A) * ((yu⁻¹ : B.Aˣ) : B.A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  unfold HH
  rw [mul_finsum_mem]
  symm
  refine finsum_mem_eq_of_bijOn (fun M => mulLat K.O (yu : B.A) M) ?_ ?_
  · refine Set.InvOn.bijOn (f' := fun M => mulLat K.O ((yu⁻¹ : B.Aˣ) : B.A) M) ⟨fun M _ => ?_, fun M _ => ?_⟩
      (fun M hM => mulLat_mem_Lin B yu hσ M hM) (fun M hM => ?_)
    · exact mulLat_inv B M yu
    · have := mulLat_inv B M yu⁻¹
      rwa [inv_inv] at this
    · have := mulLat_mem_Lin B yu⁻¹ hσ' M hM
      exact this
  · intro M hM
    rw [sgnLat_mulLat B hB.2 M hM.1 hM.2.2 yu, term_mulLat]
    ring

end GlobalTheory.UnitLemma.Move
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.eventually_adelicGLProjections_finite_near_one : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := by
  first | (exact @GlobalTheory.SchurExt.eventually_prS_prO_finGL) | (exact GlobalTheory.SchurExt.eventually_prS_prO_finGL) | (intros; apply GlobalTheory.SchurExt.eventually_prS_prO_finGL <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.schurComplementExtensionFunction_blockDiag_apply : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), ∀ h : GA E (m + 1), schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h * b₁ 1 * (χ 0 : ℂ) := by
  first | (exact @GlobalTheory.SchurExt.schurF_blockGL) | (exact GlobalTheory.SchurExt.schurF_blockGL) | (intros; apply GlobalTheory.SchurExt.schurF_blockGL  <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

theorem _root_.GlobalTheory.T.parabolicModulusSqrtChar_refinedBlocks_in_stages : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) k),
    deltaHalf k (fun c : Fin (∑ a, t a) => Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2))
        (flatHom (fun a b => GL (Fin (d' a b)) k) g) =
      deltaHalf k (fun a => Fin (d a)) (relEmbD k e' g) * relDeltaHalfD k (fun a b => Fin (d' a b)) g := by
  first | exact @GlobalTheory.JacStages.deltaHalf_flatHom | exact GlobalTheory.JacStages.deltaHalf_flatHom | (intros; apply GlobalTheory.JacStages.deltaHalf_flatHom <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

theorem _root_.GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested : ∀ (s : ℕ) (t : Fin s → ℕ) (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)]
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ : ∀ a b, Representation ℂ (Γ a b) (Y a b)),
    Nonempty (Representation.Equiv ((piTensor fun c : Fin (∑ a, t a) =>
        ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).comp (flatHom Γ))
      (piTensor fun a => piTensor (ρ a))) := by
  first | exact @GlobalTheory.JacStages.piTensor_flatHom_equiv | exact GlobalTheory.JacStages.piTensor_flatHom_equiv | (intros; apply GlobalTheory.JacStages.piTensor_flatHom_equiv <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

theorem _root_.GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : Fin s → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    Nonempty ((relJacD e' (piTensor ρ)).Equiv (piTensor fun a => jac (e' a) (ρ a))) := by
  first | exact @GlobalTheory.JacStages.relJacD_piTensor_equiv | exact GlobalTheory.JacStages.relJacD_piTensor_equiv | (intros; apply GlobalTheory.JacStages.relJacD_piTensor_equiv <;> assumption)
end

section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie

theorem semilinear_matrix_comm {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] {r : ℕ}
    (σ τ : A →+* A) (f g : D →+ D) (hf : ∀ a x, f (a • x) = σ a • f x)
    (hg : ∀ a x, g (a • x) = τ a • g x) (hc : ∀ x, f (g x) = g (f x))
    (b : Fin r → D) (hb : LinearIndependent A b) (e : A) (P Q : Fin r → Fin r → A)
    (hQ : ∀ k, g (b k) = ∑ m, Q m k • b m) (hP : ∀ k, e • f (b k) = ∑ m, P m k • b m)
    (p k : Fin r) :
    e * ∑ m, Q p m * τ (P m k) = τ e * ∑ m, P p m * σ (Q m k) := by
  have h1 : τ e • g (f (b k)) = ∑ p, (∑ m, Q p m * τ (P m k)) • b p := by

    rw [← hg, hP, map_sum]
    simp only [hg, hQ, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h2 : e • f (g (b k)) = ∑ p, (∑ m, P p m * σ (Q m k)) • b p := by

    rw [hQ, map_sum, Finset.smul_sum]
    simp only [hf, smul_comm e, hP, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h3 : ∑ p, (e * ∑ m, Q p m * τ (P m k)) • b p
      = ∑ p, (τ e * ∑ m, P p m * σ (Q m k)) • b p := by
    simp only [mul_smul, ← Finset.smul_sum]
    rw [← h1, ← h2, hc, smul_comm]
  exact (Fintype.linearIndependent_iffₛ.1 hb) _ _ h3 p

theorem matrices_comm : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → ∀ (M : ℕ) (Φ Gm : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧), (∀ k, W.γD T W.gam (b k : W.DD T) = ∑ m, (fun i => j (Gm i m k) : LetA O n) • (b m : W.DD T)) → (∀ k, (fun _ => j R.E : LetA O n) ^ M • W.φD T (b k : W.DD T) = ∑ m, (fun i => j (Φ i m k) : LetA O n) • (b m : W.DD T)) → ∀ i, R.E ^ M • (Gm i * (Φ i).map R.γ) = R.γ R.E ^ M • (Φ i * (Gm (i - 1)).map R.φ) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF _ _ M Φ Gm hG hΦ i
  obtain ⟨hj, -, hφ, hγ, -⟩ := hF
  have hb : LinearIndependent (LetA O n) (fun k => (b k : W.DD T)) :=
    b.linearIndependent.map' (W.N T).subtype (Submodule.ker_subtype _)
  have key := semilinear_matrix_comm (A := LetA O n) (letφ (n := n) W.φ₀).toRingHom
    (letγ (n := n) (W.γ₀ W.gam)).toRingHom (W.φD T).toAddMonoidHom (W.γD T W.gam).toAddMonoidHom
    (fun a x => by
      change W.φD T (a • x) = letφ W.φ₀ a • W.φD T x
      rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul])
    (fun a x => by
      change W.γD T W.gam (a • x) = letγ (W.γ₀ W.gam) a • W.γD T W.gam x
      rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul])
    (fun x => W.φγ_comm T W.gam x) _ hb ((fun _ => j R.E : LetA O n) ^ M)
    (fun m k i => j (Φ i m k)) (fun m k i => j (Gm i m k)) hG hΦ
  ext1 p k
  apply hj
  have h := congrFun (key p k) i
  simp only [Pi.mul_apply, Finset.sum_apply, Pi.pow_apply, map_pow] at h

  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow,
  map_sum, hφ, hγ]
  exact h

end GlobalTheory.WachTie
end
