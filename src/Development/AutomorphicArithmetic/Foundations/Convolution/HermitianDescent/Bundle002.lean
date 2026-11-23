module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

noncomputable section

open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {σ : R ≃ₐ[k] R} {q : ℕ}

private theorem sum_fixed (h : IsGal σ q) (r : R) :
    σ (∑ j ∈ Finset.range q, (σ ^ j) r) = ∑ j ∈ Finset.range q, (σ ^ j) r := by
  have h1 := Finset.sum_range_succ (fun j => (σ ^ j) r) q
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) r) q
  rw [h1, h.pow, pow_zero] at h2

  rw [map_sum, add_right_cancel h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ', AlgEquiv.mul_apply]

private theorem exists_tr (h : IsGal σ q) :
    ∃ t : R →ₗ[k] k, ∀ r, algebraMap k R (t r) = ∑ j ∈ Finset.range q, (σ ^ j) r := by
  choose t ht using fun r => h.fix _ (sum_fixed h r)
  refine ⟨⟨⟨t, fun a b => h.inj ?_⟩, fun c a => h.inj ?_⟩, ht⟩
  · rw [map_add (f := _), ht, ht, ht, ← Finset.sum_add_distrib]
    simp only [map_add (f := _)]
  · simp only [RingHom.id_apply, smul_eq_mul]
    rw [map_mul, ht, ht, Finset.mul_sum]
    simp only [Algebra.smul_def, map_mul, AlgEquiv.commutes]

private theorem dual (h : IsGal σ q) {s : ℕ} {x y : Fin s → R}
    (hxy : ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0) {t : R →ₗ[k] k}
    (ht : ∀ r, algebraMap k R (t r) = ∑ j ∈ Finset.range q, (σ ^ j) r) (r : R) :
    ∑ i, t (y i * r) • x i = r := by
  calc ∑ i, t (y i * r) • x i
      = ∑ i, ∑ j ∈ Finset.range q, x i * (σ ^ j) (y i) * (σ ^ j) r := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, ht, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]; ring
    _ = ∑ j ∈ Finset.range q, (if j = 0 then 1 else 0) * (σ ^ j) r := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [← Finset.sum_mul, hxy j (Finset.mem_range.1 hj)]
    _ = r := by
        simp [h.pos]

private theorem pow_tmul (A : Type) [CommRing A] [Algebra k A] (σ : R ≃ₐ[k] R) (j : ℕ) (a : A) (r : R) :
    ((Algebra.TensorProduct.congr AlgEquiv.refl σ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R) ^ j) (a ⊗ₜ r) =
      a ⊗ₜ (σ ^ j) r := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]
    simp

end

theorem galBase : GalBase := by
  intro k R _ _ _ A _ _ σ q h
  obtain ⟨t, ht⟩ := exists_tr h
  obtain ⟨s, x, y, hxy⟩ := h.sep
  have hd := dual h hxy ht
  have hsplit : (Fintype.linearCombination k x).comp
      (LinearMap.pi fun i => t.comp (LinearMap.mulLeft k (y i))) = LinearMap.id := by
    ext r
    simpa [Fintype.linearCombination_apply] using hd r
  have hfin : Module.Finite k R :=
    Module.Finite.of_surjective (Fintype.linearCombination k x) fun r =>
      ⟨_, LinearMap.congr_fun hsplit r⟩
  have hproj : Module.Projective k R := Module.Projective.of_split _ _ hsplit
  obtain ⟨c, hc⟩ : ∃ c, t c = 1 := by
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      (LinearMap.range t) (⊤ : Submodule k R) Module.Finite.fg_top (by
        intro r _
        rw [← hd r]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem_smul (LinearMap.mem_range_self _ _) Submodule.mem_top)
    have h0 : r = 0 := h.inj (by
      rw [map_zero, Algebra.algebraMap_eq_smul_one]; exact hr0 1 Submodule.mem_top)
    obtain ⟨c, hc⟩ := hr
    exact ⟨-c, by rw [map_neg, hc, h0]; ring⟩
  refine ⟨hfin, hproj, ⟨fun m hm hm' => hm.ne_top ?_⟩, ?_⟩
  · have key : ∀ r ∈ m • (⊤ : Submodule k R), t r ∈ m := by
      intro r hr
      refine Submodule.smul_induction_on hr (fun a ha n _ => ?_) (fun a b ha hb => ?_)
      · rw [map_smul, smul_eq_mul]; exact m.mul_mem_right _ ha
      · rw [map_add (f := _)]; exact m.add_mem ha hb
    rw [Ideal.eq_top_iff_one, ← hc]
    exact key c (by rw [hm']; exact Submodule.mem_top)
  · set τ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R := Algebra.TensorProduct.congr AlgEquiv.refl σ with hτ
    have hp : ∀ j a r, (τ ^ j) (a ⊗ₜ r) = a ⊗ₜ (σ ^ j) r := pow_tmul A σ
    let p : A ⊗[k] R →ₗ[k] A :=
      (TensorProduct.rid k A).toLinearMap.comp ((t.comp (LinearMap.mulLeft k c)).lTensor A)
    have hpp : ∀ a r, p (a ⊗ₜ r) = t (c * r) • a := fun a r => by simp [p]
    refine ⟨h.pos, ?_, ?_, ?_, s, fun i => 1 ⊗ₜ x i, fun i => 1 ⊗ₜ y i, fun j hj => ?_⟩
    · refine AlgEquiv.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a r => rw [hp, h.pow]; rfl
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    · refine Function.LeftInverse.injective (g := p) fun a => ?_
      rw [Algebra.TensorProduct.algebraMap_apply, hpp, mul_one, hc, one_smul]
      rfl
    · intro z hz
      have h1 : ∀ z, algebraMap A (A ⊗[k] R) (p z) =
          ∑ j ∈ Finset.range q, (τ ^ j) ((1 ⊗ₜ c) * z) := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a r =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp]
          rw [← TensorProduct.tmul_sum, ← ht, hpp, Algebra.TensorProduct.algebraMap_apply,
            Algebra.algebraMap_eq_smul_one (t (c * r)), ← TensorProduct.smul_tmul]
          rfl
        | add a b ha hb =>
          simp only [map_add (f := _), mul_add, ha, hb, Finset.sum_add_distrib]
      have h2 : ∀ j : ℕ, (τ ^ j) z = z := by
        intro j
        induction j with
        | zero => rfl
        | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hz, ih]
      refine ⟨p z, ?_⟩
      rw [h1]
      simp only [map_mul, h2, hp]
      rw [← Finset.sum_mul, ← TensorProduct.tmul_sum, ← ht, hc, map_one,
        ← Algebra.TensorProduct.one_def, one_mul]
    · simp only [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_sum, hxy j hj]
      split_ifs
      · rfl
      · exact TensorProduct.tmul_zero _ _

end UpperTheory.ConvolutionTheory.D
end
end

section

noncomputable section

namespace UpperTheory.ConvolutionTheory.D

open Classical in
private theorem dual_sum (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (τ : E ≃ₐ[F] E) :
    ∑ i, b i * τ (b.traceDual i) = if τ = 1 then 1 else 0 := by
  have li : LinearIndependent E (fun t : E ≃ₐ[F] E => ((t : E →* E) : E → E)) :=
    (linearIndependent_monoidHom E E).comp (fun t : E ≃ₐ[F] E => (t : E →* E))
      (fun s t h => AlgEquiv.ext fun x => DFunLike.congr_fun h x)
  have key := Fintype.linearIndependent_iff.1 li
    (fun t => (∑ i, b i * t (b.traceDual i)) - if t = 1 then 1 else 0) ?_ τ
  · exact sub_eq_zero.1 key
  funext z
  have hz : z = ∑ i, b i * algebraMap F E (Algebra.trace F E (b.traceDual i * z)) := by
    conv_lhs => rw [← b.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Algebra.trace F E (b.traceDual i * z) = b.repr z i := by
      conv_lhs => rw [← b.sum_repr z]

      simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, Module.Basis.trace_traceDual_mul]
      simp
    rw [this, Algebra.smul_def, mul_comm]
  simp only [trace_eq_sum_automorphisms, Finset.mul_sum, map_mul] at hz
  rw [Finset.sum_comm] at hz
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply, mul_assoc]
  exact sub_eq_zero.2 hz.symm

theorem galField : GalField := by
  classical
  intro F E _ _ _ _ _ σ hσ
  have ho : orderOf σ = Module.finrank F E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  refine ⟨Module.finrank_pos, ho ▸ pow_orderOf_eq_one σ, (algebraMap F E).injective, fun r hr => ?_,
    Module.finrank F E, Module.finBasis F E, (Module.finBasis F E).traceDual, fun j hj => ?_⟩
  · have h : ∀ τ : E ≃ₐ[F] E, τ r = r := fun τ => by
      have : Subgroup.zpowers σ ≤ MulAction.stabilizer (E ≃ₐ[F] E) r :=
        (Subgroup.zpowers_le).2 hr
      exact this (hσ τ)
    exact (IsGalois.mem_range_algebraMap_iff_fixed r).2 h
  · have := dual_sum F E (Module.finBasis F E) (σ ^ j)
    rw [show (if j = 0 then (1 : E) else 0) = if σ ^ j = 1 then 1 else 0 from
      if_congr ⟨fun h => by rw [h, pow_zero], fun h =>
        Nat.eq_zero_of_dvd_of_lt (orderOf_dvd_of_pow_eq_one h) (ho ▸ hj)⟩ rfl rfl]
    convert this

end UpperTheory.ConvolutionTheory.D
end
end

section

noncomputable section

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.D

private lemma reflect_cp_inv {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (g : GL (Fin n) R) :
    reflect n (cp g⁻¹) = C ((cp g⁻¹).coeff 0) * cp g := by
  have h1 : reflect n (cp g⁻¹) = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpolyRev := by
    rw [← Matrix.reverse_charpoly, Polynomial.reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, cp]
  have h2 := Matrix.charpoly_inv ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) (Units.isUnit _)
  have h3 := Matrix.det_eq_sign_charpoly_coeff ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  rw [← Matrix.coe_units_inv, inv_inv] at h2
  have h4 : IsUnit ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have h5 := Ring.mul_inverse_cancel _ h4
  rw [h1, cp, cp, h2]
  nth_rewrite 1 [h3] at h5
  have h6 := congrArg (C : R → R[X]) h5
  simp only [map_mul, map_pow, map_neg, map_one] at h6
  linear_combination (-((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpolyRev) * h6

private lemma ct_mul {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) : ct c (A * B) = ct c B * ct c A := by
  rw [ct, ct, ct, ← Matrix.transpose_mul, Matrix.map_mul]

private lemma ct_ct {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) (hc : c ^ 2 = 1) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : ct c (ct c A) = A := by
  ext i j
  have := congrArg (fun f : R ≃ₐ[k] R => f (A i j)) hc
  simpa [ct, pow_two] using this

private lemma csr_of_cong {k R : Type} [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R] (c : R ≃ₐ[k] R) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (g : GL (Fin n) R) (hJ : IsUnit J.det) (h : cong c g J = J) :
    IsCsr c n (cp g) := by
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det J).2 hJ
  have h1 : ct c (g : Matrix (Fin n) (Fin n) R) =
      u.val * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (u⁻¹).val := by
    rw [cong] at h
    nth_rewrite 1 [← h]
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  have h2 : (cp g).map (c : R →+* R) = cp g⁻¹ := by
    have h3 := congrArg Matrix.charpoly h1
    rw [Matrix.coe_units_inv u, Matrix.charpoly_units_conj, ct, Matrix.charpoly_transpose] at h3
    rw [cp, cp, ← h3, ← Matrix.charpoly_map]
    rfl
  refine ⟨Matrix.charpoly_monic _, ?_, ?_, ?_⟩
  · rw [cp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  · have h4 : IsUnit (g : Matrix (Fin n) (Fin n) R).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    rw [Matrix.det_eq_sign_charpoly_coeff] at h4
    exact isUnit_of_mul_isUnit_right h4
  · have h5 : c ((cp g).coeff 0) = (cp g⁻¹).coeff 0 := by
      rw [← h2, Polynomial.coeff_map]
      rfl
    rw [h2, h5, reflect_cp_inv]

theorem csrOf : CsrOf := by
  intro k R _ _ _ _ c hc n
  refine ⟨fun J g hJ h => csr_of_cong c J g hJ h, fun d => ?_⟩
  refine csr_of_cong c ((d⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) _
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)) ?_
  have h1 : (th c d).val = ct c (d⁻¹ : GL (Fin n) R).val := rfl
  have h2 : ct c d.val * (th c d).val = 1 := (th c d).inv_val
  rw [cong, Units.val_mul, ct_mul]
  nth_rewrite 1 [h1]
  rw [ct_ct c hc]
  simp only [mul_assoc, Units.inv_mul_cancel_left, h2, mul_one]

end UpperTheory.ConvolutionTheory.D
end
end

section

noncomputable section

open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

private theorem sum_pow_fix {α M : Type} [Monoid α] [AddCommGroup M] (a : α) (q : ℕ) (h : a ^ q = 1) (f : α → M) :
    ∑ j ∈ Finset.range q, f (a ^ (j + 1)) = ∑ j ∈ Finset.range q, f (a ^ j) := by
  have h1 := Finset.sum_range_succ (fun j => f (a ^ j)) q
  have h2 := Finset.sum_range_succ' (fun j => f (a ^ j)) q
  rw [h1, h, pow_zero] at h2
  exact (add_right_cancel h2).symm

private theorem sep_sum {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (σ : R ≃ₐ[k] R) (q : ℕ) (hq : 0 < q)
    {t : ℕ} (x y : Fin t → R) (h : ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0)
    {M : Type} [AddCommGroup M] [Module R M] (v : ℕ → M) :
    ∑ i, x i • ∑ j ∈ Finset.range q, (σ ^ j) (y i) • v j = v 0 := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]]
  simp [hq]

theorem descent : Descent := by
  intro k R _ _ _ σ q hG M _ _ _ _ s hs hq
  obtain ⟨t, x, y, hxy⟩ := hG.sep
  have hsj : ∀ (j : ℕ) (r : R) (m : M), (s ^ j) (r • m) = (σ ^ j) r • (s ^ j) m := by
    intro j
    induction j with
    | zero => intro r m; simp
    | succ j ih =>
      intro r m
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, AlgEquiv.mul_apply, ih, hs]
  have hfix : ∀ (n : M), s n = n → ∀ j : ℕ, (s ^ j) n = n := by
    intro n hn j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, hn]
  have hT : ∀ m : M, (∑ j ∈ Finset.range q, s ^ j) m ∈ LinearMap.eqLocus s LinearMap.id := by
    intro m

    rw [LinearMap.mem_eqLocus, LinearMap.id_apply, LinearMap.sum_apply, map_sum,
    ← sum_pow_fix s q hq fun a => a m]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_succ', Module.End.mul_apply]
  have htr : ∀ r : R, ∃ c : k, algebraMap k R c = ∑ j ∈ Finset.range q, (σ ^ j) r := by
    intro r
    refine hG.fix _ ?_

    rw [map_sum, ← sum_pow_fix σ q hG.pow fun a => a r]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_succ', AlgEquiv.mul_apply]
  choose c hc using htr
  let T : M →ₗ[k] LinearMap.eqLocus s LinearMap.id := LinearMap.codRestrict _ _ hT
  have hTv : ∀ m, (T m : M) = ∑ j ∈ Finset.range q, (s ^ j) m := fun m => LinearMap.sum_apply _ _ _
  let g : M →ₗ[k] R ⊗[k] LinearMap.eqLocus s LinearMap.id :=
    ∑ i, (TensorProduct.mk k R _ (x i)).comp (T.comp (Algebra.lsmul k k M (y i)))
  have hg : ∀ m, g m = ∑ i, x i ⊗ₜ[k] T (y i • m) := fun m => LinearMap.sum_apply _ _ _
  refine Function.bijective_iff_has_inverse.2 ⟨g, fun z => ?_, fun m => ?_⟩
  · induction z with
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | tmul r n =>
      have h1 : ∀ i, T (y i • r • (n : M)) = c (y i * r) • n := by
        intro i
        apply Subtype.ext
        rw [hTv, Submodule.coe_smul, ← algebraMap_smul R (c _), hc, Finset.sum_smul, smul_smul]
        exact Finset.sum_congr rfl fun j _ => by rw [hsj, hfix n n.2]
      have h2 : ∑ i, c (y i * r) • x i = r := by
        have := sep_sum σ q hG.pos x y hxy (M := R) fun j => (σ ^ j) r
        simp only [pow_zero, AlgEquiv.one_apply] at this
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
        rw [Algebra.smul_def, hc, smul_eq_mul, mul_comm]
        simp only [map_mul, smul_eq_mul]
      have h3 : TensorProduct.lift ((Algebra.lsmul k k M (A := R)).toLinearMap.compl₂
          (LinearMap.eqLocus s LinearMap.id).subtype) (r ⊗ₜ[k] n) = r • (n : M) := rfl
      rw [h3, hg]
      simp_rw [h1, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, h2]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hg, map_sum]
    have := sep_sum σ q hG.pos x y hxy fun j => (s ^ j) m
    simp only [pow_zero, Module.End.one_apply] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    change x i • (T (y i • m) : M) = _
    rw [hTv]
    simp only [hsj]

end UpperTheory.ConvolutionTheory.D
end
end
