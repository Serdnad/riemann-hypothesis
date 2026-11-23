module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle002
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
public import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

namespace UpperTheory.ConvolutionTheory.D

section

variable {S T : Type} [CommRing S] [CommRing T] [Algebra S T]

private theorem pow_succ_app (σ : T ≃ₐ[S] T) (j : ℕ) (t : T) : (σ ^ (j + 1)) t = σ ((σ ^ j) t) := by
  rw [pow_succ', AlgEquiv.mul_apply]

private theorem pow_succ_app' (σ : T ≃ₐ[S] T) (j : ℕ) (t : T) : (σ ^ (j + 1)) t = (σ ^ j) (σ t) := by
  rw [pow_succ, AlgEquiv.mul_apply]

private theorem exists_notMem {σ : T ≃ₐ[S] T} {q : ℕ} (h : IsGal σ q) (a : T)
    (ha : ∏ i ∈ Finset.range q, (σ ^ i) a = 1) (P : Ideal T) (hP : P ≠ ⊤) :
    ∃ z, a * σ z = z ∧ z ∉ P := by
  obtain ⟨s, x, y, hxy⟩ := h.sep
  let c : ℕ → T := fun j => ∏ i ∈ Finset.range j, (σ ^ i) a
  have hc : ∀ j, a * σ (c j) = c (j + 1) := by
    intro j
    simp only [c]
    rw [Finset.prod_range_succ', map_prod, mul_comm]
    simp only [pow_succ_app, pow_zero, AlgEquiv.one_apply]
  let z : T → T := fun t => ∑ j ∈ Finset.range q, c j * (σ ^ j) t
  have hz : ∀ t, a * σ (z t) = z t := by
    intro t
    have h1 : a * σ (z t) = ∑ j ∈ Finset.range q, c (j + 1) * (σ ^ (j + 1)) t := by

      simp only [z, map_sum, Finset.mul_sum, map_mul, ← hc, pow_succ_app, mul_assoc]
    have h2 := Finset.sum_range_succ (fun j => c j * (σ ^ j) t) q
    rw [Finset.sum_range_succ'] at h2
    have h3 : c q = 1 := ha
    have h4 : c 0 = 1 := by simp [c]
    rw [h3, h4, h.pow, pow_zero] at h2
    rw [h1]
    exact add_right_cancel h2
  have hs : ∑ i, x i * z (y i) = 1 := by
    have : ∑ i, x i * z (y i) = ∑ j ∈ Finset.range q, c j * ∑ i, x i * (σ ^ j) (y i) := by
      simp only [z, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this, Finset.sum_eq_single 0]
    · rw [hxy 0 h.pos]; simp [c]
    · intro j hj hj0
      rw [hxy j (Finset.mem_range.1 hj), if_neg hj0, mul_zero]
    · intro h0
      exact absurd (Finset.mem_range.2 h.pos) h0
  by_contra hcon
  push Not at hcon
  apply hP
  rw [Ideal.eq_top_iff_one, ← hs]
  exact P.sum_mem fun i _ => P.mul_mem_left _ (hcon _ (hz _))

private theorem mem_of_mem {σ : T ≃ₐ[S] T} {q : ℕ} (h : IsGal σ q) (a z : T) (hz : a * σ z = z)
    (P Q : Ideal T) [Q.IsPrime] (hPQ : P.comap (algebraMap S T) = Q.comap (algebraMap S T))
    (hzP : z ∈ P) : z ∈ Q := by
  have hd : ∀ j, (σ ^ j) z ∣ z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine dvd_trans ?_ ih
      rw [pow_succ_app']
      conv_rhs => rw [← hz, map_mul]
      exact dvd_mul_left _ _
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := h.pos; omega⟩
  have hN : σ (∏ j ∈ Finset.range (r + 1), (σ ^ j) z) = ∏ j ∈ Finset.range (r + 1), (σ ^ j) z := by
    rw [map_prod]
    simp only [← pow_succ_app]
    rw [Finset.prod_range_succ, h.pow, Finset.prod_range_succ' _ r, pow_zero]
  obtain ⟨n, hn⟩ := h.fix _ hN
  have h1 : algebraMap S T n ∈ P := by
    rw [hn, Finset.prod_range_succ']
    exact P.mul_mem_left _ (by simpa using hzP)
  have h2 : algebraMap S T n ∈ Q := by
    rw [← Ideal.mem_comap, ← hPQ]; exact h1
  rw [hn, Ideal.IsPrime.prod_mem_iff] at h2
  obtain ⟨j, -, hj⟩ := h2
  exact Q.mem_of_dvd (hd j) hj

end

private theorem finite_max (k S : Type) [CommRing k] [IsLocalRing k] [CommRing S] [Algebra k S]
    [Module.Finite k S] : Finite (MaximalSpectrum S) := by
  have hf := Algebra.QuasiFinite.finite_primesOver (R := k) (S := S) (IsLocalRing.maximalIdeal k)
  have : Finite ((IsLocalRing.maximalIdeal k).primesOver S) := hf
  refine Finite.of_injective (β := (IsLocalRing.maximalIdeal k).primesOver S)
    (fun m => ⟨m.asIdeal, m.isMaximal.isPrime, ⟨?_⟩⟩) ?_
  · have := m.isMaximal
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := k) m.asIdeal)).symm
  · intro m m' hm
    exact MaximalSpectrum.ext (congrArg Subtype.val hm)

theorem h90 : H90 := by
  intro k R _ _ _ _ S T _ _ _ _ _ σ q h a ha
  classical
  have hfin : Module.Finite S T := (galBase S T S σ q h).1
  have := finite_max k S
  have := Fintype.ofFinite (MaximalSpectrum S)
  have hloc : ∀ m : MaximalSpectrum S, ∃ z : T, a * σ z = z ∧
      ∀ P : Ideal T, P.IsMaximal → P.comap (algebraMap S T) = m.asIdeal → z ∉ P := by
    intro m
    by_cases hm : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.comap (algebraMap S T) = m.asIdeal
    · obtain ⟨Q, hQ, hQm⟩ := hm
      obtain ⟨z, hz, hzQ⟩ := exists_notMem h a ha Q hQ.ne_top
      exact ⟨z, hz, fun P _ hP hzP => hzQ (mem_of_mem h a z hz P Q (hP.trans hQm.symm) hzP)⟩
    · exact ⟨0, by simp, fun P hP hPm => (hm ⟨P, hP, hPm⟩).elim⟩
  choose z hz hzP using hloc
  have he : ∀ m : MaximalSpectrum S, ∃ e : S, e - 1 ∈ m.asIdeal ∧ ∀ m', m' ≠ m → e ∈ m'.asIdeal := by
    intro m
    obtain ⟨e, he⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum S => m.asIdeal)
      (fun m m' hne => MaximalSpectrum.isCoprime_of_ne hne) (Pi.single m 1)
    refine ⟨e, ?_, fun m' hne => ?_⟩
    · rw [← Ideal.Quotient.eq, he m, Pi.single_eq_same, map_one]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, he m', Pi.single_eq_of_ne hne]
  choose e he1 he0 using he
  have hu : IsUnit (∑ m, algebraMap S T (e m) * z m) := by
    by_contra hnu
    obtain ⟨P, hP, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
    let m : MaximalSpectrum S := ⟨P.comap (algebraMap S T), Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := S) P⟩
    apply hzP m P hP rfl
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)] at hmem
    have h1 : ∑ m' ∈ Finset.univ.erase m, algebraMap S T (e m') * z m' ∈ P :=
      P.sum_mem fun m' hm' => P.mul_mem_right _ (he0 m' m (Finset.ne_of_mem_erase hm').symm)
    have h2 : algebraMap S T (e m - 1) * z m ∈ P := P.mul_mem_right _ (he1 m)
    have h3 := P.sub_mem (P.sub_mem hmem h1) h2
    rw [map_sub, map_one] at h3
    convert h3 using 1
    ring
  refine ⟨hu.unit, ?_⟩

  rw [hu.unit_spec, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, σ.commutes, mul_left_comm, hz]

end UpperTheory.ConvolutionTheory.D
end

section

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.D.galExt :
    UpperTheory.ConvolutionTheory.D.GalExt := by
  intro F E k _ _ _ _ _ σ q h
  exact (UpperTheory.ConvolutionTheory.D.galBase F E k σ q h).2.2.2
end

section

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

private theorem desc_alg {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) (hG : IsGal c 2)
    (L : Type) [CommRing L] [Algebra k L] [Algebra R L] [IsScalarTower k R L] (s : L →ₐ[k] L)
    (hs : ∀ r, s (algebraMap R L r) = algebraMap R L (c r)) (hss : ∀ z, s (s z) = z) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (e : R ⊗[k] A ≃ₐ[R] L), ∀ z, e (io c A z) = s (e z) := by
  let A : Subalgebra k L := AlgHom.equalizer s (AlgHom.id k L)
  let f : R ⊗[k] A →ₐ[R] L := Algebra.TensorProduct.lift (Algebra.ofId R L) A.val fun _ _ => Commute.all _ _
  have hf : ∀ (r : R) (a : A), f (r ⊗ₜ a) = algebraMap R L r * a := fun r a => rfl
  have hb := descent k R c 2 hG L s.toLinearMap
    (fun r m => by simp [Algebra.smul_def, hs]) (LinearMap.ext fun z => by simp [pow_two, hss])
  let j : A ≃ₗ[k] LinearMap.eqLocus s.toLinearMap LinearMap.id :=
    { toFun := fun a => ⟨a.1, a.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hbij : Function.Bijective f := by
    have h2 := hb.comp (j.lTensor R).bijective
    convert h2 using 1
    funext z
    induction z with
    | add a b ha hb => simp only [Function.comp_apply, map_add (f := _)] at ha hb ⊢; rw [ha, hb]
    | tmul r a => rw [hf, ← Algebra.smul_def]; rfl
  refine ⟨A, inferInstance, inferInstance, AlgEquiv.ofBijective f hbij, fun z => ?_⟩
  change f _ = s (f z)
  induction z with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul r a =>
    have h1 : io c A (r ⊗ₜ a) = c r ⊗ₜ a := by simp [io]
    have h2 : s a = a := a.2
    rw [h1, hf, hf, map_mul, hs, h2]

private theorem inv_ex {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) (hc : c ^ 2 = 1)
    {n : ℕ} {P : R[X]} (hP : IsCsr c n P) :
    ∃ s : AdjoinRoot P →ₐ[k] AdjoinRoot P, (∀ r, s (algebraMap R _ r) = algebraMap R _ (c r)) ∧ (∀ z, s (s z) = z) ∧
      AdjoinRoot.root P * s (AdjoinRoot.root P) = 1 := by
  obtain ⟨hm, hn, hu, hr⟩ := hP
  have hcc : ∀ r, c (c r) = r := fun r => by
    rw [← AlgEquiv.mul_apply, ← pow_two, hc]; rfl
  have hx : IsUnit (AdjoinRoot.root P) := by
    have h1 : AdjoinRoot.mk P (X * P.divX + C (P.coeff 0)) = 0 := by
      rw [X_mul_divX_add, AdjoinRoot.mk_self]
    rw [map_add (f := _), map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h1
    have h2 := (hu.map (AdjoinRoot.of P)).neg
    rw [← eq_neg_of_add_eq_zero_left h1] at h2
    exact isUnit_of_mul_isUnit_left h2
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  letI : Invertible y := ⟨AdjoinRoot.root P, hy, by rw [mul_comm, hy]⟩
  have h0 : P.eval₂ ((AdjoinRoot.of P).comp (c : R →+* R)) y = 0 := by
    rw [← eval₂_map, ← eval₂_reflect_eq_zero_iff _ y n _ (natDegree_map_le.trans hn.le), hr, eval₂_mul]
    exact mul_eq_zero_of_right _ (AdjoinRoot.eval₂_root P)
  let s0 : AdjoinRoot P →+* AdjoinRoot P := AdjoinRoot.lift _ y h0
  have h1 : ∀ r, s0 (AdjoinRoot.of P r) = AdjoinRoot.of P (c r) := fun r => AdjoinRoot.lift_of h0
  have h2 : s0 (AdjoinRoot.root P) = y := AdjoinRoot.lift_root h0
  have h3 : s0 y = AdjoinRoot.root P := by
    have := congrArg s0 hy
    rw [map_mul, map_one, h2] at this
    calc s0 y = (AdjoinRoot.root P * y) * s0 y := by rw [hy, one_mul]
      _ = _ := by rw [mul_assoc, this, mul_one]
  refine ⟨⟨s0, fun a => ?_⟩, h1, fun z => ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_apply k R (AdjoinRoot P)]
    exact (h1 _).trans (by rw [c.commutes]; rfl)
  · change s0 (s0 z) = z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    induction p using Polynomial.induction_on with
    | C a => rw [AdjoinRoot.mk_C, h1, h1, hcc]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | monomial m a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, map_mul, ih, AdjoinRoot.mk_X, h2, h3]
  · change _ * s0 _ = 1
    rw [h2, hy]

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.modelEx :
    UpperTheory.ConvolutionTheory.D.ModelEx := by
  intro k R _ _ _ _ c hG n P hP hsep
  obtain ⟨s, hs, hss, hx⟩ := inv_ex c hG.pow hP
  obtain ⟨A, _, _, e, he⟩ := desc_alg c hG (AdjoinRoot P) s hs hss
  obtain ⟨-, -, hff, -⟩ := galBase k R k c 2 hG
  obtain ⟨hm, hn, -, -⟩ := hP
  haveI : Nontrivial R := hG.inj.nontrivial
  let B := (AdjoinRoot.powerBasis' hm).basis.map e.symm.toLinearEquiv
  haveI : Module.Finite R (R ⊗[k] A) := Module.Finite.of_basis B
  haveI : Module.Free R (R ⊗[k] A) := Module.Free.of_basis B
  haveI : Module.Finite k A := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat R
  haveI : Module.Flat k A := Module.Flat.of_flat_tensorProduct k A R
  haveI : Module.Free k A := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank k A = n := by
    rw [← Module.finrank_baseChange (R := R), Module.finrank_eq_card_basis B, Fintype.card_fin, ← hn]
    rfl
  let b := Module.finBasisOfFinrankEq k A hr
  have h1 : e.symm (AdjoinRoot.root P) * io c A (e.symm (AdjoinRoot.root P)) = 1 := by
    apply e.injective
    rw [map_mul, he, e.apply_symm_apply, hx, map_one]
  let g : (R ⊗[k] A)ˣ := Units.mkOfMulEqOne _ _ h1
  have h2 : cp (matU b g) = P := by
    set M := Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b) (e.symm (AdjoinRoot.root P)) with hM
    change M.charpoly = P
    have h3 : aeval (AdjoinRoot.root P) M.charpoly = 0 := by
      have h4 := Matrix.aeval_self_charpoly M
      rw [hM, aeval_algHom_apply, ← hM, map_eq_zero_iff _ (Algebra.leftMulMatrix_injective _),
        aeval_algHom_apply] at h4
      exact (map_eq_zero_iff _ e.symm.injective).1 h4
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h3
    exact eq_of_monic_of_dvd_of_natDegree_le hm M.charpoly_monic h3
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hn])
  exact ⟨A, _, _, b, g, ⟨h1, h2 ▸ hsep⟩, h2⟩
end

section

noncomputable section

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem rep_sg_succ (σ : R ≃ₐ[k] R) (i : ℕ) (d : GL (Fin n) R) :
    sg (σ ^ (i + 1)) d = sg σ (sg (σ ^ i) d) := by
  ext a b
  simp [sg, pow_succ', Matrix.GeneralLinearGroup.map_apply]

private theorem rep_sg_one (d : GL (Fin n) R) : sg (1 : R ≃ₐ[k] R) d = d := by
  ext a b
  simp [sg, Matrix.GeneralLinearGroup.map_apply]

private theorem rep_sg_up (σ : R ≃ₐ[k] R) (γ : GL (Fin n) k) : sg σ (up R γ) = up R γ := by
  ext a b
  simp [sg, up, Matrix.GeneralLinearGroup.map_apply]

private theorem rep_nm_succ (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    nm σ (q + 1) d = nm σ q d * sg (σ ^ q) d := by
  simp [nm, List.range_succ]

private theorem rep_shift (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    d * sg σ (nm σ q d) = nm σ q d * sg (σ ^ q) d := by
  induction q with
  | zero => simp [nm, rep_sg_one]
  | succ q ih => rw [rep_nm_succ, map_mul, ← mul_assoc, ih, rep_sg_succ]

private theorem rep_cp_up (γ : GL (Fin n) k) : cp (up R γ) = (cp γ).map (algebraMap k R) := by
  rw [cp, cp, ← Matrix.charpoly_map]
  rfl

end

theorem nmRep : NmRep := by
  intro k R _ _ _ _ σ q hσ n δ γ hsep hcp
  haveI : Module.Finite k R := (galBase k R k σ q hσ).1
  have hs : ((nm σ q δ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpoly.Separable := by
    have h := hsep.map (f := algebraMap k R)
    rwa [← hcp] at h
  obtain ⟨x, hx⟩ := (conjSep k R n _ hs).1 ((up R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
    ((rep_cp_up γ).trans hcp.symm)
  have hx' : nm σ q δ * x = x * up R γ := Units.ext (by simpa using hx)
  have h1 : nm σ q (sgConj σ x δ) = up R γ := by
    rw [(nmPoly k R σ q hσ n δ).2 x, mul_assoc, hx', inv_mul_cancel_left]
  refine ⟨x, h1, ?_⟩
  have h2 := rep_shift σ q (sgConj σ x δ)
  rw [h1, rep_sg_up, hσ.pow, rep_sg_one] at h2
  exact h2

end UpperTheory.ConvolutionTheory.D
end
end

section

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem cent_sg_up (σ : R ≃ₐ[k] R) (γ : GL (Fin n) k) : sg σ (up R γ) = up R γ := by
  ext a b
  simp [sg, up, Matrix.GeneralLinearGroup.map_apply]

private theorem cent_nm_sg (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    nm σ q (sg σ d) = sg σ (nm σ q d) := by
  unfold nm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  ext a b
  change (σ ^ m) (σ _) = σ ((σ ^ m) _)
  rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← pow_succ, ← pow_succ']

private theorem cent_up_inj (h : Function.Injective (algebraMap k R)) :
    Function.Injective (up R : GL (Fin n) k → GL (Fin n) R) := by
  intro s t hst
  ext a b
  exact h (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) a b) hst)

private theorem cent_descend {σ : R ≃ₐ[k] R} {q : ℕ} (hσ : IsGal σ q) (x : GL (Fin n) R) (hx : sg σ x = x) :
    ∃ t : GL (Fin n) k, x = up R t := by
  have key : ∀ y : GL (Fin n) R, sg σ y = y → ∃ M : Matrix (Fin n) (Fin n) k,
      M.map (algebraMap k R) = (y : Matrix (Fin n) (Fin n) R) := by
    intro y hy
    have h : ∀ a b, ∃ c, algebraMap k R c = (y : Matrix (Fin n) (Fin n) R) a b := fun a b =>
      hσ.fix _ (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) a b) hy)
    choose M hM using h
    exact ⟨Matrix.of M, by ext a b; exact hM a b⟩
  obtain ⟨M, hM⟩ := key x hx
  obtain ⟨N, hN⟩ := key x⁻¹ (by rw [map_inv, hx])
  have inj := Matrix.map_injective (m := Fin n) (n := Fin n) hσ.inj
  refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext hM.symm⟩
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.mul_inv]
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.inv_mul]

end

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.nmCent :
    UpperTheory.ConvolutionTheory.D.NmCent := by
  intro k R _ _ _ _ σ q hσ n a γ hsep ha x
  haveI : Module.Finite k R := (galBase k R k σ q hσ).1
  have hs : ((up R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpoly.Separable := by
    have h := hsep.map (f := algebraMap k R)
    rw [cp, ← Matrix.charpoly_map] at h
    exact h
  have hc := (conjSep k R n _ hs).2.1
  have hfix : ∀ y, nm σ q (sgConj σ y a) = up R γ → y * up R γ = up R γ * y := by
    intro y hy
    rw [(nmPoly k R σ q hσ n a).2 y, ha, mul_assoc, inv_mul_eq_iff_eq_mul] at hy
    exact hy.symm
  have hag : a * up R γ = up R γ * a := by
    apply hfix
    rw [sgConj, inv_mul_cancel, one_mul, cent_nm_sg, ha, cent_sg_up]
  have hcomm : ∀ y : GL (Fin n) R, y * up R γ = up R γ * y → a * y = y * a := by
    intro y hy
    obtain ⟨p, hp⟩ := hc a.val (by simpa using congrArg Units.val hag)
    obtain ⟨p', hp'⟩ := hc y.val (by simpa using congrArg Units.val hy)
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hp, hp', ← map_mul, ← map_mul, mul_comm]
  constructor
  · intro hx
    have h1 := hfix x (by rw [hx, ha])
    have h2 := hcomm x h1
    have h3 : sg σ x = x := by
      rw [sgConj, mul_assoc, inv_mul_eq_iff_eq_mul, ← h2] at hx
      exact mul_left_cancel hx
    obtain ⟨t, rfl⟩ := cent_descend hσ x h3
    refine ⟨t, cent_up_inj hσ.inj ?_, rfl⟩
    rw [map_mul, map_mul, h1]
  · rintro ⟨t, ht, rfl⟩
    have h2 := hcomm (up R t) (by rw [← map_mul, ← map_mul, ht.eq])
    rw [sgConj, cent_sg_up, mul_assoc, h2, inv_mul_cancel_left]
end
