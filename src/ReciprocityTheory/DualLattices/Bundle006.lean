module

public import ReciprocityTheory.DualLattices.Bundle002
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open WittVector MvPolynomial

namespace ReciprocityTheory.PGsh

section TeichSum

variable {p : ℕ} [hp : Fact p.Prime]

private lemma ghost_one {R : Type*} [CommRing R] (x : WittVector p R) :
    ghostComponent 1 x = x.coeff 0 ^ p + (p : R) * x.coeff 1 := by
  rw [WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow]
  simp [Finset.sum_range_succ] <;> ring

private lemma coeff_zero_sum {R ι : Type*} [CommRing R] (s : Finset ι) (f : ι → WittVector p R) :
    (∑ i ∈ s, f i).coeff 0 = ∑ i ∈ s, (f i).coeff 0 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, WittVector.add_coeff_zero, ih]

private lemma ringHom_aeval {K ι : Type*} [CommRing K] (σ : K →+* K) (g : ι → K)
    (S : MvPolynomial ι ℤ) : σ (aeval g S) = aeval (σ ∘ g) S := by
  induction S using MvPolynomial.induction_on <;> simp_all

private lemma univ_coeff {ι : Type} (s : Finset ι) :
    (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 0 = ∑ i ∈ s, X i ∧
    (p : MvPolynomial ι ℤ) * (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 1 =
      ∑ i ∈ s, X i ^ p - (∑ i ∈ s, X i) ^ p := by
  have h0 : (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 0 = ∑ i ∈ s, X i := by
    rw [coeff_zero_sum]
    simp
  refine ⟨h0, ?_⟩
  have hg : ghostComponent 1 (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)) =
      ∑ i ∈ s, (X i : MvPolynomial ι ℤ) ^ p := by

    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ghost_one]
    simp [WittVector.teichmuller_coeff_pos]
  rw [ghost_one, h0] at hg
  linear_combination hg

private lemma verschiebung_eq_map_frobenius_symm_mul_p {K : Type} [CommRing K] [CharP K p] [PerfectRing K p]
    (y : WittVector p K) :
    WittVector.verschiebung y = WittVector.map ((frobeniusEquiv K p).symm : K →+* K) y * p := by
  have hF : WittVector.frobenius (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) y) = y := by
    ext n
    rw [WittVector.coeff_frobenius_charP, WittVector.map_coeff]
    simp [frobeniusEquiv_symm_pow_p]
  calc WittVector.verschiebung y = WittVector.verschiebung
        (WittVector.frobenius (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) y)) := by
        rw [hF]
    _ = _ := WittVector.verschiebung_frobenius _

private lemma exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul {K : Type} [CommRing K] [CharP K p] [PerfectRing K p]
    (x : WittVector p K) :
    ∃ w : WittVector p K, x = teichmuller p (x.coeff 0) +
      (p : WittVector p K) * teichmuller p ((frobeniusEquiv K p).symm (x.coeff 1)) +
      (p : WittVector p K) ^ 2 * w := by
  have h1 : ∀ z : WittVector p K, ∃ u : WittVector p K,
      z = teichmuller p (z.coeff 0) + WittVector.verschiebung u ∧ u.coeff 0 = z.coeff 1 := by
    intro z
    refine ⟨WittVector.mk p (fun n => z.coeff (n + 1)), ?_, rfl⟩
    ext n
    rw [WittVector.coeff_add_of_disjoint]
    · rcases n with _ | n
      · simp [WittVector.teichmuller_coeff_zero, WittVector.verschiebung_coeff_zero]
      · simp [WittVector.teichmuller_coeff_pos, WittVector.verschiebung_coeff_succ]
    · intro m
      rcases m with _ | m
      · right
        simp [WittVector.verschiebung_coeff_zero]
      · left
        simp [WittVector.teichmuller_coeff_pos]
  obtain ⟨u, hu, hu0⟩ := h1 x
  rw [verschiebung_eq_map_frobenius_symm_mul_p] at hu
  obtain ⟨v, hv, -⟩ := h1 (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u)
  rw [verschiebung_eq_map_frobenius_symm_mul_p] at hv
  have hc : (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u).coeff 0 =
      (frobeniusEquiv K p).symm (x.coeff 1) := by
    rw [WittVector.map_coeff, hu0]
    try rfl
  rw [hc] at hv
  refine ⟨WittVector.map ((frobeniusEquiv K p).symm : K →+* K) v, ?_⟩
  calc x = teichmuller p (x.coeff 0) +
        WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u * p := hu
    _ = teichmuller p (x.coeff 0) + (teichmuller p ((frobeniusEquiv K p).symm (x.coeff 1)) +
          WittVector.map ((frobeniusEquiv K p).symm : K →+* K) v * p) * p := by rw [hv]
    _ = _ := by ring

theorem teichSum (p : ℕ) [Fact p.Prime] : TeichSumStatement p := by
  intro ι s
  refine ⟨⟨_, (univ_coeff (p := p) s).2⟩, ?_⟩
  intro K _ _ _ X S hS
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (∑ i ∈ s, teichmuller p (X i))
    have h0 : (∑ i ∈ s, teichmuller p (X i)).coeff 0 = ∑ i ∈ s, X i := by
      rw [coeff_zero_sum]
      simp
    have hmap : WittVector.map (MvPolynomial.aeval X).toRingHom
        (∑ i ∈ s, teichmuller p (MvPolynomial.X i : MvPolynomial ι ℤ)) =
          ∑ i ∈ s, teichmuller p (X i) := by

      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [WittVector.map_teichmuller]
      simp
    have hSeq : (∑ i ∈ s, teichmuller p (MvPolynomial.X i : MvPolynomial ι ℤ)).coeff 1 = S := by
      have hp0 : (p : MvPolynomial ι ℤ) ≠ 0 := by
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      exact mul_left_cancel₀ hp0 ((univ_coeff (p := p) s).2.trans hS.symm)
    have h1 : (∑ i ∈ s, teichmuller p (X i)).coeff 1 = MvPolynomial.aeval X S := by
      rw [← hmap, WittVector.map_coeff, hSeq]
      try rfl
    have hfr : (frobeniusEquiv K p).symm (MvPolynomial.aeval X S) =
        MvPolynomial.aeval (fun i => (frobeniusEquiv K p).symm (X i)) S :=
      ringHom_aeval ((frobeniusEquiv K p).symm : K →+* K) X S
    refine ⟨w, ?_⟩
    rw [h0, h1, hfr] at hw
    exact hw
  · intro y t
    have hd : ((p : ℕ) : WittVector p K) ∣ (teichmuller p y + (p : WittVector p K) * t) -
        teichmuller p y := ⟨t, by ring⟩
    obtain ⟨w, hw⟩ := dvd_sub_pow_of_dvd_sub hd 1
    refine ⟨w, ?_⟩
    simp only [pow_one] at hw
    rw [show teichmuller p (y ^ p) = teichmuller p y ^ p from map_pow _ _ _]
    linear_combination hw

end TeichSum

section Cyclic

end Cyclic

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

def ξmul {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker) :
    (R' : Type u) →ₗ[R₀] π.ker where
  toFun r := ⟨ξ * r, by
    rw [Submodule.restrictScalars_mem] at hξ ⊢
    exact Ideal.mul_mem_right r _ hξ⟩
  map_add' a b := by ext; simp [mul_add]
  map_smul' c r := by ext; simp

namespace BX

variable (B : BX R₀)

def ev {R' : LAlg R₀} (h : B.gg →ₗ[R₀] R') (v : B.gg ⊗[R₀] (R' : Type u)) : R' :=
  LinearMap.mul' R₀ R' (TensorProduct.map h LinearMap.id v)

end BX

end ReciprocityTheory.PGsh
end
end

section

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

structure DualPair (R : LAlg R₀) where
  D : LAlg R₀
  π : LHom D R
  σ : LHom R D
  η : (D : Type u)
  sect : ∀ r, π.1 (σ.1 r) = r
  η_sq : η * η = 0
  ker_eq : RingHom.ker π.1 = Ideal.span {η}
  free : ∀ r, σ.1 r * η = 0 → r = 0

namespace DualPair

variable {R : LAlg R₀} (Dp : DualPair R)

lemma η_mem : Dp.η ∈ Dp.π.ker := by
  show Dp.η ∈ RingHom.ker Dp.π.1
  rw [Dp.ker_eq]
  exact Ideal.subset_span (Set.mem_singleton _)

lemma sqZero : Dp.π.SqZero := by
  refine ⟨fun r => ⟨Dp.σ.1 r, Dp.sect r⟩, ?_⟩
  rw [Dp.ker_eq, Ideal.span_singleton_pow, pow_two, Dp.η_sq, Ideal.span_singleton_eq_bot]

def ηk : Dp.π.ker := ⟨Dp.η, Dp.η_mem⟩

end DualPair

namespace BX

variable (B : BX R₀)

def IsHeight {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (y : B.G R) (h : B.gg →ₗ[R₀] R) : Prop :=
  ∀ v : B.gg, ∃ z : (Dp.D : Type u)ˣ,
    B.IsPairing N (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y) z ∧ (z : Dp.D) = 1 + Dp.σ.1 (h v) * Dp.η

end BX

def HighestWeightVectorUniformBounds (B : BX R₀) : Prop :=
  ∀ (R : LAlg R₀) (Dp : DualPair R) (N : ℕ), (N : (R : Type u)) = 0 →
    (∀ (y : B.G R) (v : B.gg) (u : B.P Dp.D (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y)),
      HEq (B.pmap Dp.π u) (B.zero1 y) →
      HEq (B.nsmul1 u N) (B.zero1 (B.map Dp.σ y))) ∧
    (∀ y : B.G R, N • y = 0 → ∃! h : B.gg →ₗ[R₀] R, B.IsHeight Dp N y h) ∧
    (∀ (y y' : B.G R) (h h' : B.gg →ₗ[R₀] R), B.IsHeight Dp N y h → B.IsHeight Dp N y' h' →
      B.IsHeight Dp N (y + y') (h + h'))

end ReciprocityTheory.PGsh
end

section

noncomputable section

open WittVector Ideal TensorProduct

namespace ReciprocityTheory.PGsh

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

private lemma frob_bij : Function.Bijective (WittVector.frobenius : WittVector p R → WittVector p R) := by
  constructor
  · intro x y h
    ext n
    have h' := congrArg (fun z => WittVector.coeff z n) h
    simp only [WittVector.coeff_frobenius_charP] at h'
    apply (frobeniusEquiv R p).injective
    rw [_root_.frobeniusEquiv_apply, _root_.frobeniusEquiv_apply, frobenius_def, frobenius_def]
    exact h'
  · intro x
    refine ⟨WittVector.mk p (fun n => (frobeniusEquiv R p).symm (x.coeff n)), ?_⟩
    ext n
    rw [WittVector.coeff_frobenius_charP, WittVector.coeff_mk]
    have h := (frobeniusEquiv R p).apply_symm_apply (x.coeff n)
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h

lemma mem_span_p_iff (x : WittVector p R) : x ∈ span {(p : WittVector p R)} ↔ x.coeff 0 = 0 := by
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [← WittVector.verschiebung_frobenius, WittVector.verschiebung_coeff_zero]
  · intro hx
    obtain ⟨y, hy⟩ := (frob_bij (p := p) (R := R)).2 (WittVector.mk p (fun n => x.coeff (n + 1)))
    refine Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩
    rw [← WittVector.verschiebung_frobenius, hy]
    ext n
    cases n with
    | zero => rw [WittVector.verschiebung_coeff_zero, hx]
    | succ n => exact WittVector.verschiebung_coeff_succ _ n

lemma p_mul_eq_zero (x : WittVector p R) (h : x * p = 0) : x = 0 := by
  rw [← WittVector.verschiebung_frobenius] at h
  have h2 : WittVector.frobenius x = 0 := by
    ext n
    have h3 := congrArg (fun z => WittVector.coeff z n.succ) h
    simpa only [WittVector.verschiebung_coeff_succ, WittVector.zero_coeff] using h3
  apply (frob_bij (p := p) (R := R)).1
  rw [h2, map_zero]

lemma p_mem_nonZeroDivisors : (p : WittVector p R) ∈ nonZeroDivisors (WittVector p R) := mem_nonZeroDivisors_iff.mpr
  ⟨fun x hx => p_mul_eq_zero x (by rwa [mul_comm] at hx), fun x hx => p_mul_eq_zero x hx⟩

private lemma mul_root_eq_zero (w y : R) (h : w * y = 0) :
    w * (frobeniusEquiv R p).symm y = 0 := by
  have hr : ((frobeniusEquiv R p).symm y) ^ p = y := by
    have h1 := (frobeniusEquiv R p).apply_symm_apply y
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h1
  have hz : (w * (frobeniusEquiv R p).symm y) ^ p = 0 := by
    rw [mul_pow, hr]
    calc w ^ p * y = w ^ (p - 1) * (w * y) := by
          rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.out.pos]
      _ = 0 := by rw [h, mul_zero]
  apply (frobeniusEquiv R p).injective
  rw [map_zero, _root_.frobeniusEquiv_apply, frobenius_def, hz]

private lemma mul_iterate_root_eq_zero (w y : R) (h : w * y = 0) (n : ℕ) :
    w * ((frobeniusEquiv R p).symm^[n]) y = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mul_root_eq_zero w _ ih

end Witt

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type*} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

lemma pflat_mul_eq_zero (hO : ∀ x : O, (p : O) * x = 0 → x = 0) (pflat : PreTilt O p)
    (hpf : pflat.untilt = (p : O)) (x : PreTilt O p) (hx : pflat * x = 0) : x = 0 := by
  have hu0 : (0 : PreTilt O p).untilt = 0 := by
    have h1 : (0 : PreTilt O p).untilt = (p : O) * (0 : PreTilt O p).untilt := by
      rw [← hpf, ← map_mul, mul_zero]
    have hJ := IsAdicComplete.le_jacobson_bot (span {(p : O)}) (Ideal.mem_span_singleton_self (p : O))
    rw [Ideal.mem_jacobson_bot] at hJ
    have h2 : ((p : O) * -1 + 1) * (0 : PreTilt O p).untilt = 0 := by
      linear_combination h1
    exact ((hJ (-1)).mul_right_eq_zero).mp h2
  have hzero : ∀ y : PreTilt O p, pflat * y = 0 → PreTilt.coeff 0 y = 0 := by
    intro y hy
    have h1 : (p : O) * y.untilt = 0 := by rw [← hpf, ← map_mul, hy, hu0]
    rw [← PreTilt.mk_untilt_eq_coeff_zero, hO _ h1, map_zero]
  have hred : ∀ n : ℕ, pflat * ((frobeniusEquiv (PreTilt O p) p).symm^[n]) x = 0 :=
    mul_iterate_root_eq_zero pflat x hx
  have hli : Function.LeftInverse (frobenius (PreTilt O p) p) (frobeniusEquiv (PreTilt O p) p).symm :=
    fun z => by rw [← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  apply Perfection.ext
  intro n
  have key := Perfection.coeff_iterate_frobenius (R := ModP O p) (p := p)
    ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) 0 n
  rw [zero_add] at key
  erw [hli.iterate n x] at key
  exact key.trans ((hzero _ (hred n)).trans (map_zero (Perfection.coeff (ModP O p) p n)).symm)

end Tilt

section Main

variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem regular (hO : ∀ x : O, (p : O) * x = 0 → x = 0) : RegularStatement p O := by
  intro pflat hpf
  refine ⟨p_mem_nonZeroDivisors, ?_, ?_⟩
  · intro x hx
    rw [mem_span_p_iff] at hx ⊢
    rw [WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero] at hx
    exact pflat_mul_eq_zero hO pflat hpf _ hx
  · intro htop
    have h1 : (1 : WittVector p (PreTilt O p)) ∈
        span {(p : WittVector p (PreTilt O p)), teichmuller p pflat} := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨c, e, hce⟩ := Ideal.mem_span_pair.mp h1
    have h2 := congrArg (fun z => WittVector.coeff z 0) hce
    simp only [WittVector.add_coeff_zero, WittVector.mul_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h2
    have hp0 : (p : WittVector p (PreTilt O p)).coeff 0 = 0 := by
      rw [← mem_span_p_iff]; exact Ideal.mem_span_singleton_self _
    rw [hp0, mul_zero, zero_add, mul_comm] at h2
    have hu : IsUnit pflat := ⟨⟨pflat, _, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
    have h3 := hu.map (PreTilt.untilt (O := O) (p := p))
    rw [hpf] at h3
    exact (Fact.out : ¬IsUnit (p : O)) h3

end Main

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem map_tensorSpan {X Y : Type} (σ : Y → X) (M : Submodule R (X → C)) :
    (tensorSpan R M).map (LinearMap.funLeft R C (Prod.map σ σ)) =
      tensorSpan R (M.map (LinearMap.funLeft R C σ)) := by
  rw [tensorSpan, tensorSpan, Submodule.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨_, ⟨g, hg, h, hh, rfl⟩, rfl⟩
    exact ⟨_, Submodule.mem_map_of_mem hg, _, Submodule.mem_map_of_mem hh, by
      funext p; simp [LinearMap.funLeft_apply]⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, _, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, h, hh, rfl⟩, by funext p; simp [LinearMap.funLeft_apply]⟩

end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
end
end

section

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

def PairingPropertiesStatement (B : BX R₀) : Prop :=
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R), N • x = 0 → N • y = 0 → ∃ z, B.IsPairing N x y z) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x y z' → z = z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x x' y : B.G R) (z z' w : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x' y z' → B.IsPairing N (x + x') y w → w = z * z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y y' : B.G R) (z z' w : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x y' z' → B.IsPairing N x (y + y') w → w = z * z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N y x z' → z * z' = 1) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ), B.IsPairing N x y z → z ^ N = 1) ∧
  (∀ (R S : LAlg R₀) (f : LHom R S) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N (B.map f x) (B.map f y) (Units.map (f.1 : R →* S) z)) ∧
  (∀ (R : LAlg R₀) (N p : ℕ) (x y : B.G R) (z : (R : Type u)ˣ), N • x = 0 → (N * p) • y = 0 →
    B.IsPairing (N * p) x y z → B.IsPairing N x (p • y) z)

end ReciprocityTheory.PGsh
end
