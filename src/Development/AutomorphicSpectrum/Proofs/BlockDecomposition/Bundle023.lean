module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.PfCompl

open Ideal

variable {B T T₁ : Type*} [CommRing B] [CommRing T] [CommRing T₁]

theorem exists_level_hom (π : B) (g : B →+* T) (x : B →+* T₁) (M : ℕ)
    (hsurj : ∀ y : T, ∃ b, y - g b ∈ span {g π ^ M})
    (hinj : ∀ b, g b ∈ span {g π ^ M} → b ∈ span {π ^ M}) :
    ∃ f : T →+* T₁ ⧸ (span {x π}) ^ M,
      ∀ y b, y - g b ∈ span {g π ^ M} → f y = Ideal.Quotient.mk _ (x b) := by
  have hIJ : span {π ^ M} ≤ (span {g π ^ M}).comap g := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  have hxK : span {π ^ M} ≤ ((span {x π}) ^ M).comap x := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) M
  have hinj' : Function.Injective (Ideal.quotientMap (span {g π ^ M}) g hIJ) := by
    refine Ideal.quotientMap_injective' ?_
    intro b hb
    exact hinj b (Ideal.mem_comap.1 hb)
  have hsurj' : Function.Surjective (Ideal.quotientMap (span {g π ^ M}) g hIJ) := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨b, hb⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk _ b, by rw [Ideal.quotientMap_mk]; exact (Ideal.Quotient.eq.2 hb).symm⟩
  let e := RingEquiv.ofBijective _ ⟨hinj', hsurj'⟩
  refine ⟨(Ideal.quotientMap _ x hxK).comp (e.symm.toRingHom.comp (Ideal.Quotient.mk _)), ?_⟩
  intro y b hy
  have h1 : e (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk (span {g π ^ M}) y := by
    show Ideal.quotientMap _ g hIJ (Ideal.Quotient.mk _ b) = _
    rw [Ideal.quotientMap_mk]
    exact (Ideal.Quotient.eq.2 hy).symm
  have h2 : e.symm (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk (span {π ^ M}) b := by
    rw [← h1, RingEquiv.symm_apply_apply]
  show Ideal.quotientMap _ x hxK (e.symm (Ideal.Quotient.mk _ y)) = _
  rw [h2, Ideal.quotientMap_mk]

theorem mk_eq_of_comp_eq (π : B) (g : B →+* T) (x : B →+* T₁) (ψ : T →+* T₁)
    (hψ : ψ.comp g = x) (M : ℕ) (y : T) (b : B) (hy : y - g b ∈ span {g π ^ M}) :
    Ideal.Quotient.mk ((span {x π}) ^ M) (ψ y) = Ideal.Quotient.mk _ (x b) := by
  have hb : x b = ψ (g b) := (DFunLike.congr_fun hψ b).symm
  have hπ : ψ (g π) = x π := DFunLike.congr_fun hψ π
  rw [Ideal.Quotient.eq, hb, ← map_sub]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hy
  rw [← ht, map_mul, map_pow, hπ]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) M)

theorem existsUnique_comp_eq (π : B) (g : B →+* T)
    (hsurj : ∀ (M : ℕ) (y : T), ∃ b, y - g b ∈ span {g π ^ M})
    (hinj : ∀ (M : ℕ) (b : B), g b ∈ span {g π ^ M} → b ∈ span {π ^ M})
    (x : B →+* T₁) (hc : IsAdicComplete (span {x π}) T₁) :
    ∃! ψ : T →+* T₁, ψ.comp g = x := by
  have key : ∀ a c : T₁,
      (∀ n : ℕ, Ideal.Quotient.mk (span {x π} ^ n) a = Ideal.Quotient.mk _ c) → a = c := by
    intro a c h
    have h0 := IsHausdorff.haus' (I := span {x π}) (a - c) fun n => by
      rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
      exact Ideal.Quotient.eq.1 (h n)
    exact sub_eq_zero.1 h0
  choose f hf using fun n => exists_level_hom π g x n (hsurj n) (hinj n)
  have hle : ∀ {m n : ℕ}, m ≤ n → ∀ z : T, z ∈ span {g π ^ n} → z ∈ span {g π ^ m} := by
    intro m n h z hz
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine Ideal.mem_span_singleton'.2 ⟨t * g π ^ (n - m), ?_⟩
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]
  have hcompat : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow (span {x π}) h).comp (f n) = f m := by
    intro m n h
    ext y
    obtain ⟨b, hb⟩ := hsurj n y
    rw [RingHom.comp_apply, hf n y b hb, hf m y b (hle h _ hb)]
    first
      | rfl
      | exact Ideal.Quotient.factor_mk _ _
      | simp [Ideal.Quotient.factorPow]
  refine ⟨IsAdicComplete.liftRingHom _ f hcompat, ?_, ?_⟩
  · ext b
    apply key
    intro n
    rw [RingHom.comp_apply, IsAdicComplete.mk_liftRingHom, hf n (g b) b (by simp)]
  · intro ψ hψ
    ext y
    apply key
    intro n
    rw [IsAdicComplete.mk_liftRingHom]
    obtain ⟨b, hb⟩ := hsurj n y
    rw [hf n y b hb]
    exact mk_eq_of_comp_eq π g x ψ hψ n y b hb

end GlobalTheory.CompanionTheory.PfCompl
end

section

set_option backward.isDefEq.respectTransparency false
open MvPolynomial

namespace GlobalTheory.CompanionTheory.TraceDerivation

theorem trace_map_derivation : ∀ (K F L : Type) [Field K] [CharZero K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [FiniteDimensional F L]
    (D : Derivation K L L) (D0 : Derivation K F F),
    (∀ x : F, D (algebraMap F L x) = algebraMap F L (D0 x)) →
    ∀ y : L, algebraMap F L (D0 (Algebra.trace F L y)) =
      algebraMap F L (Algebra.trace F L (D y)) := by
  intro K F L _ _ _ _ _ _ _ _ _ D D0 h y
  classical
  let b := Module.finBasis F L
  let M := Algebra.leftMulMatrix b y
  let N := Algebra.leftMulMatrix b (D y)
  let C : Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F :=
    Matrix.of fun i j => b.repr (D (b j)) i
  have hmul : ∀ (z : L) (j), z * b j = ∑ i, Algebra.leftMulMatrix b z i j • b i := by
    intro z j
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
    exact (b.sum_repr _).symm
  have hD : ∀ j, D (b j) = ∑ k, C k j • b k := fun j => (b.sum_repr _).symm
  have hsmul : ∀ (a : F) (x : L), D (a • x) = D0 a • x + a • D x := by
    intro a x
    rw [Algebra.smul_def, D.leibniz, h, smul_eq_mul, smul_eq_mul, Algebra.smul_def,
      Algebra.smul_def]
    ring
  have h1 : ∀ j, ∑ i, (M * C) i j • b i = y * D (b j) := by
    intro j
    rw [hD j, Finset.mul_sum]
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, hmul y k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, mul_smul]
  have h2 : ∀ j, ∑ i, (C * M) i j • b i = ∑ k, M k j • D (b k) := by
    intro j
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hD k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, mul_smul]
  have key : ∀ j, ∑ i, (N + M * C) i j • b i = ∑ i, (M.map D0 + C * M) i j • b i := by
    intro j
    have e := congrArg D (hmul y j)

    rw [D.leibniz, map_sum] at e
    simp only [hsmul, Finset.sum_add_distrib, smul_eq_mul] at e
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, h1, h2, Matrix.map_apply]
    rw [← hmul (D y) j]
    rw [add_comm (D y * b j), mul_comm (D y), e]
  have hmat : N + M * C = M.map D0 + C * M := by
    ext i j
    have : b.repr (∑ i, (N + M * C) i j • b i) i = b.repr (∑ i, (M.map D0 + C * M) i j • b i) i := by
      rw [key j]
    rw [b.repr_sum_self, b.repr_sum_self] at this
    exact this
  have htr : Matrix.trace N = D0 (Matrix.trace M) := by
    have := congrArg Matrix.trace hmat
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm M C] at this
    have h3 := add_right_cancel this
    rw [h3]

    simp [Matrix.trace, map_sum]
  congr 1
  rw [Algebra.trace_eq_matrix_trace b y, Algebra.trace_eq_matrix_trace b (D y)]
  exact htr.symm

end GlobalTheory.CompanionTheory.TraceDerivation
end

section

namespace GlobalTheory.CompanionTheory.SplitQuadratic

theorem isPrincipalIdealRing_of_sq_eq_sq :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O]
      (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) →
      (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by
  intro R O _ _ _ _ ι δ e hδ hspan _ he h2
  obtain ⟨e', he'⟩ := he.exists_right_inv
  obtain ⟨h, hh⟩ := h2.exists_right_inv
  have hee' : ι e * ι e' = 1 := by rw [← map_mul, he', map_one]
  have h2' : 2 * ι h = 1 := by
    have := congrArg ι hh
    rwa [map_mul, map_one, map_ofNat] at this
  have hδ' : δ * δ = ι e * ι e := by rw [hδ, map_mul]

  have hu2 : (ι e' * δ) * (ι e' * δ) = 1 := by
    linear_combination (ι e' * ι e') * hδ' + (ι e * ι e' + 1) * hee'

  set ε₁ : O := ι h * (1 + ι e' * δ) with hε₁
  set ε₂ : O := ι h * (1 - ι e' * δ) with hε₂
  have h11 : ε₁ * ε₁ = ε₁ := by
    rw [hε₁]
    linear_combination (ι h * (1 + ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h22 : ε₂ * ε₂ = ε₂ := by
    rw [hε₂]
    linear_combination (ι h * (1 - ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h12 : ε₁ * ε₂ = 0 := by
    rw [hε₁, hε₂]
    linear_combination (-(ι h * ι h)) * hu2
  have hsum : ε₁ + ε₂ = 1 := by
    rw [hε₁, hε₂]
    linear_combination h2'

  let φ : R × R →+* O :=
    { toFun := fun x => ι x.1 * ε₁ + ι x.2 * ε₂
      map_one' := by
        simp only [Prod.fst_one, Prod.snd_one, map_one, one_mul]
        exact hsum
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination (-(ι x.1 * ι y.1)) * h11 + (-(ι x.2 * ι y.2)) * h22 +
          (-(ι x.1 * ι y.2 + ι x.2 * ι y.1)) * h12
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]
        ring }
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨p, q, rfl⟩ := hspan y
    refine ⟨(p + q * e, p - q * e), ?_⟩
    show ι (p + q * e) * ε₁ + ι (p - q * e) * ε₂ = ι p + ι q * δ
    rw [hε₁, hε₂]
    simp only [map_add (f := _), map_sub, map_mul]
    linear_combination (ι p + ι q * ι e * ι e' * δ) * h2' + (ι q * δ) * hee'
  exact IsPrincipalIdealRing.of_surjective φ hsurj

end GlobalTheory.CompanionTheory.SplitQuadratic
end

section

namespace GlobalTheory.CompanionTheory.Semistable

open MvPolynomial

theorem smooth_away_core (O : Type) [CommRing O] (ϖ : O) (σ : Type) [Finite σ] [DecidableEq σ]
    (T : Finset σ) (i0 : σ) (hi0 : i0 ∈ T) (F : Type) [Field F] [Algebra O F]
    [IsLocalization.Away ϖ F] :
    (IsLocalization.Away.map F
      (Localization.Away (algebraMap O (MvPolynomial σ O ⧸
        Ideal.span {(∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ))
      (algebraMap O (MvPolynomial σ O ⧸
        Ideal.span {(∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ})) ϖ).Smooth := by
  classical
  let P := MvPolynomial σ O
  let I : Ideal P := Ideal.span {(∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ}
  let A := P ⧸ I
  let a : A := algebraMap O A ϖ
  let B := Localization.Away a
  let C := MvPolynomial {j : σ // j ≠ i0} O
  let y : σ → C := fun i => if hi : i = i0 then 0 else MvPolynomial.X ⟨i, hi⟩
  let g : C := ∏ i ∈ T.erase i0, y i
  let h : C := MvPolynomial.C ϖ * g
  let C' := Localization.Away h
  let u : C' := IsLocalization.Away.invSelf h
  have hu : algebraMap C C' h * u = 1 := IsLocalization.Away.mul_invSelf h
  have hh : IsUnit (algebraMap C C' h) := IsLocalization.Away.algebraMap_isUnit h
  have e1 : algebraMap C C' h = algebraMap O C' ϖ * algebraMap C C' g := by
    rw [IsScalarTower.algebraMap_apply O C C' ϖ, MvPolynomial.algebraMap_eq, ← map_mul]
  have hϖ' : IsUnit (algebraMap O C' ϖ) := by
    rw [e1] at hh
    exact isUnit_of_mul_isUnit_left hh
  let z : σ → C' := fun i => if i = i0 then algebraMap O C' ϖ ^ 2 * u else algebraMap C C' (y i)
  have hzg : ∏ i ∈ T.erase i0, z i = algebraMap C C' g := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    simp only [z, if_neg (Finset.ne_of_mem_erase hi)]
  have hz : ∏ i ∈ T, z i = algebraMap O C' ϖ := by
    rw [← Finset.mul_prod_erase T z hi0, hzg]
    simp only [z, if_pos rfl]
    linear_combination (algebraMap O C' ϖ) * hu - (algebraMap O C' ϖ * u) * e1
  let ψP : P →ₐ[O] C' := MvPolynomial.aeval z
  have hψP : ∀ x ∈ I, ψP x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have h3 : ∀ i, ψP (MvPolynomial.X i) = z i := fun i => MvPolynomial.aeval_X z i
    have h4 : ψP (MvPolynomial.C ϖ) = algebraMap O C' ϖ := MvPolynomial.aeval_C z ϖ
    have h5 : ψP ((∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ) = 0 := by
      rw [map_sub, map_prod, h4]
      simp only [h3, hz, sub_self]
    rw [map_mul, h5, mul_zero]
  let ψA : A →ₐ[O] C' := Ideal.Quotient.liftₐ I ψP hψP
  have hψA : ∀ p : P, ψA (Ideal.Quotient.mk I p) = ψP p := fun p => rfl
  have hunit1 : ∀ yy : Submonoid.powers a, IsUnit (ψA yy) := by
    rintro ⟨_, n, rfl⟩
    show IsUnit (ψA (algebraMap O A ϖ ^ n))
    rw [map_pow, AlgHom.commutes]
    exact hϖ'.pow n
  let ψ : B →ₐ[O] C' := IsLocalization.liftAlgHom (M := Submonoid.powers a) (S := B) (f := ψA) hunit1
  have hψ : ∀ x : A, ψ (algebraMap A B x) = ψA x := fun x => by
    first
    | exact IsLocalization.lift_eq (M := Submonoid.powers a) (S := B) _ x
    | simp [ψ, IsLocalization.liftAlgHom]
  let xB : σ → B := fun i => algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i))
  have hxB : ∏ i ∈ T, xB i = algebraMap O B ϖ := by
    have e : (Ideal.Quotient.mk I (∏ i ∈ T, MvPolynomial.X i)) =
        Ideal.Quotient.mk I (MvPolynomial.C ϖ) :=
      Ideal.Quotient.eq.mpr (Ideal.subset_span rfl)
    simp only [xB]
    rw [← map_prod, ← map_prod, e, IsScalarTower.algebraMap_apply O A B]
    rfl
  have hϖB : IsUnit (algebraMap O B ϖ) := by
    rw [IsScalarTower.algebraMap_apply O A B]
    exact IsLocalization.Away.algebraMap_isUnit a
  have hxB' : xB i0 * ∏ i ∈ T.erase i0, xB i = algebraMap O B ϖ := by
    rw [Finset.mul_prod_erase T xB hi0, hxB]
  have hpB : IsUnit (∏ i ∈ T.erase i0, xB i) := by
    rw [← hxB'] at hϖB
    exact isUnit_of_mul_isUnit_right hϖB
  let χC : C →ₐ[O] B := MvPolynomial.aeval (fun j => xB j.1)
  have hχX : ∀ j : {j : σ // j ≠ i0}, χC (MvPolynomial.X j) = xB j.1 := fun j =>
    MvPolynomial.aeval_X (fun j : {j : σ // j ≠ i0} => xB j.1) j
  have hχy : ∀ i ∈ T.erase i0, χC (y i) = xB i := by
    intro i hi
    have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
    have hyi : y i = MvPolynomial.X ⟨i, hne⟩ := dif_neg hne
    rw [hyi, hχX ⟨i, hne⟩]
  have hχh : χC h = algebraMap O B ϖ * ∏ i ∈ T.erase i0, xB i := by
    show χC (MvPolynomial.C ϖ * ∏ i ∈ T.erase i0, y i) = _
    rw [map_mul, map_prod]
    have hC : χC (MvPolynomial.C ϖ) = algebraMap O B ϖ := MvPolynomial.aeval_C _ ϖ
    rw [hC, Finset.prod_congr rfl hχy]
  have hunit2 : ∀ yy : Submonoid.powers h, IsUnit (χC yy) := by
    rintro ⟨_, n, rfl⟩
    show IsUnit (χC (h ^ n))
    rw [map_pow, hχh]
    exact (hϖB.mul hpB).pow n
  let χ : C' →ₐ[O] B := IsLocalization.liftAlgHom (M := Submonoid.powers h) (S := C') (f := χC) hunit2
  have hχ : ∀ x : C, χ (algebraMap C C' x) = χC x := fun x => by
    first
    | exact IsLocalization.lift_eq (M := Submonoid.powers h) (S := C') _ x
    | simp [χ, IsLocalization.liftAlgHom]
  have hχu : χ (algebraMap C C' h) * χ u = 1 := by rw [← map_mul, hu, map_one]
  rw [hχ, hχh] at hχu
  have h1 : χ.comp ψ = AlgHom.id O B := by
    apply IsLocalization.algHom_ext (Submonoid.powers a)
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    show χ (ψ (algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i)))) =
      algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i))
    rw [hψ, hψA]
    have hXi : ψP (MvPolynomial.X i) = z i := MvPolynomial.aeval_X z i
    rw [hXi]
    show χ (z i) = xB i
    by_cases hi : i = i0
    · rw [hi]
      have hz0 : z i0 = algebraMap O C' ϖ ^ 2 * u := if_pos rfl
      rw [hz0, map_mul, map_pow, AlgHom.commutes]
      linear_combination (χ u * algebraMap O B ϖ) * hxB'.symm + xB i0 * hχu
    · have hzi : z i = algebraMap C C' (y i) := if_neg hi
      have hyi : y i = MvPolynomial.X ⟨i, hi⟩ := dif_neg hi
      rw [hzi, hχ, hyi, hχX ⟨i, hi⟩]
  have h2 : ψ.comp χ = AlgHom.id O C' := by
    apply IsLocalization.algHom_ext (Submonoid.powers h)
    apply MvPolynomial.algHom_ext
    intro j
    show ψ (χ (algebraMap C C' (MvPolynomial.X j))) = algebraMap C C' (MvPolynomial.X j)
    rw [hχ]
    rw [hχX j]
    show ψ (algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X j.1))) = _
    rw [hψ, hψA]
    have hXi : ψP (MvPolynomial.X j.1) = z j.1 := MvPolynomial.aeval_X z j.1
    have hzi : z j.1 = algebraMap C C' (y j.1) := if_neg j.2
    have hyi : y j.1 = MvPolynomial.X ⟨j.1, j.2⟩ := dif_neg j.2
    rw [hXi, hzi, hyi]
  let e : C' ≃ₐ[O] B := AlgEquiv.ofAlgHom χ ψ h1 h2
  haveI : Algebra.FormallySmooth C C' := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers h)
  haveI : Algebra.FormallySmooth O C' := Algebra.FormallySmooth.comp O C C'
  haveI : Algebra.FormallySmooth O B := Algebra.FormallySmooth.of_equiv e
  haveI : Algebra.FinitePresentation O A :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  haveI : Algebra.FinitePresentation A B := IsLocalization.Away.finitePresentation a
  haveI : Algebra.FinitePresentation O B := Algebra.FinitePresentation.trans O A B
  haveI : Algebra.FinitePresentation O F := IsLocalization.Away.finitePresentation ϖ
  let φ := IsLocalization.Away.map F B (algebraMap O A) ϖ
  letI : Algebra F B := φ.toAlgebra
  haveI : IsScalarTower O F B := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply O A B]
    exact (IsLocalization.map_eq _ _).symm)
  haveI : Algebra.FormallySmooth F B := Algebra.FormallySmooth.localization_base (Submonoid.powers ϖ)
  haveI : Algebra.FinitePresentation F B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation O F B
  have hs : Algebra.Smooth F B := ⟨inferInstance, inferInstance⟩
  exact hs

theorem smooth_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m → ∀ (F : Type) [Field F] [Algebra O F] [IsLocalization.Away ϖ F], (IsLocalization.Away.map F (Localization.Away (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ)) (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ})) ϖ).Smooth := by
  intro O _ _ _ ϖ _ m r hr1 hrm F _ _ _
  exact smooth_away_core O ϖ (Fin m) (Finset.univ.filter (fun i : Fin m => (i : ℕ) < r)) ⟨0, by omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, show (0 : ℕ) < r by omega⟩) F

end GlobalTheory.CompanionTheory.Semistable
end

section

namespace GlobalTheory.CompanionTheory.Summability

theorem summable_prod_pow_multiIndex : ∀ (r : ℕ) (x : Fin r → ℝ), (∀ i, 0 ≤ x i) → (∀ i, x i < 1) →
    Summable (fun j : Fin r → ℕ => ∏ i, x i ^ j i) := by
  intro r
  induction r with
  | zero =>
    intro x _ _
    exact (hasSum_fintype _).summable
  | succ r ih =>
    intro x h0 h1
    let e : ℕ × (Fin r → ℕ) ≃ (Fin (r + 1) → ℕ) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun j => (j 0, Fin.tail j)
        left_inv := fun p => by simp
        right_inv := fun j => by simp }
    rw [← e.summable_iff]
    have hA : Summable (fun n : ℕ => x 0 ^ n) := summable_geometric_of_lt_one (h0 0) (h1 0)
    have hB : Summable (fun j : Fin r → ℕ => ∏ i, x i.succ ^ j i) :=
      ih (fun i => x i.succ) (fun i => h0 _) (fun i => h1 _)
    have hM := hA.mul_of_nonneg hB (fun n => pow_nonneg (h0 0) n)
      (fun j => Finset.prod_nonneg (fun i _ => pow_nonneg (h0 _) _))
    refine hM.congr ?_
    rintro ⟨n, j⟩
    simp [e, Fin.prod_univ_succ]

end GlobalTheory.CompanionTheory.Summability
end
