module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem matrixGaussSum_mul_unit (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type)
    [CommRing R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ) (a : Matrix (Fin r) (Fin r) k)
    (g : GL (Fin r) k) :
    (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
      ψ (Matrix.trace ((a * (g : Matrix (Fin r) (Fin r) k)) * (x : Matrix (Fin r) (Fin r) k)))) =
    ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) *
      (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
        ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))) := by
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft g)
    (fun x : GL (Fin r) k => ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) *
      ((((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
        ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h2 : ξ (Matrix.GeneralLinearGroup.det (g * x)) =
      ξ (Matrix.GeneralLinearGroup.det g) * ξ (Matrix.GeneralLinearGroup.det x) := by
    rw [map_mul, map_mul]
  have h3 : ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) *
      (((ξ (Matrix.GeneralLinearGroup.det (g * x)))⁻¹ : Rˣ) : R) =
      (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) := by
    rw [h2, ← Units.val_mul, mul_inv, mul_inv_cancel_left]
  have h4 : ((g * x : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) =
      (g : Matrix (Fin r) (Fin r) k) * (x : Matrix (Fin r) (Fin r) k) := rfl
  rw [Equiv.coe_mulLeft, ← mul_assoc, h3, h4, Matrix.mul_assoc]

theorem exists_gl_det_eq_mul_eq_of_det_eq_zero (k : Type) [Field k] (r : ℕ)
    (a : Matrix (Fin r) (Fin r) k) (ha : a.det = 0) (t : kˣ) :
    ∃ g : GL (Fin r) k, Matrix.GeneralLinearGroup.det g = t ∧
      a * (g : Matrix (Fin r) (Fin r) k) = a := by
  obtain ⟨v, hv, hav⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ha
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := hi
  let w : Fin r → k := Pi.single i (((t : k) - 1) / v i)
  have hdet : (1 + Matrix.vecMulVec v w).det = (t : k) := by
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [w, single_dotProduct]
    field_simp
    ring
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + Matrix.vecMulVec v w)
    (by rw [hdet]; exact t.ne_zero), ?_, ?_⟩
  · ext
    exact hdet
  · change a * (1 + Matrix.vecMulVec v w) = a
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, hav]
    simp

theorem matrixGaussSum_singular_and_invertible :
    ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∀ a : Matrix (Fin r) (Fin r) k, a.det = 0 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))) = 0) ∧ ∀ a : GL (Fin r) k, (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace ((a : Matrix (Fin r) (Fin r) k) * (x : Matrix (Fin r) (Fin r) k)))) = ((ξ (Matrix.GeneralLinearGroup.det a) : Rˣ) : R) * (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) := by
  intro k _ _ _ R _ _ ψ ξ r _ hξ
  refine ⟨fun a ha => ?_, fun a => ?_⟩
  · obtain ⟨t, ht⟩ : ∃ t, ξ t ≠ 1 := by
      by_contra h
      push_neg at h
      exact hξ (MonoidHom.ext h)
    obtain ⟨g, hg, hag⟩ := exists_gl_det_eq_mul_eq_of_det_eq_zero k r a ha t
    have h := matrixGaussSum_mul_unit k R ψ ξ r a g
    rw [hag, hg] at h
    have h1 : ((ξ t : Rˣ) : R) ≠ 1 := fun h' => ht (Units.ext h')
    by_contra hS
    exact h1 (mul_right_cancel₀ hS (h.symm.trans (one_mul _).symm))
  · have h := matrixGaussSum_mul_unit k R ψ ξ r 1 a
    rwa [Matrix.one_mul] at h

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem quotSpanNat_mk_eq_sum {S : Type} [CommRing S] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ S)
    (n : ℕ) [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] (s : S) :
    Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) s =
      ∑ i, ((b.repr s i : ℤ) : ZMod n) • Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (b i) := by
  conv_lhs => rw [← b.sum_repr s]

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul, map_zsmul]

theorem quotSpanNat_linearIndependent {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] :
    LinearIndependent (ZMod n) (fun i => Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (b i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set c : ι → ℤ := fun i => ((g i).val : ℤ) with hc
  have hcg : ∀ i, ((c i : ℤ) : ZMod n) = g i := fun i => by simp [c]
  have h0 : Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (∑ i, c i • b i) = 0 := by
    rw [quotSpanNat_mk_eq_sum b n, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [b.repr_sum_self c, hcg]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
  obtain ⟨a, ha⟩ := h0
  have hrep := congrArg (fun y => b.repr y i) ha
  simp only [b.repr_sum_self c] at hrep
  have : a * ((n : ℕ) : S) = ((n : ℤ)) • a := by
    rw [zsmul_eq_mul, mul_comm]; simp
  rw [this, map_zsmul] at hrep
  rw [← hcg i, ← hrep]
  simp

noncomputable def zmodRingHomOfCastEqZero {R : Type} [CommRing R] (n : ℕ) (h : (n : R) = 0) :
    ZMod n →+* R :=
  (Ideal.Quotient.lift (Ideal.span {(n : ℤ)}) (Int.castRingHom R) (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      simp [h])).comp (Int.quotientSpanNatEquivZMod n).symm.toRingHom

noncomputable def quotSpanNatBasis {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] :
    Module.Basis ι (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)}) :=
  Module.Basis.mk (quotSpanNat_linearIndependent b n) (by
    rintro y -
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [quotSpanNat_mk_eq_sum b n s]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem quotSpanNatBasis_apply {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})]
    (i : ι) : quotSpanNatBasis b n i = Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (b i) :=
  Module.Basis.mk_apply _ _ _

theorem quotSpanNatBasis_repr {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})]
    (s : S) (i : ι) : (quotSpanNatBasis b n).repr (Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) s) i =
      ((b.repr s i : ℤ) : ZMod n) := by
  have h := quotSpanNat_mk_eq_sum b n s
  simp_rw [← quotSpanNatBasis_apply b n] at h
  rw [h, (quotSpanNatBasis b n).repr_sum_self]

theorem intCast_trace_eq_trace_quotSpanNat {S : Type} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] (x : S) :
    ((Algebra.trace ℤ S x : ℤ) : ZMod n) =
      Algebra.trace (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)}) (Ideal.Quotient.mk _ x) := by
  let b := Module.Free.chooseBasis ℤ S
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace (quotSpanNatBasis b n)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', Int.cast_sum, quotSpanNatBasis_apply, ← map_mul,
    quotSpanNatBasis_repr]

theorem isLocalRing_zmod_primePow (l b : ℕ) [Fact l.Prime] (hb : b ≠ 0) : IsLocalRing (ZMod (l ^ b)) := by
  have : Fact (1 < l ^ b) := ⟨Nat.one_lt_pow hb (Fact.out : l.Prime).one_lt⟩
  exact IsLocalRing.of_surjective' (PadicInt.toZModPow (p := l) b) (ZMod.ringHom_surjective _)

theorem free_finite_fst_of_prod (l b : ℕ) [Fact l.Prime] (M N : Type) [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod (l ^ b)) M] [Module (ZMod (l ^ b)) N] [Module.Free (ZMod (l ^ b)) (M × N)]
    [Module.Finite (ZMod (l ^ b)) (M × N)] :
    Module.Free (ZMod (l ^ b)) M ∧ Module.Finite (ZMod (l ^ b)) M := by
  rcases eq_or_ne b 0 with rfl | hb
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    haveI : Subsingleton M := by
      refine ⟨fun x y => ?_⟩
      rw [← one_smul (ZMod (l ^ 0)) x, ← one_smul (ZMod (l ^ 0)) y, Subsingleton.elim (1 : ZMod (l ^ 0)) 0,
        zero_smul, zero_smul]
    exact ⟨inferInstance, inferInstance⟩
  haveI := isLocalRing_zmod_primePow l b hb
  haveI : Module.Projective (ZMod (l ^ b)) M :=
    Module.Projective.of_split (LinearMap.inl _ M N) (LinearMap.fst _ M N) (by ext; simp)
  haveI : Module.Finite (ZMod (l ^ b)) M :=
    Module.Finite.of_surjective (LinearMap.fst _ M N) LinearMap.fst_surjective
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

theorem intCast_trace_eq_trace_quotient_of_mem (L : Type) [Field L] [NumberField L] (l b : ℕ) [Fact l.Prime]
    (I Q : Ideal (𝓞 L)) (hsup : I ⊔ Q = ⊤) (hmul : I * Q = Ideal.span {((l ^ b : ℕ) : 𝓞 L)})
    [Algebra (ZMod (l ^ b)) (𝓞 L ⧸ I)] (x : 𝓞 L) (hx : x ∈ Q) :
    ((Algebra.trace ℤ (𝓞 L) x : ℤ) : ZMod (l ^ b)) =
      Algebra.trace (ZMod (l ^ b)) (𝓞 L ⧸ I) (Ideal.Quotient.mk I x) := by
  haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hnIQ : ((l ^ b : ℕ) : 𝓞 L) ∈ I * Q := by rw [hmul]; exact Ideal.mem_span_singleton_self _
  have hnQ : ((l ^ b : ℕ) : 𝓞 L) ∈ Q := (Ideal.mul_le_inf.trans inf_le_right) hnIQ
  letI instJ : Algebra (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) :=
    (zmodRingHomOfCastEqZero (l ^ b) (by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l ^ b : ℕ) : 𝓞 L)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _)).toAlgebra
  letI instQ : Algebra (ZMod (l ^ b)) (𝓞 L ⧸ Q) :=
    (zmodRingHomOfCastEqZero (l ^ b) (by
      rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
      exact hnQ)).toAlgebra
  have hcop : IsCoprime I Q := Ideal.isCoprime_iff_sup_eq.mpr hsup
  let e : (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) ≃+* (𝓞 L ⧸ I) × (𝓞 L ⧸ Q) :=
    (Ideal.quotEquivOfEq hmul.symm).trans (Ideal.quotientMulEquivQuotientProd I Q hcop)
  have he : ∀ y : 𝓞 L, e (Ideal.Quotient.mk (Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) y) = (Ideal.Quotient.mk I y, Ideal.Quotient.mk Q y) := by
    intro y
    refine Prod.ext ?_ ?_ <;>
      simp [e, Ideal.quotientMulEquivQuotientProd_fst, Ideal.quotientMulEquivQuotientProd_snd,
        Ideal.Quotient.factor_mk]
  let eA : (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) ≃ₐ[ZMod (l ^ b)] (𝓞 L ⧸ I) × (𝓞 L ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := e) (fun r => congrArg (fun f => f r)
      (Subsingleton.elim ((e : (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) →+* _).comp (algebraMap (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)})))
        (algebraMap (ZMod (l ^ b)) ((𝓞 L ⧸ I) × (𝓞 L ⧸ Q)))))
  haveI hfreeJ : Module.Free (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) :=
    Module.Free.of_basis (quotSpanNatBasis (Module.Free.chooseBasis ℤ (𝓞 L)) (l ^ b))
  haveI hfinJ : Module.Finite (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) :=
    Module.Finite.of_basis (quotSpanNatBasis (Module.Free.chooseBasis ℤ (𝓞 L)) (l ^ b))
  haveI : Module.Free (ZMod (l ^ b)) ((𝓞 L ⧸ I) × (𝓞 L ⧸ Q)) := Module.Free.of_equiv eA.toLinearEquiv
  haveI : Module.Finite (ZMod (l ^ b)) ((𝓞 L ⧸ I) × (𝓞 L ⧸ Q)) := Module.Finite.equiv eA.toLinearEquiv
  obtain ⟨hfI, hfinI⟩ := free_finite_fst_of_prod l b (𝓞 L ⧸ I) (𝓞 L ⧸ Q)
  haveI : Module.Free (ZMod (l ^ b)) ((𝓞 L ⧸ Q) × (𝓞 L ⧸ I)) :=
    Module.Free.of_equiv (LinearEquiv.prodComm (ZMod (l ^ b)) (𝓞 L ⧸ I) (𝓞 L ⧸ Q))
  haveI : Module.Finite (ZMod (l ^ b)) ((𝓞 L ⧸ Q) × (𝓞 L ⧸ I)) :=
    Module.Finite.equiv (LinearEquiv.prodComm (ZMod (l ^ b)) (𝓞 L ⧸ I) (𝓞 L ⧸ Q))
  obtain ⟨hfQ, hfinQ⟩ := free_finite_fst_of_prod l b (𝓞 L ⧸ Q) (𝓞 L ⧸ I)
  rw [intCast_trace_eq_trace_quotSpanNat (l ^ b) x, ← Algebra.trace_eq_of_algEquiv eA]
  have : eA (Ideal.Quotient.mk (Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) x) = (Ideal.Quotient.mk I x, 0) := by
    show e _ = _
    rw [he, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  rw [this, Algebra.trace_prod_apply, map_zero, add_zero]

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

theorem fg_inf_sup_of_isCompl (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A : Submodule (𝓞 K) V) (U U' : Submodule K V) :
    A.FG → IsCompl U U' →
      (U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K))).FG := by
  intro hA h
  let p : V →ₗ[K] V := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U U' h
  let q : V →ₗ[𝓞 K] V := p.restrictScalars (𝓞 K)
  have hpU : ∀ x, p x ∈ U := fun x => (Submodule.linearProjOfIsCompl U U' h x).2
  have hpl : ∀ x ∈ U, p x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left h ⟨x, hx⟩)
  have hpr : ∀ x ∈ U', p x = 0 := fun x hx => by
    have := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff h).2 hx
    show ((Submodule.linearProjOfIsCompl U U' h x : U) : V) = 0
    exact congrArg Subtype.val this
  have hsub : ∀ x, x - p x ∈ U' := fun x => by
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff h]
    have h1 : p (x - p x) = 0 := by rw [map_sub, hpl _ (hpU x), sub_self]
    have h2 : ((Submodule.linearProjOfIsCompl U U' h (x - p x) : U) : V) = 0 := h1
    exact_mod_cast h2
  have heq : U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K)) = A.map q := by
    ext x
    constructor
    · rintro ⟨hxU, hx⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
      refine ⟨a, ha, ?_⟩
      change p a = a + u
      have e1 : p (a + u) = a + u := hpl _ hxU
      rw [map_add (f := _), hpr u hu, add_zero] at e1
      exact e1
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hpU a, ?_⟩
      refine Submodule.mem_sup.2 ⟨a, ha, p a - a, ?_, by abel⟩
      have := U'.neg_mem (hsub a)
      simpa using this
  rw [heq]
  exact hA.map q

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem maxIdeal_exact_pow_dvd_span_prime : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsMaximal], ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ∃ (e' : ℕ) (J : Ideal (𝓞 L)), 0 < e' ∧ e' ≤ e ∧ la ⊔ J = ⊤ ∧ Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e' * J := by
  intro L _ _ l e _ la hmax hin hout
  classical
  have hex : ∃ k, ((l : ℕ) : 𝓞 L) ∉ la ^ (k + 1) := ⟨e, hout⟩
  have hspec : ((l : ℕ) : 𝓞 L) ∉ la ^ (Nat.find hex + 1) := Nat.find_spec hex
  have hle : Nat.find hex ≤ e := Nat.find_min' hex hout
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso; rw [h, zero_add, pow_one] at hspec; exact hspec hin
    · exact h
  have hmem : ((l : ℕ) : 𝓞 L) ∈ la ^ Nat.find hex := by
    have h1 := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    rw [not_not] at h1
    have h4 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rwa [h4] at h1
  have hdvd : la ^ Nat.find hex ∣ Ideal.span {((l : ℕ) : 𝓞 L)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hmem
  obtain ⟨J, hJ⟩ := hdvd
  refine ⟨Nat.find hex, J, hpos, hle, ?_, hJ⟩
  by_contra hne
  have hJle : J ≤ la := by
    have h2 := hmax.eq_of_le hne le_sup_left
    calc J ≤ la ⊔ J := le_sup_right
      _ = la := h2.symm
  apply hspec
  have h3 : Ideal.span {((l : ℕ) : 𝓞 L)} ≤ la ^ (Nat.find hex + 1) := by
    rw [hJ, pow_succ]; exact Ideal.mul_mono_right hJle
  exact h3 (Ideal.subset_span (Set.mem_singleton _))

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem quot_pow_maximal_charP_local_card : ∀ (L : Type) [Field L] [NumberField L] (la J : Ideal (𝓞 L)) [la.IsMaximal] (l e b : ℕ), l.Prime → 0 < e → 0 < b → la ⊔ J = ⊤ → Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e * J → CharP (𝓞 L ⧸ la ^ (e * b)) (l ^ b) ∧ Finite (𝓞 L ⧸ la ^ (e * b)) ∧ ∃ π : 𝓞 L ⧸ la ^ (e * b), (∀ x : 𝓞 L ⧸ la ^ (e * b), ¬ IsUnit x ↔ π ∣ x) ∧ Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ (e * b))} = Ideal.span {π ^ e} ∧ Nat.card (𝓞 L ⧸ la ^ (e * b)) = Nat.card ((𝓞 L ⧸ la ^ (e * b)) ⧸ Ideal.span {π}) ^ (b * e) := by
  intro L _ _ la J hmax l e b hl he hb hJ hspan
  have hn0 : e * b ≠ 0 := Nat.mul_ne_zero he.ne' hb.ne'
  set n := e * b with hn
  set q := Ideal.Quotient.mk (la ^ n) with hq
  have hlla : ((l : ℕ) : 𝓞 L) ∈ la := by
    have : ((l:ℕ) : 𝓞 L) ∈ la ^ e * J := by rw [← hspan]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.pow_le_self he.ne' : la ^ e ≤ la) ((Ideal.mul_le_left : la ^ e * J ≤ la ^ e) this)
  have hl0 : ((l : ℕ) : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hla0 : la ≠ ⊥ := fun h => hl0 (by rw [h] at hlla; simpa using hlla)
  have hlatop : la ≠ ⊤ := hmax.ne_top
  have hpowle : ∀ i j : ℕ, la ^ i ≤ la ^ j ↔ j ≤ i := fun i j =>
    ⟨fun h => by
      by_contra hc
      rw [not_le] at hc
      exact absurd h (Ideal.pow_right_strictAnti la hla0 hlatop hc).not_ge,
     fun h => Ideal.pow_le_pow_right h⟩
  have hle : la ^ n ≤ la := Ideal.pow_le_self hn0
  have hnil : ∀ c ∈ la, IsNilpotent (q c) := fun c hc =>
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hc n⟩
  have hunit : ∀ a : 𝓞 L, IsUnit (q a) ↔ a ∉ la := by
    intro a
    constructor
    · intro hu ha
      obtain ⟨d, hd⟩ := hu.exists_right_inv
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective d
      have : a * c - 1 ∈ la ^ n := by
        rw [← Ideal.Quotient.eq]; simpa [hq] using hd
      have h1 : (1 : 𝓞 L) ∈ la := by
        have := la.sub_mem (la.mul_mem_right c ha) (hle this)
        simpa using this
      exact hlatop ((Ideal.eq_top_iff_one _).mpr h1)
    · intro ha
      obtain ⟨c, y, hy, hcy⟩ := hmax.exists_inv ha
      have h1 : q c * q a = 1 - q y := by
        rw [← map_mul, ← map_one q, ← map_sub, ← hcy]; simp
      have : IsUnit (q c * q a) := h1 ▸ (hnil y hy).isUnit_one_sub
      exact isUnit_of_mul_isUnit_right this
  have hmem : ∀ a : 𝓞 L, q a ∈ la.map q ↔ a ∈ la := fun a => Ideal.mem_quotient_iff_mem hle

  obtain ⟨π₀, hπla, hπ2⟩ := SetLike.exists_of_lt ((Ideal.pow_right_strictAnti la hla0 hlatop) (by norm_num : 1 < 2))
  replace hπla : π₀ ∈ la := by simpa using hπla
  change π₀ ∉ la ^ 2 at hπ2
  have hQ : Ideal.span {π₀} ⊔ la ^ 2 = la := by
    have := Ideal.eq_prime_pow_of_succ_lt_of_le (P := la) (I := Ideal.span {π₀} ⊔ la ^ 2) hla0 (i := 1)
      (lt_of_le_of_ne le_sup_right (fun h => hπ2 (h ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self π₀))))
      (by rw [pow_one]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hπla) (Ideal.pow_le_self two_ne_zero))
    simpa using this
  have hk : ∀ k, 1 ≤ k → la ≤ Ideal.span {π₀} ⊔ la ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [pow_one]; exact le_sup_right
    | succ k _ ih =>
      calc la = Ideal.span {π₀} ⊔ la ^ 2 := hQ.symm
        _ ≤ Ideal.span {π₀} ⊔ la * (Ideal.span {π₀} ⊔ la ^ k) :=
            sup_le_sup_left (by rw [pow_two]; exact Ideal.mul_mono_right ih) _
        _ = Ideal.span {π₀} ⊔ (la * Ideal.span {π₀} ⊔ la ^ (k + 1)) := by rw [Ideal.mul_sup, pow_succ']
        _ ≤ Ideal.span {π₀} ⊔ la ^ (k + 1) :=
            sup_le le_sup_left (sup_le (le_trans Ideal.mul_le_right le_sup_left) le_sup_right)
  have hm : Ideal.span {q π₀} = la.map q := by
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem]; exact (hmem π₀).mpr hπla
    · calc la.map q ≤ (Ideal.span {π₀} ⊔ la ^ n).map q := Ideal.map_mono (hk n (Nat.one_le_iff_ne_zero.mpr hn0))
        _ = Ideal.span {q π₀} := by
            rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hq, Ideal.map_quotient_self, sup_bot_eq]
  have hJtop : J.map q = ⊤ := by
    have : (1 : 𝓞 L) ∈ la ⊔ J := hJ ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp this
    have hz' : q z = 1 - q y := by rw [← map_one q, ← hyz, map_add (f := _)]; ring
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem q hz) (hz' ▸ (hnil y hy).isUnit_one_sub)
  have hlspan : Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ n)} = (la.map q) ^ e := by
    have : ((l : ℕ) : 𝓞 L ⧸ la ^ n) = q (l : 𝓞 L) := (map_natCast q l).symm
    rw [this, ← Set.image_singleton, ← Ideal.map_span, hspan, Ideal.map_mul, Ideal.map_pow, hJtop, Ideal.mul_top]
  refine ⟨⟨fun k => ?_⟩, ?_, q π₀, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    obtain ⟨v, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0.ne' l hl.ne_one
    have hcop : Nat.Coprime l m' := (Nat.Prime.coprime_iff_not_dvd hl).mpr hm'
    have hm'la : ((m' : ℕ) : 𝓞 L) ∉ la := by
      intro h
      obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hcop
      have h1 : ((u * l + w * m' : ℤ) : 𝓞 L) = 1 := by rw [huw]; simp
      push_cast at h1
      have : (1 : 𝓞 L) ∈ la := h1 ▸ la.add_mem (la.mul_mem_left _ hlla) (la.mul_mem_left _ h)
      exact hlatop ((Ideal.eq_top_iff_one _).mpr this)
    have hmu : IsUnit ((m' : ℕ) : 𝓞 L ⧸ la ^ n) := by
      rw [← map_natCast q]; exact (hunit _).mpr hm'la
    rw [Nat.cast_mul, Nat.cast_pow, hmu.mul_left_eq_zero, ← Ideal.span_singleton_eq_bot,
      ← Ideal.span_singleton_pow, hlspan, ← pow_mul, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, hq,
      Ideal.mk_ker, hpowle, (Nat.Coprime.pow_left b hcop).dvd_mul_right,
      Nat.pow_dvd_pow_iff_le_right hl.one_lt, hn]
    exact ⟨fun h => Nat.le_of_mul_le_mul_left h he, fun h => Nat.mul_le_mul_left e h⟩
  · exact Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero n hla0)
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← Ideal.mem_span_singleton, hm, hmem]
    exact (not_congr (hunit a)).trans not_not
  · rw [← Ideal.span_singleton_pow, hm, hlspan]
  · have hc1 : Nat.card ((𝓞 L ⧸ la ^ n) ⧸ la.map q) = Nat.card (𝓞 L ⧸ la) :=
      Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv
    have hc2 : ∀ I : Ideal (𝓞 L), Nat.card (𝓞 L ⧸ I) = Ideal.absNorm I := fun I => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hm, hc1, hc2, hc2, map_pow, hn, mul_comm e b]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem totallyComplex_of_root_quadratic_neg_disc :
    ∀ (K : Type) [Field K] [NumberField K] (x : K) (a b : ℤ), x ^ 2 + (a : K) * x + (b : K) = 0 →
    a ^ 2 < 4 * b → NumberField.IsTotallyComplex K := by
  intro K _ _ x a b hx hab
  refine ⟨fun v => ?_⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hv
  set φ : K →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal hv
  have h := congrArg φ hx
  simp only [map_add (f := _), map_mul, map_pow, map_intCast, map_zero] at h
  have hab' : ((a : ℝ)) ^ 2 < 4 * (b : ℝ) := by exact_mod_cast hab
  nlinarith [sq_nonneg (2 * φ x + (a : ℝ))]

end GlobalTheory
end
