module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

theorem weightSpace_tensor_ringHom_pos : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (χ : C →+* k), 0 < Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  intro k _ _ C _ _ _ χ
  let φ : k ⊗[ℤ] C →ₐ[k] k :=
    Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)
  have hφs : Function.Surjective φ := fun a => ⟨algebraMap k (k ⊗[ℤ] C) a, by rw [φ.commutes]; rfl⟩
  let m : Ideal (k ⊗[ℤ] C) := RingHom.ker φ
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφs
  haveI : IsArtinianRing (k ⊗[ℤ] C) := IsArtinianRing.of_finite k (k ⊗[ℤ] C)
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes
    (⟨fun j => OrderDual.toDual (m ^ j), fun a b h => Ideal.pow_le_pow_right h⟩ :
      ℕ →o (Ideal (k ⊗[ℤ] C))ᵒᵈ)
  have hst : ∀ j, N ≤ j → m ^ N = m ^ j := fun j hj => hN j hj
  have hJJ : IsIdempotentElem (m ^ (N + 1)) := by
    show m ^ (N + 1) * m ^ (N + 1) = m ^ (N + 1)
    rw [← pow_add, ← hst (N + 1 + (N + 1)) (by omega), hst (N + 1) (by omega)]
  obtain ⟨e, he, hJe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian (m ^ (N + 1)))).mp hJJ
  have hJe' : m ^ (N + 1) = Ideal.span {e} := hJe
  have hv : (1 - e : k ⊗[ℤ] C) ≠ 0 := by
    intro h
    have h1 : e = 1 := (sub_eq_zero.mp h).symm
    have : m ^ (N + 1) = ⊤ := by rw [hJe', h1, Ideal.span_singleton_one]
    exact hm.ne_top (top_le_iff.mp (this ▸ Ideal.pow_le_self (by omega)))
  have key : ∀ x ∈ m, x ^ (N + 1) * (1 - e) = 0 := by
    intro x hx
    have hx' : x ^ (N + 1) ∈ Ideal.span {e} := hJe' ▸ Ideal.pow_mem_pow hx (N + 1)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx'
    rw [← ha, mul_assoc, mul_sub, mul_one, he.eq, sub_self, mul_zero]
  refine lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 ?_)
  rw [Submodule.ne_bot_iff]
  refine ⟨1 - e, ?_, hv⟩
  rw [Submodule.mem_iInf]
  intro c
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨N + 1, ?_⟩
  let x : k ⊗[ℤ] C := (1 : k) ⊗ₜ c - algebraMap k (k ⊗[ℤ] C) (χ c)
  have hxm : x ∈ m := by
    simp [m, x, φ, RingHom.mem_ker]
  have hf : (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c) - χ c • (1 : Module.End k (k ⊗[ℤ] C))
      = Algebra.lmul k (k ⊗[ℤ] C) x := by
    ext y
    simp [x, sub_mul, Algebra.smul_def]
  rw [hf, ← map_pow]
  simpa using key x hxm

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem reduced_fibres_almost_all_sep : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] (y : A), (Polynomial.aeval (R := k) y).Finite → Function.Injective (Polynomial.aeval (R := k) y) → Algebra.IsSeparable (IntermediateField.adjoin k {algebraMap A (FractionRing A) y}) (FractionRing A) → ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → y - algebraMap k A α ∉ Q ^ 2 := by
  intro k A _ _ _ _ _ y hfin hinj hsep
  letI : Algebra k[X] A := (Polynomial.aeval (R := k) y).toRingHom.toAlgebra
  have hmap : ∀ p : k[X], algebraMap k[X] A p = Polynomial.aeval y p := fun p => rfl
  haveI : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [hmap, Polynomial.algebraMap_apply, Polynomial.aeval_C]; rfl)
  haveI : Module.Finite k[X] A := hfin
  haveI : FaithfulSMul k[X] A := (faithfulSMul_iff_algebraMap_injective k[X] A).mpr hinj
  letI : Algebra (FractionRing k[X]) (FractionRing A) := FractionRing.liftAlgebra k[X] (FractionRing A)
  haveI : IsScalarTower k[X] (FractionRing k[X]) (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra k[X] (FractionRing A)
  set L := FractionRing A
  set K := FractionRing k[X]
  set ybar : L := algebraMap A L y
  set E := IntermediateField.adjoin k {ybar}
  have hpoly : ∀ p : k[X], algebraMap K L (algebraMap k[X] K p) = algebraMap A L (Polynomial.aeval y p) := by
    intro p
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k[X] A L]; rfl
  have hpolyE : ∀ p : k[X], algebraMap A L (Polynomial.aeval y p) ∈ E := by
    intro p
    have : algebraMap A L (Polynomial.aeval y p) = Polynomial.aeval ybar p := by
      rw [Polynomial.aeval_algebraMap_apply]
    rw [this]
    have hy : ybar ∈ E := IntermediateField.mem_adjoin_simple_self k ybar
    have := Polynomial.aeval_algHom_apply E.val (⟨ybar, hy⟩ : E) p
    simp only [IntermediateField.coe_val] at this
    rw [show ybar = ((⟨ybar, hy⟩ : E) : L) from rfl, this]
    exact (Polynomial.aeval (⟨ybar, hy⟩ : E) p).2
  have hrange : ∀ z : K, algebraMap K L z ∈ E := by
    intro z
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := k[X]) z
    rw [map_div₀, hpoly, hpoly]
    exact div_mem (hpolyE a) (hpolyE b)
  let f : K →+* E := (algebraMap K L).codRestrict E hrange
  have hf : ∀ z : K, (f z : L) = algebraMap K L z := fun z => rfl
  let S : IntermediateField k L := (algebraMap K L).fieldRange.toIntermediateField (fun c =>
    ⟨algebraMap k[X] K (Polynomial.C c), by
      rw [hpoly, Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply]⟩)
  have hES : E ≤ S := IntermediateField.adjoin_simple_le_iff.2
    ⟨algebraMap k[X] K Polynomial.X, by rw [hpoly, Polynomial.aeval_X]⟩
  have hsurj : Function.Surjective f := by
    intro e
    obtain ⟨z, hz⟩ := hES e.2
    exact ⟨z, Subtype.ext (by rw [hf]; exact hz)⟩
  let e₁ : E ≃+* K := (RingEquiv.ofBijective f ⟨f.injective, hsurj⟩).symm
  have he : (algebraMap K L).comp (e₁ : E →+* K) = (RingEquiv.refl L : L →+* L).comp (algebraMap E L) := by
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, RingEquiv.refl_apply]
    rw [← hf]
    change ((RingEquiv.ofBijective f ⟨f.injective, hsurj⟩) ((RingEquiv.ofBijective f ⟨f.injective, hsurj⟩).symm x) : L) = _
    rw [RingEquiv.apply_symm_apply]; rfl
  haveI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_equiv_equiv e₁ (RingEquiv.refl L) he
  have hD := differentIdeal_ne_bot (A := k[X]) (B := A)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  have hc := Ideal.comap_ne_bot_of_integral_mem hd0 hd (Algebra.IsIntegral.isIntegral (R := k[X]) d)
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨δ, hδ0, fun α hα Q hQ hmem' => hα ?_⟩
  have hmem : algebraMap k[X] A (X - C α) ∈ Q ^ 2 := by
    rw [hmap, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]; exact hmem'
  set p : Ideal k[X] := Ideal.span {X - C α} with hpdef
  haveI hpmax : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C α)
  have hp0 : p ≠ ⊥ := by
    rw [hpdef, Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero α
  have hP : Q ^ 2 ∣ p.map (algebraMap k[X] A) := by
    rw [Ideal.dvd_iff_le, hpdef, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy; exact hmem
  have hdiv := pow_sub_one_dvd_differentIdeal (A := k[X]) (B := A) Q 2 hp0 hP
  rw [show 2 - 1 = 1 from rfl, pow_one, Ideal.dvd_iff_le] at hdiv
  have hδQ : δ ∈ Q.comap (algebraMap k[X] A) := hdiv hδ
  have hXQ : X - C α ∈ Q.comap (algebraMap k[X] A) :=
    Ideal.mem_comap.mpr (Ideal.pow_le_self two_ne_zero hmem)
  have hle : p ≤ Q.comap (algebraMap k[X] A) := by
    rw [hpdef, Ideal.span_le, Set.singleton_subset_iff]; exact hXQ
  have heq : p = Q.comap (algebraMap k[X] A) :=
    hpmax.eq_of_le (hQ.isPrime.comap _).ne_top hle
  rw [← heq, hpdef, Ideal.mem_span_singleton, dvd_iff_isRoot] at hδQ
  exact hδQ

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory
namespace DedekindCodimG

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

end DedekindCodimG
end GlobalTheory

namespace GlobalTheory
namespace DedekindCodimG

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

private theorem isArtinianRing_quotient_of_ne_bot_of_isDedekindDomain (A : Type) [CommRing A] [IsDedekindDomain A]
    (I : Ideal A) (hI : I ≠ ⊥) : IsArtinianRing (A ⧸ I) := by
  have : Ring.KrullDimLE 0 (A ⧸ I) := by
    refine Ring.KrullDimLE.mk₀ fun Q hQ => ?_
    have hle : I ≤ Q.comap (Ideal.Quotient.mk I) := fun a ha => by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha, Q.zero_mem]
    have hne : Q.comap (Ideal.Quotient.mk I) ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hle))
    have hmax := (Ideal.IsPrime.comap (Ideal.Quotient.mk I) (hK := hQ)).isMaximal hne
    have := hmax.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hle)
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

private theorem module_finite_quotient_of_ne_bot_of_isDedekindDomain (k A : Type) [Field k] [CommRing A] [IsDedekindDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (I : Ideal A) (hI : I ≠ ⊥) :
    Module.Finite k (A ⧸ I) := by
  haveI := isArtinianRing_quotient_of_ne_bot_of_isDedekindDomain A I hI
  exact Module.finite_of_isArtinianRing k (A ⧸ I)

private theorem algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsMaximal] :
    Function.Bijective (algebraMap k (A ⧸ P)) := by
  letI := Ideal.Quotient.field P
  haveI : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  exact ⟨(algebraMap k (A ⧸ P)).injective, IsSepClosed.algebraMap_surjective k (A ⧸ P)⟩

private theorem mul_sup_span_singleton_eq_of_mem_of_not_mem_mul (A : Type) [CommRing A] [IsDedekindDomain A]
    (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) (hP0 : P ≠ ⊥) {x : A} (hxI : x ∈ I)
    (hxIP : x ∉ I * P) : I * P ⊔ Ideal.span {x} = I := by
  have hle : I * P ⊔ Ideal.span {x} ≤ I :=
    sup_le (Ideal.mul_le_inf.trans inf_le_left) ((Ideal.span_singleton_le_iff_mem I).mpr hxI)
  obtain ⟨M, hM⟩ := Ideal.dvd_iff_le.mpr hle
  have hMP : M ∣ P := by
    have : I * M ∣ I * P := Ideal.dvd_iff_le.mpr (hM ▸ le_sup_left)
    exact (mul_dvd_mul_iff_left hI).mp this
  obtain ⟨N, hN⟩ := hMP
  rcases (Ideal.prime_of_isPrime hP0 hP.isPrime).irreducible.isUnit_or_isUnit hN with hu | hu
  · rw [hM, Ideal.isUnit_iff.mp hu, Ideal.mul_top]
  · rw [Ideal.isUnit_iff.mp hu, Ideal.mul_top] at hN
    subst hN
    refine absurd ?_ hxIP
    rw [← hM]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)

private theorem exists_sub_algebraMap_mem_of_isMaximal_of_isAlgClosed (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsMaximal] (r : A) :
    ∃ c : k, r - algebraMap k A c ∈ P := by
  obtain ⟨c, hc⟩ := (algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed k A P).2 (Ideal.Quotient.mk P r)
  refine ⟨c, Ideal.Quotient.eq.mp ?_⟩
  rw [Ideal.Quotient.mk_algebraMap, hc]

private theorem finrank_quotient_mul_maximal_eq_finrank_add_one (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (I P : Ideal A)
    (hI : I ≠ ⊥) (hP : P.IsMaximal) (hP0 : P ≠ ⊥) :
    Module.finrank k (A ⧸ I * P) = Module.finrank k (A ⧸ I) + 1 := by
  haveI := hP
  haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A (I * P) (mul_ne_zero hI hP0)
  haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI
  obtain ⟨x, hxI, hxIP⟩ : ∃ x ∈ I, x ∉ I * P := by
    by_contra! h
    have hIP : I * P = I * ⊤ := by
      rw [Ideal.mul_top]
      exact le_antisymm (Ideal.mul_le_inf.trans inf_le_left) fun y hy => h y hy
    exact hP.ne_top (mul_left_cancel₀ hI hIP)
  let f : (A ⧸ I * P) →ₗ[k] (A ⧸ I) :=
    (Ideal.Quotient.factorₐ k (Ideal.mul_le_inf.trans inf_le_left : I * P ≤ I)).toLinearMap
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hker : LinearMap.ker f = k ∙ Ideal.Quotient.mk (I * P) x := by
    apply le_antisymm
    · intro z hz
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      have haI : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hz)
      rw [← mul_sup_span_singleton_eq_of_mem_of_not_mem_mul A I P hI hP hP0 hxI hxIP] at haI
      obtain ⟨b, hb, y, hy, rfl⟩ := Submodule.mem_sup.mp haI
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_of_isMaximal_of_isAlgClosed k A P r
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      rw [← Ideal.Quotient.mkₐ_eq_mk k, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq,
        Algebra.smul_def]
      have h1 : x * (r - algebraMap k A c) ∈ I * P := Ideal.mul_mem_mul hxI hc
      have h2 : algebraMap k A c * x - (b + r * x) = -(b + x * (r - algebraMap k A c)) := by ring
      rw [h2]
      exact (I * P).neg_mem ((I * P).add_mem hb h1)
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hxI
  have hx0 : Ideal.Quotient.mk (I * P) x ≠ 0 := fun h => hxIP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, finrank_span_singleton hx0] at h
  exact h.symm

theorem _root_.GlobalTheory.DedekindCodimG.dedekind_finiteType_codim (k A : Type) [Field k]
    [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    (∀ (I : Ideal A), I ≠ ⊥ → Module.Finite k (A ⧸ I)) ∧
    (∀ (P : Ideal A), P.IsMaximal →
      Module.finrank k (A ⧸ P) = (1 : ℕ) ∧ ∃ (φ : A →ₐ[k] k), ∀ (u : A), u ∈ P ↔ (φ : A → k) u = (0 : k)) ∧
    (∀ (I J : Ideal A), I ≠ ⊥ → J ≠ ⊥ →
      Module.finrank k (A ⧸ I * J) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J)) ∧
    ∀ (I J : Ideal A), I ≠ ⊥ → I ≤ J → Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J) →
      I = J := by
  refine ⟨fun I hI => module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI, ?_, ?_, ?_⟩
  · intro P hP
    haveI := hP
    let e : k ≃ₐ[k] A ⧸ P :=
      AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) (algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed k A P)
    refine ⟨by rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self],
      e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k P), fun u => ?_⟩
    change u ∈ P ↔ e.symm (Ideal.Quotient.mk P u) = 0
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  · intro I J hI hJ
    induction J using UniqueFactorizationMonoid.induction_on_prime generalizing I with
    | h₁ => exact absurd rfl hJ
    | h₂ u hu =>
      rw [Ideal.isUnit_iff.mp hu, Ideal.mul_top]
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [Module.finrank_zero_of_subsingleton (M := A ⧸ (⊤ : Ideal A)), add_zero]
    | h₃ a p ha hp ih =>
      have hp0 : p ≠ ⊥ := hp.ne_zero
      have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp0
      have ha' : a ≠ ⊥ := ha
      rw [show I * (p * a) = I * a * p by ring, mul_comm p a,
        finrank_quotient_mul_maximal_eq_finrank_add_one k A (I * a) p (mul_ne_zero hI ha') hpmax hp0,
        finrank_quotient_mul_maximal_eq_finrank_add_one k A a p ha' hpmax hp0, ih I hI ha']
      ring
  · intro I J hI hIJ hle
    have hJ : J ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hIJ))
    haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI
    haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A J hJ
    let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
    have hker : LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    refine le_antisymm hIJ fun a ha => ?_
    have hmem : Ideal.Quotient.mk I a ∈ LinearMap.ker f :=
      LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
    rw [hker, Submodule.mem_bot] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

end DedekindCodimG
end GlobalTheory
end

section

open IsLocalRing

open scoped TensorProduct

namespace GlobalTheory

theorem etale_hom_to_field_lands_in_algClosed_subfield
    (A B K L : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] [Field K] [IsAlgClosed K] [Field L]
    (α : A →+* K) (ι : K →+* L) (β : B →+* L) :
    (∀ a ∈ maximalIdeal A, α a = 0) → β.comp (algebraMap A B) = ι.comp α →
      ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = α ∧ ι.comp ψ = β := by
  intro _ hβ
  letI : Algebra A K := α.toAlgebra
  letI : Algebra K L := ι.toAlgebra
  letI : Algebra A L := (ι.comp α).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : B →ₐ[A] L :=
    { β with
      commutes' := fun a => congrArg (fun f : A →+* L => f a) hβ }
  let f : K ⊗[A] B →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) g (fun _ _ => Commute.all _ _)
  haveI : Module.Finite K (K ⊗[A] B) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[A] B)
  haveI : Algebra.IsIntegral K (K ⊗[A] B) := Algebra.IsIntegral.of_finite K _
  haveI : Algebra.IsIntegral K f.range :=
    Algebra.IsIntegral.of_surjective f.rangeRestrict (AlgHom.rangeRestrict_surjective f)
  have hsurj : Function.Surjective (algebraMap K f.range) := by
    intro y
    have hy : IsIntegral K (y : L) := (Algebra.IsIntegral.isIntegral y).map f.range.val
    obtain ⟨k, hk⟩ := minpoly.mem_range_of_degree_eq_one K (y : L)
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hy))
    exact ⟨k, Subtype.ext hk⟩
  let e : K ≃+* f.range :=
    RingEquiv.ofBijective (algebraMap K f.range) ⟨(algebraMap K f.range).injective, hsurj⟩
  let ψ : B →+* K :=
    e.symm.toRingHom.comp (f.rangeRestrict.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B).toRingHom)
  have hι : ∀ x, ι (ψ x) = β x := by
    intro x
    have h1 : (algebraMap K f.range (ψ x) : L) = ι (ψ x) := rfl
    have h2 : algebraMap K f.range (ψ x) = f.rangeRestrict (1 ⊗ₜ x) := by
      simp only [ψ, e, RingHom.comp_apply]
      exact (RingEquiv.ofBijective (algebraMap K f.range) _).apply_symm_apply _
    rw [← h1, h2]
    simp [f, g]
  refine ⟨ψ, ?_, ?_⟩
  · ext a
    apply ι.injective
    rw [RingHom.comp_apply, hι]
    exact congrArg (fun f : A →+* L => f a) hβ
  · ext x
    exact hι x

end GlobalTheory
end

section

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.GeomPointLift

theorem nonempty_algHom_of_isAlgClosed (K C : Type) [Field K] [IsAlgClosed K] [CommRing C] [Nontrivial C]
    [Algebra K C] [Algebra.FiniteType K C] : Nonempty (C →ₐ[K] K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal C
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (C ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (C ⧸ M)
  exact ⟨(IsAlgClosed.lift : (C ⧸ M) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K M)⟩

theorem exists_lift (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (hff : Module.FaithfullyFlat A B)
    (hft : Algebra.FiniteType A B) (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k) :
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := by
  letI : Algebra A k := φ.toAlgebra
  haveI : Nontrivial (k ⊗[A] B) := Module.FaithfullyFlat.rTensor_nontrivial A B k
  haveI : Algebra.FiniteType k (k ⊗[A] B) := inferInstance
  obtain ⟨f⟩ := nonempty_algHom_of_isAlgClosed k (k ⊗[A] B)
  refine ⟨f.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply A k (k ⊗[A] B), AlgHom.commutes]
  rfl

end GlobalTheory.GeomPointLift
end
end
