module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle121
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle120
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle067
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle122
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103

@[expose] public section

section

noncomputable section

open Polynomial

namespace GlobalTheory.UnitLemma.PrincipalLat

theorem isIntegral_pi' {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

section General

variable {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing A] [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A]


variable (E) in
include E in
theorem exists_mul_isIntegral (y : A) : ∃ c : O, c ≠ 0 ∧ IsIntegral O (algebraMap O A c * y) := by
  have : Algebra.IsAlgebraic O A :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := E) (C := A)).mpr inferInstance
  obtain ⟨c, hc, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := O) y).exists_integral_multiple
  exact ⟨c, hc, by rwa [Algebra.smul_def] at h⟩

end General

section General2

variable {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing A] [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A]


variable (E) in
include E in
theorem exists_mul_le_integral (J : Submodule O A) (hJ : J.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ z ∈ J, IsIntegral O (algebraMap O A c * z) := by
  classical
  obtain ⟨s, rfl⟩ := hJ
  choose f hf0 hf using fun y : A => exists_mul_isIntegral (O := O) E y
  refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 fun y _ => hf0 y, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.mul_prod_erase s f hy, map_mul, mul_comm (algebraMap O A (f y)), mul_assoc]
    exact isIntegral_algebraMap.mul (hf y)
  | zero => rw [mul_zero]; exact isIntegral_zero
  | add x y _ _ hx hy => rw [mul_add]; exact hx.add hy
  | smul o x _ hx => rw [mul_smul_comm]; exact hx.smul o

theorem eq_mulLat_of_isPrincipalIdealRing [IsPrincipalIdealRing (integralClosure O A)]
    (J : Submodule O A) (hJ : IsLat O E J) (hst : ∀ a ∈ integralClosure O A, ∀ y ∈ J, a * y ∈ J) :
    ∃ a : Aˣ, J = mulLat O (a : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_mul_le_integral E J hJ.1
  set Λ := integralClosure O A

  have hcu : IsUnit (algebraMap O A c) := by
    rw [IsScalarTower.algebraMap_apply O E A]
    refine (IsUnit.mk0 _ ?_).map _
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc0))
  set C := algebraMap O A c
  let I : Ideal Λ :=
    { carrier := {l | ∃ z ∈ J, (l : A) = C * z}
      add_mem' := by
        rintro a b ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
        exact ⟨x + y, J.add_mem hx hy, by rw [Subalgebra.coe_add, hax, hby, mul_add]⟩
      zero_mem' := ⟨0, J.zero_mem, by simp⟩
      smul_mem' := by
        rintro a b ⟨x, hx, hbx⟩
        refine ⟨(a : A) * x, hst _ a.2 _ hx, ?_⟩
        rw [smul_eq_mul, Subalgebra.coe_mul, hbx]; ring }
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmemI : ∀ l : Λ, l ∈ I ↔ ∃ m : Λ, m * b = l := by
    intro l; rw [hb]; exact Ideal.mem_span_singleton'
  have key : ∀ z, z ∈ J ↔ ∃ l ∈ Λ, C * z = b * l := by
    intro z; constructor
    · intro hz
      obtain ⟨m, hm⟩ := (hmemI ⟨C * z, hc z hz⟩).1 ⟨z, hz, rfl⟩
      have h2 := congrArg Subtype.val hm
      simp only [Subalgebra.coe_mul] at h2
      exact ⟨m, m.2, by rw [← h2, mul_comm]⟩
    · rintro ⟨l, hl, hzl⟩
      obtain ⟨z0, hz0, hbz0⟩ : b ∈ I := by rw [hb]; exact Ideal.mem_span_singleton_self b
      have : C * z = C * (l * z0) := by rw [hzl, hbz0]; ring
      rw [hcu.mul_left_cancel this]
      exact hst l hl z0 hz0

  have hbu : IsUnit (b : A) := by
    have hle : (J : Set A) ⊆ LinearMap.range (LinearMap.mulLeft E (b : A)) := by
      intro z hz
      obtain ⟨l, _, hzl⟩ := (key z).1 hz
      refine ⟨hcu.unit⁻¹ * l, ?_⟩
      simp only [LinearMap.mulLeft_apply]
      calc (b : A) * (↑hcu.unit⁻¹ * l) = ↑hcu.unit⁻¹ * (b * l) := by ring
        _ = z := by rw [← hzl, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    have h1 : (1 : A) ∈ LinearMap.range (LinearMap.mulLeft E (b : A)) := by
      have := Submodule.span_le.2 hle
      rw [hJ.2] at this
      exact this Submodule.mem_top
    obtain ⟨w, hw⟩ := h1
    exact isUnit_iff_exists_inv.2 ⟨w, by simpa using hw⟩
  refine ⟨hcu.unit⁻¹ * hbu.unit, ?_⟩
  ext z
  rw [key z]
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule,
    Units.val_mul, IsUnit.unit_spec]
  constructor
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l, hl, ?_⟩
    rw [mul_assoc, ← hzl, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l, hl, ?_⟩
    rw [← hzl, ← mul_assoc, ← mul_assoc, IsUnit.mul_val_inv, one_mul]

end General2

theorem isPrincipalIdealRing_integralClosure {O E A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra E A] [Algebra O A]
    [IsScalarTower O E A] [Module.Finite E A] [IsReduced A] :
    IsPrincipalIdealRing (integralClosure O A) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite E A
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  haveI hpir : ∀ I : MaximalSpectrum A, IsPrincipalIdealRing (integralClosure O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure O E (A ⧸ I.asIdeal)
    infer_instance
  haveI : Finite (MaximalSpectrum A) := inferInstance
  let G : (∀ I : MaximalSpectrum A, integralClosure O (A ⧸ I.asIdeal)) →ₐ[O]
      (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    Pi.algHom O _ fun I => (integralClosure O (A ⧸ I.asIdeal)).val.comp (Pi.evalAlgHom O _ I)
  let F := (ψ.symm.toAlgHom.comp G).codRestrict (integralClosure O A) fun l =>
    (isIntegral_pi' (G l) fun I => (l I).2).map ψ.symm
  refine IsPrincipalIdealRing.of_surjective F ?_
  intro x
  refine ⟨fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩, ?_⟩
  apply Subtype.ext
  change ψ.symm (G _) = (x : A)
  have : G (fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩) = ψ x := rfl
  rw [this, AlgEquiv.symm_apply_apply]

theorem eq_mulLat_integralClosure : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
    ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)) := by
  intro K B hsep J hJ hst
  haveI : IsReduced B.A := ⟨fun a ha => Centraliser.eq_zero_of_isNilpotent B hsep a ha⟩
  haveI := isPrincipalIdealRing_integralClosure (O := K.O) (E := K.E) (A := B.A)
  exact eq_mulLat_of_isPrincipalIdealRing J hJ hst

end GlobalTheory.UnitLemma.PrincipalLat
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

theorem exists_conductor_mul_mem_adjoin : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsIntegral K.O B.g →
    ∃ c : K.O, c ≠ 0 ∧ ∀ u : B.A, IsIntegral K.O u →
      algebraMap K.O B.A c * u ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
  intro K B hP hg
  classical
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hP
  have hint : ∀ x : B.A, IsIntegral K.O x →
      ∃ t : K.O, algebraMap K.O K.E t = Algebra.trace K.E B.A x := fun x hx =>
    IsIntegrallyClosed.isIntegral_iff.1
      (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral K.O K.E B.A x hx)
  have he_int : ∀ i, IsIntegral K.O (e i) := fun i => by rw [he]; exact hg.pow _
  have hG : ∀ i j, ∃ t : K.O, algebraMap K.O K.E t = Algebra.trace K.E B.A (e i * e j) :=
    fun i j => hint _ ((he_int i).mul (he_int j))
  choose t ht using hG
  let c : K.O := (Matrix.of t).det
  have hc : algebraMap K.O K.E c = (Algebra.traceMatrix K.E e).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [ht, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have hgen : ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f := by
    intro a
    refine ⟨∑ i : Fin (Module.finrank K.E B.A), monomial (i : ℕ) (e.repr a i), ?_⟩
    calc a = ∑ i, e.repr a i • e i := (e.sum_repr a).symm
      _ = _ := by simp [map_sum, aeval_monomial, he, Algebra.smul_def]
  have hdet : (Algebra.traceMatrix K.E e).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have hwv : e.equivFun (∑ j, v j • e j) = v := by
      rw [← e.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    have hti : ∀ i, Algebra.trace K.E B.A ((∑ j, v j • e j) * e i) = 0 := by
      intro i
      have := congrFun (Algebra.traceMatrix_of_basis_mulVec e (∑ j, v j • e j)) i
      rw [hwv, hv] at this
      exact this.symm
    have hw := GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP hgen
      (∑ j, v j • e j) (fun y => by

        rw [← e.sum_repr y, Finset.mul_sum, map_sum]
        simp [mul_smul_comm, hti])
    exact funext (Fintype.linearIndependent_iff.1 e.linearIndependent v hw)
  refine ⟨c, fun h0 => hdet (by rw [← hc, h0, map_zero]), fun u hu => ?_⟩
  obtain ⟨w, hw⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum K.O K.E B.A _ e u
    (fun i j => ⟨_, ht i j⟩) (fun i => hint _ (hu.mul (he_int i)))
  have h1 : algebraMap K.O B.A c * u = ∑ j, w j • B.g ^ (j : ℕ) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, ← Algebra.smul_def, hc, hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [algebraMap_smul, he]
  rw [h1]
  exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _) _

end GlobalTheory.UnitLemma
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.IntegralFinite

open Matrix

theorem isIntegral_matrix_trace {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) : IsIntegral R M.trace := by
  first
  | exact @_root_.GlobalTheory.TargetStatementAlt.target
  | exact _root_.GlobalTheory.TargetStatementAlt.target
  | (apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementAlt.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementAlt.target ..)

variable {K : UQ} (B : InvAlg K)

theorem isIntegral_trace {x : B.A} (hx : IsIntegral K.O x) :
    IsIntegral K.O (Algebra.trace K.E B.A x) := by
  let bs := Module.finBasis K.E B.A
  rw [Algebra.trace_eq_matrix_trace bs]
  exact isIntegral_matrix_trace _ (hx.map ((Algebra.leftMulMatrix bs).restrictScalars K.O))

theorem trace_mem_range {x : B.A} (hx : IsIntegral K.O x) :
    ∃ c : K.O, algebraMap K.O K.E c = Algebra.trace K.E B.A x :=
  IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trace B hx)

theorem finite_integralClosure :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Module.Finite K.O (integralClosure K.O B.A) := by
  intro K B hsep
  classical
  let bs := Module.finBasis K.E B.A
  haveI : Algebra.IsAlgebraic K.O K.E := IsLocalization.isAlgebraic K.E (nonZeroDivisors K.O)
  haveI : Algebra.IsAlgebraic K.O B.A := Algebra.IsAlgebraic.trans K.O K.E B.A
  obtain ⟨y, hy, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples K.O (Finset.univ.image bs)
  have hy' : algebraMap K.O K.E y ≠ 0 := by
    intro h
    exact hy (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
  let b := bs.isUnitSMul (w := fun _ => algebraMap K.O K.E y) (fun _ => (Ne.isUnit hy'))
  have hbint : ∀ i, IsIntegral K.O (b i) := by
    intro i
    have h := hint (bs i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    simpa [b, Module.Basis.isUnitSMul_apply, algebraMap_smul] using h
  have hnd : (Algebra.traceForm K.E B.A).Nondegenerate := by
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact Centraliser.eq_zero_of_trace_mul B hsep a (fun z => by simpa [Algebra.traceForm_apply] using ha z)
    · exact Centraliser.eq_zero_of_trace_mul B hsep a
        (fun z => by simpa [Algebra.traceForm_apply, mul_comm] using ha z)
  let d := (Algebra.traceForm K.E B.A).dualBasis hnd b
  have hle : Subalgebra.toSubmodule (integralClosure K.O B.A) ≤ Submodule.span K.O (Set.range d) := by
    intro x hx
    have hx' : IsIntegral K.O x := hx
    rw [← d.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := trace_mem_range B (hx'.mul (hbint i))
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, ← hc, algebraMap_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)
  haveI : IsNoetherian K.O (Submodule.span K.O (Set.range d)) :=
    isNoetherian_span_of_finite K.O (Set.finite_range d)
  haveI : IsNoetherian K.O (Subalgebra.toSubmodule (integralClosure K.O B.A)) := isNoetherian_of_le hle
  exact Module.IsNoetherian.finite K.O (Subalgebra.toSubmodule (integralClosure K.O B.A))

end GlobalTheory.UnitLemma.IntegralFinite
end
end

section

open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma.TraceDet

theorem det_trace_pow_mul_ne_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ u : B.A, IsUnit u →
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ ((k : ℕ) + (l : ℕ)) * u)).det ≠ 0 := by
  intro K B hsep u hu hdet
  classical
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_power_basis_of_charpoly_separable K B hsep
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  set w : B.A := ∑ l, v l • e l with hw
  have hk : ∀ k, Algebra.trace K.E B.A ((w * u) * e k) = 0 := by
    intro k
    have := congrFun hv k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this

    rw [← this, hw, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul, he, he, pow_add]
    rw [mul_comm (v l)]
    congr 1
    congr 1
    ring
  have hz : w * u = 0 := by
    apply GlobalTheory.UnitLemma.Centraliser.eq_zero_of_trace_mul B hsep
    intro y

    rw [← e.sum_repr y, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_smul_comm, map_smul, hk k, smul_zero]
  have hw0 : w = 0 := (hu.mul_left_eq_zero).1 hz
  apply hv0
  exact (Fintype.linearIndependent_iff.1 e.linearIndependent) v hw0 |> funext

end GlobalTheory.UnitLemma.TraceDet
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.self_dual_hermitian_lattice_basis_exists : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E), (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) → (∀ x y, h y x = K.c (h x y)) → ∀ L : Submodule K.O V, L.FG → Submodule.span K.E (L : Set V) = ⊤ → (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) → ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, Submodule.span K.O (Set.range b) = L ∧ ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.SelfDualLattice.exists_orthonormal_basis | exact GlobalTheory.SelfDualLattice.exists_orthonormal_basis | (intros; apply GlobalTheory.SelfDualLattice.exists_orthonormal_basis <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Orbit

open GlobalTheory.UnitLemma

theorem coe_mulLat_of_coe_eq {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A]
    [Algebra O' A] (L : Submodule O A) (L' : Submodule O' A) (h : (L' : Set A) = L) (t : Aˣ) :
    (mulLat O' (t : A) L' : Set A) = mulLat O (t : A) L := by
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_mulLat, mem_mulLat, ← SetLike.mem_coe, h, SetLike.mem_coe]

theorem stabLat_of_coe_eq {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A]
    [Algebra O' A] (L : Submodule O A) (L' : Submodule O' A) (h : (L' : Set A) = L) :
    stabLat O' L' = stabLat O L := by
  ext t
  change (∀ y, y ∈ L' ↔ (t : A) * y ∈ L') ↔ ∀ y, y ∈ L ↔ (t : A) * y ∈ L
  simp only [← SetLike.mem_coe, h]

theorem orbSum_congr_coe {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A] [Algebra O' A]
    (G : Subgroup Aˣ) (X : Set (Submodule O A)) (X' : Set (Submodule O' A))
    (hX : ∀ L ∈ X, ∃ L' ∈ X', (L' : Set A) = L) (hX' : ∀ L' ∈ X', ∃ L ∈ X, (L : Set A) = L')
    (hG : intUnits O A ⊓ G = intUnits O' A ⊓ G) :
    orbSum O' G X' (fun _ => 1) = orbSum O G X (fun _ => 1) := by
  classical
  rw [orbSum_eq, orbSum_eq]
  let f : X → X' := fun L => ⟨Classical.choose (hX L.1 L.2), (Classical.choose_spec (hX L.1 L.2)).1⟩
  have hf : ∀ L : X, ((f L).1 : Set A) = L.1 := fun L => (Classical.choose_spec (hX L.1 L.2)).2
  let g : X' → X := fun L => ⟨Classical.choose (hX' L.1 L.2), (Classical.choose_spec (hX' L.1 L.2)).1⟩
  have hg : ∀ L : X', ((g L).1 : Set A) = L.1 := fun L => (Classical.choose_spec (hX' L.1 L.2)).2
  let e : X ≃ X' :=
    { toFun := f
      invFun := g
      left_inv := fun L => Subtype.ext (SetLike.coe_injective (by rw [hg, hf]))
      right_inv := fun L => Subtype.ext (SetLike.coe_injective (by rw [hf, hg])) }
  let q : Orb O G X ≃ Orb O' G X' := Quot.congr e (by
    intro L M
    constructor
    · rintro ⟨t, ht, h⟩
      refine ⟨t, ht, SetLike.coe_injective ?_⟩
      change ((f M).1 : Set A) = (mulLat O' (t : A) (f L).1 : Set A)
      rw [hf M, coe_mulLat_of_coe_eq L.1 (f L).1 (hf L) t, h]
    · rintro ⟨t, ht, h⟩
      refine ⟨t, ht, SetLike.coe_injective ?_⟩
      have h' : ((f M).1 : Set A) = (mulLat O' (t : A) (f L).1 : Set A) := congrArg SetLike.coe h
      rw [hf M, coe_mulLat_of_coe_eq L.1 (f L).1 (hf L) t] at h'
      exact h')
  rw [← finsum_comp_equiv q]
  refine finsum_congr fun o => ?_
  induction o using Quot.ind with
  | mk L =>
    change (((stabLat O' (f L).1 ⊓ G).relIndex (intUnits O' A ⊓ G) : ℕ) : ℚ) =
      (((stabLat O L.1 ⊓ G).relIndex (intUnits O A ⊓ G) : ℕ) : ℚ)
    rw [stabLat_of_coe_eq L.1 (f L).1 (hf L), hG]

end GlobalTheory.UnitLemma.Orbit
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_idempotent_star_eq_one_sub_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by
  first | exact @GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField | exact GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField | (intros; apply GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → Function.Bijective (fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a)) ∧ ∀ a : A.K, (∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a)) ∧ (Delta (A.invK τ p lam a) ≠ 0 ↔ IsUnit a) := by
  first | exact @GlobalTheory.JR.EtInv.invK_regular_iff_isUnit | exact GlobalTheory.JR.EtInv.invK_regular_iff_isUnit | (intros; apply GlobalTheory.JR.EtInv.invK_regular_iff_isUnit <;> assumption)
end
