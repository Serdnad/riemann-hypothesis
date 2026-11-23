module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle010
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle012
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocQuot.proof : DegZeroLocQuot.Statement := by
  intro F _ K _ ι P _ 𝒲 h𝒲 x hx

  set φ : MRing ι F →+* FractionRing (MRing ι F ⧸ P) :=
    (algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))).comp (Ideal.Quotient.mk P) with hφ
  have hne : ∀ g : MRing ι F, g ∉ P → φ g ≠ 0 := fun g hg => by
    rw [hφ, RingHom.comp_apply, Ne, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  let Q : FractionRing (MRing ι F ⧸ P) → Prop := fun y =>
    ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧
      g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧ y = φ f / φ g
  have key : Q x := by
    refine Algebra.adjoin_induction (p := fun y _ => Q y) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩
      exact ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩
    · intro c
      refine ⟨0, C c, 1, isWeightedHomogeneous_C _ c, isWeightedHomogeneous_one F _, ?_, ?_, ?_⟩
      · exact (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top inferInstance)
      · intro W hW
        exact (Ideal.ne_top_iff_one W).mp (h𝒲 W hW).ne_top
      · rw [map_one, div_one, hφ, RingHom.comp_apply,
          IsScalarTower.algebraMap_apply F (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))]
        rfl
    · rintro y z - - ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ ⟨b', f', g', hf', hg', hgP', hgW', rfl⟩
      refine ⟨b + b', f * g' + g * f', g * g', (hf.mul hg').add (hg.mul hf'), hg.mul hg', ?_, ?_, ?_⟩
      · exact fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hgP hgP')
      · intro W hW h
        exact ((h𝒲 W hW).mem_or_mem h).elim (hgW W hW) (hgW' W hW)
      · rw [div_add_div _ _ (hne g hgP) (hne g' hgP'), map_add (f := _), map_mul, map_mul, map_mul]
    · rintro y z - - ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ ⟨b', f', g', hf', hg', hgP', hgW', rfl⟩
      refine ⟨b + b', f * f', g * g', hf.mul hf', hg.mul hg', ?_, ?_, ?_⟩
      · exact fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hgP hgP')
      · intro W hW h
        exact ((h𝒲 W hW).mem_or_mem h).elim (hgW W hW) (hgW' W hW)
      · rw [div_mul_div_comm, map_mul, map_mul]
  exact key

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u

theorem isPrime_map_C_mvPolynomial {A : Type*} [CommRing A] (σ : Type*) (p : Ideal A) [p.IsPrime] :
    (p.map (C : A →+* MvPolynomial σ A)).IsPrime := by
  rw [← Ideal.mk_ker (I := p), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _

section Cone

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def coneVarMap (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (v : ∀ k, ι k) :
    MvPolynomial K (degZeroLoc P {W}) →ₐ[degZeroLoc P {W}] coneLocal P W hPW :=
  aeval fun k => algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P (X ⟨k, v k⟩))

end Cone

def ConePolyLocalization.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∃ (_ : IsLocalRing (degZeroLoc P {W})),
      letI := (coneVarMap P W hPW v).toRingHom.toAlgebra
      haveI := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
      IsLocalization.AtPrime (coneLocal P W hPW)
        ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Rank

variable {F L₀ L : Type*} [Field F] [Field L₀] [Field L] [Algebra F L₀] [Algebra F L]

theorem isFractionRing_of_div {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    (inj : Function.Injective (algebraMap A K))
    (surj : ∀ z : K, ∃ x y : A, z = algebraMap A K x / algebraMap A K y) : IsFractionRing A K :=
  haveI := (faithfulSMul_iff_algebraMap_injective A K).mpr inj
  IsFractionRing.of_field A K surj

theorem finrank_eq_relfinrank_of_div (φ : L₀ →ₐ[F] L) {K₀ : IntermediateField F L₀}
    {E : IntermediateField F L} (hKE : K₀.map φ ≤ E) {A : Subalgebra F L₀} {B : Subalgebra F L}
    [Algebra A B] (hφ : ∀ a : A, ((algebraMap A B a : B) : L) = φ a) (hA : ∀ a ∈ A, a ∈ K₀)
    (hB : ∀ b ∈ B, b ∈ E) (fracA : ∀ x ∈ K₀, ∃ y ∈ A, ∃ z ∈ A, z ≠ 0 ∧ x = y / z)
    (fracB : ∀ x ∈ E, ∃ y ∈ B, ∃ z ∈ B, z ≠ 0 ∧ x = y / z) :
    Module.finrank A B = IntermediateField.relfinrank (K₀.map φ) E := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le hKE]
  set K := K₀.map φ
  set Lf := IntermediateField.extendScalars hKE
  let _ : Algebra A K := (((φ.comp A.val).toRingHom).codRestrict K
    (fun a => show φ a ∈ K from ⟨a, hA a a.2, rfl⟩)).toAlgebra
  let _ : Algebra B Lf := ((B.val.toRingHom).codRestrict Lf (fun b => hB b b.2)).toAlgebra
  let _ : Algebra A Lf := ((algebraMap B Lf).comp (algebraMap A B)).toAlgebra
  have _ : IsScalarTower A B Lf := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have _ : IsScalarTower A K Lf := IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext (hφ a))
  have _ : IsFractionRing A K := by
    refine isFractionRing_of_div (fun a b h => Subtype.ext (φ.injective ?_)) ?_
    · exact congrArg Subtype.val h
    · rintro ⟨_, x, hx, rfl⟩
      obtain ⟨y, hy, z, hz, -, rfl⟩ := fracA x hx
      exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext (map_div₀ φ y z)⟩
  have _ : IsFractionRing B Lf := by
    refine isFractionRing_of_div (fun a b h => Subtype.ext (congrArg Subtype.val h :)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, -, rfl⟩ := fracB x hx
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext rfl⟩
  exact (IsFractionRing.finrank_eq A K B Lf).symm

end Rank

theorem mem_homFracDegZero_of_mem_degZeroLoc {K : Type*} [DecidableEq K] {ι : K → Type*}
    {F : Type*} [Field F] (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))) :
    ∀ x ∈ degZeroLoc P 𝒲, x ∈ homFracDegZero P := by
  intro x hx
  refine (Algebra.adjoin_le (S := (homFracDegZero P).toSubalgebra) ?_) hx
  rintro _ ⟨b, f, g, hf, hg, hgP, -, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨b, f, g, hf, hg, hgP, rfl⟩

theorem SemilocalFiniteRank.proof (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFinite.Statement.{u}) (h3 : DegZeroLocFrac.Statement.{u}) :
    SemilocalFiniteRank.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hd' hd W hW hdW hle
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hd' hd W hW hdW hle
  have inj : Function.Injective (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W))) := by
    intro a b hab
    apply Subtype.ext
    apply (contractFracMap j P').toRingHom.injective
    have := congrArg Subtype.val hab
    rwa [degZeroLoc.algebraMap_contract_coe, degZeroLoc.algebraMap_contract_coe] at this
  refine ⟨h2 F K K' j ι' P' hP' n hd' hd W hW hdW hle, ⟨fun r hr x y hxy => ?_⟩, ?_⟩
  · have hr0 : algebraMap (degZeroLoc (contractPrime j P') {W})
        (degZeroLoc P' (fibrePrimes j P' W)) r ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap (degZeroLoc (contractPrime j P') {W})
        (degZeroLoc P' (fibrePrimes j P' W))), inj.eq_iff]
      exact hr.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ hr0 hxy
  · refine finrank_eq_relfinrank_of_div (contractFracMap j P') (map_homFracDegZero_le j ι' P')
      (degZeroLoc.algebraMap_contract_coe j P' W)
      (mem_homFracDegZero_of_mem_degZeroLoc _ _) (mem_homFracDegZero_of_mem_degZeroLoc _ _) ?_ ?_
    · intro x hx
      refine h3 F K (fun k => ι' (j k)) (contractPrime j P')
        (isMultiProjPrime_contractPrime _ _ hP') {W} (Set.finite_singleton W) ?_ x hx
      intro W₁ hW₁
      rw [Set.mem_singleton_iff.mp hW₁]
      exact hW
    · exact h3 F K' ι' P' hP' (fibrePrimes j P' W) hfin (fun W' hW' => hW'.1)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem exists_mul_isIntegral_of_eq_mul_inv {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (R A : Subalgebra F Ω) (hRA : R ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ R, ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    {x : Ω} (hx : IsIntegral A x) : ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ IsIntegral R (d * x) := by
  let M : Submonoid R :=
    { carrier := {d | (d : Ω) ≠ 0 ∧ (d : Ω)⁻¹ ∈ A}
      mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, by
        rw [Subalgebra.coe_mul, mul_inv]; exact A.mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_ne_zero, by rw [Subalgebra.coe_one, inv_one]; exact A.one_mem⟩ }
  let _ : Algebra R A := (Subalgebra.inclusion hRA).toAlgebra
  have : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization M A := by
    refine (isLocalization_iff M A).mpr ⟨fun d => ?_, fun a => ?_, fun {a b} h => ⟨1, ?_⟩⟩
    · exact ⟨⟨_, ⟨_, d.2.2⟩, Subtype.ext (mul_inv_cancel₀ d.2.1), Subtype.ext (inv_mul_cancel₀ d.2.1)⟩, rfl⟩
    · obtain ⟨r, hr, d, hd, hd0, hdA, he⟩ := hloc a a.2
      refine ⟨(⟨r, hr⟩, ⟨⟨d, hd⟩, hd0, hdA⟩), Subtype.ext ?_⟩
      change (a : Ω) * d = r
      rw [he, mul_assoc, inv_mul_cancel₀ hd0, mul_one]
    · have e : ((algebraMap R A a : A) : Ω) = (algebraMap R A b : A) := congrArg Subtype.val h
      have e' : (a : Ω) = b := e
      rw [Subtype.ext e']
  obtain ⟨⟨d, hd0, hdA⟩, hint⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (M := M) (Rₘ := A) x hx
  exact ⟨d, d.2, hd0, hdA, hint⟩


open IntermediateField.algebraAdjoinAdjoin in
theorem exists_finset_integral_span (hN : NoetherIntegralClosureFinite.Statement.{u})
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] {S : Set Ω} (hS : S.Finite)
    (A : Subalgebra F Ω) (L : IntermediateField F Ω) (hRA : Algebra.adjoin F S ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin F S, ∃ d ∈ Algebra.adjoin F S,
      d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    (hEL : IntermediateField.adjoin F S ≤ L)
    (hfin : FiniteDimensional (IntermediateField.adjoin F S) (IntermediateField.extendScalars hEL)) :
    ∃ s : Finset Ω, (∀ e ∈ s, e ∈ L ∧ IsIntegral A e) ∧
      ∀ x ∈ L, IsIntegral A x → x ∈ Submodule.span A (s : Set Ω) := by
  classical
  let L' := IntermediateField.extendScalars hEL
  let _ : Algebra (Algebra.adjoin F S) L' :=
    ((algebraMap (IntermediateField.adjoin F S) L').comp
      (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S))).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) (IntermediateField.adjoin F S) L' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType F (Algebra.adjoin F S) := Algebra.FiniteType.adjoin_of_finite hS
  obtain ⟨t, ht⟩ := Module.finite_def.mp
    (hN F (Algebra.adjoin F S) (IntermediateField.adjoin F S) L')
  let ι₀ : L' →ₐ[Algebra.adjoin F S] Ω := { L'.val.toRingHom with commutes' := fun _ => rfl }
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective
  let _ : Algebra (Algebra.adjoin F S) A := (Subalgebra.inclusion hRA).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨t.image fun y => ι₀ y.1, ?_, fun x hx hxA => ?_⟩
  · intro e he
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp he
    exact ⟨(IntermediateField.mem_extendScalars hEL).mp y.1.2,
      ((isIntegral_algHom_iff ι₀ hι₀).mpr y.2).tower_top⟩
  obtain ⟨d, hd, hd0, hdA, hint⟩ := exists_mul_isIntegral_of_eq_mul_inv _ A hRA hloc hxA
  let z : integralClosure (Algebra.adjoin F S) L' :=
    ⟨⟨d * x, (IntermediateField.mem_extendScalars hEL).mpr
      (mul_mem (hEL (IntermediateField.algebra_adjoin_le_adjoin F S hd)) hx)⟩,
      (isIntegral_algHom_iff ι₀ hι₀).mp hint⟩
  have hz : ι₀ z ∈ Submodule.span (Algebra.adjoin F S) ((t.image fun y => ι₀ y.1 : Finset Ω) : Set Ω) := by
    have hzt : z ∈ Submodule.span (Algebra.adjoin F S) (t : Set _) := ht ▸ Submodule.mem_top
    have := Submodule.mem_map_of_mem
      (f := ι₀.toLinearMap.comp (integralClosure (Algebra.adjoin F S) L').val.toLinearMap) hzt
    rw [Submodule.map_span] at this
    rw [Finset.coe_image]
    exact this
  have e : (⟨d⁻¹, hdA⟩ : A) • (d * x) = x := by
    rw [Subalgebra.smul_def, smul_eq_mul, ← mul_assoc]
    change d⁻¹ * d * x = x
    rw [inv_mul_cancel₀ hd0, one_mul]
  rw [← e]
  exact Submodule.smul_mem _ _ (Submodule.span_le_restrictScalars (Algebra.adjoin F S) A _ hz)

section Chart

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem isMultiHomog_chartMonomial (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by
  have hb : (∑ k, b k • blockWeight ι ⟨k, u k⟩) = b := by
    funext k
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  have h := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩)
    fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (b k)
  unfold IsMultiHomog chartMonomial
  convert h using 1
  exact hb.symm


omit [DecidableEq K] in
theorem chartMonomial_not_mem_of_notMem (W : Ideal (MRing ι F)) [W.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) (b : K → ℕ) : chartMonomial u b ∉ W :=
  (Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (hu k) _ : chartMonomial u b ∈ W.primeCompl)

theorem degZeroLoc_map_eq_mul_inv (hQ : DegZeroLocQuot.Statement.{u})
    (hD : MChartDehomog.Statement.{u}) (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) {Ω : Type*} [Field Ω]
    [Algebra F Ω] (φ : FractionRing (MRing ι F ⧸ P) →ₐ[F] Ω) :
    Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))) ≤ (degZeroLoc P {W}).map φ ∧
      ∀ a ∈ (degZeroLoc P {W}).map φ,
        ∃ r ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
        ∃ d ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
          d ≠ 0 ∧ d⁻¹ ∈ (degZeroLoc P {W}).map φ ∧ a = r * d⁻¹ := by
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k h => hu k (hPW h)
  have hW1 : ∀ W' ∈ ({W} : Set (Ideal (MRing ι F))), W'.IsPrime := fun W' h => by
    rw [Set.mem_singleton_iff.mp h]; infer_instance
  have hmem : ∀ p, φ (chartMap P u p) ∈
      Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))) := fun p => by
    rw [← aeval_range]
    refine ⟨p, ?_⟩
    change aeval _ p = (φ.comp (chartMap P u)) p
    rw [chartMap, comp_aeval]
    simp
  have hq : ∀ g : MRing ι F, g ∉ P → algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P g) ≠ 0 := fun g hg => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  refine ⟨Algebra.adjoin_le ?_, fun a ha => ?_⟩
  · rintro _ ⟨v, rfl⟩
    refine Subalgebra.mem_map.mpr ⟨_, div_mem_degZeroLoc P {W} (b := blockWeight ι v)
      (isWeightedHomogeneous_X F _ v) (isWeightedHomogeneous_X F (blockWeight ι) ⟨v.1, u v.1⟩)
      (huP v.1) (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hu v.1), ?_⟩
    simp [chartMap]
  obtain ⟨a, haA, rfl⟩ := Subalgebra.mem_map.mp ha
  obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := hQ F K ι P {W} hW1 a haA
  have hm := chartMonomial_not_mem_of_notMem (F := F) W u hu b
  have hm0 := hq _ fun h => hm (hPW h)
  have hg0 := hq g hgP
  refine ⟨φ (chartMap P u f), hmem f, φ (chartMap P u g), hmem g, ?_, ?_, ?_⟩
  · rw [hD F K ι P u huP g b hg, map_ne_zero]
    exact div_ne_zero hg0 hm0
  · rw [hD F K ι P u huP g b hg, ← map_inv₀, inv_div]
    exact Subalgebra.mem_map.mpr ⟨_, div_mem_degZeroLoc P {W} (isMultiHomog_chartMonomial u b) hg
      hgP (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hgW W rfl), rfl⟩
  · rw [hD F K ι P u huP f b hf, hD F K ι P u huP g b hg, ← map_inv₀, ← map_mul]
    congr 1
    field_simp

end Chart

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

abbrev degZeroLoc.algebraOfSubset {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) [P.IsPrime] {𝒲₁ 𝒲₂ : Set (Ideal (MRing ι F))} (h𝒲 : 𝒲₁ ⊆ 𝒲₂) :
    Algebra (degZeroLoc P 𝒲₂) (degZeroLoc P 𝒲₁) :=
  (Subalgebra.inclusion (degZeroLoc_anti P h𝒲)).toRingHom.toAlgebra


set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxHeartbeats 400000 in
def SemilocalMaxIdeals.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      ∃ (𝔪 : fibrePrimes j P' W → Ideal (degZeroLoc P' (fibrePrimes j P' W)))
        (h𝔪 : ∀ W', (𝔪 W').IsMaximal),
        Function.Injective 𝔪 ∧
        (∀ M : Ideal (degZeroLoc P' (fibrePrimes j P' W)), M.IsMaximal → ∃ W', M = 𝔪 W') ∧
        ∀ W' : fibrePrimes j P' W,
          (haveI := (h𝔪 W').isPrime
           letI := degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
           IsLocalization.AtPrime (degZeroLoc P' {W'.1}) (𝔪 W')) ∧
          haveI := W'.2.1.isPrime
          Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸ 𝔪 W') = (relDeg j W'.1 : ℕ∞)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
