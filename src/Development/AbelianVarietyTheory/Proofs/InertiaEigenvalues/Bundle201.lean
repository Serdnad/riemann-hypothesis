module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle078
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle089
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle117
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle193
public import GroundTheory.AutomorphicForms.Bundle014
import GroundTheory.AutomorphicForms.Bundle006
import GroundTheory.LocalFields.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

section Fibre

variable {O E A₁ A₂ : Type} [CommRing O] [Field E] [Algebra O E]
  [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]
  [IsScalarTower O E A₁] [IsScalarTower O E A₂]

theorem inf_ker_snd_eq (M : Submodule O (A₁ × A₂)) :
    M ⊓ LinearMap.ker (LinearMap.snd O A₁ A₂) =
      (M.comap (LinearMap.inl O A₁ A₂)).map (LinearMap.inl O A₁ A₂) := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
    Submodule.mem_comap, LinearMap.inl_apply]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨a, h, rfl⟩
  · rintro ⟨x, hx, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hx, rfl⟩

theorem isLat_of_comap_inl_map_snd {M : Submodule O (A₁ × A₂)}
    (h₁ : IsLat O E (M.comap (LinearMap.inl O A₁ A₂)))
    (h₂ : IsLat O E (M.map (LinearMap.snd O A₁ A₂))) : IsLat O E M := by
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd O A₁ A₂) h₂.1 ?_, ?_⟩
  · rw [inf_ker_snd_eq]; exact h₁.1.map _
  · set S := Submodule.span E (M : Set (A₁ × A₂)) with hS
    have hl : LinearMap.range (LinearMap.inl E A₁ A₂) ≤ S := by
      rw [LinearMap.range_eq_map, ← h₁.2, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span (by simpa using hx)
    have hr : S.map (LinearMap.snd E A₁ A₂) = ⊤ := by
      rw [hS, Submodule.map_span, ← h₂.2]
      congr 1
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ S.map (LinearMap.snd E A₁ A₂) := by rw [hr]; trivial
    obtain ⟨z, hz, hzb⟩ := hb
    have hab : ((a, b) : A₁ × A₂) = z + LinearMap.inl E A₁ A₂ (a - z.1) := by
      ext <;> simp [← hzb]
    rw [hab]
    exact S.add_mem hz (hl ⟨_, rfl⟩)

end Fibre

theorem ncard_fibre_latProj (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁]
    [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁]
    [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) :
    resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 →
      ∀ y : LatPair O E g₁ g₂, ((latProj O E g₁ g₂ ⁻¹' {y}).ncard : ℚ) =
        (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^
          val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  intro hR y
  have key := GlobalTheory.T.card_stable_lattices_alt O E A₁ A₂ g₁ g₂ hR y.1.1 y.2.1 y.1.2.1 y.2.2.1 y.1.2.2 y.2.2.2
  let e : ↥(latProj O E g₁ g₂ ⁻¹' {y}) ≃
      {M : Submodule O (A₁ × A₂) // (∀ z ∈ M, (g₁, g₂) * z ∈ M) ∧
        M.comap (LinearMap.inl O A₁ A₂) = y.1.1 ∧ M.map (LinearMap.snd O A₁ A₂) = y.2.1} :=
    { toFun := fun M => ⟨M.1.1, M.1.2.2,
        congrArg (fun p : LatPair O E g₁ g₂ => (p.1 : Submodule O A₁)) M.2,
        congrArg (fun p : LatPair O E g₁ g₂ => (p.2 : Submodule O A₂)) M.2⟩
      invFun := fun M => ⟨⟨M.1, isLat_of_comap_inl_map_snd (by rw [M.2.2.1]; exact y.1.2.1)
          (by rw [M.2.2.2]; exact y.2.2.1), M.2.1⟩,
        Set.mem_singleton_iff.mpr (Prod.ext (Subtype.ext M.2.2.1) (Subtype.ext M.2.2.2))⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  have hc : (latProj O E g₁ g₂ ⁻¹' {y}).ncard = Nat.card {M : Submodule O (A₁ × A₂) //
      (∀ z ∈ M, (g₁, g₂) * z ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = y.1.1 ∧
        M.map (LinearMap.snd O A₁ A₂) = y.2.1} := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr e
  rw [hc]
  exact key

end GlobalTheory.UnitLemma
end
end

section

open Polynomial

namespace GlobalTheory.UnitLemma

theorem aeval_mul_mem_of_stable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {g : A} {M : Submodule O A}
    (hM : ∀ y ∈ M, g * y ∈ M) (p : O[X]) {m : A} (hm : m ∈ M) : aeval g p * m ∈ M := by
  induction p using Polynomial.induction_on with
  | C a => simpa [Algebra.smul_def] using M.smul_mem a hm
  | add p q hp hq => simpa [add_mul] using M.add_mem hp hq
  | monomial n a ih =>
    have := hM _ ih
    have e : aeval g (Polynomial.C a * X ^ (n + 1)) * m = g * (aeval g (Polynomial.C a * X ^ n) * m) := by
      simp only [map_mul, aeval_C, aeval_X, map_pow, pow_succ]; ring
    rw [e]; exact this

theorem finite_orbits_stLat_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Finite (MulAction.orbitRel.Quotient Aˣ (stLat O E g)) := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ _ g hsep
  set C : Submodule O A := Subalgebra.toSubmodule (integralClosure O A) with hCdef
  have hCfg : C.FG := GlobalTheory.T.integralClosure_fg_dvr_of_separable_charpoly O E A g hsep
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.exists_common_denominator_aeval_of_fg' O E A g (GlobalTheory.T.exists_aeval_eq_of_mulLeft_charpoly_separable E A g hsep) C hCfg
  have hfin := GlobalTheory.T.finite_setOf_submodule_between_smul_and_fg O A C hCfg c hc0

  have key : ∀ M : stLat O E g, ∃ t : Aˣ, mulLat O ((t⁻¹ : Aˣ) : A) (M : Submodule O A) ∈
      {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N} := by
    intro M
    obtain ⟨hML, hMg⟩ := M.2
    set N : Submodule O A := C * (M : Submodule O A) with hN
    have hMN : (M : Submodule O A) ≤ N := by
      intro m hm
      have := Submodule.mul_mem_mul (show (1 : A) ∈ C from (integralClosure O A).one_mem) hm
      simpa using this
    have hNlat : IsLat O E N := by
      refine ⟨Submodule.FG.mul hCfg hML.1, ?_⟩
      rw [eq_top_iff, ← hML.2]
      exact Submodule.span_mono hMN
    have hNC : ∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N := by
      intro x hx y hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha m hm
        rw [← mul_assoc]
        exact Submodule.mul_mem_mul ((integralClosure O A).mul_mem hx ha) hm
      · intro u v hu hv
        rw [mul_add]; exact N.add_mem hu hv
    obtain ⟨t, ht⟩ := GlobalTheory.T.eq_submoduleMulLeftImage_integralClosure_of_separable O E A g hsep N hNlat hNC
    have hcN : ∀ y ∈ N, c • y ∈ (M : Submodule O A) := by
      intro y hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha m hm
        obtain ⟨p, hp⟩ := hc a ha
        rw [← smul_mul_assoc, ← hp]
        exact aeval_mul_mem_of_stable hMg p hm
      · intro u v hu hv
        rw [smul_add]; exact Submodule.add_mem _ hu hv
    refine ⟨t, ?_, ?_⟩
    · intro x hx
      rw [mem_mulLat_iff, inv_inv] at hx
      have h1 : (t : A) * x ∈ N := hMN hx
      rw [ht, mem_mulLat_iff] at h1
      rw [hCdef, Subalgebra.mem_toSubmodule]
      rw [Subalgebra.mem_toSubmodule] at h1
      simpa [← mul_assoc] using h1
    · intro y hy
      rw [mem_mulLat_iff, inv_inv]
      have h1 : (t : A) * y ∈ N := by
        rw [ht, mem_mulLat_iff, Subalgebra.mem_toSubmodule]
        rw [hCdef, Subalgebra.mem_toSubmodule] at hy
        simpa [← mul_assoc] using hy
      simpa [mul_smul_comm] using hcN _ h1
  choose t ht using key
  let F : MulAction.orbitRel.Quotient Aˣ (stLat O E g) → {N : Submodule O A // N ∈ {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}} :=
    fun q => ⟨_, ht q.out⟩
  haveI : Finite {N : Submodule O A // N ∈ {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}} := hfin.to_subtype
  refine Finite.of_injective F ?_
  intro q₁ q₂ h
  have h' : mulLat O (((t q₁.out)⁻¹ : Aˣ) : A) (q₁.out : Submodule O A) = mulLat O (((t q₂.out)⁻¹ : Aˣ) : A) (q₂.out : Submodule O A) :=
    congrArg Subtype.val h
  rw [← q₁.out_eq, ← q₂.out_eq]
  apply Quotient.sound
  refine ⟨t q₁.out * (t q₂.out)⁻¹, ?_⟩
  apply Subtype.ext
  rw [stLat_smul_val, Units.val_mul, mulLat_mul, ← h', ← mulLat_mul]
  simp [mulLat_one]

end GlobalTheory.UnitLemma
end

section

open scoped TensorProduct

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.NormSign

theorem exists_valuativeRel_of_normed : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F],
    ∃ _ : ValuativeRel F, IsNonarchimedeanLocalField F ∧ ∀ x y : F, x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  intro F _ _ _
  letI rel : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  have hc : (NormedField.valuation (K := F)).Compatible := Valuation.Compatible.ofValuation _
  refine ⟨rel, ?_, fun x y => Iff.rfl⟩
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := inferInstance, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F))
      (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)
  · rw [ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))]
    infer_instance

theorem norm_one_tmul {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L] [Algebra R L]
    [FiniteDimensional R L] (x : L) :
    Algebra.norm B ((1 : B) ⊗ₜ[R] x) = algebraMap R B (Algebra.norm R x) := by
  have h : Algebra.lmul B (B ⊗[R] L) ((1 : B) ⊗ₜ[R] x) = (Algebra.lmul R L x).baseChange B := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b z
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.norm_apply, h, LinearMap.det_baseChange, Algebra.norm_apply]

theorem norm_algebraMap_of_isPushout : ∀ (F E K L : Type) [Field F] [Field E] [Field K] [CommRing L] [Algebra F E] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L] [FiniteDimensional F E],
    Algebra.IsPushout F E K L → ∀ z : E, Algebra.norm K (algebraMap E L z) = algebraMap F K (Algebra.norm F z) := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ h z
  haveI := h.symm
  have he : Algebra.IsPushout.equiv F K E L ((1 : K) ⊗ₜ[F] z) = algebraMap E L z := by
    simp [Algebra.IsPushout.equiv_tmul]
  rw [← he, Algebra.norm_eq_of_algEquiv, norm_one_tmul]

theorem mul_norm_of_not_norm (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] [Field L] [Algebra K L] (h2 : Module.finrank K L = 2)
    (s t : Kˣ) (hs : ¬ ∃ y : L, Algebra.norm K y = s) (ht : ¬ ∃ y : L, Algebra.norm K y = t) :
    ∃ y : L, Algebra.norm K y = ((s * t : Kˣ) : K) := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have hN := GroundTheory.Automorphic.natCard_quotient_range_normUnits_eq_two (F := K) (E := L)
  have ht' : t ∉ (GroundTheory.LocalField.normUnits K L).range := fun h =>
    ht ((GroundTheory.Automorphic.mem_range_normUnits_iff t).1 h)
  rcases GroundTheory.Automorphic.mem_or_mul_inv_mem_of_natCard_eq_two hN ht' s with h | h
  · exact absurd ((GroundTheory.Automorphic.mem_range_normUnits_iff s).1 h) hs
  · obtain ⟨z, hz⟩ := (GroundTheory.Automorphic.mem_range_normUnits_iff _).1 h
    refine ⟨z * algebraMap K L (t : K), ?_⟩
    rw [map_mul, hz, Algebra.norm_algebraMap, h2]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    have := t.ne_zero
    field_simp

theorem norms_of_isField {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    A.NL 0 = 0 ∧
    (∀ s t : A.Kˣ, (¬ ∃ y, A.NL y = s) → (¬ ∃ y, A.NL y = t) → ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K)) ∧
      ∃ y, A.NL y = ((-1 : A.Kˣ) : A.K) := by
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  haveI := hU.ultraF
  haveI := hU.ultraE
  haveI := hU.lcF
  haveI := hU.lcE
  haveI := hU.charZero
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hU.finrank_eq
  have hKL : Module.finrank A.K A.L = 2 := by
    haveI := A.push.symm
    rw [← (Algebra.IsPushout.equiv F A.K E A.L).toLinearEquiv.finrank_eq, Module.finrank_baseChange,
      hU.finrank_eq]
  haveI : CharZero A.K := charZero_of_injective_algebraMap (algebraMap F A.K).injective
  obtain ⟨vF, hFloc, hFv⟩ := exists_valuativeRel_of_normed F
  refine ⟨?_, ?_⟩
  · haveI : FiniteDimensional A.K A.L := Module.finite_of_finrank_eq_succ hKL
    exact Algebra.norm_zero (R := A.K) (S := A.L)
  constructor
  · intro s t hs ht
    obtain ⟨vK, tK, hKloc, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension F A.K
    exact @mul_norm_of_not_norm A.K A.L _ vK tK hKloc _ _ _ hKL s t hs ht
  · obtain ⟨vE, hEloc, hEv⟩ := exists_valuativeRel_of_normed E
    haveI : ValuativeExtension F E := ⟨by
      intro a b
      rw [hEv, hFv, norm_algebraMap', norm_algebraMap']⟩
    obtain ⟨z, hz⟩ := GlobalTheory.T.exists_norm_eq_neg_one_of_unramified_values F E (fun y => by
      obtain ⟨x, hx⟩ := hU.unram y
      exact ⟨x, by rw [hEv, norm_algebraMap', hx], by rw [hEv, norm_algebraMap', hx]⟩)
    refine ⟨algebraMap E A.L z, ?_⟩
    have := norm_algebraMap_of_isPushout F E A.K A.L A.push z
    simp only [Et.NL, this, hz, map_neg, map_one, Units.val_neg, Units.val_one]

theorem omega_mul_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → (∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t) ∧ ω ((-1 : A.Kˣ) : A.K) = 1 := by
  classical
  intro F E _ _ _ _ _ A ψ x μ ω h
  obtain ⟨hK, hL, -, -, hω⟩ := h
  obtain ⟨hzero, hprod, hneg⟩ := norms_of_isField A hK hL
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  have hmul : ∀ s t : A.Kˣ, (∃ y, A.NL y = s) → (∃ y, A.NL y = t) → ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K) := by
    rintro s t ⟨y, hy⟩ ⟨y', hy'⟩
    exact ⟨y * y', by simp only [Et.NL] at hy hy' ⊢; rw [map_mul, hy, hy', Units.val_mul]⟩
  have hdiv : ∀ s t : A.Kˣ, (∃ y, A.NL y = s) → (∃ y, A.NL y = ((s * t : A.Kˣ) : A.K)) → ∃ y, A.NL y = t := by
    rintro s t ⟨y, hy⟩ ⟨y', hy'⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [hzero] at hy
      exact s.ne_zero hy.symm
    refine ⟨y' * y⁻¹, ?_⟩
    have h1 : A.NL y * A.NL y⁻¹ = 1 := by
      simp only [Et.NL]; rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    simp only [Et.NL] at hy hy' h1 ⊢
    rw [map_mul, hy', Units.val_mul]
    rw [hy] at h1
    calc (s : A.K) * t * (Algebra.norm A.K) y⁻¹ = t * ((s : A.K) * (Algebra.norm A.K) y⁻¹) := by ring
      _ = t := by rw [h1, mul_one]
  have hval : ∀ s : A.Kˣ, ω s = if ∃ y, A.NL y = s then 1 else -1 := by
    intro s
    split_ifs with hs
    · exact (hω s).1 hs
    · exact (hω s).2 hs
  refine ⟨fun s t => ?_, by rw [hval, if_pos hneg]⟩
  rw [hval s, hval t, hval (s * t)]
  by_cases hs : ∃ y, A.NL y = s <;> by_cases ht : ∃ y, A.NL y = t
  · rw [if_pos hs, if_pos ht, if_pos (hmul s t hs ht)]; ring
  · rw [if_pos hs, if_neg ht, if_neg (fun h => ht (hdiv s t hs h))]; ring
  · have hst : ¬ ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K) := fun h => hs (hdiv t s ht (by rwa [mul_comm]))
    rw [if_neg hs, if_pos ht, if_neg hst]; ring
  · rw [if_neg hs, if_neg ht, if_pos (hprod s t hs ht)]; ring

end GlobalTheory.JR.WeilQuad.NormSign
end
end

section

open GlobalTheory.BI GlobalTheory.BrauerZero

namespace GlobalTheory.BrauerZero

theorem ind_one_sub_index_mem_D0 {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hK : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) :
    ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by
  classical
  haveI := Fintype.ofFinite G
  haveI hN : K.Normal := ⟨fun n hn g => by
    have h1 := hK g n
    have : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [this]; exact K.mul_mem h1 hn⟩
  letI : CommGroup (G ⧸ K) :=
    { (inferInstance : Group (G ⧸ K)) with
      mul_comm := by
        intro x y
        induction x using QuotientGroup.induction_on with
        | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          have := hK b⁻¹ a⁻¹
          have e : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ := by group
          rw [e]; exact this }
  haveI : Fintype (G ⧸ K) := Fintype.ofFinite _
  let Q := Additive (G ⧸ K)

  let F : AddChar Q ℂ → G → ℂ := fun ψ g => ψ (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))
  have hFmul : ∀ ψ : AddChar Q ℂ, ∀ a b : G, F ψ (a * b) = F ψ a * F ψ b := by
    intro ψ a b
    simp only [F, QuotientGroup.mk_mul, ofMul_mul, AddChar.map_add_eq_mul]
  have hFone : ∀ ψ : AddChar Q ℂ, F ψ 1 = 1 := by
    intro ψ
    simp only [F, QuotientGroup.mk_one, ofMul_one, AddChar.map_zero_eq_one]

  have hgen : ∀ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ)) ∈ D0 G := by
    intro ψ
    let f : G →* ℂ := { toFun := F ψ, map_one' := hFone ψ, map_mul' := hFmul ψ }
    let χ : (⊤ : Subgroup G) →* ℂˣ := (MonoidHom.toHomUnits f).comp (⊤ : Subgroup G).subtype
    have hcl : ∀ g x : G, F ψ (x⁻¹ * g * x) = F ψ g := by
      intro g x
      rw [hFmul, hFmul, mul_comm (F ψ x⁻¹), mul_assoc, ← hFmul, inv_mul_cancel, hFone, mul_one]
    have h1 : ind (⊤ : Subgroup G) (fun h => (χ h : ℂ)) = F ψ := by
      exact (ind_top (F ψ) hcl : _)
    have h2 : ind (⊤ : Subgroup G) (fun _ => (1 : ℂ)) = fun _ => (1 : ℂ) :=
      ind_top (fun _ => (1 : ℂ)) (fun _ _ => rfl)
    apply AddSubgroup.subset_closure
    exact ⟨⊤, χ, by rw [h1, h2]⟩

  have hind : ∀ g : G, ind K (fun _ => (1 : ℂ)) g = if g ∈ K then (K.index : ℂ) else 0 := by
    intro g
    have hconj : ∀ x : G, (x⁻¹ * g * x ∈ K ↔ g ∈ K) := by
      intro x
      constructor
      · intro h
        have := hN.conj_mem _ h x
        have e : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
        rwa [e] at this
      · intro h
        have := hN.conj_mem _ h x⁻¹
        have e : x⁻¹ * g * x⁻¹⁻¹ = x⁻¹ * g * x := by group
        rwa [e] at this
    simp only [ind, finsum_eq_sum_of_fintype, ext0]
    have hs : ∀ x : G, (if h : x⁻¹ * g * x ∈ K then (1 : ℂ) else 0) = if g ∈ K then 1 else 0 := by
      intro x
      by_cases hg : g ∈ K
      · rw [dite_eq_left ((hconj x).2 hg), if_pos hg]
      · rw [dite_eq_right (fun h => hg ((hconj x).1 h)), if_neg hg]
    rw [Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, ← K.card_mul_index]
    have : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := K)).ne'
    split_ifs
    · push_cast; field_simp
    · simp

  have hsum : ∀ g : G, (∑ ψ : AddChar Q ℂ, F ψ g) = if g ∈ K then (K.index : ℂ) else 0 := by
    intro g
    have := AddChar.sum_apply_eq_ite (α := Q) (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))
    simp only [F]
    rw [this]
    have hc : (Fintype.card Q : ℂ) = (K.index : ℂ) := by
      rw [Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
    have he : (Additive.ofMul (QuotientGroup.mk g : G ⧸ K) = 0) ↔ g ∈ K := by
      rw [ofMul_eq_zero, QuotientGroup.eq_one_iff]
    by_cases hg : g ∈ K
    · rw [if_pos (he.2 hg), if_pos hg, hc]
    · rw [if_neg (fun h => hg (he.1 h)), if_neg hg]
  have hcard : (Fintype.card (AddChar Q ℂ) : ℂ) = (K.index : ℂ) := by
    rw [AddChar.card_eq, Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
  have heq : ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ))
      = ∑ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ)) := by
    funext g
    rw [Finset.sum_apply]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [hind g, hsum g, hcard]
  rw [heq]
  exact AddSubgroup.sum_mem _ (fun ψ _ => hgen ψ)

end GlobalTheory.BrauerZero
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.sum_local_inv_eq_zero_of_unramified_cocycle : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ζ : Ω), IsPrimitiveRoot ζ (l ^ 1) → ∃ inv : InvFam F Ω l 1, IsLocalInvariants ζ inv ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → ∀ Av : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v) → ∀ w : Z2 (muRep F Ω l 1), (∀ g h : G F Ω, ∀ n ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ n' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), w.1 (g * n, h * n') = w.1 (g, h)) → ∀ wl : ∀ v, Z2 (muLoc F l 1 (Av v)), (∀ v (g h : Dec (F := F) (Av v)), (wl v).1 (g, h) = w.1 ((g : G F Ω), (h : G F Ω))) → ∑ v ∈ S, inv (Av v) (Submodule.Quotient.mk (wl v)) = 0 := by
  first | exact @GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle | exact GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle | (intros; apply GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle <;> assumption)
end
