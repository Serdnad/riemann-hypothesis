module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle275
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCardIndexRanks
import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle274
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle269
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle263
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle264
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle267
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.FieldsEx

variable {E : Type} [Field E] [NumberField E] {h : ℕ}

theorem one_mem_pow : (1 : E) ∈ powIdealElts E h :=
  ⟨one_ne_zero, 1, by rw [one_pow, FractionalIdeal.spanSingleton_one]⟩

theorem mul_mem_pow {x y : E} (hx : x ∈ powIdealElts E h) (hy : y ∈ powIdealElts E h) :
    x * y ∈ powIdealElts E h := by
  obtain ⟨hx0, a, ha⟩ := hx
  obtain ⟨hy0, b, hb⟩ := hy
  exact ⟨mul_ne_zero hx0 hy0, a * b, by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ha, hb, mul_pow]⟩

theorem inv_mem_pow {x : E} (hx : x ∈ powIdealElts E h) : x⁻¹ ∈ powIdealElts E h := by
  obtain ⟨hx0, a, ha⟩ := hx
  exact ⟨inv_ne_zero hx0, a⁻¹, by rw [← FractionalIdeal.spanSingleton_inv, ha, inv_pow]⟩

theorem npow_mem_pow {x : E} (hx : x ∈ powIdealElts E h) (n : ℕ) : x ^ n ∈ powIdealElts E h := by
  induction n with
  | zero => rw [pow_zero]; exact one_mem_pow
  | succ n ih => rw [pow_succ]; exact mul_mem_pow ih hx

theorem zpow_mem_pow {x : E} (hx : x ∈ powIdealElts E h) (n : ℤ) : x ^ n ∈ powIdealElts E h := by
  cases n with
  | ofNat n => simpa using npow_mem_pow hx n
  | negSucc n => rw [zpow_negSucc]; exact inv_mem_pow (npow_mem_pow hx _)

theorem prod_mem_pow {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, f i ∈ powIdealElts E h) :
    ∏ i ∈ s, f i ∈ powIdealElts E h :=
  Finset.prod_induction f (· ∈ powIdealElts E h) (fun _ _ => mul_mem_pow) one_mem_pow hf

theorem map_mem_pow {E' : Type} [Field E'] [NumberField E'] (σ : E →+* E') {x : E} (hx : x ∈ powIdealElts E h) :
    σ x ∈ powIdealElts E' h := by
  obtain ⟨hx0, a, ha⟩ := hx
  have hle : (𝓞 E)⁰ ≤ Submonoid.comap (RingOfIntegers.mapRingHom σ) (𝓞 E')⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ fun a b hab =>
      RingOfIntegers.ext (σ.injective (congrArg (fun y : 𝓞 E' => (y : E')) hab))
  have hm : IsLocalization.map E' (RingOfIntegers.mapRingHom σ) hle = σ :=
    IsLocalization.ringHom_ext (𝓞 E)⁰ (by rw [IsLocalization.map_comp]; rfl)
  refine ⟨(map_ne_zero σ).2 hx0, FractionalIdeal.extendedHom' E' hle a, ?_⟩
  rw [← map_pow, ← ha]
  change _ = FractionalIdeal.extended E' _ _
  rw [FractionalIdeal.extended_spanSingleton, hm]

theorem exists_aut [IsGalois ℚ E] (φ τ : E →+* ℂ) : ∃ σ : E ≃ₐ[ℚ] E, ∀ x, τ x = φ (σ x) := by
  letI := φ.toAlgebra
  let t : E →ₐ[ℚ] ℂ := τ.toRatAlgHom
  exact ⟨t.restrictNormal' E, fun x => (t.restrictNormal_commutes E x).symm⟩

theorem exists_gen (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ γ : 𝓞 E, γ ≠ 0 ∧ 𝔞 ^ classNumber E = Ideal.span {γ} := by
  let 𝔠 : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  have h1 : ClassGroup.mk0 (𝔠 ^ classNumber E) = 1 := by
    rw [map_pow, classNumber, pow_card_eq_one]
  obtain ⟨γ, hγ⟩ := (ClassGroup.mk0_eq_one_iff (𝔠 ^ classNumber E).2).1 h1
  have hγ' : 𝔞 ^ classNumber E = Ideal.span {γ} := hγ
  refine ⟨γ, ?_, hγ'⟩
  rintro rfl
  rw [Ideal.span_singleton_zero] at hγ'
  exact pow_ne_zero _ h𝔞 hγ'

theorem span_eq_extend (K : IntermediateField ℚ ℂ) [NumberField K] (τ : E →+* ℂ) (hK : ∀ x, τ x ∈ K)
    (𝔞 : Ideal (𝓞 E)) : Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} =
      extendIdealHom (τ.codRestrict K hK) 𝔞 := by
  refine Eq.trans ?_ (span_image_eq_coeSubmodule_map (τ.codRestrict K hK) 𝔞)
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
  rfl

end GlobalTheory.Mem.FieldsEx

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.MetSharp

open Formalism.IndefR.Mult

section Schur

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sm_ne_zero_of_ne {M : DSModel V S} {u : MMap M} (hu : u ≠ 0) : ∀ τ, ∃ w : M.sm τ, w ≠ 0 := by
  intro τ
  by_contra h
  push_neg at h
  exact hu (MultilinearMap.ext fun v => (u.map_coord_zero τ (h (v τ))).trans rfl)

theorem ipM_smul_measure_self (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {u : MMap M} {a : ℝ} (ha : 0 ≤ a)
    (hu : u ≠ 0) (h : ∃ c, IsMultIP M μ 𝓕 u u c) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 u u = (a : ℂ) * ipM M μ 𝓕 u u := by
  choose w hw using sm_ne_zero_of_ne hu
  have hv0 : ∏ τ, ⟪(w τ : M.H τ), (w τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 fun h => hw τ (Submodule.coe_eq_zero.1 h)
  have h1 : IsMultIP M (ENNReal.ofReal a • μ) 𝓕 u u ((a : ℂ) * ipM M μ 𝓕 u u) := by
    intro v v'
    obtain ⟨h1, h2⟩ := ipM_spec M μ 𝓕 u u h v v'
    refine ⟨?_, ?_⟩
    · unfold IntegrableOn at h1 ⊢
      rw [Measure.restrict_smul]
      exact h1.smul_measure ENNReal.ofReal_ne_top
    · rw [Measure.restrict_smul, integral_smul_measure, h2, ENNReal.toReal_ofReal ha, Complex.real_smul, mul_assoc]
  exact hasPeterssonInner_unique M _ 𝓕 u u w hv0 (ipM_spec M _ 𝓕 u u ⟨_, h1⟩) h1

end Schur

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem norm_sq_rows (hP : Pins R F cG) (Z : ReadL R F X0 Y) (y : Fin ((s1Of R F).D) → D.what₂.LL) :
    ‖D.jEE (Z.eRR y)‖ ^ 2 =
      (RealDat.nP F.lv2 true)⁻¹ * ‖(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)‖ ^ 2 := by
  set z : R.HE.H := Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)
    ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)) with hz
  have hzn : ‖(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)‖ = ‖z‖ := rfl
  rw [hzn]
  obtain ⟨hinj, -, hip⟩ := hP.char.base.models.HE
  set w := D.jEE (Z.eRR y) with hw
  have hT := Y.tied.sharp.ee w w
  have hJ := Z.jEE y
  have hE : ⟪w, w⟫_ℂ = ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 true)⁻¹ • R.ν0) R.fd0 (R.HE.e z) (R.HE.e z) := by
    rw [hT]
    show ipMT _ _ _ _ _ = _
    rw [ipMT, hJ]
    show ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 true)⁻¹ • R.ν0) R.fd0
      (PiTensorProduct.lift.symm (PiTensorProduct.lift (R.HE.e z))) (PiTensorProduct.lift.symm (PiTensorProduct.lift (R.HE.e z))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hip' : ⟪z, z⟫_ℂ = ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) := hip z z
  have ha : (0 : ℝ) ≤ (RealDat.nP F.lv2 true)⁻¹ := (inv_pos.2 (RealDat.nP_pos (F := F.lv2) true)).le
  by_cases hz0 : z = 0
  · have hu : R.HE.e z = 0 := by rw [hz0, map_zero]
    have hw0 : w = 0 := by
      apply Y.Ish.jE.injective
      rw [map_zero]
      apply Subtype.ext
      rw [hJ]
      show PiTensorProduct.lift (R.HE.e z) = 0
      rw [hu, map_zero]
    rw [hw0, hz0, norm_zero, norm_zero]
    ring
  · have hu : R.HE.e z ≠ 0 := fun h => hz0 (hinj (h.trans (map_zero _).symm))
    have hex : ∃ c, IsMultIP (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) c := by
      by_contra hno
      have h0 : ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) = 0 := by
        unfold ipM
        rw [dite_eq_right hno]
      exact hz0 (inner_self_eq_zero.1 (hip'.trans h0))
    rw [ipM_smul_measure_self (R.MY 0) R.ν0 R.fd0 ha hu hex, ← hip'] at hE
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ _ _ _ _ z, hE]
    exact Complex.re_ofReal_mul _ _

theorem majAt_rows_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →
    ∀ x y, Formalism.HermitianLatticesTheory.majAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR x) (Z.eRR y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 x y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  have hR := (complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim).rowHyp true
  have hn := hR.h4pos.2.2 true
  have hv0 := (pins_card_index_ranks D G Pl0 I0 T A3 Ks R F cG hP).2.2.2.2
  refine fun x y => GlobalTheory.Mem.RowSides.majAt_eq_of_normAt _ _ _ _ _ Z.eRR.toLinearMap (fun y => ?_) x y
  have hL : Formalism.HermitianLatticesTheory.normAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR y) = ‖D.jEE (Z.eRR y)‖ := by
    rw [hv0]; exact D.jEE_norm _
  have hr : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 y y =
      (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) *
        ⟪(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y), (R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)⟫_ℂ :=
    PrincipalLevelLattice.majorant_at_base_place_eq_inner (R.toCx3 F) F.cr true hR.h2 hn y y
  show Formalism.HermitianLatticesTheory.normAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR y) ^ 2 =
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 y ^ 2
  rw [hL, norm_sq_rows hP Z y]
  refine Eq.trans ?_ (Formalism.BasicNotions.normAt_sq_eq_majAt _ _ _ _).symm
  rw [hr, inner_self_eq_norm_sq_to_K, Complex.re_ofReal_mul]
  norm_cast

end GlobalTheory.Mem.R3.MetSharp
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem mem_of_avg {K : Type} [Field K] (σ : K →+* ℂ) {V : Type} [AddCommGroup V] [Module K V] {G : Type} [Group G]
    (r : Representation K G V) (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) {M : Type} [AddCommGroup M] [Module ℂ M]
    (j : V →ₛₗ[σ] M) (T : P → M →ₗ[ℂ] M) (hT : ∀ p v, T p (j v) = j (r p v))
    (S : Submodule ℂ M) (hS : ∀ v, (∀ h : P, r h v = ((ψ h : Kˣ) : K) • v) → j v ∈ S)
    (Fn : M) (hF : Fn ∈ Submodule.span ℂ (Set.range j)) (hFn : ∀ p, T p Fn = σ ((ψ p : Kˣ) : K) • Fn) : Fn ∈ S := by
  let Pj : M →ₗ[ℂ] M := (Nat.card P : ℂ)⁻¹ • ∑ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p
  have hPj : ∀ x, Pj x = (Nat.card P : ℂ)⁻¹ • ∑ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p x := by
    intro x
    simp only [Pj, LinearMap.smul_apply, LinearMap.sum_apply]
  have hcard : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hfix : Pj Fn = Fn := by
    have hterm : ∀ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p Fn = Fn := by
      intro p
      rw [hFn, smul_smul, ← map_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, map_one, one_smul]
    rw [hPj, Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hmap : ∀ v, Pj (j v) ∈ S := by
    intro v
    have e : Pj (j v) = j ((Nat.card P : K)⁻¹ • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p v) := by

      rw [hPj, map_smulₛₗ, map_sum, map_inv₀, map_natCast]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smulₛₗ, hT]
    rw [e]
    exact hS _ (avg_level K V G r P ψ v)
  have hle : Submodule.span ℂ (Set.range j) ≤ S.comap Pj :=
    Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact hmap v)
  have hPF : Pj Fn ∈ S := hle hF
  rwa [hfix] at hPF

theorem exists_rowForm (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G)
    (ψ : P →* D.what₂.LLˣ) (t : T) (f : A.fam.amb.FR t) (hlv : ∀ h : P, (A.fam.R t).r h f = ((ψ h : D.what₂.LLˣ) : D.what₂.LL) • f) :
    ∃ x, rowForm A P ψ t x = f :=
  (GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char _ _ _ (A.fam.R t).r P ψ f).2 hlv

theorem jR_mem_span (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (g : A.fam.amb.FR t)
    (hg : ∀ h : (F.lvl b).P, (A.fam.R t).r h g = (((F.lvl b).ψ h : D.what₂.LLˣ) : D.what₂.LL) • g)
    (Y : Bridge.Gf D.sp.X' → R.cX.W) (hY : Y = R.B.jR t g) :
    Y ∈ Submodule.span ℂ (Set.range fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)) := by
  obtain ⟨x, hx⟩ := exists_rowForm D G Pl0 T A (F.lvl b).P (F.lvl b).ψ t g hg
  subst hY
  subst hx
  exact Submodule.subset_span ⟨x, rfl⟩



theorem proj_span : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → Fn ∈ Submodule.span ℂ (Set.range fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F b t Fn hF hQ
  have hB := Bridge.ClassPres.extBij_holds (R.B.R t).pres
  have hF0 : Fn ∈ Submodule.span ℂ (Set.range (R.B.R t).pres.extL) := by rw [hB.2]; exact hF
  have hF' : Fn ∈ Submodule.span ℂ (Set.range (R.B.jR t)) := hF0
  obtain ⟨κ, hκ⟩ : ∃ κ : (F.lvl b).P → (levEnv D.sp.X' R.βX (R.datXt t)).Q,
      ∀ p, (R.B.R t).act_tie.red (κ p) = (p : G) :=
    ⟨fun p => ((R.B.R t).act_tie.red_surj (p : G)).choose,
      fun p => ((R.B.R t).act_tie.red_surj (p : G)).choose_spec⟩
  obtain ⟨gl, gl_apply⟩ : ∃ gl : (F.lvl b).P → (Bridge.Gf D.sp.X' → R.cX.W) →ₗ[ℂ] (Bridge.Gf D.sp.X' → R.cX.W),
      ∀ p H, gl p H = Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) H :=
    ⟨fun p => { toFun := fun H => Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) H
                map_add' := by intro H H'; funext h; simp only [Bridge.g0Act, Pi.add_apply, smul_add]
                map_smul' := by intro c H; funext h; simp only [Bridge.g0Act, Pi.smul_apply, RingHom.id_apply]; rw [smul_comm] },
      fun _ _ => rfl⟩
  have hact : ∀ (p : (F.lvl b).P) (f : A.fam.amb.FR t), gl p (R.B.jR t f) = R.B.jR t ((A.fam.R t).r p f) := by
    intro p f
    have e : (R.B.R t).pres.extL (A.leftGroupActionRight t (p : G) f) =
        Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) ((R.B.R t).pres.extL f) :=
      (R.B.R t).act_tie.act_eq (p : G) (κ p) (hκ p) f
    exact (gl_apply p _).trans e.symm
  have hg : ∀ p : (F.lvl b).P, gl p Fn = D.what₂.embLL (((F.lvl b).ψ p : D.what₂.LLˣ) : D.what₂.LL) • Fn := by
    intro p
    have hq : (R.B.R t).act_tie.red (κ p) ∈ (F.lvl b).P := by rw [hκ p]; exact p.2
    rw [gl_apply]
    funext h
    simp only [Bridge.g0Act, Pi.smul_apply]
    rw [hQ (κ p) hq h]
    have hp : (⟨_, hq⟩ : (F.lvl b).P) = p := Subtype.ext (hκ p)
    rw [hp, smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
  exact mem_of_avg D.what₂.embLL (A.fam.R t).r (F.lvl b).P (F.lvl b).ψ (R.B.jR t) gl hact _
    (fun v hv => jR_mem_span D G Pl0 T A Ks R F b t v hv _ rfl) Fn hF' hg

end GlobalTheory.TopSpan
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem prim_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3) (h : PrimRows3 R F)
    (h1 : ∀ i t p v, 0 < lam i t p v) (h2 : (R.updS R.kap lam).PThmB) (h3 : (R.updS R.kap lam).PThmA)
    (h4 : ((R.updS R.kap lam).toCx3 F).GalD F.cr false) : PrimRows3 (R.updS R.kap lam) F := by
  -- Reduce projections of the updated records before checking the row proofs.
  obtain ⟨R₂, _, _, _, _⟩ := R
  cases R₂
  dsimp only [RealDat3.updS, RealDat.upd6] at h2 h3 h4 ⊢
  obtain ⟨⟨hE, hR⟩, ⟨hW, hL⟩⟩ := h.hecke
  exact
  { heckeR := h.heckeR
    heckeL := h.heckeL
    hecke := ⟨⟨hE, ⟨hR.intw, hR.comm, hR.parts⟩⟩, ⟨hW, ⟨hL.intw, hL.comm, hL.parts⟩⟩⟩
    gUnit := h.gUnit
    gEquiv := h.gEquiv
    block := h.block
    rowTest := h.rowTest
    liftTest := h.liftTest
    liftTestB := h.liftTestB
    liftOnto := fun hW' hh => h.liftOnto hW' ⟨hh.intw, hh.comm, hh.parts⟩
    pos := h.pos
    posScal := ⟨h.posScal.1, h1⟩
    levE := h.levE
    h2P := h.h2P
    thmB := h2
    sumE := h.sumE
    unif := h.unif
    mLat := h.mLat
    levW := h.levW
    thmA := h3
    sumW := h.sumW
    scalConj := h4
    dimParts := h.dimParts }



theorem pins_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (hP : Pins R F cG)
    (hs : (R.updS R.kap lam).IsScal (reFace F Dc Sp Zsc)) : Pins ((R.updS R.kap lam).withErr e) (reFace F Dc Sp Zsc) cG := by
  let R' := R.updS R.kap lam
  let F' := reFace F Dc Sp Zsc
  have h := hP.char
  have hC : R'.WeakCharacterisation F' :=
    ⟨h.base, ⟨h.inert.tie, h.inert.onto, h.inert.hR, h.inert.hL, h.inert.SF⟩, h.fullY, h.fullX, h.fullP, hs,
      ⟨h.tup.mu_off, h.tup.mu_used, h.tup.mu_ne, h.tup.mu_conj, h.tup.mu_on⟩, h.phase, h.allPl⟩
  exact ⟨RealDat3.weak_characterisation_with_error (R := R') (F := F') hC e,
    reFace_keep R' F cG Dc Sp Zsc e hP.keep, hP.phs, hP.trSem⟩



theorem furtherRows_updatedScalars (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3) (h : UnusedChoiceStatements R F) :
    UnusedChoiceStatements (R.updS R.kap lam) F := ⟨h.ex, h.conj, h.levelW, h.integral⟩

end GlobalTheory.Mem.R3

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3



theorem reFace_scalars_errors_readings : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), (∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨ ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v)) → Pins R F cG → Holds R F → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.Wp3 i p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Z'.jW Z.jW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Dc Sp Zsc hl6 hP hH
  refine ⟨R.kap, R.lam3, reFaceErr R F Dc Sp Zsc, ?_⟩
  exact ⟨reFace_pins R F cG Dc Sp Zsc _ hl6 hP,
    ⟨reFace_prim R F Dc Sp Zsc _ hH.prim, further_face_statements_independent_of_error R F Dc Sp Zsc _ hH.aux, hH.ok, hH.sep⟩,
    reFace_errEq R F Dc Sp Zsc, rfl, fun _ _ _ _ _ => rfl,
    reFaceRead R F Dc Sp Zsc _ X0 Y, reFaceReadL R F Dc Sp Zsc _ X0 Y Z,
    rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.Mem.R3

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.base_level_frames_hermitian_ne_zero_off_place : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL), v ≠ A3.A.v0 → ∀ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, x ≠ 0 → Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT i A3.A.μ0) v x x ≠ 0 := by
  first | exact @GlobalTheory.Mem.R3.framesBase_majAt_ne_zero | exact GlobalTheory.Mem.R3.framesBase_majAt_ne_zero | (intros; apply GlobalTheory.Mem.R3.framesBase_majAt_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.exists_nonzero_rational_lift_mem_base_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ → ∃ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p ∧ x ≠ 0 := by
  first | exact @GlobalTheory.RatLift.exists_rat_lift_mem_part | exact GlobalTheory.RatLift.exists_rat_lift_mem_part | (intros; apply GlobalTheory.RatLift.exists_rat_lift_mem_part <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

theorem _root_.GlobalTheory.T.submodulePatchAtPrime_isLattice_locP : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsFullLattice E A → Submodule.IsFullLattice E B → Submodule.IsLattice E (patchAt P A B) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (patchAt P A B) = localization₂ Q.asIdeal (if Q = P then A else B) := by
  intro E _ _ _ n P A B hA hB
  first
  | exact GlobalTheory.InertExchange.patchAt_isLattice_locP P A B hA hB
  | exact GlobalTheory.InertExchange.patchAt_isLattice_locP P A B hA.toIsLattice hB.toIsLattice
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gelfandInvariantAction_smoothVectors_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (k : ℕ), ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), gelfH G (trRep σ P) k w = c • w := by
  first | exact @GlobalTheory.SmVec.GelfScalar.gelfH_scalar | exact GlobalTheory.SmVec.GelfScalar.gelfH_scalar | (intros; apply GlobalTheory.SmVec.GelfScalar.gelfH_scalar <;> assumption)
end
