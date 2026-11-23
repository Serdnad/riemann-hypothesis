module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import GroundTheory.AutomorphicForms.GLnLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle250
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
public import GroundTheory.AutomorphicForms.GLnLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open ValuativeRel GroundTheory.Automorphic.GLnLocal
open scoped Pointwise

noncomputable section
namespace GlobalTheory.StabInt

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem mem_O_iff (x : w.adicCompletion E) : x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ w.adicCompletionIntegers E := by
  show _ ↔ Valued.v x ≤ 1
  simp only [Valuation.mem_integer_iff]
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 := (Valuation.Compatible.vle_iff_le (v := Valued.v) x 1)
  rw [map_one] at h1
  rw [← h1]
  exact Iff.symm (Valuation.vle_one_iff (valuation (w.adicCompletion E)))

theorem mem_integralGL_of_mem_KGL {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) :
    g ∈ integralGL (w.adicCompletion E) n := by
  obtain ⟨u, rfl⟩ := hg
  rw [mem_integralGL_iff]
  refine ⟨fun i j => (mem_O_iff _).2 (u i j).2, fun i j => (mem_O_iff _).2 ?_⟩
  rw [← map_inv]
  exact ((u⁻¹ : GL (Fin n) (Ov E w)) i j).2

theorem mem_KGL_of_mem_integralGL {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ integralGL (w.adicCompletion E) n) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  rw [mem_integralGL_iff] at hg
  have h1 : ∀ i j, g.1 i j ∈ Ov E w := fun i j => (mem_O_iff _).1 (hg.1 i j)
  have h2 : ∀ i j, g⁻¹.1 i j ∈ Ov E w := fun i j => (mem_O_iff _).1 (hg.2 i j)
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem mem_integralGL_of_conj (N t g : GL (Fin n) (w.adicCompletion E))
    (hN : N ∈ integralGL (w.adicCompletion E) n)
    (hsep : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1)
    (htN : t * N = N * t) (ht' : g⁻¹ * t * g ∈ integralGL (w.adicCompletion E) n)
    (hN' : g⁻¹ * N * g ∈ integralGL (w.adicCompletion E) n) : t ∈ integralGL (w.adicCompletion E) n := by
  set F := w.adicCompletion E
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField _ _
  haveI : IsUltrametricDist F :=
    inferInstanceAs (@IsUltrametricDist F (Valued.toNormedField F (WithZero (Multiplicative ℤ))).toDist)
  have hO : ∀ x : F, ‖x‖ ≤ 1 ↔ x ∈ 𝒪[F] := fun x =>
    (Valued.toNormedField.norm_le_one_iff).trans (mem_O_iff x).symm
  have hs : N.val.charpoly.Separable := by
    obtain ⟨u, v, -, -, h⟩ := hsep
    exact ⟨u, v, h⟩
  have hsep' : ∃ u v : Polynomial F, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.val.charpoly + v * Polynomial.derivative N.val.charpoly = 1 := by
    obtain ⟨u, v, hu, hv, h⟩ := hsep
    exact ⟨u, v, fun i => (hO _).2 ((mem_O_iff _).2 (hu i)), fun i => (hO _).2 ((mem_O_iff _).2 (hv i)), h⟩
  have hNi : ∀ i j, ‖N.val i j‖ ≤ 1 := fun i j => (hO _).2 ((mem_integralGL_iff F n).1 hN |>.1 i j)
  have hN'i : ∀ i j, ‖((g.val)⁻¹ * N.val * g.val) i j‖ ≤ 1 := by
    intro i j
    have := ((mem_integralGL_iff F n).1 hN').1 i j
    rw [← Matrix.coe_units_inv]
    exact (hO _).2 this
  obtain ⟨c, hcu, hcN, hy, hdet⟩ := GlobalTheory.IntConj.exists_commuting_mul_integral F n N.val g.val hNi hsep' g.isUnit hN'i
  set cU := hcu.unit with hcU
  have hcUv : (cU : Matrix (Fin n) (Fin n) F) = c := rfl
  have hcadj : c ∈ Algebra.adjoin F {N.val} := GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N.val c hs hcN
  have htNv : Commute t.val N.val := by
    show t.val * N.val = N.val * t.val
    have := congrArg Units.val htN
    simpa [Units.val_mul] using this
  have htc : Commute t.val c := Algebra.commute_of_mem_adjoin_singleton_of_commute hcadj htNv
  have htcU : t * cU = cU * t := Units.ext (by simpa [Units.val_mul, hcUv] using htc.eq)
  set yU := cU⁻¹ * g with hyU
  have hyv : (yU : Matrix (Fin n) (Fin n) F) = c⁻¹ * g.val := by
    rw [hyU, Units.val_mul, Matrix.coe_units_inv, hcUv]
  have hyO : yU ∈ integralGL F n := by
    rw [mem_integralGL_iff]
    have h1 : ∀ i j, (yU : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := fun i j => by
      rw [hyv]; exact (hO _).1 (hy i j)
    refine ⟨h1, fun i j => ?_⟩
    let y₀ : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨_, h1 i j⟩
    have hy₀ : (RingHom.mapMatrix (𝒪[F]).subtype) y₀ = (yU : Matrix (Fin n) (Fin n) F) := rfl
    have hadj : ∀ i j, (yU : Matrix (Fin n) (Fin n) F).adjugate i j ∈ 𝒪[F] := fun i j => by
      rw [← hy₀, ← RingHom.map_adjugate]
      exact (y₀.adjugate i j).2
    have hd : ‖Ring.inverse (yU : Matrix (Fin n) (Fin n) F).det‖ ≤ 1 := by
      rw [Ring.inverse_eq_inv', norm_inv, hyv, hdet, inv_one]
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ ((hO _).1 hd) (hadj i j)
  have e : t = yU * (g⁻¹ * t * g) * yU⁻¹ := by
    have e1 : cU⁻¹ * t * cU = t := by
      rw [mul_assoc, htcU, ← mul_assoc, inv_mul_cancel, one_mul]
    calc t = cU⁻¹ * t * cU := e1.symm
      _ = (cU⁻¹ * g) * (g⁻¹ * t * g) * (cU⁻¹ * g)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyO ht') (Subgroup.inv_mem _ hyO)

def pairGrp {G : Type} [Group G] (t N : G) (h : Commute t N) : Subgroup G where
  carrier := {x | ∃ a b : ℤ, x = t ^ a * N ^ b}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    rw [_root_.zpow_add, _root_.zpow_add, mul_assoc, mul_assoc, ← mul_assoc (N ^ b), (h.zpow_zpow c b).eq.symm, mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    rw [_root_.mul_inv_rev, _root_.zpow_neg, _root_.zpow_neg]
    exact (h.zpow_zpow a b).inv_inv.eq.symm

theorem mem_KGL_of_commute : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N t : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    t * N = N * t → IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) (w.adicCompletion E)))) →
    t ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro E _ _ n w N t hN hsep htN htc
  set F := w.adicCompletion E
  have hNO : N ∈ integralGL F n := mem_integralGL_of_mem_KGL hN
  let H0 := pairGrp t N htN
  have hC : IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F))) :=
    htc.mul (isCompact_integralGL F n)
  have hsub : (H0 : Set (GL (Fin n) F)) ⊆
      closure (Subgroup.zpowers t : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F)) := by
    rintro _ ⟨a, b, rfl⟩
    exact Set.mul_mem_mul (subset_closure (Subgroup.zpow_mem_zpowers t a)) (Subgroup.zpow_mem _ hNO b)
  have hH : IsCompact (H0.topologicalClosure : Set (GL (Fin n) F)) := by
    rw [Subgroup.topologicalClosure_coe]
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  obtain ⟨g, hg⟩ := exists_conj_le_integralGL F n hH
  have ht' := hg t (H0.le_topologicalClosure ⟨1, 0, by simp⟩)
  have hN' := hg N (H0.le_topologicalClosure ⟨0, 1, by simp⟩)
  exact mem_KGL_of_mem_integralGL (mem_integralGL_of_conj N t g hNO hsep htN ht' hN')

end GlobalTheory.StabInt
end
end

section

open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

open GlobalTheory.AutomorphicL2Unitary Set

namespace GlobalTheory.Orb

theorem orbInt_comp_conjEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (dh : Measure H)
    [dh.IsHaarMeasure] [dh.IsMulRightInvariant] (γ : H) (dt : Measure (cent γ)) [dt.IsHaarMeasure]
    [dt.IsMulRightInvariant] (g : H) (f : H → ℂ) :
    orbInt dh γ dt (f ∘ conjEquiv g) = orbInt dh γ dt f := by
  let r : Quot (cent γ) ≃ᵐ Quot (cent γ) :=
    { toFun := rmul _ g⁻¹
      invFun := rmul _ g
      left_inv := fun q => by rw [← rmul_mul, inv_mul_cancel, rmul_one]
      right_inv := fun q => by rw [← rmul_mul, mul_inv_cancel, rmul_one]
      measurable_toFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable
      measurable_invFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable }
  have hr : MeasurePreserving r (quotMeas _ dt dh) (quotMeas _ dt dh) :=
    measurePreserving_rmul_quotMeas (isClosed_cent γ) g⁻¹
  have h3 : descend (cent γ) (conjFn γ (f ∘ conjEquiv g)) = descend (cent γ) (conjFn γ f) ∘ r := funext fun q => by
    conv_rhs => rw [← Quotient.out_eq q]
    refine Eq.trans ?_ ((leftInv_conjFn le_rfl f).descend_mk (q.out * g⁻¹)).symm
    exact congrArg f (show g * _ * g⁻¹ = _ by group)
  rw [orbInt, quotInt, h3]
  exact hr.integral_comp' _

theorem orbitalIntegral_zero_of_derivative_along_conj_curve {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H) (hs : IsProperOrbit (cent s) s) (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (c : ℝ → H) (hc : Continuous c) (f f' : H → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hf' : Continuous f') (hf'c : HasCompactSupport f') (hd : ∀ (g : H) (u : ℝ), HasDerivAt (fun v : ℝ => f ((c v)⁻¹ * g * c v)) (f' ((c u)⁻¹ * g * c u)) u) : HasOrbInt μ s dt f' 0 := by
  have hO := hs.hasOrbInt (dh := μ) (dt := dt) hf' hf'c
  refine ⟨hO.1, ?_⟩
  change orbInt μ s dt f' = 0
  set ν := quotMeas (cent s) dt μ
  have hcf : ∀ (φ : H → ℂ) (g : H), Continuous φ → Continuous (conjFn s (φ ∘ conjEquiv g)) := fun φ g hφ =>
    hφ.comp ((conjEquiv g).continuous.comp (by fun_prop : Continuous fun x : H => x⁻¹ * s * x))
  have hmeas : ∀ (φ : H → ℂ) (g : H), Continuous φ →
      AEStronglyMeasurable (descend (cent s) (conjFn s (φ ∘ conjEquiv g))) ν := fun φ g hφ =>
    (measurable_descend (leftInv_conjFn le_rfl _) (hcf φ g hφ).measurable).aestronglyMeasurable
  let F : ℝ → Quot (cent s) → ℂ := fun v => descend (cent s) (conjFn s (f ∘ conjEquiv (c v)⁻¹))
  let F' : ℝ → Quot (cent s) → ℂ := fun v => descend (cent s) (conjFn s (f' ∘ conjEquiv (c v)⁻¹))
  have hconst : ∀ v, ∫ q, F v q ∂ν = orbInt μ s dt f := fun v =>
    orbInt_comp_conjEquiv μ s dt (c v)⁻¹ f

  obtain ⟨M, hM⟩ := hf'.bounded_above_of_compact_support hf'c
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  set K : Set H := (fun p : ℝ × H => c p.1 * p.2 * (c p.1)⁻¹) '' (Icc (-1) 1 ×ˢ tsupport f')
  have hK : IsCompact K := (isCompact_Icc.prod hf'c).image (by fun_prop)
  obtain ⟨χ, hχ1, -, hχc, hχI⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let χC : H → ℂ := fun x => ((χ x : ℝ) : ℂ)
  have hχC : Continuous χC := by fun_prop
  have hχCc : HasCompactSupport χC := HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hχc Complex.ofReal_zero
  have hχO := hs.hasOrbInt (dh := μ) (dt := dt) hχC hχCc
  let bound : Quot (cent s) → ℝ := fun q => M * ‖descend (cent s) (conjFn s χC) q‖
  have hbound : Integrable bound ν := hχO.1.norm.const_mul M
  have hb : ∀ q, ∀ v ∈ Icc (-1 : ℝ) 1, ‖F' v q‖ ≤ bound q := by
    intro q v hv
    change ‖f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * (c v)⁻¹⁻¹)‖ ≤ M * ‖χC (q.out⁻¹ * s * q.out)‖
    rw [inv_inv]
    set y := (c v)⁻¹ * (q.out⁻¹ * s * q.out) * c v
    by_cases hy : y ∈ tsupport f'
    · have hx : q.out⁻¹ * s * q.out ∈ K := ⟨(v, y), ⟨hv, hy⟩, by simp only [y]; group⟩
      have : χC (q.out⁻¹ * s * q.out) = 1 := by simp [χC, hχ1 hx]
      rw [this, norm_one, mul_one]
      exact hM y
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact mul_nonneg hM0 (norm_nonneg _)
  have hderiv : ∀ q, ∀ v ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun w => F w q) (F' v q) v := by
    intro q v _
    have e1 : (fun w => F w q) = fun w => f ((c w)⁻¹ * (q.out⁻¹ * s * q.out) * c w) := funext fun w => by
      change f ((c w)⁻¹ * (q.out⁻¹ * s * q.out) * (c w)⁻¹⁻¹) = _
      rw [inv_inv]
    have e2 : F' v q = f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * c v) := by
      change f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * (c v)⁻¹⁻¹) = _
      rw [inv_inv]
    rw [e1, e2]
    exact hd _ v
  have hF0 : Integrable (F 0) ν :=
    (hs.hasOrbInt (dh := μ) (dt := dt) (f := f ∘ conjEquiv (c 0)⁻¹) (hf.comp (conjEquiv _).continuous)
      (hfc.comp_homeomorph (conjEquiv (c 0)⁻¹).toHomeomorph)).1
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F') (x₀ := (0 : ℝ))
    (s := Icc (-1 : ℝ) 1) (bound := bound) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun v => hmeas f _ hf) hF0 (hmeas f' _ hf')
    (ae_of_all _ hb) hbound (ae_of_all _ hderiv)
  have h0 : HasDerivAt (fun v => ∫ q, F v q ∂ν) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  have := h0.unique hmain.2
  rw [← orbInt_comp_conjEquiv μ s dt (c 0)⁻¹ f']
  exact this.symm

theorem hasOrbInt_zero_of_hasDerivAt_conj : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H), IsProperOrbit (cent s) s → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (c : ℝ → H), Continuous c → ∀ (f f' : H → ℂ), Continuous f → HasCompactSupport f → Continuous f' → HasCompactSupport f' → (∀ (g : H) (u : ℝ), HasDerivAt (fun v : ℝ => f ((c v)⁻¹ * g * c v)) (f' ((c u)⁻¹ * g * c u)) u) → HasOrbInt μ s dt f' 0 :=
  fun _ _ _ _ _ _ _ _ _ μ _ _ s hs dt _ _ c hc f f' hf hfc hf' hf'c hd =>
    orbitalIntegral_zero_of_derivative_along_conj_curve μ s hs dt c hc f f' hf hfc hf' hf'c hd

end GlobalTheory.Orb
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

open Matrix

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    GlobalTheory.WeilM.hTens c JA (GlobalTheory.WeilM.dbl JB) x y =
      GlobalTheory.WeilM.hTens c JA JB x.toCols₁ y.toCols₁ - GlobalTheory.WeilM.hTens c JA JB x.toCols₂ y.toCols₂ := by
  unfold GlobalTheory.WeilM.hTens GlobalTheory.WeilM.dbl
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.toCols₁_apply, Matrix.toCols₂_apply, Matrix.zero_apply, Matrix.neg_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, sub_eq_add_neg]

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    GlobalTheory.WeilM.symp c ξ JA (GlobalTheory.WeilM.dbl JB) x y =
      GlobalTheory.WeilM.symp c ξ JA JB x.toCols₁ y.toCols₁ - GlobalTheory.WeilM.symp c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold GlobalTheory.WeilM.symp
  rw [hTens_dbl, mul_sub, map_sub]

theorem toCols₁_add' (x y : Matrix α (β ⊕ β) E) : (x + y).toCols₁ = x.toCols₁ + y.toCols₁ := rfl
theorem toCols₂_add' (x y : Matrix α (β ⊕ β) E) : (x + y).toCols₂ = x.toCols₂ + y.toCols₂ := rfl
theorem toCols₁_smul' (r : R) (x : Matrix α (β ⊕ β) E) : (r • x).toCols₁ = r • x.toCols₁ := rfl
theorem toCols₂_smul' (r : R) (x : Matrix α (β ⊕ β) E) : (r • x).toCols₂ = r • x.toCols₂ := rfl

variable [Invertible (2 : R)]

def dblD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA (GlobalTheory.WeilM.dbl JB)) (κ ⊕ κ) where
  e :=
    { toFun := fun x => (Sum.elim (d.e x.toCols₁).1 (d.e x.toCols₂).1, Sum.elim (d.e x.toCols₁).2 (-(d.e x.toCols₂).2))
      invFun := fun q => Matrix.fromCols (d.e.symm (q.1 ∘ Sum.inl, q.2 ∘ Sum.inl))
        (d.e.symm (q.1 ∘ Sum.inr, -(q.2 ∘ Sum.inr)))
      map_add' := fun x y => by
        ext (i | i) <;> simp [toCols₁_add', toCols₂_add'] <;> abel
      map_smul' := fun r x => by
        ext (i | i) <;> simp [toCols₁_smul', toCols₂_smul']
      left_inv := fun x => by
        conv_rhs => rw [← Matrix.fromCols_toCols x]
        beta_reduce
        congr 1
        · exact d.e.symm_apply_apply x.toCols₁
        · have h : (((Sum.elim (d.e x.toCols₁).1 (d.e x.toCols₂).1) ∘ Sum.inr,
              -((Sum.elim (d.e x.toCols₁).2 (-(d.e x.toCols₂).2)) ∘ Sum.inr)) : (κ → R) × (κ → R)) =
              d.e x.toCols₂ := Prod.ext rfl (funext fun i => neg_neg _)
          exact (congrArg d.e.symm h).trans (d.e.symm_apply_apply _)
      right_inv := fun q => by
        ext (i | i) <;> simp }
  form w w' := by
    rw [symp_dbl, d.form, d.form]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    ring

theorem isDblCoord_dblD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) : GlobalTheory.WeilM.IsDblCoord c ξ JA JB d (dblD c d) := by
  intro w₁ w₂
  simp [dblD]

end Gen

section Reindex

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem symp_submatrix (e : γ ≃ β) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α γ E) :
    GlobalTheory.WeilM.symp c ξ JA (JB.submatrix e e) x y =
      GlobalTheory.WeilM.symp c ξ JA JB (x.submatrix id e.symm) (y.submatrix id e.symm) := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← e.symm.sum_comp]
  simp

variable [Invertible (2 : R)]

def reD (e : γ ≃ β) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {J' : Matrix γ γ E} (h : J' = JB.submatrix e e)
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA J') κ where
  e := (Matrix.reindexLinearEquiv R E (Equiv.refl α) e).trans d.e
  form w w' := by
    rw [h, symp_submatrix, d.form]
    rfl

theorem reD_e (e : γ ≃ β) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {J' : Matrix γ γ E} (h : J' = JB.submatrix e e)
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (x : Matrix α γ E) :
    (reD c e h d).e x = d.e (x.submatrix id e.symm) := rfl

end Reindex

section Group

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

def reG (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e) :
    GlobalTheory.WeilM.UG c J →* GlobalTheory.WeilM.UG c J' :=
  ((Units.map (Matrix.reindexAlgEquiv E E e.symm).toAlgHom.toMonoidHom).comp (GlobalTheory.WeilM.UG c J).subtype).codRestrict
    (GlobalTheory.WeilM.UG c J') fun g => by
      have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
      show (((g : GL β E) : Matrix β β E).submatrix e e)ᵀ * J' * (((g : GL β E) : Matrix β β E).submatrix e e).map c = J'
      rw [h, Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

theorem reG_val (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e) (g : GlobalTheory.WeilM.UG c J) :
    ((reG c e h g : GL γ E) : Matrix γ γ E) = ((g : GL β E) : Matrix β β E).submatrix e e := rfl

end Group

section Host

variable {D : D7}

def JBd (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) :
    Matrix (Fin (GlobalTheory.Doubling.dblSp S).rank) (Fin (GlobalTheory.Doubling.dblSp S).rank) D.host.E :=
  (GlobalTheory.WeilM.dbl JB).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem incM_JBd (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) :
    incM D.host.F (JBd S JB) =
      (GlobalTheory.WeilM.dbl (incM D.host.F JB)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp [JBd, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.WeilM.dbl, h1, h2]

variable [Invertible (2 : AF D.host.F)]

def ddr {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F (JBd S JB)))
      (κ ⊕ κ) :=
  reD _ finSumFinEquiv.symm (incM_JBd S JB) (dblD _ co)

end Host

section HostGroup

variable {D : D7}

def omdOf {S T : HSp D} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {X : Type} [AddCommGroup X] [Module ℂ X]
    (omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (JBd S JB)) →* Module.End ℂ X) :
    GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) →* Module.End ℂ X :=
  omd₀.comp ((MonoidHom.inr _ _).comp (reG _ finSumFinEquiv.symm (incM_JBd S JB)))

end HostGroup

end GlobalTheory.DblSchr
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.higherCohomology_twist_bound_of_regular_section : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X) (hL : L.IsLB), (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ p : ℕ, 1 ≤ p → ∀ s : (lbPow L p).Sec, Mono (cutHom F (isLB_lbPow hL p) s) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.hdim_twist_pow_le_of_regular_section | exact GlobalTheory.hdim_twist_pow_le_of_regular_section | (intros; apply GlobalTheory.hdim_twist_pow_le_of_regular_section <;> assumption)
end
