module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdUniq
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter
open scoped Pointwise

def IsLCcOn {V : Type} [TopologicalSpace V] (U : Set V) (φ : V → ℝ) : Prop :=
  IsLocallyConstant φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

def HasCOSub (V : Type) [AddGroup V] [TopologicalSpace V] : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N

section Dens

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

def HasDens (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (φ : V → ℝ) (g : X → ℝ) :
    Prop :=
  Integrable φ μ ∧ Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

theorem HasDens.sub [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v - φ₂ v) (fun b => g₁ b - g₂ b) := by
  refine ⟨h₁.1.sub h₂.1, h₁.2.1.sub h₂.2.1, fun S hS => ?_⟩
  rw [integral_sub h₁.1.integrableOn h₂.1.integrableOn, h₁.2.2 S hS, h₂.2.2 S hS,
    integral_sub (h₁.2.1.continuousOn.integrableOn_compact hS)
      (h₂.2.1.continuousOn.integrableOn_compact hS)]

theorem HasDens.const_mul (c : ℝ) {φ : V → ℝ} {g : X → ℝ} (h : HasDens μ f ι ν φ g) :
    HasDens μ f ι ν (fun v => c * φ v) (fun b => c * g b) := by
  refine ⟨h.1.const_mul c, continuous_const.mul h.2.1, fun S hS => ?_⟩
  rw [integral_const_mul, integral_const_mul, h.2.2 S hS]

theorem nonneg_of_setIntegral [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] (D : X → ℝ) (hD : Continuous D)
    (h0 : ∀ S, IsCompact S → 0 ≤ ∫ b in S, D b ∂ν) (b0 : X) : 0 ≤ D b0 := by
  by_contra hneg
  rw [not_le] at hneg
  have hev : ∀ᶠ b in 𝓝 b0, D b < D b0 / 2 :=
    hD.continuousAt.eventually (gt_mem_nhds (by linarith))
  obtain ⟨S, hSn, hSsub, hSc⟩ := local_compact_nhds hev
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hlt : ν S ≠ ⊤ := hSc.measure_lt_top.ne
  have hpos' : 0 < ν.real S := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (ν.measure_pos_of_mem_nhds hSn).ne' hlt
  have hge := setIntegral_ge_of_const_le_real (c := -(D b0 / 2)) (f := fun b => -D b) hSm hlt
    (fun b hb => by
      have : D b < D b0 / 2 := hSsub hb
      linarith)
    (hD.neg.continuousOn.integrableOn_compact hSc)
  rw [integral_neg] at hge
  have := h0 S hSc
  nlinarith

theorem HasDens.le [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) (hle : ∀ v, φ₁ v ≤ φ₂ v) (b : X) :
    g₁ b ≤ g₂ b := by
  have h := h₂.sub h₁
  have := nonneg_of_setIntegral (ν := ν) _ h.2.1 (fun S hS => by
    rw [← h.2.2 S hS]
    exact integral_nonneg fun v => sub_nonneg.2 (hle v)) b
  linarith

end Dens

section Approx

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem isOpen_inf_iInf (Λ₀ : AddSubgroup V) (h₀o : IsOpen (Λ₀ : Set V)) {ι : Type}
    (t : Finset ι) (L : ι → AddSubgroup V) (hLo : ∀ i, IsOpen (L i : Set V)) :
    IsOpen ((Λ₀ ⊓ ⨅ i ∈ t, L i : AddSubgroup V) : Set V) := by
  rw [AddSubgroup.coe_inf]
  refine h₀o.inter ?_
  simp only [AddSubgroup.coe_iInf]
  exact isOpen_biInter_finset fun i _ => hLo i

theorem exists_sub_osc (hNA : HasCOSub V) {φ : V → ℝ} (hc : Continuous φ)
    (hs : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) (Λ₀ : AddSubgroup V)
    (h₀o : IsOpen (Λ₀ : Set V)) (h₀c : IsCompact (Λ₀ : Set V)) :
    ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧ Λ ≤ Λ₀ ∧
      ∀ x z, z ∈ Λ → |φ (x + z) - φ x| < ε := by
  have hN : ∀ x : V, {z : V | |φ (x + z) - φ x| < ε / 2} ∈ 𝓝 (0 : V) := by
    intro x
    have hcx : Continuous fun z : V => |φ (x + z) - φ x| :=
      ((hc.comp (continuous_const.add continuous_id)).sub continuous_const).abs
    have : IsOpen {z : V | |φ (x + z) - φ x| < ε / 2} := isOpen_lt hcx continuous_const
    exact this.mem_nhds (by simp; linarith)
  choose L hLo hLc hLN using fun x => hNA _ (hN x)
  have hcov : tsupport φ ⊆ ⋃ x : tsupport φ, {y : V | y - (x : V) ∈ L x} := by
    intro y hy
    exact mem_iUnion.2 ⟨⟨y, hy⟩, by simp [(L y).zero_mem]⟩
  have hopen : ∀ x : tsupport φ, IsOpen {y : V | y - (x : V) ∈ L x} := fun x =>
    (hLo x).preimage (continuous_id.sub continuous_const)
  obtain ⟨t, ht⟩ := hs.isCompact.elim_finite_subcover _ hopen hcov
  have ho := isOpen_inf_iInf Λ₀ h₀o t (fun x : tsupport φ => L (x : V)) (fun x => hLo _)
  refine ⟨Λ₀ ⊓ ⨅ x ∈ t, L (x : V), ho, ?_, inf_le_left, ?_⟩
  · exact h₀c.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ ho)
      (by rw [AddSubgroup.coe_inf]; exact inter_subset_left)
  · intro x z hz
    have hz' : ∀ i ∈ t, z ∈ L (i : V) := by
      intro i hi
      have := (inf_le_right : Λ₀ ⊓ ⨅ x ∈ t, L (x : V) ≤ _) hz
      exact (AddSubgroup.mem_iInf.1 this i |> AddSubgroup.mem_iInf.1) hi
    have key : ∀ i ∈ t, x - (i : V) ∈ L (i : V) → |φ (x + z) - φ x| < ε := by
      intro i hi hxi
      have h1 := hLN (i : V) hxi
      have h2 := hLN (i : V) (show x + z - (i : V) ∈ L (i : V) by
        have := (L (i : V)).add_mem hxi (hz' i hi)
        rwa [show x - (i : V) + z = x + z - (i : V) by abel] at this)
      simp only [mem_setOf_eq, add_sub_cancel] at h1 h2
      calc |φ (x + z) - φ x| ≤ |φ (x + z) - φ i| + |φ x - φ i| := by
            rw [abs_sub_comm (φ x)]; exact abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add h2 h1
        _ = ε := by ring
    by_cases hx : x ∈ tsupport φ
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
      exact key i hi hxi
    · by_cases hxz : x + z ∈ tsupport φ
      · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hxz)
        refine key i hi ?_
        have := (L (i : V)).sub_mem hxi (hz' i hi)
        rwa [show x + z - (i : V) - z = x - (i : V) by abel] at this
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxz]
        simpa using hε

end Approx

section Main

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]

def cosApx (Λ : AddSubgroup V) (φ : V → ℝ) (x : V) : ℝ := φ ((x : V ⧸ Λ).out)

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
theorem cosApx_sub_mem (Λ : AddSubgroup V) (x : V) : -((x : V ⧸ Λ).out) + x ∈ Λ :=
  QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (x : V ⧸ Λ))

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
theorem cosApx_eq (Λ : AddSubgroup V) (φ : V → ℝ) {x y : V} (h : -x + y ∈ Λ) :
    cosApx Λ φ y = cosApx Λ φ x :=
  congrArg (fun q : V ⧸ Λ => φ q.out) (QuotientAddGroup.eq.2 h).symm

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
theorem cosApx_lc (Λ : AddSubgroup V) (hΛ : IsOpen (Λ : Set V)) (φ : V → ℝ) :
    IsLocallyConstant (cosApx Λ φ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | -x + y ∈ Λ}, hΛ.preimage (continuous_const.add continuous_id), ?_,
    fun y hy => cosApx_eq Λ φ hy⟩
  show -x + x ∈ Λ
  rw [neg_add_cancel]
  exact Λ.zero_mem

theorem densApprox_lc (μ : Measure V) [IsFiniteMeasureOnCompacts μ] (f : V → Y) (ι : X → Y)
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] (U : Set V)
    (hU : IsOpen U) (hNA : HasCOSub V) : DensApprox (IsLCcOn U) μ f ι ν U := by
  apply PI.VolStabSW.densApprox_lc <;> assumption

end Main

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem lcscPolish_holds : LCSCPolish := fun Y _ _ _ _ => TopoPolish.polish_of_lcsc Y

theorem secCtblW_holds : SecCtblW := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  infer_instance

theorem scha_holds : SCHA := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  infer_instance

theorem measGrp_holds : MeasGrp := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact ⟨inferInstance, inferInstance⟩

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

def LinDens : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), Function.Surjective A →
      DensAll μ A id ν Set.univ

def ChangeVar : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)), μ.IsAddHaarMeasure →
    ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f → ∀ x0,
      Function.Surjective (fderiv ℝ f x0) →
      ∃ N, IsOpen N ∧ x0 ∈ N ∧ ∃ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), Function.Surjective A ∧
        ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ N →
          ∃ G : (Fin n → ℝ) → ℝ, Continuous G ∧ HasCompactSupport G ∧
            ∀ S : Set (Fin m → ℝ), IsCompact S →
              ∫ v in f ⁻¹' S, φ v ∂μ = ∫ v in A ⁻¹' S, G v ∂μ

theorem submLocal_of (h1 : LinDens) (h2 : ChangeVar) : SubmLocal := by
  intro n m μ ν hμ hν f hf x0 hx0
  obtain ⟨N, hN, hxN, A, hA, hG⟩ := h2 n m μ hμ f hf x0 hx0
  refine ⟨N, hN, hxN, fun φ hc hs hφ => ?_⟩
  obtain ⟨G, hGc, hGs, hGe⟩ := hG φ hc hs hφ
  obtain ⟨g, hgc, hg⟩ := h1 n m μ ν hμ hν A hA G hGc hGs (Set.subset_univ _)
  refine ⟨g, hgc, fun S hS => ?_⟩
  have := hg S hS
  simp only [Set.image_id] at this ⊢
  rw [hGe S hS, this]

theorem submDens_of_local (h : SubmLocal) : SubmDens := by
  intro n m μ ν hμ hν f hf
  exact densAll_of_local fun x hx => h n m μ ν hμ hν f hf x hx

theorem linDens_holds : LinDens := by
  intro n m μ ν hμ hν A hA φ hc hs _
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hA)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  let K := A.ker
  let lam : Measure K := Measure.addHaar
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  have hμT : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  obtain ⟨c, hsm⟩ : ∃ c : ENNReal, μ.map T = c • (ν.prod lam) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  let H : (Fin m → ℝ) × K → ℝ := fun w => φ (T.symm w)
  have hHc : Continuous H := hc.comp T.symm.continuous
  have hHs : HasCompactSupport H := hs.comp_homeomorph T.symm.toHomeomorph
  let s : Set K := Prod.snd '' tsupport H
  have hsc : IsCompact s := hHs.image continuous_snd
  let ψ : (Fin m → ℝ) → ℝ := fun y => ∫ k in s, H (y, k) ∂lam
  have hψc : Continuous ψ :=
    continuous_parametric_integral_of_continuous (f := fun y k => H (y, k)) hHc hsc
  have hψ : ∀ y, ∫ k, H (y, k) ∂lam = ψ y := by
    intro y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_).symm
    apply image_eq_zero_of_notMem_tsupport
    intro h'
    exact hk ⟨(y, k), h', rfl⟩
  refine ⟨fun y => c.toReal * ψ y, continuous_const.mul hψc, fun S hS => ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  simp only [Set.image_id]
  let Q : (Fin m → ℝ) × K → ℝ := (Prod.fst ⁻¹' S).indicator H
  have hQ : ∀ v, (A ⁻¹' S).indicator φ v = Q (T v) := by
    intro v
    simp only [Q, Set.indicator, H, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hQi : Integrable Q (ν.prod lam) :=
    (hHc.integrable_of_hasCompactSupport hHs).indicator (measurable_fst hSm)
  rw [← integral_indicator (hSm.preimage A.continuous.measurable)]
  simp_rw [hQ]
  have e2 : ∫ v, Q (T v) ∂μ = ∫ w, Q w ∂(μ.map T) := by
    rw [show (μ.map T) = μ.map T.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
    rfl
  rw [e2, hsm, integral_smul_measure, integral_prod _ hQi, smul_eq_mul,
    ← integral_indicator hSm, ← integral_const_mul]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · simp only [Q, Set.indicator, Set.mem_preimage, hy, if_true, ← hψ y]
  · simp [Q, Set.indicator, hy]

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

def CondAA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) ↔ t ∈ v.adicCompletionIntegers F

section Vol

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]

theorem vol_one_of_ann {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V)) (hA : ann χ (L : Set V) = L) :
    μ (L : Set V) = 1 := by
  classical
  have := hμ.1
  set c : ℝ := μ.real (L : Set V) with hc
  have hcl : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ, ← Set.piecewise_eq_indicator]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) y := by
    intro y
    rw [hΦ, transform_indicator μ χ hχ L hLo y, hA]
  have hfin : μ (L : Set V) < ⊤ := hLc.measure_lt_top
  have hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) :=
      funext hT
    rw [e, integrable_indicator_iff hLo.measurableSet]
    exact integrableOn_const hfin.ne
  have h0 := hμ.2 Φ hΦc hΦs hI 0
  have e1 : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = fun y => ((c : ℝ) : ℂ) * (Φ y * χ y 0) := by
    funext y
    rw [hT y]
    by_cases hy : y ∈ (L : Set V) <;> simp [hΦ, hy]
  rw [e1, integral_const_mul, hΦ, transform_indicator μ χ hχ L hLo 0, hA,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem), neg_zero,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem)] at h0
  have h1 : c * c = 1 := by exact_mod_cast h0
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c = 1 := by nlinarith
  rw [hc, measureReal_def, ENNReal.toReal_eq_one_iff] at hc1
  exact hc1

end Vol

section Ann

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ann_eq {V : Type} (ψ0 : Fv F v → ℂ) (B : V → V → Fv F v) (L : Set V)
    (hC : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) ↔
      t ∈ v.adicCompletionIntegers F)
    (hs : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y)
    (hD : {y | ∀ x ∈ L, B x y ∈ v.adicCompletionIntegers F} = L) :
    ann (fun x y => ψ0 (B x y)) L = L := by
  ext y
  constructor
  · intro hy
    rw [← hD]
    intro x hx
    rw [← hC]
    intro s hs'
    obtain ⟨x', hx', h⟩ := hs s hs' x hx
    rw [← h y]
    exact hy x' hx'
  · intro hy
    rw [← hD] at hy
    intro x hx
    have ht := (hC _).2 (hy x hx) 1 (one_mem _)
    simpa using ht

theorem ev_int (f : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) f ∈ (v.adicCompletionIntegers F) := by
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F) f
  refine hfin.eventually_cofinite_notMem.mono fun v hv => ?_
  simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : Valued.v ((f : v.adicCompletion F)) = v.valuation F f :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v f
  exact (this ▸ hv : Valued.v ((f : v.adicCompletion F)) ≤ 1)

theorem ev_int_all {ι : Type} [Finite ι] (f : ι → F) :
    ∀ᶠ v in cofinite, ∀ i, algebraMap F (Fv F v) (f i) ∈ (v.adicCompletionIntegers F) :=
  Filter.eventually_all.2 fun i => ev_int (f i)

end Ann

end VolAAW

end PI.VolStabS
end
end
