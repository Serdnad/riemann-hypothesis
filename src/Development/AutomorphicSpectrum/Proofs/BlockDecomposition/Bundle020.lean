module

public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Colimit.Finiteness
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open TensorProduct

namespace GlobalTheory.CompanionTheory.EqCrit

theorem exists_fg_tmul_eq_zero {A : Type} [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    {Q : Type} [AddCommGroup Q] [Module A Q] (z : Q) (h : (1 : B) ⊗ₜ[A] z = 0) :
    ∃ (Q' : Submodule A Q) (hz : z ∈ Q'), Q'.FG ∧ (⟨z, hz⟩ : Q') ⊗ₜ[A] (1 : B) = 0 := by
  classical
  have h' : z ⊗ₜ[A] (1 : B) = 0 := by
    have := congrArg (TensorProduct.comm A B Q) h
    rwa [TensorProduct.comm_tmul, map_zero] at this
  let N0 : {N : Submodule A Q // N.FG} := ⟨Submodule.span A {z}, Submodule.fg_span_singleton z⟩
  have hz0 : z ∈ (N0 : Submodule A Q) := Submodule.mem_span_singleton_self z
  have he : (Module.fgSystem.equiv A Q).symm z =
      Module.DirectLimit.of A {N : Submodule A Q // N.FG} (fun i => ↥(i : Submodule A Q))
        (Module.fgSystem A Q) N0 ⟨z, hz0⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    have := congrArg (fun f => f ⟨z, hz0⟩) (Module.fgSystem.equiv_comp_of (R := A) (M := Q) N0)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply] at this
    exact this.symm
  have h2 : (TensorProduct.directLimitLeft (Module.fgSystem A Q) B)
      ((LinearMap.rTensor B ((Module.fgSystem.equiv A Q).symm : Q →ₗ[A] _)) (z ⊗ₜ[A] (1 : B))) = 0 := by
    rw [h', map_zero, map_zero]
  rw [LinearMap.rTensor_tmul, LinearEquiv.coe_coe, he, TensorProduct.directLimitLeft_tmul_of] at h2
  haveI : DirectedSystem (fun i : {N : Submodule A Q // N.FG} => TensorProduct A (↥(i : Submodule A Q)) B)
      (fun i j h => ⇑(LinearMap.rTensor B (Module.fgSystem A Q i j h))) :=
    DirectedSystem.rTensor A B (f := fun ⦃i j⦄ h => Module.fgSystem A Q i j h) inferInstance
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact h2
  refine ⟨(j : Submodule A Q), (show (N0 : Submodule A Q) ≤ j from hij) hz0, j.2, ?_⟩
  rw [LinearMap.rTensor_tmul] at hj
  exact hj

theorem exists_system {A : Type} [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    {Q : Type} [AddCommGroup Q] [Module A Q] (z : Q) (h : (1 : B) ⊗ₜ[A] z = 0) :
    ∃ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A),
      (∃ y : Fin n → B, ∀ t, ∑ j, a t j • y j = algebraMap A B (c t)) ∧
      ∀ (B₁ : Type) [CommRing B₁] [Algebra A B₁],
        (∃ y : Fin n → B₁, ∀ t, ∑ j, a t j • y j = algebraMap A B₁ (c t)) →
          (1 : B₁) ⊗ₜ[A] z = 0 := by
  classical
  obtain ⟨Q', hz, hfg, hzero⟩ := exists_fg_tmul_eq_zero B z h
  haveI : Module.Finite A Q' := Module.Finite.iff_fg.mpr hfg
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A Q'
  obtain ⟨w, hw⟩ := hπ ⟨z, hz⟩
  have hex := lTensor_exact B (LinearMap.exact_subtype_ker_map π) hπ
  have h1 : LinearMap.lTensor B π ((1 : B) ⊗ₜ[A] w) = 0 := by
    rw [LinearMap.lTensor_tmul, hw]
    have := congrArg (TensorProduct.comm A Q' B) hzero
    rwa [TensorProduct.comm_tmul, map_zero] at this
  obtain ⟨x, hx⟩ := (hex ((1 : B) ⊗ₜ[A] w)).mp h1
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  let e := S.equivFin
  let b : Fin S.card → B := fun t => (e.symm t : B × LinearMap.ker π).1
  let kk : Fin S.card → LinearMap.ker π := fun t => (e.symm t : B × LinearMap.ker π).2
  have hxsum : x = ∑ t, b t ⊗ₜ[A] kk t := by
    rw [hS, ← Finset.sum_coe_sort, ← Equiv.sum_comp e.symm]
  have hx' : ∑ t, b t ⊗ₜ[A] (kk t : Fin n → A) = (1 : B) ⊗ₜ[A] w := by

    rw [← hx, hxsum, map_sum]
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
  refine ⟨n, S.card, fun s t => (kk t : Fin n → A) s, w, ⟨b, fun s => ?_⟩, ?_⟩
  · have hvec := congrFun (congrArg (TensorProduct.piScalarRight A B B (Fin n)) hx') s

    simp only [map_sum, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Finset.sum_apply] at hvec
    rw [Algebra.algebraMap_eq_smul_one]
    exact hvec
  · intro B₁ _ _ hy
    obtain ⟨y, hy⟩ := hy
    have h2 : ∑ t, y t ⊗ₜ[A] (kk t : Fin n → A) = (1 : B₁) ⊗ₜ[A] w := by
      apply (TensorProduct.piScalarRight A B₁ B₁ (Fin n)).injective
      funext s

      simp only [map_sum, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Finset.sum_apply]
      rw [← Algebra.algebraMap_eq_smul_one]
      exact hy s
    have h3 := congrArg (LinearMap.lTensor B₁ (Q'.subtype ∘ₗ π)) h2
    have hk : ∀ t, π (kk t : Fin n → A) = 0 := fun t => LinearMap.mem_ker.mp (kk t).2

    simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.comp_apply, hk, hw, map_zero,
    TensorProduct.tmul_zero, Finset.sum_const_zero, Submodule.subtype_apply] at h3
    exact h3.symm

end GlobalTheory.CompanionTheory.EqCrit
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Shear

theorem lintegral_shear_eq : ∀ (V A : Type) [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V]
    [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V]
    (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant]
    [lam.IsAddRightInvariant] (j : A →+ V), Measurable j → ∀ f : V → A, Measurable f →
    (∀ v a, f (v + j a) = f v) → ∀ K : Set A, MeasurableSet K → lam K ≠ 0 → lam K ≠ ⊤ →
    ∀ ψ : V → ℝ≥0∞, Measurable ψ → ∫⁻ v, ψ (v + j (f v)) ∂μ = ∫⁻ v, ψ v ∂μ := by
  intro V A _ _ _ _ _ _ _ _ μ lam _ _ _ _ j hj f hf hfinv K hK hK0 hKtop ψ hψ
  classical
  have hind : Measurable (K.indicator (1 : A → ℝ≥0∞)) := measurable_one.indicator hK
  have hind_ne : ∀ a, K.indicator (1 : A → ℝ≥0∞) a ≠ ⊤ := fun a => by
    rw [Set.indicator_apply]
    split_ifs <;> simp
  have hfneg : ∀ v a, f (v + -j a) = f v := fun v a => by
    rw [← map_neg]
    exact hfinv v (-a)
  have sA : ∀ a, ∫⁻ v, ψ (v + j a + j (f v)) ∂μ = ∫⁻ v, ψ (v + j (f v)) ∂μ := fun a =>
    (lintegral_add_right_eq_self (μ := μ) (fun v => ψ (v + j a + j (f v))) (-(j a))).symm.trans
      (lintegral_congr fun v => by simp only [neg_add_cancel_right, hfneg])
  have sB : ∀ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂lam =
      ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂lam := fun v =>
    (lintegral_add_right_eq_self (μ := lam) (fun a => K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v))) (-(f v))).symm.trans
      (lintegral_congr fun a => by simp only [map_add (f := _), map_neg, add_assoc, neg_add_cancel, add_zero])
  have sC : ∀ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂μ = ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂μ :=
    fun a => (lintegral_add_right_eq_self (μ := μ) (fun v => K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a)) (-(j a))).symm.trans
      (lintegral_congr fun v => by simp only [neg_add_cancel_right, hfneg])
  have sD : ∀ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂lam = lam K * ψ v := fun v => by
    have hm : Measurable fun a => K.indicator (1 : A → ℝ≥0∞) (a + -f v) := hind.comp (measurable_add_const (-f v))
    rw [lintegral_mul_const _ hm, lintegral_add_right_eq_self (μ := lam) (K.indicator (1 : A → ℝ≥0∞)) (-f v),
      lintegral_indicator_one hK]
  have hm1 : Measurable fun p : A × V => K.indicator (1 : A → ℝ≥0∞) p.1 * ψ (p.2 + j p.1 + j (f p.2)) :=
    (hind.comp measurable_fst).mul
      (hψ.comp ((measurable_snd.add (hj.comp measurable_fst)).add (hj.comp (hf.comp measurable_snd))))
  have hm2 : Measurable fun p : V × A => K.indicator (1 : A → ℝ≥0∞) (p.2 + -f p.1) * ψ (p.1 + j p.2) :=
    (hind.comp (measurable_snd.add (hf.comp measurable_fst).neg)).mul
      (hψ.comp (measurable_fst.add (hj.comp measurable_snd)))
  have hm3 : Measurable fun p : A × V => K.indicator (1 : A → ℝ≥0∞) (p.1 + -f p.2) * ψ p.2 :=
    (hind.comp (measurable_fst.add (hf.comp measurable_snd).neg)).mul (hψ.comp measurable_snd)
  have key : lam K * ∫⁻ v, ψ (v + j (f v)) ∂μ = lam K * ∫⁻ v, ψ v ∂μ := by
    calc lam K * ∫⁻ v, ψ (v + j (f v)) ∂μ
        = ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ∫⁻ v, ψ (v + j a + j (f v)) ∂μ ∂lam := by
          simp_rw [sA]
          rw [lintegral_mul_const _ hind, lintegral_indicator_one hK]
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂μ ∂lam := by
          refine lintegral_congr fun a => ?_
          rw [lintegral_const_mul' _ _ (hind_ne a)]
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂lam ∂μ :=
          lintegral_lintegral_swap hm1.aemeasurable
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂lam ∂μ := lintegral_congr fun v => sB v
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂μ ∂lam :=
          lintegral_lintegral_swap hm2.aemeasurable
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂μ ∂lam := lintegral_congr fun a => sC a
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂lam ∂μ :=
          lintegral_lintegral_swap hm3.aemeasurable
      _ = ∫⁻ v, lam K * ψ v ∂μ := lintegral_congr fun v => sD v
      _ = lam K * ∫⁻ v, ψ v ∂μ := lintegral_const_mul' _ _ hKtop
  exact (ENNReal.mul_right_inj hK0 hKtop).mp key

end GlobalTheory.CompanionTheory.Shear
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem conj_haar_character :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (D : Set π.ker), MeasurableSet D → IsFundamentalDomain (Γ.subgroupOf π.ker) D ν → ν D ≠ 0 → ν D < ⊤ → ∃ δ : G₁ →* ℝ≥0, Measurable δ ∧ (∀ γ ∈ Γ₁, δ γ = 1) ∧ ∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = δ u • ν := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ _ hΓ ν _ D hDm hD hD0 hDtop
  classical
  have hKc : IsClosed (π.ker : Set P) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hKc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have hcont : ∀ g : P, Continuous (fun m : π.ker => MulAut.conjNormal g m) := by
    intro g
    apply continuous_induced_rng.2
    have h1 : (Subtype.val ∘ fun m : π.ker => MulAut.conjNormal g m) = fun m : π.ker => g * (m : P) * g⁻¹ := by
      funext m
      simp only [Function.comp_apply, MulAut.conjNormal_apply]
    rw [h1]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hsymm : ∀ g : P, ⇑(MulEquiv.symm (MulAut.conjNormal g : MulAut π.ker)) =
      fun m => MulAut.conjNormal g⁻¹ m := by
    intro g
    funext m
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    group
  have hex : ∀ u : G₁, ∃ c : ℝ≥0,
      Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = c • ν := by
    intro u
    haveI : (Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν).IsHaarMeasure :=
      MulEquiv.isHaarMeasure_map ν (MulAut.conjNormal (ι u) : MulAut π.ker) (hcont _)
        (by convert hcont (ι u)⁻¹ using 1; exact hsymm _)
    exact ⟨_, Measure.isMulLeftInvariant_eq_smul _ ν⟩
  choose a ha using hex
  have hcancel : ∀ b c : ℝ≥0, (b : ℝ≥0∞) * ν D = (c : ℝ≥0∞) * ν D → b = c := by
    intro b c h
    exact_mod_cast (ENNReal.mul_left_inj hD0 hDtop.ne).mp h
  have hpre : ∀ v (S : Set π.ker), MeasurableSet S →
      ν ((fun m : π.ker => MulAut.conjNormal (ι v) m) ⁻¹' S) = (a v : ℝ≥0∞) * ν S := by
    intro v S hS
    rw [← Measure.map_apply (hcont _).measurable hS, ha v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcomp : ∀ u v, (fun m : π.ker => MulAut.conjNormal (ι (u * v)) m) ⁻¹' D =
      (fun m : π.ker => MulAut.conjNormal (ι v) m) ⁻¹'
        ((fun m : π.ker => MulAut.conjNormal (ι u) m) ⁻¹' D) := by
    intro u v
    ext m
    simp only [Set.mem_preimage, map_mul, MulAut.mul_apply]
  have hmul : ∀ u v, a (u * v) = a u * a v := by
    intro u v
    apply hcancel
    rw [← hpre (u * v) D hDm, hcomp, hpre v _ ((hcont _).measurable hDm), hpre u D hDm,
      ENNReal.coe_mul]
    ring
  haveI : Countable (Γ.subgroupOf π.ker) := by
    have hinj : Function.Injective (fun x : Γ.subgroupOf π.ker =>
        (⟨((x : π.ker) : P), Subgroup.mem_subgroupOf.1 x.2⟩ : Γ)) := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subtype.mk.injEq] at h
      exact h
    exact hinj.countable
  haveI : MeasurableConstSMul (Γ.subgroupOf π.ker) π.ker :=
    ⟨fun c => by
      show Measurable (fun x : π.ker => (c : π.ker) * x)
      exact measurable_id'.const_mul _⟩
  haveI : SMulInvariantMeasure (Γ.subgroupOf π.ker) π.ker ν :=
    ⟨fun c s _ => by
      show ν ((fun x : π.ker => (c : π.ker) * x) ⁻¹' s) = ν s
      exact measure_preimage_mul ν _ s⟩
  have hΓ1 : ∀ γ ∈ Γ₁, a γ = 1 := by
    intro γ hγ
    have hg : ι γ ∈ Γ := hΓ γ hγ
    have hqmp : Measure.QuasiMeasurePreserving
        (fun m : π.ker => MulAut.conjNormal (ι γ) m) ν ν := by
      refine ⟨(hcont _).measurable.aemeasurable, ?_⟩
      rw [ha γ]
      intro s hs
      rw [Measure.smul_apply, hs, smul_zero]
    obtain ⟨e, he⟩ : ∃ e : Γ.subgroupOf π.ker → Γ.subgroupOf π.ker,
        ∀ s, ((e s : π.ker) : P) = (ι γ)⁻¹ * ((s : π.ker) : P) * ι γ := by
      refine ⟨fun s => ⟨⟨(ι γ)⁻¹ * ((s : π.ker) : P) * ι γ, ?_⟩, ?_⟩, fun s => rfl⟩
      · rw [MonoidHom.mem_ker]
        simp [MonoidHom.mem_ker.1 (s : π.ker).2]
      · exact Subgroup.mem_subgroupOf.2
          (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) (Subgroup.mem_subgroupOf.1 s.2)) hg)
    have hebij : Function.Bijective e := by
      constructor
      · intro s t hst
        have h1 := congrArg (fun x : Γ.subgroupOf π.ker => ((x : π.ker) : P)) hst
        simp only [he, mul_left_inj, mul_right_inj] at h1
        apply Subtype.ext
        apply Subtype.ext
        exact h1
      · intro t
        obtain ⟨s, hs⟩ : ∃ s : Γ.subgroupOf π.ker,
            ((s : π.ker) : P) = ι γ * ((t : π.ker) : P) * (ι γ)⁻¹ := by
          refine ⟨⟨⟨ι γ * ((t : π.ker) : P) * (ι γ)⁻¹, ?_⟩, ?_⟩, rfl⟩
          · rw [MonoidHom.mem_ker]
            simp [MonoidHom.mem_ker.1 (t : π.ker).2]
          · exact Subgroup.mem_subgroupOf.2
              (Γ.mul_mem (Γ.mul_mem hg (Subgroup.mem_subgroupOf.1 t.2)) (Γ.inv_mem hg))
        refine ⟨s, Subtype.ext (Subtype.ext ?_)⟩
        rw [he, hs]
        group
    have hsemi : ∀ s : Γ.subgroupOf π.ker, Function.Semiconj
        (fun m : π.ker => MulAut.conjNormal (ι γ) m) (fun x => e s • x) (fun x => s • x) := by
      intro s x
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, he]
      group
    have hfd := hD.preimage_of_equiv hqmp hebij hsemi
    have hmeq : ν D = ν ((fun m : π.ker => MulAut.conjNormal (ι γ) m) ⁻¹' D) :=
      hD.measure_eq hfd
    apply hcancel
    rw [← hpre γ D hDm, ← hmeq, ENNReal.coe_one, one_mul]
  have hFc : Continuous (fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) := by
    apply continuous_induced_rng.2
    have h1 : (Subtype.val ∘ fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) =
        fun p => ι p.1 * (p.2 : P) * (ι p.1)⁻¹ := by
      funext p
      simp only [Function.comp_apply, MulAut.conjNormal_apply]
    rw [h1]
    exact ((hι.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul
      (hι.comp continuous_fst).inv
  have hE : MeasurableSet ((fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) ⁻¹' D) :=
    hFc.measurable hDm
  have ha_eq : a = fun u =>
      (ν ((fun m : π.ker => MulAut.conjNormal (ι u) m) ⁻¹' D) / ν D).toNNReal := by
    funext u
    rw [hpre u D hDm, ENNReal.mul_div_cancel_right hD0 hDtop.ne, ENNReal.toNNReal_coe]
  have hmeas : Measurable a := by
    rw [ha_eq]
    exact ((measurable_measure_prodMk_left hE).div_const _).ennreal_toNNReal
  exact ⟨{ toFun := a, map_one' := hΓ1 1 Γ₁.one_mem, map_mul' := hmul }, hmeas, hΓ1,
    fun u => ha u⟩

end GlobalTheory.CompanionTheory.SplitExtLat
end

section

open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Growth

theorem lintegral_le_mul_of_encard_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (M : Set G) (hM : MeasurableSet M) (f : G → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (n : ℕ)
    (hn : ∀ x, Set.encard {γ : Γ | (γ : G) * x ∈ M} ≤ n) :
    ∫⁻ x in M, f x ∂μ ≤ n * ∫⁻ x in 𝓕, f x ∂μ := by
  have hmul : ∀ γ : Γ, Measurable fun x : G => (γ : G) * x := fun γ => measurable_const_mul _
  have hterm : ∀ (γ : Γ) (x : G), M.indicator f (γ • x) =
      f x * (M.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) := by
    intro γ x
    rw [Subgroup.smul_def, smul_eq_mul]
    by_cases hx : (γ : G) * x ∈ M
    · simp [Set.indicator_of_mem hx, hinv γ γ.2 x]
    · simp [Set.indicator_of_notMem hx]
  have hcount : ∀ x : G, ∑' γ : Γ, M.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) ≤ n := by
    intro x
    have h1 : (fun γ : Γ => M.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) =
        ({γ : Γ | (γ : G) * x ∈ M}).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext γ
      by_cases hx : (γ : G) * x ∈ M
      · simp [Set.indicator, hx]
      · simp [Set.indicator, hx]
    rw [h1, ← tsum_subtype, ENNReal.tsum_set_one]
    calc _ ≤ (((n : ℕ∞)) : ℝ≥0∞) := ENat.toENNReal_le.2 (hn x)
      _ = n := by simp
  calc ∫⁻ x in M, f x ∂μ = ∫⁻ x, M.indicator f x ∂μ := (lintegral_indicator hM f).symm
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, M.indicator f (γ • x) ∂μ := h𝓕.lintegral_eq_tsum'' _
    _ = ∫⁻ x in 𝓕, ∑' γ : Γ, M.indicator f (γ • x) ∂μ := by
        rw [lintegral_tsum]
        intro γ
        exact ((hf.indicator hM).comp (hmul γ)).aemeasurable
    _ ≤ ∫⁻ x in 𝓕, n * f x ∂μ := by
        refine lintegral_mono fun x => ?_
        simp only [hterm]
        rw [ENNReal.tsum_mul_left, mul_comm]
        exact mul_le_mul_left (hcount x) _
    _ = n * ∫⁻ x in 𝓕, f x ∂μ := by
        rw [lintegral_const_mul _ hf]

end GlobalTheory.CompanionTheory.Growth
end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Unfolding

theorem setLIntegral_le_mul_fundamentalDomain_diff {G : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (F S T : Set G) (hF : IsFundamentalDomain Γ F μ) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (h : G → ℝ≥0∞) (hh : Measurable h)
    (hinv : ∀ γ ∈ Γ, ∀ x, h (γ * x) = h x) (N : ℕ)
    (hN : ∀ x, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (hST : ∀ γ ∈ Γ, ∀ x, γ * x ∈ S → x ∉ T) :
    ∫⁻ x in S, h x ∂μ ≤ N * ∫⁻ x in F \ T, h x ∂μ := by
  have hmeas : ∀ γ : Γ, Measurable (fun x : G => S.indicator h (γ • x)) := fun γ =>
    (hh.indicator hS).comp (measurable_const_smul γ)
  have h1 : ∫⁻ x in S, h x ∂μ = ∑' γ : Γ, ∫⁻ x in F, S.indicator h (γ • x) ∂μ := by
    rw [← lintegral_indicator hS]
    exact hF.lintegral_eq_tsum'' _
  have hpt : ∀ x, ∑' γ : Γ, S.indicator h (γ • x) ≤ N * Tᶜ.indicator h x := by
    intro x
    by_cases hx : x ∈ T
    · have hz : ∀ γ : Γ, S.indicator h (γ • x) = 0 := fun γ => by
        apply Set.indicator_of_notMem
        intro hmem
        exact hST γ γ.2 x (by simpa [Subgroup.smul_def] using hmem) hx
      simp [hz]
    · have hrew : ∀ γ : Γ, S.indicator h (γ • x) =
          ({γ : Γ | (γ : G) * x ∈ S}).indicator (fun _ => h x) γ := fun γ => by
        by_cases hg : (γ : G) * x ∈ S
        · rw [Set.indicator_of_mem (s := {γ : Γ | (γ : G) * x ∈ S}) (by exact hg),
            Subgroup.smul_def, smul_eq_mul, Set.indicator_of_mem hg, hinv γ γ.2 x]
        · rw [Set.indicator_of_notMem (s := {γ : Γ | (γ : G) * x ∈ S}) (by exact hg),
            Subgroup.smul_def, smul_eq_mul, Set.indicator_of_notMem hg]
      simp_rw [hrew]
      rw [← tsum_subtype, ENNReal.tsum_set_const,
        Set.indicator_of_mem (show x ∈ Tᶜ from hx)]
      gcongr
      have hc := ENat.toENNReal_le.mpr (hN x)
      simpa using hc
  calc ∫⁻ x in S, h x ∂μ = ∑' γ : Γ, ∫⁻ x in F, S.indicator h (γ • x) ∂μ := h1
    _ = ∫⁻ x in F, ∑' γ : Γ, S.indicator h (γ • x) ∂μ :=
        (lintegral_tsum fun γ => (hmeas γ).aemeasurable).symm
    _ ≤ ∫⁻ x in F, (N : ℝ≥0∞) * Tᶜ.indicator h x ∂μ := lintegral_mono hpt
    _ = N * ∫⁻ x in F, Tᶜ.indicator h x ∂μ :=
        lintegral_const_mul _ (hh.indicator hT.compl)
    _ = N * ∫⁻ x in F \ T, h x ∂μ := by
        rw [setLIntegral_indicator hT.compl, Set.inter_comm, Set.diff_eq]

end GlobalTheory.CompanionTheory.Unfolding
end

section

namespace GlobalTheory.CompanionTheory.Congruence

open Matrix

theorem finite_quotient_span_pow (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] (ϖ : R) (m : ℕ) (hϖ : Irreducible ϖ) :
    Finite (R ⧸ Ideal.span {ϖ ^ m}) := by
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) :=
    (inferInstance : Finite (IsLocalRing.ResidueField R))
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) m

end GlobalTheory.CompanionTheory.Congruence
end
