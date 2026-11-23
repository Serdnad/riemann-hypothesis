module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqZeroOfSetIntegral
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Aesop.Main
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFIn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFT
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

@[expose] public section

section

noncomputable section

namespace PI.VolStabS.DensGen

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}

theorem ae_fib (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X}
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (b : X) :
    ∀ᵐ v ∂(fib b), f' v = b := by
  have h0 := hfib.1 b
  rw [ae_iff]
  refine measure_mono_null (fun v hv => ?_) h0
  intro hmem
  exact hv (hι (by rw [← hff']; exact hmem.1))

theorem fib_set_nonneg [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hρ0 : ∀ v, 0 ≤ ρ v) (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  apply PI.AprimeInfW.DG.fib_set_nonneg <;> assumption

theorem fib_set [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  apply PI.AprimeInfW.DG.fib_set <;> assumption

theorem eq_zero_of_setIntegral [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℝ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  have key : ∀ E : X → ℝ, ContinuousOn E W →
      (∀ S, IsCompact S → S ⊆ W → ∫ b in S, E b ∂ν = 0) → ¬ 0 < E b0 := by
    intro E hE h0E hpos
    have hca : ContinuousAt E b0 := hE.continuousAt hW
    have hnhd : E ⁻¹' Set.Ioi (E b0 / 2) ∈ 𝓝 b0 := hca.preimage_mem_nhds (Ioi_mem_nhds (by linarith))
    obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (Filter.inter_mem hnhd hW)
    have hKW : K ⊆ W := fun x hx => (hKsub hx).2
    have hpos' : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
    have hfin : ν K < ⊤ := hKc.measure_lt_top
    have hint : IntegrableOn E K ν := (hE.mono hKW).integrableOn_compact hKc
    have hconst : IntegrableOn (fun _ => E b0 / 2) K ν := by
      first
        | exact integrableOn_const hfin.ne
        | exact integrableOn_const.2 (Or.inr hfin)
        | exact (integrableOn_const (C := E b0 / 2)).2 (Or.inr hfin)
    have hmono : ∫ b in K, E b0 / 2 ∂ν ≤ ∫ b in K, E b ∂ν :=
      setIntegral_mono_on hconst hint hKc.measurableSet (fun x hx => (hKsub hx).1.le)
    rw [h0E K hKc hKW, setIntegral_const] at hmono
    have hr : 0 < (ν K).toReal := ENNReal.toReal_pos hpos'.ne' hfin.ne
    first
      | (rw [smul_eq_mul] at hmono; nlinarith)
      | (simp only [Measure.real, smul_eq_mul] at hmono; nlinarith)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine key (fun b => -D b) hD.neg (fun S hS hSW => ?_) (by simpa using hneg)
    rw [integral_neg, h0 S hS hSW, neg_zero]
  · exact key D hD h0 hpos

theorem eq_zero_of_setIntegral_c [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℂ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  have hre := eq_zero_of_setIntegral (ν := ν) (fun b => (D b).re) W b0 hW
    (Complex.continuous_re.comp_continuousOn hD) (fun S hS hSW => by
      have hint : IntegrableOn D S ν := (hD.mono hSW).integrableOn_compact hS
      have h1 := integral_re hint
      simp only [RCLike.re_to_complex] at h1
      rw [h1, h0 S hS hSW, Complex.zero_re])
  have him := eq_zero_of_setIntegral (ν := ν) (fun b => (D b).im) W b0 hW
    (Complex.continuous_im.comp_continuousOn hD) (fun S hS hSW => by
      have hint : IntegrableOn D S ν := (hD.mono hSW).integrableOn_compact hS
      have h1 := integral_im hint
      simp only [RCLike.im_to_complex] at h1
      rw [h1, h0 S hS hSW, Complex.zero_im])
  exact Complex.ext hre him

theorem cut_props {f' : V → X} (hf' : Continuous f') (q : V → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) (ψ : X → ℝ) (hψ : Continuous ψ) (C : Set X) (hC : IsClosed C)
    (hψC : ∀ x, ψ x ≠ 0 → x ∈ C) (hCU : ∀ v, f' v ∈ C → v ∈ U) :
    Continuous (fun v => q v * ψ (f' v)) ∧ HasCompactSupport (fun v => q v * ψ (f' v)) ∧
      tsupport (fun v => q v * ψ (f' v)) ⊆ U := by
  refine ⟨hq.mul (hψ.comp hf'), hqs.mul_right, ?_⟩
  have hcl : IsClosed (f' ⁻¹' C) := hC.preimage hf'
  have hsub : Function.support (fun v => q v * ψ (f' v)) ⊆ f' ⁻¹' C := by
    intro v hv
    exact hψC _ (right_ne_zero_of_mul hv)
  exact (closure_minimal hsub hcl).trans (fun v hv => hCU v hv)

theorem densGen [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts μ] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {B' N : Set X} (hfib : IsFibreFamily μ f ι U ν B fib)
    {f' : V → X} (hf' : Continuous f') (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (hNU : ∀ v, f' v ∈ N → v ∈ U)
    {Φ : V → ℂ} (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ) {g : X → ℂ}
    (hg : IsContDensityOn μ f ι ν B' Φ g) {b0 : X} (hB : B ∈ 𝓝 b0) (hB' : B' ∈ 𝓝 b0)
    (hN : N ∈ 𝓝 b0) :
    g b0 = ∫ v, Φ v ∂(fib b0) := by
  obtain ⟨C, hCn, hCsub, hCc⟩ := local_compact_nhds (inter_mem (inter_mem hB hB') hN)
  obtain ⟨K, hKn, hKsub, hKc⟩ := local_compact_nhds (interior_mem_nhds.2 hCn)
  obtain ⟨ψ, hψK, hψ0, -, -⟩ := exists_continuous_one_zero_of_isCompact hKc
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.2 hKsub)
  have hKC : K ⊆ C := hKsub.trans interior_subset
  have hKB : K ⊆ B := fun b hb => (hCsub (hKC hb)).1.1
  have hKB' : K ⊆ B' := fun b hb => (hCsub (hKC hb)).1.2
  have hψC : ∀ x, ψ x ≠ 0 → x ∈ C := by
    intro x hx
    by_contra hxC
    exact hx (by simpa using hψ0 (fun hxi => hxC (interior_subset hxi)))
  have hCU : ∀ v, f' v ∈ C → v ∈ U := fun v hv => hNU v (hCsub hv).2
  obtain ⟨hrc, hrs, hrU⟩ := cut_props hf' (fun v => (Φ v).re) (Complex.continuous_re.comp hΦc)
    (hΦs.comp_left (g := Complex.re) Complex.zero_re) ψ ψ.continuous C hCc.isClosed hψC hCU
  obtain ⟨hic, his, hiU⟩ := cut_props hf' (fun v => (Φ v).im) (Complex.continuous_im.comp hΦc)
    (hΦs.comp_left (g := Complex.im) Complex.zero_im) ψ ψ.continuous C hCc.isClosed hψC hCU
  have hr3 := hfib.2.2 _ hrc hrs hrU
  have hi3 := hfib.2.2 _ hic his hiU
  have hcut : ∀ v, f' v ∈ K → Φ v = (((Φ v).re * ψ (f' v) : ℝ) : ℂ) +
      (((Φ v).im * ψ (f' v) : ℝ) : ℂ) * Complex.I := by
    intro v hv
    have h1 : ψ (f' v) = 1 := by simpa using hψK hv
    rw [h1, mul_one, mul_one]
    exact (Complex.re_add_im _).symm
  obtain ⟨H, hH⟩ : ∃ H : X → ℂ, H = fun b => ((∫ v, (Φ v).re * ψ (f' v) ∂(fib b) : ℝ) : ℂ) +
      ((∫ v, (Φ v).im * ψ (f' v) ∂(fib b) : ℝ) : ℂ) * Complex.I := ⟨_, rfl⟩
  have hHc : ContinuousOn H K := by
    rw [hH]
    exact (Complex.continuous_ofReal.comp_continuousOn (hr3.2.mono hKB)).add
      ((Complex.continuous_ofReal.comp_continuousOn (hi3.2.mono hKB)).mul continuousOn_const)

  have hA : ∀ b ∈ K, ∫ v, Φ v ∂(fib b) = H b := by
    intro b hb
    rw [hH]
    have hIr := hr3.1 b (hKB hb)
    have hIi := hi3.1 b (hKB hb)
    rw [integral_congr_ae (g := fun v => (((Φ v).re * ψ (f' v) : ℝ) : ℂ) +
      (((Φ v).im * ψ (f' v) : ℝ) : ℂ) * Complex.I) ?_]
    · rw [integral_add hIr.ofReal (hIi.ofReal.mul_const _), integral_mul_const, integral_complex_ofReal,
        integral_complex_ofReal]
    · filter_upwards [ae_fib hfib hff' hι b] with v hv
      exact hcut v (hv ▸ hb)

  have hBint : ∀ S, IsCompact S → S ⊆ K → ∫ b in S, g b ∂ν = ∫ b in S, H b ∂ν := by
    intro S hS hSK
    have hAm : MeasurableSet (f' ⁻¹' S) := (hS.isClosed.preimage hf').measurableSet
    have hpre : f ⁻¹' (ι '' S) = f' ⁻¹' S := by
      ext v
      simp [hff', hι.mem_set_image]
    rw [← hg.2 S hS (hSK.trans hKB'), hpre,
      setIntegral_congr_fun hAm (fun v hv => hcut v (hSK hv)),
      integral_add (hrc.integrable_of_hasCompactSupport hrs).ofReal.integrableOn.integrable
        ((hic.integrable_of_hasCompactSupport his).ofReal.mul_const _).integrableOn.integrable,
      integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      fib_set hfib hf' hff' hι _ hrc hrs hrU S hS (hSK.trans hKB),
      fib_set hfib hf' hff' hι _ hic his hiU S hS (hSK.trans hKB), hH,
      integral_add ((hr3.2.mono (hSK.trans hKB)).integrableOn_compact hS).integrable.ofReal
        (((hi3.2.mono (hSK.trans hKB)).integrableOn_compact hS).integrable.ofReal.mul_const _),
      integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]
  have hD := eq_zero_of_setIntegral_c (ν := ν) (fun b => g b - H b) K b0 hKn
    ((hg.1.mono hKB').sub hHc) (fun S hS hSK => by
      rw [integral_sub ((hg.1.mono (hSK.trans hKB')).integrableOn_compact hS)
        ((hHc.mono hSK).integrableOn_compact hS), hBint S hS hSK, sub_self])
  rw [hA b0 (mem_of_mem_nhds hKn)]
  exact sub_eq_zero.1 hD

end PI.VolStabS.DensGen
end
end

section

namespace PI.VolStabS

theorem fFCount_holds : FFCount := fFCount_of_inert FFHS.fFInert_holds

end PI.VolStabS
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct
open PI.AdicCompletionValuation

theorem exists_coord_pi {X : Type} [AddCommGroup X] [TopologicalSpace X] {k : ℕ}
    (e : X ≃ₜ (Fin k → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (κ : Type) [Fintype κ] :
    ∃ (n : ℕ) (e' : (κ → X) ≃ₜ (Fin n → ℝ)), ∀ x y, e' (x + y) = e' x + e' y := by
  classical
  let L : (κ → Fin k → ℝ) ≃L[ℝ] (Fin (Module.finrank ℝ (κ → Fin k → ℝ)) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ⟨Module.finrank ℝ (κ → Fin k → ℝ), (Homeomorph.piCongrRight fun _ => e).trans L.toHomeomorph, ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply, Homeomorph.piCongrRight_apply, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [← map_add (f := _)]
  congr 1
  funext i
  simp [he]

theorem exists_coord_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ (k : ℕ) (e : Ainf F ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  have hreal : ∀ v : NumberField.InfinitePlace F, v.IsReal := fun v => NumberField.IsTotallyReal.isReal v
  let e1 : Ainf F ≃ₜ (NumberField.InfinitePlace F → ℝ) :=
    Homeomorph.piCongrRight fun v =>
      (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal (hreal v)).toHomeomorph
  let L : (NumberField.InfinitePlace F → ℝ) ≃L[ℝ]
      (Fin (Module.finrank ℝ (NumberField.InfinitePlace F → ℝ)) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ⟨Module.finrank ℝ (NumberField.InfinitePlace F → ℝ), e1.trans L.toHomeomorph, ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [← map_add (f := _)]
  congr 1
  funext v
  have hx : e1 (x + y) v = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hreal v) (x v + y v) := rfl
  have hx1 : e1 x v = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hreal v) (x v) := rfl
  have hx2 : e1 y v = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hreal v) (y v) := rfl
  rw [Pi.add_apply, hx, hx1, hx2, map_add (f := _)]

theorem exists_coord_tens (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] :
    ∃ (k : ℕ) (e : Ainf F ⊗[F] E ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  obtain ⟨k, eA, heA⟩ := exists_coord_Ainf F
  let b : Module.Basis (Fin (Module.finrank F E)) F E := Module.finBasis F E
  let bR := Algebra.TensorProduct.basis (Ainf F) b
  let ℓ : (Ainf F ⊗[F] E) ≃ₗ[Ainf F] (Fin (Module.finrank F E) → Ainf F) := bR.equivFun
  have hc1 : Continuous ℓ := IsModuleTopology.continuous_of_linearMap ℓ.toLinearMap
  have hc2 : Continuous ℓ.symm := IsModuleTopology.continuous_of_linearMap ℓ.symm.toLinearMap
  let h1 : (Ainf F ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → Ainf F) :=
    { toEquiv := ℓ.toEquiv, continuous_toFun := hc1, continuous_invFun := hc2 }
  obtain ⟨n, e', he'⟩ := exists_coord_pi eA heA (Fin (Module.finrank F E))
  refine ⟨n, h1.trans e', ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply]
  rw [show h1 (x + y) = h1 x + h1 y from map_add ℓ x y, he']

theorem exists_coord_sub {X : Type} [AddCommGroup X] [TopologicalSpace X] {N : ℕ}
    (e : X ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (H : AddSubgroup X)
    (hH : IsClosed (H : Set X)) (hdiv : ∀ n : ℕ, 0 < n → ∀ x ∈ H, ∃ y ∈ H, n • y = x) :
    ∃ (m : ℕ) (eH : H ≃ₜ (Fin m → ℝ)), ∀ x y, eH (x + y) = eH x + eH y := by
  classical
  have e0 : e 0 = 0 := by simpa using he 0 0
  let eA : X →+ (Fin N → ℝ) := { toFun := e, map_zero' := e0, map_add' := he }
  have hcl : IsClosed (e '' (H : Set X)) := e.isClosed_image.mpr hH
  have hrat : ∀ x ∈ H, ∀ q : ℚ, (q : ℝ) • e x ∈ e '' (H : Set X) := by
    intro x hx q
    obtain ⟨y, hy, hyx⟩ := hdiv q.den q.pos x hx
    refine ⟨q.num • y, H.zsmul_mem hy _, ?_⟩
    have h1 : e (q.num • y) = q.num • e y := map_zsmul eA q.num y
    have h2 : (q.den : ℝ) • e y = e x := by
      rw [← hyx]
      have := map_nsmul eA q.den y
      simp only [eA, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      rw [this, Nat.cast_smul_eq_nsmul]
    rw [h1, ← h2, smul_smul, ← Int.cast_smul_eq_zsmul ℝ]
    congr 1
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [Rat.cast_def]
    field_simp
  have hreal : ∀ x ∈ H, ∀ r : ℝ, r • e x ∈ e '' (H : Set X) := by
    intro x hx r
    have hS : IsClosed {t : ℝ | t • e x ∈ e '' (H : Set X)} :=
      hcl.preimage (continuous_id.smul continuous_const)
    have hsub : Set.range (Rat.cast : ℚ → ℝ) ⊆ {t : ℝ | t • e x ∈ e '' (H : Set X)} := by
      rintro _ ⟨q, rfl⟩; exact hrat x hx q
    have := hS.closure_subset_iff.mpr hsub
    rw [Rat.denseRange_cast.closure_range] at this
    exact this (Set.mem_univ r)
  let V : Submodule ℝ (Fin N → ℝ) :=
    { carrier := e '' (H : Set X)
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, H.add_mem ha hb, he a b⟩
      zero_mem' := ⟨0, H.zero_mem, e0⟩
      smul_mem' := by
        rintro r _ ⟨a, ha, rfl⟩
        exact hreal a ha r }
  let L : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let eI : H ≃ₜ V := e.image (H : Set X)
  refine ⟨Module.finrank ℝ V, eI.trans L.toHomeomorph, ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [← map_add (f := _)]
  congr 1
  apply Subtype.ext
  show e ((x : X) + (y : X)) = e x + e y
  exact he x y

end PI.VolStabS
end
end
