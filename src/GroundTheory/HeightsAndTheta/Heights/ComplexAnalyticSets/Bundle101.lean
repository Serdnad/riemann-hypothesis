module

import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermPrimitivePresentation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartDehomog
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle009
public import GroundTheory.ArithmeticGeometry.EtaleCompletion.Bundle001
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle078
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle092
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle099
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

namespace RueckertNullstellensatz

variable {σ : Type} [Fintype σ] {w : σ → ℂ}

theorem exists_of_mem_holGermIdeal {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {φ : holGerms w}
    (hφ : φ ∈ holGermIdeal w p) :
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
      (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
  apply GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermPrimitivePresentation.exists_of_mem_holGermIdeal <;> assumption

theorem mem_holGermIdeal_of_eq {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ} (hp : ∀ i, AnalyticAt ℂ (p i) w)
    {h : Fin k → (σ → ℂ) → ℂ} (hh : ∀ i, AnalyticAt ℂ (h i) w) (φ : holGerms w)
    (hφ : (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)) :
    φ ∈ holGermIdeal w p := by
  have hsum : φ = ∑ i, (⟨(h i : Germ (𝓝 w) ℂ), h i, hh i, rfl⟩ : holGerms w) *
      ⟨(p i : Germ (𝓝 w) ℂ), p i, hp i, rfl⟩ := by
    apply Subtype.ext
    rw [hφ, show (fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) = ∑ i, h i * p i by
      funext z; simp [Finset.sum_apply]]

    rw [show ((∑ i, h i * p i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = Germ.coeRingHom (𝓝 w) (∑ i, h i * p i) from rfl,
    map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    rfl
  rw [hsum]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem proof (hNoeth : AnalyticGermsNoetherian.Statement) (hPrime : PrimeGermNullstellensatz.Statement) :
    RueckertNullstellensatz.Statement := by
  intro σ _ w k f g hf hg hvan
  let G : holGerms w := ⟨(g : Germ (𝓝 w) ℂ), g, hg, rfl⟩
  have : IsNoetherianRing (holGerms w) := hNoeth σ w

  have hrad : G ∈ (holGermIdeal w f).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hfP, hP⟩
    obtain ⟨r, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian P)
    choose p hp hps using fun j => (show ∃ q : (σ → ℂ) → ℂ, AnalyticAt ℂ q w ∧ (q : Germ (𝓝 w) ℂ) = s j from (s j).2)
    have hPeq : holGermIdeal w p = P := by
      rw [← hs, holGermIdeal]
      congr 1
      ext φ
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, Subtype.ext (hj.trans (hps j)).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j, (hps j).symm⟩
    have hfmem : ∀ i, (⟨(f i : Germ (𝓝 w) ℂ), f i, hf i, rfl⟩ : holGerms w) ∈ holGermIdeal w p := fun i =>
      hPeq ▸ hfP (Ideal.subset_span ⟨i, rfl⟩)
    choose c _ hc using fun i => exists_of_mem_holGermIdeal p (hfmem i)
    have hfev : ∀ᶠ z in 𝓝 w, ∀ i, f i z = ∑ j, c i j z * p j z :=
      eventually_all.2 fun i => Germ.coe_eq.1 (hc i)
    have hvanp : ∀ᶠ z in 𝓝 w, (∀ j, p j z = 0) → g z = 0 := by
      filter_upwards [hvan, hfev] with z hz hfz hpz
      exact hz fun i => by rw [hfz i]; simp [hpz]
    obtain ⟨h, hh, hgh⟩ := hPrime σ w r p g hp hg (hPeq ▸ hP) hvanp
    exact hPeq ▸ mem_holGermIdeal_of_eq hp hh G (Germ.coe_eq.2 hgh)

  obtain ⟨m, hm⟩ := hrad
  have hm' : G ^ (m + 1) ∈ holGermIdeal w f := by
    rw [pow_succ']
    exact Ideal.mul_mem_left _ G hm
  obtain ⟨h, hh, hgh⟩ := exists_of_mem_holGermIdeal f hm'
  refine ⟨m + 1, h, Nat.succ_pos m, hh, ?_⟩
  have hG : ((G ^ (m + 1) : holGerms w) : Germ (𝓝 w) ℂ) = ((g ^ (m + 1) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
    rw [Germ.coe_pow]
    rfl
  rw [hG] at hgh
  filter_upwards [Germ.coe_eq.1 hgh] with z hz
  simpa using hz

end RueckertNullstellensatz

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

theorem le_ringKrullDim_slice {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hJ : IsAffVariety J (e + 1)) (hH : IsHomogIdeal J) (hℓ : linForm ℓ ∉ J) :
    ((e : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) := by
  have hP := hJ.isPrime
  have hne : J ⊔ Ideal.span {linForm ℓ - 1} ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial (Fin n) ℂ) ∈ J :=
      GroundTheory.Heights₂.Heights.ChartDehomog.proof ℂ n J ℓ 1 0 hP hH hℓ (isHomogeneous_one _ _)
        (htop ▸ Submodule.mem_top)
    exact hP.ne_top ((Ideal.eq_top_iff_one J).mpr h1)
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  have hpP : p.IsPrime := hp.1.1
  have hJp : J ≤ p := le_sup_left.trans hp.1.2
  have hht := Ideal.map_height_le_one_of_mem_minimalPrimes hp
  have hpm : (p.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := ℂ)
    (p.map (Ideal.Quotient.mk J))
  rw [hJ.dim, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJp)] at hform
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hp.1.2)
      (Ideal.Quotient.factor_surjective hp.1.2)
  refine le_trans ?_ hle
  have key : ∀ a b : ℕ∞, a ≤ 1 → a + b = ((e + 1 : ℕ) : ℕ∞) → (e : ℕ∞) ≤ b := by
    intro a b ha hab
    induction b using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      induction a using ENat.recTopCoe with
      | top => simp at ha
      | coe k =>
        have h1 : k ≤ 1 := by exact_mod_cast ha
        have h2 : k + m = e + 1 := by exact_mod_cast hab
        exact_mod_cast (by omega : e ≤ m)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) = D at hform ⊢
  induction D using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.add_bot] at hform
    exact WithBot.bot_ne_coe hform
  | coe b =>
    have hab : (p.map (Ideal.Quotient.mk J)).height + b = ((e + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast hform
    exact_mod_cast key _ b hht hab

theorem exists_isChowForm_iff {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsProjPrime J) :
    (∃ F : MvPolynomial (Fin (e + 1) × Fin n) ℂ, IsChowForm J (e + 1) F) ↔
      IsAffVariety J (e + 1) :=
  ⟨fun ⟨F, hF⟩ => ⟨hJ.isPrime, GroundTheory.Heights₂.Heights.ConeDimOfChowForm.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J F hJ hF⟩,
    fun hA => GroundTheory.Heights₂.Heights.ChowFormExists.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J hJ hA.dim⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

noncomputable section

namespace RankDeficientFibreInfinite


open HolomorphicFibreInfinite in
theorem proof : RankDeficientFibreInfinite.Statement := by
  intro k d U f hU hUne hf hinj
  classical
  have hfa : AnalyticOnNhd ℂ f U :=
    GroundTheory.Heights₂.Heights.ImplicitCurve.analyticOnNhd_of_differentiableOn hU hf

  let Q : ℕ → Prop := fun m => ∃ t ∈ U, ∃ v : Fin m → Fin k → ℂ,
    LinearIndependent ℂ (fun j => fderiv ℂ f t (v j))
  have hQ0 : Q 0 := by
    obtain ⟨t, ht⟩ := hUne
    exact ⟨t, ht, Fin.elim0, linearIndependent_empty_type⟩
  have hspec : Q (Nat.findGreatest Q k) := Nat.findGreatest_spec (Nat.zero_le k) hQ0
  have hle : ∀ m, m ≤ k → Q m → m ≤ Nat.findGreatest Q k := fun m hmk hm => Nat.le_findGreatest hmk hm
  generalize Nat.findGreatest Q k = r at hspec hle
  obtain ⟨s, hs, v, hv⟩ := hspec
  have hmax : ∀ t ∈ U, ∀ u : Fin (r + 1) → Fin k → ℂ,
      ¬ LinearIndependent ℂ (fun j => fderiv ℂ f t (u j)) := by
    intro t ht u hu
    have hu' : LinearIndependent ℂ u :=
      LinearIndependent.of_comp (fderiv ℂ f t : (Fin k → ℂ) →ₗ[ℂ] (Fin d → ℂ)) hu
    have hcard : r + 1 ≤ k := by simpa using hu'.fintype_card_le_finrank
    have := hle (r + 1) hcard ⟨t, ht, u, hu⟩
    omega

  let T : (Fin r → ℂ) →ₗ[ℂ] (Fin d → ℂ) := Fintype.linearCombination ℂ (fun j => fderiv ℂ f s (v j))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext j
    exact Fintype.linearIndependent_iff.1 hv c (by simpa [T, Fintype.linearCombination_apply] using hc) j
  obtain ⟨Λ, hΛ⟩ := T.exists_leftInverse_of_injective hT
  have hΛv : ∀ j, Λ (fderiv ℂ f s (v j)) = Pi.single j 1 := by
    intro j
    have := congrArg (fun g => g (Pi.single j (1 : ℂ))) hΛ
    simpa [T, Fintype.linearCombination_apply_single] using this
  let Λc : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) := LinearMap.toContinuousLinearMap Λ
  have hΛc : ∀ y, Λc y = Λ y := fun y => rfl

  have hev : ∀ᶠ t in 𝓝 s, t ∈ U ∧ LinearIndependent ℂ (fun j => Λ (fderiv ℂ f t (v j))) := by
    have hUev : ∀ᶠ t in 𝓝 s, t ∈ U := hU.mem_nhds hs
    refine hUev.and ?_
    have hDcont : ContinuousAt (fderiv ℂ f) s := (hfa.fderiv s hs).continuousAt
    have hc : ContinuousAt (fun t => fun j => Λc (fderiv ℂ f t (v j))) s := by
      refine continuousAt_pi.2 fun j => ?_
      exact Λc.continuous.continuousAt.comp
        ((ContinuousLinearMap.apply ℂ (Fin d → ℂ) (v j)).continuous.continuousAt.comp hDcont)
    have h0 : LinearIndependent ℂ (fun j => Λc (fderiv ℂ f s (v j))) := by
      have : (fun j => Λc (fderiv ℂ f s (v j))) = ⇑(Pi.basisFun ℂ (Fin r)) := by
        funext j
        simp [hΛc, hΛv]
      rw [this]
      exact (Pi.basisFun ℂ (Fin r)).linearIndependent
    exact hc.eventually h0.eventually

  obtain ⟨w, hw, hw0⟩ : ∃ w, fderiv ℂ f s w = 0 ∧ w ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hinj s hs
    intro x y hxy
    exact sub_eq_zero.1 (hno _ (by rw [map_sub, hxy, sub_self]))
  have hw' : Λ (fderiv ℂ f s w) = 0 := by rw [hw, map_zero]

  let A' : ℂ × (Fin r → ℂ) →L[ℂ] (Fin k → ℂ) :=
    (ContinuousLinearMap.fst ℂ ℂ (Fin r → ℂ)).smulRight w +
      ∑ j, ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin r → ℂ))).smulRight (v j)
  have hA' : ∀ p : ℂ × (Fin r → ℂ), A' p = p.1 • w + ∑ j, p.2 j • v j := by
    intro p
    simp [A']
  have hLA : ∀ p : ℂ × (Fin r → ℂ), Λ (fderiv ℂ f s (A' p)) = p.2 := by
    intro p

    rw [hA', map_add (f := _), map_add (f := _), map_smul, map_smul, hw', smul_zero, zero_add, map_sum, map_sum]
    simp only [map_smul, hΛv]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  let H : ℂ × (Fin r → ℂ) → Fin r → ℂ := fun p => Λc (f (s + A' p))
  have hfs : AnalyticAt ℂ f s := hfa s hs
  have hHd : HasFDerivAt H (Λc.comp ((fderiv ℂ f s).comp A')) 0 := by
    have h1 : HasFDerivAt (fun p => s + A' p) A' (0 : ℂ × (Fin r → ℂ)) := A'.hasFDerivAt.const_add s
    have h2 : HasFDerivAt f (fderiv ℂ f s) (s + A' 0) := by
      simpa using hfs.differentiableAt.hasFDerivAt
    exact Λc.hasFDerivAt.comp _ (HasFDerivAt.comp (f := fun p => s + A' p) (0 : ℂ × (Fin r → ℂ)) h2 h1)
  have hHc : ContDiffAt ℂ 1 H 0 := by
    have hf1 : ContDiffAt ℂ 1 f (s + A' 0) := by simpa using hfs.contDiffAt
    exact Λc.contDiff.contDiffAt.comp _
      (ContDiffAt.comp (f := fun p => s + A' p) (0 : ℂ × (Fin r → ℂ)) hf1 (contDiff_const.add A'.contDiff).contDiffAt)
  have hinv : (fderiv ℂ H 0 ∘L ContinuousLinearMap.inr ℂ ℂ (Fin r → ℂ)).IsInvertible := by
    have : fderiv ℂ H 0 ∘L ContinuousLinearMap.inr ℂ ℂ (Fin r → ℂ) =
        ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
      rw [hHd.fderiv]
      refine ContinuousLinearMap.ext fun c => ?_
      simpa [hΛc] using hLA (0, c)
    rw [this]
    exact ⟨ContinuousLinearEquiv.refl ℂ _, rfl⟩

  have hψc := hHc.contDiffAt_implicitFunction one_ne_zero hinv
  set ψ := hHc.implicitFunction one_ne_zero hinv with hψ
  have hψ0 : ψ 0 = 0 := hHc.implicitFunction_apply_self one_ne_zero hinv
  have hψeq : ∀ᶠ z in 𝓝 (0 : ℂ), H (z, ψ z) = H 0 :=
    hHc.eventually_apply_implicitFunction one_ne_zero hinv
  have hψd : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ ψ z :=
    (hψc.eventually (by simp)).mono fun z hz => hz.differentiableAt one_ne_zero
  let P : ℂ → Fin k → ℂ := fun z => s + A' (z, ψ z)
  have hP0 : P 0 = s := by simp [P, hψ0, hA']
  have hPcont : ContinuousAt P 0 :=
    continuousAt_const.add (A'.continuous.continuousAt.comp (continuousAt_id.prodMk hψc.continuousAt))
  rw [← hP0] at hev
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1 (((hPcont.eventually hev).and hψeq).and hψd)
  have hPd : ∀ z ∈ ball (0 : ℂ) δ, DifferentiableAt ℂ P z := fun z hz =>
    (differentiableAt_const _).add (A'.differentiableAt.comp z (differentiableAt_id.prodMk (hball z hz).2))
  have hPU : ∀ z ∈ ball (0 : ℂ) δ, P z ∈ U := fun z hz => (hball z hz).1.1.1
  have hfd : ∀ z ∈ ball (0 : ℂ) δ, DifferentiableAt ℂ f (P z) := fun z hz =>
    (hf _ (hPU z hz)).differentiableAt (hU.mem_nhds (hPU z hz))
  have hgP : ∀ z ∈ ball (0 : ℂ) δ, Λc (f (P z)) = Λc (f s) := by
    intro z hz
    have := (hball z hz).1.2
    simpa [H, P] using this

  have hzero : Set.EqOn (fderiv ℂ (fun z => f (P z))) 0 (ball (0 : ℂ) δ) := by
    intro z hz
    have hcomp : fderiv ℂ (fun z => f (P z)) z = (fderiv ℂ f (P z)).comp (fderiv ℂ P z) :=
      fderiv_comp z (hfd z hz) (hPd z hz)
    have hloc : (fun z => Λc (f (P z))) =ᶠ[𝓝 z] fun _ => Λc (f s) :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) hgP
    have hg0 : fderiv ℂ (fun z => Λc (f (P z))) z = 0 := by
      rw [hloc.fderiv_eq]
      exact fderiv_const_apply _
    have hgc : fderiv ℂ (fun z => Λc (f (P z))) z = Λc.comp ((fderiv ℂ f (P z)).comp (fderiv ℂ P z)) := by
      rw [← hcomp]
      have h := fderiv_comp z Λc.differentiableAt ((hfd z hz).comp z (hPd z hz))
      rw [ContinuousLinearMap.fderiv] at h
      exact h
    have hx : Λ (fderiv ℂ f (P z) (fderiv ℂ P z 1)) = 0 := by
      have := congrArg (fun L => L 1) (hgc.symm.trans hg0)
      simpa [hΛc] using this
    have := kernel_eq_of_maximal (fderiv ℂ f (P z)) v Λ (hmax _ (hPU z hz)) (hball z hz).1.1.2 hx
    rw [hcomp]
    refine ContinuousLinearMap.ext_ring ?_
    simpa using this
  have hconst : ∀ z ∈ ball (0 : ℂ) δ, f (P z) = f s := by
    intro z hz
    have := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0 : ℂ) δ).isPreconnected
      (fun z hz => ((hfd z hz).comp z (hPd z hz)).differentiableWithinAt) hzero hz (mem_ball_self hδ)
    simpa [hP0] using this

  have hPinj : Function.Injective P := by
    intro z z' hzz
    have hψz : ψ z = ψ z' := by
      have h1 := hLA (z, ψ z)
      have h2 := hLA (z', ψ z')
      have : A' (z, ψ z) = A' (z', ψ z') := add_left_cancel hzz
      rw [this] at h1
      exact h1.symm.trans h2
    have : A' (z, ψ z) = A' (z', ψ z') := add_left_cancel hzz
    rw [hA', hA', hψz] at this
    have h3 : z • w = z' • w := add_right_cancel this
    exact smul_left_injective ℂ hw0 h3
  refine ⟨f s, ?_⟩
  have hinf : (ball (0 : ℂ) δ).Infinite := infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds 0 hδ)
  refine (hinf.image hPinj.injOn).mono ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨hPU z hz, hconst z hz⟩

end RankDeficientFibreInfinite

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem AdicCompletionRegular.proof : AdicCompletionRegular.Statement := by
  intro R _ hR M hM hreg
  let B := AdicCompletion M R
  have hfg : M.FG := Ideal.fg_of_isNoetherianRing M
  have : IsLocalRing B := adicCompletion_isLocalRing_of_isMaximal M hfg
  have : IsNoetherianRing B := GroundTheory.Arith.Etale.isNoetherianRing_adicCompletion R M
  have hmax : (M.map (algebraMap R B)).IsMaximal := AdicCompletion.isMaximal_map_of_le M M le_rfl hfg
  have hmB : M.map (algebraMap R B) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hmax
  have hc : (M.map (algebraMap R B)).comap (algebraMap R B) = M :=
    (hM.eq_of_le (Ideal.comap_ne_top _ hmax.ne_top) Ideal.le_comap_map).symm
  have hunit : ∀ s : M.primeCompl, IsUnit (algebraMap R B s) := by
    intro s
    by_contra h
    have hs : algebraMap R B s ∈ maximalIdeal B := h
    rw [← hmB] at hs
    have hs' := Ideal.mem_comap.mpr hs
    rw [hc] at hs'
    exact s.2 hs'
  let _ : Algebra (Localization.AtPrime M) B :=
    (IsLocalization.lift (M := M.primeCompl) (S := Localization.AtPrime M) hunit).toAlgebra
  have : IsScalarTower R (Localization.AtPrime M) B :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq hunit r).symm
  have : Module.Flat (Localization.AtPrime M) B :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime M) M.primeCompl B).mpr inferInstance
  have hmap : (maximalIdeal (Localization.AtPrime M)).map (algebraMap (Localization.AtPrime M) B) =
      maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq, hmB]
  have : IsLocalHom (algebraMap (Localization.AtPrime M) B) := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have h1 : algebraMap (Localization.AtPrime M) B a ∈ maximalIdeal B :=
      hmap ▸ Ideal.mem_map_of_mem _ (show a ∈ maximalIdeal (Localization.AtPrime M) from h)
    exact h1 ha
  exact GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal hmap

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimeGermFiniteProjection.exists_of_step (hStep : PrimeGermProjectionStep.Statement) :
    ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)), P.IsPrime →
      ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A := by
  have key : ∀ (n : ℕ) (σ : Type) [Fintype σ], Fintype.card σ = n → ∀ (w : σ → ℂ) (P : Ideal (holGerms w)),
      P.IsPrime → ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro σ _ hn w P hP
      by_cases h0 : P = ⊥
      · subst h0
        exact isFiniteGermProjection_bot w
      · exact hStep σ w P hP h0 fun τ _ hτ v Q hQ => ih _ (hn ▸ hτ) τ rfl v Q hQ
  intro σ _ w P hP
  exact key _ σ rfl w P hP

theorem PrimeGermFiniteProjection.proof (hStep : PrimeGermProjectionStep.Statement)
    (hFF : GermProjectionFunctionForm.Statement) : PrimeGermFiniteProjection.Statement := by
  intro σ _ w k p hp hP
  obtain ⟨d, A, hA⟩ := PrimeGermFiniteProjection.exists_of_step hStep σ w _ hP
  exact ⟨d, A, hFF σ w k p d A hp hA⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
