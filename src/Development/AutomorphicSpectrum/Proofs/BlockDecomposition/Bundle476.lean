module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.CompletePartialOrder
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

open MeasureTheory
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.DualVectorFamily

theorem sum_mul_sq_le {κ : Type} (s : Finset κ) (p q : κ → ℝ≥0∞) (t : ℝ≥0∞) (h : ∀ l ∈ s, q l ^ 2 ≤ t) :
    (∑ l ∈ s, p l * q l) ^ 2 ≤ (∑ l ∈ s, p l) ^ 2 * t := by
  have hs : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hq : ∀ l ∈ s, q l ≤ t ^ (1 / 2 : ℝ) := by
    intro l hl
    have := h l hl
    rw [← hs] at this
    exact (ENNReal.pow_le_pow_left_iff (by norm_num)).1 this
  calc (∑ l ∈ s, p l * q l) ^ 2 ≤ ((∑ l ∈ s, p l) * t ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun l hl => by gcongr; exact hq l hl
    _ = (∑ l ∈ s, p l) ^ 2 * t := by rw [mul_pow, hs]

theorem abs_vecs (hKB : KerBasic) (hKL : KerLin) (hCB : CntBasic) (hVE : VecEx) (hVN : VecNorm)
    (hVI : VecInner) (hPt : PtEq) (X : Ctx) (th : X.G → X.G) (hth : Continuous th)
    (hcnt : ∀ (Ω : Set X.G) x, cnt X.Γ Ω (th x) = cnt X.Γ (th '' Ω) x)
    {ι : Type} [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (X.G → ℂ)) (T₁ T₂ : X.Hs ι →L[ℂ] X.Hs ι)
    (M : Matrix ι ι ℂ) (t₁ : ∀ i j, Tst (Φ₁ i j)) (t₂ : ∀ i j, Tst (Φ₂ i j))
    (o₁ : X.IsOp Φ₁ T₁) (o₂ : X.IsOp Φ₂ T₂) :
    ∃ k₁ k₂ : X.G → ι → X.Hs ι,
      (∀ i, Continuous (fun x => k₁ x i) ∧ Continuous fun x => k₂ x i) ∧
      (∀ x i (u : X.Hs ι), inner ℂ (k₁ x i) u = ∑ j, ∫ y, ker X.Γ (Φ₁ i j) x y * (u j : X.G → ℂ) y ∂X.ν) ∧
      (∀ x i (u : X.Hs ι), inner ℂ u (k₂ x i) =
        ∑ j, ∑ l, ∫ y, starRingEnd ℂ ((u j : X.G → ℂ) y) * ker X.Γ (Φ₂ j l) y (th x) * M l i ∂X.ν) ∧
      (∃ (C : ℝ≥0∞) (Ω : Set X.G), C ≠ ⊤ ∧ IsCompact Ω ∧ ∀ x i,
        ‖k₁ x i‖ₑ ^ 2 ≤ C * cnt X.Γ Ω x ∧ ‖k₂ x i‖ₑ ^ 2 ≤ C * cnt X.Γ Ω x) ∧
      (∀ (U : X.Hs ι →L[ℂ] X.Hs ι) (Φ : Matrix ι ι (X.G → ℂ)), (∀ i j, Tst (Φ i j)) →
        X.IsOp Φ (T₁ * U * T₂) → ∀ x,
          ker X.Γ (fun y => ∑ i, ∑ j, Φ i j y * M j i) x (th x) =
            ∑ i, inner ℂ (k₁ x i) (U (k₂ x i))) := by
  have tA : ∀ i j, Tst ((fun i j => adj (Φ₁ j i) : Matrix ι ι (X.G → ℂ)) i j) :=
    fun i j => (hKB X _ (t₁ j i)).2.2.2.1
  obtain ⟨k₁, c₁, v₁⟩ := hVE X ι (fun i j => adj (Φ₁ j i)) tA
  obtain ⟨k, c, v⟩ := hVE X ι Φ₂ t₂
  obtain ⟨C₁, Ω₁, C₁t, Ω₁c, n₁⟩ := hVN X ι (fun i j => adj (Φ₁ j i)) tA
  obtain ⟨C₂, Ω₂, C₂t, Ω₂c, n₂⟩ := hVN X ι Φ₂ t₂
  refine ⟨k₁, fun x i => ∑ l, M l i • k (th x) l, fun i => ⟨c₁ i, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ fun l _ => ((c l).comp hth).const_smul (M l i)
  · intro x i u
    exact (hVI X ι Φ₁ x i (k₁ x i) u t₁).2 (v₁ x i)
  · intro x i u
    rw [inner_sum]
    simp only [inner_smul_right, (hVI X ι Φ₂ (th x) _ (k (th x) _) u t₂).1 (v _ _), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const, mul_comm]
  · set P : ℝ≥0∞ := ∑ i, (∑ l, ‖M l i‖ₑ) ^ 2 with hP
    have Pt : P ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ =>
      ENNReal.pow_ne_top (ENNReal.sum_ne_top.2 fun l _ => eNorm_ne_top)
    refine ⟨C₁ + P * C₂, Ω₁ ∪ th '' Ω₂, ENNReal.add_ne_top.2 ⟨C₁t, ENNReal.mul_ne_top Pt C₂t⟩,
      Ω₁c.union (Ω₂c.image hth), fun x i => ⟨?_, ?_⟩⟩
    · calc ‖k₁ x i‖ₑ ^ 2 ≤ C₁ * cnt X.Γ Ω₁ x := n₁ x i _ (v₁ x i)
        _ ≤ (C₁ + P * C₂) * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
          gcongr
          · exact le_self_add
          · exact (hCB X).2.2.1 _ _ Set.subset_union_left x
    · have hb : ∀ l ∈ (Finset.univ : Finset ι), ‖k (th x) l‖ₑ ^ 2 ≤ C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
        intro l _
        calc ‖k (th x) l‖ₑ ^ 2 ≤ C₂ * cnt X.Γ Ω₂ (th x) := n₂ _ l _ (v _ l)
          _ = C₂ * cnt X.Γ (th '' Ω₂) x := by rw [hcnt]
          _ ≤ _ := by
            gcongr
            exact (hCB X).2.2.1 _ _ Set.subset_union_right x
      have hsum : ‖∑ l, M l i • k (th x) l‖ₑ ≤ ∑ l, ‖M l i‖ₑ * ‖k (th x) l‖ₑ := by
        refine (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [eNorm_smul]
      calc ‖∑ l, M l i • k (th x) l‖ₑ ^ 2 ≤ (∑ l, ‖M l i‖ₑ * ‖k (th x) l‖ₑ) ^ 2 := by gcongr
        _ ≤ (∑ l, ‖M l i‖ₑ) ^ 2 * (C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x) := sum_mul_sq_le _ _ _ _ hb
        _ ≤ P * (C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x) := by
          gcongr
          exact Finset.single_le_sum (f := fun i => (∑ l, ‖M l i‖ₑ) ^ 2) (fun _ _ => zero_le) (Finset.mem_univ i)
        _ = P * C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by rw [mul_assoc]
        _ ≤ (C₁ + P * C₂) * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
          gcongr
          exact le_add_self
  · intro U Φ tΦ oΦ x
    have hfun : (fun y => ∑ i, ∑ j, Φ i j y * M j i) =
        fun y => ∑ p : ι × ι, Φ p.1 p.2 y * M p.2 p.1 := by
      funext y
      rw [Fintype.sum_prod_type]
    rw [hfun, (hKL X (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1) fun p => tΦ _ _).2,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum, inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, inner_smul_right,
      hPt X ι Φ₁ Φ₂ Φ T₁ T₂ U t₁ t₂ tΦ o₁ o₂ oΦ x (th x) i l (k₁ x i) (k (th x) l) (v₁ x i) (v _ l),
      mul_comm]

theorem vecsEx_of : RatProper → KerBasic → KerLin → CntBasic → CntPair → VecEx → VecNorm → VecInner → PtEq →
    VecsEx := by
  intro hR hKB hKL hCB hCP hVE hVN hVI hPt E _ _ _ a b D ι _ Φ₁ Φ₂ T₁ T₂ M h₁ h₂ o₁ o₂
  open PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep in
  letI : MeasurableSpace (H E a b) := borelH E a b
  let X : Ctx := by
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E b
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E b
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E b
    haveI := (hR E a).2.1
    haveI := (hR E b).2.1
    haveI := D.haar.1
    haveI := D.haar.2.2.1
    haveI : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
    haveI : IsFiniteMeasureOnCompacts D.μ := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    exact { G := H E a b
            ms := borelH E a b
            bs := ⟨rfl⟩
            μ := D.μ
            haar := ⟨⟩
            Γ := ratH E a b
            cn := (((ratGL E a).prodMap (ratGL E b)).rangeRestrict_surjective).countable
            proper := by
              intro C hC
              have h1 := (hR E a).2.2 _ (hC.image continuous_fst)
              have h2 := (hR E b).2.2 _ (hC.image continuous_snd)
              refine ((h1.prod h2).image ((ratGL E a).prodMap (ratGL E b)).rangeRestrict).subset ?_
              rintro ⟨_, γ, rfl⟩ hγ
              exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
            F := D.F
            fd := D.fd }
  obtain ⟨k₁, k₂, c, r₁, r₂, n, d⟩ := abs_vecs hKB hKL hCB hVE hVN hVI hPt X th
    (hCP E a b).2.1 (hCP E a b).1 Φ₁ Φ₂ T₁ T₂ M h₁ h₂ o₁ o₂
  refine ⟨k₁, k₂, ⟨c, r₁, r₂, n, ?_⟩⟩
  intro U Φ hΦ hop x
  rw [(hCP E a b).2.2]
  exact d U Φ hΦ hop x

end GlobalTheory.CompanionTheory.DualVectorFamily

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FibParam

open Set Filter

theorem fibre_param_continuous : ∀ (V H Y P : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P] (μ : Measure V) (ν : Measure H) (f : V → Y) (ι : H → Y) (q : V → H) (U : Set V) (fam : H → Measure V), IsOpen U → Continuous q → Function.Injective ι → (∀ v, f v = ι (q v)) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fam → ∀ ψ : P × V → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, p.2 ∈ U) → Continuous (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ∧ HasCompactSupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ∧ ∀ z ∈ tsupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)), ∃ v, (z.1, v) ∈ tsupport ψ ∧ q v = z.2 := by
  intro V H Y P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν f ι q U fam hU hq hι hf h ψ hψ hψc hψU
  have hCc : IsCompact (tsupport ψ) := hψc
  have hC₂c : IsCompact (Prod.snd '' tsupport ψ) := hCc.image continuous_snd
  have hC₂U : Prod.snd '' tsupport ψ ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hψU x hx
  obtain ⟨ρ, hρ1, hρc, hρs, hρ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hC₂c hU hC₂U
  have hzero : ∀ p v, v ∉ Prod.snd '' tsupport ψ → ψ (p, v) = 0 := fun p v hv =>
    image_eq_zero_of_notMem_tsupport (fun hh => hv ⟨_, hh, rfl⟩)
  have hsec : ∀ p, (∀ b, Integrable (fun v => ψ (p, v)) (fam b)) ∧
      Continuous (fun b => ∫ v, ψ (p, v) ∂(fam b)) := by
    intro p
    have hgc : Continuous (fun v => ψ (p, v)) := hψ.comp (continuous_const.prodMk continuous_id)
    have hsub : Function.support (fun v => ψ (p, v)) ⊆ Prod.snd '' tsupport ψ :=
      fun v hv => by_contra fun hn => hv (hzero p v hn)
    have hts : tsupport (fun v => ψ (p, v)) ⊆ Prod.snd '' tsupport ψ :=
      closure_minimal hsub hC₂c.isClosed
    have hcs : HasCompactSupport (fun v => ψ (p, v)) :=
      hC₂c.of_isClosed_subset (isClosed_tsupport _) hts
    obtain ⟨i, c⟩ := h.2.2 _ hgc hcs (hts.trans hC₂U)
    exact ⟨fun b => i b (mem_univ b), continuousOn_univ.1 c⟩
  obtain ⟨iρ, cρ⟩ := h.2.2 ρ ρ.continuous hρc hρs
  have hRc : Continuous (fun b => ∫ v, ρ v ∂(fam b)) := continuousOn_univ.1 cρ
  have hR0 : ∀ b, 0 ≤ ∫ v, ρ v ∂(fam b) := fun b => integral_nonneg fun v => (hρ01 v).1
  have hdiff : ∀ (p p' : P) (e : ℝ) (b : H), 0 ≤ e →
      (∀ v ∈ Prod.snd '' tsupport ψ, |ψ (p, v) - ψ (p', v)| ≤ e) →
      |(∫ v, ψ (p, v) ∂(fam b)) - ∫ v, ψ (p', v) ∂(fam b)| ≤ e * ∫ v, ρ v ∂(fam b) := by
    intro p p' e b he hb
    rw [← integral_sub ((hsec p).1 b) ((hsec p').1 b), ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((iρ b (mem_univ b)).const_mul e) (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs]
    by_cases hv : v ∈ Prod.snd '' tsupport ψ
    · rw [hρ1 hv]
      simpa using hb v hv
    · rw [hzero p v hv, hzero p' v hv]
      simpa using mul_nonneg he (hρ01 v).1
  have hcont : Continuous (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) := by
    refine continuous_iff_continuousAt.2 ?_
    rintro ⟨p₀, b₀⟩
    refine Metric.continuousAt_iff'.2 fun ε hε => ?_
    set M : ℝ := (∫ v, ρ v ∂(fam b₀)) + 1 with hMdef
    have hM : 0 < M := by linarith [hR0 b₀]
    set e : ℝ := ε / (2 * M) with hedef
    have he : 0 < e := by positivity
    have ev1 : ∀ᶠ b in 𝓝 b₀, (∫ v, ρ v ∂(fam b)) < M :=
      (isOpen_lt hRc continuous_const).mem_nhds (by simp [hMdef])
    have ev2 : ∀ᶠ b in 𝓝 b₀,
        dist (∫ v, ψ (p₀, v) ∂(fam b)) (∫ v, ψ (p₀, v) ∂(fam b₀)) < ε / 2 :=
      Metric.continuousAt_iff'.1 (hsec p₀).2.continuousAt (ε / 2) (by positivity)
    have hK := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
      ((ContinuousMap.curry (⟨ψ, hψ⟩ : C(P × V, ℝ))).continuous.tendsto p₀)) _ hC₂c
    have ev3 := Metric.tendstoUniformlyOn_iff.1 hK e he
    filter_upwards [ev3.prod_nhds (ev1.and ev2)] with z hz
    obtain ⟨hz3, hz1, hz2⟩ := hz
    have hd := hdiff z.1 p₀ e z.2 he.le fun v hv => by
      have := hz3 v hv
      have h' : dist (ψ (p₀, v)) (ψ (z.1, v)) < e := this
      rw [Real.dist_eq, abs_sub_comm] at h'
      exact h'.le
    have hbound : e * (∫ v, ρ v ∂(fam z.2)) ≤ ε / 2 := by
      have h1 : e * M = ε / 2 := by
        rw [hedef]
        field_simp
      calc e * (∫ v, ρ v ∂(fam z.2)) ≤ e * M := mul_le_mul_of_nonneg_left hz1.le he.le
        _ = ε / 2 := h1
    rw [Real.dist_eq] at hz2 ⊢
    calc |(∫ v, ψ (z.1, v) ∂(fam z.2)) - ∫ v, ψ (p₀, v) ∂(fam b₀)|
        = |((∫ v, ψ (z.1, v) ∂(fam z.2)) - ∫ v, ψ (p₀, v) ∂(fam z.2)) +
            ((∫ v, ψ (p₀, v) ∂(fam z.2)) - ∫ v, ψ (p₀, v) ∂(fam b₀))| := by
          congr 1
          ring
      _ ≤ _ := abs_add_le _ _
      _ < ε := by linarith
  have hsupp : ∀ z : P × H, (∫ v, ψ (z.1, v) ∂(fam z.2)) ≠ 0 →
      ∃ v, ψ (z.1, v) ≠ 0 ∧ q v = z.2 := by
    intro z hz
    by_contra hn
    push_neg at hn
    apply hz
    have h1 : f ⁻¹' {ι z.2} ∩ U ∈ ae (fam z.2) := mem_ae_iff.2 (h.1 z.2)
    have h2 : (fun v => ψ (z.1, v)) =ᵐ[fam z.2] 0 := by
      filter_upwards [h1] with v hv
      have hqv : q v = z.2 := hι ((hf v).symm.trans hv.1)
      by_contra h0
      exact hn v h0 hqv
    exact (integral_congr_ae h2).trans (by simp)
  have hSc : IsCompact ((fun x : P × V => (x.1, q x.2)) '' tsupport ψ) :=
    hCc.image (continuous_fst.prodMk (hq.comp continuous_snd))
  have hts : tsupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ⊆
      (fun x : P × V => (x.1, q x.2)) '' tsupport ψ := by
    refine closure_minimal (fun z hz => ?_) hSc.isClosed
    obtain ⟨v, hv, hqv⟩ := hsupp z hz
    exact ⟨(z.1, v), subset_tsupport _ hv, Prod.ext rfl hqv⟩
  refine ⟨hcont, hSc.of_isClosed_subset (isClosed_tsupport _) hts, fun z hz => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hts hz
  exact ⟨x.2, hx, rfl⟩

end GlobalTheory.CompanionTheory.WeilSiegel.FibParam
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FibreMass

theorem fibre_mass_le_of_pushforward : ∀ (V K : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ [lam.IsOpenPosMeasure] [IsLocallyFiniteMeasure lam] (P : Set V), IsCompact P → IsOpen P → P ⊆ Z → ∀ c : ℝ≥0, (∀ S : Set K, MeasurableSet S → μ (P ∩ Q ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S) → ∀ s, m s P ≤ (c : ℝ≥0∞) := by
  intro V K _ _ _ _ _ _ _ _ μ lam Q Z m hQ hfam _ _ P hPc hPo hPZ c hc s
  classical
  obtain ⟨hconc, hdis, hcont⟩ := hfam
  have hPm : MeasurableSet P := hPo.measurableSet
  have hφc : Continuous (P.indicator (fun _ => (1 : ℝ))) :=
    IsClopen.continuous_indicator ⟨hPc.isClosed, hPo⟩ continuous_const
  have hφs : HasCompactSupport (P.indicator (fun _ => (1 : ℝ))) :=
    HasCompactSupport.intro hPc (fun x hx => by simp [hx])
  have hφt : tsupport (P.indicator (fun _ => (1 : ℝ))) ⊆ Z :=
    (closure_minimal Set.support_indicator_subset hPc.isClosed).trans hPZ
  obtain ⟨hint, hgc⟩ := hcont _ hφc hφs hφt
  have hfin : ∀ b, m b P < ∞ := by
    intro b
    have h2 : IntegrableOn (fun _ => (1 : ℝ)) P (m b) :=
      (integrable_indicator_iff hPm).1 (hint b (Set.mem_univ b))
    exact ((integrableOn_const_iff (by simp)).1 h2).resolve_left (by simp)
  have hgeq : ∀ b, ∫ v, P.indicator (fun _ => (1 : ℝ)) v ∂(m b) = (m b P).toReal := by
    intro b
    rw [integral_indicator hPm, setIntegral_const]
    simp [Measure.real]
  have hgcont : Continuous (fun b => (m b P).toReal) := by
    have h := continuousOn_univ.1 hgc
    simpa only [hgeq] using h
  by_contra hlt
  rw [not_le] at hlt
  have hcs : (c : ℝ) < (m s P).toReal := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (hfin s).ne).2 hlt
    simpa using h
  obtain ⟨d, hcd, hds⟩ := exists_between hcs
  obtain ⟨N, ⟨hsN, hNo⟩, hNfin⟩ := (lam.finiteAt_nhds s).exists_mem_basis (nhds_basis_opens s)
  have hWo : IsOpen ({b | d < (m b P).toReal} ∩ N) :=
    (isOpen_lt continuous_const hgcont).inter hNo
  have hWm : MeasurableSet ({b | d < (m b P).toReal} ∩ N) := hWo.measurableSet
  have hpos : lam ({b | d < (m b P).toReal} ∩ N) ≠ 0 :=
    (hWo.measure_pos lam ⟨s, hds, hsN⟩).ne'
  have hfinW : lam ({b | d < (m b P).toReal} ∩ N) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt hNfin).ne
  have hAm : MeasurableSet (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) :=
    hPm.inter (hQ.measurable hWm)
  have key : ∀ b, m b (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) =
      ({b | d < (m b P).toReal} ∩ N).indicator (fun b => m b P) b := by
    intro b
    have hcb := hconc b
    rw [← measure_inter_conull hcb]
    by_cases hb : b ∈ ({b | d < (m b P).toReal} ∩ N)
    · rw [Set.indicator_of_mem hb, ← measure_inter_conull (s := P) hcb]
      congr 1
      ext v
      constructor
      · rintro ⟨⟨hvP, _⟩, hvT⟩
        exact ⟨hvP, hvT⟩
      · rintro ⟨hvP, hvT⟩
        refine ⟨⟨hvP, ?_⟩, hvT⟩
        have hQv : Q v = b := hvT.1
        show Q v ∈ ({b | d < (m b P).toReal} ∩ N)
        rw [hQv]
        exact hb
    · rw [Set.indicator_of_notMem hb]
      have hE : (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) ∩ (Q ⁻¹' {id b} ∩ Z) = ∅ := by
        ext v
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hvW⟩, hvT⟩
        have hQv : Q v = b := hvT.1
        apply hb
        rw [← hQv]
        exact hvW
      rw [hE, measure_empty]
  have hlhs : ∫⁻ v in Z, (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)).indicator 1 v ∂μ =
      μ (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) := by
    rw [lintegral_indicator_one hAm, Measure.restrict_apply hAm,
      Set.inter_eq_left.2 (Set.inter_subset_left.trans hPZ)]
  have hrhs : ∫⁻ b, ∫⁻ v, (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)).indicator 1 v ∂(m b) ∂lam =
      ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam := by
    simp_rw [lintegral_indicator_one hAm, key]
    rw [lintegral_indicator hWm]
  have hmain : ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam ≤
      (c : ℝ≥0∞) * lam ({b | d < (m b P).toReal} ∩ N) := by
    rw [← hrhs, ← hdis _ (measurable_one.indicator hAm), hlhs]
    exact hc _ hWm
  have hlow : ENNReal.ofReal d * lam ({b | d < (m b P).toReal} ∩ N) ≤
      ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam := by
    calc ENNReal.ofReal d * lam ({b | d < (m b P).toReal} ∩ N)
        = ∫⁻ _ in ({b | d < (m b P).toReal} ∩ N), ENNReal.ofReal d ∂lam :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam :=
          setLIntegral_mono' hWm (fun b hb => ENNReal.ofReal_le_of_le_toReal hb.1.le)
  have hd0 : 0 ≤ d := (NNReal.coe_nonneg c).trans hcd.le
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinW) (hlow.trans hmain)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd0, ENNReal.coe_toReal] at h
  have hLpos : 0 < (lam ({b | d < (m b P).toReal} ∩ N)).toReal := ENNReal.toReal_pos hpos hfinW
  have h' : d ≤ (c : ℝ) := le_of_mul_le_mul_right h hLpos
  linarith

end GlobalTheory.CompanionTheory.WeilSiegel.FibreMass
end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CompactFix

theorem finiteDimensional_ker_sub_id {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) (hT : IsCompactOperator T) :
    FiniteDimensional ℂ (LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id)) := by
  set K : Submodule ℂ X := LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id) with hK
  have hfix : ∀ x ∈ K, T x = x := by
    intro x hx
    have : (T : X →ₗ[ℂ] X) x - x = 0 := by simpa [hK] using hx
    simpa [sub_eq_zero] using this
  have hclosed : IsClosed (K : Set X) := by
    have : (K : Set X) = {x | T x = x} := by
      ext x
      constructor
      · exact hfix x
      · intro h
        have h' : T x = x := h
        simp [hK, h']
    rw [this]
    exact isClosed_eq T.continuous continuous_id
  obtain ⟨C, hC, hCsub⟩ := hT
  have hpre : (T ⁻¹' C) ∈ nhds (0 : X) := hCsub
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hpre
  have hcomp : IsCompact (Metric.closedBall (0 : K) r) := by
    have hemb : Topology.IsClosedEmbedding (Subtype.val : K → X) := hclosed.isClosedEmbedding_subtypeVal
    rw [hemb.isCompact_iff]
    refine hC.of_isClosed_subset ?_ ?_
    · have : (Subtype.val '' Metric.closedBall (0 : K) r) = (K : Set X) ∩ Metric.closedBall 0 r := by
        ext x
        simp [Metric.mem_closedBall, dist_eq_norm, and_comm]
      rw [this]
      exact hclosed.inter Metric.isClosed_closedBall
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : X) ∈ Metric.closedBall (0 : X) r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      have := hball hx'
      simpa [hfix x x.2] using this
  exact FiniteDimensional.of_isCompact_closedBall ℂ hr hcomp

end GlobalTheory.CompanionTheory.CompactFix
end
