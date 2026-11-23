module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TsumEnormEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle411
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ker_integral_shift (X : Ctx) {φ f : X.G → ℂ} (hφ : Tst φ)
    (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y) (hf : MemLp f 2 X.ν) (x : X.G) :
    ∫ y, ker X.Γ φ x y * f y ∂X.ν = ∫ z, φ z * f (x * z) ∂X.μ := by
  rw [(unfold X kerBasic kernel_rows_columns_square_integrable hφ hinv hf x).2,
    ← integral_mul_left_eq_self (fun y => φ (x⁻¹ * y) * f y) x]
  simp only [inv_mul_cancel_left]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.finGen_pf :
    Basic → FinGen := by
  intro hB E _ _ _ n ι _ s
  classical
  obtain ⟨-, hmul, -, -, -, -, -, -, -, hrat, -, -⟩ := hB E n s.pos
  choose W hWle hWfd hW using s.fin
  have hfd : FiniteDimensional ℂ (⨆ p : ι × ι, W p.1 p.2 : Submodule ℂ (Sm E n)) := by
    haveI : ∀ p : ι × ι, FiniteDimensional ℂ (W p.1 p.2) := fun p => hWfd _ _
    exact Submodule.finiteDimensional_iSup _
  refine ⟨⨆ p : ι × ι, W p.1 p.2, iSup_le fun p => hWle _ _, hfd, ?_⟩
  intro v hv i t
  choose ψ hψ u hu hu' hvu using hv
  let X : Ctx := by
    haveI := CuspidalL2GL.t2Space_GA E n
    haveI := CuspidalL2GL.t2Space_GA E 0
    haveI := CuspidalL2GL.locallyCompactSpace_GA E n
    haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
    haveI := CuspidalL2GL.secondCountableTopology_GA E n
    haveI := CuspidalL2GL.secondCountableTopology_GA E 0
    haveI := (ratProper_holds E n).2.1
    haveI := (ratProper_holds E 0).2.1
    exact { G := H E n 0
            ms := borelH E n 0
            bs := ⟨rfl⟩
            μ := s.D.μ
            haar := { toIsFiniteMeasureOnCompacts :=
                        @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ s.D.μ s.D.haar.2.2.2
                      toIsMulLeftInvariant := s.D.haar.1
                      toIsOpenPosMeasure := s.D.haar.2.2.1 }
            Γ := ratH E n 0
            cn := (((ratGL E n).prodMap (ratGL E 0)).rangeRestrict_surjective).countable
            proper := by
              intro C hC
              have h1 := (ratProper_holds E n).2.2 _ (hC.image continuous_fst)
              have h2 := (ratProper_holds E 0).2.2 _ (hC.image continuous_snd)
              refine ((h1.prod h2).image ((ratGL E n).prodMap (ratGL E 0)).rangeRestrict).subset ?_
              rintro ⟨_, γ, rfl⟩ hγ
              exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
            F := s.D.F
            fd := s.D.fd }
  have hform : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), (ψ j).1 ((γ : H E n 0) * y).1 = (ψ j).1 y.1 := by
    intro j γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (s.π.cusp _ (hψ j)).1.left γ₁ y.1
  set Ft : ι → H E n 0 → ℂ := fun j x => (ψ j).1 x.1 * u j (ldet x) with hFt
  have hinv : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), Ft j ((γ : H E n 0) * y) = Ft j y := by
    intro j γ y
    simp only [hFt, hform j γ y, hmul, (hrat γ).1, zero_add]
  have hmem : ∀ j, MemLp (Ft j) 2 s.D.ν := fun j => (Lp.memLp (v j)).ae_eq (hvu j)
  have hex : ∀ j, ∃ ψ' ∈ W i j, ∀ g, ψ'.1 g =
      ∫ y, s.Φ₁ i j y * (fun r => u j (t + r)) (ldet y) * (ψ j).1 (g * y.1) ∂s.D.μ := fun j =>
    hW i j (fun r => u j (t + r)) ((hu j).comp (continuous_const.add continuous_id)) (ψ j) (hψ j)
  choose ψ' hψ' hval using hex
  refine ⟨∑ j, ψ' j, Submodule.sum_mem _ fun j _ =>
    (le_iSup (fun p : ι × ι => W p.1 p.2) (i, j)) (hψ' j), fun x hx => ?_⟩
  rw [s.vecs.rep₁]
  have hsum : (∑ j, ψ' j).1 x.1 = ∑ j, (ψ' j).1 x.1 := by
    simp [Submodule.coe_sum]
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hae : ∫ y, kerH (s.Φ₁ i j) x y * (v j : H E n 0 → ℂ) y ∂s.D.ν =
      ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν :=
    integral_congr_ae ((hvu j).mono fun y hy => by simp only [hy, hFt])
  rw [hae, hval j]
  have hs : ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν = ∫ z, s.Φ₁ i j z * Ft j (x * z) ∂s.D.μ :=
    ker_integral_shift X (φ := s.Φ₁ i j) (f := Ft j) (s.t₁ i j) (hinv j) (hmem j) x
  refine hs.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
  show s.Φ₁ i j z * ((ψ j).1 (x * z).1 * u j (ldet (x * z))) =
    s.Φ₁ i j z * u j (t + ldet z) * (ψ j).1 (x.1 * z.1)
  rw [hmul, hx, Prod.fst_mul]
  ring
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ctx_fub (X : Ctx) (φ : X.G → ℂ) (hφ : Tst φ) (g f : X.G → ℂ) (hg : MemLp g 2 X.ν) (hf : MemLp f 2 X.ν) :
    Integrable (fun y => (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y) X.ν ∧
      Integrable (fun z => g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν) X.ν ∧
      ∫ y, (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y ∂X.ν = ∫ z, g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν ∂X.ν := by
  obtain ⟨A, hA, h1, h2⟩ := rowInt X φ hφ
  have hm : Measurable (Function.uncurry (ker X.Γ φ)) := (kerBasic X φ hφ).2.1.measurable
  have hν : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hP := schurInt X.G X.ν (ker X.Γ φ) A hm hA h1 h2 g f hg hf
  have e1 : ∀ y, ∫ z, g z * ker X.Γ φ z y * f y ∂X.ν = (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y :=
    fun y => integral_mul_const _ _
  have e2 : ∀ z, ∫ y, g z * ker X.Γ φ z y * f y ∂X.ν = g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν := fun z => by
    simp_rw [mul_assoc]; exact integral_const_mul _ _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [e1] using hP.integral_prod_right
  · simpa only [e2] using hP.integral_prod_left
  · simp_rw [← e1, ← e2]
    exact (integral_integral_swap (f := fun z y => g z * ker X.Γ φ z y * f y) hP).symm

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.weak_pf :
    Weak := by
  intro E _ _ _ n ι _ s v u i
  have hth : ∀ y : H E n 0, th (th y) = y := fun y =>
    Prod.ext (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _) (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _)
  let c : ι → ℂ := fun l => s.M l i
  let g : ι → H E n 0 → ℂ := fun j z => starRingEnd ℂ ((u j : H E n 0 → ℂ) z)
  have hg : ∀ j, MemLp (g j) 2 s.D.ν := fun j => (Lp.memLp (u j)).star
  have F : ∀ j l, Integrable (fun y => (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y) s.D.ν ∧
      Integrable (fun z => g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν) s.D.ν ∧
      ∫ y, (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y ∂s.D.ν =
        ∫ z, g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν ∂s.D.ν := fun j l =>
    ctx_fub (ctx ratProper_holds s.D) (s.Φ₂ j l) (s.t₂ j l) (g j) v (hg j) (Lp.memLp v)
  have hrep : ∀ y, (v : H E n 0 → ℂ) y * inner ℂ u (s.k₂ (th y) i) =
      ∑ j, ∑ l, c l * ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y) := by
    intro y
    rw [s.vecs.rep₂ (th y) i u, hth, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const]
    ring
  have hv : ∀ (l : ι) (φ : H E n 0 → ℂ), ∫ y, φ y * ((vecM v c l : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) y ∂s.D.ν =
      c l * ∫ y, φ y * (v : H E n 0 → ℂ) y ∂s.D.ν := by
    intro l φ
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    have e : (vecM v c l : Lp ℂ 2 s.D.ν) = c l • v := rfl
    filter_upwards [Lp.coeFn_smul (c l) v] with y hy
    rw [e, hy, Pi.smul_apply, smul_eq_mul]
    ring
  have hR : inner ℂ u (s.T₂ (vecM v c)) =
      ∑ j, ∑ l, c l * ∫ z, g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν ∂s.D.ν := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [L2.inner_def]
    have h : (fun z => inner ℂ ((u j : Lp ℂ 2 s.D.ν) z) ((s.T₂ (vecM v c) j : Lp ℂ 2 s.D.ν) z)) =ᵐ[s.D.ν]
        fun z => ∑ l, c l * (g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν) := by
      filter_upwards [s.o₂ (vecM v c) j] with z hz
      rw [hz, RCLike.inner_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hv]
      simp only [g]
      ring
    rw [integral_congr_ae h, integral_finsetSum _ fun l _ => (F j l).2.1.const_mul _]
    exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
  have hint : Integrable (fun y => ∑ j, ∑ l, c l *
      ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y)) s.D.ν :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (F j l).1.const_mul _
  refine ⟨?_, ?_⟩
  · simpa only [hrep] using hint
  · simp only [hrep]
    change _ = inner ℂ u (s.T₂ (vecM v c))
    rw [hR, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (F j l).1.const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => (F j l).1.const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, (F j l).2.2]

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem cnt_le_sq {G : Type} [Group G] (Γ : Subgroup G) (Ω : Set G) (x : G) :
    cnt Γ Ω x ≤ cnt Γ Ω x ^ 2 := by
  by_cases h : ∃ γ : Γ, x⁻¹ * (γ : G) * x ∈ Ω
  · obtain ⟨γ, hγ⟩ := h
    have h1 : 1 ≤ cnt Γ Ω x := by
      have h2 := ENNReal.le_tsum (f := fun γ : Γ => Ω.indicator (1 : G → ℝ≥0∞) (x⁻¹ * (γ : G) * x)) γ
      have h3 : Ω.indicator (1 : G → ℝ≥0∞) (x⁻¹ * (γ : G) * x) = 1 := by
        rw [Set.indicator_of_mem hγ]; rfl
      rw [h3] at h2
      exact h2
    rw [sq]
    exact le_mul_of_one_le_left zero_le h1
  · have h0 : cnt Γ Ω x = 0 := by
      unfold cnt
      refine ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem (fun hm => h ⟨γ, hm⟩) _
    simp [h0]

private theorem cnt_central {G : Type} [Group G] (Γ : Subgroup G) (Ω : Set G) (a x : G)
    (ha : ∀ y, a * y = y * a) : cnt Γ Ω (a * x) = cnt Γ Ω x := by
  unfold cnt
  refine tsum_congr fun γ => ?_
  have e : (a * x)⁻¹ * (γ : G) * (a * x) = x⁻¹ * (γ : G) * x := by
    have h1 : (γ : G) * a = a * (γ : G) := (ha _).symm
    calc (a * x)⁻¹ * (γ : G) * (a * x) = x⁻¹ * a⁻¹ * ((γ : G) * a) * x := by group
      _ = x⁻¹ * (γ : G) * x := by rw [h1]; group
  rw [e]

private theorem norm_part_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (K : Submodule ℂ V) [K.HasOrthogonalProjection] (U Up : V →L[ℂ] V)
    (h1 : ∀ f ∈ K, Up f = U f) (h2 : ∀ f ∈ Kᗮ, Up f = 0) : ‖Up‖ ≤ ‖U‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
  have e : Up f = U (K.starProjection f) := by
    have h3 : f = K.starProjection f + (f - K.starProjection f) := by abel
    calc Up f = Up (K.starProjection f) + Up (f - K.starProjection f) := by
          rw [← map_add (f := _), ← h3]
      _ = U (K.starProjection f) := by
          rw [h2 _ (K.sub_starProjection_mem_orthogonal f), add_zero,
            h1 _ (K.starProjection_apply_mem f)]
  rw [e]
  refine (U.le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_left (K.norm_starProjection_apply_le f) (norm_nonneg _)

private theorem le_ofReal_sqrt {e : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) (h : e ^ 2 ≤ ENNReal.ofReal r) :
    e ≤ ENNReal.ofReal (Real.sqrt r) := by
  refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg r), Real.sq_sqrt hr]
  exact h

private theorem enorm_inner_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (a b : V) (T U : V →L[ℂ] V) (hT : ‖T‖ ≤ ‖U‖) (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (c : ℝ≥0∞)
    (ha : ‖a‖ₑ ≤ ENNReal.ofReal P) (hb : ‖b‖ₑ ≤ ENNReal.ofReal Q * c) :
    ‖(inner ℂ a (T b) : ℂ)‖ₑ ≤ ENNReal.ofReal (P * Q * ‖U‖) * c := by
  have h1 : ‖(inner ℂ a (T b) : ℂ)‖ ≤ ‖a‖ * (‖U‖ * ‖b‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((T.le_opNorm b).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))) (norm_nonneg _))
  calc ‖(inner ℂ a (T b) : ℂ)‖ₑ = ENNReal.ofReal ‖(inner ℂ a (T b) : ℂ)‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖a‖ * (‖U‖ * ‖b‖)) := ENNReal.ofReal_le_ofReal h1
    _ = ‖a‖ₑ * (ENNReal.ofReal ‖U‖ * ‖b‖ₑ) := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm, ofReal_norm]
    _ ≤ ENNReal.ofReal P * (ENNReal.ofReal ‖U‖ * (ENNReal.ofReal Q * c)) := by gcongr
    _ = ENNReal.ofReal (P * Q * ‖U‖) * c := by
        rw [ENNReal.ofReal_mul (mul_nonneg hP hQ), ENNReal.ofReal_mul hP]
        ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.gBound_pf :
    Basic → GBound := by
  intro hB E _ _ _ n ι _ s
  obtain ⟨-, -, hcomm, -⟩ := hB E n s.pos
  obtain ⟨C₀, Ω, hC₀, hΩ, hk⟩ := s.vecs.norm
  refine ⟨Ω, hΩ, fun x₀ => ?_⟩
  have hfin : cnt (ratH E n 0) Ω x₀ ≠ ⊤ := (cntBasic (ctx ratProper_holds s.D)).1 Ω hΩ x₀
  have hA : 0 ≤ C₀.toReal := ENNReal.toReal_nonneg
  have hc : 0 ≤ (cnt (ratH E n 0) Ω x₀).toReal := ENNReal.toReal_nonneg
  have hAe : ENNReal.ofReal C₀.toReal = C₀ := ENNReal.ofReal_toReal hC₀
  have hce : ENNReal.ofReal (cnt (ratH E n 0) Ω x₀).toReal = cnt (ratH E n 0) Ω x₀ :=
    ENNReal.ofReal_toReal hfin
  refine ⟨(Fintype.card ι : ℝ) * (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal),
    by positivity, fun m t y => ?_⟩
  have hU : ‖m.Uπ‖ ≤ ‖m.U‖ := norm_part_le _ m.U m.Uπ m.pp.1 m.pp.2
  have h1 : ∀ i, ‖s.k₁ (ac E n t * x₀) i‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal)) := fun i => by
    refine le_ofReal_sqrt (mul_nonneg hA hc) ?_
    rw [ENNReal.ofReal_mul hA, hAe, hce, ← cnt_central (ratH E n 0) Ω (ac E n t) x₀ (hcomm t)]
    exact (hk _ i).1
  have h2 : ∀ i, ‖s.k₂ y i‖ₑ ≤ ENNReal.ofReal (Real.sqrt C₀.toReal) * cnt (ratH E n 0) Ω y := fun i => by
    refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hA, hAe]
    exact (hk y i).2.trans (mul_le_mul_right (cnt_le_sq _ _ _) _)
  have h3 : ∀ i, ‖(inner ℂ (s.k₁ (ac E n t * x₀) i) (m.Uπ (s.k₂ y i)) : ℂ)‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal * ‖m.U‖) *
        cnt (ratH E n 0) Ω y := fun i =>
    enorm_inner_le _ _ _ _ hU _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) _ (h1 i) (h2 i)
  calc ‖m.G (ac E n t * x₀) y‖ₑ ≤ ∑ i, ‖(inner ℂ (s.k₁ (ac E n t * x₀) i) (m.Uπ (s.k₂ y i)) : ℂ)‖ₑ :=
        enorm_sum_le _ _
    _ ≤ ∑ _i : ι, ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal * ‖m.U‖) *
        cnt (ratH E n 0) Ω y := Finset.sum_le_sum fun i _ => h3 i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_assoc (Fintype.card ι : ℝ)]
end
end
