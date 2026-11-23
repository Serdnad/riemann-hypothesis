module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle006
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosT
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TsumEnormEq
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
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
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle003

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc DiscreteGroups.T1.G
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH borelSpace_H

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem slab_rat {D : Dom E n 0} {f : GA E n → ℂ} (hf : Slab D f) (γ : ratH E n 0) (x : GA E n) :
    f ((γ : H E n 0).1 * x) = f x := by
  obtain ⟨_, γ, rfl⟩ := γ
  exact hf.2.1 γ.1 x

private theorem slab_aS {D : Dom E n 0} {f : GA E n → ℂ} (hf : Slab D f) (x : H E n 0) (s : ℝ) :
    f (x * aS E n s).1 = f x.1 := by
  have h : (x * aS E n s).1 = splitCentre E n s * x.1 := (splitCentre_comm _ _).symm
  rw [h]
  exact hf.2.2.1 s x.1

private theorem cont_pair {a b : GA E n → ℂ} (ha : Continuous a) (hb : Continuous b) {u : ℝ → ℂ} (hu : Continuous u) :
    Continuous fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x) :=
  ((Complex.continuous_conj.comp (ha.comp continuous_fst)).mul (hb.comp continuous_fst)).mul
    (hu.comp continuous_ldet)

private theorem pair_integrable {D : Dom E n 0} {a b : GA E n → ℂ} (ha : Slab D a) (hb : Slab D b) {u : ℝ → ℂ}
    (hu : Continuous u) (hs : HasCompactSupport u) :
    Integrable (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) D.ν := by
  obtain ⟨χ, h1, -, hχs, -⟩ := exists_continuous_one_zero_of_isCompact (X := ℝ) hs.isCompact isClosed_empty
    (Set.disjoint_empty _)
  have hχ : Continuous fun s => ((χ s : ℝ) : ℂ) := Complex.continuous_ofReal.comp χ.continuous
  have hχc : HasCompactSupport fun s => ((χ s : ℝ) : ℂ) := hχs.comp_left Complex.ofReal_zero
  have hA : MemLp (fun x : H E n 0 => star (a x.1 * ((χ (ldet x) : ℝ) : ℂ))) 2 D.ν := (ha.2.2.2 _ hχ hχc).star
  have hB := hb.2.2.2 u hu hs
  refine (hA.integrable_mul hB).congr (ae_of_all _ fun x => ?_)
  by_cases h0 : u (ldet x) = 0
  · simp [h0]
  · have : χ (ldet x) = 1 := h1 (subset_tsupport _ h0)
    simp [this, mul_assoc]

private theorem integral_u_shift (u : ℝ → ℂ) (r c : ℝ) (hc : 0 < c) :
    ∫ s : ℝ, u (r + s * c) = (c : ℂ)⁻¹ * ∫ s, u s := by
  have h := integral_affine u r c hc
  have h2 := integral_neg_eq_self (fun s : ℝ => u (r - s * c)) volume
  have e : (fun s : ℝ => u (r - -s * c)) = fun s => u (r + s * c) := by
    funext s
    congr 1
    ring
  simp only [e] at h2
  rw [h2, h, Complex.real_smul, Complex.ofReal_inv]

private theorem pair_wt (hn : 1 ≤ n) {D : Dom E n 0} {a b : GA E n → ℂ} (ha : Slab D a) (hb : Slab D b) {u w : ℝ → ℂ}
    (hu : Continuous u) (hs : HasCompactSupport u) (hw : Continuous w) (hws : HasCompactSupport w)
    (hw1 : ∫ s, w s = 1) : prW D u a b = (∫ s, u s) * prW D w a b := by
  have hc : 0 < ldet (aS E n 1) := lg_e_pos hn
  have hinv : ∀ (γ : ratH E n 0) x, (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) ((γ : H E n 0) * x) =
      (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) x := fun γ x => by
    show starRingEnd ℂ (a ((γ : H E n 0).1 * x.1)) * b ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x)) = _
    rw [slab_rat ha, slab_rat hb, ldet_rat]
  have h := (avgInt_holds E n hn D _ hinv (cont_pair ha.1 hb.1 hu) (pair_integrable ha hb hu hs) w hw hws hw1).2
  have hin : ∀ x : H E n 0, w (ldet x) * ∫ s : ℝ, starRingEnd ℂ (a (x * aS E n s).1) * b (x * aS E n s).1 * u (ldet (x * aS E n s)) =
      ((ldet (aS E n 1) : ℂ)⁻¹ * ∫ s, u s) * (starRingEnd ℂ (a x.1) * b x.1 * w (ldet x)) := fun x => by
    simp only [slab_aS ha, slab_aS hb, ldet_mul_aS]
    rw [integral_const_mul, integral_u_shift u _ _ hc]
    ring
  simp only [hin] at h
  rw [integral_const_mul] at h
  have hc' : (ldet (aS E n 1) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  show ∫ x, _ ∂D.ν = (∫ s, u s) * ∫ x, _ ∂D.ν
  rw [h, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc', one_mul]

private theorem ldet_shift {g : GA E n} (hg : logAbs g.val.det = 0) (x : H E n 0) :
    ldet (x * ((g, 1) : H E n 0)) = ldet x := by
  have h : ldet (x * ((g, 1) : H E n 0)) = ldet x + logAbs g.val.det := Dcy.logAbs_det_mul' x.1 g
  rw [h, hg, add_zero]

private theorem slab_rt (D : Dom E n 0) {a : GA E n → ℂ} (ha : Slab D a) {g : GA E n} (hg : logAbs g.val.det = 0) :
    Slab D fun x => a (x * g) := by
  have hc : Continuous fun x => a (x * g) := ha.1.comp (continuous_mul_const g)
  refine ⟨hc, fun γ x => ?_, fun t x => ?_, fun u hu hs => ?_⟩
  · show a (_ * x * g) = a (x * g)
    rw [mul_assoc]
    exact ha.2.1 γ _
  · show a (_ * x * g) = a (x * g)
    rw [mul_assoc]
    exact ha.2.2.1 t _
  · have hm := ha.2.2.2 u hu hs
    have hcm : Continuous fun x : H E n 0 => a (x.1 * g) * u (ldet x) :=
      (hc.comp continuous_fst).mul (hu.comp continuous_ldet)
    have hsh := lintegral_shift D (fun x : H E n 0 => ‖a x.1 * u (ldet x)‖ₑ ^ (2 : ENNReal).toReal) (fun γ x => by
      show ‖a ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x))‖ₑ ^ _ = _
      rw [slab_rat ha, ldet_rat]) ((g, 1) : H E n 0)
    simp only [ldet_shift hg] at hsh
    change eLpNorm (fun x : H E n 0 => a (x.1 * g) * u (ldet x)) 2 D.ν < ⊤
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hcm.aestronglyMeasurable]
    have h2 := hm
    change eLpNorm (fun x : H E n 0 => a x.1 * u (ldet x)) 2 D.ν < ⊤ at h2
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm.aestronglyMeasurable, ← hsh] at h2
    exact h2

private theorem pair_rt (D : Dom E n 0) {a b : GA E n → ℂ} (ha : Slab D a) (hb : Slab D b) (u : ℝ → ℂ) {g : GA E n}
    (hg : logAbs g.val.det = 0) : prW D u (fun x => a (x * g)) (fun x => b (x * g)) = prW D u a b := by
  have h := integral_shift D (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) (fun γ x => by
    show starRingEnd ℂ (a ((γ : H E n 0).1 * x.1)) * b ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x)) = _
    rw [slab_rat ha, slab_rat hb, ldet_rat]) ((g, 1) : H E n 0)
  simp only [ldet_shift hg] at h
  exact h

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.wtInd_pf :
    Basic → WtInd := by
  intro _ E _ _ _ n hn D a b ha hb u hu hs
  exact ⟨pair_integrable ha hb hu hs, fun w hw hws hw1 => pair_wt hn ha hb hu hs hw hws hw1,
    fun g hg => ⟨slab_rt D ha hg, pair_rt D ha hb u hg⟩⟩

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem tst_trM (D : Dom E n 0) {ι : Type} [Fintype ι] {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ)
    (M : Matrix ι ι ℂ) : PositivityTheory.Rg.BcB.E1.Tst (G := (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D).G) (trM Φ M) := by
  have h := (PositivityTheory.Rg.BcB.E1.kerLin (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) (ι × ι)
    (fun p => Φ p.1 p.2) (fun p => M p.2 p.1) (fun p => hΦ p.1 p.2)).1
  have e : trM Φ M = fun y => ∑ p : ι × ι, Φ p.1 p.2 y * M p.2 p.1 := by
    funext y
    rw [Fintype.sum_prod_type]
    rfl
  rw [e]
  exact h

private theorem cusp_projection_self (D : Dom E n 0) (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) {w : ℝ → ℂ}
    (hw : Continuous w) (hws : HasCompactSupport w) (v : Lp ℂ 2 D.ν)
    (hv : (v : H E n 0 → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * w (ldet x)) : P0 D π v = v := by
  have hvec : IsPiVec D π (vecM v fun _ : Unit => (1 : ℂ)) := fun _ => ⟨ψ, hψ, w, hw, hws, by
    have e : (vecM v fun _ : Unit => (1 : ℂ)) () = v := one_smul ℂ v
    simpa [e] using hv⟩
  have hmem : (vecM v fun _ : Unit => (1 : ℂ)) ∈ piSp D π Unit :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span hvec)
  unfold P0
  rw [Submodule.starProjection_eq_self_iff.2 hmem]
  exact one_smul ℂ v

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.rep_pf :
    Basic → ThetaInt → KInv → PDiag → Ker → Rep := by
  intro hB hTI hK _ hKer E _ _ _ n ι _ s m ψ hψ u hu hus x₀
  obtain ⟨-, bMul, -, -, -, -, bThL, bThTh, bThMul, bRat, -, -⟩ := hB E n s.pos
  obtain ⟨ψ₁, hψ₁, hψe⟩ := s.fix.2 ψ hψ
  have hw : Continuous fun t : ℝ => u (-t) := hu.comp continuous_neg
  have hws : HasCompactSupport fun t : ℝ => u (-t) := hus.comp_homeomorph (Homeomorph.neg ℝ)
  set f : H E n 0 → ℂ := fun x => ψ₁.1 x.1 * u (-ldet x) with hf
  have hmem : MemLp f 2 s.D.ν := (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n s.pos s.D s.π s.fix ψ₁ hψ₁ _ hw hws).1
  set v : Lp ℂ 2 s.D.ν := hmem.toLp f with hvdef
  have hv : (v : H E n 0 → ℂ) =ᵐ[s.D.ν] f := hmem.coeFn_toLp
  have hP : P0 s.D s.π v = v := cusp_projection_self s.D s.π hψ₁ hw hws v hv
  obtain ⟨kI, kE⟩ := hKer E n ι s m v x₀
  rw [hP] at kE
  have hψinv : ∀ (γ : ratH E n 0) (y : H E n 0), ψ₁.1 ((γ : H E n 0) * y).1 = ψ₁.1 y.1 := by
    intro γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (s.π.cusp ψ₁ hψ₁).1.left γ₁ y.1
  have hfinv : ∀ (γ : ratH E n 0) (y : H E n 0), f ((γ : H E n 0) * y) = f y := by
    intro γ y
    simp only [hf]
    rw [hψinv γ y, bMul, (bRat γ).1, zero_add]
  have hGinv : ∀ (γ : ratH E n 0) (y : H E n 0), m.G x₀ (th ((γ : H E n 0) * y)) = m.G x₀ (th y) := by
    intro γ y
    have h2 := hK E n ι s |>.2 ⟨th (γ : H E n 0), (bRat γ).2⟩ (th y)
    simp only [Mid.G, Gk]
    rw [bThMul, h2]
  set F : H E n 0 → ℂ := fun y => f y * m.G x₀ (th y) with hF
  have hFinv : Inv F := fun γ y => by
    simp only [hF]
    rw [hfinv, hGinv]
  have hFint : Integrable F s.D.ν := kI.congr (hv.mono fun y hy => by simp only [hF, hy])
  obtain ⟨tI, tE⟩ := hTI E n s.D F hFinv hFint
  have hFth : ∀ x, F (th x) = ψ.1 x.1 * m.G x₀ x * u (ldet x) := by
    intro x
    have h1 : ψ₁.1 (th x).1 = ψ.1 x.1 := by
      have e : thetaA E n (th x).1 = x.1 := congrArg Prod.fst (bThTh x)
      rw [hψe, e]
    simp only [hF, hf]
    rw [h1, bThL, neg_neg, bThTh]
    ring
  refine ⟨tI.congr (Filter.Eventually.of_forall hFth), ?_⟩
  have hμl : s.D.μ.IsMulLeftInvariant := s.D.haar.1
  haveI hmm : MeasurableMul (H E n 0) :=
    (inferInstance : MeasurableMul (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D).G)
  have hun := (DiscreteGroups.T1.G.unfold (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D)
    PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable (tst_trM s.D m.t s.M) (f := f) hfinv hmem x₀).2
  have hun' : ∫ y, kerH m.φ x₀ y * f y ∂s.D.ν = ∫ y, m.φ (x₀⁻¹ * y) * f y ∂s.D.μ := hun
  calc ∫ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) ∂s.D.ν
      = ∫ x, F (th x) ∂s.D.ν := integral_congr_ae (Filter.Eventually.of_forall fun x => (hFth x).symm)
    _ = ∫ x, F x ∂s.D.ν := tE
    _ = ∫ y, (v : H E n 0 → ℂ) y * m.G x₀ (th y) ∂s.D.ν :=
        integral_congr_ae (hv.mono fun y hy => by simp only [hF, hy])
    _ = ∫ y, kerH m.φ x₀ y * (v : H E n 0 → ℂ) y ∂s.D.ν := kE
    _ = ∫ y, kerH m.φ x₀ y * f y ∂s.D.ν := integral_congr_ae (hv.mono fun y hy => by simp only [hy])
    _ = ∫ y, m.φ (x₀⁻¹ * y) * f y ∂s.D.μ := hun'
    _ = ∫ z, m.φ (x₀⁻¹ * (x₀ * z)) * f (x₀ * z) ∂s.D.μ :=
        (integral_mul_left_eq_self (fun y => m.φ (x₀⁻¹ * y) * f y) x₀).symm
    _ = ∫ z, m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1)) * u (-(ldet x₀ + ldet z)) ∂s.D.μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hf]
        rw [inv_mul_cancel_left, bMul, Prod.fst_mul, hψe]
        ring

end
end
