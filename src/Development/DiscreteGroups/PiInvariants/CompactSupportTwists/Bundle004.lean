module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RGrowthPiJ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

@[expose] public section

section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.F

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem one_lt_absNorm (w : HeightOneSpectrum (𝓞 E)) : 1 < Ideal.absNorm w.asIdeal := by
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact w.isPrime.ne_top
  omega

theorem norm_absC_val (x : ℝ) (w : HeightOneSpectrum (𝓞 E)) :
    ‖(((GlobalTheory.CuspRep.Model.absC E (x : ℂ)).val w : ℂˣ) : ℂ)‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-x) := by
  rw [PositivityTheory.Rg.Rs.StrStepB.absC_val]
  have h0 : 0 < (Ideal.absNorm w.asIdeal : ℕ) := by
    have := one_lt_absNorm w
    omega
  rw [Complex.norm_natCast_cpow_of_pos h0]
  simp

end DiscreteGroups.T1.G

end
end

section

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IdeleCovolume GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele PositivityTheory.Rg.BcB
open scoped ENNReal

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev lg (g : GA E n) : ℝ := logAbs g.val.det

theorem lg_eq (g : GA E n) : lg g = Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (Matrix.GeneralLinearGroup.det g)) := by
  have h := logAbs_eq_log_ideleNorm (Matrix.GeneralLinearGroup.det g)
  rw [Matrix.GeneralLinearGroup.val_det_apply] at h
  exact h

theorem lg_mul (g h : GA E n) : lg (g * h) = lg g + lg h := by
  rw [lg_eq, lg_eq, lg_eq, map_mul, map_mul,
    Real.log_mul (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _)]

def lgHom : GA E n →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (lg g)
  map_one' := by
    have h := lg_mul (1 : GA E n) 1
    rw [mul_one] at h
    simp only [show lg (1 : GA E n) = 0 by linarith, ofAdd_zero]
  map_mul' g h := by rw [lg_mul, ofAdd_add]

theorem lg_zpow (g : GA E n) (m : ℤ) : lg (g ^ m) = m * lg g := by
  have h := map_zpow (lgHom (E := E) (n := n)) g m
  have h2 := congrArg Multiplicative.toAdd h
  rw [toAdd_zpow] at h2
  simpa [lgHom, zsmul_eq_mul] using h2

theorem lg_rat (γ : GL (Fin n) E) : lg (ratGL E n γ) = 0 := by
  have hd : GeneralLinearGroup.det (ratGL E n γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  rw [lg_eq, hd, show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _,
    Real.log_one]

theorem lg_e_pos (hn : 1 ≤ n) : 0 < lg (splitCentre E n 1) := by
  rw [lg_eq, det_splitCentre_one, map_pow, Real.log_pow]
  exact mul_pos (by exact_mod_cast hn) (Real.log_pos (one_lt_ideleNorm_eIdele E))

theorem ratRange_le : (ratGL E n).range ≤ latticeGL E n := le_sup_left

instance discreteTopology_ratRange : DiscreteTopology (ratGL E n).range :=
  DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion (ratRange_le (E := E) (n := n)))
    (Continuous.subtype_mk continuous_subtype_val _) (Subgroup.inclusion_injective _)

theorem tsum_indicator (hn : 1 ≤ n) (h : GA E n → ℝ≥0∞) (hh : LeftInv (latticeGL E n) h) (v : ℝ → ℝ≥0∞)
    (y : GA E n) :
    ∑' γ : latticeGL E n, (stdDom (ratGL E n).range).indicator (fun g => h g * v (lg g)) ((γ : GA E n) * y) =
      h y * ∑' m : ℤ, v (lg y + m * lg (splitCentre E n 1)) := by
  set Γ₀ := (ratGL E n).range with hΓ₀
  set e := splitCentre E n 1 with he
  have hc : lg e ≠ 0 := (lg_e_pos hn).ne'
  let r : ℤ → Γ₀ := fun m => (existsUnique_stdDom Γ₀ (e ^ m * y)).choose
  have hr : ∀ m, ((r m : Γ₀) : GA E n) * (e ^ m * y) ∈ stdDom Γ₀ := fun m =>
    (existsUnique_stdDom Γ₀ (e ^ m * y)).choose_spec.1
  have hrlg : ∀ m, lg ((r m : Γ₀) : GA E n) = 0 := fun m => by
    obtain ⟨γ, hγ⟩ := (r m).2
    rw [← hγ]
    exact lg_rat γ
  let g : ℤ → latticeGL E n := fun m =>
    ⟨((r m : Γ₀) : GA E n) * e ^ m, mul_mem (ratRange_le (r m).2) (zpow_mem_latticeGL m)⟩
  have hlgg : ∀ m : ℤ, lg (((g m : latticeGL E n) : GA E n) * y) = lg y + m * lg e := fun m => by
    change lg (((r m : Γ₀) : GA E n) * e ^ m * y) = _
    rw [lg_mul, lg_mul, hrlg, lg_zpow]
    ring
  have hinj : Function.Injective g := fun m m' hmm => by
    have h1 := congrArg (fun γ : latticeGL E n => lg ((γ : GA E n) * y)) hmm
    simp only [hlgg] at h1
    have h2 : (m : ℝ) * lg e = m' * lg e := by linarith
    exact_mod_cast mul_right_cancel₀ hc h2
  rw [← hinj.tsum_eq, ← ENNReal.tsum_mul_left]
  · refine tsum_congr fun m => ?_
    have hmem : ((g m : latticeGL E n) : GA E n) * y ∈ stdDom Γ₀ := by
      change ((r m : Γ₀) : GA E n) * e ^ m * y ∈ stdDom Γ₀
      rw [mul_assoc]
      exact hr m
    rw [indicator_of_mem hmem]
    change h (((g m : latticeGL E n) : GA E n) * y) * v (lg (((g m : latticeGL E n) : GA E n) * y)) = _
    rw [hlgg, hh _ (g m).2 y]
  · intro γ hγ
    have hin : (γ : GA E n) * y ∈ stdDom Γ₀ := by
      by_contra hc'
      exact hγ (indicator_of_notMem hc' _)
    obtain ⟨γ₁, m, hγe⟩ := mem_latticeGL_iff.1 γ.2
    refine ⟨m, Subtype.ext ?_⟩
    have h3 : ((⟨ratGL E n γ₁, γ₁, rfl⟩ : Γ₀) : GA E n) * (e ^ m * y) ∈ stdDom Γ₀ := by
      change ratGL E n γ₁ * (e ^ m * y) ∈ stdDom Γ₀
      rw [← mul_assoc, hγe]
      exact hin
    have hu := (existsUnique_stdDom Γ₀ (e ^ m * y)).unique (hr m) h3
    change ((r m : Γ₀) : GA E n) * e ^ m = γ
    rw [hu]
    exact hγe

theorem lintegral_unfold (μ : Measure (GA E n)) [μ.IsMulLeftInvariant] (hn : 1 ≤ n) (h : GA E n → ℝ≥0∞)
    (hh : LeftInv (latticeGL E n) h) (hm : AEMeasurable h μ) (v : ℝ → ℝ≥0∞) (hv : Measurable v) :
    ∫⁻ g in stdDom (ratGL E n).range, h g * v (lg g) ∂μ =
      ∫⁻ q, h q.out * ∑' m : ℤ, v (lg q.out + m * lg (splitCentre E n 1)) ∂quotMeasure (latticeGL E n) μ := by
  have hS := measurableSet_stdDom (ratGL E n).range
  have hf : AEMeasurable ((stdDom (ratGL E n).range).indicator fun g => h g * v (lg g)) μ :=
    (hm.mul (hv.comp_aemeasurable continuous_logAbs_det.measurable.aemeasurable)).indicator hS
  rw [← lintegral_indicator hS, lintegral_eq_lintegral_tsum (Γ := latticeGL E n) hf]
  exact lintegral_congr fun q => tsum_indicator hn h hh v q.out

end DiscreteGroups.T1.G
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.RgJS
open GlobalTheory.LFun Formalism.UG GlobalTheory.PRep

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def GSat (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (φ : Sm E n) : Prop :=
  ∀ w, w ∉ S → FixAt w φ ∧ (B w).card = n ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, ∀ g : GL (Fin n) (w.adicCompletion E),
    (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < j then ϖ else 1) →
    ∀ R, IsHk w g R → ∃ m : ℕ, ((hk w R - satEig (qV E w) n (B w) j • (1 : Module.End ℂ (Sm E n))) ^ m) φ = 0

end Defs

def Supp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (φ : Sm E n), IsAutForm φ →
  φ ≠ 0 → ∀ S B, GSat S B φ →
  ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (σ : ∀ i, CuspSub E (m i)), Nonempty ι ∧ (∀ i, 1 ≤ m i) ∧
    ∀ᶠ w in Filter.cofinite, ∃ Bi : ι → Multiset ℂˣ, (∀ i, (CG.mk (σ i)).HasSat w (Bi i)) ∧ ∑ i, Bi i = B w

end DiscreteGroups.T1.G

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

theorem kerSplit_lInt_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} [Fintype ι]
    (D : Dom E a b) (k₁ k₂ : H E a b → ι → Hs (ι := ι) D) (τ : ℝ)
    (U V : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (x : H E a b) :
    lInt D k₁ k₂ τ (U - V) x = lInt D k₁ k₂ τ U x - lInt D k₁ k₂ τ V x := by
  simp only [lInt, _root_.sub_apply, inner_sub_right, Finset.sum_sub_distrib, mul_sub]

theorem kerSplit : KerSplit := by
  intro E _ _ _ n D π ι _ k₁ k₂ τ C N hb U _ _
  set S := piSp D π ι with hS
  set W := U ∘L Sᗮ.subtypeL with hW
  refine ⟨U ∘L S.starProjection, ⟨fun f hf => ?_, fun f hf => ?_⟩, ?_, ?_⟩
  · rw [ContinuousLinearMap.comp_apply, Submodule.starProjection_eq_self_iff.2 hf]
  · rw [ContinuousLinearMap.comp_apply, (Submodule.starProjection_apply_eq_zero_iff S).2 hf, map_zero]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U) fun f => ?_
    calc ‖(U ∘L S.starProjection) f‖ = ‖U (S.starProjection f)‖ := rfl
      _ ≤ ‖U‖ * ‖S.starProjection f‖ := U.le_opNorm _
      _ ≤ ‖U‖ * ‖f‖ := mul_le_mul_of_nonneg_left (S.norm_starProjection_apply_le f) (norm_nonneg U)
  · set V := U - U ∘L S.starProjection with hV
    have hWU : ‖W‖ ≤ ‖U‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U) fun f => ?_
      exact U.le_opNorm (f : Hs (ι := ι) D)
    have hVW : ‖V‖ ≤ ‖W‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg W) fun f => ?_
      have h1 : V f = W ⟨Sᗮ.starProjection f, Sᗮ.starProjection_apply_mem f⟩ := by
        change U f - U (S.starProjection f) = U (Sᗮ.starProjection f)
        rw [Submodule.starProjection_orthogonal_val, map_sub]
      rw [h1]
      refine (W.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg W))
      exact Sᗮ.norm_starProjection_apply_le f
    have hint : ∫ x, lInt D k₁ k₂ τ U x ∂D.ν - ∫ x, lInt D k₁ k₂ τ (U ∘L S.starProjection) x ∂D.ν =
        ∫ x, lInt D k₁ k₂ τ V x ∂D.ν := by
      rw [← integral_sub (hb U).1 (hb _).1]
      congr 1
      funext x
      rw [hV, kerSplit_lInt_sub]
    rw [hint]
    have hc := (hb V).2
    have hU0 : 0 ≤ C * (1 + τ) ^ N * ‖U‖ := (norm_nonneg _).trans (hb U).2
    rcases le_or_gt 0 (C * (1 + τ) ^ N) with hc0 | hc0
    · exact hc.trans (mul_le_mul_of_nonneg_left hVW hc0)
    · have hUz : ‖U‖ = 0 := le_antisymm
        (not_lt.1 fun h => absurd hU0 (not_le.2 (mul_neg_of_neg_of_pos hc0 h))) (norm_nonneg U)
      have hWz : ‖W‖ = 0 := le_antisymm (hWU.trans hUz.le) (norm_nonneg W)
      have hVz : ‖V‖ = 0 := le_antisymm (hVW.trans hWz.le) (norm_nonneg V)
      rw [hWz, mul_zero]
      rw [hVz, mul_zero] at hc
      exact hc

end DiscreteGroups.T1.G

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical

attribute [local instance] borelH

namespace DiscreteGroups.T1.G

def CutTail2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
  (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D) (r₀ r₁ ε : ℝ),
  IsTestM Φ₁ → IsTestM Φ₂ → (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ →
  IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂ → 0 ≤ r₀ → 0 ≤ r₁ → 0 < ε → ∃ C'₀ : ℝ, ∀ C' : ℝ, C'₀ ≤ C' → ∃ C : ℝ,
  ∀ (k : ℕ) (U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)), IsTestM Φ →
    IsROp D Φ (T₁ * U * T₂) → IsPiPart D π U Uπ → D4.IsTest2J (trM Φ M) (r₀ + k * r₁) →
    ‖∫ x, lInt D k₁ k₂ (C' * ((1 + k) * (1 + r₀ + r₁))) Uπ x ∂D.ν - ∫ x, lInt0 D k₁ k₂ Uπ x ∂D.ν‖ ≤ C * ‖U‖ * ε ^ k

theorem growth_of_ellipticFormula (hE : D4.EllFormula2J) (hS : SFun) (hD : DomOne) (hK : KerSplit) (hU : UncutHalf)
    (hT : CutTail2) : GrowthPiJ := by
  intro E _ _ _ _ n hn _ _ _ _ μ₁ _ μ₂ _
  obtain ⟨F₁, F₂, D, h₁, h₂, hcut, hmu⟩ := hD E n μ₁ μ₂
  refine ⟨D, hmu, ?_⟩
  intro π hπ ι _ Φ₁ Φ₂ T₁ T₂ M r₀ r₁ ε a1 a2 hfin b1 b2 hr₀ hr₁ hε
  obtain ⟨C₀, hC₀, hell⟩ := hE E n 0
  obtain ⟨k₁, k₂, hv, C, N, hb⟩ := hS E n 0 D ι Φ₁ Φ₂ T₁ T₂ M a1 a2 b1 b2
  obtain ⟨C'₀, hT'⟩ := hT E n hn D π hπ ι Φ₁ Φ₂ T₁ T₂ M k₁ k₂ r₀ r₁ ε a1 a2 hfin b1 b2 hv hr₀ hr₁ hε
  obtain ⟨Ct, hCt⟩ := hT' (max C₀ C'₀) (le_max_right _ _)
  have hC'0 : 0 ≤ max C₀ C'₀ := le_trans hC₀ (le_max_left _ _)
  refine ⟨max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct|, N, fun k U Φ t c1 c2 hU1 hU2 c3 ht => ?_⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : 0 ≤ r₀ + k * r₁ := by positivity
  have hg : 1 + (r₀ + k * r₁) ≤ (1 + k) * (1 + r₀ + r₁) := by
    nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]
  have hτ0 : 0 ≤ max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁)) := by positivity
  have hτC : C₀ * (1 + (r₀ + k * r₁)) ≤ max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁)) :=
    mul_le_mul (le_max_left _ _) hg (by positivity) hC'0
  have e1 : ellSum2 μ₁ μ₂ (trM Φ M) = ∫ x, lInt D k₁ k₂ (max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁))) U x ∂D.ν := by
    rw [← hell μ₁ μ₂ F₁ F₂ _ _ _ h₁ h₂ c3 hr hτC, ← hcut]
    exact (hb _ hτ0 U).2.2 Φ c1 c2
  obtain ⟨Uπ, hpi, -, hsplit⟩ := hK E n D π ι k₁ k₂ _ C N (fun V => ⟨(hb _ hτ0 V).1, (hb _ hτ0 V).2.1⟩) U hU1 hU2
  obtain ⟨-, hhalf⟩ := hU E n hn D π hπ ι Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ t c1 c2 hpi ht
  have htail := hCt k U Uπ Φ c1 c2 hpi c3
  rw [e1, ← hhalf]
  refine (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hsplit htail).trans (add_le_add ?_ ?_))
  · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc C * (1 + max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁))) ^ N
        ≤ |C| * (1 + max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁))) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((1 + max C₀ C'₀ * (1 + r₀ + r₁)) * (1 + k)) ^ N := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ N) (abs_nonneg C)
          nlinarith [mul_nonneg hC'0 hk]
      _ = |C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N * (1 + k) ^ N := by rw [mul_pow, mul_assoc]
      _ ≤ max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct| * (1 + k) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have h1 : Ct ≤ max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct| := (le_abs_self Ct).trans (le_max_right _ _)
    have h0 : 0 ≤ ‖U‖ * ε ^ k := by positivity
    calc Ct * ‖U‖ * ε ^ k = Ct * (‖U‖ * ε ^ k) := by ring
      _ ≤ max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct| * (‖U‖ * ε ^ k) := mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring

end DiscreteGroups.T1.G

end
end
