module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStBA
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem GaussianSum.full : GaussianSum.Statement :=
  GaussianSum.proof
    (GaussPoissonDual.proof GaussSqrt.proof
      (GaussPoissonBound.proof GaussLatticeIsLattice.proof
        (GaussLatticeCovolume.proof GaussLatticeIsLattice.proof) GaussLatticeCoords.proof
        GaussFourierSelf.proof)
      GaussDualMin.proof GaussDetFactor.proof)
    (GaussShellSum.proof (GaussShell.proof GaussPacking.proof GaussTermBound.proof))
    GaussConstant.proof

theorem ThetaMean.full : ThetaMean.Statement :=
  ThetaMean.proof
    (ThetaInnerMean.proof ThetaSummandNorm.proof
      (ThetaCubeParseval.proof ThetaCharIntegral.proof))

theorem ThetaBound.full : ThetaBound.Statement :=
  ThetaBound.proof GaussianSum.full ThetaMean.full
    (ThetaNormMajorant.proof ThetaSummandNorm.proof) ThetaFirstCoordSplit.proof ThetaConstants.proof

theorem PlueckerNormSq.full : PlueckerNormSq.Statement := PlueckerNormSq.proof CauchyBinet.proof

theorem PlueckerUnitBound.full : PlueckerUnitBound.Statement :=
  PlueckerUnitBound.proof HadamardPSD.proof

theorem PlueckerKernel.full : PlueckerKernel.Statement :=
  PlueckerKernel.proof PlueckerNormSq.full PlueckerUnitBound.full

theorem RootsOfUnityDense.full : RootsOfUnityDense.Statement := RootsOfUnityDense.proof

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyIntegrableAlt

theorem quad_pos {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (y : Fin e → ℂ) :
    0 < (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re := by
  have hx : (Fin.cons 1 y : Fin (e + 1) → ℂ) ≠ 0 := fun h => by
    have := congr_fun h 0
    simp at this
  exact hM.re_dotProduct_pos hx

theorem measurable_hermChartPot {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    Measurable (hermChartPot M) := by
  have hz : Continuous fun y : Fin e → ℂ => (Fin.cons 1 y : Fin (e + 1) → ℂ) :=
    continuous_const.finCons continuous_id
  have hc : Continuous fun y : Fin e → ℂ =>
      star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) :=
    hz.star.dotProduct (continuous_const.matrix_mulVec hz)
  exact Real.measurable_log.comp (Real.continuous_sqrt.measurable.comp (Complex.measurable_re.comp hc.measurable))

theorem pot_sub_bound (hCmp : HermFormCompare.Statement) {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hM : M.PosDef) (hN : N.PosDef) :
    ∃ K : ℝ, ∀ y : Fin e → ℂ, ‖hermChartPot M y - hermChartPot N y‖ ≤ K := by
  obtain ⟨c, hc, h1⟩ := hCmp _ M N hM hN
  obtain ⟨c', hc', h2⟩ := hCmp _ N M hN hM
  refine ⟨|Real.log c| + |Real.log c'|, fun y => ?_⟩
  have hqM := quad_pos hM y
  have hqN := quad_pos hN y
  have a1 := Real.log_le_log hqM (h1 (Fin.cons 1 y))
  have a2 := Real.log_le_log hqN (h2 (Fin.cons 1 y))
  rw [Real.log_mul hc.ne' hqN.ne'] at a1
  rw [Real.log_mul hc'.ne' hqM.ne'] at a2
  simp only [hermChartPot, Real.log_sqrt hqM.le, Real.log_sqrt hqN.le, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log c), le_abs_self (Real.log c'), abs_nonneg (Real.log c),
    abs_nonneg (Real.log c')]

theorem abs_maDensity_mix_le {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (k : ℕ) (C : ℝ) (y : Fin e → ℂ)
    (hMp : (cxHessian (hermChartPot M) y).PosSemidef) (hNp : (cxHessian (hermChartPot N) y).PosSemidef)
    (hle : ((C : ℂ) • cxHessian (hermChartPot N) y - cxHessian (hermChartPot M) y).PosSemidef) :
    ‖maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y‖ ≤
      max C 1 ^ e * maDensity (fun _ : Fin e => hermChartPot N) y := by
  set HM := cxHessian (hermChartPot M) y
  set HN := cxHessian (hermChartPot N) y
  set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => if (j : ℕ) < k then HM else HN with hAdef
  have hA : (fun j : Fin e => cxHessian (if (j : ℕ) < k then hermChartPot M else hermChartPot N) y) = A := by
    funext j
    simp only [hAdef]
    split_ifs <;> rfl
  set B : Fin e → Matrix (Fin e) (Fin e) ℂ := fun _ => ((max C 1 : ℝ) : ℂ) • HN with hBdef
  have hApsd : ∀ j, (A j).PosSemidef := fun j => by
    simp only [hAdef]
    split_ifs
    · exact hMp
    · exact hNp
  have hsm : ∀ r : ℝ, 0 ≤ r → (((r : ℝ) : ℂ) • HN).PosSemidef := fun r hr =>
    hNp.smul (Complex.zero_le_real.2 hr)
  have hAB : ∀ j, (B j - A j).PosSemidef := fun j => by
    simp only [hBdef, hAdef]
    split_ifs
    · have h : ((max C 1 : ℝ) : ℂ) • HN - HM = ((C : ℂ) • HN - HM) + (((max C 1 - C : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul]
        abel
      rw [h]
      exact hle.add (hsm _ (sub_nonneg.2 (le_max_left C 1)))
    · have h : ((max C 1 : ℝ) : ℂ) • HN - HN = (((max C 1 - 1 : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul, one_smul]
      rw [h]
      exact hsm _ (sub_nonneg.2 (le_max_right C 1))
  have hmono : (mixedDisc A).re ≤ (mixedDisc B).re := ReciprocityTheory.AnForm.A.mdisc_re_mono A B hApsd hAB
  have hnn : 0 ≤ (mixedDisc A).re := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hApsd).2
  have hB : mixedDisc B = ((max C 1 : ℝ) : ℂ) ^ e * HN.det := by
    have h := ReciprocityTheory.AnForm.A.mdisc_const (((max C 1 : ℝ) : ℂ) • HN)
    rw [det_smul, Fintype.card_fin] at h
    exact h
  have hN1 : mixedDisc (fun _ : Fin e => HN) = HN.det := ReciprocityTheory.AnForm.A.mdisc_const HN
  have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  unfold maDensity
  rw [hA, hN1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_of_nonneg hnn]
  rw [hB, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmono
  calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re
      ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (max C 1 ^ e * HN.det.re) :=
        mul_le_mul_of_nonneg_left hmono hc
    _ = _ := by ring

end ChartEnergyIntegrableAlt


open ChartEnergyIntegrableAlt in
theorem ChartEnergyIntegrable.proof (hCmp : HermFormCompare.Statement) (hHess : ChartHessCompare.Statement) :
    ChartEnergyIntegrable.Statement := by
  intro e M N hM hN k
  obtain ⟨C, hC⟩ := hHess e M N hM hN
  obtain ⟨C₀, hC₀⟩ := hHess e N N hN hN
  obtain ⟨K, hK⟩ := pot_sub_bound hCmp hM hN
  have hmix : Integrable (fun y : Fin e → ℂ =>
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y) := by
    refine Integrable.mono' ((ChartDensityIntegrable.proof e N hN).const_mul (max C 1 ^ e))
      (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity _).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    exact abs_maDensity_mix_le k C y (hC y).1.posSemidef (hC₀ y).1.posSemidef (hC y).2
  exact hmix.bdd_mul ((measurable_hermChartPot M).sub (measurable_hermChartPot N)).aestronglyMeasurable
    (Eventually.of_forall hK)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

theorem anchor_homog (f j m : ℕ) : IsMultiHomog (rootAnchorSection f j m) (fun _ => 1) := by
  classical
  intro μ hμ k
  have hdeg : rootAnchorSection f j m = monomial (∑ τ : Fin f, Finsupp.single (⟨τ, plAnchor j m⟩ : Σ _ : Fin f, PlIdx j m) 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]; rfl
  rw [hdeg] at hμ
  have := MvPolynomial.support_monomial_subset hμ
  rw [Finset.mem_singleton] at this
  subst this
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_comm, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single (plAnchor j m)]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  · intro τ _ hτ
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    exact hτ (congrArg Sigma.fst h)
  · simp

theorem RootHeight.proofNE (hA : RootArithVar.Statement) (hD : RootDivSuppEmpty.Statement)
    (hL : RootLogNormBound.Statement) (hF : RootPointsFinite.Statement) (hP : PtsIntegralZeroLowerNE.Statement)
    (hM : MultiHomogMemCoord.Statement) (hS : FsLineSmooth.Statement) : RootHeight.Statement := by
  intro f j m ζ hf hζ II hII
  have : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have hV := hA f j m ζ hf hζ
  have hmem : rootAnchorSection f j m ∉ rootPointIdeal ζ := by
    rw [rootPointIdeal, hM (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) _ _ (anchor_homog f j m)]
    simp [rootAnchorSection, rootCoord, anchor_minor]
  have hsm : IsSmoothHerm (fsMulti (plBlocks f j m)) := hS _ _
  have hR := (hII (Fin f) (plBlocks f j m)).2.2 (rootPointIdeal ζ) 0 Fin.elim0
    (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) (fun _ => 1) hV (fun j => j.elim0) hsm
    (fun _ => by simp [fsMulti, HermLine.ofMetrics]) (anchor_homog f j m) hmem
  have e1 : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) :
      Fin (0 + 1) → HermLine (plBlocks f j m)) = ![fsMulti (plBlocks f j m)] := by
    funext i; fin_cases i; rfl
  rw [e1] at hR
  have hlow := hP (Fin f) (plBlocks f j m) (rootPointIdeal ζ)
    (fun i z => Real.log (((Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) i).h z))
    (logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m)) (-grassConst f j m)
    hV.2.1.2.1 (hF f j m ζ hζ) ?_ (hL f j m ζ hζ)
  · have : recR (II (Fin f) (plBlocks f j m)) (rootPointIdeal ζ)
        (Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) =
        - arInt (rootPointIdeal ζ) (rootAnchorSection f j m) (fsMulti (plBlocks f j m)) Fin.elim0 := by
      simp [recR, hD f j m ζ hζ]
    rw [this] at hR
    show II _ _ _ 1 _ ≤ _
    rw [hR]
    simp only [arInt]
    have := hlow
    nlinarith
  · intro u z hu hz
    have hh := (fsMulti (plBlocks f j m)).smul u z hu
    have hpos := (fsMulti (plBlocks f j m)).pos z hz.1
    have hfa : (fsMulti (plBlocks f j m)).a = fun _ => 1 := rfl
    simp only [logNorm, hh, hfa, zpow_one]
    have hs : eval (fun p : (Σ _ : Fin f, PlIdx j m) => u p.1 * z p) (map (Int.castRingHom ℂ) (rootAnchorSection f j m))
        = (∏ k, u k) * eval z (map (Int.castRingHom ℂ) (rootAnchorSection f j m)) := by
      simp [rootAnchorSection, Finset.prod_mul_distrib]
    have hu0 : (∏ k, ‖u k‖) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (hu k)
    congr 1
    erw [hs]
    rw [norm_mul, norm_prod]
    field_simp

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory

noncomputable section

namespace PtsIntegralZeroLowerNEAux

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem rel_of_mk_eq {W : Ideal (MRing ι)} {a b : mcPts W}
    (h : (Quot.mk _ a : McClasses W) = Quot.mk _ b) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (b : (Σ k, ι k) → ℂ) = fun p => c p.1 * (a : (Σ k, ι k) → ℂ) p := by
  have hg := Quot.eqvGen_exact h
  clear h
  induction hg with
  | rel x y hxy => exact hxy
  | refl x => exact ⟨1, fun _ => one_ne_zero, by funext p; simp⟩
  | symm x y _ ih =>
    obtain ⟨c, hc, e⟩ := ih
    refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
    funext p
    rw [e]
    field_simp [hc p.1]
  | trans x y w _ _ ih1 ih2 =>
    obtain ⟨c, hc, e⟩ := ih1
    obtain ⟨d, hd, e'⟩ := ih2
    refine ⟨fun k => d k * c k, fun k => mul_ne_zero (hd k) (hc k), ?_⟩
    funext p
    rw [e', e]
    ring

theorem maDensity_zero (φ : Fin 0 → (Fin 0 → ℂ) → ℝ) (z : Fin 0 → ℂ) : maDensity φ z = 1 := by
  simp [maDensity, mixedDisc, Matrix.det_fin_zero]

theorem integral_fin_zero (F : (Fin 0 → ℂ) → ℝ) (y : Fin 0 → ℂ) : ∫ y', F y' = F y := by
  rw [Measure.volume_pi_eq_dirac y, integral_dirac]


omit [∀ k, Fintype (ι k)] in
theorem segre_ne_zero {W : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts W) : segre z ≠ 0 := by
  intro h0
  choose p hp using hz.1
  have h := congrFun h0 p
  simp only [segre, Pi.zero_apply] at h
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => hp k) h

theorem exists_goodProj {W : Ideal (MRing ι)} (hfin : Finite (McClasses W)) :
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), IsGoodProj W Ψ := by
  classical
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun q : McClasses W => segre (q.out : (Σ k, ι k) → ℂ)) (fun q => segre_ne_zero q.out.2)
  refine ⟨LinearMap.pi fun _ => f, fun z hz h => ?_⟩
  obtain ⟨c, hc, e⟩ := rel_of_mk_eq (Quot.out_eq (Quot.mk _ ⟨z, hz⟩ : McClasses W))
  have e' : z = fun p => c p.1 * ((Quot.mk _ ⟨z, hz⟩ : McClasses W).out : (Σ k, ι k) → ℂ) p := e
  have h0 := congrFun h 0
  rw [LinearMap.pi_apply, Pi.zero_apply, e', segre_smul, map_smul, smul_eq_mul] at h0
  exact hf _ ((mul_eq_zero.mp h0).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => hc k))

theorem bij_fibre [Nonempty K] {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (hΨ : IsGoodProj W Ψ) (y : Fin 0 → ℂ) :
    ∃ M : McClasses W → ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y, Function.Bijective M := by
  classical
  set a : ((Σ k, ι k) → ℂ) → ℂ := fun z => Ψ (segre z) 0 with ha_def
  have ha : ∀ z ∈ mcPts W, a z ≠ 0 := fun z hz h0 =>
    hΨ z hz (funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h0)
  set N : ((Σ k, ι k) → ℂ) → (((k : K) → ι k) → ℂ) := fun z => (a z)⁻¹ • segre z with hN
  have hNmem : ∀ z (hz : z ∈ mcPts W), N z ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y := by
    intro z hz
    obtain ⟨k0⟩ := ‹Nonempty K›
    let u : K → ℂ := Pi.mulSingle k0 (a z)⁻¹
    have hu : ∀ k, u k ≠ 0 := fun k => by
      by_cases hk : k = k0
      · subst hk; simp [u, ha z hz]
      · simp [u, Pi.mulSingle_eq_of_ne hk]
    refine ⟨fun p => u p.1 * z p, mcPts_smul hW u hu hz, ?_, ?_⟩
    · rw [segre_smul]
      simp [u, N]
    · funext i
      rw [Fin.fin_one_eq_zero i]
      simp [N, a, ha z hz]
  have hNrel : ∀ z z' : mcPts W, (∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (z' : (Σ k, ι k) → ℂ) = fun p => c p.1 * (z : (Σ k, ι k) → ℂ) p) → N z = N z' := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ ⟨c, hc, e⟩
    simp only at e
    subst e
    have hpc : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
    simp only [N, a, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
    congr 1
    field_simp [hpc, ha z hz]
  let M : McClasses W → ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y :=
    Quot.lift (fun z => ⟨N z, hNmem z z.2⟩) (fun z z' h => Subtype.ext (hNrel z z' h))
  refine ⟨M, ?_, ?_⟩
  · intro q q'
    induction q using Quot.ind with | mk z => ?_
    induction q' using Quot.ind with | mk z' => ?_
    intro h
    have h' : N z = N z' := congrArg Subtype.val h
    have hs : segre (z : (Σ k, ι k) → ℂ) = (a z * (a z')⁻¹) • segre (z' : (Σ k, ι k) → ℂ) := by
      have := congrArg (fun v => a z • v) h'
      simp only [N, smul_smul] at this
      rw [mul_inv_cancel₀ (ha z z.2), one_smul] at this
      exact this
    obtain ⟨c, hc, e⟩ :=
      sameOrbit_of_segre z'.2.1 _ (mul_ne_zero (ha z z.2) (inv_ne_zero (ha z' z'.2))) hs
    exact (Quot.sound ⟨c, hc, e⟩).symm
  · rintro ⟨w, z, hz, rfl, hw⟩
    refine ⟨Quot.mk _ ⟨z, hz⟩, Subtype.ext ?_⟩
    show N z = segre z
    have h1 : a z = 1 := by
      show Ψ (segre z) 0 = 1
      rw [hw]
      rfl
    simp [N, h1]


omit [∀ k, Fintype (ι k)] in
theorem density_ge {W : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)}
    {φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ} {g : ((Σ k, ι k) → ℂ) → ℝ} {c : ℝ}
    (hc : ∀ z ∈ mcPts W, c ≤ g z) {y : Fin 0 → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y) :
    c ≤ sheetDensity W Ψ φ g y w := by
  classical
  obtain ⟨z, hz, rfl, hΨz⟩ := hw
  have hex : ∃ γ, IsSheet W Ψ y (segre z) γ :=
    ⟨fun _ => z, rfl, Filter.Eventually.of_forall fun y' =>
      ⟨differentiableAt_const _, hz, by rw [Subsingleton.elim y' y]; exact hΨz⟩⟩
  unfold sheetDensity
  rw [dite_eq_left hex, maDensity_zero, mul_one]
  exact hc _ hex.choose_spec.2.self_of_nhds.2.1

end PtsIntegralZeroLowerNEAux


open PtsIntegralZeroLowerNEAux in
theorem PtsIntegralZeroLowerNE.proof : PtsIntegralZeroLowerNE.Statement := by
  intro K _ _ ι _ W φ g c hW hfin _ hc
  classical
  obtain ⟨Ψ0, hΨ0⟩ := exists_goodProj hfin
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), IsGoodProj W Ψ := ⟨Ψ0, hΨ0⟩
  unfold ptsIntegral
  rw [dite_eq_left hex]
  have hΨ : IsGoodProj W hex.choose := hex.choose_spec
  let y : Fin 0 → ℂ := fun i => i.elim0
  unfold ptsIntegralAt
  rw [integral_fin_zero _ y]
  obtain ⟨M, hM⟩ := bij_fibre hW hex.choose hΨ y
  have := hfin
  have : Finite (ReciprocityTheory.ChartRestriction.G.Geo.fibre W hex.choose y) := Finite.of_surjective M hM.2
  have hF : (ReciprocityTheory.ChartRestriction.G.Geo.fibre W hex.choose y).Finite := Set.toFinite _
  have hcard : degC W = hF.toFinset.card := by
    rw [← Nat.card_eq_card_finite_toFinset hF, ← Nat.card_eq_of_bijective M hM]
    rfl
  rw [finsum_mem_eq_finite_toFinset_sum _ hF, hcard]
  have h := Finset.card_nsmul_le_sum hF.toFinset (fun w => sheetDensity W hex.choose φ g y w) c
    (fun w hw => density_ge hc ((Set.Finite.mem_toFinset hF).mp hw))
  rw [nsmul_eq_mul] at h
  linarith

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ClosedPointChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 →
      ∀ m : Ideal (curveRing y), m.IsMaximal → ∃ t : T, y ⟨(), t⟩ ≠ 0 ∧
        ∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a

end

end GroundTheory.Heights₂.Heights
end
