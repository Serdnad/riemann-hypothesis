module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle076
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableA
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix Set
open scoped ContDiff Manifold
open GroundTheory.Heights₂.Heights (varInt chartInt SmoothNear localMult linEval linForm logReg contDiff_linEval
  contDiff_logReg smoothNear_of_contDiff)

namespace LelongWeightLimit

variable {n : ℕ}

theorem exists_contDiff_eqOn {Z : Set (Fin n → ℂ)} (hZ : IsClosed Z) {f : (Fin n → ℂ) → ℝ}
    (hf : SmoothNear Z f) (hfc : HasCompactSupport f) :
    ∃ g : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ Z, g x = f x := by
  obtain ⟨U, hU, hZU, hfU⟩ := hf
  have hK : IsCompact (Z ∩ tsupport f) := hfc.isCompact.inter_left hZ
  obtain ⟨V, hV, hKV, hVU, -⟩ :=
    exists_open_between_and_isCompact_closure hK hU (inter_subset_left.trans hZU)
  obtain ⟨θ, hθ, -, hθs, hθ1⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, Fin n → ℂ) (n := ⊤) hV hK.isClosed hKV
  rw [contMDiff_iff_contDiff] at hθ
  refine ⟨θ * f, ?_, hfc.mul_left, fun x hx => ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hx : x ∈ U
    · exact hθ.contDiffAt.mul (hfU.contDiffAt (hU.mem_nhds hx))
    · have hev : θ * f =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds fun h => hx (hVU h)] with y hy
        have : θ y = 0 := by
          by_contra h
          exact hy (subset_closure (hθs ▸ (Function.mem_support.mpr h)))
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · by_cases hxf : x ∈ tsupport f
    · rw [Pi.mul_apply, (hθ1 x).1 ⟨hx, hxf⟩, one_mul]
    · rw [Pi.mul_apply, image_eq_zero_of_notMem_tsupport hxf, mul_zero]

theorem varInt_congr {J : Ideal (MvPolynomial (Fin n) ℂ)} {d : ℕ} {f g : (Fin n → ℂ) → ℝ}
    (h : ∀ x ∈ ComplexSets.zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    varInt J d f φ = varInt J d g φ := by
  unfold varInt chartInt
  split_ifs
  · rw [CutOffDominated.chartDens_congr_zeroSet h]
  · rfl

theorem smoothNear_weight {Z : Set (Fin n → ℂ)} (u : Fin n → ℂ) {k : (Fin n → ℂ) → ℝ}
    (hk : SmoothNear Z k) (hk0 : ∀ x ∈ Z, 0 < k x) {ε : ℝ} (hε : 0 < ε) :
    SmoothNear Z (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) := by
  obtain ⟨U, hU, hZU, hkU⟩ := hk
  refine ⟨U ∩ k ⁻¹' Ioi 0, hkU.continuousOn.isOpen_inter_preimage hU isOpen_Ioi,
    fun x hx => ⟨hZU hx, hk0 x hx⟩, ?_⟩
  refine ContDiffOn.div_const (ContDiffOn.log ?_ fun x hx => ?_) _
  · exact ((contDiff_norm_sq ℝ).comp (contDiff_linEval u)).contDiffOn.add
      (contDiffOn_const.mul ((hkU.mono inter_subset_left).pow 2))
  · have h1 : 0 < ε * k x ^ 2 := mul_pos hε (pow_pos hx.2 2)
    have h2 : 0 ≤ ‖linEval u x‖ ^ 2 := sq_nonneg _
    exact (by linarith : (0 : ℝ) < ‖linEval u x‖ ^ 2 + ε * k x ^ 2).ne'

end LelongWeightLimit


open LelongWeightLimit in
theorem LelongWeightLimit.proof (hL : GroundTheory.Heights₂.Heights.LelongLimit.Statement)
    (hS : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement) (hD : LelongWeightDiff.Statement) :
    LelongWeightLimit.Statement := by
  intro n d J u f k φ hJ hdim hu hf hfc hφ hk hk0
  obtain ⟨g, hg, hgc, hgf⟩ :=
    exists_contDiff_eqOn (GroundTheory.Heights₂.Heights.SheetSumMeasurable.isClosed_zeroSet J) hf hfc
  have hsum : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) =
      ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ := by
    refine finsum_congr fun W => finsum_congr fun hW => ?_
    rw [varInt_congr (fun x hx => hgf x fun q hq => hx q (le_sup_left.trans hW.1.2 hq)) φ]
  have hlim := (hL n d J u g φ hJ hdim hu hg hgc hφ).add (hD n d J u g k φ hJ hdim hu hg hgc hφ hk hk0)
  rw [hsum, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [varInt_congr (fun x hx => (hgf x hx).symm) (vecCons _ φ),
    hS n d J g _ φ hJ hdim (smoothNear_of_contDiff hg) (smoothNear_weight u hk hk0 hε) hφ (Or.inl hgc),
    hS n d J g (logReg u ε) φ hJ hdim (smoothNear_of_contDiff hg)
      (smoothNear_of_contDiff (contDiff_logReg u hε)) hφ (Or.inl hgc)]
  ring

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsSumMeasurable.proof : PtsSumMeasurable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hfin := fibreFinite K ι P e Ψ hP hΨ
  obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin
  have hind := sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs
  have hsheet : ∀ m, ∀ y ∈ B m, IsSheet P Ψ y (segre (γ m y)) (γ m) := fun m y hy =>
    ⟨rfl, Filter.eventually_of_mem ((hBo m).mem_nhds hy) fun y' hy' => hlift m y' hy'⟩
  have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
    (hlift m y hy).1.continuousAt.continuousWithinAt
  have hO : ∀ m, Set.MapsTo (γ m) (B m) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun m y hy =>
    (hlift m y hy).2.1.1
  have hseg : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd _ fun k _ => continuous_apply _

  set σ : ℕ → (Fin e → ℂ) → ((k : K) → ι k) → ℂ := fun m =>
    (B m).piecewise (fun y => segre (γ m y)) 0 with hσdef
  have hσB : ∀ m, ∀ y ∈ B m, σ m y = segre (γ m y) := fun m y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hσm : ∀ m, Measurable (σ m) := fun m =>
    (hseg.comp_continuousOn (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet

  set a : ℕ → (Fin e → ℂ) → ℝ := fun m => (B m).piecewise
    (fun y => ‖eval (γ m y) (map (Int.castRingHom ℂ) s)‖) 0 with hadef
  set b : ℕ → (Fin e → ℂ) → ℝ := fun m => (B m).piecewise (fun y => A.h (γ m y)) 1 with hbdef
  have ham : ∀ m, Measurable (a m) := fun m =>
    ((continuous_norm.comp (MvPolynomial.continuous_eval _)).comp_continuousOn
      (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet
  have hbm : ∀ m, Measurable (b m) := fun m =>
    ((ContDiffOn.continuousOn hA).comp (hγc m) (hO m)).measurable_piecewise continuousOn_const
      (hBo m).measurableSet
  set dens : ℕ → (Fin e → ℂ) → ℝ := fun m y =>
    Real.log (a m y / b m y) * maDensity (fun j y' => pot L j (γ m y')) y with hddef
  have hdm : ∀ m, Measurable (dens m) := fun m =>
    (Real.measurable_log.comp ((ham m).div (hbm m))).mul (PtsSumMeasurable.measurable_maDensity _)
  have hdens : ∀ m, ∀ y ∈ B m,
      dens m y = logNorm A s (γ m y) * maDensity (fun j y' => pot L j (γ m y')) y := by
    intro m y hy
    simp only [hddef, hadef, hbdef, Set.piecewise_eq_of_mem _ _ _ hy, logNorm]

  set S : ℕ → Set (Fin e → ℂ) := fun m =>
    {y | y ∈ B m ∧ ∀ m' < m, ¬ (y ∈ B m' ∧ σ m' y = σ m y)} with hSdef
  have hSm : ∀ m, MeasurableSet (S m) := by
    intro m
    have : S m = B m ∩ ⋂ m' ∈ Finset.range m, (B m' ∩ {y | σ m' y = σ m y})ᶜ := by
      ext y
      simp [hSdef]
      intro _
      constructor
      · intro h i hi
        by_cases hb : y ∈ B i
        · exact Or.inr (h i hi hb)
        · exact Or.inl hb
      · intro h i hi hb
        exact (h i hi).resolve_left (not_not.mpr hb)
    rw [this]
    exact (hBo m).measurableSet.inter (Finset.measurableSet_biInter _ fun m' _ =>
      ((hBo m').measurableSet.inter (measurableSet_eq_fun (hσm m') (hσm m))).compl)
  set f : ℕ → (Fin e → ℂ) → ℝ := fun m => (S m).indicator (dens m) with hfdef
  have hfm : ∀ m, Measurable (f m) := fun m => (hdm m).indicator (hSm m)
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ m ∈ Finset.range N, f m y)
    (fun N => (Finset.measurable_sum _ fun m _ => hfm m).aestronglyMeasurable) ?_
  filter_upwards [hind] with y hy

  have hterm : ∀ m, y ∈ S m → f m y = sheetDensity P Ψ (pot L) (logNorm A s) y (σ m y) := by
    intro m hm
    have hsh := hsheet m y hm.1
    rw [← hσB m y hm.1] at hsh
    have hex : ∃ γ', IsSheet P Ψ y (σ m y) γ' := ⟨_, hsh⟩
    rw [hfdef]
    simp only
    rw [Set.indicator_of_mem hm, hdens m y hm.1]
    unfold sheetDensity
    rw [dite_eq_left hex]
    exact (hy _ _ _ hex.choose_spec hsh).symm
  have hmemF : ∀ m, y ∈ S m → σ m y ∈ (hfin y).toFinset := by
    intro m hm
    rw [Set.Finite.mem_toFinset, hσB m y hm.1]
    exact ⟨γ m y, (hlift m y hm.1).2.1, rfl, (hlift m y hm.1).2.2⟩
  have hfy : ∀ m, (∑ w ∈ (hfin y).toFinset, if σ m y = w then f m y else 0) = f m y := by
    intro m
    rw [Finset.sum_ite_eq]
    by_cases hm : y ∈ S m
    · rw [if_pos (hmemF m hm)]
    · split_ifs
      · rfl
      · rw [hfdef]
        simp only
        rw [Set.indicator_of_notMem hm]
  have hev : ∀ w ∈ (hfin y).toFinset, ∀ᶠ N in atTop,
      sheetDensity P Ψ (pot L) (logNorm A s) y w =
        ∑ m ∈ Finset.range N, if σ m y = w then f m y else 0 := by
    intro w _
    by_cases hex : ∃ γ', IsSheet P Ψ y w γ'
    · obtain ⟨γ', hγ'⟩ := hex
      have hP' : ∃ m, y ∈ B m ∧ σ m y = w := by
        obtain ⟨m, hm, hmw⟩ := hcov y w γ' hγ'
        exact ⟨m, hm, (hσB m y hm).trans hmw⟩
      obtain ⟨hm1B, hm1w⟩ := Nat.find_spec hP'
      have hm1S : y ∈ S (Nat.find hP') :=
        ⟨hm1B, fun m' hm' h => Nat.find_min hP' hm' ⟨h.1, h.2.trans hm1w⟩⟩
      filter_upwards [eventually_gt_atTop (Nat.find hP')] with N hN
      rw [Finset.sum_eq_single_of_mem (Nat.find hP') (Finset.mem_range.2 hN), if_pos hm1w,
        hterm _ hm1S, hm1w]
      intro m _ hne
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · exfalso
          have hle : Nat.find hP' ≤ m := Nat.find_min' hP' ⟨hmS.1, hmw⟩
          exact hmS.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ⟨hm1B, hm1w.trans hmw.symm⟩
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
    · have h0 : sheetDensity P Ψ (pot L) (logNorm A s) y w = 0 := by
        unfold sheetDensity
        rw [dite_eq_right hex]
      refine Eventually.of_forall fun N => ?_
      rw [h0]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · have hsh := hsheet m y hmS.1
          rw [← hσB m y hmS.1, hmw] at hsh
          exact absurd ⟨_, hsh⟩ hex
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
  have hsum : ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w =
      ∑ w ∈ (hfin y).toFinset, sheetDensity P Ψ (pot L) (logNorm A s) y w :=
    finsum_mem_eq_finite_toFinset_sum _ (hfin y)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(eventually_all_finset _).2 hev] with N hN
  rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => hfy m

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (segre)

namespace SegrePartition

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def segreSq (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : ℝ := ‖segre z i‖ ^ 2

def segreSqSum (z : (Σ k, ι k) → ℂ) : ℝ := ∑ i, segreSq z i

def numIdx (ι : K → Type*) [∀ k, Fintype (ι k)] : ℝ := Fintype.card ((k : K) → ι k)

def bump (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : ℝ :=
  Real.smoothTransition (2 * numIdx ι * (segreSq z i / segreSqSum z) - 1)


open Classical in
def rho (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if 0 < segreSqSum z then bump z i / ∑ j, bump z j else 1 / numIdx ι

omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem segreSq_nonneg (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : 0 ≤ segreSq z i :=
  sq_nonneg _

omit [DecidableEq K] in
theorem contDiff_segreSq (i : (k : K) → ι k) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segreSq z i) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segre z i) :=
    contDiff_prod fun k _ => contDiff_apply ℝ (fun _ => ℂ) (⟨k, i k⟩ : Σ k, ι k)
  exact (contDiff_norm_sq ℝ).comp h

theorem contDiff_segreSqSum :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segreSqSum z) :=
  ContDiff.sum fun i _ => contDiff_segreSq i

theorem segreSqSum_pos {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < segreSqSum z := by
  choose i hi using hz
  have h : segre z i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi k
  exact Finset.sum_pos' (fun j _ => segreSq_nonneg z j)
    ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr h) 2⟩


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem segre_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segre (fun p => c p.1 * z p) i = (∏ k, c k) * segre z i :=
  Finset.prod_mul_distrib

omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem segreSq_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segreSq (fun p => c p.1 * z p) i = ‖∏ k, c k‖ ^ 2 * segreSq z i := by
  simp only [segreSq, segre_smul, norm_mul, mul_pow]

theorem segreSqSum_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segreSqSum (fun p => c p.1 * z p) = ‖∏ k, c k‖ ^ 2 * segreSqSum z := by
  simp only [segreSqSum, segreSq_smul, Finset.mul_sum]

theorem exists_bump_pos (hN : 0 < numIdx ι) {z : (Σ k, ι k) → ℂ} (hS : 0 < segreSqSum z) :
    ∃ j, 0 < bump z j := by
  by_contra h
  push Not at h
  have hle : ∀ j, segreSq z j ≤ segreSqSum z / (2 * numIdx ι) := by
    intro j
    have h1 : 2 * numIdx ι * (segreSq z j / segreSqSum z) - 1 ≤ 0 := by
      by_contra h2
      exact absurd (Real.smoothTransition.pos_of_pos (lt_of_not_ge h2)) (not_lt.mpr (h j))
    rw [le_div_iff₀ (by positivity)]
    have h3 : 2 * numIdx ι * segreSq z j / segreSqSum z ≤ 1 := by
      rw [mul_div_assoc]; linarith
    rw [div_le_one hS] at h3
    linarith
  have hsum : segreSqSum z ≤ numIdx ι * (segreSqSum z / (2 * numIdx ι)) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => segreSq z j) _ fun j _ => hle j
    rw [Finset.card_univ, nsmul_eq_mul] at this
    exact this
  have h4 : numIdx ι * (segreSqSum z / (2 * numIdx ι)) = segreSqSum z / 2 := by
    field_simp
  linarith

theorem bump_sum_pos (hN : 0 < numIdx ι) {z : (Σ k, ι k) → ℂ} (hS : 0 < segreSqSum z) :
    0 < ∑ j, bump z j := by
  obtain ⟨j, hj⟩ := exists_bump_pos hN hS
  exact Finset.sum_pos' (fun i _ => Real.smoothTransition.nonneg _) ⟨j, Finset.mem_univ _, hj⟩

theorem contDiffOn_bump (i : (k : K) → ι k) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => bump z i)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  refine (Real.smoothTransition.contDiff (n := ⊤)).comp_contDiffOn ?_
  refine ContDiffOn.sub (contDiffOn_const.mul ?_) contDiffOn_const
  exact ContDiffOn.div (contDiff_segreSq i).contDiffOn contDiff_segreSqSum.contDiffOn
    fun z hz => (segreSqSum_pos hz).ne'

theorem bump_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (i : (k : K) → ι k) :
    bump (fun p => c p.1 * z p) i = bump z i := by
  have ha : ‖∏ k, c k‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k))
  simp only [bump, segreSq_smul, segreSqSum_smul, mul_div_mul_left _ _ ha]

theorem isDegZeroSmooth_rho (hN : 0 < numIdx ι) (i : (k : K) → ι k) :
    IsDegZeroSmooth (rho (ι := ι) i) := by
  refine ⟨?_, fun c z hc => ?_⟩
  · have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : (Σ k, ι k) → ℂ => bump z i / ∑ j, bump z j) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
      ContDiffOn.div (contDiffOn_bump i) (ContDiffOn.sum fun j _ => contDiffOn_bump j)
        fun z hz => (bump_sum_pos hN (segreSqSum_pos hz)).ne'
    refine hf.congr fun z hz => ?_
    simp only [rho, if_pos (segreSqSum_pos hz)]
  · have ha : 0 < ‖∏ k, c k‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)) 2
    have hS : 0 < segreSqSum (fun p => c p.1 * z p) ↔ 0 < segreSqSum z := by
      rw [segreSqSum_smul]; exact mul_pos_iff_of_pos_left ha
    simp only [rho, hS, bump_smul c z hc]

theorem sum_rho (hN : 0 < numIdx ι) (z : (Σ k, ι k) → ℂ) : ∑ i, rho (ι := ι) i z = 1 := by
  by_cases hS : 0 < segreSqSum z
  · simp only [rho, if_pos hS]
    rw [← Finset.sum_div, div_self (bump_sum_pos hN hS).ne']
  · simp only [rho, if_neg hS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [numIdx] at hN ⊢
    field_simp

theorem rho_eq_zero (hN : 0 < numIdx ι) (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ)
    (h : ‖segre z i‖ < (Real.sqrt (2 * numIdx ι))⁻¹ * ‖segre z‖) : rho i z = 0 := by
  have hδ : 0 < (Real.sqrt (2 * numIdx ι))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hw : 0 < ‖segre z‖ := by
    by_contra h0
    have : ‖segre z‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    rw [this, mul_zero] at h
    exact absurd h (not_lt.mpr (norm_nonneg _))
  have hle : ‖segre z‖ ≤ Real.sqrt (segreSqSum z) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun j => segreSq z j) (fun j _ => segreSq_nonneg z j)
      (Finset.mem_univ j)
  have hS : 0 < segreSqSum z := Real.sqrt_pos.mp (lt_of_lt_of_le hw hle)
  have h1 : ‖segre z i‖ < (Real.sqrt (2 * numIdx ι))⁻¹ * Real.sqrt (segreSqSum z) :=
    lt_of_lt_of_le h (mul_le_mul_of_nonneg_left hle hδ.le)
  have h2 : segreSq z i < segreSqSum z / (2 * numIdx ι) := by
    have h3 := pow_lt_pow_left₀ h1 (norm_nonneg _) two_ne_zero
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hS.le] at h3
    rw [segreSq]
    calc ‖segre z i‖ ^ 2 < (2 * numIdx ι)⁻¹ * segreSqSum z := h3
      _ = segreSqSum z / (2 * numIdx ι) := by rw [inv_mul_eq_div]
  have hb : bump z i = 0 := by
    refine Real.smoothTransition.zero_of_nonpos ?_
    rw [lt_div_iff₀ (by positivity)] at h2
    have h4 : 2 * numIdx ι * (segreSq z i / segreSqSum z) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hS]
      linarith
    linarith
  simp only [rho, if_pos hS, hb, zero_div]

end SegrePartition

theorem SegrePartition.proof : SegrePartition.Statement := by
  intro K _ _ ι _ hne
  have hN : 0 < SegrePartition.numIdx ι := by
    rw [SegrePartition.numIdx, Nat.cast_pos]
    exact Fintype.card_pos
  exact ⟨(Real.sqrt (2 * SegrePartition.numIdx ι))⁻¹,
    inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)), SegrePartition.rho,
    SegrePartition.isDegZeroSmooth_rho hN, SegrePartition.sum_rho hN,
    SegrePartition.rho_eq_zero hN⟩

end GroundTheory.Heights₂.Heights
end
end
