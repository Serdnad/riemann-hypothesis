module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.Intersections.OneNotMemOfIsPrime
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
import Mathlib.Data.ENat.BigOperators
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def eulerDirs {n : ℕ} (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) where
  carrier := {x | ∃ c : K → ℂ, fderiv ℂ F y x = bsmul c (F y)}
  add_mem' := by
    rintro x x' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c + c', by rw [map_add (f := _), hc, hc']; funext p; simp [bsmul, add_mul]⟩
  zero_mem' := ⟨0, by rw [map_zero]; funext p; simp [bsmul]⟩
  smul_mem' := by
    rintro a x ⟨c, hc⟩
    exact ⟨a • c, by rw [map_smul, hc]; funext p; simp [bsmul, mul_assoc]⟩

theorem eulerDirs_finrank (hR : pointFormRank_holds.Statement) {Q : Ideal (MRing ι)} {d n : ℕ} (hQ : IsArithVar Q d)
    {F : (Fin n → ℂ) → (Σ k, ι k) → ℂ} {y : Fin n → ℂ} (hF : AnalyticAt ℂ F y)
    (hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts Q) : n < Module.finrank ℂ (eulerDirs F y) + d := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (eulerDirs F y)
  have hsum := Submodule.finrank_add_eq_of_isCompl hU
  rw [Module.finrank_fin_fun] at hsum
  have hdm : d ≤ Module.finrank ℂ U := by omega
  set bU := Module.finBasis ℂ U
  let Mlin : (Fin (Module.finrank ℂ U) → ℂ) →ₗ[ℂ] (Fin n → ℂ) := U.subtype ∘ₗ bU.equivFun.symm.toLinearMap
  let M : (Fin (Module.finrank ℂ U) → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap Mlin
  have hMU : ∀ x, M x ∈ U := fun x => Submodule.coe_mem (bU.equivFun.symm x)
  have hMinj : Function.Injective M := fun a b h => bU.equivFun.symm.injective (Subtype.ext h)
  have hA : HasFDerivAt (fun y' => y + M y') M 0 := (M.hasFDerivAt).const_add y
  have hy : y + M 0 = y := by rw [map_zero, add_zero]
  have hF' : AnalyticAt ℂ F (y + M 0) := by rw [hy]; exact hF
  have hGa : AnalyticAt ℂ (fun y' => F (y + M y')) 0 :=
    hF'.comp (f := fun y' => y + M y') (analyticAt_const.add (M.analyticAt 0))
  have hGQ : ∀ᶠ y' in 𝓝 (0 : Fin (Module.finrank ℂ U) → ℂ), F (y + M y') ∈ mcPts Q := by
    have ht : Tendsto (fun y' => y + M y') (𝓝 0) (𝓝 y) := by
      have := hA.continuousAt.tendsto
      rwa [hy] at this
    exact ht.eventually hFQ
  obtain ⟨x, hx, c, hxc⟩ := hR K ι Q d _ (fun y' => F (y + M y')) 0 hQ hdm hGa hGQ
  have hFd : HasFDerivAt F (fderiv ℂ F y) (y + M 0) := by rw [hy]; exact hF.differentiableAt.hasFDerivAt
  have hGd : HasFDerivAt (fun y' => F (y + M y')) ((fderiv ℂ F y).comp M) 0 :=
    hFd.comp (f := fun y' => y + M y') 0 hA
  rw [hGd.fderiv, ContinuousLinearMap.comp_apply, hy] at hxc
  have hmem : M x ∈ eulerDirs F y ⊓ U := ⟨⟨c, hxc⟩, hMU x⟩
  rw [hU.inf_eq_bot, Submodule.mem_bot] at hmem
  exact hx (hMinj (by rw [hmem, map_zero]))

theorem map_star_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    M.map (starRingEnd ℂ) *ᵥ x = star (M *ᵥ star x) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

theorem PFIntZero.maDensity_eq_zero (hR : pointFormRank_holds.Statement)
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {d r : ℕ}
    {L : Fin d → HermLine ι} {L' : Fin d → HermLine ι'} (N : Fin r → HermLine ι') (hv : IsBlockMap κ v)
    (hQ : IsArithVar (imageZ v P') d) (hL : ∀ j, IsSmoothHerm (L j))
    (hLL : ∀ j, IsPullHerm κ v (L j) (L' j))
    {Ψ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (d + r + 1) → ℂ)} {y : Fin (d + r) → ℂ}
    {w : ((k : K') → ι' k) → ℂ} {γ : (Fin (d + r) → ℂ) → (Σ k', ι' k') → ℂ} (hγ : IsSheet P' Ψ y w γ) :
    maDensity (fun j y' => Real.log ((Fin.append L' N j).h (γ y'))) y = 0 := by
  set F : (Fin (d + r) → ℂ) → (Σ k, ι k) → ℂ := fun y' p => γ y' (v p) with hF
  have hγa : AnalyticAt ℂ γ y := sheet_analyticAt osgood hγ
  have hFa : AnalyticAt ℂ F y := analyticAt_pi_iff.mpr fun p => analyticAt_coord hγa (v p)
  have hFy : ∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0 := blocks_ne_zero_restrict hv hγ.2.self_of_nhds.2.1.1
  have hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts (imageZ v P') := by
    filter_upwards [hγ.2] with y' h
    refine ⟨blocks_ne_zero_restrict hv h.2.1.1, fun f hf => ?_⟩
    have h0 := h.2.1.2 _ (Ideal.mem_comap.mp hf)
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h0
    exact h0
  set A : Fin (d + r) → Matrix (Fin (d + r)) (Fin (d + r)) ℂ :=
    fun j => cxHessian (fun y' => Real.log ((Fin.append L' N j).h (γ y'))) y with hAdef
  have hker : ∀ k ∈ Finset.univ.map (Fin.castAddEmb r), ∀ x ∈ eulerDirs F y,
      (A k).map (starRingEnd ℂ) *ᵥ x = 0 := by
    intro k hk x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hk
    obtain ⟨c, hc⟩ := hx
    have hpot : (fun y' => Real.log ((Fin.append L' N (Fin.castAddEmb r j)).h (γ y'))) =
        fun y' => Real.log ((L j).h (F y')) := by
      funext y'
      rw [Fin.coe_castAddEmb, Fin.append_left, (hLL j).2]
    have h := pointFormEuler_holds.proof K ι (L j) (d + r) F y x c (hL j) hFa hFy hc
    rw [map_star_mulVec, hAdef]
    simp only
    rw [hpot, h, star_zero]
  have hmix := mixedDisc_eq_zero_of_ker (fun k => (A k).map (starRingEnd ℂ)) (eulerDirs F y) _
    (by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]; exact eulerDirs_finrank hR hQ hFa hFQ) hker
  rw [mixedDisc_map_star, map_eq_zero] at hmix
  show _ * _ * (mixedDisc A).re = 0
  rw [hmix, Complex.zero_re, mul_zero]

theorem PFIntZero.proof (hR : pointFormRank_holds.Statement) : PFIntZero.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r L L' N A s hv _ hQ hL hLL
  classical
  unfold arInt ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P' hΨ.choose (fun j z => Real.log ((Fin.append L' N j).h z)) (logNorm A s) y w
        = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · exact mul_eq_zero_of_right _ (PFIntZero.maDensity_eq_zero hR N hv hQ hL hLL hγ.choose_spec)
      · rfl
    simp [h0]
  · rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem VerticalClosedPoints.proof (hE : regularityEmbedding_holds.Statement) (hV : VerticalEmbedding.Statement) : VerticalClosedPoints.Statement := by
  intro K _ ι _ P f g a R hP hf hg hfP hgP hR hRu
  have : P.IsPrime := hP.2.1.1
  obtain ⟨x, hx⟩ := exists_funField_mul_eq hf hg hgP
  obtain ⟨e, he⟩ := hE K ι P R hP hR hRu
  rw [hV K ι P f g a x hP hf hg hfP hgP hx]
  have hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (a k : ℤ))) g :=
    ⟨a, fun _ => rfl, hg, hgP⟩
  have key : ∀ t : R, Real.log ‖e t x‖ =
      Real.log (‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) f)‖ /
        ‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g)‖) := by
    intro t
    have hg0 := eval_ne_zero_of_dimOne arithVarZero hP hA (hR t t.2)
    rw [← he t f g a hf hg hgP x hx, norm_mul, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hg0)]
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ key]
  exact Finset.sum_coe_sort R (fun t => Real.log (‖eval t (map (Int.castRingHom ℂ) f)‖ /
    ‖eval t (map (Int.castRingHom ℂ) g)‖))

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem PFSecRed.exists_form_not_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n) (c : K → ℕ) :
    ∃ s : MRing ι, IsMultiHomog s c ∧ s ∉ P :=
  ⟨∏ k, (X ⟨k, (hP.2.1.2.2 k).choose⟩ : MRing ι) ^ c k, AvoidRing.isMultiHomog_coordProd _ c,
    AvoidRing.coordProd_not_mem hP.2.1.1 _ (fun k => (hP.2.1.2.2 k).choose_spec) c⟩

theorem PFSecRed.proof
    (hMult : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      MultilinStatement F ι)
    (hDim : FibreDimStatement) : PFSecRed.Statement := by
  intro I hI r hsec K _ ι _ K' _ ι' _ κ v P' d G J L L' N hv hP' hP hJ hL hL' hN

  let c : K' → ℕ := fun k => (-(N (Fin.last r)).a k).toNat
  let H : HermLine ι' := HermLine.sqMetric c
  let A : HermLine ι' := (N (Fin.last r)).tensor H
  have hHs : IsSmoothHerm H := isSmoothHerm_sqMetric c
  have hAs : IsSmoothHerm A := isSmoothHerm_tensor (hN _) hHs
  let a : K' → ℕ := fun k => ((N (Fin.last r)).a k + c k).toNat
  have hAa : ∀ k, A.a k = a k := by
    intro k
    show (N (Fin.last r)).a k + ((-(N (Fin.last r)).a k).toNat : ℤ) =
      (((N (Fin.last r)).a k + ((-(N (Fin.last r)).a k).toNat : ℤ)).toNat : ℤ)
    omega
  have hHa : ∀ k, H.a k = c k := fun k => rfl
  obtain ⟨sA, hsA, hsAP⟩ := PFSecRed.exists_form_not_mem hP' a
  obtain ⟨sH, hsH, hsHP⟩ := PFSecRed.exists_form_not_mem hP' c
  have hsnoc : ∀ B : HermLine ι', IsSmoothHerm B →
      ∀ j, IsSmoothHerm ((Fin.snoc (Fin.init N) B : Fin (r + 1) → HermLine ι') j) := by
    intro B hB j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using hB
    · rw [Fin.snoc_castSucc]; exact hN _
  have e1 := hsec K ι K' ι' κ v P' d G J L L' (Fin.snoc (Fin.init N) A) sA a hv hP' hP hJ hL hL'
    (hsnoc A hAs) (by simpa using hAa) hsA hsAP
  have e2 := hsec K ι K' ι' κ v P' d G J L L' (Fin.snoc (Fin.init N) H) sH c hv hP' hP hJ hL hL'
    (hsnoc H hHs) (by simpa using hHa) hsH hsHP

  have hM : ∀ j, IsSmoothHerm (Fin.append L' (Fin.init N) j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact IsPullHerm.isSmoothHerm hv (hL' i) (hL i)
    | right i => rw [Fin.append_right]; exact hN _
  have hadd := (hI K' ι').2.1 P' (d + r) (Fin.append L' (Fin.init N)) (N (Fin.last r)) H hP' hM (hN _) hHs
  rw [← Fin.append_snoc, ← Fin.append_snoc, ← Fin.append_snoc, Fin.snoc_init_self] at hadd

  have hV := hDim K ι K' ι' κ v P' d (r + 1) G hv hP' hP
  have hJadd := hMult G.Φ (FibreBlock κ) (fibreIdx ι' κ) J hJ (_root_.ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (r + 1)
    (Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a)) (Fin.last r)
    (fibreDeg κ (N (Fin.last r)).a) (fibreDeg κ H.a) hV
  simp only [Fin.update_snoc_last] at hJadd
  have f0 : (fun j => fibreDeg κ (N j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  have f1 : (fun j => fibreDeg κ ((Fin.snoc (Fin.init N) A : Fin (r + 1) → HermLine ι') j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a + fibreDeg κ H.a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]; rfl
    · simp [Fin.init]
  have f2 : (fun j => fibreDeg κ ((Fin.snoc (Fin.init N) H : Fin (r + 1) → HermLine ι') j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ H.a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [Fin.init]
  rw [f1] at e1
  rw [f2] at e2
  have key : I K' ι' P' (d + (r + 1)) (Fin.append L' N) =
      I K' ι' P' (d + (r + 1)) (Fin.append L' (Fin.snoc (Fin.init N) A)) -
        I K' ι' P' (d + (r + 1)) (Fin.append L' (Fin.snoc (Fin.init N) H)) := by
    rw [eq_sub_iff_add_eq]
    exact hadd.symm
  rw [f0, key, e1, e2, hJadd]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocResidueDeg.proof (hDim : SemilocResidueFibreDim.Statement) (hAdj : SemilocResidueAdjoin.Statement) :
    SemilocResidueDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW W' hW' _ G' J' hJ
  have hrel : ∀ k', ∃ i, (X ⟨k', i⟩ : MRing ι') ∉ W' := hW'.1.2.2
  choose i' hi' using hrel
  have hfib : IsProjVarF (_root_.ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0 := hDim K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G'
  have hz : ∀ k : FibreBlock κ, G'.x' ⟨k.1, i' k.1⟩ ≠ 0 := by
    intro k h0
    apply hi' k.1
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h0
  have hj : IsChart (_root_.ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') (fun k => i' k.1) := by
    intro k hk
    apply hz k
    rw [_root_.ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X] at hk
    exact hk
  refine ⟨_, hAdj K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G' i' hi', ?_⟩
  rw [hJ.1 _ Fin.elim0 _ hfib hj]
  exact congrArg _ (ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ' (fun q => G'.x' ⟨q.1.1, q.2⟩)
    (fun k => i' k.1) hz hfib.1.2.1).symm

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocLengthSum.proof (h₁ : SemilocFinite.Statement) (h₂ : SemilocMaxIdeals.Statement)
    (h₃ : SemilocResidueDeg.Statement) (h₄ : FibreDivSupp.Statement) (h₅ : LocRingDimOne.Statement)
    (h₆ : FibreOverFinite.Statement) :
    SemilocLengthSum.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy hE
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hfin := h₆ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  obtain ⟨hmax, hinj, hcov⟩ := h₂ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  have : IsLocalRing (locRing (imageZ v P') W) := (h₅ K ι (imageZ v P') s α W hPn.2.1 hs hsP hW).2.1
  have : Module.Finite (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) :=
    (h₁ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW).1
  let _ : Fintype (fibreOver v P' W) := hfin.fintype
  have hloc : ∀ W' : fibreOver v P' W, IsLocalRing (locRing P' W'.1) := fun W' =>
    haveI := W'.2.1.1; regularityLocalFlat_holds.isLocalRing W'.2.2.1
  let _ : ∀ W' : fibreOver v P' W, Algebra (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1) :=
    fun W' => (semiToLoc P' _ W'.1 W'.2).toAlgebra
  have key := FieldNumbers.FiniteAlgebraLengthSum.proof.{0} (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W))
    (fibreOver v P' W) (fun W' => semiMaxIdeal P' _ W'.1 W'.2) (fun W' => (hmax W'.1 W'.2).1)
    (fun W₁ W₂ h => Subtype.ext (hinj W₁.1 W₂.1 W₁.2 W₂.2 h))
    (fun M hM => by obtain ⟨W', hW', h⟩ := hcov M hM; exact ⟨⟨W', hW'⟩, @h (hloc ⟨W', hW'⟩)⟩)
    (fun W' => locRing P' W'.1) (fun W' => (hmax W'.1 W'.2).2) y

  refine ⟨hfin, ?_⟩
  have hyne : (y : FractionRing (MRing ι ⧸ imageZ v P')) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hy
    exact hsP hy
  have hs' : rename v s ∉ P' := hsP
  have hterm : ∀ W' : fibreOver v P' W,
      Ring.ord (locRing P' W'.1) (algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
          (algebraMap (locRing (imageZ v P') W) _ y)) *
        Module.length (locRing (imageZ v P') W)
          (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' _ W'.1 W'.2) ≠ ⊤ ∧
      (((Ring.ord (locRing P' W'.1) (algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
          (algebraMap (locRing (imageZ v P') W) _ y)) *
        Module.length (locRing (imageZ v P') W)
          (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' _ W'.1 W'.2)).toNat : ℕ) : ℤ) =
        if rename v s ∈ W'.1 then
          ((Module.length (locRing P' W'.1) (locRing P' W'.1 ⧸ locIdeal P' W'.1 (fracMapZ v P' y))).toNat : ℤ) *
            E W'.1 else 0 := by
    intro W'
    obtain ⟨hW'p, hPW', hW'i⟩ := W'.2
    have := hW'p.1
    set x := algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
      (algebraMap (locRing (imageZ v P') W) _ y) with hxdef
    have hx : (x : FractionRing (MRing ι' ⧸ P')) = fracMapZ v P' y := by
      rw [hxdef, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, semiToLoc_coe, locToSemiloc_coe]
    have hord : Ring.ord (locRing P' W'.1) x =
        Module.length (locRing P' W'.1) (locRing P' W'.1 ⧸ locIdeal P' W'.1 (fracMapZ v P' y)) := by
      have hI : locIdeal P' W'.1 (fracMapZ v P' y) = Ideal.span {x} := by
        rw [locIdeal, ← hx]
        congr 1
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
        exact Subtype.ext_iff.symm
      rw [Ring.ord, hI]
    split_ifs with hsW'
    · obtain ⟨G', J', hJ', hEW'⟩ := hE W'.1 W'.2 hsW'
      obtain ⟨d, hd, hdE⟩ := h₃ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW W'.1 W'.2 G' J' hJ'
      have hdiv : W'.1 ∈ divSupp P' (rename v s) :=
        ((h₄ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW W'.1).1 ⟨W'.2, hsW'⟩).1
      obtain ⟨hN, -, hdim⟩ := h₅ K' ι' P' (rename v s) (Function.extend κ α 0) W'.1 hP'.2.1
        (rename_isMultiHomog hv hs) hs' hdiv
      have : Ring.KrullDimLE 1 (locRing P' W'.1) := by
        rw [Ring.krullDimLE_iff, hdim]
        rfl
      have hx0 : x ≠ 0 := fun h =>
        (map_ne_zero (fracMapZ v P')).mpr hyne (by rw [← hx, h, ZeroMemClass.coe_zero])
      have hfinord := Ring.ord_ne_top (R := locRing P' W'.1) (mem_nonZeroDivisors_of_ne_zero hx0)
      rw [hd, ← hord]
      refine ⟨WithTop.mul_ne_top hfinord (ENat.natCast_ne_top d), ?_⟩
      rw [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul, hdE, hEW']
    · have ht' : rename v t ∉ W'.1 := fun h => htW (hW'i ▸ h)
      have hxe : (x : FractionRing (MRing ι' ⧸ P')) * regularityLocalFlat_holds.fracHom P' (rename v t) =
          regularityLocalFlat_holds.fracHom P' (rename v s) := by
        rw [hx, regularityLocalFlat_holds.fracHom_apply, regularityLocalFlat_holds.fracHom_apply, ← fracMapZ_algebraMap, ← fracMapZ_algebraMap,
          ← map_mul, hy]
      have hu : IsUnit x := (regularityLocalFlat_holds.isUnit_iff hPW' x (rename_isMultiHomog hv hs) (rename_isMultiHomog hv ht) ht'
        hxe).mpr hsW'
      rw [Ring.ord_of_isUnit hu, zero_mul]
      simp
  have hset : {W' | W' ∈ fibreOver v P' W ∧ rename v s ∈ W'} =
      ↑(hfin.toFinset.filter (fun W' => rename v s ∈ W')) := by
    ext
    simp
  have hsum := ENat.sum_ne_top.mpr fun W' (_ : W' ∈ Finset.univ) => (hterm W').1
  rw [key]
  refine ⟨_, (ENat.natCast_toNat hsum).symm, ?_⟩
  rw [ENat.toNat_sum fun W' _ => (hterm W').1, Nat.cast_sum, hset, finsum_mem_coe_finset, Finset.sum_filter,
    Finset.sum_subtype (F := hfin.fintype) hfin.toFinset (fun _ => Set.Finite.mem_toFinset hfin)]
  exact Finset.sum_congr rfl fun W' _ => (hterm W').2

end GroundTheory.Heights₂.Heights.Inter
end
end
