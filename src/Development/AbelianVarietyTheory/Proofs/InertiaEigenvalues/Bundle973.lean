module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle173
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle027
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle016
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle025
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle023
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle015
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle010
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle009
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle970
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle663
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenDirichletHasSumIteratedDeriv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle553
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle964
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle954
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle963
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

namespace GlobalTheory.EqCharGood

theorem existsUnique_mulVec_of_inCell {V K : Type} [CommRing V] [CommRing K] (φ : V →+* K)
    (hφ : Function.Injective φ) {n r : ℕ} (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V)
    (hc : GlobalTheory.Reg.InCell ix u) (cv : Fin n → V) (aK : Fin r → K)
    (h : (u.map φ).mulVec aK = fun i => φ (cv i)) : ∃! a, u.mulVec a = cv := by
  let A : Matrix (Fin r) (Fin r) V := u.submatrix ix id
  have hlow : A.BlockTriangular OrderDual.toDual := fun i j hij => hc.1 i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_lowerTriangular A hlow]
    exact Finset.prod_eq_one fun i _ => hc.2 i
  have hAu : IsUnit A.det := hdet ▸ isUnit_one
  have hAK : IsUnit (A.map φ).det := by
    have e : (A.map φ).det = φ A.det := (RingHom.map_det φ A).symm
    rw [e, hdet, map_one]; exact isUnit_one
  have hinjA : ∀ v w : Fin r → V, A.mulVec v = A.mulVec w → v = w := fun v w hvw => by
    have := congrArg (A⁻¹).mulVec hvw
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  have hinjAK : ∀ v w : Fin r → K, (A.map φ).mulVec v = (A.map φ).mulVec w → v = w := fun v w hvw => by
    have := congrArg ((A.map φ)⁻¹).mulVec hvw
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAK, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  have hrow : ∀ (v : Fin r → V), A.mulVec v = fun i => u.mulVec v (ix i) := fun v => rfl
  let a : Fin r → V := A⁻¹.mulVec (fun i => cv (ix i))
  have ha : A.mulVec a = fun i => cv (ix i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
  have hmap : ∀ (M : Matrix (Fin n) (Fin r) V) (v : Fin r → V),
      (M.map φ).mulVec (fun i => φ (v i)) = fun i => φ (M.mulVec v i) := fun M v => by
    funext i
    exact (RingHom.map_mulVec φ M v i).symm
  have haK : (fun i => φ (a i)) = aK := by
    refine hinjAK _ _ ?_
    have e1 : (A.map φ).mulVec (fun i => φ (a i)) = fun i => φ (cv (ix i)) := by
      funext i
      exact (congrFun (hmap u a) (ix i)).trans (congrArg φ (congrFun ha i))
    rw [e1]
    funext i
    exact (congrFun h (ix i)).symm
  refine ⟨a, ?_, fun a' ha' => hinjA _ _ ((hrow a').trans ((funext fun i => congrFun ha' (ix i)).trans ha.symm))⟩
  funext i
  apply hφ
  have := congrFun (hmap u a) i
  rw [haK, h] at this
  exact this.symm

end GlobalTheory.EqCharGood

namespace GlobalTheory.EqCharGood



theorem inV_of_extIn_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, (letI := io.toAlgebra; ExtIn Y (abLocus Y.t.G) T io y.1.x) → evI y f ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H Dw l Xo c a n f hf la Y hP T io hio y hy
  classical
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hS := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  obtain ⟨k, hk⟩ := exists_factor T io hio
  obtain ⟨y', z, h1, h2, h3, h4⟩ := hy
  have hs : y' ≫ Y.s = spMap (k.comp (la.valuation c.F).valuationSubring.subtype) := by
    have e1 : spMap (algebraMap T.V T.Fr) ≫ (y' ≫ Y.s) =
        spMap (algebraMap T.V T.Fr) ≫ spMap (k.comp (la.valuation c.F).valuationSubring.subtype) := by
      rw [← Category.assoc, ← h3, Category.assoc, GlobalTheory.TraitDataIntrinsic.j_s, ← Category.assoc, h2, sp_comp,
        sp_comp, ← RingHom.comp_assoc, hk]
    obtain ⟨φ, hφ⟩ : ∃ φ : (la.valuation c.F).valuationSubring →+* T.V, y' ≫ Y.s = spMap φ :=
      ⟨(Spec.preimage (y' ≫ Y.s)).hom, by simp [spMap]⟩
    rw [hφ, sp_comp, sp_comp] at e1
    rw [hφ]
    congr 1
    have e2 := CommRingCat.hom_ext_iff.1 (Spec.map_injective e1)
    exact RingHom.ext fun x => hinj (RingHom.congr_fun e2 x)
  let _ : Algebra c.F T.V := k.toAlgebra
  let _ : Algebra c.F T.Fr := io.toAlgebra
  obtain ⟨zV, hzV1, hzV2⟩ := exists_lift Y y' k hs h4
  obtain ⟨J, _, M, hM⟩ := GlobalTheory.Reg.exists_finite_mchart_cover E H Dw l Xo c (la.valuation c.F).valuationSubring _ Y hP
  obtain ⟨j, hj⟩ := hM (y' (IsLocalRing.closedPoint T.V))
  obtain ⟨-, -, h3'⟩ := GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c _ _ Y
  obtain ⟨-, -, -, h4'⟩ := h3' (M j).U (M j).hU
  obtain ⟨f₀, hf₀, -⟩ := h4' T.V y' hj
  obtain ⟨ΛV⟩ := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y (M j) T.V f₀ zV hzV2 (hzV1.trans hf₀.symm)
  have hzj : z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp f₀) ≫ (M j).hU.fromSpec := by
    rw [h3, ← hf₀, ← Category.assoc, sp_comp]
  have hK := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y (M j) T.Fr _ z h2 hzj
  rw [h1] at hK
  obtain ⟨ΛK⟩ := hK
  obtain ⟨g, hg, hgi⟩ := GlobalTheory.Reg.MChart.Lift.exists_coordinates E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1 ΛK
  let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
  have hW : ∀ x, x ∈ W → InV T x := fun x h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h
  choose ix u b huW hu0 hu1 hbt hbd hgub using
    fun τ => GlobalTheory.exists_integral_pivot_decomposition T.Fr W _ _ (g τ) (hgi τ)
  choose u₀' hu₀' using fun τ i j => hW _ (huW τ i j)
  let u₀ : ∀ τ : E →+* ℂ, Matrix (Fin (M j).n) (Fin (Dw.mult τ)) T.V := fun τ => Matrix.of fun i j' => u₀' τ i j'
  have hu₀ : ∀ τ i j', algebraMap T.V T.Fr (u₀ τ i j') = u τ i j' := hu₀'
  have hcell : ∀ τ, GlobalTheory.Reg.InCell (ix τ) (u₀ τ) := fun τ =>
    ⟨fun i j hij => hinj (by rw [hu₀, map_zero]; exact hu0 τ i j hij),
     fun i => hinj (by rw [hu₀, map_one]; exact hu1 τ i)⟩

  have heigMap : ∀ τ (cv : Fin (M j).n → T.V),
      (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun i => algebraMap T.V T.Fr (cv i)) ↔ (M j).Eig f₀ τ cv := by
    intro τ cv
    refine forall_congr' fun a' => ?_
    have key : ∀ i, algebraMap T.V T.Fr ((((M j).ρ a').map f₀).mulVec cv i) =
        ((((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀)).mulVec (fun i => algebraMap T.V T.Fr (cv i))) i :=
      fun i => by rw [RingHom.map_mulVec]; rfl
    have key2 : ∀ i, algebraMap T.V T.Fr ((algebraMap c.F T.V (embK c τ a') • cv) i) =
        (algebraMap c.F T.Fr (embK c τ a') • fun i => algebraMap T.V T.Fr (cv i)) i := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      exact congrArg (· * _) (RingHom.congr_fun hk _)
    constructor
    · intro h
      funext i
      apply hinj
      rw [key, key2]
      exact congrFun h i
    · intro h
      funext i
      rw [← key, ← key2, h]
  have humap : ∀ τ, (u₀ τ).map (algebraMap T.V T.Fr) = u τ := fun τ => Matrix.ext fun i j' => hu₀ τ i j'
  have heigK : ∀ τ i, (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun j' => u τ j' i) := by
    intro τ i a'
    have hgc : ∀ i, (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun j' => g τ j' i) := fun i =>
      (GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK τ _ _ (hg τ i)).mp (y.1.eig τ i)
    have hG := (GlobalTheory.Reg.CellChart.mul_eq_smul_iff_cols (((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀))
      (algebraMap c.F T.Fr (embK c τ a')) (g τ)).mpr fun i => hgc i a'
    have hd : IsUnit (b τ).det := by
      rw [Matrix.det_of_upperTriangular (hbt τ)]
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => hbd τ i).isUnit
    have hU : ((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀) * u τ = algebraMap c.F T.Fr (embK c τ a') • u τ := by
      have e : u τ = g τ * (b τ)⁻¹ := by rw [hgub τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      rw [e, ← Matrix.mul_assoc, hG, Matrix.smul_mul]
    exact (GlobalTheory.Reg.CellChart.mul_eq_smul_iff_cols _ _ _).mp hU i
  have heigV : ∀ τ i, (M j).Eig f₀ τ (fun j' => u₀ τ j' i) := fun τ i =>
    (heigMap τ _).mp (by simpa only [hu₀] using heigK τ i)
  obtain ⟨hv1, hv2, hv3⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK
  have hbasis : ∀ τ cv, (M j).Eig f₀ τ cv → ∃! a, (u₀ τ).mulVec a = cv := by
    intro τ cv hcv
    have hcvK := (heigMap τ cv).mpr hcv
    obtain ⟨w, hw, -⟩ := hv1 (fun i => algebraMap T.V T.Fr (cv i))
    have htan := hv2 _ _ hw
    have heig := (GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK τ _ _ hw).mpr hcvK
    obtain ⟨a0, ha0, -⟩ := y.1.basis τ w htan heig
    have hv := (GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK _ (fun i j' => g τ j' i) (y.1.u τ) a0 w
      (hg τ)).mp ha0
    have heq : (∑ i, a0 i • fun j' => g τ j' i) = fun i => algebraMap T.V T.Fr (cv i) := (hv3 w htan).unique hv hw
    refine GlobalTheory.EqCharGood.existsUnique_mulVec_of_inCell (algebraMap T.V T.Fr) hinj (ix τ) (u₀ τ) (hcell τ) cv
      ((b τ).mulVec a0) ?_
    rw [humap, Matrix.mulVec_mulVec, ← hgub τ, ← heq]
    funext j'
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  obtain ⟨yV, -, hyV⟩ := GlobalTheory.Reg.exists_frPt_tie hS E H Dw l Xo c _ _ Y (M j) T.V f₀ _ ΛV u₀ heigV hbasis
  let φ : T.V →ₐ[c.F] T.Fr := ⟨algebraMap T.V T.Fr, fun x => RingHom.congr_fun hk x⟩
  obtain ⟨zK, hzK⟩ := hE.bc _ _ φ yV
  have htK := GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c _ _ Y (M j) T.V T.Fr f₀ φ u₀ yV zK hyV hzK
  have hint : Integral T io zK := GlobalTheory.Reg.tie_integral hS E H Dw l Xo c _ _ Y (M j) hP T io f₀ ix u₀ hcell zK
    (GlobalTheory.Reg.CellChart.tie_congr htK (fun _ => rfl) (fun _ _ _ => rfl))
  have htu : (M j).Comparison₂ ((algebraMap T.V T.Fr).comp f₀) u zK :=
    GlobalTheory.Reg.CellChart.tie_congr htK (fun _ => rfl) (fun τ i j' => hu₀ τ i j')
  obtain ⟨t, ht⟩ := GlobalTheory.Reg.frBor_of_tie E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1 zK ΛK u b
    (GlobalTheory.Reg.CellChart.lift_point_unique htu.choose ΛK) (fun τ => ⟨hbt τ, hbd τ⟩)
    (by rw [show (fun τ => u τ * b τ) = g from funext fun τ => (hgub τ).symm]; exact hg) htu
  show InV T (evI y f)
  rw [inV_of_frBor hf y ⟨zK, hE.test _ zK, hint⟩ t ht]
  show InV T (evR Xo c f zK)
  rw [(GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf T.V).1 T.Fr φ yV zK hzK]
  exact ⟨_, rfl⟩

end GlobalTheory.EqCharGood
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSNonvan

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem analyticAt_dslope' {f : ℂ → ℂ} {ξ x : ℂ} (hx : AnalyticAt ℂ f x) : AnalyticAt ℂ (dslope f ξ) x := by
  by_cases h : x = ξ
  · subst h
    obtain ⟨p, hp⟩ := hx
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  · have h1 : AnalyticAt ℂ (fun t => (t - ξ)⁻¹ * (f t - f ξ)) x :=
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 h)).mul (hx.sub analyticAt_const)
    refine h1.congr ?_
    filter_upwards [dslope_eventuallyEq_slope_of_ne f h] with t ht
    rw [ht, slope_def_module, smul_eq_mul]

theorem hasProd_of_subset {ι : Type} [DecidableEq ι] (f : ι → ℂ) {T T' : Finset ι} (h : T ⊆ T') {b : ℂ}
    (hb : HasProd (fun w : {w // w ∉ T'} => f w.1) b) :
    HasProd (fun w : {w // w ∉ T} => f w.1) ((∏ w ∈ T' \ T, f w) * b) := by
  classical
  let s : Set {w // w ∉ T} := {w | w.1 ∈ T'}
  let e1 : (↑(T' \ T) : Set ι) ≃ s :=
    { toFun := fun w => ⟨⟨w.1, (Finset.mem_sdiff.1 (Finset.mem_coe.1 w.2)).2⟩, (Finset.mem_sdiff.1 (Finset.mem_coe.1 w.2)).1⟩
      invFun := fun w => ⟨w.1.1, Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨w.2, w.1.2⟩)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : {w // w ∉ T'} ≃ (sᶜ : Set {w // w ∉ T}) :=
    { toFun := fun w => ⟨⟨w.1, fun hw => w.2 (h hw)⟩, w.2⟩
      invFun := fun w => ⟨w.1.1, w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : HasProd ((fun w : {w // w ∉ T} => f w.1) ∘ ((↑) : s → {w // w ∉ T})) (∏ w ∈ T' \ T, f w) :=
    (e1.hasProd_iff).1 (Finset.hasProd (T' \ T) f)
  have h2 : HasProd ((fun w : {w // w ∉ T} => f w.1) ∘ ((↑) : (sᶜ : Set {w // w ∉ T}) → {w // w ∉ T})) b :=
    (e2.hasProd_iff).1 hb
  exact h1.mul_compl h2

theorem sat_spec {a : ℕ} {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} (h : ∃ B, π.HasSat w B) :
    π.HasSat w (sat π w) := by
  unfold sat
  rw [dite_eq_left h]
  exact h.choose_spec

theorem prod_map_val (B : Multiset ℂˣ) : (B.map (fun α : ℂˣ => (α : ℂ))).prod = ((B.prod : ℂˣ) : ℂ) := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih => simp [ih]

theorem offDiag : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), IsGood T → UnrOutside T σ → UnrOutside T σ' → ∃ G : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ G (x : ℂ)) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => lfac σ σ' (x : ℂ) w.1) (G x) := by
  intro E _ _ _ a b σ σ' ha hb hσ hσ' hne T hgood hU hU'
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨F, H, hF, hH, hHpos, hFH⟩ := GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire E b a σ' σ ha hab hσ' hσ T hgood.2 hU' hU
    refine ⟨fun z => starRingEnd ℂ (F (starRingEnd ℂ z) / H (starRingEnd ℂ z)), ?_, ?_⟩
    · intro x hx
      have hopen : IsOpen {z : ℂ | H (starRingEnd ℂ z) ≠ 0} :=
        isOpen_ne_fun (hH.continuous.comp Complex.continuous_conj) continuous_const
      have hxmem : (x : ℂ) ∈ {z : ℂ | H (starRingEnd ℂ z) ≠ 0} := by
        simp only [Set.mem_setOf_eq, Complex.conj_ofReal]
        intro h0
        have := (hHpos x).1
        rw [h0, Complex.zero_re] at this
        exact lt_irrefl 0 this
      refine DifferentiableOn.analyticAt (fun z hz => ?_) (hopen.mem_nhds hxmem)
      have hd : DifferentiableAt ℂ (fun u => F u / H u) (starRingEnd ℂ z) := (hF _).div (hH _) hz
      have := hd.conj_conj
      rw [Complex.conj_conj] at this
      exact this.differentiableWithinAt
    · intro x hx
      have hp := (GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E a b σ σ' hσ hσ' T hU hU' x hx).2
      have e := GlobalTheory.T.partial_rankinSelberg_product_conj_swap_real E b a σ' σ hσ' hσ T hU' hU x hx
      have h2 : ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1 = F x / H x := (hFH x hx).tprod_eq
      have h3 : ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1 =
          starRingEnd ℂ (F (starRingEnd ℂ (x : ℂ)) / H (starRingEnd ℂ (x : ℂ))) := by
        rw [e, h2, Complex.conj_ofReal]
      beta_reduce
      rw [← h3]
      exact hp.multipliable.hasProd
  · have hne' : σ ≠ σ' := fun h => hne (by rw [h])
    obtain ⟨F, hFa, hF1, hF⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E a σ σ' ha hσ hσ' T hgood hU hU'
    refine ⟨dslope F 1, fun x hx => analyticAt_dslope' (hFa x hx), fun x hx => ?_⟩
    have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast hx.ne'
    have e : dslope F 1 (x : ℂ) = F x / ((x : ℂ) - 1) := by
      rw [dslope_of_ne _ hx1, slope_def_module, hF1 hne', sub_zero, smul_eq_mul, inv_mul_eq_div]
    rw [e]
    exact hF x hx
  · obtain ⟨F, H, hF, hH, hHpos, hFH⟩ := GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire E a b σ σ' hb hab hσ hσ' T hgood.2 hU hU'
    refine ⟨fun z => F z / H z, fun x hx => (hF.analyticAt _).div (hH.analyticAt _) ?_, fun x hx => hFH x hx⟩
    intro h0
    have := (hHpos x).1
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this

theorem tendsto_of_analyticAt {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 1) :
    Tendsto (fun x : ℝ => G x) (𝓝[>] 1) (𝓝 (G 1)) := by
  have h := hG.continuousAt.comp (x := (1 : ℝ)) (by simpa using Complex.continuous_ofReal.continuousAt)
  have h2 := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
  simp only [Function.comp_def, Complex.ofReal_one] at h2
  exact h2

theorem tendsto_partialL_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∃ z : ℂ, z ≠ 0 ∧ Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 z) := by
  intro E _ _ _ a b σ σ' ha hb hσ hσ' hne T hT hT'
  classical
  obtain ⟨T', hTT', hgood⟩ := GlobalTheory.T.exists_goodRankinSelbergPlaceSet_superset_totallyComplex E T
  have hU : UnrOutside T' σ := fun w hw => hT w fun h => hw (hTT' h)
  have hU' : UnrOutside T' σ' := fun w hw => hT' w fun h => hw (hTT' h)
  obtain ⟨G, hGa, hG⟩ := offDiag E a b σ σ' ha hb hσ hσ' hne T' hgood hU hU'
  obtain ⟨G', hG'a, hG'⟩ := offDiag E b a σ' σ hb ha hσ' hσ (Ne.symm hne) T' hgood hU' hU
  obtain ⟨D, hDa, -, hD⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E a σ σ ha hσ hσ T' hgood hU hU
  obtain ⟨D', hD'a, -, hD'⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E b σ' σ' hb hσ' hσ' T' hgood hU' hU'
  have hGa1 : AnalyticAt ℂ G 1 := by simpa using hGa 1 one_pos
  have hG'a1 : AnalyticAt ℂ G' 1 := by simpa using hG'a 1 one_pos
  have hlim : Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'}, lfac σ σ' (x : ℂ) w.1)
      (𝓝[>] 1) (𝓝 (G 1)) :=
    (tendsto_of_analyticAt hGa1).congr' (eventually_nhdsWithin_of_forall fun x hx => ((hG x hx).tprod_eq).symm)
  have hG1 : G 1 ≠ 0 := by
    intro h0
    have hG'1 : G' 1 = 0 := by
      have hlimc : Tendsto (fun x : ℝ => G' x) (𝓝[>] 1) (𝓝 (starRingEnd ℂ (G 1))) := by
        refine ((Complex.continuous_conj.tendsto _).comp (tendsto_of_analyticAt hGa1)).congr'
          (eventually_nhdsWithin_of_forall fun x hx => ?_)
        have e := GlobalTheory.T.partial_rankinSelberg_product_conj_swap_real E a b σ σ' hσ hσ' T' hU hU' x hx
        simp only [Function.comp]
        rw [← (hG x hx).tprod_eq, ← (hG' x hx).tprod_eq, e]
      rw [tendsto_nhds_unique (tendsto_of_analyticAt hG'a1) hlimc, h0, map_zero]
    let P : ℂ → ℂ := fun z => D z * D' z * dslope G 1 z * dslope G' 1 z
    have hPa : ∀ x : ℝ, 0 < x → AnalyticAt ℂ P (x : ℂ) := fun x hx =>
      (((hDa x hx).mul (hD'a x hx)).mul (analyticAt_dslope' (hGa x hx))).mul (analyticAt_dslope' (hG'a x hx))
    have hP : ∀ x : ℝ, 1 < x → ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ =>
        ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧ P x = Complex.exp g := by
      intro x hx
      obtain ⟨g, hg, he⟩ := GlobalTheory.T.dirichlet_series_exponential_sum_converges E a b σ σ' hσ hσ' T' hU hU' x hx
      refine ⟨g, hg, ?_⟩
      rw [← he, (hD x hx).tprod_eq, (hD' x hx).tprod_eq, (hG x hx).tprod_eq, (hG' x hx).tprod_eq]
      have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast hx.ne'
      have hx1' : (x : ℂ) - 1 ≠ 0 := sub_ne_zero.2 hx1
      have e1 : dslope G 1 (x : ℂ) = G x / ((x : ℂ) - 1) := by
        rw [dslope_of_ne _ hx1, slope_def_module, h0, sub_zero, smul_eq_mul, inv_mul_eq_div]
      have e2 : dslope G' 1 (x : ℂ) = G' x / ((x : ℂ) - 1) := by
        rw [dslope_of_ne _ hx1, slope_def_module, hG'1, sub_zero, smul_eq_mul, inv_mul_eq_div]
      simp only [P, e1, e2]
      field_simp
    have hN : (0 : ℝ) < 1 / ((a + b : ℕ) : ℝ) := by
      have : (0 : ℝ) < ((a + b : ℕ) : ℝ) := by exact_mod_cast (show 0 < a + b by omega)
      positivity
    obtain ⟨g, hg, -⟩ := GlobalTheory.landau_exp_hasSum_of_analyticAt ({w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ)
      (fun p => dcoef σ σ' p.1.1 p.2) (fun p => dexp p.1.1 p.2) 0 1 P (fun p => dcoef_nonneg _ _ _ _)
      (fun p => dexp_nonneg _ _) one_pos hPa hP _ hN
    set y : ℝ := 1 / ((a + b : ℕ) : ℝ) with hy
    have hs : Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ =>
        dcoef σ σ' p.1.1 p.2 * Real.exp (-(dexp p.1.1 p.2) * y)) := by
      rw [← Complex.summable_ofReal]
      refine hg.summable.congr fun p => ?_
      push_cast
      rfl
    refine GlobalTheory.PowerSumDiv.not_summable_psum_sq (a + b) (by omega) T'
      (fun w => (sat σ w).map (fun α : ℂˣ => (α : ℂ)) + (sat σ' w).map (fun α : ℂˣ => (α : ℂ))) ?_ ?_ (le_of_eq hy) ?_
    · intro w hw
      rw [Multiset.card_add, Multiset.card_map, Multiset.card_map, (sat_spec (hU w hw)).card, (sat_spec (hU' w hw)).card]
    · intro w hw
      rw [Multiset.prod_add, norm_mul, prod_map_val, prod_map_val, GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one E a σ w _ hσ (sat_spec (hU w hw)),
        GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one E b σ' w _ hσ' (sat_spec (hU' w hw)), one_mul]
    · refine hs.congr fun p => ?_
      have hq : (0 : ℝ) < (Ideal.absNorm p.1.1.asIdeal : ℝ) := by
        have := NumberField.HeightOneSpectrum.one_lt_absNorm p.1.1
        have : (0 : ℝ) < ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < Ideal.absNorm p.1.1.asIdeal)
        exact this
      simp only [dcoef, dexp]
      rw [Real.rpow_def_of_pos hq]
      have : -(((p.2 : ℝ) + 1) * Real.log (Ideal.absNorm p.1.1.asIdeal : ℝ)) * y =
          Real.log (Ideal.absNorm p.1.1.asIdeal : ℝ) * -(((p.2 : ℝ) + 1) * y) := by ring
      rw [this]
      ring
  have hfac : ∀ w ∈ T' \ T, Tendsto (fun x : ℝ => lfac σ σ' (x : ℂ) w) (𝓝[>] 1) (𝓝 (lfac σ σ' 1 w)) ∧
      lfac σ σ' 1 w ≠ 0 := by
    intro w hw
    have hw2 := (Finset.mem_sdiff.1 hw).2
    exact GlobalTheory.T.localRankinSelbergFactor_conj_tendsto_one_ne_zero (Ideal.absNorm w.asIdeal) (sat σ w) (sat σ' w) (NumberField.HeightOneSpectrum.one_lt_absNorm w)
      (GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp E a σ ha hσ T hT w hw2) (GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp E b σ' hb hσ' T hT' w hw2)
  refine ⟨(∏ w ∈ T' \ T, lfac σ σ' 1 w) * G 1,
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w hw => (hfac w hw).2) hG1, ?_⟩
  have hprodlim : Tendsto (fun x : ℝ => ∏ w ∈ T' \ T, lfac σ σ' (x : ℂ) w) (𝓝[>] 1)
      (𝓝 (∏ w ∈ T' \ T, lfac σ σ' 1 w)) := tendsto_finsetProd _ fun w hw => (hfac w hw).1
  refine (hprodlim.mul hlim).congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
  have hp := (GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E a b σ σ' hσ hσ' T' hU hU' x hx).2
  have h1 := hasProd_of_subset (fun w => lfac σ σ' (x : ℂ) w) hTT' hp.multipliable.hasProd
  exact h1.tprod_eq.symm

end GlobalTheory.RSNonvan
end
end
