module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle037
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle055
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridge
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle038
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DegreeInfimum.PlaceDegreeSums
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAnalyticModelOnFrameOrbitIsolating
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle005
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (n' : ℕ) (ν₀ : E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → letI := H.starRing; ∃ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (jj : ℤ) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ ∧ ξ ≠ 0 ∧ Module.finrank (𝓞 E) A.X = 1 ∧ (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') ∧ BetaAt ξ l.M' A.be ν₀ jj ∧ PrimAn H A ∧ (∀ y, n' • A.ct y ∈ A.abelian₂) ∧ AbDat H A DB tyB eB ∧ DB.p = Dw.p - 1 ∧ DB.q = Dw.q - 1 := by
  first | exact @GlobalTheory.AnAtFrame.exists_anArc_onOrbit | exact GlobalTheory.AnAtFrame.exists_anArc_onOrbit | (intros; apply GlobalTheory.AnAtFrame.exists_anArc_onOrbit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
open scoped Matrix

namespace GlobalTheory.FrameMatch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem flow_lact_rmul (X : Data E r) (gm : GL (Fin r) E)
    (hgm : ∀ u v, herm X.Gm ((gm : Matrix (Fin r) (Fin r) E) *ᵥ u) ((gm : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x b : Frame X.Ψ r) :
    X.flow ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) s (rmul (lact gm x) b) = rmul (lact gm (X.flow ξ s x)) b := by
  funext τ
  have key : X.flowMat ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s τ) * (gm : Matrix (Fin r) (Fin r) E).map τ.1 =
      (gm : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ τ (s τ) := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, EmbeddingHermitianPairs.flowMat_mulVec, EmbeddingHermitianPairs.flowMat_mulVec,
      GlobalTheory.PerMove.emb_mulVec, GlobalTheory.PerMove.hermC_unitary _ _ _ hgm, Matrix.mulVec_add, Matrix.mulVec_smul]
  change X.flowMat _ τ (s τ) * ((gm : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ) =
    (gm : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ τ (s τ) * mat x τ) * mat b τ
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, key, Matrix.mul_assoc (_ : Matrix (Fin r) (Fin r) ℂ) _ (mat x τ)]

theorem fj_lact_rmul (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {gm : GL (Fin r) E}
    (hgm : gm ∈ X.Γ) {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (ν : X.Ψ → ℝ) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) :
    X.fj la ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) ν P (rmul (lact gm x) b) =
      bchar la b * X.χ la gm * X.fj la ξ ν P x := by
  have h : ∀ s : X.Ψ → ℝ, P (X.flow ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) (fun τ => (s τ : ℂ)) (rmul (lact gm x) b)) =
      bchar la b * X.χ la gm * P (X.flow ξ (fun τ => (s τ : ℂ)) x) := fun s => by
    have h1 : X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := TransvectionPeriodicity.flow_real_mem_dom X hξ s x hx
    rw [flow_lact_rmul X gm (X.Γ_stab gm hgm).1, hP.2.1 _ ((AR.Up.PairUnfoldPf.lact_mem_dom_iff X hgm _).2 h1) b hb,
      hP.2.2 gm hgm _ h1, _root_.mul_assoc]
  unfold Data.fj
  split_ifs
  · simp only [h, _root_.mul_assoc (bchar la b * X.χ la gm), MeasureTheory.integral_const_mul]
    ring
  · simp
  · simp

theorem row_eq_of_lattice (X : Data E r) (τ : E →+* ℂ) (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r)
    (h : ∀ v ∈ X.Λ, (A *ᵥ Data.emb τ v) a = (B *ᵥ Data.emb τ v) a) (j : Fin r) : A a j = B a j := by
  obtain ⟨d, hd, hv⟩ := HermitianTraceFormVanishing.exists_smul_mem (R := 𝓞 E) (F := E) X.Λ (x := Pi.single j 1)
    (by rw [X.Λ_span]; trivial)
  have h2 := h _ hv
  have hemb : Data.emb τ (d • (Pi.single j 1 : Fin r → E)) = τ d • (Pi.single j 1 : Fin r → ℂ) := by
    funext k
    by_cases hk : k = j <;> simp [Data.emb, Algebra.smul_def, hk]
  rw [hemb, Matrix.mulVec_smul, Matrix.mulVec_smul] at h2
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one, Matrix.col_apply] at h2
  refine mul_left_cancel₀ ?_ h2
  simpa using hd

theorem exists_bor (X : Data E r) {y y' : Frame X.Ψ r} (hy : y ∈ X.dom) (hy' : y' ∈ X.dom) (q : ℕ)
    (h1 : ∀ τ (a : Fin r), (a : ℕ) < q → FD.col (mat y' τ) a = FD.col (mat y τ) a)
    (h2 : ∀ τ (a : Fin r), ¬ (a : ℕ) < q → ∀ j, (mat y' τ)⁻¹ a j = (mat y τ)⁻¹ a j) :
    ∃ b ∈ Bor X.Ψ r, y' = rmul y b := by
  refine ⟨fun τ => ((mat y τ)⁻¹ * mat y' τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩, ?_⟩
  · change ((mat y τ)⁻¹ * mat y' τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hy τ).1.isUnit).ne_zero (hy' τ).1
  · change ((mat y τ)⁻¹ * mat y' τ) a c = 0
    by_cases ha : (a : ℕ) < q
    · have h3 := congrFun (congrFun (Matrix.nonsing_inv_mul (mat y τ) (hy τ).1.isUnit) a) c
      rw [Matrix.one_apply_ne hca.ne'] at h3
      rw [← h3, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun j _ => congrArg _ (congrFun (h1 τ c (lt_trans hca ha)) j)
    · have h3 := congrFun (congrFun (Matrix.nonsing_inv_mul (mat y' τ) (hy' τ).1.isUnit) a) c
      rw [Matrix.one_apply_ne hca.ne'] at h3
      rw [← h3, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [h2 τ a ha j]
  · funext τ
    change mat y' τ = mat y τ * ((mat y τ)⁻¹ * mat y' τ)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hy τ).1.isUnit]

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem exists_isometry {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (i : Fin F.n)
    (P P' : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    (hu : F.u i P = F.u i P') (hex : ∀ z, (F.ex i P z).left = (F.ex i P' z).left) :
    ∃ gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La, (∀ a, P' (gam a) = P a) ∧
      (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) ∧ ∀ a, ∃ e, gam a = a + l.M • e := by
  obtain ⟨h, gam, hh, hPh, hiso, hM, -⟩ := GlobalTheory.familyUnif_exp_unique E H Dw l Xo σ' g ty F i i P P' hP hP' hu
  haveI := hP'.2.2.1
  have h1 : ∀ z, h z = z := fun z => sub_eq_zero.1 <|
    GlobalTheory.ExpUniqFamily.linear_eq_zero_of_discrete P'.range (h.toLinearMap - LinearMap.id) (fun z =>
      (F.ex_ker i P' hP' _).1 <| (GlobalTheory.ExpUniqFamily.eq_iff_sub (F.ex i P') (F.ex_add i P' hP') _ _).1
        (Over.OverMorphism.ext ((hh z).trans (hex z)))) z
  refine ⟨gam, fun a => (hPh a).trans (h1 _), hiso,
    GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di i) l gam hiso fun a ha => ?_⟩
  refine Submodule.smul_induction_on ha ?_ ?_
  · intro v hv b _
    obtain ⟨c, e, rfl⟩ := F.t_surj i b
    obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
    obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    refine ⟨e₁ + m • (gam (v • e) - v • e), ?_⟩
    rw [smul_add, ← map_smul, smul_comm v, map_add (f := _), he₁, map_nsmul, hm, smul_add, smul_smul, smul_sub]
    abel
  · rintro x y ⟨e, he⟩ ⟨e', he'⟩
    exact ⟨e + e', by rw [map_add (f := _), he, he', smul_add]; abel⟩

variable {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} (Uw : UnfWit U)

theorem comp_eq (hU : IsUnf U) {k k' : U.Comp} (x : (U.X k).dom) (x' : (U.X k').dom)
    (hu : Uw.F.u (Uw.ik k) (Uw.Pm k x) = Uw.F.u (Uw.ik k') (Uw.Pm k' x'))
    (hex : ∀ z, (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left = (Uw.F.ex (Uw.ik k') (Uw.Pm k' x') z).left) : k' = k := by
  have hbor := GlobalTheory.CompInj.frBor_of_eq (U.un k x) (U.un k' x')
    (((Uw.lie k' x').1.trans hu.symm).trans (Uw.lie k x).1.symm) fun τ i => by
      have h' := (Uw.lie k' x').2 τ i
      simp only [← hex] at h'
      exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ Uw.F _ _ (Uw.period k x)).2.1 _).unique h'
        ((Uw.lie k x).2 τ i)
  obtain ⟨gm, -, b, -, h⟩ := (hU.2.2.2.1 k k' _ _).1 hbor
  exact congrArg Sigma.fst h

theorem exists_move (hσ : GoodEmb c σ) (hU : IsUnf U) (hpr : GlobalTheory.FrameNorm.HasPrinc U l.M) (k : U.Comp)
    (x x' : (U.X k).dom) (hu : Uw.F.u (Uw.ik k) (Uw.Pm k x) = Uw.F.u (Uw.ik k) (Uw.Pm k x'))
    (hex : ∀ z, (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left = (Uw.F.ex (Uw.ik k) (Uw.Pm k x') z).left) :
    ∃ gm ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, x'.1 = rmul (lact gm x.1) b ∧ ∀ t t', Uw.Pm k x t = Uw.Pm k x' t' →
      (Uw.φ k t' : Fin r → E) = (gm : Matrix (Fin r) (Fin r) E) *ᵥ (Uw.φ k t : Fin r → E) := by
  obtain ⟨gam, hP, hiso, hM⟩ := exists_isometry Uw.F _ _ _ (Uw.period k x) (Uw.period k x') hu hex
  let φ : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (Uw.φ k).toLinearMap
  have hrange : LinearMap.range φ = (U.X k).Λ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have hφ : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ _ ∧ _ ∧ _ :=
    ⟨Subtype.val_injective.comp (Uw.φ k).injective, by rw [← LinearMap.coe_range, hrange]; exact (U.X k).Λ_span,
      (U.X k).Gm_herm, (U.X k).Gm_det, Uw.iso k⟩
  obtain ⟨gm, hgm, hgmφ⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H _ _ r (-(U.X k).ξ0) (U.X k).Gm φ φ gam
    (by rw [HermitianTraceFormVanishing.cc_neg, (U.X k).ξ0_im]) hφ hφ hiso
  have hg : ∀ a, (Uw.φ k (gam a) : Fin r → E) = (gm : Matrix (Fin r) (Fin r) E) *ᵥ (Uw.φ k a : Fin r → E) := hgmφ
  have hs : ∀ w ∈ (U.X k).Λ, ∃ a, (Uw.φ k a : Fin r → E) = w := fun w hw =>
    ⟨(Uw.φ k).symm ⟨w, hw⟩, by rw [LinearEquiv.apply_symm_apply]⟩
  have hΓ : gm ∈ (U.X k).Γ := by
    refine hpr k gm ⟨hgm, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩ fun w hw => ?_
    · obtain ⟨a, rfl⟩ := hs w hw
      rw [← hg]
      exact (Uw.φ k _).2
    · obtain ⟨a, ha⟩ := hs _ hw
      obtain ⟨a, rfl⟩ := gam.surjective a
      rw [hg] at ha
      rw [← Matrix.mulVec_injective_iff_isUnit.2 gm.isUnit ha]
      exact (Uw.φ k _).2
    · obtain ⟨a, rfl⟩ := hs w hw
      obtain ⟨e, he⟩ := hM a
      refine ⟨_, (Uw.φ k e).2, ?_⟩
      rw [← hg, he, map_add (f := _), map_nsmul, Nat.cast_smul_eq_nsmul]
      simp
  have hy : lact gm x.1 ∈ (U.X k).dom := (AR.Up.PairUnfoldPf.lact_mem_dom_iff (U.X k) hΓ _).2 x.2
  obtain ⟨idx, -, -, hper⟩ := GlobalTheory.ArcFlow.exists_idx Uw hσ hU k
  have key : ∀ w ∈ (U.X k).Λ, ∀ j, perFr (U.X k) x'.1 w (relab c σ (Uw.e j).1) (Uw.e j).2 =
      perFr (U.X k) (lact gm x.1) w (relab c σ (Uw.e j).1) (Uw.e j).2 := fun w hw j => by
    obtain ⟨a, rfl⟩ := hs w hw
    obtain ⟨a, rfl⟩ := gam.surjective a
    rw [← Uw.Pm_eq, hP, hg, GlobalTheory.PerGam.perFr_lact _ gm hgm, Uw.Pm_eq]
  obtain ⟨b, hb, hxb⟩ := exists_bor (U.X k) hy x'.2 Dw.q
    (fun τ a ha => GlobalTheory.ArcFlow.eq_of_hermC_lattice (U.X k) τ.1 _ _ fun w hw => by
      have h1 := key w hw (idx.symm (τ, a))
      rw [hper, hper] at h1
      simpa only [Equiv.apply_symm_apply, if_pos ha] using h1)
    (fun τ a ha => row_eq_of_lattice (U.X k) τ.1 _ _ a fun w hw => by
      have h1 := key w hw (idx.symm (τ, a))
      rw [hper, hper] at h1
      simpa only [Equiv.apply_symm_apply, if_neg ha] using h1)
  refine ⟨gm, hΓ, b, hb, hxb, fun t t' ht => ?_⟩
  rw [← hg, (Uw.period k x').2.1 ((hP t).trans ht)]

theorem fj_eq_zero_iff_of_same_exp : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (t : (Uw.F.Di (Uw.ik k)).La) (t' : (Uw.F.Di (Uw.ik k')).La) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ν₀ : E), GoodEmb c σ → IsUnf U → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → (U.X k).IsIso (Uw.φ k t : Fin r → E) → Uw.F.u (Uw.ik k) (Uw.Pm k x) = Uw.F.u (Uw.ik k') (Uw.Pm k' x') → (∀ z, (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left = (Uw.F.ex (Uw.ik k') (Uw.Pm k' x') z).left) → Uw.Pm k x t = Uw.Pm k' x' t' → ∀ F ∈ sec Xo c a' n, ((U.X k).fj (laU U a' n k) (Uw.φ k t : Fin r → E) (fun τ => (τ.1 ν₀).re) (rdU U F k) x.1 = 0 ↔ (U.X k').fj (laU U a' n k') (Uw.φ k' t' : Fin r → E) (fun τ => (τ.1 ν₀).re) (rdU U F k') x'.1 = 0) := by
  intro _ E _ _ _ H Dw l Xo c σ r U Uw k k' x x' t t' a' n ν₀ hσ hU hpr hD hχ hiso hu hex ht F hF
  obtain rfl := comp_eq Uw hU x x' hu hex
  obtain ⟨gm, hgm, b, hb, hxb, hφ⟩ := exists_move Uw hσ hU hpr k' x x' hu hex
  rw [hφ t t' ht, hxb, fj_lact_rmul (U.X k') (hU.2.2.2.2.1 a' n hD F hF k') hgm hiso.2.1 _ x.2 hb, hχ k' gm hgm,
    _root_.mul_one,
    mul_eq_zero, or_iff_right (AR.Up.PairUnfoldPf.bchar_ne (U.X k') hb _)]

end GlobalTheory.FrameMatch
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem ndeg_eq_places {K : Type} [Field K] [NumberField K] (N : MLine K) (hN : N.Good)
    (hc : ∀ σ : K →+* ℂ, N.n ((starRingEnd ℂ).comp σ) = N.n σ) :
    ((∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) -
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding)) / (Module.finrank ℚ K : ℝ) = N.ndeg := by
  have h1 : (∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) =
      -Real.log ((FractionalIdeal.absNorm N.I : ℚ) : ℝ) := by
    simp_rw [neg_mul]
    rw [finsum_neg_distrib, PlaceDegreeSums.sum_count_log_norm _ hN.1]
  have h2 : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding) =
      ∑ τ : K →+* ℂ, Real.log (N.n τ) := by
    rw [PlaceDegreeSums.sum_infinite_places_mult (fun σ => Real.log (N.n σ.embedding))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [h]
    · rw [h]
      exact congrArg Real.log (hc τ)
  rw [h1, h2, MLine.ndeg, MLine.deg]

theorem qbridge_of_numGood : ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Ch Ah Cc Ac Tt cc : ℝ) (be : HeightOneSpectrum (𝓞 B.KO) → ℝ) (Carch Bdeg : ℝ), Submodule.IsFullLattice B.KO (B.Mlat j ka) → (∀ la, 0 ≤ be la) → (Function.support be).Finite → (∑ᶠ la, be la * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ τ F, B.supN j ka ((starRingEnd ℂ).comp τ) F = B.supN j ka τ F) → WeightFamilies.PPv D large₂ Ch Ah * ka.size + Carch + Bdeg + Real.log (WeightFamilies.rhoP B CR Tt cc j ka : ℝ) / 2 ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ F : B.Cusp j ka, F ∉ WeightFamilies.MggK B CR Tt cc j ka → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra B.KO K₁) (φ : B.Cusp j ka →ₗ[B.KO] K₁), WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧ φ F ≠ 0 ∧ NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ) → QBridgeAt large₂ B j ka CR Ch Ah Cc Ac Tt cc := by
  intro D large₂ B j ka CR Ch Ah Cc Ac Tt cc be Carch Bdeg hlat hbe hbefin hbesum hconj hroom hdet
  classical
  obtain ⟨K₁, _, _, _, ρ, g, cf, hfam, hcf, hker, hdim⟩ := kerCore_holds B.KO (B.Cusp j ka)
    (WeightFamilies.MggK B CR Tt cc j ka)
    (fun K₁ _ _ _ φ => WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧
      NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ)
    (fun _ _ _ _ _ h => h.1)
    (fun v hv => by
      by_contra hn
      obtain ⟨K₁, _, _, _, φ, h1, h2, h3⟩ := hdet v hn
      exact h2 (hv K₁ φ ⟨h1, h3⟩))
    (fun K' K₁ _ _ _ _ _ _ e f hf => ⟨e.toLinearMap.comp f, ⟨fun v hv => by
      have := LinearMap.mem_ker.1 (hf.1 hv)
      simp [LinearMap.mem_ker, this], GlobalTheory.T.isNumberFieldFunctionalBounded_comp_extension _ _ _ _ _ _ _ K' K₁ e f hf.2⟩, fun _ => rfl⟩)
  let _ := hlat
  have hrk : WeightFamilies.rhoP B CR Tt cc j ka + Module.finrank B.KO (WeightFamilies.MggK B CR Tt cc j ka) =
      Module.finrank B.KO (B.Cusp j ka) :=
    LocalQuotientRank.rank_QuotMW (K := B.KO) (B.Mlat j ka) hlat.fg (Submodule.IsFullLattice.span_eq_top (A := B.KO) (M := B.Mlat j ka)) (WeightFamilies.MggK B CR Tt cc j ka)
  have hρ : ρ = WeightFamilies.rhoP B CR Tt cc j ka := by omega
  subst hρ
  choose N hG hd hc hint harch using fun i => (hfam i).2
  refine ⟨K₁, inferInstance, inferInstance, inferInstance, cf, be,
    fun i w => -(FractionalIdeal.count K₁ w (N i).I : ℝ), fun i σ => Real.log ((N i).n σ.embedding), Carch, Bdeg,
    hker, hbe, hbefin, hbesum, fun i => ?_, fun la w hw i F hF hne => ?_, hconj, fun σ i F hF hne => ?_,
    fun i => ?_, hroom⟩
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (N i).I)).subset fun w hw h => hw ?_
    simp [h]
  · rw [hcf] at hne ⊢
    exact (hint i la w hw F hF hne).trans_eq (sub_eq_add_neg _ _)
  · rw [hcf] at hne ⊢
    rw [← InfinitePlace.norm_embedding_eq]
    exact harch i σ.embedding F hF hne
  · rw [ndeg_eq_places (N i) (hG i) (hc i)]
    exact hd i

end GlobalTheory.ArcCM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.ArcPts
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem card_qk_pre (hL : Out.Laws) (hL2 : Out.Laws2) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (D₀ : Out.DegPre R) (hB : D₀.TauBimult) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    (k : ℕ) (hk : (k : F) ≠ 0) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ (2 * (D₀.rank + D₀.P.g)) := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  have h₁ := (GlobalTheory.GtCount.card_gtTors hL hL2 R D₀ F k hk).1
  simp only [GlobalTheory.GtCount.gtTors_iff] at h₁
  open ReciprocityTheory.ChartRestriction.G.Out in
  have hc : Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) =
      k ^ D₀.rank * Nat.card {g : GtPtF D₀ F // k • g = 0} := by
    open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR in
      let iota : D₀.X →+ GtPtF D₀ F := AddMonoidHom.mk' (fun x => (exists_iota (F := F) hB x).choose) fun x x' => by
        obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x).choose_spec
        obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x').choose_spec
        obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB (x + x')).choose_spec
        refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
        have C : IsCub (th D₀ (T := TF (R := R) F) y J) := isCub_cubV D₀.cub hJ
        rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
        exact tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
      have hi (x : D₀.X) : GtPtF.IsIota x (iota x) := (exists_iota (F := F) hB x).choose_spec
      have he (x : D₀.X) (g : GtPtF D₀ F) : GtPtF.IsIota x g ↔ g = iota x :=
        ⟨fun h => isIota_unique h (hi x), fun h => h ▸ hi x⟩
      let qkMk (y : D₀.X) (g : GtPtF D₀ F) (h : k • g = iota y) : QkPt D₀ F k :=
        ⟨y, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, (he _ _).2 h⟩
      have qk_nsmul (p : QkPt D₀ F k) : k • p.g = iota p.y := by
        obtain ⟨h, h₁, h₂⟩ := p.eq
        exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((he _ _).1 h₂)
      have equiv_iff (p p' : QkPt D₀ F k) : QkPt.Equiv D₀ F p p' ↔ ∃ z : D₀.X, p'.y = p.y + k • z ∧ p'.g = p.g + iota z :=
        exists_congr fun z => and_congr Iff.rfl
          ⟨fun ⟨_, h₁, h₂⟩ => ((isAdd_iff_eq _ _ _).1 h₂).trans (congrArg (p.g + ·) ((he _ _).1 h₁)),
           fun h => ⟨_, hi z, (isAdd_iff_eq _ _ _).2 h⟩⟩
      have hd : ∀ y : D₀.X, ∃ g : GtPtF D₀ F, k • g = iota y :=
        fun y => exists_nsmul_eq hL.mulN (Or.inl inferInstance) hk0 _
      choose r hr using hd
      let K : AddSubgroup D₀.X := (nsmulAddMonoidHom k : D₀.X →+ D₀.X).range
      have hK : Nat.card (D₀.X ⧸ K) = k ^ D₀.rank := AddSubgroup.index_range_nsmul D₀.X k
      let f : (D₀.X ⧸ K) × {g : GtPtF D₀ F // k • g = 0} → Quot (Out.QkPt.Equiv D₀ F (k := k)) := fun x =>
        Quot.mk _ (qkMk x.1.out (r x.1.out + x.2.1) (by rw [nsmul_add, hr, x.2.2, add_zero]))
      rw [← hK, ← Nat.card_prod]
      refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
      · rintro ⟨c, t⟩ ⟨c', t'⟩ h
        obtain ⟨z, hy, hg⟩ := (equiv_iff _ _).1 ((equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact h))
        change c'.out = c.out + k • z at hy
        change r c'.out + t'.1 = r c.out + t.1 + iota z at hg
        obtain rfl : c = c' := by
          rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq]
          exact ⟨z, by rw [hy, neg_add_cancel_left]; rfl⟩
        have hz : z = 0 := by
          have h0 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact left_eq_add.1 hy
          exact (smul_eq_zero.1 h0).resolve_left (by exact_mod_cast hk0)
        rw [hz, map_zero, add_zero, add_right_inj] at hg
        exact Prod.ext rfl (Subtype.ext hg.symm)
      · rintro ⟨p⟩
        obtain ⟨z, hz⟩ : -p.y + (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out ∈ K := by
          rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
        have hy : (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out = p.y + k • z := by
          rw [show k • z = _ from hz, add_neg_cancel_left]
        refine ⟨⟨QuotientAddGroup.mk p.y, p.g + iota z - r (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out, ?_⟩,
          (Quot.sound ((equiv_iff _ _).2 ⟨z, hy, ?_⟩)).symm⟩
        · rw [nsmul_sub, hr, hy, nsmul_add, qk_nsmul, map_add (f := _), map_nsmul, sub_self]
        · exact add_sub_cancel _ _
  rw [hc, h₁, ← pow_add]
  congr 1
  ring

theorem card_qk_of_tateIsoQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {R : Type} [CommRing R] [IsDomain R] {D₀ : Out.DegPre R} [Module (𝓞 E) D₀.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (hB : D₀.TauBimult) (I : TateIsoQ D D₀ oa F) (k : ℕ) (hk : 0 < k) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ Module.finrank ℤ D.La := by
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have := datum_free_int D
  let K : AddSubgroup D.La := (nsmulAddMonoidHom k : D.La →+ D.La).range
  have hK : Nat.card (D.La ⧸ K) = k ^ Module.finrank ℤ D.La := AddSubgroup.index_range_nsmul D.La k
  have hE := equiv_equivalence (D := D₀) (F := F) (k := k) hB
  let f : D.La ⧸ K → Quot (Out.QkPt.Equiv D₀ F (k := k)) := fun x => Quot.mk _ (I.ev k x.out)
  rw [← hK]
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · intro x x' h
    obtain ⟨e, he⟩ := (I.ker k hk _ _).1 (hE.symm (hE.eqvGen_iff.1 (Quot.eqvGen_exact h)))
    rw [← QuotientAddGroup.out_eq' x, ← QuotientAddGroup.out_eq' x', QuotientAddGroup.eq]
    exact ⟨e, by rw [he, neg_add_cancel_left]; rfl⟩
  · rintro ⟨p⟩
    obtain ⟨v, hv⟩ := I.onto k hk p
    obtain ⟨e, he⟩ : -v + (QuotientAddGroup.mk v : D.La ⧸ K).out ∈ K := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    refine ⟨QuotientAddGroup.mk v, Quot.sound (hE.trans ((I.ker k hk _ _).2 ⟨e, ?_⟩) hv)⟩
    rw [show k • e = _ from he, add_neg_cancel_left]

theorem finrank_V_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → (∃ r z : O, ((β r : c.F) : ℂ) = H.rt0 ∧ ((β z : c.F) : ℂ) = zeta l.A) → Module.finrank ℂ Λ.A.V = g := by
  intro hL hL2 E _ _ _ H _ D l c O _ β _ _ b a Λ g ty hty ⟨r, z, hr, hz⟩
  obtain ⟨-, I, -⟩ := a.geom ℂ r z hr hz _ rfl
  have h₁ := card_qk_pre hL hL2 a.D₀ a.bimult ℂ 2 (by norm_num)
  rw [card_qk_of_tateIsoQ a.bimult I 2 two_pos, datum_finrank_int,
    ← (GlobalTheory.PeriodExists.period_of_isTypeFn H D g ty hty).1] at h₁
  have h₂ := Nat.pow_right_injective le_rfl h₁
  have h₃ : Module.finrank ℤ Λ.A.X = a.D₀.rank := (Λ.ε.toAddEquiv.toIntLinearEquiv).finrank_eq
  rw [Λ.A.finrank_V, h₃, Λ.gB_eq]
  omega

end GlobalTheory.ArcPts
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.pointFamilies_eq_of_values_levels_universalFamily : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (y₁ y₂ : Sp F ⟶ Xo.X) (Θ₁ : FPts act Xo.univ.t y₁ φ) (Θ₂ : FPts act Xo.univ.t y₂ φ), y₁ ≫ Xo.s = y₂ ≫ Xo.s → (∀ v, ∃ ψ, Θ₁.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ ∧ Θ₂.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ) → (∀ v ∈ idealPart D l, ∃ ψ, Θ₁.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ ∧ Θ₂.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ) → ∀ v, (Θ₁.x v).left = (Θ₂.x v).left ∧ ∀ j, ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Θ₁.τ v j = Θ₂.τ v j := by
  first | exact @GlobalTheory.FamilyUnique.points_frames_eq | exact GlobalTheory.FamilyUnique.points_frames_eq | (intros; apply GlobalTheory.FamilyUnique.points_frames_eq <;> assumption)
end
