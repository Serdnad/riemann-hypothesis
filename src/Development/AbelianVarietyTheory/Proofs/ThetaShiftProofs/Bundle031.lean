module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominators
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle054
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle059
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle055
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle030
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAbelianTripleIsoOfSamePointValues
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.arcLetterRingOverDVR_polynomial_denominators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V), ϖ ≠ 0 → IsDomain (ArcSR Dw Tv.V ϖ) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (ArcSR Dw Tv.V ϖ)) ∧ ((arcιR Dw Tv.V ϖ).comp (PowerSeries.C (R := Tv.V))).Flat ∧ (∃ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) ∧ ∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) ∧ ∀ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) → (∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) → ∀ f : ArcSR Dw Tv.V ϖ, (∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr), algebraMap _ (ArcS Dw Tv.Fr) P = ψ f) → ∃ (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G := by
  first | exact @GlobalTheory.LetterDenom.main | exact GlobalTheory.LetterDenom.main | (intros; apply GlobalTheory.LetterDenom.main <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem exists_finSite_norm_eq_zpow_siteAlg :
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁)),
      (∃ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes ∧ OverLa w Tv.V io 1) ∧
      ∀ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes → OverLa w Tv.V io 1 →
        ∃ (Z : FinSite K₁ w) (ιT : Tv.Fr →+* Z.K), ιT.comp io = Z.ι ∧
          (∀ x : Tv.Fr, x ≠ 0 → ‖ιT x‖ = Z.r ^ vV Tv.V x) ∧ SiteAlg Z Tv ιT := by
  intro K₁ _ _ w
  obtain ⟨h1, h2⟩ := exists_finSite_siteAlg K₁ w
  refine ⟨h1, fun Tv io hfin ho => ?_⟩
  obtain ⟨Z, ιT, hc, hn, hs⟩ := h2 Tv io 1 hfin ho
  refine ⟨Z, ιT, hc, fun x hx => ?_, hs⟩
  have hf : ∀ v, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  obtain ⟨y, hy⟩ := w.valuation_exists_uniformizer K₁
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  have hv : vLa w y = 1 := by
    rw [vLa, hy, WithZero.log_exp, neg_neg]
  have e1 : ‖Z.ι y‖ = Z.r := by
    have := Z.norm_ι y hy0
    rw [this]
    change Z.r ^ vLa w y = Z.r
    rw [hv, zpow_one]
  have e2 : ‖ιT (algebraMap Tv.V Tv.Fr π)‖ = Z.r := by
    rw [← e1, ← hc, RingHom.comp_apply,
      norm_map_eq_zpow_vV ιT hf hπ ((map_ne_zero io).2 hy0), ho.2 y, hv]
    simp
  rw [norm_map_eq_zpow_vV ιT hf hπ hx, e2]

end GlobalTheory.ArcQ
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K), ϖ ≠ 0 → (∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1) → ∀ (t : K) (Y : ArcLt Dw → K), 0 < ‖t‖ → ‖t‖ < 1 → (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 → ∃ ev : ArcSR Dw Tv.V ϖ →+* K, (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * t ^ k) ∧ (∀ x, ev (arcXR Dw Tv.V ϖ x) = Y x) ∧ ∀ (f : ArcSR Dw Tv.V ϖ) (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G → P * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Tv.Fr (PowerSeries.C (R := Tv.Fr) (algebraMap Tv.V Tv.Fr ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr))) G → Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k‖) Filter.cofinite (nhds 0) ∧ ev f = ∑' k : ℤ, MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k := by
  first | exact @GlobalTheory.LetterEval.exists_eval | exact GlobalTheory.LetterEval.exists_eval | (intros; apply GlobalTheory.LetterEval.exists_eval <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.nonempty_unifWitnessData_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → Nonempty (UnfWit U) := by
  first | exact @GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf | exact GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf | (intros; apply GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.riemann_form_frame_periods_eq_majorant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), GoodEmb c σ → IsUnf U → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → (∀ v, (hermForm Hm (Uw.Pm k x v) (Uw.Pm k x v)).re = ∑ τ, (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 (Uw.φ k v : Fin r → E))) ∧ (0 < r → (U.X k).κ0 = 2 * (U.X k).ξ0) ∧ ∀ (xi : ℝ) (a' : (E →+* ℂ) × ℕ → ℕ), (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xi) → (lieFac Dw xi a' * (U.X k).nfac (laU U a' 0 k) x.1)⁻¹ ≤ ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re) ^ ((a' (τ, (i : ℕ)) : ℝ) / 2) := by
  first | exact @GlobalTheory.RiemMaj.riemann_eq_majorant | exact GlobalTheory.RiemMaj.riemann_eq_majorant | (intros; apply GlobalTheory.RiemMaj.riemann_eq_majorant <;> assumption)
end

section

alias GlobalTheory.T.frame_matrix_hasSum_alt := GlobalTheory.ArcLie.frame_matrix_hasSum
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ.AnFrEx

theorem eq_zero_of_mul_eventually {g : ℕ} (θ φ : (Fin g → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : ∃ z, θ z ≠ 0)
    (hφ : ContinuousAt φ 0) (h : ∀ᶠ z in nhds 0, θ z * φ z = 0) : φ 0 = 0 := by
  by_contra h0
  obtain ⟨z₀, hz₀⟩ := hne
  have h1 : ∀ᶠ z in nhds (0 : Fin g → ℂ), θ z = 0 := by
    filter_upwards [h, hφ.eventually_ne h0] with z a b
    exact (mul_eq_zero.1 a).resolve_right b
  have hl : Differentiable ℂ (fun t : ℂ => t • z₀) := differentiable_id.smul_const z₀
  have ht : Filter.Tendsto (fun t : ℂ => t • z₀) (nhds 0) (nhds 0) := by
    have := hl.continuous.tendsto 0
    simpa using this
  have han : AnalyticOnNhd ℂ (fun t : ℂ => θ (t • z₀)) Set.univ := fun t _ => (hθ.comp hl).analyticAt t
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (ht.eventually h1) (Set.mem_univ 1)
  exact hz₀ (by simpa using this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem isOpen_ex {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P) (V : Xo.univ.t.G.left.Opens) :
    IsOpen {z | ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ V} := by
  have h := ((F.hol k 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun x => differentiableOn_const _⟩).2 V 0).1
  have h2 := h.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
  convert h2 using 1
  ext z
  simp

theorem gen_unique (hT : Out.SecTwistSt) {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P)
    (θ : (Fin g → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : ∃ z, θ z ≠ 0) (κ : ℂ) (hκ : κ ≠ 0)
    (fr fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
    (hf : IsThetaFrameAt Xo.univ.t.PP (F.u k P) (fun w => (F.ex k P w).left) θ fr)
    (hf' : IsThetaFrameAt Xo.univ.t.PP (F.u k P) (fun w => (F.ex k P w).left) θ fr')
    (s s' : LB.Sec (PPx (F.u k P))) (hs : GlobalTheory.Frames.SecGen (F.u k P) s)
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx (F.u k P)), pt ≫ gxFst (F.u k P) = (F.ex k P z).left →
      pt ≫ gxSnd (F.u k P) = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (F.u k P)).U (fun _ => j)) (s.f (fun _ => j)) = κ * θ z * fr j z)
    (hv' : ∀ j z (pt : Sp ℂ ⟶ Gx (F.u k P)), pt ≫ gxFst (F.u k P) = (F.ex k P z).left →
      pt ≫ gxSnd (F.u k P) = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (F.u k P)).U (fun _ => j)) (s'.f (fun _ => j)) = κ * θ z * fr' j z) :
    ∀ i, s'.f i = s.f i := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.sec_values_complex_fibre hT E H Dw l Xo (F.u k P) s
  obtain ⟨a, ha, -⟩ := hs s'
  have hw : ∀ z, (F.ex k P z).left ≫ Xo.univ.t.G.hom = 𝟙 (Sp ℂ) ≫ F.u k P := fun z =>
    (Over.w (F.ex k P z)).trans (Category.id_comp _).symm
  obtain ⟨j, hj⟩ := GlobalTheory.FrameUnif.ThetaPtEx.exists_chart_top Xo.univ.t.PP.isLB (F.ex k P 0).left
  have hn : {z | ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} ∈ nhds (0 : Fin g → ℂ) :=
    (isOpen_ex F k P hP _).mem_nhds hj
  have key : fr' j 0 - a * fr j 0 = 0 := by
    refine eq_zero_of_mul_eventually θ (fun z => fr' j z - a * fr j z) hθ hne
      (((hf'.1 j).differentiableAt hn).continuousAt.sub
        (continuousAt_const.mul ((hf.1 j).differentiableAt hn).continuousAt)) ?_
    filter_upwards [hn] with z hz
    let pt : Sp ℂ ⟶ Gx (F.u k P) :=
      pullback.lift (f := (Over.mk (F.u k P)).hom) (g := Xo.univ.t.G.hom) (𝟙 _) (F.ex k P z).left (hw z).symm
    have p1 : pt ≫ gxFst (F.u k P) = (F.ex k P z).left := pullback.lift_snd _ _ _
    have p2 : pt ≫ gxSnd (F.u k P) = 𝟙 (Sp ℂ) := pullback.lift_fst _ _ _
    have e' := (congrArg (valAt' pt ((PPx (F.u k P)).U (fun _ => j))) (ha (fun _ => j))).trans (h1 a _ pt p2)
    rw [hv j z pt p1 p2 hz, hv' j z pt p1 p2 hz] at e'
    refine mul_left_cancel₀ hκ ?_
    linear_combination e'
  have h00 : fr' j 0 = fr j 0 := (hf'.2.2.2.1 j hj).trans (hf.2.2.2.1 j hj).symm
  have ha1 : a = 1 := by
    refine mul_right_cancel₀ (hf.2.1 j 0 hj) ?_
    rw [h00] at key
    linear_combination -key
  refine h3 s' fun i pt hp => ?_
  have e' := (congrArg (valAt' pt ((PPx (F.u k P)).U i)) (ha i)).trans (h1 a _ pt hp)
  rw [e', ha1, one_mul]

theorem sum_single_of_support {J : Type} {m : J → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : J, Fin (m τ)) (τ : J)
    (v : Fin g → ℂ) (hv : ∀ jj, v jj ≠ 0 → (e jj).1 = τ) :
    ∑ k : Fin (m τ), v (e.symm ⟨τ, k⟩) • (Pi.single (e.symm ⟨τ, k⟩) 1 : Fin g → ℂ) = v := by
  funext jj
  rw [Finset.sum_apply]
  by_cases h : (e jj).1 = τ
  · obtain ⟨⟨τ', k⟩, rfl⟩ := e.symm.surjective jj
    obtain rfl : τ' = τ := by simpa using h
    rw [Finset.sum_eq_single k (fun b _ hb => ?_) (by simp)]
    · simp
    · have : e.symm ⟨τ', k⟩ ≠ e.symm ⟨τ', b⟩ := fun hh => hb (by simpa using (e.symm.injective hh).symm)
      simp [Pi.single_eq_of_ne this]
  · have h0 : v jj = 0 := by_contra fun h' => h (hv jj h')
    rw [h0]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : jj ≠ e.symm ⟨τ, b⟩ := fun hh => h (by rw [hh]; simp)
    simp [Pi.single_eq_of_ne this]

theorem isUnit_det_of_support {J : Type} {m : J → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : J, Fin (m τ)) (τ : J)
    (v : Fin (m τ) → Fin g → ℂ) (hl : LinearIndependent ℂ v) (hv : ∀ i jj, v i jj ≠ 0 → (e jj).1 = τ) :
    IsUnit (Matrix.of fun i k : Fin (m τ) => v i (e.symm ⟨τ, k⟩)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
  rw [Fintype.linearIndependent_iff] at hl ⊢
  intro cf hc
  refine hl cf (funext fun jj => ?_)
  by_cases h : (e jj).1 = τ
  · obtain ⟨⟨τ', k⟩, rfl⟩ := e.symm.surjective jj
    obtain rfl : τ' = τ := by simpa using h
    have := congrFun hc k
    simpa [Finset.sum_apply, Matrix.row] using this
  · rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have h0 : v b jj = 0 := by_contra fun h' => h (hv b jj h')
    simp [h0]

theorem existsUnique_anFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ w : ℂ, Ha.T < w.im → ∃! y, AnFr Ha Θ z w y := by
  intro _ L2 E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha th Θ z _ hz w hw
  have hT := L2.secTwist
  have hP := Ha.period w hw
  obtain ⟨hsym, hpos⟩ := Θ.pos w hw
  obtain ⟨hd, w₀, hw₀⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero Uw.g Θ.c₁ Θ.c₂ Θ.half₁ Θ.half₂).1 _ hsym hpos
  have hθd : Differentiable ℂ (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v)) :=
    hd.comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Θ.h)).differentiable
  have hθ : ∃ v, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v) ≠ 0 := by
    refine ⟨∑ k, w₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1)), ?_⟩
    have : Θ.h.mulVec (∑ k, w₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = w₀ := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, (Θ.per w _).1]
      exact (pi_eq_sum_univ' w₀).symm
    rwa [this]
  obtain ⟨-, hder, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ Uw.F Ha.i _ hP
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨u, hu, htan, heig, hbas⟩ := GlobalTheory.T.exists_tangent_eigenbasis_exponential E H Dw l Xo c σ Uw.g Uw.e Uw.F Ha.i _ hP
    obtain ⟨fr, hfr⟩ := Θ.frame w hw
    obtain ⟨s, hs⟩ := hfr.2.2.2.2
    obtain ⟨t, ht, hval⟩ := GlobalTheory.FrameUnif.ThetaPtEx.exists_gen hT (Uw.F.u Ha.i (Ha.Pw w)) (Uw.F.ex Ha.i (Ha.Pw w))
      (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v)) fr Θ.κ Θ.κ_ne hθ hfr.2.1 s hs
    let y₀ : FrPt Xo c (CAt σ) := ⟨Uw.F.u Ha.i (Ha.Pw w), Uw.F.over_σ _ _ hP, u, htan, heig, hbas, t, ht⟩
    have hch := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c (CAt σ) y₀
    obtain ⟨⟨x', xo', u', tan', eig', basis', s', gen'⟩, ⟨hx, hc, -⟩, -⟩ :=
      hch (fun τ => (Matrix.of fun i k : Fin (Dw.mult τ) => z τ i (Uw.e.symm ⟨τ, k⟩) : Matrix _ _ ℂ)) 1
        (fun τ => isUnit_det_of_support Uw.e τ (z τ) (hz τ).1 (hz τ).2)
    dsimp only [y₀] at hx hc
    subst hx
    refine ⟨⟨Uw.F.u Ha.i (Ha.Pw w), xo', u', tan', eig', basis', t, ht⟩, ⟨rfl, fun τ i => ?_⟩, fr, hfr, hval⟩
    have := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ Uw.F Ha.i _ hP _ (u τ) _ (hu τ)
      (fun k => z τ i (Uw.e.symm ⟨τ, k⟩)) (u' τ i)).1 (hc τ i)
    rwa [sum_single_of_support Uw.e τ (z τ i) ((hz τ).2 i)] at this
  · rintro ⟨x, xo, u, tan, eig, basis, s, gen⟩ ⟨x', xo', u', tan', eig', basis', s', gen'⟩
      ⟨⟨hx, hu⟩, fr, hfr, hs⟩ ⟨⟨hx', hu'⟩, fr', hfr', hs'⟩
    dsimp only at hx hu hs hx' hu' hs'
    subst hx hx'
    obtain rfl : u = u' := funext fun τ => funext fun i => (hder _).unique (hu τ i) (hu' τ i)
    have hss := gen_unique hT Uw.F Ha.i _ hP _ hθd hθ Θ.κ Θ.κ_ne fr fr' hfr hfr' s s' gen hs hs'
    obtain rfl : s = s' := by
      cases s; cases s'
      congr 1
      exact (funext hss).symm
    rfl

end GlobalTheory.ArcQ.AnFrEx
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.ConstTanFormal

theorem corr_of_genRelR {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    {B B₀ Y₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen)
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt' : K → (Sp A' ⟶ B)}
    {pt₀ : K → (Y₀ ⟶ B₀)} {g : LB.Gen (LB.LinComb M pt ε)} {t : LB.Gen (LB.LinComb M pt' ε)}
    {ν : LB.Gen (LB.LinComb M₀ pt₀ ε)} (hg : g.IsGen) (ht : t.IsGen) (hν : ν.IsGen) {r : Sp A' ⟶ Sp A}
    {κ : Sp A ⟶ Y₀} {κ' : Sp A' ⟶ Y₀} (hκ : r ≫ κ = κ') (hp : ∀ k, pt' k = r ≫ pt k)
    (h : GenRelR w g (LB.pullGen _ _ _ ν κ)) (h' : GenRelR w t (LB.pullGen _ _ _ ν κ')) :
    LB.Gen.Corr M _ _ _ _ t (LB.pullGen M _ _ g r) := by
  have hw' := (isGen_iff w).1 hw
  have H := ConstGrp.pmaps_of_genRelR hw' hM hM₀ hg (DVR.pullGen_isGen _ _ _ _ hν κ) h
  have H' := ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht (DVR.pullGen_isGen _ _ _ _ hν κ') h'
  refine corr_of_val hM fun y J' hJ' => ?_
  choose J hJ using fun ψ : Sp A' ⟶ B₀ => exists_chart hM₀ (ψ y)
  have v := CubTransport.val_pmaps (fun k => (h.1 k).trans (Category.id_comp _).symm) H r hJ hJ'
  have v' := CubTransport.val_pmaps (fun k => (h'.1 k).trans (Category.id_comp _).symm) H' (𝟙 _) hJ hJ'
  rw [val_pull hJ, Category.comp_id, hκ] at v
  rw [val_pull hJ, Category.comp_id, Category.id_comp] at v'
  rw [val_pull hJ', Category.id_comp]
  simp only [Category.id_comp, hp] at v'
  exact mul_left_cancel (v'.symm.trans v)

theorem dualMapR_surjective {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} (h : Function.Surjective φ) :
    Function.Surjective (dualMapR φ) := fun a => by
  obtain ⟨x, hx⟩ := h a.fst
  obtain ⟨y, hy⟩ := h a.snd
  exact ⟨TrivSqZeroExt.inl x + TrivSqZeroExt.inr y, by ext <;> simp [hx, hy]⟩

theorem ker_dualMapR_mk {R : Type} [CommRing R] (I : Ideal R) :
    RingHom.ker (dualMapR (Ideal.Quotient.mk I)) ≤ I.map (algebraMap R (DualNumber R)) := fun a ha => by
  have h₁ : a.fst ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (by
    simpa using congrArg TrivSqZeroExt.fst (RingHom.mem_ker.1 ha))
  have h₂ : a.snd ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (by
    simpa using congrArg TrivSqZeroExt.snd (RingHom.mem_ker.1 ha))
  have e : a = algebraMap R (DualNumber R) a.fst + algebraMap R (DualNumber R) a.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ h₁) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h₂))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (g : ℕ) (ex₀ : (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W ex₀ z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W g ex₀ z₀ ν v g₁ hD hT
  refine FormalValue.isFormalPt_of_surjective _ fun e => ?_
  let I : Ideal ℂ⟦X⟧ := Ideal.span {PowerSeries.X}
  have hI : I ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PowerSeries.X_prime.not_isUnit
  have : IsLocalRing (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := isLocalRing_quotient_pow hI e
  have := isLocalRing_dual (ℂ⟦X⟧ ⧸ I ^ (e + 1))
  have := isLocalRing_dual ℂ⟦X⟧
  let ρ : DualNumber ℂ⟦X⟧ →+* DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := dualMapR (Ideal.Quotient.mk _)
  let s : Sp (DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1))) ⟶ Sp (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := spMap (algebraMap _ _)
  have hs : s ≫ Out.thick ℂ⟦X⟧ I e = spMap ρ ≫ (epsR ℂ⟦X⟧).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => (dualMapR_inl (Ideal.Quotient.mk (I ^ (e + 1))) r).symm)
  let xe : Sp (DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1))) ⟶ (Out.thickObj ℂ⟦X⟧ I e W.t.G).left :=
    pullback.lift (spMap ρ ≫ v.left) s (by rw [Category.assoc, Over.w v, hs])
  have hx : xe ≫ (Out.fstG I e W.t.G).left = spMap ρ ≫ v.left := pullback.lift_fst _ _ _
  have hx' : xe ≫ ((Over.map (Out.thick ℂ⟦X⟧ I e)).obj (Out.thickObj ℂ⟦X⟧ I e W.t.G)).hom =
      spMap ρ ≫ (epsR ℂ⟦X⟧).hom :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pullback.lift_snd _ _ _)).trans hs)
  have hκ : spMap ρ ≫ spMap constEps = spMap (ρ.comp constEps) := (Spec.map_comp _ _).symm
  have h' := hD.2.2 e ρ (ρ.comp constEps) xe (dualMapR_inl _) (dualMapR_eps _)
    (fun r => (congrArg ρ (dualMapR_inl _ r)).trans (dualMapR_inl _ _))
    ((congrArg ρ (dualMapR_eps _)).trans (dualMapR_eps _)) hx
  have hp : ∀ x k, xe ≫ W.P.D.toPre.Oφ (W.P.U.gt e).pG (W.e x) k =
      spMap ρ ≫ Out.DegPre.gtφT W.P.D.toPre (epsR ℂ⟦X⟧) g₁.b (W.e x) k := fun x k => by
    refine W.spec.1.1.hom_ext ?_ ?_
    · refine ((h' x).1 k).trans ?_
      exact (congrArg (· ≫ _) hκ.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap ρ ≫ ·) ((hT x).1 k).symm).trans (Category.assoc _ _ _).symm))
    · rw [Category.assoc, Category.assoc]
      refine Eq.trans ?_ (hx'.trans ?_)
      · refine congrArg (xe ≫ ·) ?_
        fin_cases k <;> exact Over.w _
      · refine congrArg (spMap ρ ≫ ·) ?_
        fin_cases k <;> exact (Over.w _).symm
  refine ⟨_, inferInstance, ρ, xe, dualMapR_surjective Ideal.Quotient.mk_surjective, ?_, hx, hp 0 2, fun y => ?_⟩
  · rw [idealEps, ← Ideal.map_pow]
    exact ker_dualMapR_mk _
  · obtain ⟨x, rfl⟩ := W.e.surjective y
    exact corr_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB (g₁.isGen _)
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt e).t_gen _) xe) (ν.isGen x) hκ (hp x) (hT x) (h' x)

end GlobalTheory.ConstTanFormal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

theorem _root_.GlobalTheory.T.firstOrderJet_constSection_mul_coordinate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (jt₀ : Fin 4 → a.D₀.P.L.ι), IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (h.symm z)).b.left)) z₀ ν.b.left → (∀ x j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (Λ.ex0 (h.symm 0)) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (Λ.ex0 (h.symm z)) x j) 0 z₀)) → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀ → valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀) ((ν.s (Λ.ε α)).s jt₀).val = jet (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) (h.symm z₀) * jet (fun v : Λ.A.V => Λ.u.fr (jt₀ 2) v.2) (h.symm z₀) ^ j := by
  first | exact @GlobalTheory.ConstTanJet.jet_sec_mul_coord | exact GlobalTheory.ConstTanJet.jet_sec_mul_coord | (intros; apply GlobalTheory.ConstTanJet.jet_sec_mul_coord <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

theorem _root_.GlobalTheory.T.constantSection_mul_coord_dualNumberPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (j : ℕ) (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) (jM : W.P.D.toPre.P.L.ι) (jf jt : Fin 4 → W.P.D.toPre.P.L.ι) (jt₀ : Fin 4 → a.D₀.P.L.ι), TanRel W ν g₁ → IsConstMul W j x s₀ f r → FormalValue.CohCharts g₁ (W.e x) jM jf jt → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀ → valR (A := DualNumber ℂ⟦X⟧) g₁.b.left _ (W.w.s (fun _ => jt₀ 2, jM)).val ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e x) jt) = TrivSqZeroExt.inl r * constEps (valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB x) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀) ((ν.s x).s jt₀).val) := by
  first | exact @GlobalTheory.ConstTanAlg.main | exact GlobalTheory.ConstTanAlg.main | (intros; apply GlobalTheory.ConstTanAlg.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_abelianTriple_iso_of_same_point_values : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ), ∃ (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)), IsRigIso m.cm o₁.t.PP o₂.t.PP w ∧ ∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j' := by
  first | exact @GlobalTheory.FamilyIso.exists_sabMap_of_same_values | exact GlobalTheory.FamilyIso.exists_sabMap_of_same_values | (intros; apply GlobalTheory.FamilyIso.exists_sabMap_of_same_values <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecFibre

theorem specPts_isFibAt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ lin cst, IsFactor A lin cst → ∃ T' ≥ Ψ.T, IsHolTo {w : ℂ | T' < w.im} Ψ.yw ∧ ∀ w : ℂ, T' < w.im → IsFibAt A o.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w) := by
  intro hL hL2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hR lin cst hF
  obtain ⟨T₁, hT₁, h₁⟩ := GlobalTheory.T.specialisedPoints_holomorphic_quasiPeriodic hL hL2 E H D l B bb S s o A y Φ Γ Ψ hA hR lin cst hF
  obtain ⟨T₂, hT₂, h₂⟩ := GlobalTheory.T.thetaSections_extend_germRings_and_span_fibres hL hL2 E H D l B bb S s o A y Φ Γ Ψ hA hR 1
  obtain ⟨T₀, hT₀⟩ := A.exists_isConvLine
  have hc := (GlobalTheory.HalfPoint.holomorphic_curve S Ψ.T Ψ.yT Ψ.yw Ψ.yw_eq).1
  have hle : Ψ.T ≤ max (max T₁ T₂) T₀ := le_trans hT₁ (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨max (max T₁ T₂) T₀, hle, ?_, ?_⟩
  · intro U f
    obtain ⟨ho, hd⟩ := hc U f
    have hsub : ∀ w : ℂ, max (max T₁ T₂) T₀ < w.im → Ψ.T < w.im := fun w hw => lt_of_le_of_lt hle hw
    refine ⟨?_, hd.mono fun w hw => ⟨hsub w hw.1, hw.2⟩⟩
    have h3 : IsOpen {w : ℂ | max (max T₁ T₂) T₀ < w.im} := isOpen_lt continuous_const Complex.continuous_im
    convert h3.inter ho using 1
    ext w
    exact ⟨fun h => ⟨h.1, hsub w h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  · intro w hw
    have hw₁ : T₁ < w.im := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hw
    have hw₂ : T₂ < w.im := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hw
    have hw₃ : T₀ < w.im := lt_of_le_of_lt (le_max_right _ _) hw
    have hw₀ : Ψ.T < w.im := lt_of_le_of_lt hT₁ hw₁
    obtain ⟨a1, a2, a3, a4⟩ := GlobalTheory.SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w hw₀
    obtain ⟨b1, b2, b3, b4⟩ := h₁ w hw₁
    obtain ⟨σt, -, σ₀, -, c1, -⟩ := h₂ w hw₀ hw₂
    exact ⟨a1, a2, b1, b2, b3, a3, a4, b4, fun th hth => ⟨σ₀ 0 th, c1 0 th hth⟩,
      fun th hth v => AnArc.summable_term hT₀ one_ne_zero hth hw₃ v⟩

end GlobalTheory.SpecFibre
end
