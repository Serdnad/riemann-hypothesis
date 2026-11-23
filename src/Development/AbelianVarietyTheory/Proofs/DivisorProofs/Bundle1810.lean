module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.FockVac

theorem hasDerivAt_translate {n g : ℕ} (c : Fin g → ℝ) (H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ)
    (hH : ∀ z w, H z w = ∑ j, (c j : ℂ) * z j * conj (w j)) (F : (Fin n → Fin g → ℂ) → ℂ) (hF : Differentiable ℂ F)
    (Z A : Fin n → Fin g → ℂ) :
    HasDerivAt (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A)))
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b)) *
        (-(Real.pi * ∑ b, H (A b) (Z b)) * F Z + fderiv ℂ F Z A)) 0 := by
  have hc : ∀ z w, conj (H z w) = H w z := fun z w => by

    simp only [hH, map_sum, map_mul, conj_ofReal, conj_conj]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e : (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A))) =
      fun t : ℝ => (fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) + (-(Real.pi * ∑ b, H (A b) (Z b)) * u +
        -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) t := by
    funext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    have h1 : ∀ b, I * ((H (Z b) (((t : ℂ) • A) b)).im : ℂ) = t * (H (Z b) (A b) - H (A b) (Z b)) / 2 := fun b => by
      have h2 : H (Z b) (((t : ℂ) • A) b) = t * H (Z b) (A b) := by
        simp only [hH, Pi.smul_apply, smul_eq_mul, map_mul, conj_ofReal, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [h2, ← hc (Z b) (A b), Complex.sub_conj, Complex.im_ofReal_mul]
      push_cast
      ring
    have h3 : ∀ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b) =
        H (Z b) (Z b) + t * H (Z b) (A b) + t * H (A b) (Z b) + t ^ 2 * H (A b) (A b) := fun b => by
      simp only [hH, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_add (f := _), conj_ofReal, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [Complex.ofReal_sum, mul_assoc, Finset.mul_sum]
    simp only [h1, h3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  rw [e]
  refine HasDerivAt.comp_ofReal (e := fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) +
    (-(Real.pi * ∑ b, H (A b) (Z b)) * u + -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) ?_
  rw [Complex.ofReal_zero]
  have h1 : HasDerivAt (fun u : ℂ => Z + u • A) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const A).const_add Z
  have h2 : HasDerivAt (fun u : ℂ => F (Z + u • A)) (fderiv ℂ F Z A) 0 := by
    have := (hF (Z + (0 : ℂ) • A)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
    rwa [zero_smul, add_zero] at this
  have h3 := ((((hasDerivAt_id (0 : ℂ)).const_mul (-(Real.pi * ∑ b, H (A b) (Z b)))).fun_add
    ((hasDerivAt_pow 2 (0 : ℂ)).const_mul (-(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b))))).const_add
      (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b))).cexp.fun_mul h2
  refine h3.congr_deriv ?_
  simp only [id, zero_smul, add_zero, mul_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Nat.add_one_sub_one, pow_one]
  ring

theorem isFockVacAt_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (s τ)) f := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv f φ hf hR τ z
  obtain ⟨hd, -, hH⟩ := hx_of_isONFr _ r g V.rank X bas idx hs hev x hx0
  obtain ⟨-, hadd, hline, -⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x
  have hJ := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv).2.2 τ z
  have hF := GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hR.1 hd
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real (WeilVacMove.isTheta_add (WeilVacMove.isTheta_dRho hψ hθ τ z hf)
    (WeilVacMove.isTheta_smul I (WeilVacMove.isTheta_dRho hψ hθ τ _ hf))) fun w hw => ?_
  have hw' : w.map (finPart D) = 0 := hw
  have key : ∀ u, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ u f w =
      cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ u 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ u 1))) := fun u => by
    rw [← (hasDerivAt_translate _ _ hH _ hF _ _).deriv]
    unfold Formalism.IndefR.Datum.dRho
    congr 1
    funext t
    have h0 : (w + lineAt θ τ u t).map (finPart D) = 0 := by
      ext i j
      have h1 := congrFun (congrFun hw' i) j
      have h2 := congrFun (congrFun ((WeilVacMove.isLineAt_lineAt hθ τ u).2.1 t) i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at h1 h2
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply, map_add, h1, h2, add_zero]
    rw [heisO, GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x hx0 w _ hw', hR.2 _ h0, hadd, hline]
  have hI : ∀ a b : Fin g → ℂ, hx X bas idx x (I • a) b = I * hx X bas idx x a b := fun a b => by
    simp only [hH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [annih, Pi.add_apply, Pi.smul_apply, key, key, hJ, map_smul]
  simp only [Pi.smul_apply, hI, ← Finset.mul_sum, smul_eq_mul]
  linear_combination (cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ z 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ z 1)))) * I_mul_I

end GlobalTheory.AdTh.FockVac
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem leviForm_neg_log_unit_sub_log_grD : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)) (c : AlgChart X.str σ X.dim), y ∈ c.e.source →
      leviForm (fun v => -Real.log (‖ratVal u (c.e.symm v)‖ ^ 2) - Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) := by
  intro F _ σ X ι _ m k E H hH y A hA u hu τ i c hy
  obtain ⟨W, hW, a, rfl⟩ := hu.regAt.exists_fnOf
  have hyW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 hW
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := X.str) (σ := σ) W)
  have hm := ChartGlue.mem_over c.e hy hyW
  have hg := c.holo W a
  have hf : ContDiffAt ℂ 2 (ev X.str σ W a ∘ c.e.symm) (c.e y) :=
    (SCV.analyticAt_of_differentiableOn hg (ho.mem_nhds hm)).contDiffAt
  have h0 : (ev X.str σ W a ∘ c.e.symm) (c.e y) ≠ 0 := by
    have := ratVal_ne_zero hu
    rw [ratVal_fnOf hyW] at this
    simpa [Function.comp, c.e.left_inv hy] using this
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2)) (c.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have hsm := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y A hA τ).2 c hy).self_of_nhds
  have hG := (ldPart_grD_smooth _ _ _ _ hsm.1 hsm.2).2 i
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hsm.2).2.1 i).1
  have hD : ContDiffAt ℝ 2 (fun v => Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) :=
    (hG.log hpos.ne').of_le (WithTop.coe_le_coe.2 le_top)
  rw [leviForm_congr (u' := fun v => -Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2) +
      -Real.log (grD (H A (c.e.symm v) τ) i)), leviForm_add hlog.neg hD.neg,
    leviForm_neg (fun v => Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2)), leviForm_log_normSq_eq_zero hf h0,
    neg_zero, zero_add]
  filter_upwards [ho.mem_nhds hm] with v hv
  simp only [Function.comp, sub_eq_add_neg]
  rw [ratVal_fnOf hv.2]

end GlobalTheory.ChernCalc
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem contDiffOn_holoMap {n d : ℕ} {U : Set (V n)} (hU : IsOpen U) {p : V n → V d}
    (hp : DifferentiableOn ℂ p U) : ContDiffOn ℂ ∞ p U := by
  rw [contDiffOn_piLp]
  intro i
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ U hU
    ((EuclideanSpace.proj i : V d →L[ℂ] ℂ).differentiable.comp_differentiableOn hp)

theorem pull_chern_of_eventually {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n)
    (A' : HolAtlas M' n') {r : Type} [Fintype r] [DecidableEq r] {f : M' → M} (hf : A.IsHolo A' f) (G : M → Matrix r r ℂ)
    (G' T : M' → Matrix r r ℂ) (p : A'.Pt) (c : A.ι) (hc : f p.pt ∈ (A.e c).source) (hG : SmoothUnitAt A G (f p.pt))
    (hT : HolUnitAt A' T p.pt) (h : ∀ᶠ z in 𝓝 p.pt, G' z = T z * G (f z) * (T z)ᴴ) (j : ℕ) :
    pull (fderiv ℂ (A.e c ∘ f ∘ p.ch.symm) p.crd) (A.chern G j ⟨(c, f p.pt), hc⟩ : Alt n) = (A'.chern G' j p : Alt n') := by
  have hp : p.pt ∈ p.ch.source := p.2
  have hinv : p.ch.symm p.crd = p.pt := p.ch.left_inv hp
  have hU : IsOpen (p.ch.target ∩ p.ch.symm ⁻¹' (f ⁻¹' (A.e c).source)) :=
    p.ch.isOpen_inter_preimage_symm ((A.e c).open_source.preimage hf.1)
  have hmem : p.crd ∈ p.ch.target ∩ p.ch.symm ⁻¹' (f ⁻¹' (A.e c).source) :=
    ⟨p.ch.map_source hp, by rw [Set.mem_preimage, hinv]; exact hc⟩
  set ψ : V n' → V n := A.e c ∘ f ∘ p.ch.symm with hψ
  have hs : ContDiffAt ℂ ∞ ψ p.crd := (contDiffOn_holoMap hU (hf.2 p.1.1 c)).contDiffAt (hU.mem_nhds hmem)
  have hv : ψ p.crd = A.e c (f p.pt) := by simp only [hψ, Function.comp_apply, hinv]
  have hg : MContDiffAt ∞ (fun u => G ((A.e c).symm u)) (ψ p.crd) := hv ▸ (hG.2 c hc).self_of_nhds
  have hu : IsUnit (G ((A.e c).symm (ψ p.crd))).det := by rw [hv, (A.e c).left_inv hc]; exact hG.1
  have h1 := ((GlobalTheory.T.curvature_power_pullback_holomorphic n n' r (fun u => G ((A.e c).symm u)) ψ p.crd (hs.of_le (by norm_cast)) hg hu).2 j).2
  have hg' : MContDiffAt ∞ (fun x => G ((A.e c).symm (ψ x))) p.crd := fun a b =>
    (hg a b).comp p.crd (hs.restrict_scalars ℝ)
  have hTu : IsUnit (T (p.ch.symm p.crd)).det := by rw [hinv]; exact hT.1
  have hTd := hT.2 p.1.1 hp
  have ht : Tendsto p.ch.symm (𝓝 p.crd) (𝓝 p.pt) := by
    have := p.ch.continuousAt_symm (p.ch.map_source hp)
    rwa [ContinuousAt, p.ch.left_inv hp] at this
  have he : ∀ᶠ x in 𝓝 p.crd, G' (p.ch.symm x) =
      T (p.ch.symm x) * G ((A.e c).symm (ψ x)) * (T (p.ch.symm x))ᴴ := by
    filter_upwards [ht.eventually h, hU.mem_nhds hmem] with x hx hx'
    rw [hx]
    simp only [hψ, Function.comp_apply]
    rw [(A.e c).left_inv hx'.2]
  have h2 := (GlobalTheory.T.chernTransgression_forms_frame_invariant n' r _ _ (fun x => G' (p.ch.symm x)) (fun x => G' (p.ch.symm x)) (fun x => T (p.ch.symm x))
    (fun x => T (p.ch.symm x)) (fun x => T (p.ch.symm x)) p.crd hg' hu hg' hu hTd hTu hTd hTu hTd hTu
    (he.mono fun x hx => ⟨hx, hx⟩) j).2.1
  show pull _ (chernAt _ (A.e c (f p.pt)) j : Alt n) = (chernAt (fun v => G' (p.ch.symm v)) p.crd j : Alt n')
  rw [h2, h1, hv]

theorem pullback_chernF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ x : ι × ℕ, (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) (fld (atlas X σ) (chernF E H x)) = fld (atlas Y σ) (chernF E' (pullGram E H φ f hf) x) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH x
  funext p
  have hol := GlobalTheory.T.varietyComplexPointsMap_isHolomorphic F σ X Y f hf
  have hE := GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame F σ X Y ι m E E' φ f hf hR H hH
  have hA := (E.nonempty (under (ptMap σ f hf p.pt))).choose_spec
  have hB := (E'.nonempty (under p.pt)).choose_spec
  have hP := hR.sub (under p.pt) _ hB _ (by
    have := hA
    exact (congrArg (fun w => (E.nonempty (under (ptMap σ f hf p.pt))).choose ∈ E.S w) (hE p.pt).1).mp this) x.1
  refine pull_chern_of_eventually (atlas X σ) (atlas Y σ) hol (gramAt E H x.1 (ptMap σ f hf p.pt))
    (gramAt E' (pullGram E H φ f hf) x.1 p.pt)
    (fun z => (((E'.nonempty (under p.pt)).choose *
      (Mat.map (E.nonempty (under (ptMap σ f hf p.pt))).choose φ)⁻¹) x.1).map (ratVal · z)) p _ _
    (GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) _ _ hA x.1).1
    (GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ Y _ _ p.pt (fun i j => mem_O_ratOf.1 (hP.1 i j)) hP.2.1 (mem_O_ratOf.1 hP.2.2.1)) ?_ x.2
  filter_upwards [(hol.1.tendsto p.pt).eventually (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m 0 E _ _ hA),
    GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ Y ι m m E' _ _ hB] with z h1 h2
  exact (hE z).2 _ ((congrArg (fun w => (E.nonempty (under (ptMap σ f hf p.pt))).choose ∈ E.S w) (hE z).1).mp h1) _ h2 x.1

end GlobalTheory.ChernCalc
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernCalc

theorem powAt_coe_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (x : V n) (k : ℕ) :
    ((powAt G x k : Ev n) : Alt n) = ∑ i, (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) := by
  simp [powAt, Matrix.trace]

theorem transAt_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (x : V n) (k : ℕ) :
    transAt G G' x k = ∑ a, ∑ i ∈ Finset.range k, ∑ p, ∑ q,
      (conn G x (coordVec a) - conn G' x (coordVec a)) p q •
        ((((curvEv G' x ^ (k - 1 - i) * curvEv G x ^ i) q p : Ev n) : Alt n) * dz a) := by
  unfold transAt
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Algebra.smul_def, mul_assoc]

theorem powAt_transAt_smooth : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ k, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((powAt G x k : Alt n)) S) v) ∧ dbarAt (fun x => (powAt G x k : Alt n)) v = 0 ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (transAt G G' x k) S) v) := by
  intro n r _ _ G G' v hG hGu hG' hG'u k
  obtain ⟨hconst, hsum, hsmul, hmul⟩ := GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v
  obtain ⟨_, hdsum, _, _, _⟩ := GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v
  have hpe : ∀ i, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr
      (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) S) v) ∧
      dbarAt (fun x => (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n)) v = 0 :=
    fun i => GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G G' v hG hGu hG' hG'u k 0 i i
  have hpf : (fun x => ((powAt G x k : Ev n) : Alt n)) =
      fun x => ∑ i ∈ Finset.univ, (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) :=
    funext fun x => powAt_coe_eq_sum G G' x k
  refine ⟨?_, ?_, ?_⟩
  · simp only [powAt_coe_eq_sum G G']
    exact hsum r Finset.univ _ fun i _ => (hpe i).1
  · rw [hpf, hdsum r Finset.univ _ fun i _ S => ((hpe i).1 S).differentiableAt (by simp)]
    exact Finset.sum_eq_zero fun i _ => (hpe i).2
  · have hη : ∀ a p q, ContDiffAt ℝ ∞
        (fun x => (conn G x (coordVec a) - conn G' x (coordVec a)) p q) v := fun a p q =>
      ((hG.conn hGu (j := ∞) (by simp) (coordVec a)).sub
        (hG'.conn hG'u (j := ∞) (by simp) (coordVec a))) p q
    simp only [transAt_eq_sum]
    refine hsum _ Finset.univ _ fun a _ => hsum _ _ _ fun i _ => hsum _ Finset.univ _ fun p _ =>
      hsum _ Finset.univ _ fun q _ => hsmul _ _ (hη a p q) ?_
    exact hmul _ _ (GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).1 (hconst (dz a))

end GlobalTheory.ChernCalc
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.chernTopFormSignedMeasure_eq_atlas_part : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), ∀ (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ), chernTopPart E H R ε = (atlas X σ).part (evalF (atlas X σ) (chernF E H) R) ε := by
  first | exact @GlobalTheory.ChernCalc.chernTopPart_eq_part | exact GlobalTheory.ChernCalc.chernTopPart_eq_part | (intros; apply GlobalTheory.ChernCalc.chernTopPart_eq_part <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.chernTransgressionForm_holomorphic_pullback : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ∀ k, transAt (fun x => G (φ x)) (fun x => G' (φ x)) w k = pull (fderiv ℂ φ w) (transAt G G' (φ w) k) := by
  first | exact @GlobalTheory.ChernCalc.transAt_comp_holo | exact GlobalTheory.ChernCalc.transAt_comp_holo | (intros; apply GlobalTheory.ChernCalc.transAt_comp_holo <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem cInfAt_ratVal_on {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {κ : Type} [Fintype κ] {f : κ → X.Fn}
    {y : CxPts X.str σ} (hf : ∀ a, RegAt (under y) (f a)) {G : (κ → ℂ) → ℝ} {O : Set (κ → ℂ)} (hO : IsOpen O)
    (hG : ContDiffOn ℝ ∞ G O) (hy : (fun a => ratVal (f a) y) ∈ O) :
    CInfAt (fun z => G fun a => ratVal (f a) z) y := by
  choose U hyU g e using fun a => (hf a).exists_fnOf
  let W : X.X.Opens := ⟨⋂ a, U a, isOpen_iInter_of_finite fun a => (U a).isOpen⟩
  have hW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 (Set.mem_iInter.2 hyU)
  have hle (a) : W ≤ U a := Set.iInter_subset (fun a => (U a : Set X.X)) a
  have hev (z : CxPts X.str σ) (hz : z ∈ ptsIn X.str σ W) :
      (fun a => ev X.str σ W (resG X.X (hle a) (g a)) z) = fun a => ratVal (f a) z := by
    funext a
    rw [ev_res (hle a) hz, ← e a, ratVal_fnOf (ptsIn_mono (hle a) hz)]
  refine ⟨W, κ, inferInstance, fun a => resG X.X (hle a) (g a), G, O, hW, hO, ?_, hG, ?_⟩
  · rw [hev y hW]; exact hy
  · filter_upwards [(isOpen_ptsIn W).mem_nhds hW] with z hz
    rw [hev z hz]

theorem cInfAt_neg_log_normSq_ratVal {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {y : CxPts X.str σ} {u : X.Fn}
    (hu : UnitAt (under y) u) : CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2)) y := by
  have hO : IsOpen {w : Unit → ℂ | w () ≠ 0} := isOpen_ne_fun (continuous_apply ()) continuous_const
  have hG : ContDiffOn ℝ ∞ (fun w : Unit → ℂ => -Real.log (‖w ()‖ ^ 2)) {w | w () ≠ 0} := by
    intro w hw
    have h1 : ContDiffAt ℝ ∞ (fun w : Unit → ℂ => ‖w ()‖ ^ 2) w :=
      ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) ())).contDiffAt
    have h2 : ‖w ()‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hw)
    exact (h1.log h2).neg.contDiffWithinAt
  exact cInfAt_ratVal_on (κ := Unit) (f := fun _ => u) (fun _ => hu.regAt) hO hG (ratVal_ne_zero hu)

end GlobalTheory.ChernCalc


theorem GlobalTheory.ChernCalc.cInfAt_logUnit_grD : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)),
      CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2) - Real.log (grD (H A z τ) i)) y := by
  intro F _ σ X ι _ m k E H hH y A hA u hu τ i
  refine (GlobalTheory.ChernCalc.cInfAt_neg_log_normSq_ratVal hu).add ?_ |>.congr (Eventually.of_forall fun z => sub_eq_add_neg _ _)
  have := X.smooth_str
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
  have hev := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y A hA τ).2 c hc)
  obtain ⟨O, hOP, hOo, hyO⟩ := eventually_nhds_iff.1 hev
  have hS : IsOpen (c.e.source ∩ c.e ⁻¹' O) := c.e.isOpen_inter_preimage hOo
  refine cInfAt_of_chart hS c ?_ hc ⟨hc, hyO⟩
  intro v hv
  have hvO : v ∈ O := by
    have := hv.2.2
    rwa [Set.mem_preimage, c.e.right_inv hv.1] at this
  obtain ⟨hsm, hpd⟩ := hOP v hvO
  have hd := (ldPart_grD_smooth _ _ _ v hsm hpd).2 i
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hpd).2.1 i).1
  exact (hd.log hpos.ne').neg.contDiffWithinAt
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_lift_sections_zeroScheme_regularSequence_lineBundle : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (p : Y ⟶ Sp k) (M L : LB Y), M.IsLB → ∀ (hL : L.IsLB) (d : ℕ) (t : Fin d → L.Sec) (l : ℤ), RegSeq hL (GlobalTheory.LB.toMod M) (List.ofFn t) → VanishFrom L (GlobalTheory.LB.toMod M) 0 → (d : ℤ) ≤ l → ∀ (W : Y → Y.Opens) (b : ∀ y, Vanishing.H0 p (tw M L l) (W y)), (∀ y, y ∈ W y) → (∀ y z, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr inf_le_left (b y) - Vanishing.H0.restr inf_le_right (b z) : Vanishing.H0 p (tw M L l) (W y ⊓ W z))) → ∃ σ : Vanishing.H0 p (tw M L l) ⊤, ∀ y, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr le_top σ - b y) := by
  first | exact @GlobalTheory.HSCore.exists_glue_mod_regSeq | exact GlobalTheory.HSCore.exists_glue_mod_regSeq | (intros; apply GlobalTheory.HSCore.exists_glue_mod_regSeq <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspRep.ParLawsT

variable {E Ω : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

theorem locParT_eq_of_isLocComp (hT : UpperTheory.Zero.LLC.RecTExists) {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) (h : IsPlaceOver A w) :
    locParT hT (CG.mk π) h = locRecT hT h (cls (ParLaws.toRep σ)) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [locParT, CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl

theorem cls_loc_eq_of_isLocComp {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) :
    (⟨a, ParLaws.toCl ((CG.mk π).loc w)⟩ : IrrGL (k := w.adicCompletion E)) = cls (ParLaws.toRep σ) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl

theorem locParT_ofChar_eq (hT : UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) :
    locParT hT (CG.ofChar χ) h = locRecT hT h (.ofChar (χ.loc w) (ParLaws.isSmoothChar_loc χ w)) :=
  locParT_eq_of_isLocComp hT (CG.isLoc_ofChar χ w) h

end GlobalTheory.CuspRep.ParLawsT

theorem GlobalTheory.CuspRep.ParLawsT.locParT_twist : ∀ (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (π : CG E a) (χ : HChar E) (h : IsPlaceOver A w), UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl (π.loc w)⟩ : IrrGL (k := w.adicCompletion E)) → locParT hT (π.twist χ) h = (locParT hT π h).lpChar (locParT hT (CG.ofChar χ) h) := by
  intro hF hT E Ω _ _ _ _ _ _ A w a π χ h hg
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨_, _, H⟩ := isRecT_locRecT hT h
  have hg' : UpperTheory.Zero.LLC.Good (cls (ParLaws.toRep σ)) := cls_loc_eq_of_isLocComp hσ ▸ hg
  refine (locParT_eq_of_isLocComp hT (hσ.twist χ) h).trans ?_
  rw [locParT_ofChar_eq, show locParT hT (Quotient.mk _ π) h = _ from locParT_eq_of_isLocComp hT hσ h, ← H.twist _ _ _ hg']
  exact congrArg _ (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm

end
end
