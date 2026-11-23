module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle089
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle050
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle085
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle088
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle081
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle080
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle064
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.OrthoMetric

namespace GlobalTheory.SupFull

theorem hm_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x : (U.X k).dom) (W : PullbackSections.UnfAt U k x) (Wu : PullbackSections.UnitAt W), (U.X k).IsOrtho x.1 → Wu.Hm = Matrix.diagonal fun j => ((2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k x W Wu hx
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij
    Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  have hper : ∀ (v : Fin r → E) j, perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2 =
      if (((W.e.trans f) j).2 : ℕ) < (U.X k).p0 then
        FD.hermC ((W.e.trans f) j).1.1 (U.X k).Gm
          (FD.col (FD.mat x.1 ((W.e.trans f) j).1) ((W.e.trans f) j).2) (FD.Data.emb ((W.e.trans f) j).1.1 v)
      else ((FD.mat x.1 ((W.e.trans f) j).1)⁻¹.mulVec (FD.Data.emb ((W.e.trans f) j).1.1 v))
        ((W.e.trans f) j).2 := by
    intro v j
    have h := hf (W.e j)
    rw [Equiv.trans_apply]
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    generalize ((W.e j).2 : ℕ) = i at h ⊢
    dsimp only at h ⊢
    rw [← hp0] at h
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dite_eq_right a, dif_pos (show conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have key : Wu.Hm = Matrix.diagonal fun j => ((2 * (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) := by
    refine PullbackSections.UH.herm_eq_of_im W.Pm W.per.2.2.2.1 _ _ fun a b => ?_
    rw [Wu.c1, OrthoHerm.im_diag_eq_trace (U.X k).p0 _ (U.X k).Gm (U.X k).Ψ (U.X k).cmType (W.e.trans f) hcc x.1 hx
      (W.φ k a) (W.φ k b) _ _ (fun j => (W.pm_eq a j).trans (hper _ j)) (fun j => (W.pm_eq b j).trans (hper _ j)),
      ← W.isom, Rat.cast_intCast]
  have hd : ∀ j, (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖ := by
    intro j
    have hn : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖((W.e.trans f) j).1.1 (U.X k).ξ0‖ := by
      rcases hf (W.e j) with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · rw [Equiv.trans_apply, h]
      · rw [Equiv.trans_apply, h]
        exact (Complex.norm_conj _).symm
    rw [hn]
    clear hn
    have hpos := Wu.pos (Pi.single j 1) (by simp)
    rw [key, hermForm, single_dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Pi.single_eq_same, star_one,
      _root_.one_mul, _root_.mul_one, Complex.ofReal_re] at hpos
    generalize ((W.e.trans f) j).1.1 = τ at hpos ⊢
    have hre : (τ (-(U.X k).ξ0)).re = 0 := by
      have h := congrArg τ hcc
      rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg τ (-(U.X k).ξ0)] at h
      have := congrArg Complex.re h
      simp only [Complex.conj_re, Complex.neg_re] at this
      linarith
    have hp : 0 < (τ (-(U.X k).ξ0)).im := by linarith
    rw [← norm_neg, ← map_neg, ← Complex.abs_im_eq_norm.mpr hre, abs_of_pos hp]
  rw [key]
  simp only [hd]

theorem isMetric_of_isOrtho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (x : (U.X k).dom), (U.X k).IsOrtho x.1 → IsMetric (U.un k x) 1 (fun b => ((2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ : ℝ) : ℂ) • 1) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hpq k x hx
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := hm_eq_diagonal E H Dw l Xo c σ r U hσ hU k x W Wu hx
  obtain ⟨Φ₀⟩ := nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (secNZ_of_secGen lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩ := exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2 Wu.c3 Wu.c4
    Wu.c5 Wu.c6 Wu.c7
  choose w hw using fun τ i => hD _ _ ((U.un k x).tan τ i) (W.der τ i)
  have hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume := hΛ ▸ Wu.c8
  have hN := Wu.c9.symm
  have hG : ∀ (b : E →+* ℂ) (i j : Fin (Dw.mult b)),
      (((2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ : ℝ) : ℂ) • (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) i j =
        Real.pi * hermForm Wu.Hm (Pi.single (W.e.symm ⟨b, j⟩) 1) (Pi.single (W.e.symm ⟨b, i⟩) 1) := by
    intro b i j
    rw [hH]
    simp [hermForm, Matrix.mulVec_diagonal, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all <;> ring
  exact isMetricAt_of Φ hg u Wu.Hm χ Wu.θ Wu.Fd w (fun b i => Pi.single (W.e.symm ⟨b, i⟩) 1)
    ⟨ht, hA, hR, hF, hFd, hN, hw, hG⟩

theorem isBddSec_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U U' : Unf Xo c σ r), GoodEmb c σ → IsUnf U → IsUnf U' → 1 ≤ Dw.p + Dw.q → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, (∀ k, (U.X k).IsBddSec (laU U a n k) (rdU U f k)) → ∀ k, (U'.X k).IsBddSec (laU U' a n k) (rdU U' f k) := by
  intro E _ _ _ H Dw l Xo c σ r U U' hσ hU hU' hpq a n hd f hf hb k'
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, -, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hs' := hU'.2.2.2.2.1 a n hd f hf k'
  choose C hC using fun k => (hb k).2
  have hpos : ∀ (X : FD.Data E r) (b : E →+* ℂ), 0 < 2 * Real.pi * ‖relab c σ b X.ξ0‖ := fun X b =>
    mul_pos (by positivity) (norm_pos_iff.2 ((map_ne_zero _).2 X.ξ0_ne))
  let κ : U.Comp → (E →+* ℂ) → ℝ := fun k b =>
    2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ / (2 * Real.pi * ‖relab c σ b (U'.X k').ξ0‖)
  let B : U.Comp → ℝ := fun k =>
    (∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2)) * |C k|
  refine ⟨hs', ∑ k, B k, fun x₁ hx₁ => ?_⟩
  obtain ⟨b, hbB, ho⟩ := (FD.orthonormalFlagTranslate_holds r (U'.X k')).1 x₁ hx₁
  have hx' := FD.OrthogonalFrameDomain.rmul_mem_dom (U'.X k') hx₁ hbB
  rw [← (FD.orthonormalFlagTranslate_holds r (U'.X k')).2.1 _ _ hs'.2.1 x₁ hx₁ b hbB,
    PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ ho)]
  have hN := isMetric_of_isOrtho E H Dw l Xo c σ r U' hσ hU' hpq k' ⟨_, hx'⟩ ho
  have hrd' : ‖rdU U' f k' (FD.rmul x₁ b)‖ = cabs (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := by
    have e : rdU U' f k' (FD.rmul x₁ b) = toC (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := dif_pos hx'
    rw [e]; rfl
  rw [hrd']
  generalize U'.un k' ⟨_, hx'⟩ = y at hN ⊢
  obtain ⟨k, x, t, hx, ht⟩ := GlobalTheory.T.exists_orthonormalFrame_borelChange_complexFramedPoint E H Dw l Xo c σ r U hU y
  obtain ⟨g, hg0, hgd, hchg⟩ :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y y).1 t).1 ht
  have hm0 := isMetric_of_isOrtho E H Dw l Xo c σ r U hσ hU hpq k x hx
  have hm1 := GlobalTheory.T.metric_change_of_frame E H Dw l Xo c σ (U.un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨hNN, hG⟩ := GlobalTheory.T.metric_data_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hnone : cabs (t none : CAt σ) = 1 := by
    rw [_root_.mul_one] at hNN
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hNN.symm
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), cabs (t (some p) : CAt σ) = (Real.sqrt (κ k p.1))⁻¹ := by
    rintro ⟨τ, i⟩
    rw [← hgd τ i]
    refine OrthoBound.norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _
      (div_pos (hpos _ _) (hpos _ _)) (fun i j hij => hg0 τ j i hij) ?_ i
    have h1 := (congrFun hG τ).symm
    have h2 : ((2 * Real.pi * ‖relab c σ τ (U'.X k').ξ0‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos _ _).ne'
    dsimp only at h1
    rw [Complex.ofReal_div, div_eq_inv_mul, mul_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have hev := hwt (CAt σ) (GlobalTheory.FrameNorm.Comparison₂.isReduced_cAt σ) a n f hf t _ _ ht
  have hw : cabs (wchar (ex Dw a n) t) =
      ∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2) := by
    rw [GlobalTheory.FrameNorm.Comparison₂.cabs_wchar, Fintype.prod_option, hnone, one_pow, _root_.one_mul]
    exact Finset.prod_congr rfl fun p _ => by rw [hsome p]; rfl
  have hrd : ‖rdU U f k x.1‖ = cabs (evR Xo c f (U.un k x)) := by
    have e : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
    rw [e]; rfl
  have hle := hC k x.1 x.2
  rw [PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ hx), hrd] at hle
  have hB0 : ∀ k, 0 ≤ B k := fun k => mul_nonneg (Finset.prod_nonneg fun p _ => by positivity) (abs_nonneg _)
  rw [hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, hw]
  exact (mul_le_mul_of_nonneg_left (hle.trans (le_abs_self _)) (Finset.prod_nonneg fun p _ => by positivity)).trans
    (Finset.single_le_sum (f := B) (fun k _ => hB0 k) (Finset.mem_univ k))

end GlobalTheory.SupFull
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

open AlgebraicGeometry Filter GlobalTheory.CompHt
open scoped ENNReal

set_option autoImplicit false

namespace GlobalTheory.ImageDegree

theorem growth_eq_of_tendsto (D : ℕ) (r : ℕ → ℕ) {c : ℝ} (hc : 0 ≤ c)
    (h : Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (nhds (c / D.factorial))) :
    growth D (fun m => (r m : ℕ∞)) = ENNReal.ofReal c := by
  have hf : (0 : ℝ) < D.factorial := by positivity
  have h2 : Tendsto (fun m : ℕ => ENNReal.ofReal ((D.factorial : ℝ) * ((r m : ℝ) / (m : ℝ) ^ D))) atTop
      (nhds (ENNReal.ofReal c)) := by
    refine ENNReal.tendsto_ofReal ?_
    have := h.const_mul (D.factorial : ℝ)
    rwa [mul_div_cancel₀ _ hf.ne'] at this
  refine (Tendsto.limsup_eq ?_)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm.ne')
  have hm'' : (m : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top m)
  rw [ENat.toENNReal_coe, mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast]

theorem ringKrullDim_of_birational {k : Type} [Field k] (S : LinSys k) (h : S.IsVariety) (hb : S.BasePointFree)
    (hB : S.Birational) : ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = (S.D + 1 : ℕ) :=
  GlobalTheory.T.ringKrullDim_cone_image_of_birational_linearSystem k S h hb hB

theorem finrank_quotientPiece_le_lineBundleSections {k : Type} [Field k] (S : LinSys k) (h : S.IsVariety) (m : ℕ) :
    Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) ≤ lbH0 k (lbPow S.L m) :=
  GlobalTheory.T.quotient_piece_finrank_le_h0 k S h m

theorem rankGrowth_lineBundleSections_le_image_forms {k : Type} [Field k] [CharZero k] (S : LinSys k) (h : S.IsVariety) (hb : S.BasePointFree)
    (hB : S.Birational) :
    growth S.D (fun m => (lbH0 k (lbPow S.L m) : ℕ∞)) ≤
      growth S.D (fun m => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) :=
  GlobalTheory.T.rankGrowth_lineBundle_sections_le_image_forms k S h hb hB

theorem topologicalKrullDim_eq {k : Type} [Field k] (S : LinSys k) (h : S.IsVariety) :
    topologicalKrullDim S.Y = S.D := by
  have := HeightExists.isIntegral h
  have hc (U : S.Y.Opens) (hU : IsAffineOpen U) (hne : (U : Set S.Y).Nonempty) :
      topologicalKrullDim (U : Set S.Y) = S.D := by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(S.Y, U))).trans
      (SmoothDim.ringKrullDim_affineOpen k _ S.str _ h.smooth U hU hne)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    exact ⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (genericPoint S.Y))
    exact (hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

theorem degree_image_eq_topSelf : Quoted → ∀ (F : Type) [Field F] [NumberField F] (S : LinSys F), S.IsVariety → S.BasePointFree →
    S.Birational → 0 < S.del ∧ (hilbertDegree S.imageIdeal : ℤ) = S.del ∧
      ringKrullDim (MvPolynomial (Fin S.N) F ⧸ S.imageIdeal) = (S.D + 1 : ℕ) := by
  intro Q F _ _ S hV hb hB
  have hdim := ringKrullDim_of_birational S hV hb hB
  have hp := HeightExists.isPrime_imageIdeal hV
  have hI := S.isHomogeneous_imageIdeal
  have hdeg := degree_idealHilbertPoly_eq_of_isPrime hI hdim
  have hHG := (growth_of_eventually_eq_eval S.D 1 (fun m => Module.finrank F (quotPiece S.imageIdeal (m : ℤ)))
    (idealHilbertPoly S.imageIdeal) le_rfl (eventually_finrank_quotPiece hI)).1 hdeg.le (hilbertDegree S.imageIdeal)
    (cast_hilbertDegree_of_degree_eq hI hdeg)
  simp only [one_mul, Nat.cast_one, one_pow] at hHG
  have hHG' : growth S.D (fun m => (Module.finrank F (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) = hilbertDegree S.imageIdeal := by
    refine Eq.trans ?_ hHG
    congr 1
    funext m
    rw [one_mul]
  have hstr : strHom F S.Y = S.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom F (X := S.Y)) := hstr ▸ hV.proj
  have hnef : IsNef F S.L := IsGenerated.isNef_of_isProjOver ⟨S.N, S.b, hb⟩ hV.proj
  have hYd := topologicalKrullDim_eq S hV
  have h0 := Q.nef.2.2.topSelf_nonneg hproj hYd hnef
  have hG := growth_eq_of_tendsto S.D (fun m => lbH0 F (lbPow S.L m)) (Int.cast_nonneg h0)
    (Q.nef.2.2.tendsto hproj hYd hnef)
  have hle1 : growth S.D (fun m => (Module.finrank F (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) ≤
      growth S.D (fun m => (lbH0 F (lbPow S.L m) : ℕ∞)) :=
    limsup_le_limsup (Eventually.of_forall fun m => ENNReal.div_le_div_right (mul_le_mul_right
      (ENat.toENNReal_le.2 (Nat.cast_le.2 (finrank_quotientPiece_le_lineBundleSections S hV m))) _) _)
  have hle2 := rankGrowth_lineBundleSections_le_image_forms S hV hb hB
  rw [hHG', hG] at hle1 hle2
  have e : (hilbertDegree S.imageIdeal : ℝ≥0∞) = ENNReal.ofReal (topSelfIntersection F S.L S.D : ℝ) := le_antisymm hle1 hle2
  have e' : ((hilbertDegree S.imageIdeal : ℝ) : ℝ) = (topSelfIntersection F S.L S.D : ℝ) := by
    rw [← ENNReal.ofReal_natCast] at e
    exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (Int.cast_nonneg h0)).1 e
  have hdel : (hilbertDegree S.imageIdeal : ℤ) = S.del := by
    rw [LinSys.del]; exact_mod_cast e'
  obtain ⟨Ω, _, _, x, hx, -⟩ := HeightExists.exists_generic hV
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero x.1)
  have hX : (X j : MvPolynomial (Fin S.N) F) ∉ S.imageIdeal := fun hX => hj (by simpa using S.eval₂_coords_eq_zero x.1 hX)
  have hpos := hilbertDegree_pos hI hX
  exact ⟨hdel ▸ (by exact_mod_cast hpos), hdel, hdim⟩

end GlobalTheory.ImageDegree
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanJac

theorem derivation_eq_zero {F N : Type} [Field F] [NumberField F] [AddCommGroup N] [Module F N]
    (δ : Derivation ℤ F N) (a : F) : δ a = 0 := by
  haveI : Algebra.FormallyEtale ℤ ℚ := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyEtale ℚ F := Algebra.FormallyEtale.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℤ F := Algebra.FormallyUnramified.comp ℤ ℚ F
  rw [← δ.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D ℤ F a) 0,
    map_zero]

theorem snd_eq_zero {F K : Type} [Field F] [NumberField F] [Field K] (χ : F →+* DualNumber K)
    (a : F) : (χ a).snd = 0 := by
  letI : Module F K := ((TrivSqZeroExt.fstHom K K K).toRingHom.comp χ).toModule
  let δ : Derivation ℤ F K := Derivation.mk'
    { toFun := fun x => (χ x).snd
      map_add' := fun x y => by rw [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun n x => by
        rw [map_zsmul, TrivSqZeroExt.snd_smul]
        rfl }
    (fun x y => by
      change (χ (x * y)).snd = (χ x).fst * (χ y).snd + (χ y).fst * (χ x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, mul_comm (χ x).snd])
  exact derivation_eq_zero δ a

theorem exists_forms_map {k A K : Type} [CommRing k] [CommRing A] [Field K] {D : ℕ}
    (α : k →+* A) (ψ : A →+* K) (φ : Fin D → A →+* DualNumber K)
    (hφ : ∀ b x, (φ b x).fst = ψ x) (hc : ∀ b a, (φ b (α a)).snd = 0) :
    ∃ Λ : Forms α D →ₛₗ[ψ] K,
      ∀ f, Λ (dForm α f) = (Matrix.of fun a b => (φ b (f a)).snd).det := by
  letI := α.toAlgebra
  letI := ψ.toAlgebra
  letI : Algebra k K := (ψ.comp α).toAlgebra
  haveI : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let δ (f : A) : Fin D → K := fun b => (φ b f).snd
  have hmul (f g : A) : δ (f * g) = f • δ g + g • δ f := by
    funext b
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    simp only [δ, map_mul, TrivSqZeroExt.snd_mul, hφ, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    change _ = ψ f * _ + ψ g * _
    ring
  have hδc (a : k) : δ (algebraMap k A a) = 0 := funext fun b => hc b a
  let d : Derivation k A (Fin D → K) := Derivation.mk'
    { toFun := δ
      map_add' := fun f g => by
        funext b
        simp only [δ, map_add (f := _), TrivSqZeroExt.snd_add, Pi.add_apply]
      map_smul' := fun a f => by
        rw [Algebra.smul_def, hmul, hδc, smul_zero, add_zero, algebraMap_smul]
        rfl } hmul
  let det : (Fin D → K) [⋀^Fin D]→ₗ[A] K :=
    { (Matrix.detRowAlternating (n := Fin D) (R := K)).toMultilinearMap.restrictScalars A with
      map_eq_zero_of_eq' := (Matrix.detRowAlternating (n := Fin D) (R := K)).map_eq_zero_of_eq }
  let Λ := exteriorPower.alternatingMapLinearEquiv (det.compLinearMap d.liftKaehlerDifferential)
  refine ⟨⟨Λ.toAddHom, Λ.map_smul⟩, fun f => ?_⟩
  refine (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans ?_
  simp only [AlternatingMap.compLinearMap_apply, Derivation.liftKaehlerDifferential_comp_D]
  rfl

end GlobalTheory.TanJac

namespace GlobalTheory.TanJac

theorem det_mul_jacobian_comm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] (z : Sp K ⟶ M.X) (i : M.K.bundle.ι)
    (w : Fin (dimFlag Dw) → (Sp (DualNumber K) ⟶ M.X))
    (hw : ∀ b, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = z)
    (O O' : M.X.Opens) (hO : O ≤ M.K.bundle.U i) (hO' : O' ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (g' : Fin (dimFlag Dw) → Γ(M.X, O'))
    (hz : ⊤ ≤ z ⁻¹ᵁ O) (hz' : ⊤ ≤ z ⁻¹ᵁ O') (hwO : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O) (hwO' : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O'), (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd).det * evalPt z O' hz' (M.K.jacobian i hO' g') =
      (Matrix.of fun a b => (evalPt (w b) O' (hwO' b) (g' a)).snd).det * evalPt z O hz (M.K.jacobian i hO g) := by
  intro E _ _ _ H Dw l Xo c Y X Z M K _ z i w hw O O' hO hO' g g' hz hz' hwO hwO'
  let x0 := z.base (IsLocalRing.closedPoint K)
  have hx0 : x0 ∈ O ⊓ O' := ⟨hz (Set.mem_univ _), hz' (Set.mem_univ _)⟩
  obtain ⟨V, hV, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens hx0
  have hV' : IsAffineOpen V := hV
  have hVO : V ≤ O := hVle.trans inf_le_left
  have hVO' : V ≤ O' := hVle.trans inf_le_right
  have hzV : ⊤ ≤ z ⁻¹ᵁ V := ((IsLocalRing.closedPoint_mem_iff (z ⁻¹ᵁ V)).1 hxV).ge
  have hwV : ∀ b, ⊤ ≤ w b ⁻¹ᵁ V := fun b =>
    GlobalTheory.CompHS.le_preimage_of_dualNumber _ (w b) V (by rw [hw b]; exact hzV)
  have hfst : ∀ b f, (evalPt (w b) V (hwV b) f).fst = evalPt z V hzV f := by
    intro b f
    have e := evalPt_spMap_comp (TrivSqZeroExt.fstHom K K K).toRingHom (w b) V (hwV b)
      (by rw [hw b]; exact hzV) f
    have e' : ∀ (x : Sp K ⟶ M.X) (_ : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = x)
        (h₁ : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b) ⁻¹ᵁ V) (h₂ : ⊤ ≤ x ⁻¹ᵁ V),
        evalPt (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b) V h₁ f = evalPt x V h₂ f := by
      rintro x rfl h₁ h₂
      rfl
    rw [← e' z (hw b) (by rw [hw b]; exact hzV) hzV, e]
    rfl
  obtain ⟨Λ, hΛ⟩ := exists_forms_map (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str V) (evalPt z V hzV)
    (fun b => evalPt (w b) V (hwV b)) hfst
    (fun b a => snd_eq_zero ((evalPt (w b) V (hwV b)).comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str V)) a)
  have hVi : V ≤ M.K.bundle.U i := hVO.trans hO
  have key : ∀ (P : M.X.Opens) (hP : P ≤ M.K.bundle.U i) (hVP : V ≤ P)
      (f : Fin (dimFlag Dw) → Γ(M.X, P)) (hzP : ⊤ ≤ z ⁻¹ᵁ P) (hwP : ∀ b, ⊤ ≤ w b ⁻¹ᵁ P),
      (Matrix.of fun a b => (evalPt (w b) P (hwP b) (f a)).snd).det =
        evalPt z P hzP (M.K.jacobian i hP f) * Λ (resForm hVi (M.K.om i)) := by
    intro P hP hVP f hzP hwP
    have e := congrArg Λ (M.K.jacobian_smul_om i hV' hVi (fun a => resG M.X hVP (f a)))
    have e1 : Λ (dOn M.str (fun a => resG M.X hVP (f a))) =
        (Matrix.of fun a b => (evalPt (w b) V (hwV b) (resG M.X hVP (f a))).snd).det :=
      hΛ (fun a => resG M.X hVP (f a))
    have e2 : Λ (M.K.jacobian i hVi (fun a => resG M.X hVP (f a)) • resForm hVi (M.K.om i)) =
        evalPt z V hzV (M.K.jacobian i hVi (fun a => resG M.X hVP (f a))) *
          Λ (resForm hVi (M.K.om i)) :=
      Λ.map_smulₛₗ _ _
    rw [← evalPt_res z hVP hzP hzV, GlobalTheory.CanonLB.resG_jacobian, ← e2, e, e1]
    congr 1
    ext a b
    exact (congrArg TrivSqZeroExt.snd (evalPt_res (w b) hVP (hwP b) (hwV b) (f a))).symm
  have alg : ∀ (d d' A B C : K), d = A * C → d' = B * C → d * B = d' * A := by
    intro d d' A B C h h'
    rw [h, h']
    ring
  exact alg _ _ _ _ _ (key O hO hVO g hz hwO) (key O' hO' hVO' g' hz' hwO')

end GlobalTheory.TanJac
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_commuting_coordinate_derivations_regular_functions : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), ∃ d : Fin g → Derivation ℂ (Sec (str A) U) (Sec (str A) U), (∀ a b x, d a (d b x) = d b (d a x)) ∧ ∀ a x, ∀ z ∈ pre u.ex U, val u.ex U (d a x) z = fderiv ℂ (val u.ex U x) z (Pi.single a 1) := by
  first | exact @GlobalTheory.CechPer.exists_commuting_coordinate_derivations | exact GlobalTheory.CechPer.exists_commuting_coordinate_derivations | (intros; apply GlobalTheory.CechPer.exists_commuting_coordinate_derivations <;> assumption)
end
