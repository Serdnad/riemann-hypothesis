module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1938
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.kernel_route_big_vertex_rational_left_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g : GA D (G.V (.grid i (j + 1))), kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := by
  first | exact @GlobalTheory.BigRouteInv.kerBig_rat_mul | exact GlobalTheory.BigRouteInv.kerBig_rat_mul | (intros; apply GlobalTheory.BigRouteInv.kerBig_rat_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.continuous_translates_kernel_route_small_vertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
      translates z (kerSmall W Θ' p.1 g₁) p.2) := by
  first | exact @GlobalTheory.SmallRoute.continuous_translates_kerSmall | exact GlobalTheory.SmallRoute.continuous_translates_kerSmall | (intros; apply GlobalTheory.SmallRoute.continuous_translates_kerSmall <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.ddcLeviForm_eq_zero_of_complexLine_invariant : ∀ (n : ℕ) (u : V n → ℝ) (z ξ η : V n), ContDiffAt ℝ 2 u z → (∀ (x : V n) (c : ℂ), u (x + c • ξ) = u x) → ddc u z ξ η = 0 ∧ ddc u z η ξ = 0 := by
  first | exact @GlobalTheory.ddc_eq_zero_of_invariant | exact GlobalTheory.ddc_eq_zero_of_invariant | (intros; apply GlobalTheory.ddc_eq_zero_of_invariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.BotSmall

theorem bottom_small : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (δ t0 : ℂ) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) (i j : Fin D.R.m) 𝔪, IsBottom G μ₀ i j 𝔪 P P' → P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap) := by
  intro D T L sc μ₀ hL G δ t0 Q P P' i j 𝔪 hB
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hB.rank
  have hd : P.d ≤ 2 * bigN D := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    have hj := j.2
    obtain ⟨e1, e2, -⟩ := ranks_exact D i j
    have h1 : rankV D (i + 1) (j + 1) ≤ bigN D - 1 := by
      simp only [rankV, bigN, Ranks.r]
      have : (↑i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
      have : (↑j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
      have : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
      omega
    have h2 : rankV D i j ≤ rankV D (i + 1) (j + 1) := by
      simp only [rankV]
      have : (↑i) * sLen D ≤ (↑i + 1) * sLen D := Nat.mul_le_mul_right _ (by omega)
      have : (↑j) * D.R.t ≤ (↑j + 1) * D.R.t := Nat.mul_le_mul_right _ (by omega)
      omega
    omega

  have key : ∀ (R : Pair D ⊤ δ t0 Q) (χ : Formalism.L2.Host.HChar D.host.E),
      HasChars R χ (nuH G μ₀ i j)⁻¹ → R.d = botBig D i j + botSmall D i j → ∀ τ, (R.n τ : ℝ) ≤ 2 * (maxWt D sc.cGap : ℝ) := by
    intro R χ hc hRd τ
    have habs := GlobalTheory.SplitWeight.abs_weight_eq_abs_infType R.W.chV' R.W.ep' (nuH G μ₀ i j)⁻¹ _ R.W.ep_pm.2 hc.2
      (nuH_inv_hasInf hL G i j) τ
    have hw := R.wt τ
    have hsub := two_mul_wtA_sub D sc.cGap i j τ
    set E := (num D sc.cGap τ).e (↑j + 1) + cen D sc.cGap τ (D.R.m - ↑i)
    have hA : (wtA D sc.cGap i j τ).natAbs ≤ maxWt D sc.cGap ∧ (wtA' D sc.cGap i j τ).natAbs ≤ maxWt D sc.cGap := by
      have := Finset.le_sup (f := fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
        max (wtA D sc.cGap x.1 x.2.1 x.2.2).natAbs (wtA' D sc.cGap x.1 x.2.1 x.2.2).natAbs) (Finset.mem_univ (i, j, τ))
      have h2 := le_max_right 1 (Finset.univ.sup fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
        max (wtA D sc.cGap x.1 x.2.1 x.2.2).natAbs (wtA' D sc.cGap x.1 x.2.1 x.2.2).natAbs)
      simp only at this
      exact ⟨le_trans (le_max_left _ _) (this.trans h2), le_trans (le_max_right _ _) (this.trans h2)⟩
    have hA1 : |wtA D sc.cGap i j τ| ≤ (maxWt D sc.cGap : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hA.1
    have hA2 : |wtA' D sc.cGap i j τ| ≤ (maxWt D sc.cGap : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hA.2
    have hep : |(R.W.ep' : ℤ) * R.W.chV'.n τ| = |2 * E| := by
      rw [abs_mul, ← habs]
      rcases R.W.ep_pm.2 with h | h <;> rw [h] <;> simp
    have hdz : (R.d : ℤ) = (botBig D i j : ℤ) + (botSmall D i j : ℤ) := by rw [hRd]; push_cast; ring
    have hn : (R.n τ : ℤ) ≤ 2 * (maxWt D sc.cGap : ℤ) := by
      have hnn : (0 : ℤ) ≤ R.n τ := Nat.cast_nonneg _
      have hpos : 0 ≤ (R.W.ep' : ℤ) * R.W.chV'.n τ := by push_cast at hw; omega
      rw [abs_of_nonneg hpos] at hep
      have h1 := abs_le.1 hA1
      have h2 := abs_le.1 hA2
      rcases le_or_gt 0 E with hE | hE
      · rw [abs_of_nonneg (by omega)] at hep
        push_cast at hw hsub; omega
      · rw [abs_of_neg (by omega)] at hep
        push_cast at hw hsub; omega
    exact_mod_cast hn
  exact ⟨⟨hd, key P _ hB.chars hr3⟩, ⟨hr4 ▸ hd, key P' _ hB.chars' (hr4.trans hr3)⟩⟩

end GlobalTheory.BotSmall
end

section

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.CosetTheta

variable {D : D7}

theorem conj_ne_bot {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) : D.host.conj • 𝔪 ≠ ⊥ := by
  intro h
  apply h𝔪
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
  simpa [inv_smul_smul] using this

theorem mul_mem_one {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {y : D.host.E}
    (hy : y ∈ (((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) :
    ((Ideal.absNorm (D.host.conj • 𝔪) : ℕ) : D.host.E) * y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hJ : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (conj_ne_bot h𝔪)
  rw [FractionalIdeal.coe_div hJ, Submodule.mem_div_iff_forall_mul_mem] at hy
  have hn : ((Ideal.absNorm (D.host.conj • 𝔪) : ℕ) : D.host.E) ∈
      ((((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) :
        Submodule (𝓞 D.host.E) D.host.E) := by
    rw [FractionalIdeal.coe_coeIdeal, IsLocalization.mem_coeSubmodule]
    exact ⟨_, Ideal.absNorm_mem _, by simp⟩
  have h2 := hy _ hn
  rw [FractionalIdeal.coe_coeIdeal, IsLocalization.mem_coeSubmodule] at h2
  obtain ⟨z, -, hz⟩ := h2
  rw [Submodule.mem_one]
  exact ⟨z, by rw [hz, mul_comm]⟩

theorem nsmul_mem_homL {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ} {A : Matrix (Fin d) (Fin a) D.host.E}
    (hA : A ∈ homL D (stdL D a) (skewLat D 𝔪 d)) :
    Ideal.absNorm (D.host.conj • 𝔪) • A ∈ homL D (stdL D a) (stdL D d) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    apply Submodule.subset_span
    intro x hx
    have h := hA x hx
    rw [skewLat, Submodule.mem_pi] at h
    rw [stdL, Submodule.mem_pi]
    intro i _
    rw [Matrix.smul_mulVec, Pi.smul_apply, nsmul_eq_mul]
    exact mul_mem_one h𝔪 (h i trivial)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem nsmul_mem_YYl {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ} {B : Matrix (Fin d) (Fin a) D.host.E}
    (hB : B ∈ YYl D (stdL D a) (skewLat D 𝔪 d)) :
    Ideal.absNorm (D.host.conj • 𝔪) • B ∈ YYl D (stdL D a) (stdL D d) := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA, rfl⟩ := hB
    apply Submodule.subset_span
    exact ⟨c, hc, _, nsmul_mem_homL h𝔪 hA, smul_comm _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem absNormConj_smul_mem_stdThetaLattice {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {a d : ℕ}
    {x : VC D a d} (hx : x ∈ La D (tor0 D cc δ) (stdL D a) (skewLat D 𝔪 d)) :
    Ideal.absNorm (D.host.conj • 𝔪) • x ∈ La0 D (tor0 D cc δ) a d := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    refine ⟨w, hw, _, nsmul_mem_YYl h𝔪 hA, ?_⟩
    funext τ i j
    simp only [embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem u_mem_TT {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ} {x : VC D N N'} {M : ℕ}
    (hM : 0 < M) (hx : M • x ∈ La0 D (tor0 D cc δ) N N') {F : VC D N N' → ℂ} (hF : F ∈ TT D (tor0 D cc δ) N N') :
    U D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) N N' := by
  have hw : wdPh D (tor0 D cc δ) x ≠ 0 := by simp [wdPh, ee, Complex.exp_ne_zero]
  have e : U D (tor0 D cc δ) x F = (wdPh D (tor0 D cc δ) x)⁻¹ • Wd D (tor0 D cc δ) x F := by
    funext z
    simp only [Wd, Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_cancel_left₀ hw]
  rw [e]
  exact NormUniq.tt_smul (GlobalTheory.T.thetaFunction_rationalTranslate_mem hc hM hx hF) _

theorem iop_mem_TT {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ} {La₂ : AddSubgroup (VC D N N')}
    {M : ℕ} (hM : 0 < M) (hLa : ∀ x ∈ La₂, M • x ∈ La0 D (tor0 D cc δ) N N') {F : VC D N N' → ℂ}
    (hF : F ∈ TT D (tor0 D cc δ) N N') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') La₂ F ∈ TT D (tor0 D cc δ) N N' := by
  classical
  by_cases h : ((La0 D (tor0 D cc δ) N N').addSubgroupOf La₂).index = 0
  · have e : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') La₂ F = 0 := by
      funext z
      simp [Iop, h]
    rw [e]
    exact NormUniq.tt_zero _
  · have : ((La0 D (tor0 D cc δ) N N').addSubgroupOf La₂).FiniteIndex := ⟨h⟩
    haveI : Fintype (La₂ ⧸ (La0 D (tor0 D cc δ) N N').addSubgroupOf La₂) := Fintype.ofFinite _
    have e : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') La₂ F =
        ((Real.sqrt (((La0 D (tor0 D cc δ) N N').addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) •
          ∑ q : La₂ ⧸ (La0 D (tor0 D cc δ) N N').addSubgroupOf La₂,
            al D (tor0 D cc δ) ((Quotient.out q : La₂) : VC D N N') •
              U D (tor0 D cc δ) ((Quotient.out q : La₂) : VC D N N') F := by
      funext z
      simp only [Iop, finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [e]
    exact NormUniq.tt_smul (NormUniq.tt_sum _ fun q _ =>
      NormUniq.tt_smul (u_mem_TT hc hM (hLa _ (Quotient.out q : La₂).2) hF) _) _

theorem cosetVec_mem_TT : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ →
    ∀ o : ℕ, cosetVec P 𝔪 o ∈ TT D (tor0 D ⊤ δ) P.a P.d := by
  intro D δ t0 Q P 𝔪 h𝔪 o
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d := VacMove.vac_TT h1 P.crv P.vac.1
  have hM : 0 < Ideal.absNorm (D.host.conj • 𝔪) :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact conj_ne_bot h𝔪)
  have hI := iop_mem_TT P.crv hM (fun x hx => absNormConj_smul_mem_stdThetaLattice h𝔪 hx) he
  unfold cosetVec
  exact NormUniq.tt_smul (GlobalTheory.T.thetaFunction_rationalTranslate_mem P.crv one_pos
    (by rw [one_smul]; exact pt_unitBlock_mem δ o P.a P.d) hI) _

end GlobalTheory.FunObj.CosetTheta
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

theorem _root_.GlobalTheory.T.twist_and_nu_ramified_place_degree_one_exponent_two : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → IsBaseCond (condF G.pl) → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → ¬ (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ (q : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 ∧ ExpAt (nuH G μ₀ i j) w 2 := by
  first | exact @GlobalTheory.BadPlaceExp.main | exact GlobalTheory.BadPlaceExp.main | (intros; apply GlobalTheory.BadPlaceExp.main <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.thetaPoint_mem_standard_and_skewLattice_of_entries_mem : ∀ (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (w : Matrix (Fin d) (Fin a) D.host.E), (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) → pt D (tor0 D ⊤ δ) δ w ∈ La0 D (tor0 D ⊤ δ) a d ∧ pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) := by
  first | exact @GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem | exact GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem | (intros; apply GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem <;> assumption)
end

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BottomNu

theorem exists_heckeU_nu_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m), ∃ χ : HeckeU D (botBig D i j + botSmall D i j), (∀ x, χ.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) ∧ ∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χ.n τ := by
  intro D T L sc μ₀ hL G i j
  have hu : (nuH G μ₀ i j)⁻¹.IsUnitary := by
    have h := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G μ₀ i j hL)
    intro x
    have e : (((nuH G μ₀ i j)⁻¹).1 x : ℂˣ) = ((nuH G μ₀ i j).1 x)⁻¹ := rfl
    rw [e, Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have htriv : (nuH G μ₀ i j)⁻¹.TrivOn D.host.F := by
    have h1 := (L.C.isMu0 j).triv
    have h2 := G.ch.triv (D.R.m - i) hm.1 hm.2
    have h3 : (L.xiH μ₀).TrivOn D.host.F := hL.xi_triv μ₀
    exact (((h1.mul h3).mul h2.inv)).inv
  have hp : ∀ τ, Even (2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i)) -
      ((botBig D i j + botSmall D i j : ℕ) : ℤ)) := by
    intro τ
    obtain ⟨h1, h2, -⟩ := ranks_exact D i j
    obtain ⟨u, hu⟩ := D.R.t_odd
    obtain ⟨v, hv⟩ := odd_sLen D
    have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
    obtain ⟨w, hw⟩ : ∃ w : ℕ, botBig D i j + botSmall D i j = 2 * w := ⟨(botBig D i j + botSmall D i j) / 2, by omega⟩
    refine ⟨(GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i) - w, ?_⟩
    rw [hw]; push_cast; ring
  have hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) →
      (nuH G μ₀ i j)⁻¹.1 (finIdl D u) = 1 := by
    obtain ⟨M, hM, h⟩ := GlobalTheory.T.exists_nat_heckeCharacter_trivial_congruent_units D.host.E (nuH G μ₀ i j)⁻¹
    refine ⟨M, hM, fun u hu ⟨s, hs, e⟩ => h _ (GlobalTheory.Mem.Col2.SplitChar.finIdl_unit hu)
      (fun w => by rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_fst]; rfl) fun P => ?_⟩
    rw [GlobalTheory.Mem.Col2.SplitChar.vl_sub_one, e, map_mul, GlobalTheory.Mem.Col2.SplitChar.vl_nat,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact mul_le_of_le_one_right' (GlobalTheory.Mem.Col2.SplitChar.vl_le hs P)
  exact ⟨GlobalTheory.SplitCharGen.ofHChar _ (nuH G μ₀ i j)⁻¹ _ hu (GlobalTheory.T.squareNu_inv_hasInfinityType_cmType hL G i j) hp hc
    (GlobalTheory.T.heckeCharacter_trivial_subfield_kills_idele_norms D _ htriv (GlobalTheory.T.exists_nat_heckeCharacter_trivial_congruent_units D.host.E _)) (GlobalTheory.T.heckeCharacter_unramified_inert_kills_units D _ fun P hP => GlobalTheory.T.squareNu_inv_unramified_over_inert_prime hL G i j P hP), fun x => rfl, fun τ => GlobalTheory.T.bottomRanks_sum_le_two_exponent_add_centre D sc.cGap i j τ⟩

end GlobalTheory.BottomNu
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

theorem _root_.GlobalTheory.T.gridConductorIdealCM_isCoprime_halfDifferent : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L), Nat.Coprime D.host.pde (D.host.QS * D.host.q) → Nat.Coprime D.host.pde' (D.host.QS * D.host.q) → IsCoprime (condE P) D.host.𝔟 := by
  first | exact @GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb | exact GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb | (intros; apply GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.meanValuation_ge_of_integral_at_prime : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {β : ℂ} {p : K[X]}, GlobalTheory.FunObj.SqNum.IsMinPol σ β p → β ≠ 0 → ∀ {c : K}, c ≠ 0 → ∀ {l : ℕ}, l.Prime → ∀ {w : Formalism.PairingDivisionLocalBalance.Pl K}, (l : 𝓞 K) ∈ w.asIdeal → ∀ {m : ℕ}, GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ m * (σ c * β)) → -((m : ℝ) * (Formalism.DivisionValues.vw w (l : K) : ℝ)) ≤ (Formalism.DivisionValues.vw w c : ℝ) + GlobalTheory.FunObj.SqNum.meanVal_vw w p := by
  first | exact @GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt | exact GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt | (intros; apply GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem _root_.GlobalTheory.T.squareBottomPairs_weights_eq : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T) (i j : Fin D.R.m)
    (𝔪 : Ideal (𝓞 D.host.E)) {δ t0 : ℂ} {Q : ℕ} (P P' : Pair D ⊤ δ t0 Q), IsBottom G t i j 𝔪 P P' → P'.n = P.n := by
  first | exact @GlobalTheory.BottomWeights.isBottom_n_eq | exact GlobalTheory.BottomWeights.isBottom_n_eq | (intros; apply GlobalTheory.BottomWeights.isBottom_n_eq <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.exists_addChar_thetaCommutatorPhase_skewLattice : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}, ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), ∃ χ : AddChar ((La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) ℂ, ∀ y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), χ (y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d) := by
  first | exact @GlobalTheory.CommPhase.chars | exact GlobalTheory.CommPhase.chars | (intros; apply GlobalTheory.CommPhase.chars <;> assumption)
end
