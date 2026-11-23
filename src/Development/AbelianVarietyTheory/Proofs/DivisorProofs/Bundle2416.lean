module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle045
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle078
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle038
public import Formalism.PieriBlockIdeals.Bundle006
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LargeParameterEstimates
public import Formalism.SharpRestriction.Bundle001
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.SharpRestriction.Divisibility.JumpSets
public import Development.AutomorphicArithmetic.PrimeDiscriminants.ExcSet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp


noncomputable section

namespace GlobalTheory.PetDef

open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adelAut_of_gamma {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} (hχ : ∀ k la γ, γ ∈ (X k).Γ → (X k).χ la γ = 1) (hd : DictIsUnif V dict Kf th hr)
    (hm : MuUnit V dict mu) (hL : DictLoc V dict) (hmc : Continuous mu) : AdelAut V dict mu := by
  intro la P hP
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · obtain ⟨γ', hγ', he⟩ := hd.1 γ hγ g
    have hE := (eqv_holSub X la (holCusp_mem_holSub X la hP)).2 (dict g).1 γ' hγ' (dict g).2 (hd.2.2.2.1 g)
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [hE, hχ _ _ _ hγ', one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨N, hN, k, x, hx, hs⟩ := hL g₀
    have hsec : (X k).IsSec (la k) (P k) := (hP k).1.1
    have hPc : ContinuousOn (P k) (X k).dom := hsec.1.continuousOn
    have hc : ContinuousOn (fun g => mu g * P k (x g)) N :=
      hmc.continuousOn.mul (hPc.comp hx fun g hg => (hs g hg).1)
    have heq : (fun g => mu g * P k (x g)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      obtain ⟨hd', γ, hγ, he⟩ := hs g hg
      show mu g * P k (x g) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show mu g * P k (x g) = mu g * P k (lact γ (x g))
      rw [hsec.2.2 γ hγ (x g) hd', hχ _ _ _ hγ, one_mul]
    exact (hc.continuousAt hN).congr heq

end Gen

section Cover

variable {D : D7} {T : Core D} {j : ℕ}

theorem dictLoc_of_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ)
    (hσ : GoodEmb Y.d.c₂ σ) : ∃ th hr, DictIsUnif (D.sp.W j) (Y.dict σ) Y.Kf th hr ∧ DictLoc (D.sp.W j) (Y.dict σ) := by
  obtain ⟨th, hr, hth, hd⟩ := h.dictU σ hσ
  refine ⟨th, hr, hd, ?_⟩
  have hN : 0 < D.host.g 0 * D.host.g 1 * Y.d.pd := by
    rw [h.pd]
    exact Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) (pow_pos (by norm_num) _)
  have hK : Y.Kf ≤ GfC (D.sp.W j) := fun k hk => ((h.levelK k).1 hk).1
  exact GlobalTheory.DictLocTest.locClause_of_unif_places hd hK (GlobalTheory.T.principalLevel_mul_archimedean_mem_nhds D _ _ Y.Kf hN h.levelK) (fun c τ => ⟨_, hth c τ⟩)

theorem muUnit_one (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) :=
  ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, h.unit σ hσ⟩

theorem adelAut_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AdelAut (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, hL⟩ := dictLoc_of_good Y h σ hσ
  exact adelAut_of_gamma (fun k la γ hγ => GlobalTheory.CovTop.Model.chi_eq_one h σ hσ k la γ hγ) hd (muUnit_one Y h σ hσ) hL
    continuous_const

theorem aeDom_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AeDom Y.U σ (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, -⟩ := dictLoc_of_good Y h σ hσ
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)
  exact aeDom_of_aut Y.d.Xo₂ Y.d.c₂ (adelAut_good Y h σ hσ) (quotSupp_of _ hV hP) (muUnit_one Y h σ hσ) hd

end Cover

end GlobalTheory.PetDef
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.LargeParameterEstimates

theorem large_of_rows_pow {P : Par} {X' A : ℝ} (hH : P.Hyp) (hR : Rows P X' A) (hB : Big P.L P.x X' A)
    (h45 : P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S)
    (hpow : 4 * P.x ^ 2 * P.L ^ 2 * P.b ^ ((4 : ℝ) / 7) < P.b ^ ((4 : ℝ) / 5)) : P.Large := by
  have ht4 : (4 : ℝ) ≤ P.t := by
    have := hH.t_ge; have : 4 ≤ P.t := by omega
    exact_mod_cast this
  have hA1 : 1 ≤ A := by linarith [hR.t_le]
  have hx := hB.x_ge
  have hL := hB.L_ge
  have hA7 : A ^ 7 ≤ P.b := by
    have h3 := hB.b3
    have hx2 : (1 : ℝ) ≤ P.x ^ 2 := one_le_pow₀ (by linarith)
    have hL3 : (1 : ℝ) ≤ P.L ^ 3 := one_le_pow₀ (by linarith)
    have hA70 : 0 ≤ A ^ 7 := by positivity
    have : A ^ 7 ≤ 40 * A ^ 7 * P.x ^ 2 * P.L ^ 3 := by
      have h1 : (1 : ℝ) ≤ 40 * P.x ^ 2 * P.L ^ 3 := by nlinarith
      nlinarith
    exact this.trans h3
  have hA4 : A ^ 4 ≤ P.b ^ ((4 : ℝ) / 7) := by
    have e : (A ^ 7) ^ ((4 : ℝ) / 7) = A ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) hA7 (by norm_num)
  refine Formalism.CohomologicalDescent.LargeParameterEstimates.large_bound_of_constraints P X' A hH hR hB h45 ?_
  have hc : 0 ≤ 4 * P.x ^ 2 * P.L ^ 2 := by positivity
  calc 4 * A ^ 4 * P.x ^ 2 * P.L ^ 2 = (4 * P.x ^ 2 * P.L ^ 2) * A ^ 4 := by ring
    _ ≤ (4 * P.x ^ 2 * P.L ^ 2) * P.b ^ ((4 : ℝ) / 7) := mul_le_mul_of_nonneg_left hA4 hc
    _ = 4 * P.x ^ 2 * P.L ^ 2 * P.b ^ ((4 : ℝ) / 7) := by ring
    _ < P.b ^ ((4 : ℝ) / 5) := hpow

theorem w_over_S_real {x e k n Δ a1 a2 : ℝ} (hx : 0 < x) (hk : 0 ≤ k) (hn : 0 < n) (hS : 0 < k * (4 * Δ))
    (hkx : k ≤ x ^ a1) (hnx : n ≤ x ^ a2) (hΔ : Δ ≤ Real.exp (x ^ (e / 4) / 2))
    (E1 : 4 * x ^ (a1 + a2) ≤ Real.exp (1 / 10 * x ^ e)) (E2 : 20 * x ^ (e / 3) ≤ x ^ e)
    (E3 : 10 * x ^ (e / 4) ≤ x ^ e) :
    Real.exp (x ^ e) ^ ((4 : ℝ) / 5) ≤ x * Real.exp (x ^ e) / Real.exp (x ^ (e / 3)) / (x * n) / (k * (4 * Δ)) := by
  have hΔ0 : 0 ≤ Δ := by
    by_contra h; push_neg at h; nlinarith
  have hrhs : x * Real.exp (x ^ e) / Real.exp (x ^ (e / 3)) / (x * n) = Real.exp (x ^ e - x ^ (e / 3)) / n := by
    rw [Real.exp_sub]; field_simp
  rw [hrhs, le_div_iff₀ hS, ← Real.exp_mul, le_div_iff₀ hn]
  have hkn : k * n ≤ x ^ (a1 + a2) := by
    rw [Real.rpow_add hx]; exact mul_le_mul hkx hnx hn.le (by positivity)
  have h1 : k * (4 * Δ) * n ≤ Real.exp (1 / 10 * x ^ e) * Real.exp (x ^ (e / 4) / 2) := by
    calc k * (4 * Δ) * n = (4 * (k * n)) * Δ := by ring
      _ ≤ (4 * x ^ (a1 + a2)) * Real.exp (x ^ (e / 4) / 2) := by
          apply mul_le_mul (by linarith) hΔ hΔ0 (by positivity)
      _ ≤ Real.exp (1 / 10 * x ^ e) * Real.exp (x ^ (e / 4) / 2) :=
          mul_le_mul_of_nonneg_right E1 (by positivity)
  rw [← Real.exp_add] at h1
  have h2 : Real.exp (1 / 10 * x ^ e + x ^ (e / 4) / 2) ≤ Real.exp (x ^ e * (1 / 5) - x ^ (e / 3)) :=
    Real.exp_le_exp.2 (by linarith)
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos (x ^ e * ((4 : ℝ) / 5))).le
  rw [← Real.exp_add] at h3
  have e4 : x ^ e * ((4 : ℝ) / 5) + (x ^ e * (1 / 5) - x ^ (e / 3)) = x ^ e - x ^ (e / 3) := by ring
  rw [e4] at h3
  calc Real.exp (x ^ e * ((4 : ℝ) / 5)) * (k * (4 * Δ)) * n
      = Real.exp (x ^ e * ((4 : ℝ) / 5)) * (k * (4 * Δ) * n) := by ring
    _ ≤ _ := h3

theorem pow_real {x e : ℝ} (hx : 0 < x) (E : 5 * x ^ (2 + 2 * e) ≤ Real.exp (8 / 35 * x ^ e)) :
    4 * x ^ 2 * (x ^ e) ^ 2 * Real.exp (x ^ e) ^ ((4 : ℝ) / 7) < Real.exp (x ^ e) ^ ((4 : ℝ) / 5) := by
  rw [← Real.exp_mul, ← Real.exp_mul]
  have e1 : x ^ (2 + 2 * e) = x ^ 2 * (x ^ e) ^ 2 := by
    rw [Real.rpow_add hx, Real.rpow_two, mul_comm 2 e, Real.rpow_mul hx.le, Real.rpow_two]
  rw [e1] at E
  have hp : 0 < x ^ 2 * (x ^ e) ^ 2 := by have := Real.rpow_pos_of_pos hx e; positivity
  have h1 : 4 * x ^ 2 * (x ^ e) ^ 2 < Real.exp (8 / 35 * x ^ e) := by linarith
  have h2 := mul_lt_mul_of_pos_right h1 (Real.exp_pos (x ^ e * ((4 : ℝ) / 7)))
  rw [← Real.exp_add] at h2
  have e2 : 8 / 35 * x ^ e + x ^ e * ((4 : ℝ) / 7) = x ^ e * ((4 : ℝ) / 5) := by ring
  rwa [e2] at h2

end GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.LargeParameterEstimates

theorem ev_large (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    0 < x ∧
    4 * x ^ ((9 / 2 + 10 * eps + eps / 100) + (2 + 8 * eps + eps / 100)) ≤ Real.exp (1 / 10 * x ^ eps) ∧
    20 * x ^ (eps / 3) ≤ x ^ eps ∧ 10 * x ^ (eps / 4) ≤ x ^ eps ∧
    5 * x ^ (2 + 2 * eps) ≤ Real.exp (8 / 35 * x ^ eps) := by
  have E1 := Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_power_le_exp_mul_power 4 ((9 / 2 + 10 * eps + eps / 100) + (2 + 8 * eps + eps / 100)) (1 / 10) eps
    (by norm_num) he
  have E4 := Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_power_le_exp_mul_power 5 (2 + 2 * eps) (8 / 35) eps (by norm_num) he
  have E2 : ∀ᶠ x : ℝ in Filter.atTop, 20 ≤ x ^ (2 * eps / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have E3 : ∀ᶠ x : ℝ in Filter.atTop, 10 ≤ x ^ (3 * eps / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have E : ∀ᶠ x : ℝ in Filter.atTop, 0 < x ∧
      4 * x ^ ((9 / 2 + 10 * eps + eps / 100) + (2 + 8 * eps + eps / 100)) ≤ Real.exp (1 / 10 * x ^ eps) ∧
      20 * x ^ (eps / 3) ≤ x ^ eps ∧ 10 * x ^ (eps / 4) ≤ x ^ eps ∧
      5 * x ^ (2 + 2 * eps) ≤ Real.exp (8 / 35 * x ^ eps) := by
    filter_upwards [E1, E2, E3, E4, Filter.eventually_gt_atTop 0] with x e1 e2 e3 e4 hx
    refine ⟨hx, e1, ?_, ?_, e4⟩
    · have s : x ^ eps = x ^ (eps / 3) * x ^ (2 * eps / 3) := by
        rw [← Real.rpow_add hx]; congr 1; ring
      have := Real.rpow_pos_of_pos hx (eps / 3)
      rw [s]; nlinarith
    · have s : x ^ eps = x ^ (eps / 4) * x ^ (3 * eps / 4) := by
        rw [← Real.rpow_add hx]; congr 1; ring
      have := Real.rpow_pos_of_pos hx (eps / 4)
      rw [s]; nlinarith
  exact Filter.eventually_atTop.1 E

end GlobalTheory.ExpTie
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

namespace GlobalTheory.BigTop.Fun.PolBound

theorem log_le_posLog' (y : ℝ) : Real.log y ≤ Real.posLog y := by
  unfold Real.posLog; exact le_max_right _ _

theorem posLog_le_of_log_le {y B : ℝ} (hy : Real.log y ≤ B) (hB : 0 ≤ B) : Real.posLog y ≤ B := by
  unfold Real.posLog; exact max_le hB hy

theorem pol_core {C Q f m k t lb Lb : ℝ} (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hf0 : 0 ≤ f) (hf : f ≤ Q) (hm0 : 0 ≤ m)
    (hm : m ≤ Q) (hk0 : 0 ≤ k) (hk : k ≤ Q) (ht0 : 0 ≤ t) (ht : t ≤ Q) (hlb0 : 0 ≤ lb) (hlb : lb ≤ Q)
    (hLb : Lb ≤ 20 * Q) :
    100000 * C ^ 3 * f * m ^ 2 * (k + m * (t + (k + m + 5) + 1)) ^ 2 *
      ((k + m - 1) * (k + m * (t + (k + m + 5) + 1)) * lb + C * f ^ 2 * (k + m) ^ 6 * Lb) ≤
      13000000000 * C ^ 4 * Q ^ 16 := by
  set N := k + m * (t + (k + m + 5) + 1) with hNdef
  have hQ0 : 0 ≤ Q := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hN0 : 0 ≤ N := by positivity
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have hN : N ≤ 10 * Q ^ 2 := by
    have h1 : t + (k + m + 5) + 1 ≤ 9 * Q := by linarith
    have h2 : m * (t + (k + m + 5) + 1) ≤ Q * (9 * Q) := mul_le_mul hm h1 (by positivity) hQ0
    nlinarith
  have hr : k + m - 1 ≤ 2 * Q := by linarith
  have hnr0 : 0 ≤ k + m := by linarith
  have hnr : k + m ≤ 2 * Q := by linarith
  have i1 : (k + m - 1) * N * lb ≤ (2 * Q) * (10 * Q ^ 2) * Q := by
    have a : (k + m - 1) * (N * lb) ≤ (2 * Q) * (N * lb) := mul_le_mul_of_nonneg_right hr (by positivity)
    have b : N * lb ≤ (10 * Q ^ 2) * Q := mul_le_mul hN hlb hlb0 (by positivity)
    have c : (2 * Q) * (N * lb) ≤ (2 * Q) * ((10 * Q ^ 2) * Q) := mul_le_mul_of_nonneg_left b (by positivity)
    calc (k + m - 1) * N * lb = (k + m - 1) * (N * lb) := by ring
      _ ≤ _ := a.trans c
      _ = _ := by ring
  have i2 : C * f ^ 2 * (k + m) ^ 6 * Lb ≤ C * Q ^ 2 * (2 * Q) ^ 6 * (20 * Q) := by
    have a : C * f ^ 2 * (k + m) ^ 6 * Lb ≤ C * f ^ 2 * (k + m) ^ 6 * (20 * Q) :=
      mul_le_mul_of_nonneg_left hLb (by positivity)
    have b : C * f ^ 2 * (k + m) ^ 6 ≤ C * Q ^ 2 * (2 * Q) ^ 6 := by gcongr
    exact a.trans (mul_le_mul_of_nonneg_right b (by positivity))
  have hQ4 : Q ^ 4 ≤ Q ^ 9 := pow_le_pow_right₀ hQ (by norm_num)
  have hinner : (k + m - 1) * N * lb + C * f ^ 2 * (k + m) ^ 6 * Lb ≤ 1300 * C * Q ^ 9 := by
    have e1 : (2 * Q) * (10 * Q ^ 2) * Q = 20 * Q ^ 4 := by ring
    have e2 : C * Q ^ 2 * (2 * Q) ^ 6 * (20 * Q) = 1280 * C * Q ^ 9 := by ring
    have e3 : 20 * Q ^ 4 ≤ 20 * C * Q ^ 9 := by
      have : Q ^ 4 ≤ C * Q ^ 9 := hQ4.trans (le_mul_of_one_le_left (by positivity) hC)
      linarith
    linarith
  have hpre0 : 0 ≤ 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 := by positivity
  have hpre : 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 ≤ 100000 * C ^ 3 * Q * Q ^ 2 * (10 * Q ^ 2) ^ 2 := by gcongr
  calc 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 * ((k + m - 1) * N * lb + C * f ^ 2 * (k + m) ^ 6 * Lb)
      ≤ 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 * (1300 * C * Q ^ 9) := mul_le_mul_of_nonneg_left hinner hpre0
    _ ≤ 100000 * C ^ 3 * Q * Q ^ 2 * (10 * Q ^ 2) ^ 2 * (1300 * C * Q ^ 9) :=
        mul_le_mul_of_nonneg_right hpre (by positivity)
    _ = 13000000000 * C ^ 4 * Q ^ 16 := by ring

end GlobalTheory.BigTop.Fun.PolBound

namespace GlobalTheory.BigTop.Fun.PolBound

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem rpow_mono {x a b : ℝ} (hx : 1 ≤ x) (h : a ≤ b) : x ^ a ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx h

theorem factors_le {D : D7} (L : SizeData₂ D) (hS : SizesAt L) (T : ℕ) (hT : L.Ct + 1 ≤ T) :
    (D.R.f : ℝ) ≤ L.sc.x ^ (T + 9) ∧ (D.R.m : ℝ) ≤ L.sc.x ^ (T + 9) ∧ (D.R.k : ℝ) ≤ L.sc.x ^ (T + 9) ∧
      (D.R.t : ℝ) ≤ L.sc.x ^ (T + 9) ∧ Real.log L.sc.b ≤ L.sc.x ^ (T + 9) ∧ 0 ≤ Real.log L.sc.b ∧
      Real.log (L.sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|) ≤ 20 * L.sc.x ^ (T + 9) := by
  obtain ⟨hN, hM, hK, hKR, hTt, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, hPde, -⟩ := hS
  set x := L.sc.x with hxdef
  have hx1 : 1 ≤ x := L.sc.one_lt_alt.le
  have hx0 : 0 ≤ x := by linarith
  have he0 : 0 < L.sc.eps := L.sc.eps_pos
  have he1 : L.sc.eps < 1 / 52 := L.sc.eps_lt
  have hth : szTh L = L.sc.eps / 100 := rfl
  have hpow : ∀ j : ℕ, j ≤ T + 9 → x ^ j ≤ x ^ (T + 9) := fun j hj => pow_le_pow_right₀ hx1 hj
  have hrp : ∀ (a : ℝ) (j : ℕ), a ≤ j → x ^ a ≤ x ^ j := fun a j h => by
    rw [← Real.rpow_natCast]; exact rpow_mono hx1 h

  have hLd : L.sc.L = x ^ L.sc.eps := by rw [hxdef]; rfl
  have hlb : Real.log L.sc.b = x ^ L.sc.eps := by
    show Real.log (Real.exp L.sc.L) = _
    rw [Real.log_exp]; exact hLd
  have hLx : x ^ L.sc.eps ≤ x := by
    have := hrp L.sc.eps 1 (by norm_num; linarith); simpa using this

  have hm : (D.R.m : ℝ) ≤ x := by
    have hd1 : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0 _
    have h1 : Real.sqrt (x * L.sc.delta1) ≤ x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt (by nlinarith)
    have h2 : x ^ szTh L * Real.sqrt (x * L.sc.delta1) ≤ x ^ szTh L * x ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx0 _)
    rw [← Real.rpow_add (by linarith)] at h2
    have h3 : x ^ (szTh L + 1 / 2) ≤ x ^ (1 : ℕ) := hrp _ 1 (by rw [hth]; push_cast; linarith)
    linarith [hM.2, pow_one x]
  have hk : (D.R.k : ℝ) ≤ x ^ 5 := hK.2.trans (hrp _ 5 (by rw [hth]; push_cast; linarith))
  have hn : (D.R.n : ℝ) ≤ x ^ 3 := hN.2.trans (hrp _ 3 (by rw [hth]; push_cast; linarith))
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hf : (D.R.f : ℝ) ≤ x ^ 5 := by
    have h := hKR.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h2 : (D.R.m : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hm0 hm 2
    have h3 : (D.R.m : ℝ) ^ 2 * D.R.n ≤ x ^ 2 * x ^ 3 := mul_le_mul h2 hn (Nat.cast_nonneg _) (by positivity)
    calc (D.R.f : ℝ) ≤ _ := h
      _ ≤ _ := h3
      _ = x ^ 5 := by ring
  have ht : (D.R.t : ℝ) ≤ x ^ T := by
    refine hTt.2.trans (hrp _ T ?_)
    have : L.Ct + szTh L ≤ L.Ct + 1 := by rw [hth]; linarith
    linarith
  have hQ5 : x ^ 5 ≤ x ^ (T + 9) := hpow 5 (by omega)
  have hQ8 : x ^ 8 ≤ x ^ (T + 9) := hpow 8 (by omega)
  have hQ1 : x ≤ x ^ (T + 9) := by simpa using hpow 1 (by omega)
  refine ⟨hf.trans hQ5, hm.trans hQ1, hk.trans hQ5, ht.trans (hpow T (by omega)), by rw [hlb]; linarith,
    by rw [hlb]; positivity, ?_⟩

  have hb : Real.posLog L.sc.b ≤ x := posLog_le_of_log_le (by rw [hlb]; exact hLx) hx0
  have hnr : Real.posLog ((D.R.k + D.R.m : ℕ) : ℝ) ≤ 2 * x ^ 5 := by
    refine posLog_le_of_log_le ((Real.log_le_self (Nat.cast_nonneg _)).trans ?_) (by positivity)
    push_cast
    have : (D.R.m : ℝ) ≤ x ^ 5 := hm.trans (by simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 5))
    linarith
  have hg : ∀ i : Fin 2, Real.posLog (D.host.g i : ℝ) ≤ x := fun i => by
    refine posLog_le_of_log_le ((hG i i).2.2.trans ?_) hx0
    rw [hLd, ← Real.rpow_add (by linarith)]
    have := hrp (szTh L + L.sc.eps) 1 (by rw [hth]; push_cast; linarith)
    simpa using this
  have hp1 : Real.posLog (D.host.pde : ℝ) ≤ x := posLog_le_of_log_le (hPde.1.trans (hLd ▸ hLx)) hx0
  have hp2 : Real.posLog (D.host.pde' : ℝ) ≤ x := posLog_le_of_log_le (hPde.2.trans (hLd ▸ hLx)) hx0
  have hdE : Real.posLog |((discr D.host.E : ℤ) : ℝ)| ≤ 6 * x ^ 8 := by
    refine posLog_le_of_log_le ?_ (by positivity)
    have e := logdE_eq_rd D
    unfold logdE at e
    rw [e]
    have hlr : Real.log D.host.rdE ≤ 2 * x ^ 3 + x := by
      have h1 := UpperTheory.Ram.Rd.log_rdE_le D.host
      have h2 : Real.log (D.R.n : ℝ) ≤ x ^ 3 := (Real.log_le_self (Nat.cast_nonneg _)).trans hn
      have hq : Real.log D.host.q ≤ x := hQD.2.2.1.trans (by
        have := hrp (L.sc.eps / 5 + szTh L) 1 (by rw [hth]; push_cast; linarith); simpa using this)
      have hd : Real.log D.host.d ≤ x := hQD.2.2.2.2.1.trans (by
        have := hrp (L.sc.eps / 5 + szTh L) 1 (by rw [hth]; push_cast; linarith); simpa using this)
      linarith
    have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    calc 2 * (D.R.f : ℝ) * Real.log D.host.rdE ≤ 2 * (D.R.f : ℝ) * (2 * x ^ 3 + x) :=
          mul_le_mul_of_nonneg_left hlr (by positivity)
      _ ≤ 2 * x ^ 5 * (2 * x ^ 3 + x) := by gcongr
      _ ≤ 6 * x ^ 8 := by
          have : x ^ 6 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by norm_num)
          nlinarith
  have hprod : Real.log (L.sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|) ≤ Real.posLog L.sc.b + Real.posLog ((D.R.k + D.R.m : ℕ) : ℝ) +
      Real.posLog (D.host.g 0 : ℝ) + Real.posLog (D.host.g 1 : ℝ) + Real.posLog (D.host.pde : ℝ) +
      Real.posLog (D.host.pde' : ℝ) + Real.posLog |((discr D.host.E : ℤ) : ℝ)| := by
    refine (log_le_posLog' _).trans ?_
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    exact Real.posLog_mul
  have h8 : x ^ 5 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by norm_num)
  have h18 : x ≤ x ^ 8 := by simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 8)
  have := hg 0
  have := hg 1
  refine hprod.trans ?_
  linarith

end GlobalTheory.BigTop.Fun.PolBound

namespace GlobalTheory.BigTop.Fun

open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.BigTop.Fun.PolBound

end GlobalTheory.BigTop.Fun
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpTie

theorem not_dvd_discr_host (D : D7) {l : ℕ} (hl : l.Prime) (hS : l ∉ Formalism.MainNotions.JumpSetsAlt.excSet D) :
    ¬ ((l : ℕ) : ℤ) ∣ NumberField.discr D.host.E :=
  UpperTheory.ExcSet.not_dvd_discr D hl hS

end GlobalTheory.ExpTie
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.exists_sec_nonzero_on_finite_of_generated' : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∀ S : Set X, S.Finite → ∃ s : L.Sec, ∀ x ∈ S, x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_nonzero_on_finite_of_generated | exact GlobalTheory.exists_sec_nonzero_on_finite_of_generated | (intros; apply GlobalTheory.exists_sec_nonzero_on_finite_of_generated <;> assumption)
end
