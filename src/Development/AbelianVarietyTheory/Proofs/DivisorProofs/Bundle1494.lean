module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle001
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField), f ∈ P.H a b → ∀ i j, ContinuousOn (ratVal (q := p) (σ := σ) (P.loc a b f i j)) (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) ∧ ∀ (D : ℕ) (c : AlgChart p σ D), DifferentiableOn ℂ (fun v => ratVal (P.loc a b f i j) (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j))) := by
  first | exact @GlobalTheory.HSAmp.loc_continuousOn_holo | exact GlobalTheory.HSAmp.loc_continuousOn_holo | (intros; apply GlobalTheory.HSAmp.loc_continuousOn_holo <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_holomorphicTypeFamily_holomorphicType : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → (ι → Mt n) → ℂ) (C : ℝ), (∀ o, HolFn Hm q x₀ w (f o)) → (∀ o, ∀ u ∈ UG Hm, ‖f o u‖ ≤ C) → (∀ u ∈ UG Hm, AEStronglyMeasurable (fun o => f o u) ν) → HolFn Hm q x₀ w fun u => ∫ o, f o u ∂ν := by
  first | exact @GlobalTheory.HolDict.holFn_integral | exact GlobalTheory.HolDict.holFn_integral | (intros; apply GlobalTheory.HolDict.holFn_integral <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.multiplicityMap_complexRightDerivative_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (y : M.sm τ), (y : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z (v τ : M.H τ) → RderC θ V τ Z (T v) = T (Function.update v τ y) := by
  first | exact @GlobalTheory.MultDer.rderC_eq | exact GlobalTheory.MultDer.rderC_eq | (intros; apply GlobalTheory.MultDer.rderC_eq <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → (∃ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure ∧ IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ ∧ IsCompact (closure 𝓕)) ∧ (∀ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure → IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤) ∧ ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ z ∈ ZI V ξ, ∃ γ ∈ ZI V ξ, γ ∈ GQ V ∧ ∃ u ∈ ZI V ξ, u ∈ GinfC V ∧ ∃ k ∈ ZI V ξ, k ∈ GfC V ∧ k ∈ U ∧ z = γ * u * k := by
  first | exact @GlobalTheory.TransvMeasure.transvection_measure | exact GlobalTheory.TransvMeasure.transvection_measure | (intros; apply GlobalTheory.TransvMeasure.transvection_measure <;> assumption)
end

section

open Filter Topology GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.eventually_log_ncard_seminormBall_one_ge : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G) (B : ℕ → ℝ → Set G) (d : ℕ), 0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) → ∀ α β t₀ : ℝ, (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => Real.log ((B m (Real.exp (t * m))).ncard : ℝ) / (m : ℝ) ^ d) atTop (𝓝 (α + β * t))) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α - ε) * (m : ℝ) ^ d ≤ Real.log ((B m 1).ncard : ℝ) := by
  first | exact @GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge | exact GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge | (intros; apply GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge <;> assumption)
end

section

open Filter Topology GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.exists_log_ncard_seminormBall_exp_small_le : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G) (B : ℕ → ℝ → Set G) (d : ℕ), 0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) → ∀ C : ℝ, (∀ᶠ m : ℕ in atTop, Real.log ((B m (Real.exp (3 * m))).ncard : ℝ) ≤ C * (m : ℝ) ^ d) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop, Real.log ((B m (Real.exp (δ * m))).ncard : ℝ) ≤ Real.log ((B m 1).ncard : ℝ) + ε * (m : ℝ) ^ d := by
  first | exact @GlobalTheory.VolBr.log_ncard_ball_exp_le | exact GlobalTheory.VolBr.log_ncard_ball_exp_le | (intros; apply GlobalTheory.VolBr.log_ncard_ball_exp_le <;> assumption)
end

section

open Filter Topology
open GlobalTheory GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.log_ncard_unitBall_le_of_independent_level_bound : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → (B 1).Finite → ∀ (q : ℕ) (T : ℝ), 3 ≤ q → 0 ≤ T → (∀ (r : ℕ) (e : Fin r → G) (n : Fin r → ℕ), LinearIndependent ℤ e → (∀ j, e j ∈ B ((2 / q : ℝ) ^ n j)) → ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ T) → Real.log ((B 1).ncard : ℝ) ≤ Real.log q * T := by
  first | exact @GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound | exact GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound | (intros; apply GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ n : ℕ, f ^ n ∈ P.H (n * a) (n * b) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (n * a) (n * b) σ y (f ^ n) = P.nu a b σ y f ^ n := by
  first | exact @GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow | exact GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow | (intros; apply GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.smallSections_twistedPower_encard_eq_ball : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → ∀ (t : ℝ) (m : ℕ), ((M.shift (fun _ => t) fun _ => rfl).pow m).smallSec.encard = (P.Bl (m * a) (m * b) (Real.exp (t * m))).encard ∧ (M.pow m).smallSec.encard = (P.Bl (m * a) (m * b) 1).encard ∧ (M.shift (fun _ => t) fun _ => rfl).smallSec.encard = (P.Bl a b (Real.exp t)).encard := by
  first | exact @GlobalTheory.VolBr.SmallBall.main | exact GlobalTheory.VolBr.SmallBall.main | (intros; apply GlobalTheory.VolBr.SmallBall.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.exists_nhds_nu_le_exp_mul_of_far_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∀ (σ : k →+* ℂ) (y₀ : CxPts p σ), ∃ (W : Set (CxPts p σ)) (ρ : ℝ), W ∈ 𝓝 y₀ ∧ 0 < ρ ∧ ∀ (N : ℕ) (f : X.functionField) (R : ℝ), f ∈ P.H N 0 → (∀ (σ' : k →+* ℂ) (y : CxPts p σ'), ρ ≤ P.nu 0 1 σ' y s → P.nu N 0 σ' y f ≤ R) → ∀ y ∈ W, P.nu N 0 σ y f ≤ Real.exp (δ * N) * R := by
  first | exact @GlobalTheory.VolBr.Pair.max_principle_near | exact GlobalTheory.VolBr.Pair.max_principle_near | (intros; apply GlobalTheory.VolBr.Pair.max_principle_near <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem exists_coeff_le_of_linearIndependent : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (r : ℕ) (f : Fin r → X.functionField), (∀ j, f j ∈ P.H a b) → LinearIndependent ℤ f → ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Fin r → ℤ) (R : ℝ), (∑ j, c j • f j) ∈ P.Bl a b R → ∀ j, |(c j : ℝ)| ≤ C * R := by
  intro k _ X _ p D hX P a b r f hf hli
  classical
  have h1 : genericPoint X ∈ ⨆ i, P.L.B.U i := by rw [P.L.isLB.cover]; trivial
  have h2 : genericPoint X ∈ ⨆ j, P.A.B.U j := by rw [P.A.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h1
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
  obtain ⟨U, hU, hgU, hle⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X)
    (U := P.L.B.U i ⊓ P.A.B.U j) ⟨hi, hj⟩
  have hl : U ≤ P.L.B.U i := fun x hx => (hle hx).1
  have hr : U ≤ P.A.B.U j := fun x hx => (hle hx).2
  have : Nonempty U := ⟨⟨_, hgU⟩⟩
  have : CharZero Γ(X, U) :=
    ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero
  have := finiteType_int_of_isAffineOpen hX hU
  have hg : ∀ l, ∃ g, fnOf U hgU g = P.loc a b (f l) i j := fun l =>
    exists_fnOf_eq hgU fun x hx => hf l x i j (hl hx) (hr hx)
  choose g hg using hg
  set c0 : X.functionField := (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b with hc0def
  have hloc : ∀ h, P.loc a b h i j = h * c0 := fun h => by simp only [Pair.loc, c0, mul_assoc]
  have hc0 : c0 ≠ 0 := mul_ne_zero (zpow_ne_zero _ (P.r i).ne_zero) (zpow_ne_zero _ (P.r' j).ne_zero)
  have hlig : LinearIndependent ℤ g := by
    have h3 : LinearIndependent ℤ ((LinearMap.mulRight ℤ c0) ∘ f) :=
      hli.map' _ (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hc0))
    refine LinearIndependent.of_comp (fnOf U hgU).toAddMonoidHom.toIntLinearMap ?_
    have e : (⇑(fnOf U hgU).toAddMonoidHom.toIntLinearMap ∘ g) = ⇑(LinearMap.mulRight ℤ c0) ∘ f := by
      funext l
      simp [hg, hloc]
    rw [e]
    exact h3
  obtain ⟨x, hx⟩ := GlobalTheory.CxPointsSep.exists_det_ne_zero Γ(X, U) r g hlig
  obtain ⟨-, -, -, hsurj, -⟩ := GlobalTheory.ContRead.exists_continuous_read k X p D hX U hU (fun _ _ => 0)
    fun _ => continuousOn_const
  choose σ y hy hyx using hsurj
  let M : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun s l => x s (g l)
  let w : Fin r → ℝ := fun s => Real.exp ((a * (P.L.φ (σ (x s))).φ i (y (x s)) +
    b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2)
  let E : ℝ := ∑ s, w s
  let K : ℝ := ∑ l, ∑ s, ‖M⁻¹ l s‖
  have hE : 0 ≤ E := Finset.sum_nonneg fun s _ => (Real.exp_pos _).le
  have hK : 0 ≤ K := Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun s _ => norm_nonneg _
  refine ⟨K * E, mul_nonneg hK hE, fun cc R hR l => ?_⟩
  set v : Fin r → ℂ := Matrix.mulVec M fun l => (cc l : ℂ) with hvdef
  have hsum : P.loc a b (∑ l, cc l • f l) i j = fnOf U hgU (∑ l, cc l • g l) := by

    rw [hloc, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, hg, hloc, smul_mul_assoc]
  have key : ∀ s, ‖v s‖ ≤ R * w s := by
    intro s
    have e := GlobalTheory.VolBr.nu_eq k X p P a b _ hR.1 (σ (x s)) (y (x s)) i j
      (ptsIn_mono hl (hy (x s))) (ptsIn_mono hr (hy (x s)))
    rw [hsum, ratVal_fnOf (hy (x s)), ev_eq (hy (x s)), hyx] at e
    have hv : v s = x s (∑ l, cc l • g l) := by

      simp [v, M, Matrix.mulVec, dotProduct, map_sum, map_zsmul, mul_comm]
    have hb := hR.2 (σ (x s)) (y (x s))
    rw [e] at hb
    rw [hv]
    have hw : ‖x s (∑ l, cc l • g l)‖ = ‖x s (∑ l, cc l • g l)‖ *
        Real.exp (-(a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2) * w s := by
      rw [mul_assoc, ← Real.exp_add]
      have : -(a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2 +
          (a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2 = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    rw [hw]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hR0 : 0 ≤ R := by
    by_contra h
    push_neg at h
    have := mul_neg_of_neg_of_pos h (Real.exp_pos _ : (0 : ℝ) < w l)
    linarith [key l, norm_nonneg (v l)]
  have hinv : (fun l => (cc l : ℂ)) = Matrix.mulVec M⁻¹ v := by
    rw [hvdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hx), Matrix.one_mulVec]
  have habs : |(cc l : ℝ)| = ‖(cc l : ℂ)‖ := by simp
  rw [habs, congrFun hinv l]
  calc ‖Matrix.mulVec M⁻¹ v l‖ = ‖∑ s, M⁻¹ l s * v s‖ := rfl
    _ ≤ ∑ s, ‖M⁻¹ l s‖ * ‖v s‖ := (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
    _ ≤ ∑ s, ‖M⁻¹ l s‖ * (R * E) := Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left ((key s).trans (mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := w) (fun t _ => (Real.exp_pos _).le) (Finset.mem_univ s)) hR0)) (norm_nonneg _)
    _ = (∑ s, ‖M⁻¹ l s‖) * E * R := by rw [← Finset.sum_mul]; ring
    _ ≤ K * E * R := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hE) hR0
        exact Finset.single_le_sum (f := fun l => ∑ s, ‖M⁻¹ l s‖)
          (fun t _ => Finset.sum_nonneg fun s _ => norm_nonneg _) (Finset.mem_univ l)

end GlobalTheory.HSNef
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict


open Formalism.L2.NTheta in
theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) {n : ℕ} (hn : n = R.r) :
    StrictAnti fun a : Fin n => lamAt h a := by
  intro a b hab
  have h1 : (a : ℕ) < b := hab
  have h2 := b.2
  have h3 := lamAt_add_add_le h (b - a) a (by omega)
  rw [show (a : ℕ) + (b - a) = b by omega] at h3
  have h4 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith


open Formalism.L2.NTheta in
theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := by rw [hpq, hn]; exact odd_r R
  ext x
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a | a, rfl⟩
    · exact ⟨⟨a, by have := a.2; omega⟩, by simp⟩
    · exact ⟨⟨p + a, by have := a.2; omega⟩, by simp⟩
  · rintro ⟨a, rfl⟩
    by_cases ha : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, ha⟩, by simp [ha]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_⟩
      simp [ha, show p + ((a : ℕ) - p) = a by omega]


open Formalism.L2.NTheta in
theorem isEnum_holPar_kapW {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n)
    {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q (kapW h p q)) lam ε) (a : Fin n) :
    lam a = (lamAt h a : ℝ) ∧ ε a = decide ((a : ℕ) < p) := by
  obtain ⟨hs, f, hf, hS⟩ := he
  rw [holPar_kapW_eq h hn hpq] at hS
  have hg := lamAt_strictAnti h hn
  have hfs : StrictAnti f := fun a b hab => by
    have := hs hab
    rw [hf, hf] at this
    exact_mod_cast this
  have m1 : ∀ a, ∃ b : Fin n, (lamAt h b, decide ((b : ℕ) < p)) = (f a, ε a) := fun a => by
    have : (f a, ε a) ∈ Finset.univ.image fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p)) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, hb⟩
  have m2 : ∀ a : Fin n, ∃ b, (f b, ε b) = (lamAt h a, decide ((a : ℕ) < p)) := fun a => by
    have : (lamAt h a, decide ((a : ℕ) < p)) ∈ Finset.univ.image fun a : Fin n => (f a, ε a) := by
      rw [← hS]; exact Finset.mem_image_of_mem (fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p))) (Finset.mem_univ a)
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, hb⟩
  have e : f = fun a : Fin n => lamAt h a := by
    refine (StrictMono.range_inj hfs.dual_right hg.dual_right).1 ?_ |> fun e => funext fun a => congrFun e a
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := m1 a
      exact ⟨b, congrArg Prod.fst hb⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := m2 a
      exact ⟨b, congrArg Prod.fst hb⟩
  subst e
  refine ⟨hf a, ?_⟩
  obtain ⟨b, hb⟩ := m1 a
  obtain rfl : b = a := hg.injective (congrArg Prod.fst hb)
  exact (congrArg Prod.snd hb).symm

theorem holShape_of_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → HolShape (R.MW i σ) ∧ (∀ ρ, nNeg ((R.MW i σ).ε ρ) = (D.R.sigW ((i : ℕ) + 1)).2) ∧ ∃ w, WtIs (R.MW i σ) w := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ ht i σ hσ
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    rw [rank_Wc i]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have key : ∀ ρ a, (R.MW i σ).lam ρ a = (Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) a : ℝ) ∧
      (R.MW i σ).ε ρ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun ρ a => by
    have he := (R.MW i σ).enum ρ
    unfold Links.parAt at he
    rw [if_pos ((GlobalTheory.ConjReading.branch_of_pins T ht.alg ht.laws.pins σ ρ).1 hσ)] at he
    rw [← hs ρ]
    exact isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs ρ]; exact hr) he a
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i σ).lam ρ) := fun ρ => by
    refine ⟨((R.MW i σ).enum ρ).1, fun a => ?_⟩
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) a
    obtain ⟨s, hs'⟩ := Formalism.L2.NTheta.odd_r D.R
    refine ⟨z - s, ?_⟩
    have hn : (((Wc D i).rank : ℕ) : ℝ) = 2 * s + 1 := by rw [rank_Wc i, hs']; push_cast; rfl
    rw [(key ρ a).1, hz, hn]
    push_cast
    ring
  refine ⟨fun ρ => ⟨hc ρ, _, by omega, fun a => (key ρ a).2⟩, fun ρ => ?_, ?_⟩
  · rw [nNeg_shape (by omega) fun a => (key ρ a).2]
    omega
  · choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ ((R.MW i σ).ε ρ) _ (hc ρ).2 a
    exact ⟨fun ρ c => w ρ (revNeg ((R.MW i σ).ε ρ) (arr (nNeg ((R.MW i σ).ε ρ)) c)), fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.HolDict
end
