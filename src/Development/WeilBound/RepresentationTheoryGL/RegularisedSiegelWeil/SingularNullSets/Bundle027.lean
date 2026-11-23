module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle026
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCoefficientOfConvergence
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle765
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle006
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LThCoef

open GlobalTheory.CompanionTheory.SiegelND (pairH)
open GlobalTheory.CompanionTheory.ThetaCoefND (gramOf continuous_pairH pairH_ne_zero setIntegral_pairH)
open GlobalTheory.CompanionTheory.HermPoisson (ofHermE)

variable {D : D7}

theorem thS_eq (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {W : HSp D} {n : ℕ} {m : Measure (GA D W)}
    {𝓕 : Set (GA D W)} {Ψ : Mx D W.rank n → ℂ} (hvol : m 𝓕 < ⊤) (hΨ : Continuous Ψ) {C : ℝ≥0}
    (hC : ∀ h : GA D W, ∑' x : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat x.1))‖ₑ ≤ C) (x : hermA D n) :
    thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X) =
      ∑' y : Sp W n, pairH ψ (ofHermE (gramOf W y.1)).1 x * co W m 𝓕 Ψ y.1 := by
  obtain ⟨-, hψn, -, -⟩ := hψ
  have hnorm : ∀ y : Sp W n, ‖pairH ψ (ofHermE (gramOf W y.1)).1 x‖ = 1 := fun y => hψn _
  have key : ∀ (h : GA D W) (y : Sp W n),
      pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat y.1)) (mm (mt W h⁻¹) (rat y.1))) * Ψ (mm (mt W h⁻¹) (rat y.1)) =
        pairH ψ (ofHermE (gramOf W y.1)).1 x * Ψ (mm (mt W h⁻¹) (rat y.1)) := by
    intro h y
    rw [ip_inv]
    exact congrArg (· * Ψ (mm (mt W h⁻¹) (rat y.1))) (pch_rat ψ x (gramOf W y.1))
  calc thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X)
      = ∫ h in 𝓕, ∑' y : Sp W n, pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat y.1)) (mm (mt W h⁻¹) (rat y.1))) *
          Ψ (mm (mt W h⁻¹) (rat y.1)) ∂m := rfl
    _ = ∫ h in 𝓕, ∑' y : Sp W n, pairH ψ (ofHermE (gramOf W y.1)).1 x * Ψ (mm (mt W h⁻¹) (rat y.1)) ∂m := by
        congr 1
        funext h
        congr 1
        funext y
        exact key h y
    _ = _ := exch hvol hΨ hC (fun y : Sp W n => pairH ψ (ofHermE (gramOf W y.1)).1 x) hnorm

theorem _root_.PositivityTheory.Rg.Rsw.L.thCoef : LatBound → ThCoef := by
  classical
  intro hLB D n W ψ hψ θ hθ m 𝓕 hm h𝓕 lam 𝓖 hl Ψ hΨ
  obtain ⟨C, hC⟩ := hLB D θ hθ W n Ψ hΨ
  have hvol : m 𝓕 < ⊤ := GlobalTheory.Cmp.RallisRange.vol_lt_top W hm h𝓕
  have hΨc : Continuous Ψ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Ψ hΨ).1
  have hth := fun x => thS_eq ψ hψ hvol hΨc hC x
  have hsum := summable_co hvol hΨc hC
  have hpn : ∀ (S x : hermA D n), ‖pairH ψ S x‖ = 1 := fun S x => hψ.2.1 _
  refine ⟨hvol.ne, ?_, fun β => ?_⟩
  · refine (continuous_tsum (f := fun (y : Sp W n) (x : hermA D n) => pairH ψ (ofHermE (gramOf W y.1)).1 x * co W m 𝓕 Ψ y.1)
      (fun y => (continuous_pairH hψ _).mul continuous_const) hsum
      (fun y x => by rw [norm_mul, hpn, one_mul])).congr fun x => (hth x).symm
  obtain ⟨i1, -, i3, -, -, -⟩ := lattice_Mx D n n
  have : IsTopologicalAddGroup (Mx D n n) := i1
  have : SecondCountableTopology (Mx D n n) := i3
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have hcoef : ∫ x in 𝓖, thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X) * conj (pch ψ x.1 (rat β.1)) ∂lam =
      ∑' y : Sp W n, if gramOf W y.1 = β then co W m 𝓕 Ψ y.1 else 0 := by
    have e1 : ∀ x : hermA D n, thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X) * conj (pch ψ x.1 (rat β.1)) =
        ∑' y : Sp W n, co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x * (pairH ψ (ofHermE β).1 x)⁻¹) :=
      fun x => by
        rw [hth x, pch_rat ψ x β, conj_eq_inv (hpn _ _), ← tsum_mul_right]
        exact tsum_congr fun y => by ring
    rw [integral_congr_ae (ae_of_all _ e1), integral_tsum]
    · refine tsum_congr fun y => ?_
      rw [integral_const_mul]
      split_ifs with h
      · rw [h]
        have e3 : ∀ x, pairH ψ (ofHermE β).1 x * (pairH ψ (ofHermE β).1 x)⁻¹ = 1 := fun x =>
          mul_inv_cancel₀ (pairH_ne_zero hψ _ _)
        simp only [e3, integral_const, measureReal_def, Measure.restrict_apply_univ, hl.2.2]
        simp
      · rw [setIntegral_pairH hψ hl h, mul_zero]
    · intro y
      exact (continuous_const.mul ((continuous_pairH hψ _).mul
        ((continuous_pairH hψ _).inv₀ (pairH_ne_zero hψ _)))).aestronglyMeasurable
    · have e2 : ∀ y : Sp W n, ∫⁻ x in 𝓖, ‖co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x *
          (pairH ψ (ofHermE β).1 x)⁻¹)‖ₑ ∂lam = ‖co W m 𝓕 Ψ y.1‖ₑ := fun y => by
        have e4 : ∀ x, ‖co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x *
            (pairH ψ (ofHermE β).1 x)⁻¹)‖ₑ = ‖co W m 𝓕 Ψ y.1‖ₑ := fun x => by
          have h5 : ‖co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x *
              (pairH ψ (ofHermE β).1 x)⁻¹)‖ = ‖co W m 𝓕 Ψ y.1‖ := by
            rw [norm_mul, norm_mul, norm_inv, hpn, hpn]
            simp
          exact (ofReal_norm _).symm.trans ((congrArg ENNReal.ofReal h5).trans (ofReal_norm _))
        simp only [e4, setLIntegral_const, hl.2.2, mul_one]
      simp only [e2]
      exact tsum_co_ne_top hvol hΨc hC
  refine ⟨fun hno => ?_, fun x₀ hr hg => ?_⟩
  · rw [hcoef]
    exact (tsum_congr fun y => if_neg fun h => hno ⟨y.1, y.2, congrArg Subtype.val h⟩).trans tsum_zero
  rw [hcoef]
  obtain ⟨-, -, -, hB, hTG, -, hcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : MeasurableConstSMul (GQ W) (GA D W) := ⟨fun γ => measurable_const_mul (γ : GA D W)⟩
  have : SMulInvariantMeasure (GQ W) (GA D W) m := ⟨fun γ s _ => measure_preimage_mul m (γ : GA D W) s⟩
  obtain ⟨e, he⟩ := orbit_equiv W x₀ hr
  let T := {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank ∧ gramQ W y = gramQ W x₀}
  let s : Set (Sp W n) := {y | gramOf W y.1 = β}
  let q : s ≃ T :=
    { toFun := fun y => ⟨y.1.1, y.1.2, (congrArg Subtype.val y.2 : gramQ W y.1.1 = β.1).trans hg.symm⟩
      invFun := fun t => ⟨⟨t.1, t.2.1⟩, Subtype.ext (t.2.2.trans hg)⟩
      left_inv := fun y => rfl
      right_inv := fun t => rfl }
  have hpt : ∀ (γ : GQ W) (h : GA D W), Ψ (mm (mt W h⁻¹) (rat (e γ).1)) = Ψ (mm (mt W (γ⁻¹ • h)⁻¹) (rat x₀)) :=
    fun γ h => by
      rw [he]
      show Ψ (mm (mt W h⁻¹) (mm (mt W γ) (rat x₀))) = Ψ (mm (mt W (((γ : GA D W))⁻¹ * h)⁻¹) (rat x₀))
      rw [mul_inv_rev, inv_inv, mt_mul]
      exact congrArg Ψ (Matrix.mul_assoc _ _ _).symm
  have hint : Integrable (fun h : GA D W => Ψ (mm (mt W h⁻¹) (rat x₀))) m := by
    refine ⟨(cont_term hΨc x₀).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, h𝓕.lintegral_eq_tsum']
    let g : T → ℝ≥0∞ := fun t => ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat t.1))‖ₑ ∂m
    have hinj : Function.Injective fun t : T => (⟨t.1, t.2.1⟩ : Sp W n) := fun t t' h =>
      Subtype.ext (by simpa using congrArg Subtype.val h)
    calc ∑' γ : GQ W, ∫⁻ h in 𝓕, ‖Ψ (mm (mt W (γ⁻¹ • h)⁻¹) (rat x₀))‖ₑ ∂m = ∑' γ, g (e γ) :=
          tsum_congr fun γ => by simp only [g, hpt]
      _ = ∑' t, g t := e.tsum_eq g
      _ ≤ ∑' y : Sp W n, ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun y : Sp W n => ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m)
      _ < ⊤ := lint_fin hvol hΨc hC
  calc (∑' y : Sp W n, if gramOf W y.1 = β then co W m 𝓕 Ψ y.1 else 0)
      = ∑' y : Sp W n, s.indicator (fun y => co W m 𝓕 Ψ y.1) y := tsum_congr fun y => by
        simp only [Set.indicator_apply, s, Set.mem_ofPred_eq]
    _ = ∑' y : s, co W m 𝓕 Ψ y.1.1 := (tsum_subtype s _).symm
    _ = ∑' t : T, co W m 𝓕 Ψ t.1 := q.tsum_eq (fun t => co W m 𝓕 Ψ t.1)
    _ = ∑' γ : GQ W, co W m 𝓕 Ψ (e γ).1 := (e.tsum_eq (fun t => co W m 𝓕 Ψ t.1)).symm
    _ = ∑' γ : GQ W, ∫ h in 𝓕, Ψ (mm (mt W (γ⁻¹ • h)⁻¹) (rat x₀)) ∂m :=
        tsum_congr fun γ => integral_congr_ae (ae_of_all _ fun h => hpt γ h)
    _ = orb W m Ψ x₀ := (h𝓕.integral_eq_tsum' _ hint).symm

end PositivityTheory.Rg.Rsw.L.LThCoef

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCfRel

open Set Metric

variable {D : D7} {n : ℕ}

theorem cut_cont {H : G D n → ℝ≥0} {φ : G D n → ℂ} {s₀ : ℂ} {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ} {σ : ℝ}
    (hE : IsCont H φ s₀ U d E σ) (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) :
    ContinuousOn (fun p : ℂ × KAt D n v => cutR nb C (E p.1) (g * p.2)) (U ×ˢ univ) := by
  have hterm : ∀ x : hermA D n, ContinuousOn (fun p : ℂ × KAt D n v => E p.1 (g * ↑p.2 * nb x))
      (U ×ˢ univ) := by
    intro x
    have hc : Continuous (fun p : ℂ × KAt D n v => (p.1, g * ↑p.2 * nb x)) :=
      continuous_fst.prodMk ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul
        continuous_const)
    exact hE.cont.comp hc.continuousOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
  show ContinuousOn (fun p : ℂ × KAt D n v => ∑ x ∈ C.s, C.co x * E p.1 (g * ↑p.2 * nb x)) (U ×ˢ univ)
  exact continuousOn_finsetSum _ (fun x _ => continuousOn_const.mul (hterm x))

theorem cut_bound {H : G D n → ℝ≥0} {φ : G D n → ℂ} {s₀ : ℂ} {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ}
    {σ : ℝ} (hE : IsCont H φ s₀ U d E σ) (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) {S : Set ℂ}
    (hSU : S ⊆ U) (hS : IsCompact S) : ∃ M, ∀ z ∈ S, ∀ u : KAt D n v, ‖cutR nb C (E z) (g * u)‖ ≤ M := by
  obtain ⟨B, hB⟩ := (hS.prod (isCompact_cset nb C g)).exists_bound_of_continuousOn
    (hE.cont.mono (Set.prod_mono hSU (Set.subset_univ _)))
  refine ⟨∑ x ∈ C.s, ‖C.co x‖ * B, fun z hz u => ?_⟩
  show ‖∑ x ∈ C.s, C.co x * E z (g * ↑u * nb x)‖ ≤ _
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [norm_mul]
  have hmem : (z, g * ↑u * nb x) ∈ S ×ˢ cset nb C g := Set.mk_mem_prod hz (mem_cset nb C g u hx)
  have hb : ‖E z (g * ↑u * nb x)‖ ≤ B := hB _ hmem
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

theorem onU {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (hH : IsHt H) {s₀ : ℂ} {φ : G D n → ℂ}
    (hφc : Continuous φ) (hφl : IsLaw χ s₀ φ) {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ} {σ : ℝ}
    (hE : IsCont H φ s₀ U d E σ) (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (c : ℂ → ℂ)
    (hc : Differentiable ℂ c) (νv : Measure (KAt D n v)) [IsFiniteMeasure νv]
    (hrel : ∀ z g, ∫ k, cutR nb C (fam H φ s₀ z) (g * k) ∂νv = c z * fam H φ s₀ z g) (g : G D n) :
    ∀ z ∈ U, ∫ u, cutR nb C (E z) (g * u) ∂νv = c z * E z g := by
  have hh : DifferentiableOn ℂ (fun z => ∫ u, cutR nb C (E z) (g * u) ∂νv) U :=
    diffOn_integral νv (fun z (u : KAt D n v) => cutR nb C (E z) (g * u)) hE.isOpen (cut_cont hE nb C g)
      (fun u => by simp only [cutR]; exact DifferentiableOn.fun_sum fun x _ => (hE.hol _).const_mul _)
      (fun S hSU hS => cut_bound hE nb C g hSU hS)
  have hg : DifferentiableOn ℂ (fun z => c z * E z g) U := hc.differentiableOn.mul (hE.hol g)
  refine eqOn_right hE.isOpen hE.right.1 hE.right.isPreconnected hh hg (max σ ((n : ℝ) / 2)) fun z hz => ?_
  have h1 : σ < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have h2 : (n : ℝ) / 2 < z.re := lt_of_le_of_lt (le_max_right _ _) hz
  have e : ∀ u : KAt D n v, cutR nb C (E z) (g * u) = d.eval z * cutR nb C (eisS (fam H φ s₀ z)) (g * u) := by
    intro u
    simp only [cutR, hE.eq z h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [e]
  rw [integral_const_mul, farRight hH hφc hφl nb C c νv hrel h2 g, hE.eq z h1 g]
  ring

end LCfRel

open LCfRel Set Metric in
theorem cfRel : HtExist → CfRel := by
  intro _ D n χ _ H hH s₀ φ hφc hφl U d E σ hE ε hrad nb _ v C c hc νv hν hrel k hk hvan g
  haveI : IsProbabilityMeasure νv := hν
  obtain ⟨hε, hball, hne⟩ := hrad
  have hsph : Metric.sphere s₀ ε ⊆ U := fun z hz => hball (Metric.sphere_subset_closedBall hz)
  have hdne : ∀ z ∈ Metric.sphere s₀ ε, Polynomial.eval z d ≠ 0 := by
    intro z hz
    refine hne z (Metric.sphere_subset_closedBall hz) ?_
    rintro rfl
    rw [Metric.mem_sphere, dist_self] at hz
    linarith
  have hEc : ∀ y, ContinuousOn (fun z => E z y) (Metric.sphere s₀ ε) :=
    fun y => ((hE.hol y).continuousOn).mono hsph
  have hdc : ContinuousOn (fun z => Polynomial.eval z d) (Metric.sphere s₀ ε) :=
    (Polynomial.continuous d).continuousOn
  have hpc : ContinuousOn (fun z : ℂ => (z - s₀) ^ (k - 1)) (Metric.sphere s₀ ε) :=
    ((continuous_id.sub continuous_const).pow _).continuousOn
  have hstep1 : ∀ u : KAt D n v, cutR nb C (cf d E s₀ ε k) (g * ↑u) =
      (2 * ↑Real.pi * Complex.I)⁻¹ * ∮ z in C(s₀, ε),
        (z - s₀) ^ (k - 1) * (cutR nb C (E z) (g * ↑u) / Polynomial.eval z d) := by
    intro u
    have hcs := circle_sum C.s C.co
      (fun x z => (z - s₀) ^ (k - 1) * (E z (g * ↑u * nb x) / Polynomial.eval z d)) s₀ hε.le
      (fun x _ => hpc.mul ((hEc _).div hdc hdne))
    beta_reduce at hcs
    have hsum : (∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (cutR nb C (E z) (g * ↑u) / Polynomial.eval z d)) =
        ∑ x ∈ C.s, C.co x * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (E z (g * ↑u * nb x) / Polynomial.eval z d) := by
      rw [← hcs]
      refine circleIntegral.integral_congr hε.le (fun z _ => ?_)
      show (z - s₀) ^ (k - 1) * ((∑ x ∈ C.s, C.co x * E z (g * ↑u * nb x)) / Polynomial.eval z d) = _
      rw [Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hsum, Finset.mul_sum]
    show ∑ x ∈ C.s, C.co x * cf d E s₀ ε k (g * ↑u * nb x) = _
    refine Finset.sum_congr rfl (fun x _ => ?_)
    show C.co x * ((2 * ↑Real.pi * Complex.I)⁻¹ * ∮ z in C(s₀, ε),
      (z - s₀) ^ (k - 1) * (E z (g * ↑u * nb x) / Polynomial.eval z d)) = _
    ring
  have hcont2 : ContinuousOn (fun p : ℂ × KAt D n v =>
      (p.1 - s₀) ^ (k - 1) * (cutR nb C (E p.1) (g * ↑p.2) / Polynomial.eval p.1 d))
      (Metric.sphere s₀ ε ×ˢ univ) := by
    have h1 : ContinuousOn (fun p : ℂ × KAt D n v => cutR nb C (E p.1) (g * ↑p.2))
        (Metric.sphere s₀ ε ×ˢ univ) :=
      (cut_cont hE nb C g).mono (Set.prod_mono hsph subset_rfl)
    exact (hpc.comp continuousOn_fst (fun (p : ℂ × KAt D n v) (hp : p ∈ Metric.sphere s₀ ε ×ˢ univ) => hp.1)).mul
      (h1.div (hdc.comp continuousOn_fst (fun (p : ℂ × KAt D n v) (hp : p ∈ Metric.sphere s₀ ε ×ˢ univ) => hp.1)) (fun p hp => hdne p.1 hp.1))
  have hbound : ∃ M, ∀ z ∈ Metric.sphere s₀ ε, ∀ u : KAt D n v,
      ‖(z - s₀) ^ (k - 1) * (cutR nb C (E z) (g * ↑u) / Polynomial.eval z d)‖ ≤ M := by
    obtain ⟨M1, hM1⟩ := cut_bound hE nb C g hsph (isCompact_sphere s₀ ε)
    obtain ⟨A, hA⟩ := (isCompact_sphere s₀ ε).exists_bound_of_continuousOn hpc
    obtain ⟨B, hB⟩ := (isCompact_sphere s₀ ε).exists_bound_of_continuousOn (hdc.inv₀ hdne)
    refine ⟨A * (M1 * B), fun z hz u => ?_⟩
    rw [norm_mul, div_eq_mul_inv, norm_mul]
    have hA' : ‖(z - s₀) ^ (k - 1)‖ ≤ A := hA z hz
    have hM' : ‖cutR nb C (E z) (g * ↑u)‖ ≤ M1 := hM1 z hz u
    have hB' : ‖(Polynomial.eval z d)⁻¹‖ ≤ B := hB z hz
    exact mul_le_mul hA' (mul_le_mul hM' hB' (norm_nonneg _) ((norm_nonneg _).trans hM'))
      (by positivity) ((norm_nonneg _).trans hA')
  obtain ⟨M, hM⟩ := hbound
  have hswap := circle_swap νv
    (fun z (u : KAt D n v) => (z - s₀) ^ (k - 1) * (cutR nb C (E z) (g * ↑u) / Polynomial.eval z d))
    s₀ hε.le hcont2 hM
  beta_reduce at hswap
  have hinner : ∀ z ∈ Metric.sphere s₀ ε,
      ∫ u, (z - s₀) ^ (k - 1) * (cutR nb C (E z) (g * ↑u) / Polynomial.eval z d) ∂νv =
        (z - s₀) ^ (k - 1) * (c z * (E z g / Polynomial.eval z d)) := by
    intro z hz
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_div,
      onU hH hφc hφl hE nb C c hc νv hrel g z (hsph hz)]
    ring
  have hvan' : ∀ j : ℕ, k < j →
      ∮ z in C(s₀, ε), (z - s₀) ^ (j - 1) * (E z g / Polynomial.eval z d) = 0 := by
    intro j hj
    have h0' : (2 * ↑Real.pi * Complex.I)⁻¹ *
        ∮ z in C(s₀, ε), (z - s₀) ^ (j - 1) * (E z g / Polynomial.eval z d) = 0 :=
      congrFun (hvan j hj) g
    rcases mul_eq_zero.1 h0' with h | h
    · exact absurd h (inv_ne_zero Complex.two_pi_I_ne_zero)
    · exact h
  have hce := circle_entire_mul c hc (fun z => E z g / Polynomial.eval z d) s₀ hε
    ((hEc g).div hdc hdne) k hk hvan'
  beta_reduce at hce
  show ∫ u, cutR nb C (cf d E s₀ ε k) (g * ↑u) ∂νv = c s₀ * cf d E s₀ ε k g
  simp_rw [hstep1]
  rw [MeasureTheory.integral_const_mul, ← hswap, circleIntegral.integral_congr hε.le hinner, hce]
  show _ = c s₀ * ((2 * ↑Real.pi * Complex.I)⁻¹ *
    ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (E z g / Polynomial.eval z d))
  ring

end PositivityTheory.Rg.Rsw.L

end
end
