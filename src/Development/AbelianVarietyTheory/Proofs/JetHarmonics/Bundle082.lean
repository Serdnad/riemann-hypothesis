module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermEqGaugedFormalGroupLawExpIntegral
import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle053
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle009
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle020
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001

@[expose] public section

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.CharGerm

open MvPowerSeries GlobalTheory.RowLaw.GermRing GlobalTheory.FormalInv

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {Y : RawChart C d I κ} {V : VF C}

theorem const_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (F : MvPowerSeries σ C) : constantCoeff (subst a F) = constantCoeff F := by
  have hs := hasSubst_of_constantCoeff_zero ha
  have e : F = (F - MvPowerSeries.C (constantCoeff F)) + MvPowerSeries.C (constantCoeff F) := by ring
  rw [e, subst_add hs, map_add (f := _), constantCoeff_subst_zero ha (by simp), subst_C]
  simp

theorem coeff_single_subst_lg (hY : RLaw Y V) (F : MvPowerSeries κ C) (i : κ) :
    coeff (Finsupp.single i 1) (subst Y.lg F) = coeff (Finsupp.single i 1) F := by
  have hs := hasSubst_of_constantCoeff_zero (lg_const hY)
  have h := subst_sub_subst_mem_degGe (a := Y.lg) (b := (X : κ → MvPowerSeries κ C)) (k := 1) (m := 1)
    (fun s => mem_degGe_one.2 (lg_const hY s)) (fun s => mem_degGe_one.2 (constantCoeff_X s))
    (fun s => mem_degGe.2 fun μ hμ => by rw [map_sub, hY.lin s μ (by omega), sub_self])
    (f := F - MvPowerSeries.C (constantCoeff F)) (mem_degGe_one.2 (by simp))
  have h2 := mem_degGe.1 h (Finsupp.single i 1) (by simp)
  have e : F = (F - MvPowerSeries.C (constantCoeff F)) + MvPowerSeries.C (constantCoeff F) := by ring
  rw [map_sub, sub_eq_zero, congrFun subst_self] at h2
  conv_lhs => rw [e, subst_add hs, map_add (f := _), h2, subst_C]
  rw [← map_add (f := _)]
  exact congrArg _ e.symm

theorem subst_ex_eq_mvExp (hY : RLaw Y V) (χ : MvPowerSeries κ C) (h0 : constantCoeff χ = 1)
    (hχ : subst (addP Y (gp C κ (0 : Fin 2)) (gp C κ 1)) χ =
      subst (gp C κ (0 : Fin 2)) χ * subst (gp C κ (1 : Fin 2)) χ) :
    subst Y.ex χ = mvExp (∑ i : κ, coeff (Finsupp.single i 1) χ • (X i : MvPowerSeries κ C)) := by
  haveI := hY.charZero
  have hex := hasSubst_of_constantCoeff_zero hY.exc
  have hlg := hasSubst_of_constantCoeff_zero (lg_const hY)
  have hlin : ∀ i, coeff (Finsupp.single i 1) χ = coeff (Finsupp.single i 1) (subst Y.ex χ) := by
    intro i
    rw [← coeff_single_subst_lg hY (subst Y.ex χ), subst_comp_subst_apply hex hlg]
    simp only [hY.exlg]
    exact congrArg _ (congrFun subst_self χ).symm
  simp only [hlin]
  refine GlobalTheory.AddChar.eq_mvExp_of_additive C κ _ (by rw [const_subst hY.exc, h0]) ?_
  have hg : ∀ (j : Fin 2) x, constantCoeff (gp C κ j x) = 0 := fun j x => constantCoeff_X _
  have hgs : ∀ j : Fin 2, HasSubst (gp C κ j) := fun j => hasSubst_of_constantCoeff_zero (hg j)
  let e : Fin 2 × κ → MvPowerSeries (Fin 2 × κ) C := fun p => subst (gp C κ p.1) (Y.ex p.2)
  have he0 : ∀ p, constantCoeff (e p) = 0 := fun p => constantCoeff_subst_zero (hg _) (hY.exc _)
  have hes := hasSubst_of_constantCoeff_zero he0
  have hadd : ∀ i, constantCoeff (addP Y (gp C κ (0 : Fin 2)) (gp C κ 1) i) = 0 := fun i =>
    constantCoeff_subst_zero (log_add_const hY (hg 0) (hg 1)) (hY.exc i)
  have hA : HasSubst (fun i : κ => (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have k1 : ∀ (j : Fin 2) (F : MvPowerSeries κ C),
      subst e (subst (gp C κ j) F) = subst (fun x => subst (gp C κ j) (Y.ex x)) F := by
    intro j F
    rw [subst_comp_subst_apply (hgs j) hes]
    congr 1
    funext x
    rw [gp, subst_X hes]
  have h1 := congrArg (subst e) hχ
  rw [subst_mul hes, k1, k1, ← subst_comp_subst_apply hex (hgs 0), ← subst_comp_subst_apply hex (hgs 1),
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hadd) hes] at h1
  refine Eq.trans ?_ h1
  rw [subst_comp_subst_apply hex hA]
  congr 1
  funext i
  unfold addP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (log_add_const hY (hg 0) (hg 1))) hes]
  congr 1
  funext x
  rw [subst_add hes, k1, k1, lg_ex hY (hg 0), lg_ex hY (hg 1)]
  rfl

end GlobalTheory.RowLaw.CharGerm

namespace GlobalTheory.RowLaw


open MvPowerSeries GlobalTheory.RowLaw.GermRing GlobalTheory.RowLaw.CharGerm in
theorem upG_mvExp_char_mem_intGerm : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ (H : ∀ g, X.CartHyp V g) (χ : MvPowerSeries κ C), IntS V χ → MvPowerSeries.constantCoeff χ = 1 → MvPowerSeries.subst (addP X (gp C κ (0 : Fin 2)) (gp C κ 1)) χ = MvPowerSeries.subst (gp C κ (0 : Fin 2)) χ * MvPowerSeries.subst (gp C κ (1 : Fin 2)) χ → ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → upG g (mvExp (∑ x : I g, (∑ i, MvPowerSeries.coeff (Finsupp.single i 1) χ * X.u g x i) • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈ IntGerm V t := by
  intro C _ V d _ I _ κ _ Y hY H χ hi h0 hχ g S t ht
  haveI := hY.charZero
  rw [intGerm_eq_expInt C V d I κ Y hY H S t ht]
  have hg : ∀ x, constantCoeff (gp C κ g x) = 0 := fun x => constantCoeff_X _
  refine ⟨subst (gp C κ g) χ, intS_subst hg (fun _ => intS_X _) hi, ?_⟩
  have hL : ∀ (g : Fin 2) (i : κ), constantCoeff (∑ c : I g, Y.u g c i •
      (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) = 0 := fun g i => by

    simp [map_sum]
  have hLs := hasSubst_of_constantCoeff_zero (hL g)
  have hes : HasSubst (fun p : Fin 2 × κ => Y.expPt p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => constantCoeff_subst_zero (hL _) (hY.exc _)
  have hU0 : ∀ x : I g, constantCoeff (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C) = 0 :=
    fun _ => constantCoeff_X _
  have hUs := hasSubst_of_constantCoeff_zero hU0
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hg) hes]
  have e : (fun s => subst (fun p : Fin 2 × κ => Y.expPt p.1 p.2) (gp C κ g s)) = fun s =>
      subst (fun i : κ => ∑ c : I g, Y.u g c i • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C))
        (Y.ex s) := by
    funext s
    rw [gp, subst_X hes]
    rfl

  rw [e, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hY.exc) hLs, subst_ex_eq_mvExp hY χ h0 hχ,
  (GlobalTheory.mvExp_add_subst_linear C κ).2.2.1 _ _ _ (hL g) (by simp [map_sum])]
  unfold upG

  rw [(GlobalTheory.mvExp_add_subst_linear C (I g)).2.2.1 _ _ _ hU0 (by simp [map_sum])]
  congr 1
  rw [subst_sum_smul hLs, subst_sum_smul hUs]
  simp only [subst_X hLs, subst_X hUs, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

end GlobalTheory.RowLaw
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP2 Formalism.QuantumDeterminants

namespace GlobalTheory.JetBoundShifted

open Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal

theorem bigCellJetBound_shiftedTypePlace {P : M.Par} {Wp Wq Wq' : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] {up up' : ℕ → ℝ}
    (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P up up') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp)) (n₀ p₀ : ℕ) (hT : 0 < Tq p)
    (h : ∀ c : Fin (P.r + 1) → ℂ, Ew q (fun _ => 1) F (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c)) :
    jN2 q F ≤ ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) * bigCellDetWeightedEnergyIntegral p f (2 * p₀ + n₀) := by
  have hT0 : 0 ≤ (Tq p)⁻¹ ^ n₀ := by positivity
  unfold jN2 bigCellDetWeightedEnergyIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun c => ?_
  rw [← ENNReal.ofReal_mul hT0]
  refine ENNReal.ofReal_le_ofReal ((h c).trans (le_of_eq ?_))
  ring

end GlobalTheory.JetBoundShifted

namespace GlobalTheory.JetBoundShifted

open MeasureTheory
open scoped ENNReal

theorem main : ∀ C₃ CΛ C₀ C₂ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → 0 < C₂ → ∃ C₄ : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Fp : B.Mat P.k P.r → (Wqp →L[ℂ] Wp)) (Fm : B.Mat P.k P.r → (Wqm →L[ℂ] Wp)) (b Λ : ℝ) (n₀ p₀ : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → TBB.TTp pp = TBB.TTp p → TBB.TTp pm = TBB.TTp p → NormAtSh p pp pm f Fp Fm b n₀ p₀ → TBB.PtBound pp Fp (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) → TBB.PtBound pm Fm (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.JetConstSq.main C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Fp Fm b Λ n₀ p₀ hb hΛ hΛb
    hn₀ hp₀ htp htm hNorm hPp hPm hReg γ hγ hG
  have hGp : 0 < TBB.Gp pp γ := by rw [gp_eq p pp htp]; exact hG
  have hGm : 0 < TBB.Gp pm γ := by rw [gp_eq p pm htm]; exact hG
  have hK := hC₄ b Λ P.r n₀ p₀ hb hΛ hΛb hn₀ hp₀
  set G := TBB.Gp p γ with hGdef
  set m : ℝ := ((2 * P.r + 2 : ℕ) : ℝ) with hm
  have hb0 : 0 < b := by linarith
  have hT0 : 0 < TBB.Tq p := p.T.base.T'_pos
  set c : ℝ := 1 * (C₂ * Λ ^ 2) ^ (P.r + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  set T : ℝ := (TBB.Tq p)⁻¹ ^ n₀ with hTdef
  have hT0' : 0 ≤ T := by positivity
  set B3 : ℝ := b ^ (2 * C₃ * m ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) with hB3
  have hB30 : 0 ≤ B3 := by positivity
  set A : ℝ := (3 * b) ^ (2 * n₀) * (TBB.Tq p / G) ^ n₀ * G⁻¹ ^ (2 * p₀) with hA
  have hA0 : 0 ≤ A := by positivity
  set J := TBB.jN2 p f
  have hReg' : TBB.bigCellDetWeightedEnergyIntegral p f (2 * p₀ + n₀) ≤ ENNReal.ofReal B3 * J := hReg _ le_rfl
  have hEp : ENNReal.ofReal (TBB.Ew pp (fun _ => 1) Fp (P.r + 1) [] γ) ≤
      ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J)) := by
    refine (hPp γ hγ hGp).trans ?_
    gcongr
    exact (bigCellJetBound_shiftedTypePlace p pp f Fp n₀ p₀ hT0 fun c => hNorm.2.1 c).trans (by gcongr)
  have hEm : ENNReal.ofReal (TBB.Ew pm (fun _ => 1) Fm (P.r + 1) [] γ) ≤
      ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J)) := by
    refine (hPm γ hγ hGm).trans ?_
    gcongr
    exact (bigCellJetBound_shiftedTypePlace p pm f Fm n₀ p₀ hT0 fun c => hNorm.2.2 c).trans (by gcongr)
  set X := ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J))
  have hE : ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] γ) ≤ ENNReal.ofReal A * (2 * X) := by
    refine (ENNReal.ofReal_le_ofReal (hNorm.1 γ hγ hG)).trans ?_
    rw [ENNReal.ofReal_mul hA0]
    gcongr
    refine ENNReal.ofReal_add_le.trans ?_
    rw [two_mul]; exact add_le_add hEp hEm
  refine hE.trans ?_
  clear_value A c T B3 J G m
  have hX : ENNReal.ofReal A * (2 * X) = ENNReal.ofReal (A * 2 * c * T * B3) * J := by
    simp only [X]
    rw [show A * 2 * c * T * B3 = A * (2 * (c * (T * B3))) by ring, ENNReal.ofReal_mul hA0,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hT0', ENNReal.ofReal_ofNat]
    ring
  rw [hX]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by simp)
  have hGne : G ≠ 0 := hG.ne'
  have heq : A * 2 * c * T * B3 = (2 * (3 * b) ^ (2 * n₀) * c * B3) * G⁻¹ ^ (2 * p₀ + n₀) := by
    simp only [hA, hTdef]
    rw [pow_add, div_eq_mul_inv]
    have : (TBB.Tq p * G⁻¹) ^ n₀ * (TBB.Tq p)⁻¹ ^ n₀ = G⁻¹ ^ n₀ := by
      rw [← mul_pow]; congr 1; field_simp
    linear_combination (2 * (3 * b) ^ (2 * n₀) * G⁻¹ ^ (2 * p₀) * c * B3) * this
  rw [heq]
  exact mul_le_mul_of_nonneg_right hK (by positivity)

end GlobalTheory.JetBoundShifted
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_algClosed_valuedField_over_completeDVR : ∀ (T : CDVR) (ϖ : T.V), Irreducible ϖ → CharZero T.Fr → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F) (_ : Algebra T.Fr F) (_ : Algebra T.V F) (_ : IsScalarTower T.V T.Fr F) (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v ∧ ∃ (O : Type) (_ : CommRing O) (_ : Algebra O F) (_ : Algebra T.V O) (_ : IsScalarTower T.V O F), Function.Injective (algebraMap O F) ∧ (∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) ∧ ∀ g : ℕ, g ≠ 0 → ¬ IsUnit ((g : ℕ) : T.V) → IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O := by
  first | exact @GlobalTheory.ClosedValuedField.exists_field_over_cdvr | exact GlobalTheory.ClosedValuedField.exists_field_over_cdvr | (intros; apply GlobalTheory.ClosedValuedField.exists_field_over_cdvr <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem eigBasis_of_generic {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {A J : Type} [Fintype J] {m : J → ℕ} {d : ℕ} (M : A → Matrix (Fin d) (Fin d) V) (χ : J → A → K)
    (hsep : ∀ j j', j ≠ j' → ∃ a, χ j a ≠ χ j' a) (u : (Σ j, Fin (m j)) → Fin d → V)
    (heig : ∀ a ℓ i, ∑ k, algebraMap V K (M a i k) * algebraMap V K (u ℓ k) = χ ℓ.1 a * algebraMap V K (u ℓ i))
    (hbas : ∀ p : Fin d → K, ∃! b : (Σ j, Fin (m j)) → K, ∀ k, ∑ ℓ, b ℓ * algebraMap V K (u ℓ k) = p k)
    (τ : J) (t : A → V) (ht : ∀ a, algebraMap V K (t a) = χ τ a)
    (hsat : ∀ (v : Fin d → V) (a : V), a ≠ 0 →
      a • v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩) →
      v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩)) :
    (∀ i a, (M a).mulVec (u ⟨τ, i⟩) = t a • u ⟨τ, i⟩) ∧
      ∀ v : Fin d → V, (∀ a, (M a).mulVec v = t a • v) → ∃! c : Fin (m τ) → V, ∑ i, c i • u ⟨τ, i⟩ = v := by
  classical
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  have hext : ∀ (g : Fin (m τ) → K) (k : Fin d),
      ∑ ℓ : (Σ j, Fin (m j)), (if h : ℓ.1 = τ then g (h ▸ ℓ.2) else 0) * algebraMap V K (u ℓ k) =
        ∑ i, g i * algebraMap V K (u ⟨τ, i⟩ k) := by
    intro g k
    rw [Fintype.sum_sigma, Finset.sum_eq_single τ]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  refine ⟨fun i a => ?_, fun v hv => ?_⟩
  · funext k
    apply hinj
    have := heig a ⟨τ, i⟩ k

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, ht]
    exact this
  obtain ⟨b, hb, -⟩ := hbas fun k => algebraMap V K (v k)
  have hb0 : ∀ ℓ : (Σ j, Fin (m j)), ℓ.1 ≠ τ → b ℓ = 0 := by
    intro ℓ hℓ
    obtain ⟨a, ha⟩ := hsep _ _ hℓ
    have h1 : ∀ k, ∑ ℓ', (b ℓ' * χ ℓ'.1 a) * algebraMap V K (u ℓ' k) = χ τ a * algebraMap V K (v k) := by
      intro k
      have h2 := congrArg (algebraMap V K) (congrFun (hv a) k)

      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, ht] at h2
      rw [← h2]
      simp only [← hb, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ℓ' _ => ?_
      rw [mul_assoc, ← heig, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      ring
    have h2 : ∀ k, ∑ ℓ', (χ τ a * b ℓ') * algebraMap V K (u ℓ' k) = χ τ a * algebraMap V K (v k) := by
      intro k
      rw [← hb, Finset.mul_sum]
      simp only [mul_assoc]
    have h3 := congrFun ((hbas fun k => χ τ a * algebraMap V K (v k)).unique h1 h2) ℓ
    have h4 : b ℓ * (χ ℓ.1 a - χ τ a) = 0 := by
      rw [mul_sub, h3]; ring
    exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 ha)
  have hb1 : ∀ k, ∑ i, b ⟨τ, i⟩ * algebraMap V K (u ⟨τ, i⟩ k) = algebraMap V K (v k) := by
    intro k
    rw [← hb k, Fintype.sum_sigma, Finset.sum_eq_single τ]
    · intro j _ hj
      exact Finset.sum_eq_zero fun i _ => by rw [hb0 ⟨j, i⟩ hj, zero_mul]
    · simp
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors V) fun i => b ⟨τ, i⟩
  choose g hg using hs
  have hmem : (s : V) • v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩) := by
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨g, funext fun k => hinj ?_⟩

    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hg, ← hb1, Finset.mul_sum]
    simp only [Algebra.smul_def, mul_assoc]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 (hsat v s (nonZeroDivisors.ne_zero s.2) hmem)
  refine ⟨c, hc, fun c' hc' => ?_⟩
  have hK : ∀ c : Fin (m τ) → V, ∑ i, c i • u ⟨τ, i⟩ = v → ∀ k,
      ∑ ℓ : (Σ j, Fin (m j)), (if h : ℓ.1 = τ then algebraMap V K (c (h ▸ ℓ.2)) else 0) * algebraMap V K (u ℓ k) =
        algebraMap V K (v k) := by
    intro c hc k
    rw [hext (fun i => algebraMap V K (c i)) k, ← hc]

    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  have h5 := (hbas fun k => algebraMap V K (v k)).unique (hK c' hc') (hK c hc)
  funext i
  apply hinj
  simpa using congrFun h5 ⟨τ, i⟩

theorem isEigBasis_uvecT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ)
      (τT : 𝓞 E →+* T.V), (∀ a, algebraMap T.V T.Fr (τT a) = io (embK c τ a)) →
      IsEigBasis Ch.actT τT (fun i : Fin (Dw.mult τ) => Ch.uvecT ⟨τ, i⟩) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch τ τT hτ
  letI := io.toAlgebra
  have hu : ∀ ℓ i, Ch.ch.uvec ℓ i = algebraMap T.V T.Fr (Ch.uvecT ℓ i) := Ch.gen.1.2.2.2.2.2.2
  have hA : ∀ a j, Ch.ch.B.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (Ch.actT a j) := Ch.gen.1.2.1
  refine eigBasis_of_generic (K := T.Fr) (m := Dw.mult) (fun a => linPart (Ch.actT a))
    (fun τ a => io (embK c τ a)) ?_ Ch.uvecT ?_ ?_ τ τT hτ (SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ).2
  · intro j j' h
    obtain ⟨a, ha⟩ := GlobalTheory.EigDir.embK_sep c j j' h
    exact ⟨a, fun e => ha (io.injective e)⟩
  · intro a ℓ i
    have h := GlobalTheory.EigDir.linEig_holds E H Dw l Xo c T.Fr y.1 Ch.ch a ℓ i
    simp only [hu, ReciprocityTheory.ChartRestriction.G.TB.dLin, hA] at h
    exact h
  · intro p
    have h := Ch.ch.chart.basis p
    simp only [hu] at h
    exact h

end GlobalTheory.CharDepth
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem unitaryGroup_matGroup_unimodular : ∀ (k r : ℕ), PI.IsMatGroup (GG k r) ∧
    ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), PI.BesselPeriodGGP.IsHaarOn (GG k r) μG →
      PI.IsHaarOnM (GG k r) μG ∧ PI.IsRightInvM (GG k r) μG := by
  intro k r
  have hG : PI.IsMatGroup (GG k r) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  refine ⟨hG, fun μG hμ => ?_⟩
  have hμ' : PI.IsHaarOnM (GG k r) μG := hμ
  refine ⟨hμ', ?_⟩
  obtain ⟨μ, h1, h2, -⟩ := GlobalTheory.SgInf.exists_unimod_GG (k := k) (r := r)
  have h1' : PI.IsHaarOnM (GG k r) μ := h1
  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos _ (GG k r) μ hG h1').1 μG hμ'
  intro s hs
  have h3 : μ.map (PI.rmulQ s) = μ := h2 s hs
  rw [hc, Measure.map_smul, h3]
  apply Measurable.aemeasurable
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [PI.rmulQ, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.quotientMeasure_right_invariant : PI.QuotInv := by
  first | exact @GlobalTheory.QuotRightInv.quotInv | exact GlobalTheory.QuotRightInv.quotInv | (intros; apply GlobalTheory.QuotRightInv.quotInv <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_quotientMeasure_weil : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM G μG → PI.IsHaarOnM S μS → PI.IsRightInvM S μS → ∃ ν, PI.IsQuotM μG μS ν := by
  first | exact @GlobalTheory.QuotWeil.exists_isQuotM | exact GlobalTheory.QuotWeil.exists_isQuotM | (intros; apply GlobalTheory.QuotWeil.exists_isQuotM <;> assumption)
end
