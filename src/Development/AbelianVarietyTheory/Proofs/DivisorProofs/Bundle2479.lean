module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle003
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotalExponentTopWeightBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsTopGrid
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1621
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem trace_definite_forms_identity : TraceDefinitePairsEqAutomorphicTrace := by
  intro p _ G ha V _ _ _ ξ wt hξ L f hf hfb K' f' hf' hf'b hvan
  rw [GlobalTheory.T.bi_invariant_test_function_sum p G ha wt L f hf hfb K' f' hf' hf'b]
  unfold dTrace
  refine finsum_congr (fun q => ?_)
  rw [GlobalTheory.T.heckeTrace_definiteForm_eq_sum_conjClasses p G ha V ξ L f hf hfb K' f' hf' hf'b (Quot.out q)]
  refine finsum_congr (fun c => ?_)
  split_ifs with h
  · rw [hξ (Quot.out q) (Quotient.out c) h.1 h.2.1]
  · rw [GlobalTheory.T.centSum_eq_zero_of_orbitalIntegral_eq_zero p G ha L f hf hfb K' f' hf' hf'b (Quot.out q) (Quotient.out c)
      (hvan (Quot.out q) _ _ _ (Quotient.out c) h), mul_zero]

end GlobalTheory.LKDef
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FPair

theorem bil {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W →ₗ[K] K) (s s' : K) (u : V) (v : W) : f (s • u) (s' • v) = s * (s' * f u v) := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private theorem full_grid_corner {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}
    {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)) :
    Submodule.IsFullLattice D.host.E (latAt S (.grid D.R.m D.R.m) y) := by
  have hsd := (G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
    have : D.R.m = 0 := (Node.grid.inj e).1
    have := D.R.two_le_m
    omega).sd
  have hΛ := GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hsd
  have hglob := Formalism.UG.P.csGlob_lattice (F := D.host.F) _
    (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top (finG (G.V (.grid D.R.m D.R.m)) y)
  let g := S.N.fr (.grid D.R.m D.R.m)
  let e : (Fin (G.V (.grid D.R.m D.R.m)).rank → D.host.E) ≃ₗ[D.host.E]
      (Fin (G.V (.grid D.R.m D.R.m)).rank → D.host.E) := LinearEquiv.ofLinearMap g.1.mulVecLin (g⁻¹).1.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])
  haveI : Submodule.IsLattice D.host.E (latAt S (.grid D.R.m D.R.m) y) :=
    GlobalTheory.T.isLattice_vertexLattice_gridCorner S y
  refine ⟨?_⟩
  have hset : (latAt S (.grid D.R.m D.R.m) y : Set _) =
      e.symm '' (Formalism.UG.CS.globLat (finG (G.V (.grid D.R.m D.R.m)) y) (G.Λ (.grid D.R.m D.R.m)) : Set _) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨z, hz, rfl⟩
      change e (e.symm z) ∈ Formalism.UG.CS.globLat (finG (G.V (.grid D.R.m D.R.m)) y) (G.Λ (.grid D.R.m D.R.m))
      simpa using hz
  rw [hset, Submodule.span_image_linearEquiv, hglob.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem finPair : FinPairK := by
  obtain ⟨CF0, h6⟩ := GlobalTheory.T.exists_totalExponent_topWeight_bound
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨K0, h6'⟩ := h6 CF hCF
  refine ⟨max K0 0, fun ε C hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h6' ε
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ => ?_⟩
  obtain ⟨hb1, Dn, hDn, hdiv, hlog⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt
  obtain ⟨h5mul, h5div, h5fin, h5sum⟩ := GlobalTheory.T.placeValuation_localDegree_arithmetic (K := D.what₂.LL)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (le_trans (by norm_num) hS.size.2.2.2.1 : 1 ≤ D.R.m)
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb1
  have hK : K0 ≤ C := (le_max_left _ _).trans hC
  have hC0 : 0 ≤ C := (le_max_right _ _).trans hC
  refine ⟨fun w => (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ), ⟨fun w => ?_, ?_, fun s => ?_⟩, ?_⟩
  · show (0 : ℝ) ≤ (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ)
    exact_mod_cast (h5div w Dn Dn hDn dvd_rfl).1
  · refine (h5fin Dn hDn).subset fun w hw => ?_
    intro h0
    exact hw (by simp [h0])
  · refine (h5sum Dn hDn s).trans (hlog.trans ?_)
    unfold bOne
    have e1 : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b := by positivity
    have e2 : K0 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b ≤
        C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b := by
      have := mul_le_mul_of_nonneg_right hK e1
      linarith
    have e3 : C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b ≤
        C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig ch.G) * large₂.sc.b := by
      have h1 : 0 ≤ C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b := by positivity
      have h2 : Real.log large₂.sc.b ≤ D.R.m * (Real.log large₂.sc.b + sig ch.G) := by nlinarith
      have := mul_le_mul_of_nonneg_left h2 h1
      nlinarith
    exact e2.trans e3
  · intro w y a a' u v hu hv
    obtain ⟨u0, s, hu0, hs, hsa, hsu⟩ := hu
    obtain ⟨v0, s', hv0, hs', hsa', hsv⟩ := hv
    have hIS := fun τ => GlobalTheory.WtInterlace.weights_top_grid ch.G τ
    refine ⟨GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0, ?_, ?_⟩
    · rw [← hu0, ← hv0]
      exact (GlobalTheory.T.branchingPairing_extendScalars D.what₂.embLL _ _ _ u0 v0).symm
    · have h4 := GlobalTheory.T.branchingPairing_integral_upToExponents (labLL D) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) (listedWt ch.G (.grid D.R.m D.R.m))
        (fun τ => (hIS τ).1) (fun τ => (hIS τ).2) _ _ (full_grid_corner ch.S.toGridChoice y) (GlobalTheory.T.mem_vertexLatticeOrthonormalCoords_topNode_iff ch.S.toGridChoice y) w
        (s • u0) (s' • v0) hsu hsv
      erw [bil] at h4
      by_cases hy : GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0 = 0
      · exact Or.inl hy
      right
      rcases h4 with h0 | h4
      · exact absurd h0 (mul_ne_zero hs (mul_ne_zero hs' hy))
      rw [h5mul w _ _ hs (mul_ne_zero hs' hy), h5mul w _ _ hs' hy] at h4
      set p := Formalism.EigenvalueLevelCeiling.plc w
      set E := ∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p
      have hp := (h5div w (p ^ E) Dn hDn (hdiv p (Formalism.EigenvalueLevelCeiling.plc_prime w))).2
      rw [Nat.cast_pow] at hp
      have h4' : (-(Formalism.DivisionValues.vw w ((p : D.what₂.LL) ^ E) : ℝ)) ≤
          (Formalism.DivisionValues.vw w s : ℝ) + ((Formalism.DivisionValues.vw w s' : ℝ) + (Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0) : ℝ)) := by
        exact_mod_cast h4
      have hp' : (Formalism.DivisionValues.vw w ((p : D.what₂.LL) ^ E) : ℝ) ≤ (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ) := by exact_mod_cast hp
      linarith

theorem infPair : InfPairK := by
  obtain ⟨CF0, h8⟩ := GlobalTheory.T.archimedean_branching_constant_bound
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨K0, h8'⟩ := h8 CF hCF
  refine ⟨max K0 0, fun ε C hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h8' ε
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ => ?_⟩
  obtain ⟨hb1, hlog⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb1
  have hK : K0 ≤ C := (le_max_left _ _).trans hC
  have hC0 : 0 ≤ C := (le_max_right _ _).trans hC
  have hIS := fun τ => GlobalTheory.WtInterlace.weights_top_grid ch.G τ
  set P := ∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ) (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2 with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun τ _ => sq_nonneg _
  have hPa : P ≤ Real.exp (aOne ch.G C large₂.sc.b) := by
    have h1 : Real.log P ≤ aOne ch.G C large₂.sc.b := by
      refine hlog.trans ?_
      unfold aOne
      have e1 : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
      have e2 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G := by positivity
      have := mul_le_mul_of_nonneg_right hK e1
      nlinarith
    rcases hP0.lt_or_eq with h | h
    · calc P = Real.exp (Real.log P) := (Real.exp_log h).symm
        _ ≤ _ := Real.exp_le_exp.2 h1
    · rw [← h]; exact (Real.exp_pos _).le
  intro σ B B' u v hu hv
  obtain ⟨u0, hu0, hB⟩ := hu
  obtain ⟨v0, hv0, hB'⟩ := hv
  refine ⟨GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0, ?_, ?_⟩
  · rw [← hu0, ← hv0]
    exact (GlobalTheory.T.branchingPairing_extendScalars D.what₂.embLL _ _ _ u0 v0).symm
  · obtain ⟨hn1, hn2, h7⟩ := GlobalTheory.T.branchingPairing_archimedean_bound_fockNorm σ ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) (listedWt ch.G (.grid D.R.m D.R.m))
      (fun τ => (hIS τ).1) (fun τ => (hIS τ).2) u0 v0
    refine h7.trans ?_
    have hB1 : (pairK (wt ch.G (.top D.R.m)) (fun _ => (1 : Matrix _ _ ℂ)) (GlobalTheory.CoefModel.mapVV σ _ u0)
        (GlobalTheory.CoefModel.mapVV σ _ u0)).re ≤ B := hB
    have hB2 : (pairK (fun τ => (listedWt ch.G (.grid D.R.m D.R.m) τ).dual) (fun _ => (1 : Matrix _ _ ℂ))
        (GlobalTheory.CoefModel.mapVV σ _ v0) (GlobalTheory.CoefModel.mapVV σ _ v0)).re ≤ B' := hB'
    have hPa' : (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank.symm.symm (wt ch.G (.top D.R.m) τ)
        (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ Real.exp (aOne ch.G C large₂.sc.b) := hPa
    have hP0' : 0 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank.symm.symm (wt ch.G (.top D.R.m) τ)
        (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) := hP0
    have hBn : 0 ≤ B := hn1.trans hB1
    calc _ ≤ Real.exp (aOne ch.G C large₂.sc.b) * _ * _ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPa' hn1) hn2
      _ ≤ Real.exp (aOne ch.G C large₂.sc.b) * B * B' := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hB1 (Real.exp_pos _).le) hB2 hn2
          exact mul_nonneg (Real.exp_pos _).le hBn

end GlobalTheory.FPair

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRam

open GlobalTheory.WeilParts

variable {D : D7}

theorem unramAt_mul {e : AF D.host.F} {a b : (AE D)ˣ →* Circle} (ha : UnramAt e a) (hb : UnramAt e b) : UnramAt e (a * b) := by
  intro x h1 h2 h3
  rw [MonoidHom.mul_apply, ha x h1 h2 h3, hb x h1 h2 h3, one_mul]

theorem unramAt_pow {e : AF D.host.F} {a : (AE D)ˣ →* Circle} (ha : UnramAt e a) (n : ℕ) : UnramAt e (a ^ n) := by
  intro x h1 h2 h3
  rw [MonoidHom.pow_apply, ha x h1 h2 h3, one_pow]

theorem bottom_ram : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hr T Lc μ₀ hμ G => ?_⟩⟩
  intro W i j A A' WW X _ t v e he
  by_cases hS : v ∈ G.pl.S0 ∨ ∃ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
  · right
    rw [mul_div_mul_right_eq_div]
    rcases hS with hS | ⟨PP, hPP, hPv⟩
    · refine ⟨GlobalTheory.T.small_place_not_nonsplit G μ₀ hμ t v e he hS, ?_, ?_⟩
      · rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
        · exact GlobalTheory.T.not_unramAt_mu_div_chi_at_base_place G μ₀ hμ t v e he h0 i j
        · exact GlobalTheory.T.large_place_ratio_ramified G μ₀ hμ t v e he h1 i j
      · rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
        · subst h0; exact GlobalTheory.T.auxiliary_place_not_dvd_different_base_field G
        · exact GlobalTheory.T.large_place_not_dvd_different large₂ hr v h1
    · refine ⟨GlobalTheory.T.twist_place_under_not_nonSplit G μ₀ hμ t v e he PP hPP hPv, ?_, hPv ▸ GlobalTheory.T.twist_place_under_not_dvd_differentIdeal Lc μ₀ hμ t PP hPP⟩
      by_cases h0 : v ∈ G.pl.S0
      · rcases G.pl.mem_S0_of_sum_eq.1 h0 with h0 | h1
        · exact GlobalTheory.T.not_unramAt_mu_div_chi_at_base_place G μ₀ hμ t v e he h0 i j
        · exact GlobalTheory.T.large_place_ratio_ramified G μ₀ hμ t v e he h1 i j
      · exact GlobalTheory.T.square_mu_div_chi_ramified_at_twist_place G μ₀ hμ t v e he h0 PP hPP hPv i j
  · left
    push_neg at hS
    obtain ⟨h1, h2⟩ := GlobalTheory.T.grid_characters_unramified G μ₀ hμ t v e he hS.1 i
    exact ⟨unramAt_mul (GlobalTheory.T.level_character_unramified_mu G μ₀ hμ t v e he hS.1 hS.2 j) (unramAt_pow h2 _), unramAt_mul h1 (unramAt_pow h2 _)⟩

end GlobalTheory.BotRam

end
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem splitPartRealisationWithScalars_char_of_weak : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.R.toRealDat.ExAt → SingleIndexPlacesAreTwisted p → (R2 p).Char (F2 p) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hE hW
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak p.charW hE
  exact GlobalTheory.BigOn.char_charOf D _ _ _ p.P.A3.A _ p.R.toRealDat (F2 p) hc.lev ⟨hc.grp.red_R, hc.grp.red_L, hc.grp.levels, hc.grp.record, hc.grp.chiW⟩ hc.fam hc.models hc.chain hc.thP
    ⟨GlobalTheory.T.splitPart_nonzeroIndexPlaces_twisted D L hT Gi Gl Kc Y cX ex Csz p hW, hc.tup.mu_off, hc.tup.mu_used, hc.tup.mu_ne, hc.tup.mu_conj, hc.tup.mu_on⟩

end GlobalTheory.BigOn
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.FrameRead

open Formalism.IndefR.Bridge

theorem linInd_of_basis {K C X M I : Type} [Field K] [Field C] [AddCommGroup X] [Module K X] [AddCommGroup M] [Module C M]
    (φ : K →+* C) (f : X →ₛₗ[φ] M) (b : Module.Basis I K X) (h : LinearIndependent C fun i => f (b i))
    (n : ℕ) (x : Fin n → X) (hx : LinearIndependent K x) : LinearIndependent C fun a => f (x a) := by
  classical
  have h1 : LinearIndependent K fun a => b.repr (x a) :=
    hx.map' b.repr.toLinearMap (LinearMap.ker_eq_bot.2 b.repr.injective)
  have h2 := GlobalTheory.LatBC.linInd_mapRange φ φ.injective h1
  have h3 := h2.map' (Finsupp.linearCombination C fun i => f (b i)) (LinearMap.ker_eq_bot.2 h)
  refine (funext fun a => ?_ : (fun a => f (x a)) = _) ▸ h3
  simp only [Function.comp_apply]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]

  conv_lhs => rw [← b.linearCombination_repr (x a), Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  simp only [map_smulₛₗ, Finsupp.sum]

theorem exists_avatar {K C X W M I : Type} [Field K] [Field C] [AddCommGroup X] [Module K X] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup M] [Module C M] [Fintype I] (io : C ≃+* ℂ) {σ : K →+* ℂ} {e0 : K →+* C} (h : ∀ x, io (e0 x) = σ x)
    (b : Module.Basis I K X) (c0 : X →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => c0 (b i))
    (hsp : Submodule.span ℂ (Set.range fun i => c0 (b i)) = ⊤) (Φ : X →ₛₗ[e0] M) (hΦ : LinearIndependent C fun i => Φ (b i)) :
    ∃ θ : W →+ M, (∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w) ∧ (∀ x, θ (c0 x) = Φ x) ∧ Function.Injective θ := by
  classical
  let B : Module.Basis I ℂ W := Module.Basis.mk hli hsp.ge
  have hB : ∀ i, B i = c0 (b i) := fun i => Module.Basis.mk_apply _ _ i
  let θ : W →+ M :=
    { toFun := fun w => ∑ i, io.symm (B.repr w i) • Φ (b i)
      map_zero' := by simp
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib] }
  have hθ : ∀ w, θ w = ∑ i, io.symm (B.repr w i) • Φ (b i) := fun _ => rfl
  have hs : ∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w := fun a w => by
    simp [hθ, Finset.smul_sum, mul_smul]
  have hb : ∀ i, θ (c0 (b i)) = Φ (b i) := fun i => by
    rw [← hB, hθ, B.repr_self, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Finsupp.single_apply, hj.symm]
    · simp
  refine ⟨θ, hs, fun x => ?_, (injective_iff_map_eq_zero θ).2 fun w hw => ?_⟩
  · rw [← b.sum_repr x]

    simp only [map_sum, map_smulₛₗ, hs, hb, ← h, RingEquiv.symm_apply_apply]
  · have := Fintype.linearIndependent_iff.1 hΦ _ ((hθ w).symm.trans hw)
    refine B.ext_elem fun i => ?_
    simpa using this i

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G}
  {χ : J →* ℂˣ}

theorem exists_reading (P : ClassPres ι S σ ρ J χ) {C M : Type} [Field C] [AddCommGroup M] [Module C M] (io : C ≃+* ℂ)
    {e0 : K →+* C} (h : ∀ x, io (e0 x) = σ x) (θ : W →+ M) (hs : ∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w)
    (hinj : Function.Injective θ) (Λ : G →* Module.End C M) (hΛ : ∀ γ w, θ (ρ γ w) = Λ (ι γ) (θ w)) :
    ∃ rd : S.Forms →ₛₗ[e0] (G → M),
      (∀ f γ g, rd f (ι γ * g) = rd f g) ∧
      (∀ f (k : J) g, Λ k (rd f (g * k)) = io.symm (χ k : ℂ) • rd f g) ∧
      (∀ (n : ℕ) (f : Fin n → S.Forms), LinearIndependent K f → LinearIndependent C fun a => rd (f a)) ∧
      (∀ (f f' : S.Forms) (A : Finset G), P.ext f' = dcOp A (P.ext f) → (∀ a ∈ A, Λ a = 1) → ∀ g, rd f' g = ∑ s ∈ A, rd f (g * s)) ∧
      ∀ (f : S.Forms) c, rd f (P.y c) = Λ (P.y c)⁻¹ (θ (P.coef ((f : S.Cl → S.V) c))) := by
  let rd : S.Forms →ₛₗ[e0] (G → M) :=
    { toFun := fun f g => Λ g⁻¹ (θ (P.extL f g))
      map_add' := fun f f' => by funext g; simp only [map_add (f := _), Pi.add_apply]
      map_smul' := fun a f => by
        funext g
        simp only [map_smulₛₗ, Pi.smul_apply, hs, ← h, RingEquiv.symm_apply_apply, RingHom.id_apply] }
  have hrd : ∀ f g, rd f g = Λ g⁻¹ (θ (P.ext f g)) := fun _ _ => rfl
  have hm : ∀ a b z, Λ a (Λ b z) = Λ (a * b) z := fun a b z => by rw [map_mul]; rfl
  refine ⟨rd, fun f γ g => ?_, fun f k g => ?_, fun n f hf => ?_, fun f f' A hA h1 g => ?_, fun f c => ?_⟩
  · have := P.extMem_holds f γ g 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at this
    rw [hrd, hrd, this, hΛ, hm]
    congr 2
    group
  · have := P.extMem_holds f 1 g k
    simp only [one_mul, map_one, Module.End.one_apply] at this
    rw [hrd, hrd, this, hs, hm, map_smul]
    congr 3
    group
  · have h1 := linInd_of_basis σ P.extL S.basis P.extBij_holds.1 n f hf
    rw [Fintype.linearIndependent_iff] at h1 ⊢
    intro a ha i
    have h2 := h1 (fun i => io (a i)) (funext fun g => hinj ?_) i
    · simpa using h2
    have h3 := congrArg (fun F => Λ g (F g)) ha

    simp only [Finset.sum_apply, Pi.smul_apply, hrd, map_sum, map_smul, hm, mul_inv_cancel, map_one, Module.End.one_apply,
    Pi.zero_apply, map_zero] at h3

    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, hs, RingEquiv.symm_apply_apply, Pi.zero_apply, map_zero]
    exact h3

  · rw [hrd, hA, dcOp, map_sum, map_sum]
    refine Finset.sum_congr rfl fun s hs' => ?_
    have e : Λ s⁻¹ = 1 := by
      have := map_mul Λ s⁻¹ s
      rw [h1 s hs', mul_one, inv_mul_cancel, map_one] at this
      exact this.symm
    rw [hrd, mul_inv_rev, map_mul, e, one_mul]
  · rw [hrd, P.ext_rep]

end GlobalTheory.FrameRead
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.definiteSideRealisations_coefMap_differ_rootOfUnity : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    {A : FamIn D.what₂.LL G Pl0 T m} {cR : Bridge.CoefDat D D.sp.X'} {cL : ∀ i : Fin m, Bridge.CoefDat D (D.sp.V ((i : ℕ) + 1))}
    {lR : ∀ t, Bridge.LevEnv D D.sp.X' (A.ok t × ℕ)} {lL : ∀ (i : Fin m) t, Bridge.LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)}
    (B : Bridge.FamReal D A cR cL lR lL) (pl : Pl0 → Pl D.host.E) (S : Set (Pl D.host.E)) (Qt : T → Finset (Pl D.host.E))
    (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) (lamR : D.what₂.Tau → DomWeight D.sp.X'.rank)
    (lamL : ∀ i : Fin m, D.what₂.Tau → DomWeight (D.sp.V ((i : ℕ) + 1)).rank)
    (gramR gramR' : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R c0R' : VV D.what₂.LL lamR →ₛₗ[D.what₂.embLL] cR.W)
    (c0L c0L' : ∀ i : Fin m, VV D.what₂.LL (lamL i) →ₛₗ[D.what₂.embLL] (cL i).W),
    Bridge.FamTie B pl S Qt tauL lamR lamL gramR c0R c0L → Bridge.FamTie B pl S Qt tauL lamR lamL gramR' c0R' c0L' →
    ∀ i : Fin m, ∃ a : D.what₂.LL, (∃ k : ℕ, k ≠ 0 ∧ a ^ k = 1) ∧ ∀ F, c0L' i F = D.what₂.embLL a • c0L i F := by
  first | exact @GlobalTheory.CoefRoot.coef_root | exact GlobalTheory.CoefRoot.coef_root | (intros; apply GlobalTheory.CoefRoot.coef_root <;> assumption)
end
end
