module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle010
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle009
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle004
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle110
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ B : GlobalTheory.LFun.Fam D.host.E, ∃ a : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B → ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = a P d • f := by
  first | exact @GlobalTheory.ParamEigen.eig_of_param | exact GlobalTheory.ParamEigen.eig_of_param | (intros; apply GlobalTheory.ParamEigen.eig_of_param <;> assumption)
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Deg

theorem rowsDeg_at_record : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → CT ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → 2 * C2 ≤ C → |Ca| ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), 3 * |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsDeg T Z C := by
  intro CT cH cV Ca C2 Ch c C k2 hCT k3 k4 hCh hcC hCsq1 hC2 hCa D large₂ u T Z C' Cl Cg cb Cu cT C0 h3C hH hC3 hHH hV hA hS hTP hG0 hE
  have hc0 : 0 ≤ c := by linarith
  have hC1 : 1 ≤ C := k2.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by nlinarith
  have hHHc : UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 c :=
    BridgeLemma₂.rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) hHH
  have hK := BridgeLemma₂.rows_KBound_of Z hH hHHc k2 hCT
  have hr0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ D.R.m := by rw [BridgeLemma₂.rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast BridgeLemma₂.rows_f_pos D
  have hL1 : 1 ≤ large₂.sc.L := BridgeLemma.d_one_le_L D large₂
  have hkm : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have hk5 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.1.2.1
  have ha2 : |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2 ≤ D.R.k := by
    refine le_trans ?_ hk5
    have e1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e4 : (D.R.m : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h5 : 0 ≤ (D.R.m : ℝ) ^ 5 := by positivity
    have e2 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ))) (by linarith : 0 ≤ large₂.sc.L - 1)]
    have hab := abs_nonneg C2
    have hP : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by linarith
    calc |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2
        = |C2| * ((D.R.m : ℝ) ^ 2 + 2 * (D.R.m : ℝ) ^ 4) := by ring
      _ ≤ |C2| * (3 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hab
      _ = (3 * |C2|) * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
      _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := mul_le_mul_of_nonneg_right h3C hP
      _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * D.R.k) + 4 * BridgeLemma₂.pairCountExponent D c D.R.k +
    4 * (c * (D.R.rS : ℝ) ^ 2) + (|C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2) / 2 +
    12 * ((D.R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := BridgeLemma₂.pairCountExponent_nonneg D hc0 D.R.k
    positivity
  have hqb := BridgeLemma₂.rows_q_bound (m := D.R.m) (k := D.R.k) (r := D.R.rS) (c := c)
    (cf := Cnt.cF D.R.f) (a2 := |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2)
    (BridgeLemma₂.rows_m_cast _) hr0 hkm hc0 (BridgeLemma₂.rows_cF_le hH) ha2
  have hqb' : ((D.R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * D.R.k * (D.R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold BridgeLemma₂.pairCountExponent; exact hqb
  have hra0 : 0 ≤ ((D.R.rS : ℝ) + 1) * a := by positivity
  have hyp : BridgeLemma₂.rows_Hyps Z C' Cl Cg cb Cu cT CT C0 1 c (9 * c + 3) Ca C2 Ch 1 1
      ⌈((D.R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := hC3
      hHH := hHHc
      hV := BridgeLemma₂.rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) hV
      hDEC := hA.2.2
      ha := hS.1
      hb := hS.2.1
      hp := hA.1
      hpp := hA.2.1
      h6 := hS.2.2.1
      hδ := zero_le_one
      hThA := BridgeLemma.word_theorem_a_admissible D u u
      hT := hTP
      hG0 := hG0
      hE := hE
      hc := hc0
      hCh := hCh
      hdim := BridgeLemma₂.rows_dim_pos Z hH.1 (hS.2.2.2.2 hH.1 u)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine BridgeLemma₂.rows_RowsDeg_record _ hyp hK k2 hcC hC1 hCsq hC2 hCa ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil (((D.R.rS : ℝ) + 1) * a)
  have h2 : (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 ≤
      (|C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2) / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * ((D.R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = ((D.R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

end GlobalTheory.Core.Deg
end
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.columnDimension_window_three_of_columnCount : ∀ D : D7, DataNW D → (∀ u, GlobalTheory.Core.Rk.RankMu D u) → StandingNumericalData D 3 := by
  first | exact @GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu | exact GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu | (intros; apply GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_coprime_multiplier_hyperbolic_terms_near_reference : ∀ (D : D7) (X : HidaSetting D), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, ∀ a, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a - hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g ∧ (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
  first | exact @GlobalTheory.ScalW.ef_near_ref | exact GlobalTheory.ScalW.ef_near_ref | (intros; apply GlobalTheory.ScalW.ef_near_ref <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_coprime_multiplier_negativeVector_term_near : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) - hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := by
  first | exact @GlobalTheory.ScalW.znear_term | exact GlobalTheory.ScalW.znear_term | (intros; apply GlobalTheory.ScalW.znear_term <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.wordElement_conj_orthProjHyperbolicNegativeSpan_eq : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : VA X.B.I), X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y) = ∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a + ∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) := by
  first | exact @GlobalTheory.ScalW.Conj.prj_conj | exact GlobalTheory.ScalW.Conj.prj_conj | (intros; apply GlobalTheory.ScalW.Conj.prj_conj <;> assumption)
end

section

open Matrix

namespace GlobalTheory.BesselChar

theorem unip_pi_iff {ι S : Type} [Fintype ι] [DecidableEq ι] [CommRing S] {n ρ : ℕ}
    (E : Matrix (Fin n) (Fin ρ) (ι → S)) (K : Matrix (Fin ρ) (Fin n) (ι → S))
    (M : Matrix (Fin n) (Fin n) (ι → S)) :
    GlobalTheory.BesselChar.Unip E K M ↔ ∀ i, GlobalTheory.BesselChar.Unip (E.map (Pi.evalRingHom (fun _ => S) i))
      (K.map (Pi.evalRingHom (fun _ => S) i)) (M.map (Pi.evalRingHom (fun _ => S) i)) := by
  constructor
  · rintro ⟨⟨T, hT, e⟩, h2⟩ i
    set φ := Pi.evalRingHom (fun _ => S) i
    refine ⟨⟨T.map φ, fun j l hjl => by simp [Matrix.map_apply, hT j l hjl], ?_⟩, fun y hy => ?_⟩
    · have := congrArg (fun X => X.map φ) e
      simpa only [Matrix.map_mul, Matrix.map_add _ (map_add φ)] using this
    · let y' : Fin n → ι → S := fun k => Pi.single i (y k)
      have hy' : K *ᵥ y' = 0 := by
        funext j i'
        by_cases hi : i' = i
        · subst hi
          have h1 := congr_fun (mulVec_map φ K y') j
          have h0 : (fun k => φ (y' k)) = y := by
            funext k; simp [φ, y']
          rw [h0, hy] at h1
          simpa [φ] using h1.symm
        · show (∑ k, K j k * y' k) i' = 0
          rw [Finset.sum_apply]
          refine Finset.sum_eq_zero fun k _ => ?_
          simp [y', Pi.single_apply, hi]
      obtain ⟨a, ha⟩ := h2 y' hy'
      refine ⟨fun l => φ (a l), ?_⟩
      have h0 : (fun k => φ (y' k)) = y := by
        funext k; simp [φ, y']
      have h1 := mulVec_map φ M y'
      have h3 := mulVec_map φ E a
      rw [h0] at h1
      rw [h1, h3, ha]
      funext k
      simp only [Pi.add_apply, map_add (f := _)]
      rw [show φ (y' k) = y k from congr_fun h0 k]
  · intro h
    choose hc hv using h
    choose T hT e using hc
    refine ⟨⟨Matrix.of fun j l i => T i j l, fun j l hjl => by funext i; exact hT i j l hjl, ?_⟩, fun y hy => ?_⟩
    · ext k l i
      have h1 := congr_fun (congr_fun (e i) k) l
      have hT' : (Matrix.of fun j l i => T i j l).map (Pi.evalRingHom (fun _ => S) i) = T i := by
        ext j l; rfl
      have h2 : ((M * E).map (Pi.evalRingHom (fun _ => S) i)) k l
          = ((E + E * Matrix.of fun j l i => T i j l).map (Pi.evalRingHom (fun _ => S) i)) k l := by
        rw [Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hT']
        exact h1
      simpa using h2
    · have hyi : ∀ i, K.map (Pi.evalRingHom (fun _ => S) i) *ᵥ (fun k => y k i) = 0 := by
        intro i
        have := mulVec_map (Pi.evalRingHom (fun _ => S) i) K y
        refine this.trans ?_
        rw [hy]; rfl
      choose a ha using fun i => hv i _ (hyi i)
      refine ⟨fun l i => a i l, ?_⟩
      funext k i
      have h1 := congr_fun (mulVec_map (Pi.evalRingHom (fun _ => S) i) M y) k
      have h3 := congr_fun (mulVec_map (Pi.evalRingHom (fun _ => S) i) E (fun l i => a i l)) k
      have h4 := congr_fun (ha i) k
      simp only [Pi.evalRingHom_apply] at h1 h3
      show (M *ᵥ y) k i = y k i + (E *ᵥ fun l i => a i l) k i
      rw [← h1, ← h3, h4]
      rfl

end GlobalTheory.BesselChar
end

section

open Matrix

namespace GlobalTheory.BesselChar.JointSplit

variable {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂]

theorem fwd (f : A →+* R₁) (g : A →+* R₂) (hinj : ∀ y, f y = 0 → g y = 0 → y = 0)
    (hsurj : ∀ a b, ∃ y, f y = a ∧ g y = b) {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A)
    (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A) (h : GlobalTheory.BesselChar.Unip E K M) :
    GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f) := by
  obtain ⟨⟨T, hT, hMT⟩, h2⟩ := h
  refine ⟨⟨T.map f, fun j i hij => by simp [hT j i hij], ?_⟩, fun y₁ hy₁ => ?_⟩
  · rw [← Matrix.map_mul, hMT, Matrix.map_add _ (map_add f), Matrix.map_mul]
  · choose l hl1 hl2 using hsurj
    obtain ⟨y, hfy, hgy⟩ : ∃ y : Fin n → A, (fun i => f (y i)) = y₁ ∧ (fun i => g (y i)) = 0 :=
      ⟨fun i => l (y₁ i) 0, funext fun i => hl1 _ _, funext fun i => hl2 _ _⟩
    have hKy : K *ᵥ y = 0 := by
      funext i
      apply hinj
      · have := congrFun (GlobalTheory.BesselChar.mulVec_map f K y) i
        rw [hfy, hy₁] at this
        exact this.symm
      · have := congrFun (GlobalTheory.BesselChar.mulVec_map g K y) i
        rw [hgy, Matrix.mulVec_zero] at this
        exact this.symm
    obtain ⟨a, ha⟩ := h2 y hKy
    refine ⟨fun i => f (a i), ?_⟩
    subst hfy
    rw [GlobalTheory.BesselChar.mulVec_map, GlobalTheory.BesselChar.mulVec_map, ha]
    funext i
    simp only [Pi.add_apply, map_add (f := _)]

theorem bwd (f : A →+* R₁) (g : A →+* R₂) (hinj : ∀ y, f y = 0 → g y = 0 → y = 0)
    (hsurj : ∀ a b, ∃ y, f y = a ∧ g y = b) {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A)
    (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A)
    (h1 : GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f))
    (h2 : GlobalTheory.BesselChar.Unip (E.map g) (K.map g) (M.map g)) : GlobalTheory.BesselChar.Unip E K M := by
  choose l hl1 hl2 using hsurj
  have l00 : l 0 0 = 0 := hinj _ (hl1 0 0) (hl2 0 0)
  have extM : ∀ {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) A), X.map f = Y.map f → X.map g = Y.map g → X = Y := by
    intro p q X Y hf hg
    ext i j
    rw [← sub_eq_zero]
    apply hinj
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun hf i) j
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun hg i) j
  have extV : ∀ {p : ℕ} (x z : Fin p → A), (fun i => f (x i)) = (fun i => f (z i)) →
      (fun i => g (x i)) = (fun i => g (z i)) → x = z := by
    intro p x z hf hg
    funext i
    rw [← sub_eq_zero]
    apply hinj
    · rw [map_sub, sub_eq_zero]; exact congrFun hf i
    · rw [map_sub, sub_eq_zero]; exact congrFun hg i
  obtain ⟨⟨T₁, hT₁, e₁⟩, k₁⟩ := h1
  obtain ⟨⟨T₂, hT₂, e₂⟩, k₂⟩ := h2
  let T : Matrix (Fin ρ) (Fin ρ) A := Matrix.of fun i j => l (T₁ i j) (T₂ i j)
  have hTf : T.map f = T₁ := by ext i j; exact hl1 _ _
  have hTg : T.map g = T₂ := by ext i j; exact hl2 _ _
  refine ⟨⟨T, fun j i hij => ?_, ?_⟩, fun y hy => ?_⟩
  · show l (T₁ j i) (T₂ j i) = 0
    rw [hT₁ j i hij, hT₂ j i hij, l00]
  · apply extM
    · rw [Matrix.map_mul, Matrix.map_add _ (map_add f), Matrix.map_mul, hTf, e₁]
    · rw [Matrix.map_mul, Matrix.map_add _ (map_add g), Matrix.map_mul, hTg, e₂]
  · have hy₁ : K.map f *ᵥ (fun i => f (y i)) = 0 := by
      rw [GlobalTheory.BesselChar.mulVec_map, hy]; funext i; exact map_zero f
    have hy₂ : K.map g *ᵥ (fun i => g (y i)) = 0 := by
      rw [GlobalTheory.BesselChar.mulVec_map, hy]; funext i; exact map_zero g
    obtain ⟨a₁, ha₁⟩ := k₁ _ hy₁
    obtain ⟨a₂, ha₂⟩ := k₂ _ hy₂
    have ea₁ : (fun i => f (l (a₁ i) (a₂ i))) = a₁ := funext fun i => hl1 _ _
    have ea₂ : (fun i => g (l (a₁ i) (a₂ i))) = a₂ := funext fun i => hl2 _ _
    refine ⟨fun i => l (a₁ i) (a₂ i), extV _ _ ?_ ?_⟩
    · rw [← GlobalTheory.BesselChar.mulVec_map, ha₁]
      conv_lhs => rw [← ea₁, GlobalTheory.BesselChar.mulVec_map]
      funext i
      simp only [Pi.add_apply, map_add (f := _)]
    · rw [← GlobalTheory.BesselChar.mulVec_map, ha₂]
      conv_lhs => rw [← ea₂, GlobalTheory.BesselChar.mulVec_map]
      funext i
      simp only [Pi.add_apply, map_add (f := _)]

theorem unip_iff_of_joint : ∀ {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂] (f : A →+* R₁) (g : A →+* R₂), (∀ y, f y = 0 → g y = 0 → y = 0) → (∀ a b, ∃ y, f y = a ∧ g y = b) → ∀ {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A) (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A), GlobalTheory.BesselChar.Unip E K M ↔ GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f) ∧ GlobalTheory.BesselChar.Unip (E.map g) (K.map g) (M.map g) := by
  intro A R₁ R₂ _ _ _ f g hinj hsurj n ρ E K M
  refine ⟨fun h => ⟨fwd f g hinj hsurj E K M h, fwd g f (fun y hg hf => hinj y hf hg)
    (fun a b => (hsurj b a).imp fun _ h => h.symm) E K M h⟩, fun h => bwd f g hinj hsurj E K M h.1 h.2⟩

end GlobalTheory.BesselChar.JointSplit
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.hasDiscreteSeriesKTypes_of_hasParam_cover : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasTypes R lam := by
  first | exact @GlobalTheory.CoverDS.hasTypes_of_hasParam_of_group | exact GlobalTheory.CoverDS.hasTypes_of_hasParam_of_group | (intros; apply GlobalTheory.CoverDS.hasTypes_of_hasParam_of_group <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagFrameWeights

theorem isUnit_res {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) (x : Formalism.L2.DIV.kP PP) (hx : x ≠ 0) :
    IsUnit x := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (Formalism.L2.DIV.kP PP) := Ideal.Quotient.field PP.asIdeal
  exact isUnit_iff_ne_zero.mpr hx



theorem exists_diag_frame : ∀ {D : D7} {n : ℕ} (ρ k : ℕ) (Pg : Finset (Pl D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β₀ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)), Formalism.L2.DIV.IsFrame β₀ Λ → ∀ a : ∀ PP : Pl D.host.E, Fin n → Fin n → kP PP, (∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → a PP i j ≠ 0) → ∃ β₃ : GL (Fin n) (Formalism.IndefR.Lev.EAf D), Formalism.L2.DIV.IsFrame β₃ Λ ∧ Formalism.L2.DIV.St β₃ = Formalism.L2.DIV.St β₀ ∧ ∀ PP ∈ Pg, ∀ y ∈ Formalism.L2.DIV.St β₀, (Formalism.L2.DIV.redFn β₃ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k ↔ Formalism.L2.DIV.redFn β₀ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k) ∧ (∑ i, ∑ j, if Formalism.L2.DIV.symEdge ρ k i j then a PP i j * ((Formalism.L2.DIV.redFn β₀ PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j else 0) = Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge ρ k) (Formalism.L2.DIV.redFn β₃ PP y) := by
  intro D n ρ k Pg Λ β₀ hβ a ha
  classical
  let w : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP i j =>
    if h : PP ∈ Pg ∧ Formalism.L2.DIV.symEdge ρ k i j then (isUnit_res PP (a PP i j) (ha PP h.1 i j h.2)).unit else 1
  let d : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP =>
    GlobalTheory.SeeConjScale.forestLift (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k) (w PP)
  have hd : ∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → (((d PP i)⁻¹ : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) * (d PP j : Formalism.L2.DIV.kP PP) = a PP i j := by
    intro PP hPP i j h
    have e := congrArg Units.val (GlobalTheory.SeeConjScale.forestLift_edge (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k)
      (GlobalTheory.SeeConjScale.symEdge_uniq ρ k) (w PP) h)
    rw [Units.val_mul] at e
    rw [e]
    simp only [w, dif_pos (And.intro hPP h), IsUnit.unit_spec]
  have hex : ∀ j : Fin n, ∃ u : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ,
      ∀ PP ∈ Pg, Formalism.L2.DIV.resS D.host.F PP u = d PP j :=
    fun j => GlobalTheory.FrameRescale.exists_unit_res (D := D) Pg (fun PP => d PP j)
  choose u hu using hex
  have hSt : ∀ M, M ∈ Formalism.L2.DIV.St (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ↔ M ∈ Formalism.L2.DIV.St β₀ := by
    intro M
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨GlobalTheory.SeeConjRead.diagGL u * y * (GlobalTheory.SeeConjRead.diagGL u)⁻¹, (GlobalTheory.FrameRescale.frGL_mul β₀ (GlobalTheory.SeeConjRead.diagGL u) y).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u, ?_⟩
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
  have hred : ∀ PP ∈ Pg, ∀ M ∈ Formalism.L2.DIV.St β₀,
      Formalism.L2.DIV.redFn (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP M =
        (GlobalTheory.SeeConjRead.diagGL (d PP))⁻¹ * Formalism.L2.DIV.redFn β₀ PP M * GlobalTheory.SeeConjRead.diagGL (d PP) := by
    intro PP hPP M hM
    obtain ⟨y, rfl⟩ := hM
    have e1 : Formalism.L2.DIV.frGL β₀ y =
        Formalism.L2.DIV.frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u) := by
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
    have hb : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (GlobalTheory.SeeConjRead.diagGL u) = GlobalTheory.SeeConjRead.diagGL (d PP) := by
      apply Units.ext
      ext i j
      show Formalism.L2.DIV.resS D.host.F PP (((GlobalTheory.SeeConjRead.diagGL u : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j) =
        ((GlobalTheory.SeeConjRead.diagGL (d PP) : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.kP PP)) i j
      rw [GlobalTheory.SeeConjRead.diagGL_val, GlobalTheory.SeeConjRead.diagGL_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        exact hu i PP hPP
      · exact map_zero _
    have e3 := Formalism.L2.DIV.redFn_frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u)
    have e4 := Formalism.L2.DIV.redFn_frGL β₀ PP y
    rw [← e1] at e3
    rw [e3, e4, GlobalTheory.FrameRescale.bc_conj, hb]
  refine ⟨β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u), ?_, ?_, ?_⟩
  · intro x
    rw [hβ x]
    have hinv : ((β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u))⁻¹).val = Matrix.diagonal (fun i => ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D)) *
          (β₀⁻¹).val := by
      rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, GlobalTheory.SeeConjRead.diagGL_inv, GlobalTheory.FrameRescale.intGL_diagGL_val]
    rw [hinv]
    refine forall_congr' fun i => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    have hm : ((u i : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) * ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) = 1 := congrArg Subtype.val (u i).mul_inv
    constructor
    · intro h
      exact Subring.mul_mem _ ((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ).val.2 h
    · intro h
      have h2 := Subring.mul_mem _ (u i).val.2 h
      rwa [← mul_assoc, hm, one_mul] at h2
  · ext M
    exact hSt M
  · intro PP hPP y hy
    rw [hred PP hPP y hy]
    refine ⟨(GlobalTheory.SeeConjRead.unipSym_conj_iff ρ k (d PP) _).symm, ?_⟩
    unfold Formalism.L2.DIV.edgeSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [GlobalTheory.SeeConjRead.diagGL_conj_apply, ← hd PP hPP i j h]
      ring
    · rfl

end GlobalTheory.DiagFrameWeights
end
end
