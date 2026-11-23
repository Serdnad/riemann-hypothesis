module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle467
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBplusNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle430
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
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
import Mathlib.RingTheory.Finiteness.Lattice
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section
namespace GlobalTheory.FibDensMass

section Curry
variable {ι : Type} [Fintype ι] {κ : ι → Type} [∀ i, Fintype (κ i)] {Y : (i : ι) → κ i → Type}
  [∀ i j, MeasurableSpace (Y i j)]

theorem measurePreserving_curry (μ : ∀ i j, Measure (Y i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry Y) (Measure.pi fun p : (i : ι) × κ i => μ p.1 p.2)
      (Measure.pi fun i => Measure.pi fun j => μ i j) := by
  apply _root_.GlobalTheory.ColFourier.measurePreserving_piCurry <;> assumption

end Curry

theorem lintegral_fin_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]
    · refine lintegral_congr fun a => ?_
      rw [Fin.prod_univ_succ]
      rfl
    · exact Finset.aemeasurable_fun_prod _ fun i _ =>
        (hf _).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)

theorem lintegral_fintype_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod fun i => hf _

theorem block_mass (s : ℕ) (A : Matrix (Fin s) (Fin s) ℂ) (hA : A.PosDef) :
    ∫⁻ w : Low s → ℂ, ENNReal.ofReal (GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) *
      GlobalTheory.FlagFibre.dens Aᵀ w) = 1 := by
  have hAt : Aᵀ.PosDef := hA.transpose
  have hd : 0 < A.det.re := (GlobalTheory.FlagFibre.FlagInt.re_facts hA).1
  have hc := GlobalTheory.TrueCx.flagConst_pos s
  have hk : 0 ≤ GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) := by positivity
  simp_rw [ENNReal.ofReal_mul hk]
  rw [lintegral_const_mul _ (GlobalTheory.FlagFibre.measurable_dens _).ennreal_ofReal,
    GlobalTheory.FlagFibre.FlagInt.lintegral_dens s Aᵀ hAt, Matrix.det_transpose, ← ENNReal.ofReal_mul hk]
  rw [← ENNReal.ofReal_one]
  congr 1
  have : A.det.re ^ ((s : ℤ) - 1) * A.det.re ^ (1 - (s : ℤ)) = 1 := by
    rw [← zpow_add₀ hd.ne']; simp
  calc GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) * (A.det.re ^ (1 - (s : ℤ)) / GlobalTheory.TrueCx.flagConst s)
        = (A.det.re ^ ((s : ℤ) - 1) * A.det.re ^ (1 - (s : ℤ))) * (GlobalTheory.TrueCx.flagConst s / GlobalTheory.TrueCx.flagConst s) := by ring
    _ = 1 := by rw [this, div_self hc.ne', one_mul]

end GlobalTheory.FibDensMass

open GlobalTheory.FibDensMass in
theorem GlobalTheory.FlagCell2.fibDens_mass : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (G : Mat m ℂ), (∀ τ, (G τ).PosDef) → (∀ y, 0 ≤ fibDens G y) ∧ ∫⁻ y : Cell m → ℂ, ENNReal.ofReal (fibDens G y) = 1 := by
  intro ι _ m G hG
  have hnn : ∀ τ (w : Low (m τ) → ℂ), 0 ≤ GlobalTheory.TrueCx.flagConst (m τ) * (G τ).det.re ^ ((m τ : ℤ) - 1) *
      GlobalTheory.FlagFibre.dens (G τ)ᵀ w := fun τ w =>
    mul_nonneg (mul_nonneg (GlobalTheory.TrueCx.flagConst_pos _).le
      (zpow_nonneg (GlobalTheory.FlagFibre.FlagInt.re_facts (hG τ)).1.le _)) (GlobalTheory.FlagFibre.dens_nonneg _ _)
  refine ⟨fun y => Finset.prod_nonneg fun τ _ => hnn τ _, ?_⟩
  have hmp := measurePreserving_curry (Y := fun (τ : ι) (_ : Low (m τ)) => ℂ) (fun _ _ => (volume : Measure ℂ))
  let g : ∀ τ, (Low (m τ) → ℂ) → ℝ≥0∞ := fun τ w => ENNReal.ofReal (GlobalTheory.TrueCx.flagConst (m τ) *
    (G τ).det.re ^ ((m τ : ℤ) - 1) * GlobalTheory.FlagFibre.dens (G τ)ᵀ w)
  have hpt : ∀ y : Cell m → ℂ, ENNReal.ofReal (fibDens G y) = ∏ τ, g τ (MeasurableEquiv.piCurry (fun (τ : ι) (_ : Low (m τ)) => ℂ) y τ) := by
    intro y
    simp only [fibDens, g]
    rw [ENNReal.ofReal_prod_of_nonneg fun τ _ => hnn τ _]
    rfl
  simp_rw [hpt]
  rw [show (volume : Measure (Cell m → ℂ)) = Measure.pi fun p : Cell m => (volume : Measure ℂ) from rfl,
    hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (fun z => ∏ τ, g τ (z τ))]
  rw [lintegral_fintype_prod (μ := fun τ => Measure.pi fun _ : Low (m τ) => (volume : Measure ℂ))
    fun τ => ((GlobalTheory.FlagFibre.measurable_dens _).const_mul _).ennreal_ofReal.aemeasurable]
  exact Finset.prod_eq_one fun τ _ => block_mass (m τ) (G τ) (hG τ)
end
end

section

noncomputable section

namespace GlobalTheory.RankAdd

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

theorem finrank_iSup_of_indep {R V ι : Type} [Field R] [AddCommGroup V] [Module R V] [FiniteDimensional R V]
    [Fintype ι] (S : ι → Submodule R V) (hS : iSupIndep S) :
    finrank R (⨆ i, S i : Submodule R V) = ∑ i, finrank R (S i) := by
  classical
  have key : ∀ s : Finset ι, finrank R (⨆ i ∈ s, S i : Submodule R V) = ∑ i ∈ s, finrank R (S i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
      have hd : Disjoint (S a) (⨆ i ∈ s, S i) := hS.disjoint_biSup (y := (s : Set ι)) (by exact_mod_cast ha)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (S a) (⨆ i ∈ s, S i)
      rw [hd.eq_bot, finrank_bot, add_zero] at h
      exact h
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), S i) = ⨆ i, S i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← hu]
  exact key Finset.univ

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ}

theorem rankOn_eq_finrank_span (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (Z : Comp Xo c) (G : WTZ D.host.E) :
    rankOn U Z G = finrank c.F (Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G))) := by
  have hset : (partLat U Z G : Set (cuspW Xo c U G)) =
      Submodule.inclusion (cuspOn_le U Z G) '' (latOn U Z G : Set (cuspOn U Z G)) := by
    simp [partLat]
  rw [hset, Submodule.span_image]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (Submodule.inclusion_injective (cuspOn_le U Z G)) _))

end GlobalTheory.RankAdd

namespace GlobalTheory.RankAdd

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

theorem cuspOn_comap_indep {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ D.host.E) :
    iSupIndep (fun Z : Comp Xo c => (cuspOn U Z G).comap (cuspW Xo c U G).subtype) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), (cuspOn U j G).comap (cuspW Xo c U G).subtype) ≤
      LinearMap.ker ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype) :=
    iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact GlobalTheory.CuspSplit.idem_mul_eq_zero (Ne.symm hj) (Submodule.mem_comap.1 hy)
  have h0 := hle hx'
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply] at h0
  apply Subtype.ext
  calc (x : Rul Xo c) = idem Z * x :=
        (GlobalTheory.CuspSplit.idem_mul_of_mem_cuspOn (Submodule.mem_comap.1 hx)).symm
    _ = 0 := h0


set_option maxHeartbeats 1000000 in
theorem rankW_eq_finsum_rankOn : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
    (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : WTZ D.host.E),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → GoodW U x V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G := by
  intro D H Dw l Xo c r U x V dict G hU hG
  obtain ⟨-, -, -, hsup⟩ := GlobalTheory.CuspSplit.splits D H Dw l Xo c r U V dict hU G
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)

  obtain ⟨-, ⟨s, hs⟩, htop⟩ := hG
  haveI : FiniteDimensional c.F (cuspW Xo c U G) := by
    refine Module.Finite.of_fg_top ⟨s, ?_⟩
    rw [← htop, ← hs, Submodule.span_span_of_tower]
  set S : Comp Xo c → Submodule c.F (cuspW Xo c U G) :=
    fun Z => Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G)) with hSdef
  have hspan : Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) = ⨆ Z, S Z := by
    apply le_antisymm
    · rw [Submodule.span_le, ← hsup]
      intro y hy
      have hle : (⨆ Z : Comp Xo c, partLat U Z G) ≤ (⨆ Z, S Z).restrictScalars (𝓞 c.F) :=
        iSup_le fun Z z hz => (le_iSup S Z) (Submodule.subset_span hz)
      exact hle hy
    · exact iSup_le fun Z => Submodule.span_mono (by rw [← hsup]; exact le_iSup (fun Z => partLat U Z G) Z)
  have hind : iSupIndep S := (cuspOn_comap_indep U G).mono fun Z =>
    Submodule.span_le.2 fun y hy => Submodule.mem_comap.2 (GlobalTheory.CuspSplit.coe_mem_of_mem_partLat hy)
  rw [finsum_eq_sum_of_fintype]
  show finrank c.F (Submodule.span c.F (latW U G : Set (cuspW Xo c U G))) = _
  rw [hspan, finrank_iSup_of_indep S hind]
  exact Finset.sum_congr rfl fun Z _ => (rankOn_eq_finrank_span U Z G).symm

end GlobalTheory.RankAdd
end
end

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

theorem _root_.GlobalTheory.T.cuspForms_supLattice_split_over_components : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ G : WTZ D.host.E, Splits U G := by
  first | exact @GlobalTheory.CuspSplit.splits | exact GlobalTheory.CuspSplit.splits | (intros; apply GlobalTheory.CuspSplit.splits <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.topNodeFormWeight_abs_le_linear : ∃ K1 : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), sc.cGap = 1 → ∀ τ i, |(((wt G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ K1 * large₂.sc.b := by
  first | exact @GlobalTheory.InfSize.WtSize.wt_top_abs_le | exact GlobalTheory.InfSize.WtSize.wt_top_abs_le | (intros; apply GlobalTheory.InfSize.WtSize.wt_top_abs_le <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.TopFlip.MeasW

theorem nu_eq {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {t t' : T} {M M' : Vol G}
    (hM : M.Is t) (hM' : M'.Is t') (i j : Fin D.R.m) :
    M.ν (.grid (i + 1) (j + 1)) = M'.ν (.grid (i + 1) (j + 1)) :=
  GlobalTheory.FunObjModel.isAt_unique (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩) (hM'.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩)

theorem exists_ratio : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (i j : Fin D.R.m) (m : Measure (GA D (spW G i j))), m.IsHaarMeasure →
      ∃ s₀ : NNReal, s₀ ≠ 0 ∧ ∀ (t : T) (M : Vol G), M.Is t → ∀ s : NNReal, M.ν (.grid (i + 1) (j + 1)) = s • m → s = s₀ := by
  intro D T L sc G μ₀ _ i j m hm
  by_cases h : ∃ (t : T) (M : Vol G) (s : NNReal), M.Is t ∧ M.ν (.grid (i + 1) (j + 1)) = s • m
  · obtain ⟨t₀, M₀, s₀, hM₀, e₀⟩ := h
    have hH := (hM₀.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund.1
    obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (spW G i j)
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (GA D (spW G i j))) := inferInstance
    have hK0 : m K ≠ 0 :=
      ((isOpen_interior.measure_pos m K.interior_nonempty).trans_le (measure_mono interior_subset)).ne'
    have hK1 : m K ≠ ⊤ := K.isCompact.measure_lt_top.ne
    refine ⟨s₀, ?_, fun t M hM s e => ?_⟩
    · rintro rfl
      rw [e₀, zero_smul] at hH
      exact (isOpen_univ.measure_pos (0 : Measure (GA D (spW G i j))) Set.univ_nonempty).ne' rfl
    · have e1 : s • m = s₀ • m := e.symm.trans ((nu_eq hM hM₀ i j).trans e₀)
      have e2 : (s : ENNReal) * m K = (s₀ : ENNReal) * m K := by
        have e3 := congrArg (fun μ : Measure (GA D (spW G i j)) => μ K) e1
        exact e3
      exact_mod_cast (ENNReal.mul_left_inj hK0 hK1).1 e2
  · exact ⟨1, one_ne_zero, fun t M hM s e => absurd ⟨t, M, s, hM, e⟩ h⟩

end GlobalTheory.TopFlip.MeasW

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.SplitHalves

open GlobalTheory.LFun GlobalTheory.LFun.SplitTie GlobalTheory.FlipMatch.RowChart

variable {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem eq_zero_of_at {z : AE D} (hz : At (evFin D.host.F v) z) (h1 : piW τ z = 0)
    (h2 : piW (τ.comp D.sp.cm.sig) z = 0) : z = 0 := by
  classical
  set l : AF D.host.F := GlobalTheory.LatVac.liftV v 1 with hl
  have hz1 : z = l • z := by
    have h0 := hz (1 - l) (by rw [map_sub, map_one, hl, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h0
    exact h0
  refine ae_ext ?_ fun Q => ?_
  · have e : infPart D (algebraMap (AF D.host.F) (AE D) l) = 0 := by
      change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    rw [hz1, Algebra.smul_def, RingHom.map_mul, e, zero_mul, map_zero]
  · rw [map_zero, map_zero]
    by_cases h : Q.under (𝓞 D.host.F) = v
    · have hm : Q.asIdeal ∈ v.asIdeal.primesOver (𝓞 D.host.E) := ⟨Q.isPrime, ⟨h ▸ rfl⟩⟩
      rw [primesOver_eq_split (isCMExt_host D) τ] at hm
      rcases hm with e | e
      · obtain rfl : Q = splitPrime τ := HeightOneSpectrum.ext e
        rw [← isPlaceIso_complEquiv τ, h1, map_zero]
      · obtain rfl : Q = splitPrime (τ.comp D.sp.cm.sig) := HeightOneSpectrum.ext e
        rw [← isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), h2, map_zero]
    · have e : cpt (D := D) Q (toEAf D (algebraMap (AF D.host.F) (AE D) l)) =
          GlobalTheory.AdeleBaseChange.locMap D.host.F Q (l.2 (Q.under (𝓞 D.host.F))) := (comp_toAd D).base l Q
      have e2 : l.2 (Q.under (𝓞 D.host.F)) = 0 := GlobalTheory.AdelicU.evalV_singleFin_ne h _
      rw [hz1, Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, e, e2, map_zero, zero_mul]

theorem mul_eq_iff {ε : AE D} (hε : At (evFin D.host.F v) ε) {p q : AE D →+* Fv D.host.F v} (hp : p ε = 1) (hq : q ε = 0)
    (hinj : ∀ z : AE D, At (evFin D.host.F v) z → p z = 0 → q z = 0 → z = 0) (z : AE D) :
    ε * z = z ↔ At (evFin D.host.F v) z ∧ q z = 0 := by
  refine ⟨fun h => ⟨fun a ha => ?_, ?_⟩, fun ⟨h1, h2⟩ => sub_eq_zero.1 (hinj _ (fun a ha => ?_) ?_ ?_)⟩
  · rw [← h, ← smul_mul_assoc, hε a ha, zero_mul]
  · rw [← h, RingHom.map_mul, hq, zero_mul]
  · rw [smul_sub, ← smul_mul_assoc, hε a ha, zero_mul, h1 a ha, sub_zero]
  · rw [RingHom.map_sub, RingHom.map_mul, hp, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, h2, mul_zero, sub_zero]

theorem piW_atPl_one : piW τ (atPl (splitPrime τ) 1) = 1 := by
  classical
  exact (complEquiv τ (splitPrime_under τ)).injective (by
    rw [isPlaceIso_complEquiv τ, (atPl_spec _ _).2, Pi.single_eq_same, map_one])

theorem piW_comp_atPl_one : piW (τ.comp D.sp.cm.sig) (atPl (splitPrime τ) 1) = 0 := by
  classical
  exact (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
    rw [isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec _ _).2,
      Pi.single_eq_of_ne (splitPrime_comp_ne (isCMExt_host D) τ), map_zero])

theorem isHalf_iff (ε : AE D) {m k d : ℕ} (e : Fin d ≃ Fin k) (Gm : Matrix (Fin m) (Fin m) D.host.E) (hG : Gm.det ≠ 0)
    (u : Matrix (Fin m) (Fin k) (AE D)) :
    IsHalf ε (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔ ∀ a b, ε * u a b = u a b := by
  constructor
  · intro h a b
    have hAB : (Gm⁻¹).map (incA D) * Gm.map (incA D) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hG), Matrix.map_one _ (map_zero _) (map_one _)]
    obtain ⟨b, rfl⟩ := e.surjective b
    exact half_cancel (x := uᵀ.submatrix e id) hAB h b a
  · intro h a b
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc]
    exact congrArg (· * _) (h c (e a))

theorem entries_iff {m k : ℕ} (u : Matrix (Fin m) (Fin k) (AE D)) (q : AE D →+* Fv D.host.F v) :
    (∀ a b, At (evFin D.host.F v) (u a b) ∧ q (u a b) = 0) ↔ At (evFin D.host.F v) u ∧ u.map q = 0 :=
  ⟨fun h => ⟨fun c hc => Matrix.ext fun a b => (h a b).1 c hc, Matrix.ext fun a b => (h a b).2⟩,
    fun h a b => ⟨fun c hc => congrFun (congrFun (h.1 c hc) a) b, congrFun (congrFun h.2 a) b⟩⟩

theorem halves : ∀ {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∀ {m k d : ℕ} (e : Fin d ≃ Fin k) (Gm : Matrix (Fin m) (Fin m) D.host.E), Gm.det ≠ 0 → ∀ u : Matrix (Fin m) (Fin k) (AE D),
      (IsHalf (atPl w 1) (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔
        At (evFin D.host.F v) u ∧ u.map (piW (τ.comp D.sp.cm.sig)) = 0) ∧
      (IsHalf (cA D (atPl w 1)) (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔
        At (evFin D.host.F v) u ∧ u.map (piW τ) = 0) := by
  intro D v τ w hw m k d e Gm hG u
  subst hw
  have hε := at_atPl τ 1
  constructor
  · rw [isHalf_iff _ e Gm hG, ← entries_iff]
    exact forall₂_congr fun a b => mul_eq_iff hε (piW_atPl_one τ) (piW_comp_atPl_one τ)
      (fun z h0 h1 h2 => eq_zero_of_at τ h0 h1 h2) _
  · rw [isHalf_iff _ e Gm hG, ← entries_iff]
    refine forall₂_congr fun a b => mul_eq_iff (p := piW (τ.comp D.sp.cm.sig)) (at_cA hε) ?_ ?_
      (fun z h0 h1 h2 => eq_zero_of_at τ h0 h2 h1) _
    · rw [← piW_cA_eq, GlobalTheory.DualPairCheck.cA_cA, piW_atPl_one]
    · rw [piW_cA_eq, piW_comp_atPl_one]

end GlobalTheory.SplitHalves

end
end

section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU


theorem _root_.GlobalTheory.T.adelicSchwartz_pointValues_admitted : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], (∀ x : κ → AF F, (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ) ∧ (∃ φ ∈ schA F κ, φ 0 = 1) ∧ (∀ w, ∀ φ ∈ schA F κ, schr ψ w φ ∈ schA F κ) ∧ ∀ (w w' : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ), schr ψ w (schr ψ w' φ) = ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  first | exact @GlobalTheory.TowU.PointVal.adelicSchwartz_pointValues_admitted_alt | exact GlobalTheory.TowU.PointVal.adelicSchwartz_pointValues_admitted_alt | (intros; apply GlobalTheory.TowU.PointVal.adelicSchwartz_pointValues_admitted_alt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)), ∀ φ ∈ SB (κ → Fv F v), φ ≠ 0 →
    ∃ r : (κ → AF F) → ℂ, Rest (evFin F v) φ r ∧ tens (evFin F v) φ r ≠ 0 := by
  first | exact @GlobalTheory.InertSph.exists_rest_tens_ne_zero | exact GlobalTheory.InertSph.exists_rest_tens_ne_zero | (intros; apply GlobalTheory.InertSph.exists_rest_tens_ne_zero <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)


theorem _root_.GlobalTheory.T.eq_zero_of_adelicFourier_separatingChars_vanish : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ (d : ℕ) (A : Type) [AddCommGroup A] (p : A → (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →ₗ[AF F] AF F),
    (∀ a b, p (a + b) = p a + p b) → (∀ u, (∀ a, ψ (p a u) = 1) → u = 0) →
    ∀ μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ N : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ, Continuous N → Integrable N μ → (∀ a, ∫ u, ψ (p a u) * N u ∂μ = 0) → N = 0 := by
  first | exact @GlobalTheory.AdelicFourierUniq.eq_zero | exact GlobalTheory.AdelicFourierUniq.eq_zero | (intros; apply GlobalTheory.AdelicFourierUniq.eq_zero <;> assumption)
end

section


theorem _root_.GlobalTheory.T.meanLogPeriod_chowlaSelberg : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod := by
  first | exact @GlobalTheory.MeanPeriodClosed.meanPeriod | exact GlobalTheory.MeanPeriodClosed.meanPeriod | (intros; apply GlobalTheory.MeanPeriodClosed.meanPeriod <;> assumption)
end
