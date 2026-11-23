module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle394
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle381
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle382
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartBaseLatticeSupDualSelfDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroLevelTypePrimeOrientationFramesFunctiona
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle383
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle699
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle385
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle388
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
import Mathlib.NumberTheory.RamificationInertia.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.DoubleCosetMeasures.Statement
import Formalism.LocalToGlobal.Divisibility.QLocTied

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct RestrictedProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAnnihilator

open GlobalTheory.IdemModTwo


open Classical in
theorem continuous_singleV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  apply _root_.GlobalTheory.FinPl.SplitPoint.continuous_single_at <;> assumption

theorem trace_split {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} (he : SplitAt D v e)
    (x y : Fv D.host.F v) :
    Algebra.trace (AF D.host.F) (AE D) (fj D (singleV D.host.F v x) * e * (fj D (singleV D.host.F v y) * e)) =
      pairA D.host.F 0 (singleV D.host.F v (x * y)) := by
  have h1 : fj D (singleV D.host.F v x) * e * (fj D (singleV D.host.F v y) * e) =
      fj D (singleV D.host.F v (x * y)) * e := by
    rw [mul_mul_mul_comm, he.1, ← map_mul, singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same]
  have h2 := GlobalTheory.FockCompare.SymplVal.trace_AE D (fj D (singleV D.host.F v (x * y)) * e)
  rw [map_mul (cA D), cA_fj, ← mul_add, he.2.2, ← map_mul (fj D), singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same, mul_one] at h2
  rw [h1]
  exact tmul_one_inj (F := D.host.F) (E := D.host.E) h2

theorem annihilator_subset_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ V ∈ nhds (0 : AE D), ∃ C : Set (AE D), IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → ψ (Algebra.trace (AF D.host.F) (AE D) (a * s)) = 1) → a ∈ C := by
  intro D ψ hψ e hε V hV
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  obtain ⟨y, hy⟩ := hψ v
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  let j : Fv D.host.F v → AE D := fun x => fj D (singleV D.host.F v x) * e
  have hj : Continuous j := by
    have h1 : Continuous (algebraMap (AF D.host.F) (AE D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))
    have h2 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x) :=
      Continuous.prodMk continuous_const (continuous_singleV D.host.F v)
    exact (h1.comp h2).mul continuous_const
  have hj0 : j 0 = 0 := by
    have h0 : singleV D.host.F v 0 = 0 := by
      rw [← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self]
    simp only [j, h0, map_zero, zero_mul]
  have hV' : j ⁻¹' V ∈ nhds (0 : Fv D.host.F v) := hj.continuousAt.preimage_mem_nhds (by rwa [hj0])
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV'
  refine ⟨j '' Metric.closedBall 0 (‖y‖ / r), (isCompact_closedBall _ _).image hj, fun a ha hs => ?_⟩
  obtain ⟨x, hx⟩ := he.exists_scalar a
  rw [ha] at hx
  refine ⟨x, ?_, hx.symm⟩
  by_contra hn
  rw [mem_closedBall_zero_iff, not_le] at hn
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hr.le) hn
  have hx0 : x ≠ 0 := norm_pos_iff.1 hxpos
  have hmem : y / x ∈ Metric.ball (0 : Fv D.host.F v) r := by
    rw [mem_ball_zero_iff, norm_div, div_lt_iff₀ hxpos]
    rw [div_lt_iff₀ hr] at hn
    linarith
  have h := hs (j (y / x)) (hball hmem) (by
    show e * (_ * e) = _ * e
    rw [mul_left_comm, he.1])
  rw [hx] at h
  change ψ (Algebra.trace _ _ (_ * (_ * e))) = 1 at h
  rw [trace_split he, mul_div_cancel₀ _ hx0] at h
  exact hy h

end GlobalTheory.SplitAnnihilator

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_core_compatible_adelicData_characters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → FrameKs T.Q.c.F R.MW → ∃ dict mu chiW x₀, TieIn (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) ∧ LawsCore (reCore T dict mu chiW x₀ T.cE).toCore := by
  first | exact @GlobalTheory.RealGeo.exists_tieIn_reCore | exact GlobalTheory.RealGeo.exists_tieIn_reCore | (intros; apply GlobalTheory.RealGeo.exists_tieIn_reCore <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df.RowsEx

theorem map_mem_span_image {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) (S : Set V) {x : V} (hx : x ∈ Submodule.span K S) :
    j x ∈ Submodule.span ℂ (j '' S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul k y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem span_image_eq_top {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) {ι : Type} (b : Module.Basis ι K V) (S : Set V)
    (hS : Submodule.span K S = ⊤) (hb : Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) :
    Submodule.span ℂ (j '' S) = ⊤ := by
  rw [eq_top_iff, ← hb, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact map_mem_span_image σ j S (by rw [hS]; exact Submodule.mem_top)

end GlobalTheory.Mem.Df.RowsEx

open GlobalTheory.Mem.Df.RowsEx in
theorem GlobalTheory.Mem.Df.rowsDef_nonempty : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), Nonempty (RowsDef I l hX) := by
  intro B X I hI hP l hX
  classical
  have hb := fun a => GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis I hX a
  choose j hj using fun a => (hb a).2.1
  have hA := fun a => GlobalTheory.T.exists_equiv_hermitianFrameNorm_at_complexPlace B.LL B.embLL (MtHL I hX a) (MtCx I a) (j a) (hb a).1.1
    (by simpa only [hj] using (hb a).2.2.1) (by simpa only [hj] using (hb a).2.2.2)
  choose n gA hgA using hA
  have hme := GlobalTheory.T.exists_tupleUnitaryForms_equiv_periodRowForms I hI hP l hX
  choose mq hmq using hme
  let jj : ∀ a, (MtHL I hX a).V →ₛₗ[B.embLL] EuclideanSpace ℂ (Fin (n a)) := fun a => (gA a).toLinearMap.comp (j a)
  letI : ∀ a, Module (𝓞 B.LL) (MtHL I hX a).V := fun a => (MtHL I hX a).modOV
  haveI : ∀ a, IsScalarTower (𝓞 B.LL) B.LL (MtHL I hX a).V := fun a => (MtHL I hX a).towV
  have hL := fun a => GlobalTheory.exists_oLat_of_fg_ringOfIntegers B.O B.LL B.OtoLL B.embLL (MtHL I hX a).V
    (EuclideanSpace ℂ (Fin (n a))) (jj a) (MtHL I hX a).L B.O_int (hb a).1.2.1
    (span_image_eq_top B.embLL (jj a) (MtHL I hX a).b _ (hb a).1.2.2 (by
      have h2 := (hb a).2.2.2
      simp only [← hj] at h2
      have : (Set.range fun i => jj a ((MtHL I hX a).b i)) = (gA a).toLinearMap '' (Set.range fun i => j a ((MtHL I hX a).b i)) := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, h2, Submodule.map_top, LinearEquiv.range]))
  choose L hLc hLg hLy hLs using hL
  let mt : B.places.Pl → (I.cols l).Tup := fun w => if B.places.resChar w = B.host.pde then I.muStar' else I.muStar
  have hmt : ∀ w, mt (B.places.conj w) = mt w := fun w => by
    simp only [mt, GlobalTheory.Mem.Top.TwFin.resChar_conj]
  obtain ⟨W, g, hstd, hmuAt, hmuTw, he0, heT, hcar, hgen, heOp, hze⟩ :=
    GlobalTheory.T.exists_rows_prescribedUnitaryForms_standIns B (I.cols l) n (fun u => (mq u I.mu0).symm.trans (gA I.mu0))
      (fun u a => (mq u a).symm.trans (gA a)) L mt hmt (GlobalTheory.T.stepZeroColumns_classSumForm_posDef I hI hP l hX)
  letI := W.instAmb
  letI := W.instAmbi
  refine ⟨⟨W, fun a => (gA a).trans (g a).toLinearEquiv, ?_, hstd⟩⟩
  refine
    { muAt := hmuAt
      muTw := hmuTw
      eMt0 := ?_
      eMtTw := ?_
      norm := ?_
      lat := ?_
      gen := ?_
      eOp := heOp
      ze := hze }
  · intro u F
    have h : W.eMt0 u (mq u I.mu0 F) = g (I.cols l).mu0 (gA I.mu0 F) :=
      (he0 u _).trans (congrArg (g (I.cols l).mu0) (congrArg (gA I.mu0) ((mq u I.mu0).symm_apply_apply F)))
    have h' : (W.eMt0 u).symm (g (I.cols l).mu0 (gA I.mu0 F)) = mq u I.mu0 F := by
      rw [← h]; exact (W.eMt0 u).symm_apply_apply _
    have hs := hmq u I.mu0 F
    rw [← h'] at hs
    exact hs
  · intro u a F
    have h : W.eMtTw u a (mq u a F) = g a (gA a F) :=
      (heT u a _).trans (congrArg (g a) (congrArg (gA a) ((mq u a).symm_apply_apply F)))
    have h' : (W.eMtTw u a).symm (g a (gA a F)) = mq u a F := by
      rw [← h]; exact (W.eMtTw u a).symm_apply_apply _
    have hs := hmq u a F
    rw [← h'] at hs
    exact hs
  · intro a x
    have h := (g a).norm_map (gA a (toCx I hX a x))
    exact (hgA a x).trans ((congrArg (fun z => ‖gA a z‖) (hj a x)).trans h.symm)
  · intro a y
    constructor
    · intro hy
      have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := by simpa using hy
      obtain ⟨x, hx, hxy⟩ := (Set.ext_iff.1 (hLc a) _).1 ((hcar a _).1 hy')
      refine ⟨x, hx, ?_⟩
      have h1 : gA a (toCx I hX a x) = (g a).symm y := (congrArg (gA a) (hj a x)).symm.trans hxy
      have h2 : g a (gA a (toCx I hX a x)) = y := by rw [h1]; simp
      exact h2
    · rintro ⟨x, hx, rfl⟩
      have h1 : jj a x = gA a (toCx I hX a x) := congrArg (gA a) (hj a x)
      have h2 : g a (jj a x) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 ⟨x, hx, rfl⟩)
      rw [h1] at h2
      exact h2
  · intro a y hy
    have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).gen := by simpa using hy
    have h1 := hLg a _ ((hgen a _).1 hy')
    have h2 : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 h1)
    simpa using h2
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.baseLatticeStepZero_add_conjGeneratorDual_selfDual : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (pb : 𝓞 (I.rec7 l Z).host.E), (pb : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj ((A u).piU : (I.rec7 l Z).host.E) → (H.lev0 u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 (I.rec7 l Z).host.E) (dualSet ((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (I.rec7 l Z).sp.gram0 (H.lev0 u).Lb) = (I.rec7 l Z).sp.crdLat0 ((I.rec7 l Z).sp.X 0).L0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.base_step_zero_tied | exact GlobalTheory.Mem.Col2.TC.base_step_zero_tied | (intros; apply GlobalTheory.Mem.Col2.TC.base_step_zero_tied <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chart_base_lattice_sup_dual_selfDual : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (pb : 𝓞 (I.rec7 l Z).host.E), (pb : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj ((A u).piU : (I.rec7 l Z).host.E) → ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ (I.rec7 l Z).R.m) (β : H.Ch u i), (H.lev u i h1 hm β).Lb ⊔ Ideal.span {pb} • Formalism.L2.Herm.dualL (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (H.lev u i h1 hm β).Lb = Formalism.L2.Herm.crdLat ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X i).L0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.chart_base_sup_dual | exact GlobalTheory.Mem.Col2.TC.chart_base_sup_dual | (intros; apply GlobalTheory.Mem.Col2.TC.chart_base_sup_dual <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZeroLevel_typePrimeOrientation_frames_functionals : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → ∀ u, ∃ x : Formalism.L2.Herm.ColLevelX (H.lev0 u) (fun x => x ∈ (I.rec7 l Z).host.K) (A u).piU (H.vT u) (fun v c z => ((I.rec7 l Z).fm u).fv 0 v c ((A u).pr 0 v c z)), x.piG = X.piG := by
  first | exact @GlobalTheory.Mem.Col2.TC.intV_coe_eq_inclE_of_T_mem | exact GlobalTheory.Mem.Col2.TC.intV_coe_eq_inclE_of_T_mem | (intros; apply GlobalTheory.Mem.Col2.TC.intV_coe_eq_inclE_of_T_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.exists_coefficientField_lower_bounds : ∀ (D : D7), ∃ c0 : Big D, ∀ (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l), (∀ x, j x ∈ (c0 l j).1) ∧ muK l 1 ≤ (c0 l j).1 ∧ ∀ K0 : Loc.FinExt l, (c0 l j).1 ≤ K0.1 → ∀ w ∈ placesOver D.host.E l, ∃ Bw : LocBridge l D.host.E D.nd.Om (_root_.ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(Loc.OL K0), ∀ x, x ∈ D.nd.plOm.1 w ↔ ‖Bw.j x‖ ≤ 1 := by
  first | exact @GlobalTheory.CoeffFieldLower.exists_low | exact GlobalTheory.CoeffFieldLower.exists_low | (intros; apply GlobalTheory.CoeffFieldLower.exists_low <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD

private theorem levEx_of_levelPrimes_eq (D : D7) (S : Finset ℕ) (g : Fin 2 → ℕ) (a b c : ℕ) (hS : S = {g 0, g 1, a, b, c})
    (hlev : ∀ p, p ∈ D.host.levelPrimes ↔ p ∈ S ∨ ∃ u, p = (D.mem u).A.T)
    (hg : ∀ i, D.host.g i = g i) (ha : D.host.pde = a) (hb : D.host.pde' = b) (hc : q0Av D = c) : LevEx D := by
  intro p
  rw [hlev, hS]
  simp only [Finset.mem_insert, Finset.mem_singleton, hg, ha, hb, hc, Fin.exists_fin_two]
  tauto

theorem levEx_of_over : ∀ (D : D7) (P : PreCh) (Lv : LevCh P), Over D P Lv →
    P.H.levelPrimes = {P.H.g 0, P.H.g 1, P.H.pde, P.H.pde', DC.q0H P.H} → LevEx D ∧ ∀ N h, LevEx (setDiv D N h) := by
  intro D P Lv hO hlev
  obtain ⟨sp, hT, hY, hA, hV, hz, X, hX, rfl⟩ := hO
  refine (fun hD => ⟨hD, fun _ _ => hD⟩) ?_
  obtain ⟨B, C, W, V, S, Ns, G⟩ := X
  cases B
  dsimp only at hX
  subst hX
  refine levEx_of_levelPrimes_eq _ P.H.levelPrimes P.H.g P.H.pde P.H.pde' (DC.q0H P.H) hlev ?_ (fun _ => rfl) rfl rfl ?_
  · intro p
    have hT' := C.A_T
    show p ∈ P.H.levelPrimes ∪ Finset.univ.image Lv.T ↔ _
    rw [Finset.mem_union, Finset.mem_image]
    exact or_congr Iff.rfl
      ⟨fun ⟨u, _, hu⟩ => ⟨u, hu.symm.trans (hT' u).symm⟩, fun ⟨u, hu⟩ => ⟨u, Finset.mem_univ _, (hT' u).symm.trans hu.symm⟩⟩
  · unfold q0Av DC.q0H rPrAv DC.rPrH LevelStarExponents.condE
    rfl

end GlobalTheory.Mem.HD
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section
namespace GlobalTheory.Mem.HD.RamBoth

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
  simpa using h

theorem exists_intCast_cong {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (z : w.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ k : ℤ, Valued.v (algebraMap E (w.adicCompletion E) (k : E) - z) ≤ WithZero.exp (-1 : ℤ) := by
  obtain ⟨b, hb⟩ := GlobalTheory.CMVal.Euler.SplitPair.exists_int_cong w z hz
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Fact (Nat.card (𝓞 E ⧸ w.asIdeal)).Prime := ⟨hc ▸ hp⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  have htop : AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) = ⊤ := by
    rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card (AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal)) with h | h
    · exfalso
      have : (1 : 𝓞 E ⧸ w.asIdeal) ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := AddSubgroup.mem_zmultiples 1
      rw [h, AddSubgroup.mem_bot] at this
      exact one_ne_zero this
    · exact h
  obtain ⟨k, hk⟩ : Ideal.Quotient.mk w.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := htop ▸ AddSubgroup.mem_top _
  have hk' : ((k : 𝓞 E ⧸ w.asIdeal)) = Ideal.Quotient.mk w.asIdeal b := by simpa using hk
  have hmem : b - (k : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hk', map_intCast, sub_self]
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((b : E) - (k : E))) ≤ WithZero.exp (-1 : ℤ) := by
    have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [hval]
    refine le_exp_neg_one_of_lt_one ?_
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (b - (k : 𝓞 E))).2 hmem
    simpa using this
  have hb' : Valued.v (algebraMap E (w.adicCompletion E) (b : E) - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := hb
  refine ⟨k, ?_⟩
  have := Valuation.map_sub_le _ (hb'.trans (by simp)) h1
  rw [map_sub (algebraMap E (w.adicCompletion E)), sub_sub_sub_cancel_left] at this
  exact this

theorem mem_aboveF_iff (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {R : HeightOneSpectrum (𝓞 D.host.E)} :
    R ∈ aboveF (L := D.host.E) D.host.F v ↔ R.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl


open Classical in
theorem aboveF_eq_pair (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w P : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ aboveF (L := D.host.E) D.host.F v) (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (hne : w ≠ P) :
    aboveF (L := D.host.E) D.host.F v = {w, P} := by
  haveI := v.isMaximal
  haveI : NoZeroSMulDivisors (𝓞 D.host.F) (𝓞 D.host.E) := ⟨fun {c x} e => by
    rw [Algebra.smul_def, mul_eq_zero,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))] at e
    exact e⟩
  have h1 := Ideal.card_primesOverFinset_le_finrank (𝓞 D.host.E) D.host.F D.host.E v.ne_bot
  rw [D.sp.cm.deg2] at h1
  have h2 : (aboveF (L := D.host.E) D.host.F v).card ≤ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 D.host.E)).card := by
    refine Finset.card_le_card_of_injOn HeightOneSpectrum.asIdeal (fun R hR => ?_)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
    rw [Finset.mem_coe, mem_aboveF_iff] at hR
    rw [IsDedekindDomain.coe_primesOverFinset v.ne_bot]
    exact ⟨R.isPrime, ⟨hR ▸ rfl⟩⟩
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro R hR
    rw [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl <;> assumption
  · rw [Finset.card_pair hne]; omega

theorem unrAt_of_pair {E : Type} [Field E] [NumberField E] {F : Type} [Field F] [NumberField F] [Algebra F E]
    [DecidableEq (HeightOneSpectrum (𝓞 E))] (χ : HChar E) {v : HeightOneSpectrum (𝓞 F)} {w P : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 F) = v) (hP : P.under (𝓞 F) = v) (hne : w ≠ P) (hS : aboveF (L := E) F v = {w, P})
    (hp : (Ideal.absNorm w.asIdeal).Prime) (hF : χ.TrivOn F) (ht : χ.TameAt w) (hun : χ.UnrAt P) : χ.UnrAt w := by
  intro u hu
  have hu1 : Valued.v (u : w.adicCompletion E) = 1 := hu
  obtain ⟨k, hk⟩ := exists_intCast_cong w hp u hu1.le
  have hval : ∀ (R : HeightOneSpectrum (𝓞 E)), Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = 1 ↔
      (k : 𝓞 E) ∉ R.asIdeal := fun R => by
    have h1 : Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = R.valuation E (k : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' R (k : E)
    have h2 : R.valuation E (k : E) = R.intValuation (k : 𝓞 E) := by
      rw [← map_intCast (algebraMap (𝓞 E) E) k]
      exact HeightOneSpectrum.valuation_of_algebraMap (K := E) R (k : 𝓞 E)
    rw [h1, h2, HeightOneSpectrum.intValuation_eq_one_iff]
  have hmem : ∀ (R : HeightOneSpectrum (𝓞 E)), R.under (𝓞 F) = v → ((k : 𝓞 E) ∈ R.asIdeal ↔ (k : 𝓞 F) ∈ v.asIdeal) :=
    fun R hR => by
      rw [← hR, ← map_intCast (algebraMap (𝓞 F) (𝓞 E)) k]
      exact Iff.rfl
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have h5 : Valued.v (algebraMap E (w.adicCompletion E) (k : E)) = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ hk.trans_lt hlt), hu1]
  have hkw := (hval w).1 h5
  have hkP : (k : 𝓞 E) ∉ P.asIdeal := fun h => hkw ((hmem w hw).2 ((hmem P hP).1 h))
  have hk0 : (k : F) ≠ 0 := by
    intro h
    have : k = 0 := by exact_mod_cast h
    exact hkw (by simp [this])
  have hco : ∀ R : HeightOneSpectrum (𝓞 E), ((atFin R (upF F (Units.mk0 (k : F) hk0)) : (R.adicCompletion E)ˣ) :
      R.adicCompletion E) = algebraMap E (R.adicCompletion E) (k : E) := fun R => by
    rw [← map_intCast (algebraMap F E) k]
    rfl
  have h7 := hF.1 v (Units.mk0 (k : F) hk0)
  unfold HChar.resFin at h7
  rw [MonoidHom.finsetProd_apply, hS, Finset.prod_pair hne] at h7
  have h6 : χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 := hun _ (by
    unfold IsUnitAt
    rw [hco, (hval P).2 hkP])
  change χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0))) * χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 at h7
  rw [h6, mul_one] at h7
  have h8 : χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0)) / u) = 1 := by
    refine ht _ ?_ ?_
    · unfold IsUnitAt
      rw [Units.val_div_eq_div_val, map_div₀, hco, h5, hu1, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, hco]
      exact hk
  rw [map_div, div_eq_one, h7] at h8
  exact h8.symm

theorem ram_both : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp →
    ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)),
    w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v →
    ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := by
  classical
  intro D C nch Tp hT μ v w P hw hP hr hun
  by_cases hne : w = P
  · exact hr (hne ▸ hun)
  · exact hr (unrAt_of_pair _ ((mem_aboveF_iff D).1 hw) ((mem_aboveF_iff D).1 hP) hne
      (by convert aboveF_eq_pair D hw hP hne) (hT.ram μ w hr).2.1 (Tp.xi_triv μ) (Tp.xi_tame μ w) hun)

end GlobalTheory.Mem.HD.RamBoth

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.definiteUnitary_spherical_iff_hasSatake_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n) (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w → (π.Sph w ↔ ∃ α, π.IsSat w α) := by
  first | exact @GlobalTheory.InertSatake.sph_iff_isSat | exact GlobalTheory.InertSatake.sph_iff_isSat | (intros; apply GlobalTheory.InertSatake.sph_iff_isSat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.move_down_level_functional_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → ∀ (x : ↥(LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) (hx : γ.1.1 *ᵥ x.1 ∈ LkG (I.rec7 l Z) i hi (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), (I.fm l u a).fv i v _ (L.pr v _ x) = g (L.prk v c.1 ⟨_, hx⟩) := by
  set_option maxHeartbeats 8000000 in
    exact @GlobalTheory.Mem.Col2.TC.dn_level_functional
end
