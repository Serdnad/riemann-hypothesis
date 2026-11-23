module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle051
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle049
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinBase
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle004
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle053
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle046
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinTop
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtExA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle308
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle017
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}
theorem ratV_inc_k {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : ∃ v : Fin L.n → E, u = GlobalTheory.ThK.incV F v := by
  induction hu using AddSubgroup.closure_induction with
  | mem _ h => obtain ⟨v, rfl⟩ := h; exact ⟨v, rfl⟩
  | zero => exact ⟨0, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | add _ _ _ _ h h' =>
    obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := h'; exact ⟨v + w, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | neg _ _ h => obtain ⟨v, rfl⟩ := h; exact ⟨-v, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
theorem neg_incV_k (v : Fin L.n → E) : -GlobalTheory.ThK.incV F v = GlobalTheory.ThK.incV F (-v) := funext fun i => by simp [GlobalTheory.ThK.incV]
def unipotentFirstMatrix (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (v : Fin L.n → E) : Matrix (Fin d.n) (Fin d.n) E := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (v j)
theorem Au_inc_k (v : Fin L.n → E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (GlobalTheory.ThK.incV F v) = incM F (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L v) := by
  ext a b

  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix, incM, Matrix.one_apply, Matrix.sum_apply, Matrix.single_apply, GlobalTheory.ThK.incV, map_sum, apply_ite]
theorem Apc_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ := by
  have h1 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ = 1 := mul_eq_one_comm.1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_blk_k d (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU u))
  have h2 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ = 1 := by rw [← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k, Matrix.transpose_one]
  calc (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) * ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ) := by rw [h2, Matrix.mul_one]
    _ = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
theorem Ap_inc_k (hU : L.UData uM ν 𝓤) (v : Fin L.n → E) : ∃ M : Matrix (Fin d.n) (Fin d.n) E,
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (GlobalTheory.ThK.incV F v) = incM F M := by
  have : FiniteDimensional F E := Module.Finite.of_basis d.bs
  let e := AlgEquiv.ofBijective σ (AlgHom.bijective σ)
  refine ⟨((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v))ᵀ).map e.symm, Matrix.map_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cA_injective_k d) ?_⟩
  show (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (GlobalTheory.ThK.incV F v)).map (cA σ) = (incM F (((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v))ᵀ).map e.symm)).map (cA σ)
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Apc_k, kunf.incM_map_cA, Matrix.map_map, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.neg_incV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k]
  have h : (⇑σ ∘ ⇑e.symm) = id := funext fun x => e.apply_symm_apply x
  rw [h, Matrix.map_id]
  rfl
theorem uM_rat_k (hU : L.UData uM ν 𝓤) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : uM u ∈ rat2 σ d.Y := by
  obtain ⟨v, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k hu
  obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_inc_k hU v
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L v) 0 0 M) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k, hM]
  simp [incM, Matrix.fromBlocks_map]
theorem cj_rat_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV)
    {β : nA σ d.Y d.b} (hβ : β ∈ nF σ d.Y d.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β ∈ nF σ d.Y d.b := by
  obtain ⟨v, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k hu
  obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_inc_k hU v
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 hβ
  refine kunf.mem_nF_iff.2 ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v) * T * M, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.neg_incV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k, hT, hM, kunf.incM_mul', kunf.incM_mul']
theorem mul_Au_k (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ a, X a L.i₀ = 0) (u : Fin L.n → AE F E) :
    X * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u = X := by
  have h : ∀ j, X * Matrix.single L.i₀ (L.em j) (u j) = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, zero_mul]
    · exact mul_zero _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, Matrix.mul_add, Matrix.mul_one, Finset.mul_sum, h, Finset.sum_const_zero, add_zero]
theorem AuT_mul_k (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ b, X L.i₀ b = 0) (u : Fin L.n → AE F E) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * X = X := by
  have h : ∀ j, (Matrix.single L.i₀ (L.em j) (u j))ᵀ * X = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, mul_zero]
    · exact zero_mul _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_sum, Matrix.add_mul, Matrix.one_mul,
    Finset.sum_mul, h, Finset.sum_const_zero, add_zero]
theorem trace_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Matrix.trace (T.1.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β).1) = Matrix.trace (T.1.1 * β.1) := by
  have h1 : T.1.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) = T.1.1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.mul_Au_k _ (fun a => (hT.1 a).2) _
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * T.1.1 = T.1.1 := by
    apply Matrix.map_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cA_injective_k d)
    show (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * T.1.1).map (cA σ) = T.1.1.map (cA σ)
    rw [kunf.map_cA_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Apc_k]
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C1.AuT_mul_k _ (fun b => by simp [(hT.1 b).1]) _
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

section



section
set_option linter.style.haveILetI false
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
open ComplexParameterFamilyContinuity
theorem cptDom_k : _root_.PositivityTheory.SiegelWeilFormula.Act.CptDom_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun nb lam 𝓖 h => ?_, fun L uM ν 𝓤 h => ?_⟩
  · have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
    obtain ⟨hlc, hsc, ht2, hbo⟩ := kfour.nA_top hσ d.ok.frame
    obtain ⟨K, hK, hc⟩ := kfour.nF_cocompact hσ d.ok.frame
    obtain ⟨hnb, hlam, hfd, h1⟩ := h
    obtain ⟨𝓖₀, hfd₀, hcpt⟩ := addFD_of_cover' (nF σ d.Y d.b) hK hc lam
    exact ⟨𝓖₀, ⟨hnb, hlam, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩
  · obtain ⟨hfr, hν, hfd, h1⟩ := h
    haveI : DiscreteTopology L.ratV := ratVec_discrete (F := F) (E := E) L.n
    haveI : Countable L.ratV := ratVec_countable (F := F) (E := E) L.n
    obtain ⟨K, hK, hc⟩ : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ v, ∃ γ ∈ L.ratV, γ + v ∈ K :=
      ratVec_cocompact (F := F) (E := E) L.n
    obtain ⟨𝓤₀, hfd₀, hcpt⟩ := addFD_of_cover' L.ratV hK hc ν
    exact ⟨𝓤₀, ⟨hfr, hν, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩
theorem absConv_k : _root_.PositivityTheory.SiegelWeilFormula.Act.AbsConv_k := by
  intro F E _ _ _ _ _ σ d L s₁ f hf he
  obtain ⟨U, p, Ê, t, -, -, -, -, -, -, -, hmaj⟩ := he 0
  refine ⟨t, fun z hz nb lam 𝓖 h𝓖 hc𝓖 uM ν 𝓤 h𝓤 hc𝓤 T x => ?_⟩
  obtain ⟨hTG, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ d.ok.frame
  obtain ⟨hnb, hlam, hfd, h1⟩ := h𝓖
  obtain ⟨hfr, hν, hfdU, hU1⟩ := h𝓤
  have cu : Continuous uM := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_uM_k L ⟨hfr, hν, hfdU, hU1⟩
  have cn : Continuous nb := kunf.continuous_nb hnb
  have cφ : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z
  set m : (Fin L.n → AE F E) × nA σ d.Y d.b → d.G := fun p => nb p.2 * (uM p.1 * x) with hm
  have cm : Continuous m := (cn.comp continuous_snd).mul ((cu.comp continuous_fst).mul continuous_const)
  have hKc : IsCompact (closure 𝓤 ×ˢ closure 𝓖) := hc𝓤.prod hc𝓖
  obtain ⟨u, hu, hub⟩ := (hmaj z hz).1 (m '' (closure 𝓤 ×ˢ closure 𝓖)) (hKc.image cm)
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std
  have cψ := kfour.continuous_chr (σ := σ) (Y := d.Y) (b := d.b) hψ.1 T.1.1
  obtain ⟨Mψ, hMψ⟩ := hc𝓖.exists_bound_of_continuousOn cψ.continuousOn
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ
  haveI : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by rw [hU1]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  have hS : ∀ᵐ p ∂μ, p ∈ closure 𝓤 ×ˢ closure 𝓖 := by
    rw [ae_iff]
    refine measure_mono_null (t := (closure 𝓤)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (closure 𝓖)ᶜ) ?_ ?_
    · intro p hp
      simp only [Set.mem_ofPred_eq, Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, Set.mem_univ _⟩
      · exact Or.inr ⟨Set.mem_univ _, hp⟩
    · have eU : (closure 𝓤)ᶜ ∩ 𝓤 = ∅ := (show Disjoint (closure 𝓤)ᶜ 𝓤 from
        Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓤)ᶜ) (h' : y ∈ 𝓤) => hy (subset_closure h')).inter_eq
      have eG : (closure 𝓖)ᶜ ∩ 𝓖 = ∅ := (show Disjoint (closure 𝓖)ᶜ 𝓖 from
        Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓖)ᶜ) (h' : y ∈ 𝓖) => hy (subset_closure h')).inter_eq
      refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eU, measure_empty, zero_mul]
      · rw [Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eG, measure_empty, mul_zero]
  have hbd : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, ∀ᵐ p ∂μ, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ≤ |u q| * |Mψ| := by
    intro q
    filter_upwards [hS] with p hp
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k, norm_mul]
    refine mul_le_mul ((hub (m p) ⟨p, hp, rfl⟩ q).trans (le_abs_self _)) ((hMψ p.2 hp.2).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)
  have hcq : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) := fun q =>
    (cφ.comp (continuous_const.mul cm)).mul (cψ.comp continuous_snd)
  have hint : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) μ := fun q =>
    Integrable.of_bound (hcq q).aestronglyMeasurable _ (hbd q)
  refine ⟨hint, ?_⟩
  refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun p => norm_nonneg _) (fun q => ?_)
    ((hu.abs.mul_right |Mψ|).mul_right (μ.real Set.univ))
  calc ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂μ ≤ ∫ _p, |u q| * |Mψ| ∂μ :=
        integral_mono_ae (hint q).norm (integrable_const _) (hbd q)
    _ = |u q| * |Mψ| * μ.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem step_of_triv_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hD : _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k) (x : d.G) (hx : ∀ w, d.cw w (inFrame d.b x) = 1) :
    ∃ B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id B := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have he : eInf F • inFrame d.b x = eInf F • (1 : Matrix _ _ (AE F E)) := (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_one_iff_k d _).1 hx
  obtain ⟨x₁, x₂, x₃, x₄, t, c, b, a, a', hxe, h1, h2, h3, h4, ht, hc, hb, -, ha'⟩ :=
    hD F E σ d ε w₀ hw₀ (eInf F) eInf_mul_self x he
  obtain ⟨AW, BW, hW⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepW_k d hT hA ε w₀ hw₀
  have hW3 := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d hW hW) hW
  have h4' : w₀ * (w₀ * w₀ * w₀) = 1 := by simpa only [mul_assoc] using _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf hw₀
  obtain ⟨BC, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_conj_k d hT hW hW3 (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepN_k d hT x₂ c h2 hc) h4'
  have hinv : w₀⁻¹ = w₀ * w₀ * w₀ := (eq_inv_of_mul_eq_one_left (_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf hw₀)).symm
  obtain ⟨BM, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepM_k d hT x₃ a a' h3 ha'
  have hall := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepN_k d hT x₁ t h1 ht) hC) hM) (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepN_k d hT x₄ b h4 hb)
  rw [hxe, hinv]
  exact ⟨_, hall⟩
end SDf
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem finAct_step_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) {B : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ} (hB : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id B) :
    ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F),
      ∀ f : Mx F E d.m d.n → ℂ, (∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X) → ∀ Φ ∈ d.sch,
        d.T Φ = (fun X => f X * g fun k => (d.crd X k).2) → d.T (d.om x Φ) = fun X => f X * g' fun k => (d.crd X k).2 := by
  intro g hg
  set G : Mx F E d.m d.n → ℂ := fun X => g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X) with hGdef
  have hG : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_invInf_k d g
  have hBG := (hB.2 G hG).1
  set g₁ : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ := fun y => B G (d.cmb fun k => pairA F 0 (y k)) with hg₁
  have hfc : ∀ y, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d (d.cmb fun k => pairA F 0 (y k)) = y := fun y => by
    funext k
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k, _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
    rfl
  have hBg : ∀ X, B G X = g₁ (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X) := fun X => _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.invInf_fcrd_k d hBG X
  by_cases hg0 : g = 0
  · refine ⟨0, (SB _).zero_mem, fun f hf Φ hΦ hTΦ => ?_⟩
    have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ, hg0]; funext X; simp)
    subst hΦ0
    rw [map_zero, d.T_zero]
    funext X
    simp
  refine ⟨g₁, ?_, fun f hf Φ hΦ hTΦ => ?_⟩
  swap
  · have e := (hB.2 G hG).2 f hf Φ hΦ hTΦ
    rw [e]
    funext X
    simp only [id]
    rw [hBg X]
    rfl
  obtain ⟨φ, v₀, hv₀⟩ := exists_schwartz_ne (κ := Fin d.m × Fin d.n × Fin 2) F
  set f₀ : Mx F E d.m d.n → ℂ := fun X => φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1 with hf₀d
  have hf₀ : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f₀ := by
    intro X Z hZ
    have hZ' := (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d Z).1 hZ
    show (φ fun k => _) = φ fun k => _
    congr 1
    funext k
    have : (d.crd Z k).1 = 0 := by
      rw [← eInf_fst_mul (d.crd Z k), ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_smul_k, hZ']
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_add_k]
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((d.crd X k).1 + (d.crd Z k).1) = _
    rw [this, add_zero]
  have hmem : (fun X => f₀ X * G X) ∈ d.schM := by
    show (fun c => f₀ (d.cmb c) * G (d.cmb c)) ∈ schA F (Fin d.m × Fin d.n × Fin 2)
    have e : (fun c => f₀ (d.cmb c) * G (d.cmb c)) = pureA F (⇑φ) g := by
      funext c
      show (φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd (d.cmb c) k).1) *
        g (fun k => (d.crd (d.cmb c) k).2) = _
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
      rfl
    rw [e]
    exact Submodule.subset_span ⟨φ, g, hg, rfl⟩
  obtain ⟨Φ₀, hΦ₀, hTΦ₀⟩ := (hT.1 F E σ d).2.1 _ hmem
  have e := (hB.2 G hG).2 f₀ hf₀ Φ₀ hΦ₀ hTΦ₀
  have hm := (hT.1 F E σ d).1 _ (d.om_sch x Φ₀ hΦ₀)
  rw [e] at hm
  have hs := slice_mem _ hm (fun k => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k))
  have e2 : (fun y : Fin d.m × Fin d.n × Fin 2 → Af F =>
      (fun X => id f₀ X * B G X) (d.cmb fun k => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k)) (y k))) =
      φ v₀ • g₁ := by
    funext y
    simp only [id, Pi.smul_apply, smul_eq_mul]
    rw [hBg]
    have h1 : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d (d.cmb fun k => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k)) (y k)) = y := by
      funext k
      simp only [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k, _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
      rfl
    rw [h1]
    congr 1
    show (φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd (d.cmb _) k).1) = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
    congr 1
    funext k
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (v₀ k)
  have hs' : φ v₀ • g₁ ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F) := by
    rw [← e2]
    exact hs
  have := (SB (Fin d.m × Fin d.n × Fin 2 → Af F)).smul_mem (φ v₀)⁻¹ hs'
  rwa [smul_smul, inv_mul_cancel₀ hv₀, one_smul] at this
end SDf
theorem finAct_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k → _root_.PositivityTheory.SiegelWeilFormula.FinAct_k := by
  intro hT hA hD F E _ _ _ _ _ σ d x hx
  obtain ⟨B, hB⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_of_triv_k d hT hA hD x hx
  exact _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.finAct_step_k d hT x hB
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Hgt
open scoped Matrix TensorProduct NNReal
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl GlobalTheory.WeilM
open GlobalTheory.CompanionTheory.IwaDbl.FrameCore
open Formalism.UG (cT bc)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem exists_scal_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) :
    ∃ ξ : E, ξ ≠ 0 ∧ (∀ i j, σ ((ξ • Y.Jᵀ) j i) = (ξ • Y.Jᵀ) i j) ∧ ∀ w, ∃ (M : Matrix (Fin n) (Fin n) ℂ) (r : ℝ), Mᴴ = M ∧
      IsCartan M (Y.θ w) ∧ r ≠ 0 ∧ (ξ • Y.Jᵀ).map (B.emb w).1 = (r : ℂ) • Mᵀ := by
  have hc := hB.cm
  rcases hY with h | h
  · refine ⟨1, one_ne_zero, fun i j => by simpa using h.herm j i, fun w => ⟨_, 1, ?_, h.cartan w, one_ne_zero, ?_⟩⟩
    · exact Matrix.ext fun i j => (hc.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))
    · ext i j; simp
  · obtain ⟨x, hx⟩ : ∃ x, x - σ x ≠ 0 := by
      by_contra! e
      have := hc.2.1
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
        (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y =>
          (hc.2.2.2 τ y).symm.trans (congrArg τ (sub_eq_zero.1 (e y)).symm))))
    have hs : σ (x - σ x) = -(x - σ x) := by rw [map_sub, cm_conj_conj hc, neg_sub]
    refine ⟨_, hx, fun i j => ?_, fun w => ?_⟩
    · change σ (_ * Y.J i j) = _ * Y.J j i
      rw [map_mul, hs, h.skew, neg_mul_neg]
    · have h1 := hc.2.2.2 (B.emb w).1 (x - σ x)
      rw [hs, map_neg] at h1
      have h2 : (B.emb w).1 (x - σ x) = ((B.emb w).1 (x - σ x)).im * Complex.I := by
        have := congrArg Complex.re h1
        simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at this
        exact Complex.ext (by simp only [Complex.mul_I_re, Complex.ofReal_im]; linarith) (by simp)
      refine ⟨_, ((B.emb w).1 (x - σ x)).im, Matrix.ext fun i j => ?_, h.cartan w, fun e => hx ?_, Matrix.ext fun i j => ?_⟩
      · change star (Complex.I * (B.emb w).1 (Y.J j i)) = Complex.I * (B.emb w).1 (Y.J i j)
        rw [star_mul', ← hc.2.2.2, h.skew]; simp
      · rw [e] at h2
        exact (map_eq_zero _).1 (h2.trans (by simp))
      · change (B.emb w).1 (_ * Y.J j i) = _ * (Complex.I * (B.emb w).1 (Y.J j i))
        rw [map_mul, ← mul_assoc, ← h2]
theorem iwasawa2_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (x : G2 σ Y) :
    ∃ p : siegelOf (Equiv.refl (Fin n ⊕ Fin n)) (UG (cA σ) (dbl (incM F Y.J))).subtype, ∃ k ∈ stab2 σ Y B, x = p * k := by
  have hL : Y.L.IsFullLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨ξ, hξ, hh, hw⟩ := _root_.GlobalTheory.ThK.Dbl.Hgt.exists_scal_k hB hY
  choose M r h1 h2 h3 h4 using hw
  choose b hb hb' using fun w => exists_arch hB.cm (B.emb w) (h1 w) (isUnit_of_cartan (h2 w)) (h2 w) (h3 w) (h4 w)
  obtain ⟨a, -, ha⟩ := Frames.exists_isLatticeFrame_of_arch Y.L b
  obtain rfl : b = fun w => bc (compInf F E w) a := (funext ha).symm
  obtain ⟨g, rfl⟩ := back_surj hξ x
  obtain ⟨p, k, hk, rfl⟩ := HasIwasawa.adelic (a := a) (_root_.GlobalTheory.ThK.Dbl.Hgt.hasIwasawa_fin'_k hB hY (det_ne hY) hξ hh) hb g
  have k2 := keeps_back hL.fg hξ (mem_KAd.1 (inv_mem hk)).1
  rw [map_inv] at k2
  exact ⟨⟨_, back_mem_par hξ p.2⟩, back σ Y hξ k, ⟨fun w => back_comm hξ _ ((hb' w _).1 ((mem_KAd.1 hk).2 w)),
    keeps_back hL.fg hξ (mem_KAd.1 hk).1, k2⟩, map_mul _ _ _⟩
theorem hgtEx_core_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hK : IsCompact (stab2 σ Y B : Set (G2 σ Y))) :
    (∃ K a, IsStab2 (σ := σ) (Y := Y) B K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x) ∧
    ∃ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, Continuous e ∧ ∀ h h', IsEmb h h' (e (h, h')) := by
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := t2Space_adeleRing' (F := F)
  have := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have hI := iwasawaOf_of_isCompact (ν := absE F E) continuous_subtype_val continuous_absE hK (_root_.GlobalTheory.ThK.Dbl.Hgt.iwasawa2_k hB hY)
  refine ⟨⟨_, fun x => hgtOf (Equiv.refl _) (UG (cA σ) (dbl (incM F Y.J))).subtype (absE F E) (stab2 σ Y B) x, isStab2_stab2 B,
    ⟨fun x => ?_, fun p t hp k hk => ?_⟩,
    NNReal.continuous_coe.comp (hI.continuous_hgtOf continuous_subtype_val continuous_absE hK), fun x => hgtOf_pos x⟩,
    emb2 σ Y, ((continuous_blkGL _).comp (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _, fun _ _ => rfl⟩
  · obtain ⟨p, h⟩ := _root_.GlobalTheory.ThK.Dbl.Hgt.iwasawa2_k hB hY x
    exact ⟨p, leviOf _ _ p, isPar_iff.2 ⟨mem_siegelOf.1 p.2, rfl⟩, h⟩
  · obtain ⟨h1, h2⟩ := isPar_iff.1 hp
    have := hI.hgtOf_mul ⟨p, mem_siegelOf.2 h1⟩ hk
    rw [show t = leviOf (Equiv.refl _) (UG (cA σ) (dbl (incM F Y.J))).subtype ⟨p, mem_siegelOf.2 h1⟩ from Units.ext h2.symm]
    exact congrArg NNReal.toReal this
end GlobalTheory.ThK.Dbl.Hgt
end
end
end
