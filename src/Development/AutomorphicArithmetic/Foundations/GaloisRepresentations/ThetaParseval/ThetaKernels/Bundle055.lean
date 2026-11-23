module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle040
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.BddOfPer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle038
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem bdd_of_per_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {U : nA σ d.Y d.b × d.G → ℂ} (hU : Continuous U)
    (hper : ∀ β, ∀ l ∈ nF σ d.Y d.b, ∀ y, U (β + l, y) = U (β, y)) {C : Set d.G} (hC : IsCompact C) :
    ∃ M, ∀ β, ∀ y ∈ C, ‖U (β, y)‖ ≤ M := by
  obtain ⟨K, hK, hKβ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSing.nCocompact_k d
  obtain ⟨M, hM⟩ := (hK.prod hC).exists_bound_of_continuousOn hU.continuousOn
  refine ⟨M, fun β y hy => ?_⟩
  obtain ⟨l, hl, hβl⟩ := hKβ β
  have e := hper (β - l) l hl y
  rw [sub_add_cancel] at e
  rw [e]
  exact hM _ ⟨hβl, hy⟩

theorem fc_avg_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (hG : IsTopologicalGroup d.G)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hCD : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (f : d.G → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g)
    (ψ₀ : (Fin d.n → Fin d.n → ℝ) → ℂ) (hψc : Continuous ψ₀) (hψs : HasCompactSupport ψ₀)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x))
    (β : (Fin d.n → Fin d.n → ℝ) → nA σ d.Y d.b) (hβc : Continuous β) (hβ : ∀ x, R.ι w (nr x) = nb (β x))
    (T : nF σ d.Y d.b) (z : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (fun y => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z =
      fc d.B.ψ d.b nb lam 𝓖 f T z * ∫ x, ψ₀ x * d.B.ψ (d.tt (T.1.1 * (β x).1)) := by
  have := hG
  set χ : nA σ d.Y d.b → ℂ := fun β₀ => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β₀.1))))
    with hχ
  set U : nA σ d.Y d.b × d.G → ℂ := fun p => f (nb p.1 * p.2) * χ p.1 with hUdef
  have hnbc := _root_.PositivityTheory.SiegelWeilFormula.KSing.continuous_nb_k d hCD.1
  have hnrc := cont_nr nr hnr
  have hιr : Continuous fun x => R.ι w (nr x) * z := ((R.cont w).comp hnrc).mul continuous_const
  have hUc : Continuous U :=
    (hf.comp ((hnbc.comp continuous_fst).mul continuous_snd)).mul ((_root_.PositivityTheory.SiegelWeilFormula.KSing.chi_cont_k d T).comp continuous_fst)
  have hUper : ∀ β₀, ∀ l ∈ nF σ d.Y d.b, ∀ y, U (β₀ + l, y) = U (β₀, y) := by
    intro β₀ l hl y
    simp only [hUdef, hχ]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.chi_add_k d T β₀ l, _root_.PositivityTheory.SiegelWeilFormula.KSing.chi_per_k d T hl, mul_one, add_comm, _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hCD.1, mul_assoc, hinv _ (_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_rat_k d hCD.1 hl)]
  obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSing.bdd_of_per_k d hUc hUper ((hψs.isCompact).image hιr)
  haveI : IsFiniteMeasure (lam.restrict 𝓖) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact hCD.2.2.2.trans_lt ENNReal.one_lt_top⟩
  have e1 : ∀ β₀ x, f (R.ι w (nr x) * (nb β₀ * z)) * ψ₀ x * χ β₀ = U (β₀, R.ι w (nr x) * z) * ψ₀ x := by
    intro β₀ x
    simp only [hUdef]
    rw [hβ x, ← mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hCD.1, add_comm, _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hCD.1,
      show nb β₀ * nb (β x) * z = nb β₀ * (nb (β x) * z) from mul_assoc _ _ _]
    ring
  have eL : fc d.B.ψ d.b nb lam 𝓖 (fun y => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z =
      ∫ β₀, ∫ x, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂volume ∂(lam.restrict 𝓖) := by
    unfold fc
    congr 1
    funext β₀
    rw [← integral_mul_const]
    congr 1
    funext x
    exact e1 β₀ x
  have hcont : Continuous (Function.uncurry fun (β₀ : nA σ d.Y d.b) (x : Fin d.n → Fin d.n → ℝ) =>
      U (β₀, R.ι w (nr x) * z) * ψ₀ x) :=
    (hUc.comp (continuous_fst.prodMk (hιr.comp continuous_snd))).mul (hψc.comp continuous_snd)
  have hint : Integrable (Function.uncurry fun (β₀ : nA σ d.Y d.b) (x : Fin d.n → Fin d.n → ℝ) =>
      U (β₀, R.ι w (nr x) * z) * ψ₀ x) ((lam.restrict 𝓖).prod volume) := by
    refine Integrable.mono' ((integrable_const M).mul_prod (hψc.norm.integrable_of_hasCompactSupport hψs.norm))
      (_root_.PositivityTheory.SiegelWeilFormula.KSing.aesm_of_continuous_k d hCD hcont) (Eventually.of_forall fun p => ?_)
    show ‖U (p.1, R.ι w (nr p.2) * z) * ψ₀ p.2‖ ≤ M * ‖ψ₀ p.2‖
    rw [norm_mul]
    by_cases hx : p.2 ∈ tsupport ψ₀
    · exact mul_le_mul_of_nonneg_right (hM p.1 _ ⟨p.2, hx, rfl⟩) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [eL, integral_integral_swap hint]
  have e2 : ∀ x, ∫ β₀, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂(lam.restrict 𝓖) =
      fc d.B.ψ d.b nb lam 𝓖 f T z * (ψ₀ x * d.B.ψ (d.tt (T.1.1 * (β x).1))) := by
    intro x
    rw [integral_mul_const]
    have : ∫ β₀, U (β₀, R.ι w (nr x) * z) ∂(lam.restrict 𝓖) = fc d.B.ψ d.b nb lam 𝓖 f T (nb (β x) * z) := by
      rw [hβ x]
      rfl
    rw [this, _root_.PositivityTheory.SiegelWeilFormula.KSing.fc_shift_k d hCD f hinv T (β x) z]
    ring
  simp_rw [e2]
  rw [integral_const_mul]
end PositivityTheory.SiegelWeilFormula.KSing
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem phz_leftInv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ d.Y ⊓ rat2 σ d.Y) (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
  intro p hp g
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 hp.1
  obtain ⟨T, hT⟩ := par_rat ht hp.2
  obtain ⟨u, hu⟩ := det_rat hT
  have ha : d.a (p * g) = d.a g := by
    rw [IsHgt.mul d.ok.hgt ht, hu, GlobalTheory.Doubling.absE_inclR]; simp
  have hfp : f (p * g) = f g := Law.rat (z := s₁ + (d.n : ℂ) / 2) hf.law d.ok.hecke hp.1 hp.2 g
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, ha, hfp]
theorem eis_leftInv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    ∀ γ ∈ rat2 σ d.Y, ∀ g, d.eis f s₁ z (γ * g) = d.eis f s₁ z g :=
  GlobalTheory.Eis.leftInv_cosetSum (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.phz_leftInv_k d hf z)
theorem fc_dom_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 𝓖₀ : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (h₀ : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀)
    (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T g = fc d.B.ψ d.b nb lam 𝓖₀ φ T g := by
  unfold fc
  letI : lam.IsAddHaarMeasure := h.2.1
  have hinv : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  refine @MeasureTheory.IsAddFundamentalDomain.setIntegral_eq _ _ ℂ _ _ _ _ _ _ lam _ hinv _ _
    h.2.2.1 h₀.2.2.1 _ (fun β₀ β => ?_)
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add h.1, mul_assoc, hφ _ (kunf.nb_rat h.1 β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end
