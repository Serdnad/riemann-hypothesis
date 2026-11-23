module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle051
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle064
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle053
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle048
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousInsK
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle001
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
theorem isClosed_nA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsClosed (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have e : (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) =
      {β | βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ))} := Set.ext fun β => kunf.mem_nA_iff hε β
  rw [e]
  exact isClosed_eq continuous_id.matrix_transpose (((continuous_id.matrix_map hc).const_smul (((ε : ℤ) : AE F E))).neg)
instance locCompact_nA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : LocallyCompactSpace (nA σ d.Y d.b) :=
  haveI : LocallyCompactSpace (Matrix (Fin d.n) (Fin d.n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d.n → Fin d.n → AE F E))
  (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.isClosed_nA_k d).isClosedEmbedding_subtypeVal.locallyCompactSpace
theorem coef_periodic_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb) (φ : d.G → ℂ)
    (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) (β₀ : nF σ d.Y d.b)
    (β : nA σ d.Y d.b) :
    φ (nb (β₀ +ᵥ β) * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * (β₀ +ᵥ β).1)))) =
      φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) := by
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add hN, mul_assoc, hφ _ (kunf.nb_rat hN β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
theorem cj_mp_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) {v : Fin L.n → AE F E} (hv : v ∈ L.ratV) :
    MeasurePreserving (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 v) lam lam := by
  letI hLamHaar : lam.IsAddHaarMeasure := h.2.1
  refine ⟨(_root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU h.1 v).measurable, ?_⟩
  have hl := latHaar (nA σ d.Y d.b) lam (nF σ d.Y d.b) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 v) (fun x => ⟨fun hx => ?_, fun hx => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 hv hx⟩)
    𝓖 h.2.2.1 (fun hz => one_ne_zero (h.2.2.2.symm.trans hz))
      (fun ht => ENNReal.one_ne_top (h.2.2.2.symm.trans ht))
  · exact hl
  · have := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 (neg_mem hv) hx
    rwa [show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-v) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 v x) = x from _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 v x] at this
theorem fc_conj_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * g) = fc d.B.ψ d.b nb lam 𝓖 φ T g := by
  letI hLamHaar : lam.IsAddHaarMeasure := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  let H : nA σ d.Y d.b → ℂ := fun β =>
    φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have e1 : ∀ β, φ (nb β * (uM u * g)) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      H (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u β) := by
    intro β
    have e : nb β * (uM u * g) = uM u * (nb (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u β) * g) := by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.nb_cj_k hU h.1 u β]; group
    simp only [H]
    rw [e, hφ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_rat_k hU hu), _root_.PositivityTheory.SiegelWeilFormula.Act.C1.trace_cj_k hU h.1 hT]
  have hme : MeasurableEmbedding (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u) := (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 u).toHomeomorph.measurableEmbedding
  have himg : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u) '' 𝓖 = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u)) ⁻¹' 𝓖 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u x) ∈ 𝓖
      rwa [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k]
    · intro hy
      refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) y, hy, ?_⟩
      simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 (-u) y
  have hfd : IsAddFundamentalDomain (nF σ d.Y d.b) ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u)) ⁻¹' 𝓖) lam := by
    refine h.2.2.1.preimage_of_equiv (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mp_k h hU (neg_mem hu)).quasiMeasurePreserving
      (e := fun γ => ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u γ.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 hu γ.2⟩) ⟨fun γ γ' hγ => ?_, fun γ => ?_⟩ fun γ x => ?_
    · have := congrArg (fun y : nF σ d.Y d.b => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) y.1) hγ
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k] at this
      exact Subtype.ext this
    · refine ⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) γ.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 (neg_mem hu) γ.2⟩, Subtype.ext ?_⟩
      simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 (-u) γ.1
    · show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u γ.1) + x) = γ.1 + _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) x
      rw [map_add (f := _), _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k]
  unfold fc
  simp_rw [e1]
  refine ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mp_k h hU hu).setIntegral_image_emb hme H 𝓖).symm.trans ?_
  rw [himg]
  exact hfd.setIntegral_eq h.2.2.1 (fun β₀ β => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.coef_periodic_k d h.1 φ hφ T g β₀ β)
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem pEquiv_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b),
      (∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) ∧
      ∀ β, β ∈ nF σ d.Y d.b ↔ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β ∈ L.ratV ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β ∈ fA F) ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β ∈ nF σ L.Y L.b := by
  obtain ⟨P, h1, h2⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pEquiv0_k L h.δ0 ⟨cM (0, 1), by
    obtain ⟨A', hA'⟩ := h.cf (0, 1)
    refine ⟨A', ?_⟩
    rw [hA']
    have hu : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (0 : Fin L.n → AE F E) = 1 := by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k]
    rw [hu]⟩
  exact ⟨P, h1, h2⟩
theorem lam_map_k {lam : Measure (nA σ d.Y d.b)} [lam.IsAddHaarMeasure] {ν : Measure (Fin L.n → AE F E)} [ν.IsAddHaarMeasure]
    {lam' : Measure (nA σ L.Y L.b)} [lam'.IsAddHaarMeasure] (P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ lam.map P = c • ((ν.prod (lamA F)).prod lam') := by
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  haveI : (lam.map P).IsAddHaarMeasure := P.isAddHaarMeasure_map lam
  haveI : SFinite ν := inferInstance
  haveI : SFinite lam' := inferInstance
  haveI : SFinite (lamA F) := inferInstance
  haveI : (ν.prod (lamA F)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  haveI : SFinite (ν.prod (lamA F)) := inferInstance
  haveI : ((ν.prod (lamA F)).prod lam').IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(Measure.addHaarScalarFactor (lam.map P) ((ν.prod (lamA F)).prod lam') : ℝ≥0∞),
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top, ?_⟩
  rw [← ENNReal.smul_def]
  exact Measure.isAddLeftInvariant_eq_smul _ _
theorem kap_eq_k {ν : Measure (Fin L.n → AE F E)} [ν.IsAddHaarMeasure] {κ : Measure ((Fin L.n → AE F E) × AF F)}
    [κ.IsAddHaarMeasure] : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ κ = c • (ν.prod (lamA F)) := by
  haveI : SFinite ν := inferInstance
  haveI : SFinite (lamA F) := inferInstance
  haveI : (ν.prod (lamA F)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(Measure.addHaarScalarFactor κ (ν.prod (lamA F)) : ℝ≥0∞),
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top, ?_⟩
  rw [← ENNReal.smul_def]
  exact Measure.isAddLeftInvariant_eq_smul _ _
end PositivityTheory.SiegelWeilFormula.Act.C5
namespace PositivityTheory.SiegelWeilFormula.Act.C5
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
