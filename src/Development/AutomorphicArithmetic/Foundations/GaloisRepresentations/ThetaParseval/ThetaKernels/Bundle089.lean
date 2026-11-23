module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle080
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle034
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle086
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle083
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ExistsSchwartzOneCpt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle077
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle087
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle050
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle078
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeylEmbeddedColumns
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HandsCoordkTau
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle048
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle065
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinTermLeftInvariant
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle071
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle076
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle064
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.CountableProdSub
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.VaddInvBotProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Real.Pi.Irrational
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



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem line_data_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k)
    (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ (k : d.G) (ω χ C : ℂ) (c : ℝ) (ν : Measure (Mx F E d.m d.n)) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d))
      (vv : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)),
      k ∈ d.K ∧ ‖ω‖ = 1 ∧ (∀ j : ℕ, 0 < j → ω ^ j ≠ 1) ∧ χ ≠ 0 ∧ C ≠ 0 ∧ ν.IsAddHaarMeasure ∧
      νf.IsAddHaarMeasure ∧
      (∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → d.om k Ω = χ • Ω) ∧
      (∀ ξ z, actB (cA σ) k (vv ξ z) = vv ξ (ω * z)) ∧
      ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → ∀ Φ ∈ d.sch, ∀ ξ z,
        _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (vv ξ z) Ω) = C * Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) *
          (Complex.exp (-(z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi))) *
            ∫ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ)) := by
  obtain ⟨C, c, s, ν, νf, hC, hs, hν, hνf, hB⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.B_vline_k hT hU hH hA hF R
  obtain ⟨χ, hχ, heig⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.om_rot_vac'_k hT hLO hLI R 1
  let W : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → Mx F E d.m d.n := fun ξ => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R (s⁻¹ • ξ) 0
  have hW : ∀ ξ, finOne F • W ξ = 0 := fun ξ => (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_eq_zero_iff_k _).1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R _ _)
  have hsW : ∀ ξ, s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (W ξ) = ξ := fun ξ => by
    simp only [W, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k, smul_smul, mul_inv_cancel₀ hs, one_smul]
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R 1, Complex.exp (-((1 : ℝ) * Complex.I)), χ, C, c, ν, νf, fun ξ z => _root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R (W ξ) z, _root_.PositivityTheory.SiegelWeilFormula.KFP.rot_mem_k R 1,
    ?_, ?_, hχ, hC, hν, hνf, heig, fun ξ z => _root_.PositivityTheory.SiegelWeilFormula.KFP.actB_rot_vline'_k R 1 (hW ξ) z, fun g hg Ω hΩ hTΩ Φ hΦ ξ z => ?_⟩
  · rw [Complex.norm_exp]
    simp
  · intro j hj h
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    have h3 : -(j : ℝ) = 2 * Real.pi * k := by
      have := congrArg Complex.im hk
      simp at this
      linarith
    have hk0 : (k : ℝ) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, neg_eq_zero] at h3
      exact (Nat.cast_pos.2 hj).ne' h3
    refine irrational_pi ⟨-(j : ℚ) / (2 * k), ?_⟩
    push_cast
    field_simp
    linarith
  · have := hB g hg Ω hΩ hTΩ Φ hΦ (W ξ) (hW ξ) z
    rwa [hsW] at this
theorem B_rel_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) {ν : Measure (Mx F E d.m d.n)} (hν : ν.IsAddHaarMeasure) {k : d.G} {χ : ℂ}
    (hχ : χ ≠ 0) {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hk : d.om k Ω = χ • Ω) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (q : Polynomial ℂ)
    (hq : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0)
    (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = 0 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.B_rel'_k hT hU hν hχ hΩ hk hΦ q hq v
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section



section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelEx_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k := _root_.PositivityTheory.SiegelWeilFormula.Ald.modelExists_of_siegelSmall (_root_.PositivityTheory.SiegelWeilFormula.Ald.siegelSmall_of_slice_k sliceFacts)
end PositivityTheory.SiegelWeilFormula.Ald
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
open PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem inj_core_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {p : d.G} (hp : p ∈ par2 σ d.Y) (hpr : p ∈ rat2 σ d.Y) {c c' : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L}
    {γ' γ'' : G2 σ L.Y} (h' : γ' ∈ rat2 σ L.Y) (h'' : γ'' ∈ rat2 σ L.Y)
    (e : p * (w₁ * (cM c.1 * L.j γ')) = w₁ * (cM c'.1 * L.j γ'')) :
    γ'' * γ'⁻¹ ∈ par2 σ L.Y ∧ (γ'' = γ' → c = c') :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.inj_core_k h hp hpr h' h'' e
theorem conj_par_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {p' : G2 σ L.Y} (hp : p' ∈ par2 σ L.Y) (hpr : p' ∈ rat2 σ L.Y) (c : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ c₂ : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L, w₁ * (cM c.1 * L.j p') = p * (w₁ * cM c₂.1) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C6.conj_rationalParabolic_embed h hp hpr c
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section



section
set_option linter.unusedSectionVars false
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem fix_mul_k {x y : d.G}
    (hx : ∀ k, inFrame d.b x k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (hy : ∀ k, inFrame d.b y k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (k) : inFrame d.b (x * y) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp only [hy]
  rw [← Matrix.mul_apply, Matrix.mul_one, hx]
theorem perF_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T (γ + β) = Ψ (nb β * (uM u * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc, hΨ _ (kunf.nb_rat h.nb hγ) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_nb_k h γ)]
  congr 1
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]
theorem perFE_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (Ψ : d.G → ℝ≥0∞) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T (γ + β)‖ₑ = Ψ (nb β * (uM u * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β‖ₑ := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc, hΨ _ (kunf.nb_rat h.nb hγ) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_nb_k h γ)]
  congr 2
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]
theorem shift_eq_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (r b u : Fin L.n → AE F E) (s a : AF F) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (r + b) * cM (u, s + a) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L r * cM (0, s)) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) := by
  have e1 : cM (u, s + a) = cM (0, s) * cM (u, a) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_split_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.centre_additive h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_split_k h u a, ← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_comm_k h, mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_add_k, e1]
  simp only [mul_assoc]
  rw [← mul_assoc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b) (cM (0, s)), _root_.PositivityTheory.SiegelWeilFormula.Act.C5.unipotent_commutes_centre h, mul_assoc]
theorem rr_rat_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {r : Fin L.n → AE F E} (hr : r ∈ L.ratV) {s : AF F}
    (hs : s ∈ (algebraMap F (AF F)).range) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L r * cM (0, s) ∈ rat2 σ d.Y :=
  mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_rat_k hr) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_rat_k h (c := (0, s)) (zero_mem _) hs)
theorem rr_fix_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (r : Fin L.n → AE F E) (s : AF F) (k) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L r * cM (0, s)) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.fix_mul_k (L := L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_sM_k r) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_cM_k h (0, s)) k
theorem pt_eq_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (x : d.G) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb β * (uM u * x) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).1) *
      (cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).2) * (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x)) := by
  calc nb β * (uM u * x) = (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β) * cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β))) * x := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.nb_split_k (R := R) h β]
        simp only [mul_assoc]
        rw [← mul_assoc (cM (0, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β)) (uM u), ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_comm_k h, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_split_k h]
    _ = _ := by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.move_k h]; simp only [mul_assoc]
instance countable_ratV_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Countable L.ratV := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have h : ((L.ratV : AddSubgroup (Fin L.n → AE F E)) : Set (Fin L.n → AE F E)).Countable := by
    refine (Set.countable_range (GlobalTheory.ThK.incV F : (Fin L.n → E) → _)).mono fun u hu => ?_
    obtain ⟨v, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k hu
    exact ⟨v, rfl⟩
  exact h.to_subtype
theorem coordsC_ck_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫ p, Ψ (nb p.2 * (uM p.1 * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c.toReal • ∫ p, Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' p.1
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  haveI : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  letI : lam.IsAddHaarMeasure := hc.2.1
  letI : lam'.IsAddHaarMeasure := hc'.2.1
  haveI := hU.2.1
  letI : SigmaFinite lam := Measure.IsAddHaarMeasure.sigmaFinite lam
  letI : SigmaFinite lam' := Measure.IsAddHaarMeasure.sigmaFinite lam'
  obtain ⟨-, -, hiff⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pEquiv_k h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainC (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_tau_k h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2)
    (fun q => Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L q.2.2.1 * (cM (q.2.1, q.2.2.2) * (L.j (nb' q.1) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' q.1)
    (fun γ hγ u β => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.perF_k h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (g.1 + b) * (cM (u, g.2 + a) * _)) * _ = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.shift_eq_k h, mul_assoc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L g.1 * cM (0, g.2)), hΨ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_rat_k h hg1 hg2) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_fix_k h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).1) *
        (cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).2) * (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.pt_eq_k (R := R) h x u β]
      congr 1
      unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.tr_sub_k L hT β])
  rw [key, ← Measure.prod_restrict]
theorem coordsE_ck_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℝ≥0∞) (hΨm : Measurable Ψ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫⁻ p, Ψ (nb p.2 * (uM p.1 * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c * ∫⁻ p, Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' p.1‖ₑ
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  haveI : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  letI : lam.IsAddHaarMeasure := hc.2.1
  letI : lam'.IsAddHaarMeasure := hc'.2.1
  haveI := hU.2.1
  letI : SigmaFinite lam := Measure.IsAddHaarMeasure.sigmaFinite lam
  letI : SigmaFinite lam' := Measure.IsAddHaarMeasure.sigmaFinite lam'
  obtain ⟨-, -, hiff⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pEquiv_k h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainE (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_tau_k h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ)
    (fun q => Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L q.2.2.1 * (cM (q.2.1, q.2.2.2) * (L.j (nb' q.1) * x))) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' q.1‖ₑ)
    (fun γ hγ u β => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.perFE_k h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (g.1 + b) * (cM (u, g.2 + a) * _)) * _ = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.shift_eq_k h, mul_assoc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L g.1 * cM (0, g.2)), hΨ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_rat_k h hg1 hg2) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_fix_k h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β‖ₑ = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).1) *
        (cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).2) * (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x))) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)‖ₑ
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.pt_eq_k (R := R) h x u β]
      congr 2
      unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.tr_sub_k L hT β])
  rw [key, ← Measure.prod_restrict]
end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
end
end
end
