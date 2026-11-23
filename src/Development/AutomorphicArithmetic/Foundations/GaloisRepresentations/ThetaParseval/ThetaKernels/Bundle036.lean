module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.BlockTriangularFrames.SiegelParabolicEqStabiliserCols
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle015
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle026
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.CmbVCrdV
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle027
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.BasisReprMap
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace COneB
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def Nu_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := ∑ j, Matrix.single L.i₀ (L.em j) (u j)
theorem em_ne_k (j : Fin L.n) : L.em j ≠ L.i₀ := (L.rng (L.em j)).2 ⟨j, rfl⟩
theorem Nu_mul_k (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u * _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L v = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  apply Matrix.single_mul_single_of_ne
  exact _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.em_ne_k L _
theorem Nu_add_k (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L (u + v) = _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L v := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]
theorem Nu_cont_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L) := by
  have e : _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L = fun u => ∑ j, u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext u; simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
omit L in
theorem unit_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : ∃ e : AE F E,
    (inFrame d.b x)ᵀ * Matrix.fromBlocks 0 1 (e • 1) 0 * (inFrame d.b x).map (cA σ) = Matrix.fromBlocks 0 1 (e • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨((ε : ℤ) : AE F E), ?_⟩
  have hF := kfour.frameEq_adelic (F := F) (Y := d.Y) hε
  have hU : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b x] at hU
  have h1 : (incM F d.b.1)ᵀ * (incM F (d.b⁻¹).1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.transpose_one]
  have h2 : (incM F (d.b⁻¹).1).map (cA σ) * (incM F d.b.1).map (cA σ) = 1 := by
    rw [← SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← hF]
  conv_rhs => rw [← hU]
  rw [SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one, ← Matrix.mul_assoc (incM F d.b.1)ᵀ (incM F (d.b⁻¹).1)ᵀ, h1, Matrix.one_mul]
omit L in
theorem blk_unit_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (a a' : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a 0 0 a') : aᵀ * a'.map (cA σ) = 1 := by
  obtain ⟨e, he⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.unit_frame_k d x
  rw [hx] at he
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero _), Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one] at he
  have := (Matrix.fromBlocks_inj.1 he).2.1
  exact this
omit L in
theorem cA_cA_mat_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {p q : Type} (M : Matrix p q (AE F E)) : (M.map (cA σ)).map (cA σ) = M := by
  have hσ : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  ext i j; simp [kfour.cA_cA' σ hσ]
theorem uM_frame_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u) 0 0 (((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ).map (cA σ)) := by
  obtain ⟨a', ha'⟩ := hu.1 u
  have ha : inFrame d.b (uM u) = Matrix.fromBlocks (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u) 0 0 a' := ha'
  rw [ha]
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.blk_unit_k d _ _ _ ha
  have h2 : (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ * (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_mul_k, sub_zero,
      sub_add_cancel, Matrix.transpose_one]
  have h3 : a'.map (cA σ) = (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ * (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ) * a'.map (cA σ) := by rw [h2, Matrix.one_mul]
      _ = (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ * ((1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ * a'.map (cA σ)) := by rw [Matrix.mul_assoc]
      _ = (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ := by rw [h1, Matrix.mul_one]
  have h4 : a' = ((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ).map (cA σ) := by rw [← h3, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.cA_cA_mat_k d]
  rw [h4]
theorem uM_add_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  apply kfour.inFrame_injective d.b
  rw [SiegelEisensteinSeries.Grp.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_frame_k L hu, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_frame_k L hu, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_frame_k L hu, Matrix.fromBlocks_multiply]
  have e1 : (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u) * (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L v) = 1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L (u + v) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_add_k, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_mul_k, add_zero]
    abel
  have e2 : ((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ).map (cA σ) * ((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L v)ᵀ).map (cA σ) = ((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L (u + v))ᵀ).map (cA σ) := by
    have hm := Matrix.map_mul (L := (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ) (M := (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L v)ᵀ) (f := (cA σ).toRingHom)
    erw [← hm]
    rw [← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_add_k, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_mul_k,
      sub_zero]
    congr 2
    abel
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e2]
theorem uM_zero_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : uM 0 = 1 := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_add_k L hu 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)
theorem uM_neg_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (uM u)⁻¹ = uM (-u) := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_add_k L hu (-u) u
  rw [neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_zero_k L hu] at h
  exact (eq_inv_of_mul_eq_one_left h.symm).symm
theorem uM_cont_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : Continuous uM := by
  have hcA : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  have hmat : Continuous fun u => mat2 (uM u) := by
    have e : (fun u => mat2 (uM u)) = fun u => incM F d.b.1 * Matrix.fromBlocks (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u) 0 0
        (((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ).map (cA σ)) * incM F (d.b⁻¹).1 := by
      funext u; rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_frame_k L hu]
    rw [e]
    refine (continuous_const.matrix_mul (Continuous.matrix_fromBlocks (continuous_const.add (_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_cont_k L))
      continuous_const continuous_const ?_)).matrix_mul continuous_const
    exact ((continuous_const.sub (_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_cont_k L)).matrix_transpose).matrix_map hcA
  have hinv : Continuous fun u => mat2 (uM u)⁻¹ := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_neg_k L hu]
    exact hmat.comp continuous_neg
  refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
  exact Units.continuous_iff.2 ⟨hmat, hinv⟩
theorem ratV_cocompact_k : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ u, ∃ r ∈ L.ratV, r + u ∈ K := by
  obtain ⟨C, hC, hCx⟩ := kfour.exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi (fun _ => C), isCompact_univ_pi (fun _ => hC), fun u => ?_⟩
  choose x hx using fun j => hCx (u j)
  refine ⟨GlobalTheory.ThK.incV F x, AddSubgroup.subset_closure ⟨x, rfl⟩, fun j _ => ?_⟩
  simpa [GlobalTheory.ThK.incV] using hx j
end COneB
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eisValue_of_k (hBL : _root_.GlobalTheory.ThK.Dbl.EisBL_k) (hSec : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {r' s' : ℕ}
    (hY : d.Y.IsHerm σ d.B r' s' ∨ d.Y.IsSkew σ d.B r' s') (c : ℂ) (hM : _root_.PositivityTheory.SiegelWeilFormula.MainC_k c d) (Φ : d.Fn) (hK : d.KFin Φ) :
    EisValueAt (_root_.GlobalTheory.ThK.Dbl.flat d.a (d.sec0 Φ) (s0 d.m d.n)) (s0 d.m d.n) (fun x => c * d.I Φ x) := by
  obtain ⟨Ê, ⟨t, hsum, -⟩, hw⟩ := hBL F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.χ d.ok.hecke d.m d.ok.res d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt (s0 d.m d.n) (d.sec0 Φ) (hSec F E σ d Φ hK)
  intro x
  have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ y) = _root_.GlobalTheory.ThK.Dbl.flat d.a (d.sec0 Φ) (s0 d.m d.n) z :=
    fun z => funext fun y => by
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, _root_.GlobalTheory.ThK.Dbl.flat]
      rw [Real.coe_toNNReal _ (Khead.hgt_nonneg d.ok.hgt y)]
  have Heisenberg₂ : ∀ z : ℂ, t < z.re → d.eis (d.sec0 Φ) (s0 d.m d.n) z x = Ê z x := fun z hz => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.eis]
    rw [hfl z]
    exact (hsum z hz x).tsum_eq
  have hmer := Khead.meromorphicOn_of_weak hw x
  have hext : IsExtAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (Ê · x) :=
    ⟨Set.univ, trivial, isRightDomain_univ, hmer, t, fun z hz => (Heisenberg₂ z hz).symm⟩
  obtain ⟨H', hext', han, hval⟩ := hM Φ hK x
  have hev := hext'.eventuallyEq hext
  have hloc : Function.update (Ê · x) (s0 d.m d.n) (c * d.I Φ x) =ᶠ[𝓝 (s0 d.m d.n)] H' := by
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with z hz
    by_cases e : z = s0 d.m d.n
    · subst e; rw [Function.update_self]; exact hval.symm
    · rw [Function.update_of_ne e]; exact (hz e).symm
  refine ⟨Function.update (Ê · x) (s0 d.m d.n) (c * d.I Φ x), fun z _ => (hmer z trivial).update _ _,
    ⟨max t (s0 d.m d.n).re, fun z hz => ?_⟩, han.congr hloc.symm, Function.update_self _ _ _⟩
  have hz1 : t < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hz2 : z ≠ s0 d.m d.n := fun e => by subst e; exact lt_irrefl _ (lt_of_le_of_lt (le_max_right _ _) hz)
  rw [Function.update_of_ne hz2]
  exact hsum z hz1 x
end PositivityTheory.SiegelWeilFormula.Atop
namespace PositivityTheory.SiegelWeilFormula
theorem Atop.fieldOf_k : _root_.PositivityTheory.SiegelWeilFormula.FieldOf_k := by
  intro hBL hSec hLt hLe F E _ _ _ _ _ σ B m n A Y r s r' s' h1 h2 h3 h4 h5 χ h6 h7 κ _ dd om S l h8 b K a h9 h10 h11 μ D
    h12 h13 Φ h14 h15
  by_cases hlt : n < m
  · exact _root_.PositivityTheory.SiegelWeilFormula.Khead.siegelWeilStd_lt_k hLt F E σ B m n A Y r s r' s' hlt h1 h2 h3 h4 h5 χ h6 h7 κ dd om S l h8 b K a h9 h10 h11
      μ D h12 h13 Φ h14 h15
  · simp only [if_neg hlt]
    let d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ :=
      { B := B, m := m, n := n, A := A, Y := Y, r := r, s := s, χ := χ, κ := κ, dd := dd, om := om, S := S, l := l, b := b,
        K := K, a := a, μ := μ, D := D, bs := _root_.PositivityTheory.SiegelWeilFormula.Khead.basis2_k h1,
        ok := ⟨h1, h2, h3, h4, h5.imp (fun h => ⟨h.1, h.2.skew⟩) (fun h => ⟨h.1, h.2.herm⟩), h6, h7, h8, h9, h10, h11, h12,
          h13⟩ }
    have hY : d.Y.IsHerm σ d.B r' s' ∨ d.Y.IsSkew σ d.B r' s' := h5.elim (fun h => .inr h.2) (fun h => .inl h.2)
    exact _root_.PositivityTheory.SiegelWeilFormula.Atop.eisValue_of_k hBL hSec d hY 2 (hLe F E σ d (not_lt.mp hlt)) Φ ⟨h14, h15⟩
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA PositivityTheory.SiegelWeilFormula.ThetaDictR.PureC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem pure_prod_of'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf)
    (u : GL (Fin d.n) (AE F E)) (η : E)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star)
    (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1)
    (l : InfinitePlace F → ℝ) (hl : ∀ w, |l w| = 1) :
    ∃ (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ),
      HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧
      HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin (fun Y => d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ))
        (Gen.phiInf θ l fr g P) Φf := by
  obtain ⟨hloc, hcof, hT⟩ := hP
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ :=
    fun v Y => gf v (crdV d.bs v (toMxV v Y * Av u v))
  refine ⟨fun X => ∏ᶠ v, Φv v (HeckeCharacterZeroLocus.SiegelWeilU.projV v X), Φv,
    ⟨fun v => isSB_comp d.bs u v (gf v) (hloc v), ?_, fun X => rfl⟩, ?_⟩
  · filter_upwards [hcof, int_iff (m := d.m) d.bs u] with v hv hint
    funext Y
    show gf v _ = _
    rw [hv]
    by_cases h : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV d.bs v
    · rw [Set.indicator_of_mem h]
      refine (Set.indicator_of_mem ?_ _).trans rfl
      exact (hint Y).2 h
    · rw [Set.indicator_of_notMem h]
      refine Set.indicator_of_notMem ?_ _
      intro h'
      exact h ((hint Y).1 h')
  · intro X
    dsimp only
    rw [hT]
    dsimp only
    congr 1
    · unfold Gen.phiInf
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB.crd_eq_k R u η θ th fr frc g gc w X, hl w, mul_one]
      rfl
    · refine finprod_congr fun v => ?_
      congr 1
      funext k
      have hZ : (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map (mapV v) =
          toMxV v (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X)) * Av u v := by
        rw [map_mul_alg]
        congr 1
        ext a j
        simp only [Matrix.map_apply, toMx, toMxV, Matrix.of_apply, HeckeCharacterZeroLocus.SiegelWeilU.projV, HeckeCharacterZeroLocus.SiegelWeilU.projFin,
          mapV_eq]
      have h1 : HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) k).2 =
          phiV v (d.crd (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) k) := rfl
      rw [h1, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, ← basis_repr_map']
      simp only [crdV]
      rw [← hZ]
      rfl
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def WhitAtC_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) (x : d.G) : Prop :=
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T →
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (c * d.orb T (d.om x Φ))
theorem asc_whitAt_iff_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k c d Φ ↔ ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x := by
  constructor
  · intro h x nb lam 𝓖 hc ε w hw T hT
    exact h nb lam 𝓖 hc ε w hw T hT x
  · intro h nb lam 𝓖 hc ε w hw T hT x
    exact h x nb lam 𝓖 hc ε w hw T hT
def IwaRedC_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → ∀ (c : ℂ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Q : d.Fn → Prop), (∀ Φ, Q Φ → Φ ∈ d.sch) → (∀ Φ, Q Φ → ∀ k ∈ d.K, Q (d.om k Φ)) →
    (∀ Φ, Q Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x) → ∀ Φ, Q Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x
def LinRedC_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k → _root_.PositivityTheory.SiegelWeilFormula.LamBd_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → ∀ (c : ℂ) (F E : Type) [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.EisAll → ∀ (k : ℕ) (cs : Fin k → ℂ)
    (Φs : Fin k → d.Fn), (∀ i, d.KFin (Φs i)) → ∀ x, (∀ i, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d (Φs i) x) → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d (∑ i, cs i • Φs i) x
def VacSpan_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.VacK_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac →
    ∃ (k : ℕ) (cs : Fin k → ℂ) (Φs : Fin k → d.Fn),
      (∀ i, d.KFin (Φs i) ∧ d.T (Φs i) ∈ R.vac ∧ ∃ gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R (Φs i) (fun _ => 1) gf) ∧ Φ = ∑ i, cs i • Φs i
def GenDictX_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → ∀ P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T →
  ∃ (dd : ℕ) (J : Matrix (Fin d.m) (Fin d.m) E) (T' : Matrix (Fin d.n) (Fin d.n) E) (bs : Module.Basis (Fin dd) F E)
    (ψ : AddChar (AF F) ℂ) (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (l : InfinitePlace F → ℝ)
    (εs : InfinitePlace F → Fin d.m → Bool) (fr : InfinitePlace F → GL (Fin d.m) ℂ) (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (lv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (ν : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)) (c : ℂ) (C : ℝ),
    Gen.Dat0 σ J T' bs ψ θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ J y y = 0 → y = 0) ∧ (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    0 < C ∧
    (∃ t : ℝ, ∀ z : ℂ, t < z.re →
      (Integrable (fun β => flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x)) lam →
        Integrable (Gen.whI (AF F) σ J ψ μ Φg (Gen.nuA θ g lv L₁ L₂) (T'.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z) ν) ∧
      ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
        c * (C : ℂ) ^ (z - s0 d.m d.n) *
          ∫ b, Gen.whI (AF F) σ J ψ μ Φg (Gen.nuA θ g lv L₁ L₂) (T'.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z b ∂ν) ∧
    ∃ μH 𝓕, HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m J μH ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m J μH 𝓕 ∧
      d.orb T (d.om x Φ) = c * HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕
        (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ d.m J Φg {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T'})
def CorePure_k (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ) : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ok d.m d.n → d.EisAll → ∀ Φ, d.KFin Φ →
    ∀ P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf → (vac → P = fun _ => 1) → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x
def CoreX_k : Prop := ∀ (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ), _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → Gen.WhitGenX ok vac c →
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.CorePure_k ok vac c
def DictAsmX_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.KWhit.CellFormula_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelEx_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.HeightDict_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.MeasDict_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.ThetaDict_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k
theorem eisAll_of_k (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hE : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.EisAll :=
  fun Φ hΦ => hE F E σ d _ _ (hS F E σ d Φ hΦ)
theorem levi_kfin_k (ok : ℕ → ℕ → Prop) (vac : Prop) (hv : ¬ vac) (c : ℂ) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k)
    (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k)
    (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CorePure_k ok vac c) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hok : ok d.m d.n) (hE : d.EisAll) :
    ∀ Φ, d.KFin Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x := by
  intro Φ hΦ x hx
  obtain ⟨R⟩ := hR F E σ d
  obtain ⟨k, cs, Φs, hs, rfl⟩ := hP hT hF hPK F E σ d R Φ hΦ (hK F E σ d R Φ hΦ)
  refine hL hT hTC hLB hU hS c F E σ d hE k cs Φs (fun i => (hs i).1) x (fun i => ?_)
  obtain ⟨P, gf, hpg⟩ := (hs i).2
  exact hC F E σ d R hok hE (Φs i) (hs i).1 P gf hpg (fun h => absurd h hv) x hx
theorem all_kfin_k (ok : ℕ → ℕ → Prop) (vac : Prop) (hv : ¬ vac) (c : ℂ) (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k)
    (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k)
    (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CorePure_k ok vac c) (hKK : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
      [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ, d.KFin Φ → ∀ k ∈ d.K, d.KFin (d.om k Φ))
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
    (hok : ok d.m d.n) (hE : d.EisAll) : ∀ Φ, d.KFin Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x :=
  hI hT c F E σ d d.KFin (fun Φ h => h.1) (hKK F E σ d)
    (_root_.PositivityTheory.SiegelWeilFormula.KWhit.levi_kfin_k ok vac hv c hT hTC hLB hR hF hK hPK hS hU hP hL hC d hok hE)
def KFinK_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ, d.KFin Φ → ∀ k ∈ d.K, d.KFin (d.om k Φ)
theorem whitK_of_X_k (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CoreX_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k) (hKK : _root_.PositivityTheory.SiegelWeilFormula.KWhit.KFinK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hW : Gen.WhitGenLt)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k := by
  intro F E _ _ _ _ _ σ d hnm hE Φ hΦ nb lam 𝓖 hc ε w hw T hT' x
  have := _root_.PositivityTheory.SiegelWeilFormula.KWhit.all_kfin_k (fun M n => n < M) False not_false 1 hI hT hTC hLB hR hF hK hPK hS hU hP hL
    (hC _ _ _ hT hA hS hU hW hD) hKK d hnm hE Φ hΦ x nb lam 𝓖 hc ε w hw T hT'
  simpa only [one_mul] using this
theorem whitEq_of_X_k (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CoreX_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k) (hKK : _root_.PositivityTheory.SiegelWeilFormula.KWhit.KFinK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k)
    (hW : Gen.WhitGenEq) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k := by
  intro F E _ _ _ _ _ σ d hmn Φ hΦ
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.asc_whitAt_iff_k]
  exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.all_kfin_k (fun M n => M = n ∧ 1 ≤ M) False not_false 2 hI hT hTC hLB hR hF hK hPK hS hU hP hL
    (hC _ _ _ hT hA hS hU hW hD) hKK d ⟨hmn, d.ok.hm⟩ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.eisAll_of_k hS hEW d) Φ hΦ
theorem whitLow_of_X_k (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hV : _root_.PositivityTheory.SiegelWeilFormula.KWhit.VacSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CoreX_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k) (hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (hW : Gen.WhitGenLow)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k := by
  intro F E _ _ _ _ _ σ d R hmn Φ hΦ hvac
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.asc_whitAt_iff_k]
  have hE := _root_.PositivityTheory.SiegelWeilFormula.KWhit.eisAll_of_k hS hEW d
  have hcore := hC _ _ _ hT hA hS hU hW hD
  refine hI hT 0 F E σ d (fun Φ => Φ ∈ d.sch ∧ d.T Φ ∈ R.vac) (fun Φ h => h.1)
    (fun Φ h k hk => ⟨d.ok.dbl.weil.2.1.pres k Φ h.1, (hVK F E σ d R).1 Φ h.1 h.2 k hk⟩) ?_ Φ ⟨hΦ, hvac⟩
  intro Φ' h' x hx
  obtain ⟨k, cs, Φs, hs, rfl⟩ := hV hT hF hPK hVK F E σ d R Φ' h'.1 h'.2
  refine hL hT hTC hLB hU hS 0 F E σ d hE k cs Φs (fun i => (hs i).1) x (fun i => ?_)
  obtain ⟨gf, hpg⟩ := (hs i).2.2
  exact hcore F E σ d R ⟨hmn, d.ok.hm⟩ hE (Φs i) (hs i).1 _ gf hpg (fun _ => rfl) x hx
end PositivityTheory.SiegelWeilFormula.KWhit
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
def Au_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)
theorem em_ne_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (j : Fin L.n) : L.em j ≠ L.i₀ := fun h => (L.rng (L.em j)).2 ⟨j, rfl⟩ h
theorem Au_mul_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L v = _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (u + v) := by
  have h0 : (∑ j, Matrix.single L.i₀ (L.em j) (u j)) * (∑ k, Matrix.single L.i₀ (L.em k) (v k)) = 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun k _ => Matrix.single_mul_single_of_ne _ _ _ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.em_ne_k L j) _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, add_mul, mul_add, one_mul, mul_one, h0, add_zero, Pi.add_apply, Matrix.single_add,
    Finset.sum_add_distrib, add_assoc]
theorem Au_zero_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L 0 = 1 := by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k]
theorem cA_injective_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Function.Injective (cA σ) := by
  have : FiniteDimensional F E := Module.Finite.of_basis d.bs
  have hb : Function.Bijective σ := AlgHom.bijective σ
  exact (Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofBijective σ hb)).injective
theorem frame_blk_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {x : d.G} {A A' : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (h : inFrame d.b x = Matrix.fromBlocks A 0 0 A') : Aᵀ * A'.map (cA σ) = 1 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have h2 := kunf.frame_eq hε x
  rw [h] at h2
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.map_zero _ (map_zero (cA σ))] at h2
  exact (Matrix.fromBlocks_inj.1 h2).2.1
theorem blk_unique_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {x y : d.G} {A A₁ A₂ : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (hx : inFrame d.b x = Matrix.fromBlocks A 0 0 A₁) (hy : inFrame d.b y = Matrix.fromBlocks A 0 0 A₂) : x = y := by
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_blk_k d hx
  have h2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_blk_k d hy
  have h1' : A₁.map (cA σ) * Aᵀ = 1 := mul_eq_one_comm.1 h1
  have e : A₁.map (cA σ) = A₂.map (cA σ) := by
    calc A₁.map (cA σ) = A₁.map (cA σ) * (Aᵀ * A₂.map (cA σ)) := by rw [h2, Matrix.mul_one]
      _ = A₂.map (cA σ) := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have e2 : A₁ = A₂ := Matrix.map_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cA_injective_k d) e
  apply kunf.inFrame_injective d.b
  rw [hx, hy, e2]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end
