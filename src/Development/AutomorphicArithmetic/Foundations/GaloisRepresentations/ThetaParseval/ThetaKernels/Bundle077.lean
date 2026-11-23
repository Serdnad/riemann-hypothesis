module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle034
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle048
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle038
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle036
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle069
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle060
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle062
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle067
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.IncMFromBlocks
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle004
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle040
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle058
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle001
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C5 PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq
set_option linter.unusedSectionVars false
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
variable (L) in
structure Hyp_k (nb : nA σ d.Y d.b → d.G) (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (w₁ : d.G)
    (cM : (Fin L.n → AE F E) × AF F → d.G) (δ : E) : Prop where
  nb : IsNMap d.b nb
  uM : ∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 a'
  nb' : IsNMap L.b nb'
  wr : w₁ ∈ rat2 σ d.Y
  wf : ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)
  cf : ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 A'
  δ0 : δ ≠ 0
variable (L) in
abbrev Cr_k : Type := {c : (Fin L.n → AE F E) × AF F // c.1 ∈ L.ratV ∧ c.2 ∈ (algebraMap F (AF F)).range}
variable (L) in
def Fix_k (x : d.G) : Prop :=
  ∀ k, inFrame d.b x k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)
theorem fix_mul_k {x y : d.G} (hx : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L x) (hy : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L y) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (x * y) := by
  intro k
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)]
  · rw [hy, Matrix.one_apply_eq, mul_one]; exact hx k
  · intro j _ hj; rw [hy j, Matrix.one_apply_ne hj, mul_zero]
  · simp
theorem fix_inv_k {x : d.G} (hx : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L x) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L x⁻¹ := by
  intro k
  have h1 := congrFun (congrFun (GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul d.b x) k) (Sum.inl L.i₀)
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)] at h1
  · rw [hx, Matrix.one_apply_eq, mul_one] at h1; exact h1
  · intro j _ hj; rw [hx j, Matrix.one_apply_ne hj, mul_zero]
  · simp
theorem fix_j_k (g : G2 σ L.Y) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (L.j g) := by
  intro k
  exact (L.j_out g (Sum.inl L.i₀) (by simp) k).2
theorem first_orbit_parabolic_left {p g : d.G} (hp : p ∈ par2 σ d.Y) : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (p * g) ↔ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L g := by
  constructor
  · intro h1
    have := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_parabolic_mul L ((par2 σ d.Y).inv_mem hp) h1
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  · exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_parabolic_mul L hp
theorem not_first_orbit_weyl (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {g : d.G} (hg : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L g) : ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (w₁ * g) := by
  intro hS
  obtain ⟨a₀, b₀, ha, hb, hW⟩ := h.wf
  have h1 := hS L.i₀
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)] at h1
  · rw [hg, Matrix.one_apply_eq, mul_one, hW] at h1
    simp [Matrix.single_apply, Matrix.one_apply] at h1
    exact hb (kfour.inclR_injective (F := F) (by rw [h1, map_zero]))
  · intro j _ hj; rw [hg j, Matrix.one_apply_ne hj, mul_zero]
  · simp
theorem out_mk_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (γ : rat2 σ d.Y) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ γ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = p * γ.1 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k γ
theorem mk_eq_mk_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {γ γ' : rat2 σ d.Y} :
    (Quotient.mk _ γ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = Quotient.mk _ γ' ↔ γ'.1 * γ.1⁻¹ ∈ par2 σ d.Y := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp
theorem rep_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q ∈ rat2 σ d.Y := (Quotient.out q).2
theorem mk_rep_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) : (Quotient.mk _ ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k d q⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = q := Quotient.out_eq q
theorem weyl_commutes_embedding (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (g : G2 σ L.Y) : w₁ * L.j g = L.j g * w₁ := by
  obtain ⟨a₀, b₀, ha, hb, hW⟩ := h.wf
  apply kunf.inFrame_injective d.b
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul]
  set W := inFrame d.b w₁
  set J := inFrame d.b (L.j g)
  have hJ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.pad_j_k L g
  let P : Fin d.n ⊕ Fin d.n → Prop := fun l => l = Sum.inl L.i₀ ∨ l = Sum.inr L.i₀
  have hWo : ∀ r c, ¬ (P r ∧ P c) → (W - 1) r c = 0 := by
    intro r c hrc
    rw [Matrix.sub_apply, hW]
    simp only [P, not_and_or] at hrc
    rcases hrc with hr | hr <;> push_neg at hr <;>
      simp [Matrix.single_apply, Matrix.one_apply, hr.1, hr.2, Ne.symm hr.1, Ne.symm hr.2]
  have hJo : ∀ r c, (P r ∨ P c) → (J - 1) r c = 0 := by
    intro r c hrc
    rw [Matrix.sub_apply, sub_eq_zero]
    rcases hrc with (h | h) | (h | h)
    · exact hJ r c (Or.inl h)
    · exact hJ r c (Or.inr (Or.inl h))
    · exact hJ r c (Or.inr (Or.inr (Or.inl h)))
    · exact hJ r c (Or.inr (Or.inr (Or.inr h)))
  have e1 : (W - 1) * (J - 1) = 0 :=
    mul_eq_zero_of_supp P (fun r l hl => hWo r l fun h => hl h.2) (fun l c hl => hJo l c (Or.inl hl))
  have e2 : (J - 1) * (W - 1) = 0 :=
    mul_eq_zero_of_supp (fun l => ¬ P l) (fun r l hl => hJo r l (Or.inr (not_not.1 hl))) (fun l c hl => hWo l c fun h => hl h.1)
  have eW : W = 1 + (W - 1) := by abel
  have eJ : J = 1 + (J - 1) := by abel
  rw [eW, eJ]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, e1, e2]
  abel
theorem uA_neg_mul_k (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u = 1 := by
  have := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k L (-u) u
  simp only [neg_add_cancel] at this
  rw [show _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u = _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u from rfl, this]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k]
theorem cM_frame_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    inFrame d.b (cM c) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ)) := by
  obtain ⟨A', hA'⟩ := h.cf c
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have h2 := kunf.frame_eq hε (cM c)
  rw [hA'] at h2
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.map_zero _ (map_zero (cA σ))] at h2
  have h1 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ * A'.map (cA σ) = 1 := (Matrix.fromBlocks_inj.1 h2).2.1
  have h1' : A'.map (cA σ) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ = 1 := mul_eq_one_comm.1 h1
  have hinv : (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ = 1 := by rw [← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.uA_neg_mul_k, Matrix.transpose_one]
  have e : A'.map (cA σ) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ := by
    calc A'.map (cA σ) = A'.map (cA σ) * ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ) := by rw [hinv, Matrix.mul_one]
      _ = (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have e2 : A' = (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ) := by
    rw [← e, Matrix.map_map]
    ext i j
    simp [cA_inv' hσ]
  rw [hA', e2]
theorem fix_cM'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (cM c) := by
  intro k
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h]
  rcases k with k | k
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L]
  · simp
theorem cM_rat'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {c : (Fin L.n → AE F E) × AF F} (hu : c.1 ∈ L.ratV)
    (ha : c.2 ∈ (algebraMap F (AF F)).range) : cM c ∈ rat2 σ d.Y := by
  obtain ⟨u₀, hu₀⟩ := ComplexParameterFamilyContinuity.mem_ratVec.1 hu
  obtain ⟨a₀, ha₀⟩ := ha
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u₀ j))
    (Matrix.single L.i₀ L.i₀ (a₀ • δ)) 0 ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (-u₀ j))ᵀ.map σ)) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h, ← hu₀, ← ha₀, Afc.incM_fromBlocks, kfour.incM_zero]
  congr 1
  · ext i k
    simp [incM, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, GlobalTheory.ThK.incV, Matrix.single_apply, Matrix.one_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · ext i k
    simp only [incM, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.map_apply, Matrix.single_apply]
    split_ifs
    · show (algebraMap F (AF F) a₀) • ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] (a₀ • δ)
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        ← Algebra.algebraMap_eq_smul_one]
    · simp
  · ext i k
    have cA_inclR (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) =
        (1 : AF F) ⊗ₜ[F] σ x
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    simp [incM, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, GlobalTheory.ThK.incV, Matrix.single_apply, Matrix.one_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [cA_inclR]
theorem emS_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    (inFrame d.b (cM c)).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = 1 := by
  ext r r'
  rcases r with k | k <;> rcases r' with k' | k' <;>
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L, L.inj.eq_iff,
      Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L _)] <;> split_ifs <;> simp
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem holPhi_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) {nb lam 𝓖}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (A : d.G → ℂ) (hAc : Continuous A)
    (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g) (pp qq : ℕ) (e : ℤ)
    (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) (x' : d.G) :
    IsHolW pp qq e fun y => fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) := by
  have hc' := hc
  obtain ⟨hN, -, -, h1⟩ := hc'
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ d.ok.frame
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ d.ok.frame
  obtain ⟨-, -, hTG, -, -, -⟩ := H.auxEx F E σ d
  haveI := hTG
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std
  have hnbc := kfour.nb_continuous hσ d.ok.frame hN
  let u : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have huc : Continuous u := kfour.continuous_chr hψ.1 T.1.1
  let γf : nA σ d.Y d.b → nA σ d.Y d.b := fun β => Classical.choose (hKc β)
  have hγ : ∀ β, γf β ∈ nF σ d.Y d.b ∧ γf β + β ∈ K := fun β => Classical.choose_spec (hKc β)
  let c : nA σ d.Y d.b → d.G := fun β => nb (γf β + β) * x'
  have key : ∀ β (g : d.G), A (c β * g) = A (nb β * (x' * g)) := by
    intro β g
    show A (nb (γf β + β) * x' * g) = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hN, mul_assoc, mul_assoc, hAi _ (_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_rat_k d hN (hγ β).1)]
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hC : IsCompact ((fun k => nb k * x') '' K) := hK.image (hnbc.mul continuous_const)
  have hmeas : ∀ y, AEStronglyMeasurable (fun β => A (c β * R.ι w y) * u β) (lam.restrict 𝓖) := by
    intro y
    have e : (fun β => A (c β * R.ι w y) * u β) = fun β => A (nb β * (x' * R.ι w y)) * u β :=
      funext fun β => by rw [key]
    rw [e]
    exact ((hAc.comp (hnbc.mul continuous_const)).mul huc).aestronglyMeasurable
  have := H.holT.2 d.n pp qq e d.G (R.ι w) (R.cont w) A hAc hA (nA σ d.Y d.b) (lam.restrict 𝓖) c u _ hC
    (fun β => ⟨_, (hγ β).2, rfl⟩) (fun β => (hψ.2.1 _).le) hmeas
  convert this using 2 with y
  simp only [fc]
  congr 1
  funext β
  rw [key]
theorem holCoef_pf_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (w : InfinitePlace F) {nb lam 𝓖}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b}
    {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (A : d.G → ℂ) (hAc : Continuous A) (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g)
    (pp qq : ℕ) (e : ℤ) (hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) :
    (∀ τ (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w y * x) = Complex.exp (τ * d.m) * fc d.B.ψ d.b nb lam 𝓖 A T x) ∧
    ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ u x, fc d.B.ψ d.b nb lam 𝓖 A T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 A T x := by
  have hc' := hc
  obtain ⟨hN, -, -, -⟩ := hc'
  have hr : ∀ l, _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T L.i₀ l = 0 := fun l => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, (hT.1 l).1]
  have hcol : ∀ k, _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T k L.i₀ = 0 := fun k => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, (hT.1 k).2]
  have hchar : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (h : Matrix (Fin d.n) (Fin d.n) ℂ) (xN y : GR d.n),
      h.IsHermitian → mR xN = nU h → fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w (xN * y)) =
        Complex.exp (Complex.I * (_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T * h).trace) * fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) := by
    intro x' hx' h xN y hh hxN
    obtain ⟨β₁, hι, hBw, hBu, hBf⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.unipotent_realEmbedding_exists d R w hN xN h hxN
    rw [map_mul, ← mul_assoc, hx' xN, hι, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KSing.fc_shift_k d hc A hAi T β₁,
      _root_.PositivityTheory.SiegelWeilFormula.AStep.character_unipotent_trace d R w T β₁ h hh hBw hBu hBf]
  have hright : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ)
      (xx y : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' → aᴴ * _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T * a = _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T →
      fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w (xx * y)) = F0 pp qq e xx * fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) :=
    fun x' hx' => H.holT.1 d.n pp qq e _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.holPhi_k H R w hc T A hAc hAi pp qq e hA x') (_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T) (hchar x' hx')
  have hleft : ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ) (xx : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' →
      aᴴ * _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T * a = _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T →
      ∀ x, fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w xx * x) = F0 pp qq e xx * fc d.B.ψ d.b nb lam 𝓖 A T x := by
    intro a a' xx hxx hs x
    obtain ⟨x', y₀, rfl, hx'⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.decW_pf_k R w x
    rw [← mul_assoc, ← hx' xx, mul_assoc, ← map_mul, hright x' hx' a a' xx y₀ hxx hs]
  refine ⟨fun τ y hy x => ?_, fun uM ν 𝓤 hu u x => ?_⟩
  · rw [hleft _ _ y hy (stab_diag L.i₀ _ (fun k hk => by simp [Pi.single_eq_of_ne hk]) _ hr hcol) x,
      weight_factor_dilation L.i₀ τ y hy]
    congr 2
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · have h0 := Krd.zeta_ne R.hζ
    refine (H.uEx F E σ d R L).2 uM ν 𝓤 hu w _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.fcCont_k d hc T A hAc hAi)
      (fun u hu' x => (H.fcConj F E σ d L nb lam 𝓖 hc).2 uM ν 𝓤 hu T T' hT A hAc hAi u hu' x) ?_ u x
    intro u y huy x
    rw [huy]
    obtain ⟨a', ha'⟩ := hu.1 u
    set S := ∑ j, Matrix.single L.i₀ (L.em j) (u j) with hS
    have hne : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
    set M := d.cw w S with hMdef
    have hM : ∀ k l, k ≠ L.i₀ → M k l = 0 := by
      intro k l hk
      simp [hMdef, hS, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.sum_apply, Matrix.single_apply, Ne.symm hk]
    have hM0 : M L.i₀ L.i₀ = 0 := by
      simp [hMdef, hS, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.sum_apply, Matrix.single_apply, hne]
    have hmy : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y)) * dZ d.n R.ζ⁻¹ := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k]
      simp only [← Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.one_mul]
      rw [Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.mul_one]
    rw [← huy, ha'] at hmy
    have hy : mR y = Matrix.fromBlocks (1 + M) 0 0 ((R.ζ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ)) * d.cw w a' *
        (R.ζ⁻¹ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ))) := by
      rw [hmy, hMdef]
      simp [dZ, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_add (f := _)]
    rw [hleft _ _ y hy (stab_row L.i₀ M hM _ hr hcol) x, weight_factor_det_one pp qq e y _ _ hy (det_row L.i₀ M hM hM0), one_mul]
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem cw_mul'_k (w : InfinitePlace F) {p q r : Type} [Fintype q] (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    d.cw w (A * B) = d.cw w A * d.cw w B := Matrix.map_mul
theorem cw_add'_k (w : InfinitePlace F) {p q : Type} (A B : Matrix p q (AE F E)) :
    d.cw w (A + B) = d.cw w A + d.cw w B := Matrix.map_add _ (map_add _) A B
theorem cw_one'_k (w : InfinitePlace F) : d.cw w (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_transpose'_k (w : InfinitePlace F) {p q : Type} (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ := rfl
theorem incM_b_mul_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 := by
  rw [incM, incM, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
theorem incM_b_inv_mul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) :
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
      incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 := by
  rw [incM, incM, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
theorem inFrame_mul'_k (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, e, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)), _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.one_mul]
theorem inFrame_one'_k : inFrame d.b (1 : d.G) = 1 := by
  have e : mat2 (1 : d.G) = 1 := rfl
  simp only [inFrame, e, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_inv_mul_k]
theorem matrixRep_eq_frameConj (x : d.G) : mat2 x = incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * inFrame d.b x *
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) := by
  simp only [inFrame, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.mul_one, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.one_mul]
theorem cw_inFrame_prod'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (f : InfinitePlace F → GR d.n) (w' : InfinitePlace F) :
    ∀ L : List (InfinitePlace F), L.Nodup → d.cw w' (inFrame d.b ((L.map fun w => R.ι w (f w)).prod)) =
      if w' ∈ L then d.cw w' (inFrame d.b (R.ι w' (f w'))) else 1 := by
  intro L
  induction L with
  | nil => intro _; simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.inFrame_one'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_one'_k]
  | cons a L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, _root_.PositivityTheory.SiegelWeilFormula.KFP.inFrame_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_mul'_k, ih hL.2]
    by_cases h : w' = a
    · subst h
      simp [hL.1]
    · rw [R.off_w a w' (f a) h, Matrix.one_mul]
      simp [h]
theorem dZ_cw_rot'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) (w : InfinitePlace F) :
    dZ d.n R.ζ * d.cw w (inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t)) = yrotM d.n (R.sg w) t * dZ d.n R.ζ := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_inFrame_prod'_k R (fun w => yrot d.n (R.sg w) t) w _ (Finset.nodup_toList _),
    if_pos (Finset.mem_toList.2 (Finset.mem_univ w)), R.at_w, mR_yrot]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end
