module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle304
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle182
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixPer

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def flagCoordMap (d : HypDec S S₀ ρ) (p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ)) : flagN d :=
  ⟨d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2),
    mul_mem (d.levi_mem_NFlag p.1.2) (mul_mem (d.nB_mem_NFlag p.2.1) (d.nC_mem_NFlag p.2.2))⟩

theorem flagCoordMap_bijective (d : HypDec S S₀ ρ) : Function.Bijective (flagCoordMap d) := by
  refine ⟨fun p q h => ?_, fun n => ?_⟩
  · rcases p with ⟨⟨u, hu⟩, b, c⟩
    rcases q with ⟨⟨v, hv⟩, b', c'⟩
    have e : d.levi u * (d.nB b * d.nC c) = d.levi v * (d.nB b' * d.nC c') :=
      congrArg Subtype.val h
    have eX := congrArg (fun g => d.pX * (mt S g * d.jX)) e
    simp only [mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX] at eX
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul, Matrix.one_mul] at eX
    have huv : u = v := Units.ext eX
    subst v
    have e' := mul_left_cancel e
    have e0 := congrArg (fun g => d.pX * (mt S g * d.j0)) e'
    simp only [mt_mul, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.pX_j0,
      cancel₂ d.pX_jX, Matrix.one_mul, zero_add] at e0
    subst b'
    have eY := congrArg (fun g => d.pX * (mt S g * d.jY)) (mul_left_cancel e')
    simp only [d.nC_jY, Matrix.mul_add, d.pX_jY, cancel₂ d.pX_jX, Matrix.one_mul, zero_add] at eY
    exact Prod.ext rfl (Prod.ext rfl (Subtype.ext eY))
  · obtain ⟨T, B, hT, hX, h0⟩ := exists_blocks d n.2
    obtain ⟨u, hu, huT⟩ := Decomp.exists_unit hT
    let b := (u⁻¹).1 * B
    let g := d.levi u * d.nB b
    have hgX : mt S g * d.jX = mt S n.1 * d.jX := by
      dsimp only [g]
      rw [mt_mul, Matrix.mul_assoc, d.nB_jX, d.levi_jX, hX, huT, Matrix.mul_add, Matrix.mul_one]
    have hg0 : mt S g * d.j0 = mt S n.1 * d.j0 := by
      dsimp only [g, b]
      rw [mt_mul, Matrix.mul_assoc, d.nB_j0, h0, Matrix.mul_add,
        d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc (mt S (d.levi u)), d.levi_jX,
        Matrix.mul_assoc d.jX, ← Matrix.mul_assoc u.1, Units.mul_inv, Matrix.one_mul]
    let k := g⁻¹ * n.1
    have hkX : mt S k * d.jX = d.jX := by
      dsimp only [k]
      rw [mt_mul, Matrix.mul_assoc, ← hgX, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have hk0 : mt S k * d.j0 = d.j0 := by
      dsimp only [k]
      rw [mt_mul, Matrix.mul_assoc, ← hg0, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have gram {m l : ℕ} (X : Mx D S.rank m) (Y : Mx D S.rank l) :
        adj (mt S k * X) * (gA S * (mt S k * Y)) = adj X * (gA S * Y) := by
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) _ Y,
        ← Matrix.mul_assoc (adj (mt S k)), GlobalTheory.MixModel.mt_unitary]
    have pY : d.pY * (mt S k * d.jY) = 1 := by
      rw [d.pY_eq, Matrix.mul_assoc, ← hkX, gram, d.gram_XY]
    have p0 : d.p0 * (mt S k * d.jY) = 0 := by
      rw [d.p0_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hk0, gram, d.gram_0Y, Matrix.mul_zero]
    let C := d.pX * (mt S k * d.jY)
    have hkY : mt S k * d.jY = d.jY + d.jX * C := by
      conv_lhs => rw [← Matrix.one_mul (mt S k * d.jY), ← d.sum_eq_one]
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
        pY, p0, Matrix.mul_zero, add_zero, Matrix.mul_one, add_comm]
    have hC := gram d.jY d.jY
    rw [hkY, d.gram_YY] at hC
    simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_YY,
      d.gram_XY, cancel₃ d.gram_XX, cancel₃ d.gram_YX, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add] at hC
    let c : skewA D ρ := ⟨C, eq_neg_of_add_eq_zero_left hC⟩
    have hk : k = d.nC c := d.ga_ext (hkX.trans (d.nC_jX c).symm)
      (hk0.trans (d.nC_j0 c).symm) (hkY.trans (d.nC_jY c).symm)
    refine ⟨(⟨u, hu⟩, b, c), Subtype.ext ?_⟩
    change d.levi u * (d.nB b * d.nC c) = n.1
    rw [← mul_assoc, ← hk]
    exact mul_inv_cancel_left g n.1

theorem pX_mt_flagCoord (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) =
      u.1 * (d.pX + c.1 * d.pY + b * d.p0 - (half D • (b * plus S₀ b)) * d.pY) := by
  rw [mt_mul, mt_mul, ← Matrix.mul_assoc, d.pX_levi, Matrix.mul_assoc, ← Matrix.mul_assoc d.pX, d.pX_nB]
  congr 1
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_nC, d.wittDecomp_projAnisotropic_unipotentSkew, d.pY_nC]

theorem flagCoord_jX (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jX) = u.1 := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jX, d.pY_jX, d.p0_jX, Matrix.mul_zero,
    Matrix.mul_one, add_zero, sub_zero]

theorem flagCoordinate_at_base (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.j0) = u.1 * b := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.mul_zero,
    Matrix.mul_one, add_zero, sub_zero, zero_add]

theorem flagCoord_jY (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jY) =
      u.1 * (c.1 - half D • (b * plus S₀ b)) := by
  rw [← Matrix.mul_assoc, pX_mt_flagCoord]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, d.pX_jY, d.pY_jY, d.p0_jY, Matrix.mul_zero,
    Matrix.mul_one, add_zero, zero_add, Matrix.mul_sub]

theorem flagCoord_inv_jX (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c))⁻¹ * d.jX) = (u⁻¹).1 := by
  set g := d.levi u * (d.nB b * d.nC c)
  have h1 : Formalism.L2.Theta.mt S g * d.jX = d.jX * u.1 := by
    simp only [g, mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  have h2 : Formalism.L2.Theta.mt S g⁻¹ * d.jX = d.jX * (u⁻¹).1 := by
    calc Formalism.L2.Theta.mt S g⁻¹ * d.jX = Formalism.L2.Theta.mt S g⁻¹ * (d.jX * u.1 * (u⁻¹).1) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX * (u⁻¹).1 := by
          rw [← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  rw [h2, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]

end GlobalTheory.MixPer

namespace GlobalTheory.MixPer

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem flagCoord_b (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    (u⁻¹).1 * (d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.j0)) = b := by
  rw [flagCoordinate_at_base, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem flagCoord_c (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    (u⁻¹).1 * (d.pX * (Formalism.L2.Theta.mt S (d.levi u * (d.nB b * d.nC c)) * d.jY)) + half D • (b * plus S₀ b) = c.1 := by
  rw [flagCoord_jY, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, sub_add_cancel]

end GlobalTheory.MixPer

namespace GlobalTheory.MixPer

theorem flagCoord_homeo : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    ∃ e : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) ≃ₜ flagN d,
      ∀ p, (e p : GA D S) = d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2) := by
  intro D S S₀ ρ d
  have := (lattice_Mx D ρ ρ).1
  let e0 := Equiv.ofBijective _ (flagCoordMap_bijective d)
  have key : ∀ n : flagN d, (n : GA D S) =
      d.levi (e0.symm n).1.1 * (d.nB (e0.symm n).2.1 * d.nC (e0.symm n).2.2) := fun n =>
    congrArg Subtype.val (e0.apply_symm_apply n).symm
  have hM : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S) :=
    (continuous_mt S).comp continuous_subtype_val
  have hMi : Continuous fun n : flagN d => Formalism.L2.Theta.mt S (n : GA D S)⁻¹ :=
    (continuous_mt S).comp continuous_subtype_val.inv
  have hU : ∀ n : flagN d, ((e0.symm n).1.1).val = d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.jX) := by
    intro n; rw [key n, flagCoord_jX]
  have hUi : ∀ n : flagN d, (((e0.symm n).1.1)⁻¹).val =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) := by
    intro n; rw [key n, flagCoord_inv_jX]
  have hB : ∀ n : flagN d, (e0.symm n).2.1 =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) * (d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.j0)) := by
    intro n; rw [← hUi n]; conv_rhs => rw [key n]
    exact (flagCoord_b d _ _ _).symm
  have hC : ∀ n : flagN d, ((e0.symm n).2.2).val =
      d.pX * (Formalism.L2.Theta.mt S (n : GA D S)⁻¹ * d.jX) * (d.pX * (Formalism.L2.Theta.mt S (n : GA D S) * d.jY)) +
        half D • ((e0.symm n).2.1 * plus S₀ (e0.symm n).2.1) := by
    intro n; rw [← hUi n]; conv_rhs => rw [key n]
    exact (flagCoord_c d _ _ _).symm
  have cU : Continuous fun n : flagN d => ((e0.symm n).1.1).val := by
    simp only [hU]; exact continuous_const.matrix_mul (hM.matrix_mul continuous_const)
  have cUi : Continuous fun n : flagN d => (((e0.symm n).1.1)⁻¹).val := by
    simp only [hUi]; exact continuous_const.matrix_mul (hMi.matrix_mul continuous_const)
  have cB : Continuous fun n : flagN d => (e0.symm n).2.1 := by
    simp only [hB]
    exact (continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul
      (continuous_const.matrix_mul (hM.matrix_mul continuous_const))
  have cC : Continuous fun n : flagN d => ((e0.symm n).2.2).val := by
    have hp : Continuous fun n : flagN d => (e0.symm n).2.1 * plus S₀ (e0.symm n).2.1 :=
      cB.matrix_mul (continuous_const.matrix_mul (continuous_adj.comp cB))
    simp only [hC]
    exact ((continuous_const.matrix_mul (hMi.matrix_mul continuous_const)).matrix_mul
      (continuous_const.matrix_mul (hM.matrix_mul continuous_const))).add (hp.const_smul (half D))
  refine ⟨{ toEquiv := e0, continuous_toFun := ?_, continuous_invFun := ?_ }, fun p => rfl⟩
  · show Continuous (flagCoordMap d)
    exact Continuous.subtype_mk ((d.continuous_levi.comp (continuous_subtype_val.comp continuous_fst)).mul
      ((d.continuous_nB.comp (continuous_fst.comp continuous_snd)).mul
        (d.continuous_nC.comp (continuous_snd.comp continuous_snd)))) _
  · refine Continuous.prodMk ?_ (Continuous.prodMk cB ?_)
    · exact continuous_induced_rng.2 (Units.continuous_iff.2 ⟨cU, cUi⟩)
    · exact continuous_induced_rng.2 cC

end GlobalTheory.MixPer
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesClosed

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

def lowPart {m : ℕ} (M : Mx D m m) : Mx D m m := Matrix.of fun i j => if j ≤ i then M i j else 0

theorem continuous_lowPart {m : ℕ} : Continuous (lowPart (D := D) (m := m)) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun a : Mx D m m => if j ≤ i then a i j else 0
    split_ifs
    · exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const

theorem lowPart_eq_iff {m : ℕ} (M : Mx D m m) :
    lowPart M = lowPart 1 ↔ ∀ i j : Fin m, (j < i → M i j = 0) ∧ M i i = 1 := by
  constructor
  · intro h i j
    refine ⟨fun hji => ?_, ?_⟩
    · have := congrFun (congrFun h i) j
      simp only [lowPart, Matrix.of_apply, if_pos hji.le] at this
      rwa [Matrix.one_apply_ne hji.ne'] at this
    · have := congrFun (congrFun h i) i
      simp only [lowPart, Matrix.of_apply, if_pos (le_refl i), Matrix.one_apply_eq] at this
      exact this
  · intro h
    ext i j
    simp only [lowPart, Matrix.of_apply]
    split_ifs with hji
    · rcases hji.lt_or_eq with hlt | heq
      · rw [(h i j).1 hlt, Matrix.one_apply_ne hlt.ne']
      · subst heq; rw [(h j j).2, Matrix.one_apply_eq]
    · rfl

theorem strictUp_sub_one {m : ℕ} {M : Mx D m m} (h : ∀ i j : Fin m, (j < i → M i j = 0) ∧ M i i = 1) :
    GlobalTheory.BesselChar.StrictUp (M - 1) := by
  intro j i hij
  rcases hij.lt_or_eq with hlt | heq
  · rw [Matrix.sub_apply, (h j i).1 hlt, Matrix.one_apply_ne hlt.ne', sub_zero]
  · subst heq; rw [Matrix.sub_apply, (h i i).2, Matrix.one_apply_eq, sub_self]

theorem mem_jacGrp_iff_mat (g : GA D S) : g ∈ jacGrp d ↔
    (d.p0 ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.jX) = 0 ∧
      ∀ i j : Fin ρ, (j < i → (d.pX ⬝ (mt S g ⬝ d.jX)) i j = 0) ∧ (d.pX ⬝ (mt S g ⬝ d.jX)) i i = 1) := by
  constructor
  · intro hg
    obtain ⟨n, hn, h, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.1 g).1 hg
    obtain ⟨u, hu, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
    have e : mt S (d.levi u * (d.nB b * d.nC c) * d.emb0 h) ⬝ d.jX = d.jX ⬝ u.1 := by
      rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, GlobalTheory.MixPer.Decomp.mt_flag_jX]
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_jX, d.pY_jX, d.pX_jX, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.one_mul]
    exact ⟨rfl, rfl, fun i j => hu i j⟩
  · rintro ⟨h0, hY, hX⟩
    obtain ⟨u, hu, hu1⟩ := GlobalTheory.MixPer.Decomp.exists_unit (strictUp_sub_one hX)
    have hu' : u.1 = d.pX ⬝ (mt S g ⬝ d.jX) := by rw [hu1, add_sub_cancel]
    have hgX : mt S g ⬝ d.jX = d.jX ⬝ u.1 := by
      rw [hu']
      conv_lhs => rw [GlobalTheory.MixPer.Decomp.decomp d (mt S g ⬝ d.jX)]
      rw [h0, hY, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
    have hst : (d.levi u)⁻¹ * g ∈ stabX d := mem_fixer.2 (GlobalTheory.MixPer.Decomp.fix_of_eq (by rw [d.levi_jX, hgX]))
    obtain ⟨n, hn, h, hnh⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.1 _).1 hst
    have hn' : n ∈ flagN d := (Subgroup.mem_inf.1 (show n ∈ flagN d ⊓ fixer S d.jX from hn)).1
    have e : g = d.levi u * n * d.emb0 h := by rw [mul_assoc, ← hnh, mul_inv_cancel_left]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem (d.levi_mem_NFlag hu) hn')) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem jacGrp_closed : IsClosed (jacGrp d : Set (GA D S)) := by
  haveI : T2Space (Mx D S₀.rank ρ) := (lattice_Mx D _ _).2.2.2.1
  haveI : T2Space (Mx D ρ ρ) := (lattice_Mx D _ _).2.2.2.1
  have hc : Continuous fun g : GA D S => mt S g ⬝ d.jX := (continuous_mt S).matrix_mul continuous_const
  have e : (jacGrp d : Set (GA D S)) = {g | d.p0 ⬝ (mt S g ⬝ d.jX) = 0} ∩ {g | d.pY ⬝ (mt S g ⬝ d.jX) = 0} ∩
      {g | lowPart (d.pX ⬝ (mt S g ⬝ d.jX)) = lowPart 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_jacGrp_iff_mat, Set.mem_inter_iff, Set.mem_setOf_eq, lowPart_eq_iff, and_assoc]
  rw [e]
  exact ((isClosed_eq (continuous_const.matrix_mul hc) continuous_const).inter
    (isClosed_eq (continuous_const.matrix_mul hc) continuous_const)).inter
    (isClosed_eq (continuous_lowPart.comp (continuous_const.matrix_mul hc)) continuous_const)

theorem flagUnipotent_anisotropic_projection_eq_one {n : GA D S} (hn : n ∈ flagN d) : d.p0 ⬝ (mt S n ⬝ d.j0) = 1 := by
  obtain ⟨u, -, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
  rw [mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]
  rw [d.nC_j0, d.nB_j0, ← Matrix.mul_assoc d.p0 (mt S (d.levi u)), d.wittDecomp_projAnisotropic_levi, Matrix.mul_add, d.p0_j0,
    ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]

theorem witt_anisotropic_block_flag_mul_embedded {n : GA D S} (hn : n ∈ flagN d) (k : GA D S₀) :
    d.p0 ⬝ (mt S (n * d.emb0 k) ⬝ d.j0) = mt S₀ k := by
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n) d.j0, ← Matrix.mul_assoc d.p0, flagUnipotent_anisotropic_projection_eq_one d hn,
    Matrix.one_mul]



theorem exists_emb_of_fix {k : GA D S₀} (hk : mt S₀ k ⬝ o.jB = o.jB) : ∃ a : GA D A, o.emb (a, 1) = k := by
  have h1 : o.pB ⬝ (mt S₀ k ⬝ o.jA) = 0 := by
    have e : adj o.jB ⬝ (gA S₀ ⬝ (mt S₀ k ⬝ o.jA)) = 0 := by
      conv_lhs => rw [← hk]
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S₀) (mt S₀ k) o.jA,
        ← Matrix.mul_assoc (adj (mt S₀ k)) (gA S₀ ⬝ mt S₀ k) o.jA, mt_unitary, o.gram_BA]
    rw [o.pB_eq, Matrix.mul_assoc, Matrix.mul_assoc, e, Matrix.mul_zero]
  obtain ⟨M, hM⟩ : ∃ M : Mx D A.rank A.rank, M = o.pA ⬝ (mt S₀ k ⬝ o.jA) := ⟨_, rfl⟩
  have hA : mt S₀ k ⬝ o.jA = o.jA ⬝ M := by
    calc mt S₀ k ⬝ o.jA = (o.jA ⬝ o.pA + o.jB ⬝ o.pB) ⬝ (mt S₀ k ⬝ o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA ⬝ M := by rw [Matrix.add_mul, Matrix.mul_assoc o.jB, h1, Matrix.mul_zero, add_zero, Matrix.mul_assoc, hM]
  have hu : adj M * (gA A * M) = gA A := by
    calc adj M * (gA A * M) = adj (o.jA ⬝ M) ⬝ (gA S₀ ⬝ (o.jA ⬝ M)) := by
          rw [adj_mul, ← o.gram_AA]; simp only [Matrix.mul_assoc]
      _ = adj (mt S₀ k ⬝ o.jA) ⬝ (gA S₀ ⬝ (mt S₀ k ⬝ o.jA)) := by rw [hA]
      _ = gA A := by
          rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S₀) (mt S₀ k) o.jA,
            ← Matrix.mul_assoc (adj (mt S₀ k)) (gA S₀ ⬝ mt S₀ k) o.jA, mt_unitary, o.gram_AA]
  have key : mt S₀ k = o.jA ⬝ M ⬝ o.pA + o.jB ⬝ o.pB := by
    have e : mt S₀ k ⬝ (o.jA ⬝ o.pA + o.jB ⬝ o.pB) = mt S₀ k := by rw [o.sum_eq_one]; exact Matrix.mul_one _
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hk] at e
    exact e.symm
  exact ⟨ofMat A M hu, mt_injective S₀ (by rw [o.mt_emb, mt_ofMat, mt_one, Matrix.mul_one, key])⟩

def prodSub : Subgroup (GA D S) where
  carrier := {g | ∃ n ∈ flagN d, ∃ h, g = n * embA d o h}
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, hn, h, rfl⟩ ⟨n', hn', h', rfl⟩
    refine ⟨n * (embA d o h * n' * (embA d o h)⁻¹), mul_mem hn ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 n' hn' _), h * h', ?_⟩
    rw [map_mul]; group
  inv_mem' := by
    rintro _ ⟨n, hn, h, rfl⟩
    refine ⟨embA d o h⁻¹ * n⁻¹ * (embA d o h⁻¹)⁻¹, (GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 _ (inv_mem hn) _, h⁻¹, ?_⟩
    rw [map_inv]; group

theorem besGrp_le_prodSub : besGrp d o ≤ prodSub d o :=
  sup_le (fun n hn => ⟨n, hn, 1, by simp⟩) (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, by simp⟩)

theorem besGrp_eq_inter :
    (besGrp d o : Set (GA D S)) = (jacGrp d : Set (GA D S)) ∩ {g | d.p0 ⬝ (mt S g ⬝ d.j0) ⬝ o.jB = o.jB} := by
  ext g
  constructor
  · intro hg
    obtain ⟨n, hn, h, rfl⟩ := besGrp_le_prodSub d o hg
    refine ⟨mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨o.emb (h, 1), rfl⟩), ?_⟩
    show d.p0 ⬝ (mt S (n * d.emb0 (o.emb (h, 1))) ⬝ d.j0) ⬝ o.jB = o.jB
    rw [witt_anisotropic_block_flag_mul_embedded d hn, o.emb_jB, mt_one, Matrix.mul_one]
  · rintro ⟨hg, he⟩
    obtain ⟨n, hn, k, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.1 g).1 hg
    have he' : d.p0 ⬝ (mt S (n * d.emb0 k) ⬝ d.j0) ⬝ o.jB = o.jB := he
    rw [witt_anisotropic_block_flag_mul_embedded d hn] at he'
    obtain ⟨a, ha⟩ := exists_emb_of_fix o he'
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨a, by rw [embA_apply, ha]⟩)

theorem besGrp_isClosed : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L),
    IsClosed (besGrp d o : Set (GA D S)) := by
  intro D S S₀ A L ρ d o
  rw [besGrp_eq_inter]
  haveI : T2Space (Mx D S₀.rank L.rank) := (lattice_Mx D _ _).2.2.2.1
  exact (jacGrp_closed d).inter (isClosed_eq
    ((continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)).matrix_mul continuous_const)
    continuous_const)

end GlobalTheory.BesClosed
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm

namespace GlobalTheory.MixedTerm.DerLaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_tauE_add_conj (D : D7) (e : D.host.E) :
    ∑ t, (tauE D t e + starRingEnd ℂ (tauE D t e)) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [Finset.sum_add_distrib, h4]

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  rw [← sum_tauE_add_conj]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

theorem trace_map_mul (D : D7) (τ : D.what₂.Tau) {m n : ℕ} (P : Matrix (Fin m) (Fin n) D.host.E)
    (x : Matrix (Fin n) (Fin m) D.host.E) :
    Matrix.trace (P.map (tauE D τ) * x.map (tauE D τ)) = tauE D τ (Matrix.trace (P * x)) := by
  rw [← Matrix.map_mul]

  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem term_derAlong : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ x y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 (derAlong ψ θ V W C x G) y = (2 * Real.pi * Complex.I * (ratPair W y x : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hiso hCC ψ hψ θ hθ μ 𝓨 hcov G hG x y
  have hlin := GlobalTheory.T.mixedModelTerm_linear_thetaFunctions D V V' W r C C' B ψ hψ μ 𝓨 hcov y
  have hder := fun τ => GlobalTheory.T.mixedModelTerm_derivative_isotropicDirection D V V' W r C C' B hiso hCC ψ hψ θ hθ μ 𝓨 hcov G hG τ (x.map (tauE D τ)) y
  set f : D.what₂.Tau → WO V W → ℂ :=
    fun τ => Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ (x.map (tauE D τ))) G with hf
  have hft : ∀ τ, IsThetaFunO ψ V W (f τ) := fun τ => GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hG
  have hsum : ∀ s : Finset D.what₂.Tau,
      term ψ V V' W C C' B μ 𝓨 (∑ τ ∈ s, f τ) y = ∑ τ ∈ s, term ψ V V' W C C' B μ 𝓨 (f τ) y := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      have h0 := hlin.2 0 G hG
      rw [zero_smul, zero_mul] at h0
      simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hlin.1 _ _ (hft a) (GlobalTheory.Size.theta_finsetSum s fun i _ => hft i), ih]
  show term ψ V V' W C C' B μ 𝓨 (∑ τ, f τ) y = _
  rw [hsum, Finset.sum_congr rfl fun τ _ => hder τ, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  simp only [trace_map_mul, sum_two_re_tauE, ratPair, Complex.ofReal_ratCast]

end GlobalTheory.MixedTerm.DerLaw

end
end
