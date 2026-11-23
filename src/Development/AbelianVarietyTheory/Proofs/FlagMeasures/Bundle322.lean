module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle287
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle145
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictLat
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassIntegralLatticesBoundedDetLine
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassLatticesOrbitsSubspacesSharpExponent
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle070
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitPairK

open Matrix Formalism.MainNotions.S GlobalTheory.RowLev
open scoped TensorProduct

theorem hform_mulVec_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have e : ∀ (N : Matrix n n A) (u v : n → A), Formalism.UG.hform σ N u v = (σ ∘ u) ⬝ᵥ (N *ᵥ v) := by
    intro N u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [e, e, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

variable (I : AutInst)

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp [AutInst.fmat]

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp [AutInst.fmat]

theorem hAf_unitary (x : I.Gf) (v w : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I (I.fmat x *ᵥ v) (I.fmat x *ᵥ w) = hAf I v w := by
  unfold hAf
  rw [hform_mulVec_mulVec]
  have h : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
      I.fmat x = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  rw [h]

theorem hAf_move (x : I.Gf) (v w : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I v (I.fmat x *ᵥ w) = hAf I (I.fmat x⁻¹ *ᵥ v) w := by
  rw [← hAf_unitary I x (I.fmat x⁻¹ *ᵥ v) w, mulVec_mulVec, fmat_mul_inv, one_mulVec]

theorem hAf_smul_right (v w : Fin I.n → I.E ⊗[I.F] Af I.F) (c : I.E ⊗[I.F] Af I.F) :
    hAf I v (c • w) = c * hAf I v w := by
  simp only [hAf, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hAf_smul_left (v w : Fin I.n → I.E ⊗[I.F] Af I.F) (c : I.E ⊗[I.F] Af I.F) :
    hAf I (c • v) w = sigA I c * hAf I v w := by
  simp only [hAf, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hAf_sub_right (u v w : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I u (v - w) = hAf I u v - hAf I u w := by
  simp only [hAf, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hAf_sub_left (u u' w : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I (u - u') w = hAf I u w - hAf I u' w := by
  simp only [hAf, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem lf_iff {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    (y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    y ∈ I.Lf ↔ ∀ i, (((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
      *ᵥ y) i ∈ IntAf I.F I.E := by
  have e : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
    show Submodule.span _ _ = Submodule.span _ _
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
  rw [← e]
  exact hβ y

theorem eps_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (hx : ∀ i j, ε * ((β₀⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    ε • ((I.fmat x - 1) *ᵥ y) ∈ I.Lf := by
  rw [lf_iff I hβ] at hy ⊢
  intro i
  set Bi : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
    ((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) with hBi
  set B : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
    ((β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) with hB
  have hBB : B * Bi = 1 := by rw [hB, hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hM : ∀ i j, ε * (Bi * I.fmat x * B) i j ∈ IntAf I.F I.E := by
    intro i j
    have := hx i j
    rwa [Units.val_mul, Units.val_mul] at this
  have key : Bi *ᵥ ((I.fmat x - 1) *ᵥ y) = (Bi * I.fmat x * B) *ᵥ (Bi *ᵥ y) - Bi *ᵥ y := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (Bi * I.fmat x), hBB, Matrix.mul_one, Matrix.mul_sub,
      Matrix.mul_one, sub_mulVec]
  rw [mulVec_smul, key]
  generalize Bi *ᵥ y = z at hy ⊢
  show ε * ((Bi * I.fmat x * B) *ᵥ z - z) i ∈ IntAf I.F I.E
  rw [Pi.sub_apply, mul_sub]
  refine sub_mem ?_ (mul_mem hεi (hy i))
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [← mul_assoc]
  exact mul_mem (hM i j) (hy j)

theorem sig_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (hxi : ∀ i j, ε * ((β₀⁻¹ * ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    sigA I ε • ((I.fmat x - 1) *ᵥ y) ∈ I.Lf := by
  rw [GlobalTheory.AdelicLattice.adelicLattice_selfDual]
  intro y' hy'
  have h1 := eps_mem I hβ hεi x⁻¹ hxi hy'
  have h2 := (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 hy _ h1
  have e : hAf I y' (sigA I ε • ((I.fmat x - 1) *ᵥ y)) = hAf I (ε • ((I.fmat x⁻¹ - 1) *ᵥ y')) y := by
    rw [hAf_smul_right, hAf_smul_left, sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, hAf_sub_right,
      hAf_sub_left, hAf_move]
  rw [e]
  exact h2

theorem mv_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (h1 : ∀ i j, (1 - ε - sigA I ε) * (I.fmat x - 1) i j = 0)
    (hx : ∀ i j, ε * ((β₀⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    (hxi : ∀ i j, ε * ((β₀⁻¹ * ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x *ᵥ y ∈ I.Lf := by
  set w := (I.fmat x - 1) *ᵥ y with hw
  have hxy : I.fmat x *ᵥ y = y + w := by
    rw [hw, sub_mulVec, one_mulVec]
    abel
  have h0 : (1 - ε - sigA I ε) • w = 0 := by
    funext i
    simp only [hw, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Finset.mul_sum, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_assoc, h1 i j, zero_mul]
  have hsplit : w = ε • w + sigA I ε • w + (1 - ε - sigA I ε) • w := by
    rw [← add_smul, ← add_smul, show ε + sigA I ε + (1 - ε - sigA I ε) = 1 by ring, one_smul]
  rw [hxy, hsplit, h0, add_zero, ← add_assoc]
  exact add_mem (add_mem hy (eps_mem I hβ hεi x hx hy)) (sig_mem I hβ hεi x hxi hy)

end GlobalTheory.SplitPairK


open GlobalTheory.SplitPairK in
theorem GlobalTheory.SplitPairK.mem_kset_of_split : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (ε : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), ε * ε = ε → ε * Formalism.L2.SG.HidaSetting.sigA I ε = 0 → ε ∈ Formalism.MainNotions.S.IntAf I.F I.E → ∀ (k : I.Gf), (∀ i j, (1 - ε - Formalism.L2.SG.HidaSetting.sigA I ε) * (I.fmat k - 1) i j = 0) → (∀ i j, ε * ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → (∀ i j, ε * ((β₀⁻¹ * ((k⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → k ∈ I.Kset := by
  intro I β₀ hβ ε _ _ hεi k h1 h2 h3
  have h1' : ∀ i j, (1 - ε - sigA I ε) * (I.fmat k⁻¹ - 1) i j = 0 := by
    intro i j
    have e : I.fmat k⁻¹ - 1 = -(I.fmat k⁻¹ * (I.fmat k - 1)) := by
      rw [Matrix.mul_sub, fmat_inv_mul, Matrix.mul_one]
      abel
    rw [e, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum, neg_eq_zero]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [mul_left_comm, h1 l j, mul_zero]
  have h3' : ∀ i j, ε * ((β₀⁻¹ * ((k⁻¹⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ :
      GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈
      Formalism.MainNotions.S.IntAf I.F I.E := by
    simpa only [inv_inv] using h2
  show ((k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))) ∈ Formalism.UG.stabGL I.Lf
  intro y
  refine ⟨fun hy => mv_mem I hβ hεi k h1 h2 h3 hy, fun hy => ?_⟩
  have := mv_mem I hβ hεi k⁻¹ h1' h3 h3' hy
  rwa [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec] at this

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct Matrix

namespace GlobalTheory.RowLev

open Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.RedBasicsPf PIW.AdelClassFin IsDedekindDomain

theorem redMat0_of_actsAs : ∀ (I : AutInst) (N p : ℕ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) (fr : GlobalTheory.RowLev.PlFrame I N p w) (x : I.Gf), x ∈ I.Kset → ∀ M : Matrix (Fin N) (Fin N) (ZMod p), fr.ActsAs x M → Formalism.L2.SG.Pf.RowDictPf.RedMat0 I w p x M := by
  intro I N p w fr x hx M hM
  have hp : p.Prime := fr.prime
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p :=
    (Nat.card_congr fr.residueEquiv.toEquiv).trans (Nat.card_zmod p)
  have h1 : ∀ u ∈ lamAf (F := I.F) (wLat0 I w), u ∈ extId I w.asIdeal • I.Lf := by
    refine fun u hu => lamAf_w_le I w _ (fun a ha y hy => ?_) hu
    rw [DictLat.iv_smulE]
    exact Submodule.smul_mem_smul (r := Inhab.psi I.F I.E a) (Ideal.subset_span ⟨a, ha, rfl⟩) (DictLat.iv_mem I hy)
  have h2 : ∀ u ∈ extId I w.asIdeal • I.Lf, u ∈ lamAf (F := I.F) (wLat0 I w) := by
    intro u hu
    refine Submodule.smul_induction_on hu (fun a ha v hv => ?_) (fun _ _ h h' => add_mem h h')
    refine Submodule.span_induction (p := fun a _ => a • v ∈ lamAf (F := I.F) (wLat0 I w)) ?_ ?_ ?_ ?_ ha
    · rintro z ⟨b, hb, e⟩
      show (z : I.E ⊗[I.F] Af I.F) • v ∈ _
      rw [e]
      exact smul_mem I w hb hv
    · simp
    · intro a b _ _ ha hb
      rw [add_smul]; exact add_mem ha hb
    · intro s a _ ha
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ s ha
  have hz : ∀ u : I.Lf, fr.c u = 0 ↔ (u : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ lamAf (F := I.F) (wLat0 I w) :=
    fun u => (fr.c_ker u).trans ⟨h2 _, h1 _⟩
  choose y hy using fun i : Fin N => fr.c_surj (Pi.single i 1)
  choose b hbL hb using fun i => dense I w hp hcard (y i).2
  let B : Fin N → I.Lf := fun i => ⟨iv I (b i), DictLat.iv_mem I (hbL i)⟩
  have hB : ∀ i, fr.c (B i) = Pi.single i 1 := by
    intro i
    have e : fr.c (y i - B i) = 0 := (hz _).2 (hb i)
    rw [map_sub, sub_eq_zero] at e
    rw [← e, hy]
  have hci : ∀ (n : ℤ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u := by
    intro n u; rw [map_smulₛₗ, map_intCast]
  have hcn : ∀ (n : ℕ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u := by
    intro n u; rw [map_smulₛₗ, map_natCast]
  refine ⟨b, ⟨hbL, fun z hz' => ?_⟩, fun i => ?_⟩
  · let Z : I.Lf := ⟨iv I z, DictLat.iv_mem I hz'⟩
    let c : Fin N → ℤ := fun j => ((fr.c Z j).val : ℤ)
    refine ⟨c, inter I w ?_⟩
    rw [iv_lin]
    have e0 : fr.c (Z - ∑ j, ((c j : ℤ) : IntAf I.F I.E) • B j) = 0 := by

      rw [map_sub, map_sum, sub_eq_zero]
      simp only [hci, hB]
      funext k
      simp [c, Finset.sum_apply, Pi.single_apply]
    have e1 := (hz _).1 e0
    convert e1 using 1
    simp [Z, B, Submodule.coe_sum]
    rfl
  · let V : I.Lf := ⟨I.fmat x *ᵥ iv I (b i), Inhab.mulVec_mem hx (B i).2⟩
    have hV : fr.c V = M *ᵥ Pi.single i 1 := by rw [← hB i]; exact hM (B i) V.2
    have e0 : fr.c (V - ∑ j, (((M j i).val : ℕ) : IntAf I.F I.E) • B j) = 0 := by

      rw [map_sub, map_sum, sub_eq_zero, hV]
      simp only [hcn, hB, ZMod.natCast_zmod_val]
      funext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    have e1 := (hz _).1 e0
    convert e1 using 1
    rw [Submodule.coe_sub, Submodule.coe_sum]
    refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun j _ => ?_)
    show _ = ((((M j i).val : ℕ) : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) • iv I (b j)
    rw [SubringClass.coe_natCast]
    rfl

end GlobalTheory.RowLev
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open IsDedekindDomain

namespace GlobalTheory.FixedConj

theorem comm_tensCastR_symm_mem_intAf {E : Type} [Field E] [NumberField E] {F₁ F₂ : Subfield E} (h : F₁ = F₂)
    (x : E ⊗[F₂] FiniteAdeleRing (𝓞 F₂) F₂)
    (hx : x ∈ Subring.closure ({x | ∃ y : 𝓞 E, x = (y : E) ⊗ₜ[F₂] (1 : FiniteAdeleRing (𝓞 F₂) F₂)} ∪
      {x | ∃ a : FiniteAdeleRing (𝓞 F₂) F₂, (∀ v, a v ∈ v.adicCompletionIntegers F₂) ∧ x = (1 : E) ⊗ₜ[F₂] a})) :
    (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).toRingEquiv
      ((GlobalTheory.StdFrame.tensCastR h).symm x) ∈ Formalism.L2.Herm.intAf (↥F₁) E := by
  subst h
  have hS : Subring.closure ({x | ∃ y : 𝓞 E, x = (y : E) ⊗ₜ[F₁] (1 : FiniteAdeleRing (𝓞 F₁) F₁)} ∪
      {x | ∃ a : FiniteAdeleRing (𝓞 F₁) F₁, (∀ v, a v ∈ v.adicCompletionIntegers F₁) ∧ x = (1 : E) ⊗ₜ[F₁] a}) ≤
      (Formalism.L2.Herm.intAf (↥F₁) E).comap
        (((GlobalTheory.StdFrame.tensCastR (rfl : F₁ = F₁)).symm.trans
          (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).toRingEquiv : _ ≃+* _) : _ →+* _) := by
    rw [Subring.closure_le]
    rintro z (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · show (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E)
          ((Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).symm ((y : E) ⊗ₜ[F₁] 1)) ∈ _
      rw [AlgEquiv.apply_symm_apply]
      exact Subring.subset_closure (Or.inl ⟨⟨(y : E), ⟨y, rfl⟩⟩, rfl⟩)
    · show (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E)
          ((Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).symm ((1 : E) ⊗ₜ[F₁] a)) ∈ _
      rw [AlgEquiv.apply_symm_apply]
      exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact hS hx

theorem adeleEquiv_mem_intAf : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E),
    a ∈ ReciprocityTheory.Aut.ALint D.host.E → GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
  intro D hF a ha
  exact comm_tensCastR_symm_mem_intAf hF a ha

end GlobalTheory.FixedConj
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.NormConst

theorem two_v_pos (D : D7) : 0 < 2 * D.host.v := by
  show 0 < 2 * (D.host.rdE / 2)
  unfold Formalism.BasicNotions.Host.rdE
  have h0 : (0:ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have := Real.rpow_pos_of_pos h0 (1 / (Module.finrank ℚ D.host.E : ℝ))
  linarith

theorem abs_discr_F (D : D7) : |(NumberField.discr D.host.F : ℝ)| = (2 * D.host.v) ^ D.R.f := by
  have h2v : 2 * D.host.v = D.host.rdE := by show 2 * (D.host.rdE / 2) = D.host.rdE; ring
  rw [h2v]
  obtain ⟨h1, -⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hn := GlobalTheory.RealPlaces.finrank_E D
  have hpos : Module.finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  have key : D.host.rdE ^ (2 * D.R.f) = |(NumberField.discr D.host.F : ℝ)| ^ 2 := by
    rw [← hn]
    unfold Formalism.BasicNotions.Host.rdE
    rw [one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
    have h3 : |(NumberField.discr D.host.E : ℝ)| = (NumberField.discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
    rw [h3, sq_abs]
  have hr0 : 0 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.rdE; positivity
  rw [mul_comm, pow_mul] at key
  exact ((pow_left_inj₀ (pow_nonneg hr0 _) (abs_nonneg _) two_ne_zero).1 key).symm

theorem card_infinitePlace_E (D : D7) : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [← D.what₂.card_Tau]
  exact (Fintype.card_of_bijective
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))).symm

theorem sum_range_closed (k : ℕ) : ∀ n : ℕ,
    (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (4 * ((i : ℝ) + 1) + 2 * k)) =
      2 * (n : ℝ) * (n + 1) * (2 * n + 1) / 3 + k * n * (n + 1)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_closed k n]
    push_cast; ring

theorem sum_exponents (r k : ℕ) :
    (∑ a : Fin r, (((r - (a : ℕ)) * (4 * (r - (a : ℕ)) + 2 * k) : ℕ) : ℝ)) =
      2 * (r : ℝ) * (r + 1) * (2 * r + 1) / 3 + k * r * (r + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (((r - i) * (4 * (r - i) + 2 * k) : ℕ) : ℝ)) r,
    ← Finset.sum_range_reflect, ← sum_range_closed k r]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have e : r - (r - 1 - j) = j + 1 := by omega
  rw [e]; push_cast; ring

end GlobalTheory.CovDom.NormConst

namespace GlobalTheory.CovDom

theorem normalising_constants : ∀ (D : D7), (∀ a, 0 < sc D a) ∧ |(NumberField.discr D.host.F : ℝ)| ^ (-(((D.R.k : ℝ) + 1) * (D.R.rS : ℝ) ^ 2) - 4 * ((D.R.rS : ℝ) ^ 3 - D.R.rS) / 3 - 3 * (D.R.rS : ℝ) / 2) * (∏ a : Fin D.R.rS, sc D a ^ (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k)) ^ Fintype.card (InfinitePlace D.host.E) = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  intro D
  have hv := NormConst.two_v_pos D
  refine ⟨fun a => pow_pos hv _, ?_⟩
  rw [NormConst.card_infinitePlace_E, D.what₂.card_Tau, NormConst.abs_discr_F]
  have hprod : ∏ a : Fin D.R.rS, sc D a ^ (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k) =
      (2 * D.host.v) ^ (∑ a : Fin D.R.rS, (D.R.rS - (a : ℕ)) * (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k)) := by
    unfold sc
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← pow_mul]
  rw [hprod, ← pow_mul, ← Real.rpow_natCast (2 * D.host.v) D.R.f,
    ← Real.rpow_mul hv.le, ← Real.rpow_natCast (2 * D.host.v) (_ * D.R.f), ← Real.rpow_add hv]
  congr 1
  rw [Nat.cast_mul, Nat.cast_sum, NormConst.sum_exponents]
  ring

end GlobalTheory.CovDom
end
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.totalMass_integralLattices_bounded_det_line : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → Module.finrank K V = 1 → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ 1 → ∀ X : ℕ, 1 ≤ X → ∑ n ∈ Finset.Icc 1 (X ^ 2), orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h₁ I₁ * (X : ℝ) ^ (2 + Real.logb 2 (fDeg K))) := by
  first | exact @GlobalTheory.Mass.LineMass.main | exact GlobalTheory.Mass.LineMass.main | (intros; apply GlobalTheory.Mass.LineMass.main <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.exists_subspaceReps_sum_orbitMass_le : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ j : ℕ, 1 ≤ j → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ de : ℕ, 1 ≤ de → ∃ s : Finset (Submodule K V), (∀ U ∈ s, Module.finrank K U = j) ∧ (∀ U : Submodule K V, Module.finrank K U = j → (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)).Nonempty → ∃ U₀ ∈ s, ∃ g : isom h, g • U₀ = U) ∧ ∑ U ∈ s, orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)) ≤ ENNReal.ofReal (mass h₁ I₁ * (de : ℝ) ^ j * (de : ℝ) ^ (2 + Real.logb 2 (fDeg K))) := by
  first | exact @GlobalTheory.Mass.TotalMass.main | exact GlobalTheory.Mass.TotalMass.main | (intros; apply GlobalTheory.Mass.TotalMass.main <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.hermitian_volume_depends_only_on_field_signature : VolumeInvariant := by
  first | exact @GlobalTheory.VolInvariant.volumeInvariant | exact GlobalTheory.VolInvariant.volumeInvariant | (intros; apply GlobalTheory.VolInvariant.volumeInvariant <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.mass_rowLattice_orthogonal_split_prime : ∀ (D : D7) (u : D.what₂.Word), letI := D.host.cmStar; ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → (Lat.Tu D u).Prime → Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) → ∀ Λ : Cnt.LatV D, IsRowLat D F0 Λ → mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) = Cnt.massS D D.R.k * ((((Lat.Tu D u : ℕ) : ℝ) ^ D.R.k - 1) / (((Lat.Tu D u : ℕ) : ℝ) - 1)) ^ D.R.f ∧ Cnt.massS D D.R.k * Cnt.NT D u ^ (D.R.k - 1) ≤ mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) := by
  first | exact @GlobalTheory.Mass.RowPerpMass.main | exact GlobalTheory.Mass.RowPerpMass.main | (intros; apply GlobalTheory.Mass.RowPerpMass.main <;> assumption)
end
