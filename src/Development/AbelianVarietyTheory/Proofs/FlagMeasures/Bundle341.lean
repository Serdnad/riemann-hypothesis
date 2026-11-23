module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle145
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle153
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle049
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle333
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Formalism.PeriodIntegrals.Bundle023
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle323

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.G.FrameClose

variable {I : AutInst}

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

theorem hA_unitary (x : I.Gf) (v w : VA I) :
    Formalism.L2.SG.HidaSetting.hA I (I.fmat x *ᵥ v) (I.fmat x *ᵥ w) = Formalism.L2.SG.HidaSetting.hA I v w := by
  unfold Formalism.L2.SG.HidaSetting.hA
  rw [hform_mulVec_mulVec]
  have h : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
      I.fmat x = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  rw [h]

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp [AutInst.fmat]

theorem hA_move (x : I.Gf) (v w : VA I) :
    Formalism.L2.SG.HidaSetting.hA I v (I.fmat x *ᵥ w) = Formalism.L2.SG.HidaSetting.hA I (I.fmat x⁻¹ *ᵥ v) w := by
  rw [← hA_unitary x (I.fmat x⁻¹ *ᵥ v) w, mulVec_mulVec, fmat_mul_inv, one_mulVec]

theorem hA_sub_left (v v' w : VA I) :
    Formalism.L2.SG.HidaSetting.hA I (v - v') w = Formalism.L2.SG.HidaSetting.hA I v w - Formalism.L2.SG.HidaSetting.hA I v' w := by
  simp only [Formalism.L2.SG.HidaSetting.hA, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hA_nat_left (c : ℕ) (v w : VA I) :
    Formalism.L2.SG.HidaSetting.hA I ((c : I.E ⊗[I.F] Af I.F) • v) w = (c : I.E ⊗[I.F] Af I.F) * Formalism.L2.SG.HidaSetting.hA I v w := by
  simp only [Formalism.L2.SG.HidaSetting.hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast,
    Finset.mul_sum, mul_assoc]

theorem hA_int {v w : VA I} (hv : v ∈ I.Lf) (hw : w ∈ I.Lf) : Formalism.L2.SG.HidaSetting.hA I v w ∈ IntAf I.F I.E :=
  (GlobalTheory.AdelicLattice.adelicLattice_selfDual I w).1 hw v hv

theorem nat_smul_mem (c : ℕ) {v : VA I} (hv : v ∈ I.Lf) : (c : I.E ⊗[I.F] Af I.F) • v ∈ I.Lf := by
  rw [Nat.cast_smul_eq_nsmul]
  exact I.Lf.nsmul_mem hv c

theorem mL_le (g : ℕ) : Formalism.L2.SG.HidaSetting.mL I g ≤ I.Lf := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.RowIndex.mem_mL.1 hx
  exact nat_smul_mem g hz

theorem zmod_of_mL {g : ℕ} {x w : VA I} (hx : x ∈ Formalism.L2.SG.HidaSetting.mL I g) (hw : w ∈ I.Lf) :
    ZMod' I g (Formalism.L2.SG.HidaSetting.hA I x w) := by
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.RowIndex.mem_mL.1 hx
  rw [hA_nat_left]
  exact ⟨_, hA_int hz hw, rfl⟩

theorem den_of_inAt {g : ℕ} {w0 w : VA I} (hw0 : w0 ∈ I.Lf) (h : InAt I g g (w0 - w)) :
    ∃ c : ℕ, Nat.Coprime c g ∧ (c : I.E ⊗[I.F] Af I.F) • w ∈ I.Lf := by
  obtain ⟨c, hc, hm⟩ := h
  refine ⟨c, hc, ?_⟩
  have e : (c : I.E ⊗[I.F] Af I.F) • w = (c : I.E ⊗[I.F] Af I.F) • w0 - (c : I.E ⊗[I.F] Af I.F) • (w0 - w) := by
    rw [smul_sub]; abel
  rw [e]
  exact sub_mem (nat_smul_mem c hw0) (mL_le g hm)

theorem inAt_pair {g : ℕ} {β v0 v w : VA I} (hβ : β ∈ I.Lf) (hv : InAt I g g (v0 - v))
    (h0 : ZMod' I g (Formalism.L2.SG.HidaSetting.hA I v0 β))
    (hw : ∃ c : ℕ, Nat.Coprime c g ∧ (c : I.E ⊗[I.F] Af I.F) • w ∈ I.Lf) :
    InAt I g g (Formalism.L2.SG.HidaSetting.hA I v β • w) := by
  obtain ⟨c1, hc1, h1⟩ := hv
  obtain ⟨t0, ht0, e0⟩ := h0
  obtain ⟨c2, hc2, h2⟩ := hw
  obtain ⟨t1, ht1, e1⟩ := zmod_of_mL h1 hβ
  rw [hA_nat_left, hA_sub_left, e0] at e1
  have key : (c1 : I.E ⊗[I.F] Af I.F) * Formalism.L2.SG.HidaSetting.hA I v β =
      (g : I.E ⊗[I.F] Af I.F) * ((c1 : I.E ⊗[I.F] Af I.F) * t0 - t1) := by
    linear_combination -e1
  have hm : (c1 : I.E ⊗[I.F] Af I.F) * t0 - t1 ∈ IntAf I.F I.E :=
    sub_mem (mul_mem (natCast_mem _ c1) ht0) ht1
  refine ⟨c1 * c2, Nat.Coprime.mul_left hc1 hc2, ?_⟩
  have e : ((c1 * c2 : ℕ) : I.E ⊗[I.F] Af I.F) • (Formalism.L2.SG.HidaSetting.hA I v β • w) =
      ((c1 : I.E ⊗[I.F] Af I.F) * t0 - t1) • ((g : I.E ⊗[I.F] Af I.F) • ((c2 : I.E ⊗[I.F] Af I.F) • w)) := by
    rw [smul_smul, smul_smul, smul_smul, Nat.cast_mul]
    congr 1
    linear_combination (c2 : I.E ⊗[I.F] Af I.F) * key
  rw [e]
  exact (Formalism.L2.SG.HidaSetting.mL I g).smul_mem (⟨_, hm⟩ : IntAf I.F I.E) (Submodule.subset_span ⟨_, h2, rfl⟩)

end GlobalTheory.St.G.FrameClose

namespace GlobalTheory.St.G.FrameClose

variable {D : D7}

theorem transported_close (X : HidaSetting D) (u : D.what₂.Word) {β : VA X.B.I} (hβ : β ∈ X.B.I.Lf)
    (hz : ZMod' X.B.I X.B.g (Formalism.L2.SG.HidaSetting.hA X.B.I X.z0 β))
    (he : ∀ a, ZMod' X.B.I X.B.g (Formalism.L2.SG.HidaSetting.hA X.B.I (X.e0 a) β))
    (hf : ∀ a, ZMod' X.B.I X.B.g (Formalism.L2.SG.HidaSetting.hA X.B.I (X.f0 a) β))
    (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I)
    (H : ∀ y ∈ X.B.I.Lf, (∀ a, InAt X.B.I X.B.g X.B.g
        (Formalism.L2.SG.HidaSetting.hA X.B.I (Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a)) y • Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a)) ∧
        InAt X.B.I X.B.g X.B.g
        (Formalism.L2.SG.HidaSetting.hA X.B.I (Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a)) y • Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a))) →
      InAt X.B.I X.B.g X.B.g
        (Formalism.L2.SG.HidaSetting.hA X.B.I (Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u)) y • Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u)) →
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y - y ∈ Formalism.L2.SG.HidaSetting.mL X.B.I X.B.g) :
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ β) - X.B.I.fmat (X.xu u) *ᵥ β ∈
      Formalism.L2.SG.HidaSetting.mL X.B.I X.B.g := by
  obtain ⟨hef, hz0, -⟩ := X.vectorsInLattice
  refine H _ ((X.xu_K u β).1 hβ) (fun a => ⟨?_, ?_⟩) ?_
  · have hfix : X.B.I.fmat (X.xu u) *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a) =
        Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a) := (X.xu_fix u a).1
    have hu := hA_unitary (X.xu u) (Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a)) β
    rw [hfix] at hu
    rw [hu]
    exact inAt_pair hβ (X.basisApprox a).1 (he a) (den_of_inAt (hef a).2 (X.basisApprox a).2)
  · have hfix : X.B.I.fmat (X.xu u) *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a) =
        Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a) := (X.xu_fix u a).2
    have hu := hA_unitary (X.xu u) (Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a)) β
    rw [hfix] at hu
    rw [hu]
    exact inAt_pair hβ (X.basisApprox a).2 (hf a) (den_of_inAt (hef a).1 (X.basisApprox a).1)
  · rw [hA_move]
    obtain ⟨c', hc', hm⟩ := X.xu_z u
    have hv : InAt X.B.I X.B.g X.B.g
        (X.z0 - X.B.I.fmat (X.xu u)⁻¹ *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u)) := by
      refine ⟨c', hc', ?_⟩
      rw [← neg_sub, smul_neg]
      exact neg_mem hm
    refine inAt_pair hβ hv hz ?_
    obtain ⟨d, hd, hdm⟩ := den_of_inAt hz0 hv
    refine ⟨d, hd, ?_⟩
    have h := (X.xu_K u _).1 hdm
    rwa [mulVec_smul, mulVec_mulVec, fmat_mul_inv, one_mulVec] at h

theorem typeVec_close : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), (∀ y ∈ X.B.I.Lf, (∀ a, InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) ∧ InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a))) → InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u)) → (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y - y ∈ mL X.B.I X.B.g) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) := by
  intro D X u wt ιA _ _ c p H i
  obtain ⟨-, -, hb⟩ := X.vectorsInLattice
  exact ⟨transported_close X u (hb i).1 (X.weightVectorsIntegral i).1 (fun a => ((X.weightVectorsIntegral i).2.2 a).1)
      (fun a => ((X.weightVectorsIntegral i).2.2 a).2.1) c p H,
    transported_close X u (hb i).2 (X.weightVectorsIntegral i).2.1 (fun a => ((X.weightVectorsIntegral i).2.2 a).2.2.1)
      (fun a => ((X.weightVectorsIntegral i).2.2 a).2.2.2) c p H⟩

end GlobalTheory.St.G.FrameClose
end
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.G

theorem trace_cm_eq_add_star {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + star x := by
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hc.deg2
  have : Algebra.IsQuadraticExtension F E := ⟨hc.deg2⟩
  classical
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom hc.sig hc.sig
    (by ext y; simp [Formalism.BasicNotions.CMData.sig]) (by ext y; simp [Formalism.BasicNotions.CMData.sig])
  have hs : ∀ y, s y = star y := fun y => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ s := by
    intro h
    have hall : ∀ y : E, y ∈ (algebraMap F E).range := fun y => (hc.fixed y).1 (by
      rw [← hs, ← h]; rfl)
    have h1 : Module.finrank F E = 1 := by
      apply finrank_eq_one (1 : E) one_ne_zero
      intro w
      obtain ⟨a, ha⟩ := hall w
      exact ⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩
    rw [hc.deg2] at h1
    omega
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hc.deg2]
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  rw [trace_eq_sum_automorphisms, huniv, Finset.sum_pair hne, hs]
  rfl

theorem psiEinf_eq_exp_trace (I : Formalism.MainNotions.S.AutInst) (y : I.E) :
    psiEinf I y = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ I.E y : ℚ) : ℂ)) := by
  have := I.cm.totReal
  rw [show psiEinf I y = PI.ScPsiExists.psiEinf I y from rfl, PI.ScPsiExists.UnitaryGroupMassFormula.psiEinf_eq,
    PI.ScPsiExists.UnitaryGroupMassFormula.sHom_coe]
  have h2 : ∀ v, I.φ v y + star (I.φ v y) =
      v.embedding (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y) := by
    intro v
    rw [← I.φ_over, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add (f := _), I.cm.cmUnram.2.1 (I.φ v) y]
    rfl
  have h3 : PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y = Algebra.trace I.F I.E y := by
    apply (algebraMap I.F I.E).injective
    rw [PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, trace_cm_eq_add_star I.cm]
  rw [Finset.sum_congr rfl (fun v _ => h2 v), PI.ScPsiExists.UnitaryGroupMassFormula.sum_embedding_eq_trace, h3,
    Algebra.trace_trace]
  rfl

theorem psiEf_transport_rat : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ x : D.host.E, X.psiEf (ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x)) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ)) = 1 := by
  intro D X ιA hA x
  have h1 : ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm x) := by
    rw [RingEquiv.symm_apply_eq, hA.1 (X.ιE.symm x), X.ιE.apply_symm_apply]
  have htr : Algebra.trace ℚ D.host.E x = Algebra.trace ℚ X.B.I.E (X.ιE.symm x) := by
    conv_lhs => rw [← X.ιE.apply_symm_apply x]
    exact Algebra.trace_eq_of_algEquiv X.ιE.toRatAlgEquiv (X.ιE.symm x)
  rw [h1, htr, ← psiEinf_eq_exp_trace]
  exact X.psiEf_rat (X.ιE.symm x)

end GlobalTheory.St.G

end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain

namespace GlobalTheory.HL.UniExt

theorem exists_equiv_of_indep {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent K v) (B : Matrix (Fin n) (Fin n) K) (hB : IsUnit B.det) :
    ∃ N : V ≃ₗ[K] V, ∀ b, N (v b) = ∑ a, B a b • v a := by
  classical
  set W := Submodule.span K (Set.range v) with hW
  let bW : Module.Basis (Fin n) K W := Module.Basis.span hv
  let φ : W ≃ₗ[K] W := Matrix.toLinearEquiv bW B hB
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  let e : (W × C) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl W C hC
  refine ⟨e.symm.trans ((LinearEquiv.prodCongr φ (LinearEquiv.refl K C)).trans e), fun b => ?_⟩
  have hvb : v b = ((bW b : W) : V) := (Module.Basis.coe_span_apply hv b).symm
  have h1 : e.symm (v b) = (bW b, 0) := by
    rw [LinearEquiv.symm_apply_eq, hvb]
    simp [e]
  have h2 : φ (bW b) = ∑ a, B a b • bW a := by
    simp [φ, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have h3 : ∀ a, ((bW a : W) : V) = v a := fun a => Module.Basis.coe_span_apply hv a
  rw [LinearEquiv.trans_apply, h1, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl', h2]
  simp [h3]

theorem indep_frames {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) :
    LinearIndependent E (Sum.elim G.f G.f') := by
  classical
  set g : Fin (r + 1) ⊕ Fin (r + 1) → Fin (k + 2 * r + 1) → E := Sum.elim G.f G.f' with hg
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  obtain ⟨-, -, -, -, -, hind⟩ := GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  obtain ⟨hli, -, -⟩ := GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)
  set S := G.S p with hS
  set Ep := (A.loc p).Ep
  let s : Fin (r + 1) ⊕ Fin (r + 1) → Epˣ := fun q =>
    Units.map (algebraMap (A.loc p).Fp Ep).toMonoidHom (G.c p ^ (r - (Sum.elim (fun a : Fin (r + 1) => (a : ℕ)) (fun a => (a : ℕ)) q)))
  have hu : ∀ q, A.bc p (g q) = ((s q : Epˣ) : Ep) • Sum.elim S.f S.f' q := by
    intro q
    rcases q with a | a
    · simp only [hg, Sum.elim_inl, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f_eq p a).symm
    · simp only [hg, Sum.elim_inr, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f'_eq p a).symm
  let e := (finSumFinEquiv (m := r + 1) (n := r + 1))
  refine (linearIndependent_equiv e.symm).1 ((hind _ (g ∘ e.symm)).2 ?_)
  have : (fun q => A.bc p (g q)) = s • Sum.elim S.f S.f' := by
    funext q; rw [hu]; rfl
  have h2 : LinearIndependent Ep (fun q => A.bc p (g q)) := by
    rw [this]; exact hli.units_smul s
  exact (linearIndependent_equiv e.symm).2 h2

theorem det_isUnit_of_unitri {E : Type} [Field E] {n : ℕ} (B : Matrix (Fin n) (Fin n) E)
    (hB : ∀ i j, j < i → B i j = 0) (hB1 : ∀ i, B i i = 1) : IsUnit B.det := by
  have hbt : B.BlockTriangular id := fun i j h => hB i j h
  rw [Matrix.det_of_upperTriangular hbt]
  simp [hB1]

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ i j, j < i → B i j = 0) → (∀ i, B i i = 1) → (∃ N : G.GLV, ∀ b, N (G.f b) = ∑ a, B a b • G.f a) ∧ (∃ N : G.GLV, ∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) := by
  intro F E _ _ _ _ _ sig A r k G B hB hB1
  have hdet := det_isUnit_of_unitri B hB hB1
  have hi := indep_frames A r k G
  exact ⟨exists_equiv_of_indep (K := E) (V := G.V) G.f (hi.comp Sum.inl Sum.inl_injective) B hdet,
    exists_equiv_of_indep (K := E) (V := G.V) G.f' (hi.comp Sum.inr Sum.inr_injective) B hdet⟩

end GlobalTheory.HL.UniExt
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SlocCoef

theorem rationalDualPairing_eq_scaledLocalPairing {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) {r k : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : Frames (A.L p) r k) (Hm : Matrix (Fin (k + 2 * r + 1)) (Fin (k + 2 * r + 1)) E)
    (c : ((A.loc p).Fp)ˣ) (hHm : S.Hm = Hm.map (A.loc p).ιE)
    (fv : Fin (r + 1) → Fin (k + 2 * r + 1) → E) (ev : Fin r → Fin (k + 2 * r + 1) → E)
    (Sf : Fin (r + 1) → Fin (k + 2 * r + 1) → (A.loc p).Ep) (Se : Fin r → Fin (k + 2 * r + 1) → (A.loc p).Ep)
    (hfe : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ))) • Sf a = A.bc p (fv a))
    (hee : ∀ a : Fin r, Se a = algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (ev a))
    (hd : ∀ a j, hf (A.L p) S.Hm (Sf a) (Se j) = if a = j.castSucc then 1 else 0)
    (b : Fin (r + 1)) (a : Fin r) :
    ∑ i, ∑ j, fv b i * Hm i j * sig (ev a j) = if b = a.castSucc then 1 else 0 := by
  haveI := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
  set α : ℕ → (A.loc p).Ep := fun n => algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - n)) with hα
  have hu : ∀ n, IsUnit (α n) := fun n => ((c.isUnit.pow _)).map _
  have key := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 Hm (fv b) (ev a)
  have h1 : hf (A.L p) S.Hm (A.bc p (fv b)) (Se a) = α b * (if b = a.castSucc then 1 else 0) := by
    rw [← hfe b, ← hd b a]
    simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : hf (A.L p) S.Hm (A.bc p (fv b)) (Se a) = (A.loc p).ιE (∑ i, ∑ j, fv b i * Hm i j * sig (ev a j)) * α a := by
    rw [hee a, ← key, hHm]
    simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.sum_mul, hα]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1] at h2
  split_ifs at h2 ⊢ with hb
  · subst hb
    have ha : ((a.castSucc : Fin (r + 1)) : ℕ) = (a : ℕ) := Fin.coe_castSucc a
    rw [ha, mul_one] at h2
    have h3 : (A.loc p).ιE (∑ i, ∑ j, fv a.castSucc i * Hm i j * sig (ev a j)) = (A.loc p).ιE 1 := by
      rw [map_one]
      exact (hu (a : ℕ)).mul_right_cancel (by rw [one_mul]; exact h2.symm)
    exact (A.loc p).ιE.injective h3
  · rw [mul_zero] at h2
    have h3 := ((hu (a : ℕ)).mul_left_eq_zero).mp h2.symm
    exact (A.loc p).ιE.injective (by rw [h3, map_zero])

end GlobalTheory.SlocCoef

namespace GlobalTheory.SlocCoef

theorem pair_f_es {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (b : Fin (r + 1)) (a : Fin r) :
    ∑ i, ∑ j, G.f b i * G.Hm i j * sig (G.es a j) = if b = a.castSucc then 1 else 0 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  exact rationalDualPairing_eq_scaledLocalPairing A p (G.S p) G.Hm (G.c p) (G.Hm_eq p) G.f G.es (G.S p).f (G.S p).es
    (G.f_eq p) (G.es_eq p) (G.S p).dual b a

theorem pair_f'_es' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (b : Fin (r + 1)) (a : Fin r) :
    ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.es' a j) = if b = a.castSucc then 1 else 0 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  exact rationalDualPairing_eq_scaledLocalPairing A p (G.S p) G.Hm (G.c p) (G.Hm_eq p) G.f' G.es' (G.S p).f' (G.S p).es'
    (G.f'_eq p) (G.es'_eq p) (G.S p).dual' b a

theorem coef_sum {E : Type} [Field E] [NumberField E] (sig : E → E) {r n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (fv : Fin (r + 1) → Fin n → E) (ev : Fin r → Fin n → E)
    (hd : ∀ b a, ∑ i, ∑ j, fv b i * Hm i j * sig (ev a j) = if b = a.castSucc then 1 else 0)
    (N : (Fin n → E) ≃ₗ[E] (Fin n → E)) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hN : ∀ b, N (fv b) = ∑ a, B a b • fv a) :
    (∑ a : Fin r, ∑ i, ∑ j, N (fv a.succ) i * Hm i j * sig (ev a j)) = Formalism.L2.SG.PairVal.sgUp B := by
  have h1 : ∀ a : Fin r, ∑ i, ∑ j, N (fv a.succ) i * Hm i j * sig (ev a j) = B a.castSucc a.succ := by
    intro a
    rw [hN]
    have e : ∀ i j, (∑ c, B c a.succ • fv c) i * Hm i j * sig (ev a j) =
        ∑ c, B c a.succ * (fv c i * Hm i j * sig (ev a j)) := by
      intro i j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    simp_rw [e]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hd]
    simp
  rw [Finset.sum_congr rfl fun a _ => h1 a]
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, lt_self_iff_false, dif_neg, not_false_eq_true, add_zero,
    add_lt_add_iff_right, Fin.is_lt, dif_pos]
  refine Finset.sum_congr rfl fun a _ => ?_
  rfl

end GlobalTheory.SlocCoef

theorem GlobalTheory.SlocCoef.main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (N : G.GLV), ((∀ b, N (G.f b) = ∑ a, B a b • G.f a) → (∑ a : Fin r, ∑ i, ∑ j, N (G.f a.succ) i * G.Hm i j * sig (G.es a j)) = Formalism.L2.SG.PairVal.sgUp B) ∧ ((∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) → (∑ a : Fin r, ∑ i, ∑ j, N (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) = Formalism.L2.SG.PairVal.sgUp B) := by
  intro F E _ _ _ _ _ sig A r k G B N
  exact ⟨GlobalTheory.SlocCoef.coef_sum sig G.Hm G.f G.es (GlobalTheory.SlocCoef.pair_f_es G) N B,
    GlobalTheory.SlocCoef.coef_sum sig G.Hm G.f' G.es' (GlobalTheory.SlocCoef.pair_f'_es' G) N B⟩
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselModelTransport_conj_placeMatrices : ∀ {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s : X.B.I.Ginf) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ τ, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (s (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X)) → ∀ w : InfinitePlace D.host.E, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w) := by
  first | exact @GlobalTheory.CovDomGrp.Transp.transp | exact GlobalTheory.CovDomGrp.Transp.transp | (intros; apply GlobalTheory.CovDomGrp.Transp.transp <;> assumption)
end
