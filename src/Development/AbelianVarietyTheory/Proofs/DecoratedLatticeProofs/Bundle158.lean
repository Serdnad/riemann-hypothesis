module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ConjugationInvariantMeasure
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle136
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFundamentalDomainProdOfKernelImage
import Formalism.LocalRingCardinality.DataHost
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NPartConj

variable (I : Formalism.MainNotions.S.AutInst)

theorem nsmul_mL' {g k : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I} (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) :
    ((k : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • v) ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv k

theorem nsmul_Lf' {k : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I} (hv : v ∈ I.Lf) :
    ((k : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • v) ∈ I.Lf := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv k

theorem mL_le_Lf' (g : ℕ) : Formalism.L2.SG.HidaSetting.mL I g ≤ I.Lf :=
  Submodule.span_le.2 (by rintro _ ⟨y, hy, rfl⟩; exact nsmul_Lf' I hy)

theorem K_mL' {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I}
    (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) : I.fmat x *ᵥ v ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  have h : Formalism.L2.SG.HidaSetting.mL I g ≤
      (Formalism.L2.SG.HidaSetting.mL I g).comap (Formalism.L2.SG.Pf.unitaryCongruence.mvO I (I.fmat x)) :=
    Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      show I.fmat x *ᵥ ((g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • y) ∈ Formalism.L2.SG.HidaSetting.mL I g
      rw [Matrix.mulVec_smul]
      exact Formalism.L2.SG.Pf.unitaryCongruence.smul_mem_mL I (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hx hy))
  exact h hv

theorem K_sub_mL' {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I}
    (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) : (I.fmat x - 1) *ᵥ v ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]; exact sub_mem (K_mL' I hx hv) hv

theorem hcn_of {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {n N N0 : Formalism.L2.SG.HidaSetting.VA I}
    (hN : I.fmat x *ᵥ N0 = N) {c : ℕ}
    (h : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (n - N0) ∈ Formalism.L2.SG.HidaSetting.mL I g) :
    (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N ∈
      Formalism.L2.SG.HidaSetting.mL I g := by
  have e : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N =
      I.fmat x *ᵥ ((c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (n - N0)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hN, smul_sub]
  rw [e]; exact K_mL' I hx h

theorem conj_sub (x m : I.Gf) (n : Formalism.L2.SG.HidaSetting.VA I) :
    (I.fmat (x⁻¹ * m * x) - 1) *ᵥ n = I.fmat x⁻¹ *ᵥ ((I.fmat m - 1) *ᵥ (I.fmat x *ᵥ n)) := by
  rw [Formalism.L2.SG.Pf.unitaryCongruence.fmat_mul, Formalism.L2.SG.Pf.unitaryCongruence.fmat_mul]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul, Matrix.one_mulVec]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul, Matrix.sub_mulVec,
    Matrix.one_mulVec]

theorem term_cong {g : ℕ} {x m : I.Gf} (hx : x ∈ I.Kset) (hm : m ∈ I.Kset)
    {f F n N : Formalism.L2.SG.HidaSetting.VA I} (hf : f ∈ I.Lf) (hn : n ∈ I.Lf) (hFx : I.fmat x *ᵥ F = F) {c : ℕ}
    (hcf : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (f - F) ∈ Formalism.L2.SG.HidaSetting.mL I g)
    (hcn : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N ∈
      Formalism.L2.SG.HidaSetting.mL I g) :
    Formalism.L2.SG.HidaSetting.ZMod' I g (((c * c : ℕ) : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) *
      (Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) -
        Formalism.L2.SG.HidaSetting.hA I F ((I.fmat m - 1) *ᵥ N))) := by
  set C : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) with hC
  have e1 : Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) =
      Formalism.L2.SG.HidaSetting.hA I (I.fmat x *ᵥ f) ((I.fmat m - 1) *ᵥ (I.fmat x *ᵥ n)) := by
    rw [conj_sub, PIW.NormChiNBi.hA_left_inv, inv_inv]
  have hsig : Formalism.L2.SG.HidaSetting.sigA I C = C := by rw [hC, map_natCast]
  have esc : ∀ u v : Formalism.L2.SG.HidaSetting.VA I, Formalism.L2.SG.HidaSetting.hA I (C • u) ((I.fmat m - 1) *ᵥ (C • v)) =
      C * C * Formalism.L2.SG.HidaSetting.hA I u ((I.fmat m - 1) *ᵥ v) := by
    intro u v
    rw [Matrix.mulVec_smul, PIW.NormChiNBi.hA_smul_left, PIW.NormChiNBi.hA_smul_right, hsig]; ring
  have hδf : C • (I.fmat x *ᵥ f) - C • F ∈ Formalism.L2.SG.HidaSetting.mL I g := by
    have e : C • (I.fmat x *ᵥ f) - C • F = I.fmat x *ᵥ (C • (f - F)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hFx, smul_sub]
    rw [e]; exact K_mL' I hx hcf
  have hA'L : C • F ∈ I.Lf := by
    have e : C • F = C • f - C • (f - F) := by rw [smul_sub]; abel
    rw [e]; exact sub_mem (nsmul_Lf' I hf) (mL_le_Lf' I g hcf)
  have hBL : (I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n)) ∈ I.Lf :=
    Formalism.L2.SG.Pf.unitaryCongruence.K_sub_mv I hm (nsmul_Lf' I (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hx hn))
  have key : ((c * c : ℕ) : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) *
      (Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) -
        Formalism.L2.SG.HidaSetting.hA I F ((I.fmat m - 1) *ᵥ N)) =
      Formalism.L2.SG.HidaSetting.hA I (C • (I.fmat x *ᵥ f) - C • F) ((I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n))) +
      Formalism.L2.SG.HidaSetting.hA I (C • F) ((I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n) - C • N)) := by
    rw [PIW.NormChiNBi.hA_sub_left, Matrix.mulVec_sub, PIW.NormChiNBi.hA_sub_right, e1, esc, esc, esc, Nat.cast_mul]
    ring
  rw [key]
  obtain ⟨s, hs, hs'⟩ := PIW.NormChiNBi.hA_mL_left I g hδf hBL
  obtain ⟨t, ht, ht'⟩ := PIW.NormChiNBi.hA_mL_right I g (K_sub_mL' I hm hcn) hA'L
  exact ⟨s + t, add_mem hs ht, by rw [hs', ht', mul_add]⟩

end GlobalTheory.NPartConj

namespace GlobalTheory.NPartConj

theorem term_each (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf)
    (hm : m ∈ X.B.I.Kset) (a : Fin D.R.rS) :
    ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) -
        hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  obtain ⟨c1, hc1, h1⟩ := (X.basisApprox a).2
  have hFx : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := (X.xu_fix u a).2
  have hx := X.xu_K u
  obtain ⟨c2, hc2, N0, hN0, h2⟩ : ∃ c2 : ℕ, Nat.Coprime c2 X.B.g ∧ ∃ N0 : VA X.B.I,
      X.B.I.fmat (X.xu u) *ᵥ N0 = incl X.B.I (nxt X.eR (X.zR u) a) ∧
      ((c2 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (nxt X.e0 X.z0 a - N0)) ∈ mL X.B.I X.B.g := by
    unfold nxt
    split_ifs with h
    · obtain ⟨c2, hc2, h2⟩ := (X.basisApprox ⟨a.1 + 1, h⟩).1
      exact ⟨c2, hc2, _, (X.xu_fix u _).1, h2⟩
    · obtain ⟨c2, hc2, h2⟩ := X.xu_z u
      refine ⟨c2, hc2, X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u), ?_, ?_⟩
      · rw [Matrix.mulVec_mulVec, PIW.NormChiNBi.fmat_mul_inv', Matrix.one_mulVec]
      · have h3 := neg_mem h2
        rwa [← smul_neg, neg_sub] at h3
  have hcop : Nat.Coprime (c1 * c2) X.B.g := Nat.Coprime.mul_left hc1 hc2
  refine ⟨(c1 * c2) * (c1 * c2), Nat.Coprime.mul_left hcop hcop, ?_⟩
  have hcf : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (X.f0 a - incl X.B.I (X.fR a)) ∈
      mL X.B.I X.B.g := by
    rw [Nat.cast_mul, mul_comm, mul_smul]; exact nsmul_mL' X.B.I h1
  have hcN : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (nxt X.e0 X.z0 a - N0) ∈
      mL X.B.I X.B.g := by
    rw [Nat.cast_mul, mul_smul]; exact nsmul_mL' X.B.I h2
  exact term_cong X.B.I hx hm (X.vectorsInLattice.1 a).2 (PIW.NormChiNBi.nxt_mem X a) hFx hcf
    (hcn_of X.B.I hx hN0 hcN)

theorem nsum_cong : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf), m ∈ X.B.I.Kset → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ a, (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) - hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  intro D X u m hm
  choose c hc h using term_each D X u m hm
  refine ⟨∏ a, c a, Nat.Coprime.prod_left fun a _ => hc a, ?_⟩
  rw [Finset.mul_sum]
  refine Formalism.L2.SG.Pf.unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ a)
  rw [hk]
  have e : ∀ T : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F,
      ((c a * k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T =
        (k : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((c a : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T) := by
    intro T; push_cast; ring
  rw [e]
  exact Formalism.L2.SG.Pf.unitaryCongruence.Z_smul X.B.I X.B.g (natCast_mem _ k) (h a)

end GlobalTheory.NPartConj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MuSHaar

open scoped Pointwise

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Sinf Formalism.L2.SG.PoincareInHH.PoincareSetting

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

theorem muN_conj (h : X.B.I.Ginf) (hh : h ∈ Hinf X u) :
    (X.muN u).map (fun x => h * x * h⁻¹) = X.muN u := by
  have hNc : IsClosed (X.NinfU u) := isClosed_ninfU X u
  have hHc : IsCompact ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := hinf_compact X u
  obtain ⟨-, hfin, hpos⟩ := haarOnSet_isHaar_inst X.B.I (NinfSub X.eR (X.zR u)) (isClosed_ninfU X u)
    (X.muN u) (X.muN_haar u)
  have hgN : QPK.IsGrp (X.NinfU u) :=
    ⟨(NinfSub X.eR (X.zR u)).one_mem, fun a ha b hb => (NinfSub X.eR (X.zR u)).mul_mem ha hb,
      fun a ha => (NinfSub X.eR (X.zR u)).inv_mem ha⟩
  have hgH : QPK.IsGrp ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) :=
    ⟨(Hinf X u).one_mem, fun a ha b hb => (Hinf X u).mul_mem ha hb, fun a ha => (Hinf X u).inv_mem ha⟩
  exact QPK.conjugation_invariant_measure X.B.I.Ginf (X.NinfU u) _ hNc hHc hgN hgH
    (fun h hh m hm => conj_ninf X u hh hm) (X.muN u) (X.muN_haar u) ⟨fun K hK => hfin K hK⟩
    (fun U hU hne => (hpos U hU hne).ne') h hh

theorem muS_compact {K : Set X.B.I.Ginf} (hK : IsCompact K) :
    ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) K < ⊤ := by
  haveI := (X.muN_haar u).1
  haveI := (X.muH_haar u).1
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  set L : Set X.B.I.Ginf := (K * ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)⁻¹) ∩ X.NinfU u with hL
  have hLc : IsCompact L := (hK.mul (hinf_compact X u).inv).inter_right (isClosed_ninfU X u)
  rw [Measure.map_apply hmul hK.isClosed.measurableSet]
  calc ((X.muN u).prod (X.muH u)) ((fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) ⁻¹' K)
      ≤ ((X.muN u).prod (X.muH u)) (L ×ˢ Set.univ) := by
        refine measure_mono_ae ?_
        filter_upwards [ae_NH X u] with p hp hpK
        refine ⟨⟨?_, hp.1⟩, Set.mem_univ _⟩
        have e : p.1 = (p.1 * p.2) * p.2⁻¹ := by group
        rw [e]
        exact Set.mul_mem_mul hpK (Set.inv_mem_inv.2 hp.2)
    _ = X.muN u L * X.muH u Set.univ := Measure.prod_prod _ _
    _ < ⊤ := ENNReal.mul_lt_top (muN_compact X u hLc) (hFinite_holds X u)

theorem muS_isHaarOnSet : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  intro D X u
  obtain ⟨hNσ, hN0, -, hNinv⟩ := X.muN_haar u
  obtain ⟨hHσ, hH0, -, hHinv⟩ := X.muH_haar u
  haveI := hNσ
  haveI := hHσ
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI : IsFiniteMeasureOnCompacts (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) :=
      ⟨fun K hK => muS_compact X u hK⟩
    infer_instance
  · intro h0
    have h1 := congrArg (fun μ : Measure X.B.I.Ginf => μ Set.univ) h0
    simp only [Measure.map_apply hmul MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero,
      Pi.zero_apply] at h1
    rw [← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero, Measure.measure_univ_eq_zero,
      Measure.measure_univ_eq_zero] at h1
    exact h1.elim hN0 hH0
  · exact ae_iff.1 (Formalism.L2.SG.WuDecayPf.muSOn X u)
  · intro s hs
    obtain ⟨h0, hh0, n0, hn0, rfl⟩ := levi X u hs
    have hf : (X.muN u).map (fun x => h0 * (n0 * x) * h0⁻¹) = X.muN u := by
      have e : (fun x => h0 * (n0 * x) * h0⁻¹) = (fun x => h0 * x * h0⁻¹) ∘ (fun x => n0 * x) := rfl
      rw [e, ← Measure.map_map (by fun_prop) (by fun_prop), hNinv n0 hn0, muN_conj X u h0 hh0]
    have hg : (X.muH u).map (fun y => h0 * y) = X.muH u := hHinv h0 hh0
    have hfm : Measurable (fun x : X.B.I.Ginf => h0 * (n0 * x) * h0⁻¹) := by fun_prop
    have hgm : Measurable (fun y : X.B.I.Ginf => h0 * y) := by fun_prop
    calc (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)).map (fun x => h0 * n0 * x)
        = ((X.muN u).prod (X.muH u)).map ((fun x => h0 * n0 * x) ∘ (fun p => p.1 * p.2)) :=
          Measure.map_map (by fun_prop) hmul
      _ = ((X.muN u).prod (X.muH u)).map ((fun p => p.1 * p.2) ∘
            Prod.map (fun x => h0 * (n0 * x) * h0⁻¹) (fun y => h0 * y)) := by
          congr 1; funext p; simp only [Function.comp, Prod.map]; group
      _ = (((X.muN u).prod (X.muH u)).map
            (Prod.map (fun x => h0 * (n0 * x) * h0⁻¹) (fun y => h0 * y))).map (fun p => p.1 * p.2) :=
          (Measure.map_map hmul (hfm.prodMap hgm)).symm
      _ = (((X.muN u).map (fun x => h0 * (n0 * x) * h0⁻¹)).prod ((X.muH u).map (fun y => h0 * y))).map
            (fun p => p.1 * p.2) := by rw [Measure.map_prod_map _ _ hfm hgm]
      _ = ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) := by rw [hf, hg]

end GlobalTheory.MuSHaar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.dependent_frame_first_column_relation : ∀ (E : Type) [Field E] (n ρ : ℕ) (x : Matrix (Fin n) (Fin ρ) E), (¬ LinearIndependent E x.transpose ↔ ∃ j : Fin ρ, (∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ∧ (∀ j j' : Fin ρ, ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) → ((∀ a : Fin ρ → E, (∀ i, j' ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j' = 1 ∧ (∀ i, j' < i → a i = 0) ∧ x *ᵥ a = 0) → j = j') ∧ ∀ (j : Fin ρ) (u : Matrix (Fin ρ) (Fin ρ) E), (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → (((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ↔ ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → (x * u) *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ (x * u) *ᵥ a = 0)) := by
  first | exact @GlobalTheory.DepFrame.dependent_frame_first_relation | exact GlobalTheory.DepFrame.dependent_frame_first_relation | (intros; apply GlobalTheory.DepFrame.dependent_frame_first_relation <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image : ∀ (N G : Type) [Group N] [Group G] [MeasurableSpace N] [MeasurableSpace G] [MeasurableMul N] [MeasurableMul G] (ν : Measure N) (μ : Measure G) [SFinite ν] [SFinite μ] [ν.IsMulLeftInvariant] [μ.IsMulLeftInvariant] (Γ : Subgroup (N × G)) [Countable Γ] (𝓐 : Set N) (𝓑 : Set G), IsFundamentalDomain (Γ.comap (MonoidHom.inl N G)) 𝓐 ν → IsFundamentalDomain (Γ.map (MonoidHom.snd N G)) 𝓑 μ → IsFundamentalDomain Γ (𝓐 ×ˢ 𝓑) (ν.prod μ) := by
  first | exact @GlobalTheory.isFundamentalDomain_prod_of_ker_image | exact GlobalTheory.isFundamentalDomain_prod_of_ker_image | (intros; apply GlobalTheory.isFundamentalDomain_prod_of_ker_image <;> assumption)
end
