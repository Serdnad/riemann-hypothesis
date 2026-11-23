module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle086
public import Formalism.LocalRingCardinality.DataHost
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.MiTop

theorem lattice_ratio_vector_of_scalar_factorisation {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (e c θ θ' : R)
    (X X' Sm Sm' Kk Z : GL n R) (hZ : Z.val = c • (1 : Matrix n n R))
    (hT : X⁻¹ * Sm = Z * (X'⁻¹ * Sm') * Kk) (zY zY' Γ : n → R)
    (hm : e • Matrix.mulVec (Sm⁻¹).val zY = e • (θ • Γ)) (hm' : e • Matrix.mulVec (Sm'⁻¹).val zY' = e • (θ' • Γ)) :
    e • ((θ * c) • Matrix.mulVec ((X'⁻¹ * Sm') * Kk * (X'⁻¹ * Sm')⁻¹).val (Matrix.mulVec (X'⁻¹).val zY')) =
      e • (θ' • Matrix.mulVec (X⁻¹).val zY) := by
  set M := (X'⁻¹ * Sm') * Kk * (X'⁻¹ * Sm')⁻¹ with hM
  have hg : Z * M * X'⁻¹ = (X⁻¹ * Sm) * Sm'⁻¹ := by
    rw [hM, hT]; group
  have h2 : c • Matrix.mulVec M.val (Matrix.mulVec (X'⁻¹).val zY') = Matrix.mulVec (Z * M * X'⁻¹).val zY' := by
    have : (Z * M * X'⁻¹).val = c • (M.val * (X'⁻¹).val) := by
      rw [Units.val_mul, Units.val_mul, hZ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [this, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have h3 : e • (θ • Matrix.mulVec (Sm'⁻¹).val zY') = e • (θ' • Matrix.mulVec (Sm⁻¹).val zY) := by
    rw [smul_comm e θ (Matrix.mulVec (Sm'⁻¹).val zY'), hm', smul_comm e θ' (Matrix.mulVec (Sm⁻¹).val zY), hm,
      smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [mul_smul, h2, hg, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, h3,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul]
  congr 3
  group

theorem redFn_scalar_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Formalism.L2.DIV.Pl E)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (c : E ⊗[F] Formalism.L2.Herm.Af F) (hx : x ∈ Formalism.L2.DIV.St β)
    (hc : x.val = c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (i₀ : Fin n) :
    ∃ hci : c ∈ Formalism.L2.Herm.intAf F E,
      (Formalism.L2.DIV.resS F PP ⟨c, hci⟩ = 1 → Formalism.L2.DIV.redFn β PP x = 1) := by
  obtain ⟨y, rfl⟩ := hx
  have hy : (Formalism.L2.DIV.intGL F E n y).val = c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have e1 : Formalism.L2.DIV.intGL F E n y = β⁻¹ * Formalism.L2.DIV.frGL β y * β := by
      simp only [Formalism.L2.DIV.frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e1, Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hent : ∀ i j, ((y.val i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
      (c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) i j := fun i j => by
    rw [← hy]; rfl
  have hci : c ∈ Formalism.L2.Herm.intAf F E := by
    have h := hent i₀ i₀
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [← h]; exact (y.val i₀ i₀).2
  refine ⟨hci, fun h1 => ?_⟩
  rw [Formalism.L2.DIV.redFn_frGL]
  apply Units.ext
  ext i j
  have hyij : y.val i j = if i = j then ⟨c, hci⟩ else 0 := by
    apply Subtype.ext
    rw [hent i j, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  show Formalism.L2.DIV.resS F PP (y.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j
  rw [hyij, Matrix.one_apply]
  split_ifs <;> simp [h1]


end GlobalTheory.MiTop

end
end

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.MiTop.UnitAtLevel

theorem smulOne_mulVec {R : Type} [CommRing R] {n : ℕ} (c : R) (y : Fin n → R) :
    Matrix.mulVec (c • (1 : Matrix (Fin n) (Fin n) R)) y = c • y := by
  funext i
  rw [Matrix.smul_one_eq_diagonal, Matrix.mulVec_diagonal]
  rfl

theorem inv_of_scalar {R : Type} [CommRing R] {n : ℕ} (hn : 0 < n) (A : GL (Fin n) R) (c : R)
    (hA : A.val = c • (1 : Matrix (Fin n) (Fin n) R)) :
    ∃ ι : R, ι * c = 1 ∧ (A⁻¹).val = ι • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : (A⁻¹).val * A.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  rw [hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] at h2
  refine ⟨(A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩, by rw [mul_comm]; exact h2, ?_⟩
  have h3 : A.val * ((A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩ • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
    rw [hA, Matrix.smul_mul, Matrix.one_mul, smul_smul, h2, one_smul]
  calc (A⁻¹).val = (A⁻¹).val * (A.val * ((A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩ • (1 : Matrix (Fin n) (Fin n) R))) := by
        rw [h3, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem mem_of_shift {R : Type} [CommRing R] (O : Subring R) (a u ι : R) (ha : ∃ a', a' * a = 1) (hι : ι * u = 1)
    (key : ∀ c, a * c ∈ O ↔ a * (ι * c) ∈ O) : u ∈ O ∧ ι ∈ O := by
  obtain ⟨a', ha'⟩ := ha
  have e1 : a * a' = 1 := by rw [mul_comm]; exact ha'
  have e2 : a * (ι * a') = ι := by linear_combination ι * e1
  have e3 : a * (ι * (a' * u)) = 1 := by linear_combination (ι * u) * e1 + hι
  have e4 : a * (a' * u) = u := by linear_combination u * e1
  constructor
  · have := (key (a' * u)).2 (by rw [e3]; exact O.one_mem)
    rwa [e4] at this
  · have := (key a').1 (by rw [e1]; exact O.one_mem)
    rwa [e2] at this

end GlobalTheory.MiTop.UnitAtLevel

namespace GlobalTheory.MiTop


end GlobalTheory.MiTop

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FinPl.AwayLevel.single_natCast_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (T : ℕ) (j b : Fin n) [Decidable (b = j)] :
    (Pi.single j (T : K) : Fin n → K) b = ((if b = j then (T : 𝓞 K) else 0 : 𝓞 K) : K) := by
  by_cases hb : b = j
  · subst hb
    simp
  · simp [hb]

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoPlace

theorem exists_prime_mem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (n : ℕ) (hn : n ≠ 0)
    (h : (n : A) ∈ P) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : A) ∈ P :=
  _root_.GlobalTheory.ExistsPrimeMem.exists_prime_mem P hP n hn h

theorem exists_prime_mem_pl {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 E) ∈ PP.asIdeal :=
  exists_prime_mem PP.asIdeal PP.isPrime _ (fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem _)

end GlobalTheory.XGeoPlace
end
end
