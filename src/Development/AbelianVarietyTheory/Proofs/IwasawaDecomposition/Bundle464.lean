module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle111
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle452
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle264
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle802
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle807
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Formalism.LocalToGlobal.HermitianForms.Bundle008
public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle451
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle403
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle416
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle454
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle437
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle440
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle455
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.weightTensorRepOfEmbeddings_isIrreducible : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → (GlobalTheory.AlgWtF.tenRepF emb lam).IsIrreducible := by
  first | exact @GlobalTheory.AlgWtF.tenRepF_isIrreducible | exact GlobalTheory.AlgWtF.tenRepF_isIrreducible | (intros; apply GlobalTheory.AlgWtF.tenRepF_isIrreducible <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameRedSplit

theorem conj_red_core {R K k ι : Type} [CommRing R] [Field K] [CommRing k] {m : ℕ} (S : Subring R) (O : ValuationSubring K)
    (pr : R →+* K) (φ : O →+* k) (res : S →+* k) (hres : ∀ z : S, ∃ h : pr z ∈ O, res z = φ ⟨_, h⟩)
    (β : GL (Fin m) R) (B B' : Matrix (Fin m) (Fin m) R) (hBB : B * B' = 1)
    (U : Set ι) (Km : ι → Matrix (Fin m) (Fin m) R) (Z : ∀ κ ∈ U, GL (Fin m) S)
    (hZ : ∀ κ (hκ : κ ∈ U), β.1 * (Z κ hκ).1.map S.subtype * (β⁻¹).1 = B * Km κ * B')
    (hsurj : ∀ u : GL (Fin m) O, ∃ κ, ∃ hκ : κ ∈ U, (Km κ).map pr = u.1.map O.subtype) :
    ∃ b : GL (Fin m) k, ∀ κ (hκ : κ ∈ U) (y : GL (Fin m) O), (Km κ).map pr = y.1.map O.subtype →
      (Z κ hκ).1.map res = (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).1 := by
  classical
  obtain ⟨γ, hγ⟩ : ∃ γ : Matrix (Fin m) (Fin m) R, γ = (β⁻¹).1 * B := ⟨_, rfl⟩
  obtain ⟨γ', hγ'⟩ : ∃ γ' : Matrix (Fin m) (Fin m) R, γ' = B' * β.1 := ⟨_, rfl⟩
  have g1 : γ * γ' = 1 := by
    rw [hγ, hγ', Matrix.mul_assoc, ← Matrix.mul_assoc B, hBB, Matrix.one_mul, Units.inv_mul]
  have g2 : γ' * γ = 1 := mul_eq_one_comm.mp g1
  have hZ' : ∀ κ (hκ : κ ∈ U), (Z κ hκ).1.map S.subtype = γ * Km κ * γ' := by
    intro κ hκ
    have e : γ * Km κ * γ' = (β⁻¹).1 * (B * Km κ * B') * β.1 := by
      rw [hγ, hγ']; simp only [Matrix.mul_assoc]
    rw [e, ← hZ κ hκ]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  let c : GL (Fin m) K := ⟨γ.map pr, γ'.map pr, by rw [← Matrix.map_mul, g1, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, g2, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hc : ∀ κ (hκ : κ ∈ U), (c.1 * (Km κ).map pr * (c⁻¹).1) = ((Z κ hκ).1.map S.subtype).map pr := by
    intro κ hκ
    rw [hZ' κ hκ, Matrix.map_mul, Matrix.map_mul]
    rfl
  have hent : ∀ u : GL (Fin m) O, ∀ a b, (c * Matrix.GeneralLinearGroup.map O.subtype u * c⁻¹).1 a b ∈ O := by
    intro u a b
    obtain ⟨κ, hκ, hK⟩ := hsurj u
    have e : (c * Matrix.GeneralLinearGroup.map O.subtype u * c⁻¹).1 = c.1 * (Km κ).map pr * (c⁻¹).1 := by
      rw [hK]; rfl
    rw [e, hc κ hκ, Matrix.map_apply, Matrix.map_apply]
    exact (hres _).1
  have hnorm : ∀ u ∈ Formalism.UG.GLint (Fin m) O.toSubring, c * u * c⁻¹ ∈ Formalism.UG.GLint (Fin m) O.toSubring := by
    rintro _ ⟨u, rfl⟩
    refine GlobalTheory.HeckeStdFacts.mem_GLint_iff.2 ⟨fun a b => hent u a b, fun a b => ?_⟩
    have e : (c * Formalism.UG.bc O.toSubring.subtype u * c⁻¹)⁻¹ = c * Matrix.GeneralLinearGroup.map O.subtype u⁻¹ * c⁻¹ := by
      rw [map_inv]
      group
      rfl
    rw [e]
    exact hent u⁻¹ a b
  obtain ⟨h, ⟨h₀, rfl⟩, hconj⟩ := GlobalTheory.HeckeStdFacts.exists_int_of_normalizes O.valuation O.toSubring
    (fun x => (O.valuation_le_one_iff x).symm) c hnorm
  suffices H : ∀ h₁ : GL (Fin m) O, (∀ x, c * x * c⁻¹ = Matrix.GeneralLinearGroup.map O.subtype h₁ * x *
      (Matrix.GeneralLinearGroup.map O.subtype h₁)⁻¹) → ∃ b : GL (Fin m) k, ∀ κ (hκ : κ ∈ U) (y : GL (Fin m) O),
      (Km κ).map pr = y.1.map O.subtype → (Z κ hκ).1.map res = (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).1 from H h₀ hconj
  intro h₁ hconj'
  refine ⟨Matrix.GeneralLinearGroup.map φ h₁, fun κ hκ y hy => ?_⟩
  ext a b
  obtain ⟨hm, hr⟩ := hres ((Z κ hκ).1 a b)
  have e1 : pr ((Z κ hκ).1 a b : R) = (c * Matrix.GeneralLinearGroup.map O.subtype y * c⁻¹).1 a b := by
    have := congrFun (congrFun (hc κ hκ) a) b
    rw [hy] at this
    exact this.symm
  have e2 : (c * Matrix.GeneralLinearGroup.map O.subtype y * c⁻¹) =
      Matrix.GeneralLinearGroup.map O.subtype (h₁ * y * h₁⁻¹) := by
    rw [hconj']
    simp only [map_mul, map_inv]
  have e3 : (⟨_, hm⟩ : O) = (h₁ * y * h₁⁻¹).1 a b := by
    apply Subtype.ext
    show pr _ = _
    rw [e1, e2]
    rfl
  have e4 : Matrix.GeneralLinearGroup.map φ h₁ * Matrix.GeneralLinearGroup.map φ y * (Matrix.GeneralLinearGroup.map φ h₁)⁻¹ =
      Matrix.GeneralLinearGroup.map φ (h₁ * y * h₁⁻¹) := by
    simp only [map_mul, map_inv]
  rw [Matrix.map_apply, hr, e3, e4]
  rfl

theorem resS_eq_phiR (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (y : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ h : s.proj (y : EAf D) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      resS D.host.F s.w y = GlobalTheory.MtRed.phiR s ⟨_, h⟩ := by
  have hmem : s.proj (y : EAf D) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (GlobalTheory.RowGood.proj_le_one s y.2)
  refine ⟨hmem, ?_⟩
  obtain ⟨a, ha, hφ⟩ := GlobalTheory.MtRed.exists_approx s ⟨_, hmem⟩
  rw [hφ]
  exact GlobalTheory.RowGood.res_eq (rfl : maximalRealSubfield D.host.E = _) s (y : EAf D) y (GlobalTheory.RowGood.tr_rfl _).symm a ha



theorem frameRed_exists : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), R3.StdFrame hF P → IsBaseFrame V β Λ 1 → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)), IsResidue s φ ∧ FrameRed hn P β s φ b := by
  intro D V n hn hF P β Λ hP hβ s
  subst hn
  obtain ⟨⟨β₀, β₀', h01, h10, hmat⟩, hK⟩ := hP
  have hSt : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank, finE V (P.ψ κ) ∈ St β := fun κ hκ =>
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ (P.into κ)).2 ((hK κ).1 hκ)
  have hfin : ∀ κ : Formalism.AUTREP.GAf D.host.E V.rank, (finE V (P.ψ κ)).1 =
      β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * (κ.1.1.map (GlobalTheory.RowGood.tr hF)) *
        β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := by
    intro κ
    have e := congrArg (fun M => Matrix.map M (GlobalTheory.LevSplit.swp D.host.F D.host.E)) (hmat κ)
    refine e.trans ?_
    simp only [Matrix.map_mul]
    rfl
  have hBB : β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) = 1 := by
    rw [← Matrix.map_mul, h01, Matrix.map_one _ (map_zero _) (map_one _)]
  have hZ : ∀ (κ : Formalism.AUTREP.GAf D.host.E V.rank) (hκ : κ ∈ {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank}),
      β.1 * (pullFr β ⟨_, hSt κ hκ⟩).1.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).1 =
        β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * (κ.1.1.map (GlobalTheory.RowGood.tr hF)) *
          β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := by
    intro κ hκ
    exact (congrArg (fun g : GL (Fin V.rank) (EAf D) => g.1) (frGL_pullFr β ⟨_, hSt κ hκ⟩)).trans (hfin κ)
  have hpr : ∀ κ : Formalism.AUTREP.GAf D.host.E V.rank, (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj = (s.loc V.rank κ).1 := by
    intro κ
    ext i j
    simp only [Matrix.map_apply]
    rw [GlobalTheory.RowGood.tr_rfl]
    rfl
  have hsurj : ∀ u : GL (Fin V.rank) (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)),
      ∃ κ : Formalism.AUTREP.GAf D.host.E V.rank, ∃ _ : κ ∈ {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank},
        (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj =
          u.1.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype := by
    intro u
    obtain ⟨x, hx, hloc⟩ := GlobalTheory.SplitSec.exists_trivOutside_loc D.host.E V.rank s
      (Matrix.GeneralLinearGroup.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype u)
    refine ⟨x, (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s hx).1 ⟨u, ?_⟩, ?_⟩
    · exact hloc.symm
    · rw [hpr, hloc]; rfl
  obtain ⟨b, hb⟩ := conj_red_core (R := EAf D) (K := s.v.adicCompletion (maximalRealSubfield D.host.E)) (k := kP s.w)
    (ι := Formalism.AUTREP.GAf D.host.E V.rank) (m := V.rank) (S := Formalism.L2.Herm.intAf D.host.F D.host.E)
    (O := s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (pr := s.proj) (φ := GlobalTheory.MtRed.phiR s)
    (res := resS D.host.F s.w) (hres := resS_eq_phiR D s) (β := β) (hBB := hBB)
    (U := {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank})
    (Km := fun κ => κ.1.1.map (GlobalTheory.RowGood.tr hF))
    (Z := fun κ hκ => pullFr β ⟨_, hSt κ hκ⟩) (hZ := hZ) (hsurj := hsurj)
  refine ⟨GlobalTheory.MtRed.phiR s, b, ⟨GlobalTheory.MtRed.phiR_surj s, GlobalTheory.MtRed.phiR_eq_zero s⟩, fun κ hκ y hy a c => ?_⟩
  have hy' : (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj =
      y.1.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype := by
    rw [hpr]
    exact Matrix.ext fun i j => (hy i j).symm
  have e := congrFun (congrFun (hb κ hκ y hy') a) c
  have hr : redFn β s.w (finE V (P.ψ κ)) = Formalism.UG.bc (resS D.host.F s.w) (pullFr β ⟨_, hSt κ hκ⟩) := by
    have h1 := redFn_frGL β s.w (pullFr β ⟨_, hSt κ hκ⟩)
    rwa [frGL_pullFr] at h1
  rw [← e, hr]
  rfl

end GlobalTheory.FrameRedSplit
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.stdMaximalCompact_reduction_properties : ∀ (D : D7) (n : ℕ), (∀ κ, km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E)) ∧ (∀ κ, km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)) ↔ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n) ∧ (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v) (PP : Pl D.host.E), ReciprocityTheory.Aut.TrivOutside A κ → NG.OverPl PP v → v ∉ A → redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w, Function.Surjective φ ∧ (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) ∧ (∀ a : 𝓞 D.host.E, ∃ h : s.i (a : D.host.E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), φ ⟨_, h⟩ = Ideal.Quotient.mk _ a) ∧ ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ a b, ∃ h : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin n) (EAf D)) s.w (km D n κ)).val a b = φ ⟨_, h⟩ := by
  first | exact @GlobalTheory.MtRed.km_reduction | exact GlobalTheory.MtRed.km_reduction | (intros; apply GlobalTheory.MtRed.km_reduction <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_deeperLevel_iff_matrices_mod_place_symmetric : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (k ∈ X.K2 ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) := by
  first | exact @GlobalTheory.Mem.GroupLoc.membership_iff_unipSym | exact GlobalTheory.Mem.GroupLoc.membership_iff_unipSym | (intros; apply GlobalTheory.Mem.GroupLoc.membership_iff_unipSym <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelLift_gelfandInvariantFinite_of_finite : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∃ Z : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Z ∧ F ∈ Z ∧ ∀ τ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) → ∀ f, ∃ Z : Submodule ℂ (GA D W → ℂ), FiniteDimensional ℂ Z ∧ (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∈ Z ∧ ∀ τ k, ∀ φ ∈ Z, gelf θ W τ k φ ∈ Z := by
  first | exact @GlobalTheory.Mem.LiftFin.lift_zfin | exact GlobalTheory.Mem.LiftFin.lift_zfin | (intros; apply GlobalTheory.Mem.LiftFin.lift_zfin <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section


theorem GlobalTheory.Mem.Col2.TwP.weightedInner_twisted : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ (o : Formalism.L2.Forms.FrP (I.rec7 l Z)), o.IsON → ∀ (z z' : (I.per l u a).Wrow) (Pc Qc : (I.fm l u a).clsP → MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) ℂ), (∀ c, Pc c ∈ CSpan (I.fm l u a).sg) → (∀ c, Qc c ∈ CSpan (I.fm l u a).sg) → (∀ c, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Pc c)) → (∀ c, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z' c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Qc c)) → (I.fm l u a).ipP z z' = ∑ c, ((Nat.card ((I.fm l u a).stabilizer₂ c) : ℕ) : ℂ)⁻¹ * nfAll (I.fm l u a).sg (Qc c) (Pc c) := by
  intro B X I hI hP l Z u a o ho z z' Pc Qc _ _ hz hz'
  have hgP : gramP (I.rec7 l Z) = 1 := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.1
  have hG : ∀ τ, gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z)) τ = 1 := fun τ => by
    rw [hgP, gramC_one]
  have hsh : shiftOf (sgTG (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := by
    refine congrArg shiftOf (funext fun τ => ?_)
    obtain ⟨t, ht⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (t + 1) := by
      rw [ht, show B.R.m * (2 * t + 1 + 1) = 2 * (B.R.m * (t + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = t + 1 := by omega
    show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
    simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.shW]
    congr 1
    funext i
    show ((I.perIn u a).sg τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = ((I.perIn u a).sg τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
    rw [e1, e2]
    push_cast
    ring
  have hl : nfAll (I.perIn u a).sgT = nfAll (I.fm l u a).sg :=
    MetricTie.nfAll_shift _ _ _ fun _ _ => rfl
  show (I.perIn u a).ipP B.fields.emb B.embLL (l.per u a) z z' = _
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : z c = fun s => fnOf _ (shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Pc c) (id s : Formalism.L2.Forms.FrP (I.rec7 l Z)) := hz c
  have e2 : z' c = fun s => fnOf _ (shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Qc c) (id s : Formalism.L2.Forms.FrP (I.rec7 l Z)) := hz' c
  show (I.perIn u a).wt c * ipVal B.fields.emb B.embLL (I.perIn u a).sgT (z c) (z' c) = _
  rw [e1, e2]
  exact congrArg₂ (· * ·) rfl (MetricTie.ipVal_step B.fields.emb B.embLL (I.perIn u a).sgT hl hsh hG id (fun _ => rfl) o ho (Pc c) (Qc c))


theorem GlobalTheory.Mem.Col2.TwP.norm_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (K : ClassesAtPrimes (I.fm l u a) bad) {okW : (I.rec7 l Z).what₂.places.Pl → Prop} (V : ValuationAtPrimes K okW), (∀ z, V.eW z = GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z) → NormPTieG V := by
  intro B X I hI hP l Z u a bad K okW V hV s x Pc hPc o ho
  have hgP : gramP (I.rec7 l Z) = 1 := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := by
    refine congrArg shiftOf (funext fun τ => ?_)
    obtain ⟨t, ht⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (t + 1) := by
      rw [ht, show B.R.m * (2 * t + 1 + 1) = 2 * (B.R.m * (t + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = t + 1 := by omega
    show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
    simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.shW]
    congr 1
    funext i
    show ((I.perIn u a).sg τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = ((I.perIn u a).sg τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
    rw [e1, e2]
    push_cast
    ring
  have hl : nfAll (I.perIn u a).sgT = nfAll (I.fm l u a).sg :=
    MetricTie.nfAll_shift _ _ _ fun _ _ => rfl
  have h := @MetricTie.norm_step _ _ _ _ _ _ _ _ _ _ _ B.fields.emb B.embLL (I.perIn u a).sgT (I.stX a) (base_fOk B)
    (l.per u a).step (l.fmL u a).famP ((I.perIn u a).clFin (l.per u a)) _ hl _ hsh _ _
    (fun τ => by rw [hgP, gramC_one]; rfl) (fun y => (y : Formalism.L2.Forms.FrP (I.rec7 l Z))) (fun _ => rfl) s x Pc
    (fun c z => by
      have e := (congrFun (hV ((I.fm l u a).ptEmb x)) c).symm.trans (hPc c)
      exact congrFun e z) o ho
  refine h.trans (Finset.sum_congr rfl fun c _ => ?_)
  congr 2
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
  rfl



theorem GlobalTheory.Mem.Col2.TwP.forms_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∃ V : ValuationAtPrimes K (okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T), NormPTieG V ∧ ∀ z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → V.eW z c s = z c s' := by
  intro B X I hI hP l Z u a Q K hQ hQv hK
  let V : ValuationAtPrimes K (okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T) :=
    { sg := GlobalTheory.T.rowForms_weight_eq_parameter_sub_rho I hI hP l Z u a
      eW := GlobalTheory.Mem.Col2.TwP.eWt I l Z u a
      ptC := GlobalTheory.T.tupleChain_complexForms_eq_algebraicModularForms I hI hP l Z u a Q K hQ hQv hK
      ipP := GlobalTheory.Mem.Col2.TwP.weightedInner_twisted I hI hP l Z u a
      rat := GlobalTheory.T.tupleChain_forms_rational_iff_frame_values I hI hP l Z u a
      lat := GlobalTheory.T.tuple_integralForms_row_place_by_place I hI hP l Z u a Q K hQ hQv hK }
  refine ⟨V, GlobalTheory.Mem.Col2.TwP.norm_tw I hI hP l Z u a K V fun _ => rfl, fun z c s s' h => ?_⟩
  exact GlobalTheory.Mem.Col2.TwP.eWt_apply I l Z u a z c s s' h

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd

theorem reindex_symm_reindex {κ : Type} [CommRing κ] {a b : ℕ} (e : Fin a ≃ Fin b) (y : GL (Fin a) κ) :
    Units.map (Matrix.reindexAlgEquiv κ κ e.symm).toMonoidHom (Units.map (Matrix.reindexAlgEquiv κ κ e).toMonoidHom y) = y := by
  apply Units.ext
  ext i j
  simp

theorem of_reindex_mem_HK {κ : Type} [CommRing κ] {a n r t m : ℕ} (h : a = n) (hn : n = r + m * t) (hra : r ≤ a)
    (y : GL (Fin a) κ)
    (hy : Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y ∈ Formalism.L2.Col.HK n κ r (List.replicate m t)) :
    y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ Formalism.L2.DIV.upperLeftBlock hra y = 1 := by
  subst h
  rw [reindex_finCongr_rfl] at hy
  obtain ⟨hUT, h1⟩ := Formalism.L2.Col.mem_HK.1 hy
  have hb : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := by
    intro i j hij
    refine hUT (show Formalism.L2.Col.coarse r (List.replicate m t) j.val < Formalism.L2.Col.coarse r (List.replicate m t) i.val from ?_)
    rw [coarse_eq_blkOf hn, coarse_eq_blkOf hn]
    exact hij
  refine ⟨hb, ?_⟩
  apply Units.ext
  rw [Formalism.L2.DIV.upper_block_val_submatrix hra (Formalism.L2.DIV.blockTri_blkOf_le r t hb), Units.val_one]
  ext i j
  rw [Matrix.submatrix_apply, h1 _ _ i.2 j.2]
  simp [Matrix.one_apply, Fin.ext_iff]

theorem of_reindex_mem_HQ {κ : Type} [CommRing κ] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y ∈ Formalism.L2.Col.blockUT n κ r [b]) :
    y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  subst h
  rw [reindex_finCongr_rfl] at hy
  intro i j hij
  refine hy (show Formalism.L2.Col.coarse r [b] j.val < Formalism.L2.Col.coarse r [b] i.val from ?_)
  rw [coarseBlockIndex_eq_twoBlock hn, coarseBlockIndex_eq_twoBlock hn]
  exact hij

theorem redG_ptE_of (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) {U : Set I.ι}
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X')
    (hSt : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈ Formalism.L2.DIV.St L.βX)
    (hz : ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
    (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :
    Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ w =
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) :=
  redAt_reindex (finCongr (rank_X' X)) L.βX hL.beta.2 _ hSt (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz) w.1



theorem mem_J_of_redG_mem_grp : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') (hz : RowAd.ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp →
      h ∈ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J := by
  intro X px I U L hI hL t h hz hred
  have hβ : L.βX = 1 := hL.beta.2
  have hSt : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈ Formalism.L2.DIV.St L.βX := by
    have h1 := reindex_mem_St_one (finCongr (rank_X' X)).symm (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz)
    have e2 : Units.map (Matrix.reindexAlgEquiv (Formalism.IndefR.Lev.EAf X.toD7) (Formalism.IndefR.Lev.EAf X.toD7)
        (finCongr (rank_X' X)).symm).toMonoidHom (ptE X h) = Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) :=
      reindex_symm_reindex _ _
    rw [hβ]
    exact e2 ▸ h1
  have hUA : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈
      Formalism.L2.DIV.UA X.toD7.sp.cm X.toD7.sp.X'.gram := by
    obtain ⟨g, hg⟩ := h.2
    rw [← hg]
    exact GlobalTheory.LevSplit.finE_mem_UA X.toD7.sp.X' g
  have hw : ∀ w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1,
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∈
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1 w).H := fun w => by
    rw [← redG_ptE_of X I L hL t h hSt hz w]
    exact hred w (Set.mem_univ _)
  have hG : ∀ PP ∈ (L.datXt t).Pg,
      Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _)) ∈
                Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (L.datXt t).r (L.datXt t).t) ∧
        Formalism.L2.DIV.upperLeftBlock (L.datXt t).hr
          (Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) = 1 := by
    intro PP hPP
    have hP : PP ∈ (X.B.primes px).vGs := by
      have hP' : PP ∈ L.Pg := hPP
      rw [hL.Pg] at hP'
      exact hP'
    have hm := hw ⟨PP, by classical exact Finset.mem_union_left _ hP⟩
    rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ hP] at hm
    exact of_reindex_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr _ hm
  have hQ : ∀ PP ∈ (L.datXt t).Q,
      Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (L.datXt t).r) := by
    intro PP hPP
    have hq : PP ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      have hP' : PP ∈ L.Q t := hPP
      have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
        simp only [ColIn.Q, tup_ixOf]
      rw [hL.Q t, e] at hP'
      exact hP'
    have hm := hw ⟨PP, by classical exact Finset.mem_union_right _ hq⟩
    by_cases hP : PP ∈ (X.B.primes px).vGs
    · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ hP] at hm
      exact Formalism.L2.DIV.blockTri_blkOf_le _ _
        (of_reindex_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr _ hm).1
    · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ _ hP] at hm
      exact of_reindex_mem_HQ (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) _ hm
  exact ⟨Formalism.L2.DIV.mem_parLev.2 ⟨hUA, hSt, fun PP hP => (hG PP hP).1, hQ⟩,
    Subgroup.mem_bot.2 (funext fun PP => (hG PP.1 PP.2).2)⟩

end GlobalTheory.Mem.R3.RowDeco
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.levelGroup_reduction_onto_finite_group_surjective : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U), Function.Surjective (LiftBrg.ActQ.redQ X I U L eG i t) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.ActQ.redQ_surjective | exact GlobalTheory.Mem.R3.LiftBrg.ActQ.redQ_surjective | (intros; apply GlobalTheory.Mem.R3.LiftBrg.ActQ.redQ_surjective <;> assumption)
end
