module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle391
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoordinatesFormsAndFibreNormBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section

namespace GlobalTheory.ResidueEisenstein.LeviConj

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cT_smul' (s : AF F ⊗[F] E →+* AF F ⊗[F] E) {p q : Type} (a : AF F ⊗[F] E) (M : Matrix p q (AF F ⊗[F] E)) :
    cT s (a • M) = s a • cT s M := by
  ext i k; simp [cT]

theorem det_conj_mul_det (s : AF F ⊗[F] E →+* AF F ⊗[F] E) {k : ℕ} (M K : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))
    (hK : IsUnit K.det) (h : cT s M * K * M = K) : s M.det * M.det = 1 := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have e : (cT s M).det = s M.det := by
    rw [cT, Matrix.det_transpose]; exact (RingHom.map_det s M).symm
  rw [e] at hd
  apply hK.mul_right_cancel
  rw [one_mul]; nth_rewrite 2 [← hd]; ring


open GlobalTheory.SphEis.UnipCrd in
theorem crd_conj_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (l : (AF F ⊗[F] E)ˣ) (γ : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F C = (l : AF F ⊗[F] E) • adMat F C → (matHom _ σ J g).1 * adMat F D = adMat F D * γ → ∃ δ : GL (Fin m) (AF F ⊗[F] E), absE F E (Matrix.GeneralLinearGroup.det δ) = 1 ∧ δ.1 * adMat F J₀⁻¹ * cT (sigR (AF F) σ) δ.1 = adMat F J₀⁻¹ ∧ ∀ u b c, GlobalTheory.SphEis.Crd σ J C D Z J₀ u b c → GlobalTheory.SphEis.Crd σ J C D Z J₀ (g * u * g⁻¹) ((l : AF F ⊗[F] E) • (b * δ.1)) (((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • c) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g l γ hC hD
  set s := sigR (AF F) σ with hs
  set G := (matHom _ σ J g).1 with hG
  have hU : cT s G * adMat F J * G = adMat F J := g.2
  have pres : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) (AF F ⊗[F] E)) (Y : Matrix (Fin n) (Fin q) (AF F ⊗[F] E)),
      cT s (G * X) * adMat F J * (G * Y) = cT s X * adMat F J * Y := by
    intro p q X Y
    rw [Formalism.UG.cT_mul]
    calc cT s X * cT s G * adMat F J * (G * Y) = cT s X * (cT s G * adMat F J * G) * Y := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]
  have g0 : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), cT (σ : E →+* E) X * J * Y = 0 →
      cT s (adMat F X) * adMat F J * adMat F Y = 0 := by
    intro p q X Y h; have := gr_adMat (F := F) σ J X Y; rw [h] at this; simpa [gr] using this
  have hcd : cT s (adMat F C) * adMat F J * adMat F D = 1 := by
    have := gr_adMat (F := F) σ J C D; rw [hF.cd] at this; simpa [gr] using this
  have hzz : cT s (adMat F Z) * adMat F J * adMat F Z = adMat F J₀ := by
    have := gr_adMat (F := F) σ J Z Z; rw [hF.zz] at this; simpa [gr] using this
  have hcz := g0 C Z hF.cz
  have hdz := g0 D Z hF.dz
  have linv : (l : AF F ⊗[F] E) * ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 := Units.mul_inv l
  have sinv : s (l : AF F ⊗[F] E) * s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 := by rw [← map_mul, linv, map_one]
  have ssl : ∀ x, s (s x) = x := sigR_invol σ hF.cm

  have hγ : γ = s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • 1 := by
    have e := pres (adMat F C) (adMat F D)
    rw [hC, hD, hcd, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc, hcd,
      Matrix.one_mul] at e
    calc γ = (s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * s (l : AF F ⊗[F] E)) • γ := by rw [mul_comm, sinv, one_smul]
      _ = _ := by rw [← smul_smul, e]

  have hcgz : cT s (adMat F C) * adMat F J * (G * adMat F Z) = 0 := by
    have e := pres (adMat F C) (adMat F Z)
    rw [hC, hcz, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Matrix.smul_mul, Matrix.smul_mul] at e
    calc _ = (s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * s (l : AF F ⊗[F] E)) •
          (cT s (adMat F C) * adMat F J * (G * adMat F Z)) := by rw [mul_comm, sinv, one_smul]
      _ = 0 := by rw [← smul_smul, e, smul_zero]
  have cTγ : cT s γ = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • 1 := by
    rw [hγ, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', ssl, Formalism.UG.cT_one]
  have hdgz : cT s (adMat F D) * adMat F J * (G * adMat F Z) = 0 := by
    have e := pres (adMat F D) (adMat F Z)
    rw [hD, hdz, Formalism.UG.cT_mul, cTγ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul] at e
    calc _ = ((l : AF F ⊗[F] E) * ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) •
          (cT s (adMat F D) * adMat F J * (G * adMat F Z)) := by rw [linv, one_smul]
      _ = 0 := by rw [← smul_smul, e, smul_zero]
  have hsum : adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J))
      + adMat F D * (cT s (adMat F C) * adMat F J) = 1 := by
    have := congrArg (fun M => adMat F M) hF.sum
    simp only [adMat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [cT_adMat, cT_adMat, cT_adMat]
    simpa only [adMat] using this
  obtain ⟨δ₀, hδ₀⟩ : ∃ X, X = adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J * (G * adMat F Z)) := ⟨_, rfl⟩
  have hGZ : G * adMat F Z = adMat F Z * δ₀ := by
    calc G * adMat F Z = (adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J))
      + adMat F D * (cT s (adMat F C) * adMat F J)) * (G * adMat F Z) := by rw [hsum, Matrix.one_mul]
      _ = _ := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
        simp only [← Matrix.mul_assoc (cT s (adMat F D)), ← Matrix.mul_assoc (cT s (adMat F C)),
          ← Matrix.mul_assoc (cT s (adMat F Z))]
        rw [hdgz, hcgz, Matrix.mul_zero, Matrix.mul_zero, zero_add, add_zero, hδ₀]
  have hδu : cT s δ₀ * adMat F J₀ * δ₀ = adMat F J₀ := by
    have e := pres (adMat F Z) (adMat F Z)
    rw [hGZ, hzz, Formalism.UG.cT_mul] at e
    calc cT s δ₀ * adMat F J₀ * δ₀ = cT s δ₀ * (cT s (adMat F Z) * adMat F J * adMat F Z) * δ₀ := by rw [hzz]
      _ = _ := by rw [← e]; simp only [Matrix.mul_assoc]

  have hu0 : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have jj : adMat F J₀⁻¹ * adMat F J₀ = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu0, Matrix.map_one _ (map_zero _) (map_one _)]
  have jj' : adMat F J₀ * adMat F J₀⁻¹ = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu0, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ0 : cT s (adMat F J₀) = adMat F J₀ := by
    rw [cT_adMat]; congr 1; ext i k; simp [Formalism.UG.cT, hF.herm₀.1]
  have hJ0i : cT s (adMat F J₀⁻¹) = adMat F J₀⁻¹ := by
    rw [cT_adMat, cT_inv_herm σ J₀ hF.herm₀]
  have hK : IsUnit (adMat F J₀).det := by
    rw [show (adMat F J₀).det = inclR (F := F) (AF F) J₀.det from (RingHom.map_det _ _).symm]; exact hu0.map _
  obtain ⟨δi, hδi⟩ : ∃ X, X = adMat F J₀⁻¹ * cT s δ₀ * adMat F J₀ := ⟨_, rfl⟩
  have hl : δi * δ₀ = 1 := by
    rw [hδi, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s δ₀), hδu, jj]
  have hr : δ₀ * δi = 1 := mul_eq_one_comm.mp hl
  let δ : GL (Fin m) (AF F ⊗[F] E) := ⟨δi, δ₀, hl, hr⟩
  have hδval : δ.1 = δi := rfl
  have hiu : cT s δi * adMat F J₀ * δi = adMat F J₀ := by
    calc cT s δi * adMat F J₀ * δi = cT s δi * (cT s δ₀ * adMat F J₀ * δ₀) * δi := by rw [hδu]
      _ = cT s (δ₀ * δi) * adMat F J₀ * (δ₀ * δi) := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hr, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  have cTδi : cT s δi = adMat F J₀ * δ₀ * adMat F J₀⁻¹ := by
    rw [hδi, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJ0, hJ0i, cT_cT σ hF.cm, Matrix.mul_assoc]
  have key : δ₀ * adMat F J₀⁻¹ = adMat F J₀⁻¹ * cT s δi := by
    rw [cTδi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, jj, Matrix.one_mul]
  refine ⟨δ, ?_, ?_, ?_⟩
  · have h1 := GlobalTheory.ResidueEisenstein.LeviConj.det_conj_mul_det s δi (adMat F J₀) hK hiu
    have hu : GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det δ) * Matrix.GeneralLinearGroup.det δ = 1 := by
      ext
      show sigR (AF F) σ _ * _ = 1
      exact h1
    have h2 := congrArg (absE F E) hu
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq] at h2
    exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2
  · rw [hδval, Matrix.mul_assoc, ← key, hδi]
    calc adMat F J₀⁻¹ * cT s δ₀ * adMat F J₀ * (δ₀ * adMat F J₀⁻¹)
        = adMat F J₀⁻¹ * (cT s δ₀ * adMat F J₀ * δ₀) * adMat F J₀⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hδu, jj, Matrix.one_mul]
  · intro u b c hu
    set Gi := (matHom _ σ J g⁻¹).1 with hGi
    have hGiG : Gi * G = 1 := by
      rw [hGi, hG, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    have iC : Gi * adMat F C = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • adMat F C := by
      have e : adMat F C = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (G * adMat F C) := by
        rw [hC, smul_smul, Units.inv_mul, one_smul]
      conv_lhs => rw [e]
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have iZ : Gi * adMat F Z = adMat F Z * δi := by
      have e : adMat F Z = G * adMat F Z * δi := by rw [hGZ, Matrix.mul_assoc, hr, Matrix.mul_one]
      conv_lhs => rw [e]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have hGD : G * adMat F D = s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • adMat F D := by
      rw [hD, hγ, Matrix.mul_smul, Matrix.mul_one]
    have iD : Gi * adMat F D = s (l : AF F ⊗[F] E) • adMat F D := by
      have e : adMat F D = s (l : AF F ⊗[F] E) • (G * adMat F D) := by
        rw [hGD, smul_smul, sinv, one_smul]
      conv_lhs => rw [e]
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have hplus : adMat F Z * GlobalTheory.SphEis.plus σ J₀ ((l : AF F ⊗[F] E) • (b * δi)) =
        s (l : AF F ⊗[F] E) • (G * (adMat F Z * GlobalTheory.SphEis.plus σ J₀ b)) := by
      simp only [GlobalTheory.SphEis.plus]
      rw [GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Formalism.UG.cT_mul, ← Matrix.mul_assoc G, hGZ, Matrix.mul_smul, Matrix.mul_smul]
      congr 1
      rw [← hs, ← Matrix.mul_assoc (adMat F J₀⁻¹), ← key]; simp only [Matrix.mul_assoc]
    have hm : (matHom _ σ J (g * u * g⁻¹)).1 = G * (matHom _ σ J u).1 * Gi := by
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm]
      calc G * (matHom _ σ J u).1 * Gi * adMat F C
          = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (G * ((matHom _ σ J u).1 * adMat F C)) := by
            rw [Matrix.mul_assoc, iC, Matrix.mul_smul, Matrix.mul_assoc]
        _ = adMat F C := by rw [hu.onC, hC, smul_smul, Units.inv_mul, one_smul]
    · rw [hm, hδval]
      calc G * (matHom _ σ J u).1 * Gi * adMat F Z = G * ((matHom _ σ J u).1 * adMat F Z) * δi := by
            rw [Matrix.mul_assoc, iZ, ← Matrix.mul_assoc, Matrix.mul_assoc G]
        _ = _ := by
            rw [hu.onZ, Matrix.mul_add, ← Matrix.mul_assoc G (adMat F C), hGZ, hC, Matrix.add_mul, Matrix.mul_assoc,
              hr, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    · rw [hm, hδval, hplus]
      calc G * (matHom _ σ J u).1 * Gi * adMat F D
          = s (l : AF F ⊗[F] E) • (G * ((matHom _ σ J u).1 * adMat F D)) := by
            rw [Matrix.mul_assoc, iD, Matrix.mul_smul, Matrix.mul_assoc]
        _ = s (l : AF F ⊗[F] E) • (G * adMat F D - G * (adMat F Z * GlobalTheory.SphEis.plus σ J₀ b) + G * (adMat F C * c)) := by
            rw [hu.onD, Matrix.mul_add, Matrix.mul_sub]
        _ = _ := by
            rw [hGD, ← Matrix.mul_assoc G (adMat F C), hC]
            simp only [smul_add, smul_sub, smul_smul, sinv, one_smul, Matrix.smul_mul, Matrix.mul_smul]
            rw [mul_comm (s (l : AF F ⊗[F] E))]

end GlobalTheory.ResidueEisenstein.LeviConj

end
end

section

noncomputable section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpecFinite

open GlobalTheory.CuspMult GlobalTheory.PRep

section Abstract

variable {H X : Type} [Group H] [TopologicalSpace H] [AddCommGroup X] [Module ℂ X]

theorem simple_asSubmodule {ρ : Representation ℂ H X} (U : Subrepresentation ρ) (hU : U.toRepresentation.IsIrreducible) :
    IsSimpleModule (MonoidAlgebra ℂ H) U.asSubmodule := by
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) U.toRepresentation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).1 hU
  exact IsSimpleModule.congr (GlobalTheory.RepCount.subEquiv U).symm

theorem exists_sub_equiv {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ H W} {ρ : Representation ℂ H X}
    (h1 : σ.IsIrreducible) {f : W →ₗ[ℂ] X} (hf : ∀ g s, f (σ g s) = ρ g (f s)) (h0 : f ≠ 0) :
    ∃ U : Subrepresentation ρ, U.toSubmodule = LinearMap.range f ∧ Function.Injective f ∧
      ∃ e : W ≃ₗ[ℂ] U.toSubmodule, (∀ s, (e s : X) = f s) ∧ ∀ g s, e (σ g s) = U.toRepresentation g (e s) := by
  let F := f.intertwiningMap_of_isIntertwiningMap σ ρ hf
  have hi : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | hz
    · exact hi
    · exact absurd (LinearMap.ext fun s => DFunLike.congr_fun hz s) h0
  exact ⟨F.range, rfl, hi, LinearEquiv.ofInjective f hi, fun s => rfl, fun g s => Subtype.ext (hf g s)⟩

theorem rank_homInto_lt {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W) (ρ : Representation ℂ H X)
    (C : Submodule ℂ X) (K : Subgroup H) (hA : FiniteDimensional ℂ ↥(C ⊓ fixed ρ K)) (h1 : σ.IsIrreducible)
    {x : W} (hx0 : x ≠ 0) (hx : ∀ k ∈ K, σ k x = x) : Module.rank ℂ (homInto σ ρ C) < Cardinal.aleph0 := by
  let ev : homInto σ ρ C →ₗ[ℂ] ↥(C ⊓ fixed ρ K) :=
    { toFun := fun f => ⟨(f : W →ₗ[ℂ] X) x, f.2.1 x, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => by rw [← f.2.2, hx k hk]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun f hf => ?_
    by_contra hne
    obtain ⟨U, -, hi, -⟩ := exists_sub_equiv h1 f.2.2 (fun h => hne (Subtype.ext h))
    have h0 : (f : W →ₗ[ℂ] X) x = (f : W →ₗ[ℂ] X) 0 := by
      rw [map_zero]
      exact congrArg Subtype.val hf
    exact hx0 (hi h0)
  haveI := FiniteDimensional.of_injective ev hinj
  exact Module.rank_lt_aleph0 ℂ _

theorem finite_classes (ρ : Representation ℂ H X) (C : Submodule ℂ X) (K : Subgroup H)
    (hA : FiniteDimensional ℂ ↥(C ⊓ fixed ρ K)) :
    ∃ (n : ℕ) (Ws : Fin n → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
      (σs : ∀ i, Representation ℂ H (Ws i)),
      ((∀ i, (σs i).IsIrreducible) ∧ (∀ i, IsAdmissible (σs i)) ∧ ∀ i j, i ≠ j → IsEmpty ((σs i).Equiv (σs j))) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → IsAdmissible σ →
        homInto σ ρ C ≠ ⊥ → (∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x) → ∃ i, Nonempty (σ.Equiv (σs i)) := by
  classical
  let S : Set (Subrepresentation ρ) := {U | U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    IsAdmissible U.toRepresentation ∧ U.toSubmodule ⊓ fixed ρ K ≠ ⊥}
  let comp : Subrepresentation ρ → Submodule (MonoidAlgebra ℂ H) ρ.asModule :=
    fun U => isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule U.asSubmodule
  let T : Set (Submodule (MonoidAlgebra ℂ H) ρ.asModule) := comp '' S
  have hT : sSupIndep T := (sSupIndep_isotypicComponents (MonoidAlgebra ℂ H) ρ.asModule).mono (by
    rintro _ ⟨U, hU, rfl⟩
    exact ⟨U.asSubmodule, simple_asSubmodule U hU.2.1, rfl⟩)
  have hy : ∀ c : T, ∃ y : ↥(C ⊓ fixed ρ K), y ≠ 0 ∧
      ρ.asModuleEquiv.symm (y : X) ∈ (c : Submodule (MonoidAlgebra ℂ H) ρ.asModule) := by
    rintro ⟨_, U, hU, rfl⟩
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hU.2.2.2
    exact ⟨⟨y, hU.1 hy.1, hy.2⟩, fun h => hy0 (congrArg Subtype.val h), U.asSubmodule.le_isotypicComponent hy.1⟩
  choose y hy0 hyc using hy
  have hsm : ∀ (c : T) (a : ℂ), ρ.asModuleEquiv.symm ((a • y c : ↥(C ⊓ fixed ρ K)) : X) ∈
      (c : Submodule (MonoidAlgebra ℂ H) ρ.asModule) := fun c a => by
    rw [Submodule.coe_smul, map_smul]
    exact Submodule.smul_of_tower_mem _ a (hyc c)
  have hli : LinearIndependent ℂ y := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have hx : ρ.asModuleEquiv.symm ((g i • y i : ↥(C ⊓ fixed ρ K)) : X) ∈
        (i : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ⊓ sSup (T \ {(i : Submodule (MonoidAlgebra ℂ H) ρ.asModule)}) := by
      refine ⟨hsm i (g i), ?_⟩
      have he : (g i • y i : ↥(C ⊓ fixed ρ K)) = - ∑ j ∈ s.erase i, g j • y j := by
        rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase s (fun j => g j • y j) hi, hs]

      rw [he, Submodule.coe_neg, Submodule.coe_sum, map_neg, map_sum]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
      refine (le_sSup (show (j : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ∈ T \ {(i : Submodule (MonoidAlgebra ℂ H) ρ.asModule)} from
          ⟨j.2, fun h => Finset.ne_of_mem_erase hj (Subtype.ext h)⟩) :
        (j : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ≤ _) (hsm j (g j))
    rw [(hT i.2).eq_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff, Submodule.coe_eq_zero, smul_eq_zero] at hx
    exact hx.resolve_right (hy0 i)
  haveI : Finite T := hli.finite
  haveI := Fintype.ofFinite T
  let e := Fintype.equivFin T
  have hrep : ∀ c : T, ∃ U ∈ S, comp U = c := fun c => c.2
  choose U hUS hUc using hrep
  refine ⟨Fintype.card T, fun i => ↥(U (e.symm i)).toSubmodule, fun i => inferInstance, fun i => inferInstance,
    fun i => (U (e.symm i)).toRepresentation, ⟨fun i => (hUS _).2.1, fun i => (hUS _).2.2.1, fun i j hij => ⟨fun φ => hij ?_⟩⟩, ?_⟩
  · obtain ⟨ψ⟩ := (GlobalTheory.CuspFactor.nonempty_equiv_iff _ _).1 ⟨φ⟩
    have h3 := ((GlobalTheory.RepCount.subEquiv _).symm.trans (ψ.trans (GlobalTheory.RepCount.subEquiv _))).isotypicComponent_eq
      (M := ρ.asModule)
    exact e.symm.injective (Subtype.ext ((hUc _).symm.trans (h3.trans (hUc _))))
  · rintro W _ _ σ h1 h2 hne ⟨x, hx0, hx⟩
    obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hne
    obtain ⟨V, hV, hi, ev, hev, heq⟩ := exists_sub_equiv h1 hf.2 hf0
    haveI : IsSimpleModule (MonoidAlgebra ℂ H) σ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).1 h1
    let ψ : σ.asModule ≃ₗ[MonoidAlgebra ℂ H] V.toRepresentation.asModule :=
      LinearEquiv.ofBijective (GlobalTheory.RepCount.modMap ev.toLinearMap heq) ev.bijective
    have hVirr : V.toRepresentation.IsIrreducible :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).2 (IsSimpleModule.congr ψ.symm)
    have hVS : V ∈ S := by
      refine ⟨?_, hVirr, GlobalTheory.RepCount.isAdmissible_of_injective ev.symm.toLinearMap (fun g s => ?_) ev.symm.injective h2, ?_⟩
      · rw [hV]
        rintro _ ⟨s, rfl⟩
        exact hf.1 s
      · rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, heq, LinearEquiv.apply_symm_apply]
      · rw [Submodule.ne_bot_iff]
        refine ⟨f x, ⟨hV ▸ ⟨x, rfl⟩, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => by rw [← hf.2, hx k hk]⟩, fun h => hx0 (hi ?_)⟩
        rw [h, map_zero]
    refine ⟨e ⟨comp V, V, hVS, rfl⟩, ?_⟩
    show Nonempty (σ.Equiv (U (e.symm (e ⟨comp V, V, hVS, rfl⟩))).toRepresentation)
    generalize hc : e.symm (e ⟨comp V, V, hVS, rfl⟩) = c
    rw [Equiv.symm_apply_apply] at hc
    haveI := simple_asSubmodule V hVirr
    haveI := simple_asSubmodule (U c) (hUS c).2.1
    have hle : (U c).asSubmodule ≤ comp V :=
      ((U c).asSubmodule.le_isotypicComponent).trans_eq ((hUc c).trans (congrArg Subtype.val hc).symm)
    obtain ⟨χ⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule V.asSubmodule) _ hle
    exact (GlobalTheory.CuspFactor.nonempty_equiv_iff _ _).2
      ⟨(ψ.trans (GlobalTheory.RepCount.subEquiv V)).trans (χ.symm.trans (GlobalTheory.RepCount.subEquiv _).symm)⟩

end Abstract

theorem specFin : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation →
    SpecFin := by
  intro hQ hP hDM D V S M μ _ _
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hm : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ →
      mCuspDS μ σ M = Module.rank ℂ (homInto σ (finRep M) (allMaps θ M)) := fun W _ _ σ h =>
    (GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hQ hP hDM D θ hθ V S M μ W σ h.1).symm
  refine ⟨fun W _ _ σ h1 h2 => ?_, fun K hK => ?_⟩
  · haveI := GlobalTheory.CuspFactor.nontrivial_of_irr σ h1
    obtain ⟨x, hx0⟩ := exists_ne (0 : W)
    let St : Subgroup (GfC V) :=
      { carrier := {g | σ g x = x}
        mul_mem' := fun {a b} ha hb => by
          show σ (a * b) x = x
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          show σ a⁻¹ x = x
          conv_lhs => rw [← ha]
          simp }
    rw [hm W σ h2]
    exact rank_homInto_lt σ (finRep M) (allMaps θ M) St (GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ St (h2.1 x)) h1 hx0
      (fun k hk => hk)
  · obtain ⟨n, Ws, i1, i2, σs, hs, hcov⟩ :=
      finite_classes (finRep M) (allMaps θ M) K (GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ K hK)
    refine ⟨n, Ws, i1, i2, σs, hs, fun W _ _ σ h1 h2 hm0 hx => hcov W σ h1 h2 (fun h => hm0 ?_) hx⟩
    rw [hm W σ h2, h, rank_bot]

end GlobalTheory.SpecFinite

end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem slab_subset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ b, IsFlowJ σ J X Y b → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ g, Real.exp (-1) ≤ h g → h g ≤ 1 → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ y ∈ C, g = u * m * y := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D b hb
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) :=
    (HtCont.isCompact_isHt_scales F E σ n J r X Y L a h D).1
  refine ⟨(fun q : ℝ × GAd σ J => b q.1 * q.2) '' (Set.Icc (-1 : ℝ) 0 ×ˢ (levelAll σ J L a : Set (GAd σ J))), ?_, ?_⟩
  · exact (isCompact_Icc.prod hK).image ((hb.cont.comp continuous_fst).mul continuous_snd)
  · intro g h1 h2
    obtain ⟨p, l, hp, k, hk, rfl⟩ := D.iwa g
    rw [D.ht p l hp k hk] at h1 h2
    have hpos : (0 : ℝ) < absE F E (Matrix.GeneralLinearGroup.det l) := lt_of_lt_of_le (Real.exp_pos _) h1
    set t : ℝ := Real.log (absE F E (Matrix.GeneralLinearGroup.det l)) with ht
    have ht1 : -1 ≤ t := (Real.le_log_iff_exp_le hpos).2 h1
    have ht0 : t ≤ 0 := Real.log_nonpos hpos.le h2
    obtain ⟨l', hl', hal'⟩ := hb.onX (-t)
    have hs : ScalesBy σ J X (p * b (-t)) (l * l') := by
      unfold ScalesBy at *
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hl', ← Matrix.mul_assoc, hp, Matrix.mul_assoc, Units.val_mul]
    have hone : absE F E (Matrix.GeneralLinearGroup.det (l * l')) = 1 := by
      apply NNReal.coe_injective
      rw [map_mul, map_mul, NNReal.coe_mul, hal', Real.exp_neg, ht, Real.exp_log hpos, mul_inv_cancel₀ hpos.ne', NNReal.coe_one]
    obtain ⟨u, hu, m, -, e, -, -, hm⟩ := GlobalTheory.T.leviDecomposition_wittFrameStabilizer F E σ n J r X Y D.cm D.herm D.witt _ _ hs
    have h0 : b 0 = 1 := by
      have := hb.add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    refine ⟨u, hu, m, hm hone, b t * k, ⟨(t, k), ⟨⟨ht1, ht0⟩, hk⟩, rfl⟩, ?_⟩
    rw [← e, mul_assoc, ← mul_assoc (b (-t)), ← hb.add, neg_add_cancel, h0, one_mul]

end GlobalTheory.ResidueEisenstein
end

section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.integral_coordinates_forms_and_fibre_norm_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), DefCase U ξ → Dom a n → ∀ (Z : Comp Xo c) (P : PtData Z), (∀ σ, P.N ((starRingEnd ℂ).comp σ) = P.N σ ∧ ∀ τ, ‖(P.X ((starRingEnd ℂ).comp σ) τ).det‖ = ‖(P.X σ τ).det‖) ∧ ∀ (x : TIdx (part Dw a) → c.F) (f : Rul Xo c), f ∈ sec Xo c a n → Reads Z P.y₀ a n x f → (x ∈ locLat (P.matA a n) → ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v f) ∧ ∀ σ, ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) ξ (wtZ a n) f z ≤ matNorm (P.matY a n) σ x := by
  first | exact @GlobalTheory.DefPt.IntNorm.integral_and_norm_le | exact GlobalTheory.DefPt.IntNorm.integral_and_norm_le | (intros; apply GlobalTheory.DefPt.IntNorm.integral_and_norm_le <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_two_step_unfolding_semidirect_lattice : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G) (D : Set G), μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → ∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ x in D, ∫⁻ m : M, ∫⁻ u : N, φ (u * m * x) ∂ν ∂π ∂μ = ν DN * π DM * ∫⁻ x, φ x ∂μ := by
  first | exact @GlobalTheory.ResLine.lintegral_two_step_unfolding | exact GlobalTheory.ResLine.lintegral_two_step_unfolding | (intros; apply GlobalTheory.ResLine.lintegral_two_step_unfolding <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.height_function_scaling_parabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → IsHt (levelAll σ J L a) h ∧ ∀ p l, Scales σ J (col X) p l → ∀ g, h (p * g) = absE F E l * h g := by
  first | exact @GlobalTheory.ResLine.iwasawaHeight_isHt | exact GlobalTheory.ResLine.iwasawaHeight_isHt | (intros; apply GlobalTheory.ResLine.iwasawaHeight_isHt <;> assumption)
end
