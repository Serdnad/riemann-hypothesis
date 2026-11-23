module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfBis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



namespace UpperTheory.V.Z.J.D

private theorem lat {α : Type*} [Lattice α] {Y B f z E : α} (h1 : Y ≤ B) (h2 : Y ≤ f) (h3 : Y ≤ E) :
    Y ⊓ (B ⊓ f ⊓ z ⊓ E) = Y ⊓ z :=
  le_antisymm (le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    (le_inf inf_le_left (le_inf (le_inf (le_inf (inf_le_left.trans h1) (inf_le_left.trans h2)) inf_le_right)
      (inf_le_left.trans h3)))

private theorem eig_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {a b : ℂ} {F : M} (h0 : F ≠ 0)
    (hT : T F = a • F) (hF : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hF
  have h1 : (T - b • (1 : Module.End ℂ M)) F = (a - b) • F := by
    simp [hT, sub_smul]
  have h : ∀ i : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ i) F = (a - b) ^ i • F := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, pow_succ']
  rw [h k] at hk
  by_contra hne
  exact smul_ne_zero (pow_ne_zero k (sub_ne_zero.2 hne)) h0 hk

private theorem eig_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {b : ℂ} {F : M}
    (hT : T F = b • F) : F ∈ T.maxGenEigenspace b :=
  (Module.End.mem_maxGenEigenspace T b F).2 ⟨1, by simp [hT]⟩

private theorem eig_le {M I : Type*} [AddCommGroup M] [Module ℂ M] (T : I → Module.End ℂ M) (ev : I → ℂ) (i : I) (a : ℂ)
    (O Y Y' : Submodule ℂ M) (hne : Y ⊓ (O ⊓ ⨅ i, (T i).maxGenEigenspace (ev i)) ≠ ⊥)
    (h1 : ∀ F ∈ Y, T i F = a • F) (h2 : ∀ F ∈ Y', T i F = a • F) : Y' ≤ (T i).maxGenEigenspace (ev i) := by
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hFe : F ∈ (T i).maxGenEigenspace (ev i) :=
    (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hF).2).2 i
  have hae : a = ev i := eig_eq _ hF0 (h1 F (Submodule.mem_inf.1 hF).1) hFe
  intro F' hF'
  exact eig_mem _ (hae ▸ h2 F' hF')

private theorem scalar (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GLw n w)) (j : ℕ) :
    ∃ a : ℂ, ∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v := by
  by_cases h : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w (n := n))
  · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ.smooth τ.irred h
    obtain ⟨-, a, -, ha, -⟩ := UpperTheory.V.Hi.satT L n w τ B hB
    exact ⟨a j, ha j⟩
  · refine ⟨0, fun v hv => ?_⟩
    have hv0 : v = 0 := by
      by_contra h0
      rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hv
      exact h ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩)
    simp [hv0]

end UpperTheory.V.Z.J.D
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



namespace UpperTheory.V.Z.J.D

private theorem val_eq {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {F : M} (h0 : F ≠ 0) {a b : ℂ}
    (h : T F = a • F) (hg : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hg
  have hp : ∀ k : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ k) F = (a - b) ^ k • F := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, LinearMap.smul_apply,
        Module.End.one_apply, ← sub_smul, smul_smul, pow_succ]
  rw [hp k] at hk
  rcases smul_eq_zero.1 hk with h1 | h1
  · exact sub_eq_zero.1 (by_contra fun h2 => pow_ne_zero k h2 h1)
  · exact absurd h1 h0

private theorem chi_map {n : ℕ} {R S G : Type} [CommRing R] [CommRing S] [Group G] (D : W.GDet n R G) (f : R →+* S) (g : G) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra R (Polynomial S) := ((algebraMap S (Polynomial S)).comp f).toAlgebra
  let φ : Polynomial R →ₐ[R] Polynomial S :=
    { Polynomial.mapRingHom f with commutes' := fun b => Polynomial.map_C f }
  refine Eq.trans ?_ (D.nat (Polynomial R) (Polynomial S) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1)))
  change D.D (Polynomial S) _ = D.D (Polynomial S) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  simp [map_sub, MonoidAlgebra.mapRingHom_single]

private theorem pol_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n q : ℕ) (a : ℕ → R) (b : ℕ → S)
    (h : ∀ j ≤ n, f (a j) = b j) : (Hi.heckePol n q a).map f = Hi.heckePol n q b := by
  unfold Hi.heckePol

  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  simp

private theorem ss_irr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp

end UpperTheory.V.Z.J.D
end
end
