module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle161
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadRowWeights
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle159
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLaw
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle203
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth

@[expose] public section

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

open GlobalTheory.ValCmp

theorem sqAct_eq_rnd_invTranspose (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (g : GL (Fin n) K) (f : MP K n) :
    sqAct K n lam g f = rnd K lam.detShift ((g : Matrix (Fin n) (Fin n) K)⁻¹).transpose f := by
  have hdet : IsUnit (g : Matrix (Fin n) (Fin n) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)
  have hinv : (((g : Matrix (Fin n) (Fin n) K)⁻¹).transpose)⁻¹ = (g : Matrix (Fin n) (Fin n) K).transpose := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hdet]
  have hpow : (((g : Matrix (Fin n) (Fin n) K)⁻¹).transpose).det ^ (-lam.detShift) =
      (g : Matrix (Fin n) (Fin n) K).det ^ lam.detShift := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_zpow', neg_neg]
  simp only [GlobalTheory.ValCmp.rnd, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hinv, hpow, sqAct, detPow,
    Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

private lemma detShift_eq_w_last {m : ℕ} (lam : DomWeight (m + 1)) : lam.detShift = lam.w (Fin.last m) := by
  unfold DomWeight.detShift
  rw [dite_eq_left (Nat.succ_pos m)]
  rfl

private lemma natW_antitone_succ {m : ℕ} (lam : DomWeight (m + 1)) : Antitone lam.natW := by
  intro i j hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)

private lemma natW_last_eq_zero {m : ℕ} (lam : DomWeight (m + 1)) : lam.natW (Fin.last m) = 0 := by
  unfold DomWeight.natW
  rw [detShift_eq_w_last, sub_self, Int.toNat_zero]

private lemma dual_detShift_eq_neg_w_zero {m : ℕ} (lam : DomWeight (m + 1)) : lam.dual.detShift = -lam.w 0 := by
  rw [detShift_eq_w_last]
  show -lam.w (Fin.rev (Fin.last m)) = -lam.w 0
  rw [Fin.rev_last]

private lemma natW_dual_eq_nuDual {m : ℕ} (lam : DomWeight (m + 1)) :
    lam.dual.natW = GlobalTheory.ValCmp.nuDual lam.natW := by
  funext i
  have h0 : lam.w (Fin.rev i) ≤ lam.w 0 := lam.anti (Fin.zero_le _)
  have h1 : lam.w (Fin.last m) ≤ lam.w (Fin.rev i) := lam.anti (Fin.le_last _)
  have h2 : lam.dual.w i = -lam.w (Fin.rev i) := rfl
  show (lam.dual.w i - lam.dual.detShift).toNat =
    (lam.w 0 - lam.detShift).toNat - (lam.w (Fin.rev i) - lam.detShift).toNat
  rw [dual_detShift_eq_neg_w_zero, h2, detShift_eq_w_last]
  omega

private lemma neg_detShift_add_natW_zero_eq_dual_detShift {m : ℕ} (lam : DomWeight (m + 1)) :
    -(lam.detShift + ((lam.natW 0 : ℕ) : ℤ) + 0) = lam.dual.detShift := by
  have h0 : lam.w (Fin.last m) ≤ lam.w 0 := lam.anti (Fin.zero_le _)
  rw [dual_detShift_eq_neg_w_zero, detShift_eq_w_last]
  simp only [DomWeight.natW, detShift_eq_w_last]
  omega

theorem iso_irr_comp_conjU : ∀ (n : ℕ), 0 < n → ∀ lam : DomWeight n,
    Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam.dual) := by
  intro n hn lam
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨Ψ, hinj, hmap, hact, -, -⟩ := GlobalTheory.ValCmp.exists_posOk_dual ℂ ℂ m lam.natW
    (natW_antitone_succ lam) (natW_last_eq_zero lam) lam.detShift 0
  have hmem : ∀ f : nablaSq ℂ (m + 1) lam, Ψ f ∈ nablaSq ℂ (m + 1) lam.dual := by
    intro f
    change Ψ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ (m + 1) (m + 1) lam.dual.natW
    rw [natW_dual_eq_nuDual, ← hmap]
    exact Submodule.mem_map_of_mem f.2
  let L : nablaSq ℂ (m + 1) lam →ₗ[ℂ] nablaSq ℂ (m + 1) lam.dual :=
    (Ψ ∘ₗ (nablaSq ℂ (m + 1) lam).subtype).codRestrict _ hmem
  have hL : Function.Bijective L := by
    constructor
    · intro f f' h
      have h1 : Ψ ((f : MP ℂ (m + 1)) - f') = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val h
      exact Subtype.ext (sub_eq_zero.mp (hinj _ (Submodule.sub_mem _ f.2 f'.2) h1))
    · rintro ⟨y, hy⟩
      have hy' : y ∈ (Formalism.GradedWeylDivisibility.dualWeyl ℂ (m + 1) (m + 1) lam.natW).map Ψ := by
        rw [hmap, ← natW_dual_eq_nuDual]
        exact hy
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy'
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  refine ⟨LinearEquiv.ofBijective L hL, fun g x => Subtype.ext ?_⟩
  have hu : IsUnit (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det := by
    have hdet := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.mp g.2)
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact isUnit_iff_exists_inv.mpr ⟨_, hdet⟩
  have hg : ((((star (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).transpose)⁻¹).transpose) =
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff.mp g.2)
  change Ψ (sqAct ℂ (m + 1) lam (unitaryIncl (m + 1) (conjU (m + 1) g)) (x : MP ℂ (m + 1))) =
    sqAct ℂ (m + 1) lam.dual (unitaryIncl (m + 1) g) (Ψ x)
  rw [sqAct_eq_rnd_invTranspose, sqAct_eq_rnd_invTranspose]
  simp only [GlobalTheory.Branching.unitaryIncl_coe, conjU_coe]
  rw [hg, hact _ hu _ x.2, zpow_zero, one_smul, neg_detShift_add_natW_zero_eq_dual_detShift]

end GlobalTheory.OneFunctional
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.card_mul_finrank_subgroupEigenspace_of_trace_vanishes : ∀ (G M : Type) [Group G] [Finite G] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M) (P : Subgroup G) (χ : P →* ℂˣ), (∀ g ∈ P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) → Nat.card P * Module.finrank ℂ (eig ρ P fun g => ((χ g : ℂˣ) : ℂ)) = Module.finrank ℂ M := by
  first | exact @GlobalTheory.DefFree.card_mul_finrank_eig | exact GlobalTheory.DefFree.card_mul_finrank_eig | (intros; apply GlobalTheory.DefFree.card_mul_finrank_eig <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem iso_directSum_fockOne : ∀ (a b : ℕ) (α β : ℤ), Iso (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod ((GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b))) ((GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) (fockOne a b α β) := by
  intro a b α β
  obtain ⟨e⟩ := GlobalTheory.GLDuality.nonempty_equiv_polyRep a b
  obtain ⟨e, he⟩ := Iso.of_equiv e
  refine ⟨e, fun p x => ?_⟩
  have key : (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod
      ((GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b)))
      ((GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) p x =
      ((((detU a ^ α) p.1 * (detU b ^ β) p.2 : ℂˣ) : ℂ)) •
      (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) =>
        GlobalTheory.GLDuality.pieceRep (MonoidHom.id (GL (Fin a) ℂ)) (MonoidHom.id (GL (Fin b) ℂ)) i)
        (unitaryIncl a (conjU a p.1), unitaryIncl b p.2) x := by
    apply DFinsupp.ext
    intro i
    change TensorProduct.map ((((detU a ^ α) p.1 : ℂˣ) : ℂ) • (irr a (GlobalTheory.GLDuality.pad a i) (conjU a p.1)))
        ((((detU b ^ β) p.2 : ℂˣ) : ℂ) • (irr b (GlobalTheory.GLDuality.pad b i) p.2)) (x i) =
      ((((detU a ^ α) p.1 * (detU b ^ β) p.2 : ℂˣ) : ℂ)) •
        TensorProduct.map (irr a (GlobalTheory.GLDuality.pad a i) (conjU a p.1)) (irr b (GlobalTheory.GLDuality.pad b i) p.2) (x i)
    rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul, Units.val_mul, LinearMap.smul_apply]
  rw [key, map_smul, he]
  rfl

end GlobalTheory.OneFunctional
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum Kronecker Matrix

namespace GlobalTheory.OneFunctional.FockTensor

theorem linSub_prod {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] (M : ι → Matrix σ σ ℂ)
    (f : ι → MvPolynomial (ι × σ) ℂ) : linSub M (∏ τ, f τ) = ∏ τ, linSub M (f τ) := by
  simp only [linSub, MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.toLinearMap_apply, map_prod]

theorem linSub_rename {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] (M : ι → Matrix σ σ ℂ)
    (τ : ι) (f : MvPolynomial σ ℂ) :
    linSub M (rename (Prod.mk τ) f) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.sub (M τ)ᵀ f) := by
  unfold Formalism.GradedWeylDivisibility.sub
  simp only [linSub, MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.toLinearMap_apply, aeval_rename]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  congr 1
  funext i

  simp [Function.comp_apply, map_sum, Matrix.transpose_apply]

theorem fockOne_apply (a b : ℕ) (α β : ℤ) (h : U a) (g : U b) (f : MvPolynomial (Fin b × Fin a) ℂ) :
    fockOne a b α β (h, g) f =
      ((detU a h ^ α * detU b g ^ β : ℂˣ) : ℂ) • Formalism.GradedWeylDivisibility.sub (g.1 ⊗ₖ (star h.1)ᵀ)ᵀ f := rfl

theorem fock_apply {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ) (h : UG ι a) (g : UG ι b)
    (f : Pol ι a b) :
    fock a b α β (h, g) f =
      (((∏ τ, detU a (h τ) ^ α τ) * ∏ τ, detU b (g τ) ^ β τ : ℂˣ) : ℂ) •
        linSub (fun τ => (g τ).1 ⊗ₖ (star (h τ).1)ᵀ) f := rfl

theorem outer₂_fockOne_iso : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ),
    Iso (outer₂ fun τ => fockOne a b (α τ) (β τ)) (fock a b α β) := by
  intro ι _ _ a b α β
  obtain ⟨e, he⟩ := GlobalTheory.PolyTensor.exists_piTensor_equiv ι (Fin b × Fin a)
  refine ⟨e, ?_⟩
  rintro ⟨h, g⟩ x
  have key : e.toLinearMap ∘ₗ outer₂ (fun τ => fockOne a b (α τ) (β τ)) (h, g) =
      fock a b α β (h, g) ∘ₗ e.toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      outer₂_apply, PiTensorProduct.map_tprod, he, fockOne_apply, fock_apply, linSub_prod, linSub_rename]
    simp only [map_smul]
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, ← map_prod, Units.coe_prod, Units.val_mul]
  exact LinearMap.congr_fun key x

end GlobalTheory.OneFunctional.FockTensor
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.exists_ganGrossPrasad_row_weights : ∀ (S : Sizes) (Q : Entries S), Q.Good → ∃ lam : ∀ j : Fin (S.m + 1), DomWeight (S.nR j), (∀ i, (lam 0).w i = hw Q.psiPar i) ∧ (∀ i, (lam (Fin.last _)).w i = hw Q.bigPar i) ∧ ∀ j : Fin S.m, StepW (Q.e j - (S.nR j.succ / 2 : ℕ)) (-Q.e j + (S.nR j.castSucc / 2 : ℕ)) (lam j.castSucc) (lam j.succ) := by
  first | exact @GlobalTheory.OneFunctional.RowWeights.exists_row_weights | exact GlobalTheory.OneFunctional.RowWeights.exists_row_weights | (intros; apply GlobalTheory.OneFunctional.RowWeights.exists_row_weights <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecModel

section Conj

variable {n : ℕ} {J P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem lie_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * G + G * X = 0) :
    (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹)
      = (P * X * P⁻¹)ᴴ * J * (P * P⁻¹) + (P * P⁻¹)ᴴ * J * (P * X * P⁻¹) := by rw [h1]; simp
    _ = (P⁻¹)ᴴ * (Xᴴ * G + G * X) * P⁻¹ := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

theorem lie_conj_inv (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * J + J * X = 0) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * (Xᴴ * ((P * P⁻¹)ᴴ * J) + J * (P * P⁻¹) * X) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp

theorem exp_smul_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P * X * P⁻¹)) = P * NormedSpace.exp (t • X) * P⁻¹ := by
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

theorem prod_conj (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P * g * P⁻¹).prod = P * l.prod * P⁻¹ := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h1]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P * a * P⁻¹ * (P * l.prod * P⁻¹) = P * a * (P⁻¹ * P) * l.prod * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]
        simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smoothVec_of_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * J + J * X = 0} σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

theorem smoothVec_to_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ w) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w := by
  intro k Xs hXs
  have h := hw k (fun i => P * Xs i * P⁻¹) fun i => lie_conj hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))).prod =
      P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹ := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P * g * P⁻¹ := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj hP _ _
    rw [this, prod_conj hP]
  simpa only [e] using h

end Conj

theorem mem_sm_iff : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ),
    w ∈ M.sm τ ↔ SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w := by
  intro D V S M τ w
  rw [GlobalTheory.SmVec.sm_eq M τ, GlobalTheory.SmVec.mem_smSub]
  constructor
  · intro h
    exact smoothVec_of_conj (M.fr_unit τ) (M.fr_gram τ) h
  · intro h
    exact smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) h

end GlobalTheory.SmVecModel
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.placeIdempotent_under_eq_of_lies_over : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), Formalism.L2.NTheta.IsIdemAt e PP → IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := by
  first | exact @GlobalTheory.IdemUnder.under_eq_of_isIdemAt | exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt | (intros; apply GlobalTheory.IdemUnder.under_eq_of_isIdemAt <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistPlaces_localDatum_blockTriangular_law : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Q, gS PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, gT PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y' = (∏ PP ∈ Q, (((ξ PP (dBlk (blk2 r) 1 (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (dBlk (blk2 r) 1 (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y := by
  first | exact @GlobalTheory.OmegaTwistLaw.omegaQ_blockTri | exact GlobalTheory.OmegaTwistLaw.omegaQ_blockTri | (intros; apply GlobalTheory.OmegaTwistLaw.omegaQ_blockTri <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frameMatrix_movedHom_integral_reduction : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) := by
  first | exact @GlobalTheory.FrameRed.frMapO_actO_red | exact GlobalTheory.FrameRed.frMapO_actO_red | (intros; apply GlobalTheory.FrameRed.frMapO_actO_red <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRed

theorem frMapO_actO_int_red : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP : Pl D.host.E, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) :=
  frMapO_actO_red

end GlobalTheory.FrameRed

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.typePlaces_localDatum_blockTriangular_law : ∀ (D : D7) (a b r t j : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + j * t → b = r + (j + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Pg, gS PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, gT PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, upperLeftBlock ha (gS PP) = upperLeftBlock hb (gT PP)) → (∀ PP ∈ Pg, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Pg, (((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ) * ((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ)⁻¹)) * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y' = ((∏ PP ∈ Pg, ∏ c ∈ Finset.range j, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gS PP)) : ℂˣ) : ℂ) * ((∏ PP ∈ Pg, ∏ c ∈ Finset.range (j + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gT PP)) : ℂˣ) : ℂ)⁻¹ * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y := by
  first | exact @GlobalTheory.StepLaw.TypeDatum.omegaG_law | exact GlobalTheory.StepLaw.TypeDatum.omegaG_law | (intros; apply GlobalTheory.StepLaw.TypeDatum.omegaG_law <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist

theorem exists_thG_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.tw_thF → R.ex_thF → R.ex_thG := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm h e i t
  obtain ⟨th, h1⟩ := GlobalTheory.GoodProjLift.exists_thG D G Pl0 T A Ks R h0 hf hm fun i t => ((h i t).1 (e i t)).1
  exact ⟨th i t, h1 i t⟩

end GlobalTheory.Twist
end
