module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle155
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.StatementG

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompFinIdemSum

variable {D : D7}

theorem compFin_tensAt_ne {u v : HeightOneSpectrum (𝓞 D.host.F)} (h : u ≠ v)
    (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    compFin D.host.F D.host.E u (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
    have h0 : evFin D.host.F u (pairA D.host.F 0 (singleFin v a)) = 0 := evalV_singleFin_ne h a
    have h1 : compFin D.host.F D.host.E u (pairA D.host.F 0 (singleFin v a) ⊗ₜ[D.host.F] x) =
        evFin D.host.F u (pairA D.host.F 0 (singleFin v a)) ⊗ₜ[D.host.F] x :=
      Algebra.TensorProduct.map_tmul ..
    rw [h1, h0, TensorProduct.zero_tmul]
  | add y z hy hz => simp only [map_add (f := _), hy, hz, add_zero]



open Classical in
theorem compFin_add_cA_eq_one : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ PP ∈ Z,
    compFin D.host.F D.host.E ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (e + cA D e) = 1 := by
  intro D Z e he PP hPP
  classical
  obtain ⟨⟨es, hes, rfl⟩, hcc⟩ := he
  obtain ⟨v0, τ0, -, hPP0⟩ := GlobalTheory.SplitIdemDict.exists_emb (hes PP hPP)
  have hu : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v0 := by rw [hPP0]; exact splitPrime_under τ0
  rw [hu]
  have key : ∀ Q ∈ Z, compFin D.host.F D.host.E v0 (es Q) =
      (if Q = PP then splitIdem (isCMExt_host D) τ0 else 0) +
        (if Q = splitPrime (τ0.comp D.sp.cm.sig) then 1 - splitIdem (isCMExt_host D) τ0 else 0) := by
    intro Q hQ
    obtain ⟨v, τ, hI, hQτ⟩ := GlobalTheory.SplitIdemDict.exists_emb (hes Q hQ)
    have hQv : Q.under (𝓞 D.host.F) = v := by rw [hQτ]; exact splitPrime_under τ
    rw [GlobalTheory.SplitIdemDict.eq_idem hI, GlobalTheory.EmbChart.idem]
    by_cases hv : v = v0
    · subst hv
      rcases eq_or_eq_comp_conj (isCMExt_host D) τ0 τ with h | h <;> rw [h] at hQτ ⊢
      · rw [if_pos (hQτ.trans hPP0.symm), if_neg (by rw [hQτ]; exact (splitPrime_comp_ne (isCMExt_host D) τ0).symm),
          add_zero]
        exact GlobalTheory.EmbChart.compFin_tensAt _ _
      · rw [if_neg (by rw [hQτ, hPP0]; exact splitPrime_comp_ne (isCMExt_host D) τ0), if_pos hQτ, zero_add,
          GlobalTheory.EmbChart.compFin_tensAt, splitIdem_comp]
    · have h1 : Q ≠ PP := fun h => hv (by rw [← hQv, h, hu])
      have h2 : Q ≠ splitPrime (τ0.comp D.sp.cm.sig) := fun h => hv (by rw [← hQv, h]; exact splitPrime_under _)
      rw [if_neg h1, if_neg h2, add_zero]
      exact compFin_tensAt_ne (Ne.symm hv) _
  have hsum : compFin D.host.F D.host.E v0 (∑ Q ∈ Z, es Q) = splitIdem (isCMExt_host D) τ0 +
      (if splitPrime (τ0.comp D.sp.cm.sig) ∈ Z then 1 - splitIdem (isCMExt_host D) τ0 else 0) := by

    rw [map_sum, Finset.sum_congr rfl key]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos hPP]
  have hc : compFin D.host.F D.host.E v0 (cA D (∑ Q ∈ Z, es Q)) =
      sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v0 (∑ Q ∈ Z, es Q)) :=
    (GlobalTheory.SplitIdemDict.compFin_cA _).symm
  have h1 : ∀ a : Fv D.host.F v0 ⊗[D.host.F] D.host.E, a + (1 - a) = 1 := fun a => by abel
  rw [map_add (f := _), hc, hsum]
  by_cases hP' : splitPrime (τ0.comp D.sp.cm.sig) ∈ Z
  · exfalso
    have hz := congrArg (compFin D.host.F D.host.E v0) hcc
    rw [map_mul, hc, hsum, if_pos hP', h1, map_one, mul_one, map_zero] at hz
    have h3 := congrArg (fun y => splitProj τ0 y) hz
    simp only [map_one, map_zero] at h3
    exact one_ne_zero h3
  · rw [if_neg hP', add_zero, sigR_splitIdem, h1]

end GlobalTheory.CompFinIdemSum

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GfCut

variable {R : Type} [CommRing R] {n : ℕ}

theorem idem_mul (φ : R) (hφ : φ * φ = φ) (A B : Matrix (Fin n) (Fin n) R)
    (h : A * B = 1) : (φ • A + (1 - φ) • (1 : Matrix (Fin n) (Fin n) R)) * (φ • B + (1 - φ) • 1) = 1 := by
  have h1 : φ * (1 - φ) = 0 := by rw [mul_sub, mul_one, hφ, sub_self]
  have h2 : (1 - φ) * φ = 0 := by rw [mul_comm, h1]
  have h3 : (1 - φ) * (1 - φ) = 1 - φ := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, hφ, zero_smul, mul_one, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem map_idem {T : Type} [CommRing T] (ψ : R →+* T) (f : R) (M : Matrix (Fin n) (Fin n) R) :
    (f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)).map ψ = ψ f • M.map ψ + (1 - ψ f) • 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add (f := _),
    map_mul, map_sub, map_one]
  split_ifs <;> simp

theorem idem_unitary (σ : R →+* R) (ε : R) (hε : σ ε = ε) (hεε : ε * ε = ε) (J M : Matrix (Fin n) (Fin n) R)
    (h : Formalism.UG.cT σ M * J * M = J) :
    Formalism.UG.cT σ (ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) * J * (ε • M + (1 - ε) • 1) = J :=
  _root_.GlobalTheory.TruncationIsometry.cut_isometry σ ε hε hεε J M h

end GlobalTheory.GfCut

open GlobalTheory.GfCut in
theorem GlobalTheory.GfCut.exists_cut : ∀ {D : D7} (T : HSp D) (g : GA D T) (ε : AE D), g ∈ GfC T → ε * ε = ε → cA D ε = ε → ∃ k : GA D T, k ∈ GfC T ∧ Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
  intro D T g ε hg hεε hε
  set M := Formalism.L2.Theta.mt T g with hM
  have hinv : M * ((matHom T g)⁻¹).1 = 1 := (matHom T g).mul_inv
  have hinv' : ((matHom T g)⁻¹).1 * M = 1 := (matHom T g).inv_mul
  let K : GL (Fin T.rank) (AE D) := ⟨ε • M + (1 - ε) • 1, ε • ((matHom T g)⁻¹).1 + (1 - ε) • 1,
    idem_mul ε hεε _ _ hinv, idem_mul ε hεε _ _ hinv'⟩
  have hgU : Formalism.UG.cT (cA D) M * T.gram.map (incA D) * M = T.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig T.gram from g).2
  have hKU : K ∈ HR (AF D.host.F) D.sp.cm.sig T.gram :=
    idem_unitary (cA D) ε hε hεε _ M hgU
  let k : GA D T := (⟨K, hKU⟩ : HR (AF D.host.F) D.sp.cm.sig T.gram)
  refine ⟨k, ?_, rfl⟩
  have hg1 : infHom T g = 1 := hg
  show infHom T k = 1
  have hg2 := congrArg Units.val hg1
  apply Units.ext
  change (ε • M + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))).map _ = 1
  rw [map_idem]
  change M.map _ = 1 at hg2
  rw [hg2, ← add_smul, add_sub_cancel, one_smul]

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemLevRed

theorem mem_lev_of_reductions : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (y : GL (Fin T.rank) (EAf D)), LT.Q = ∅ → y ∈ UA D.sp.cm T.gram → y ∈ St βT → ∀ (a b : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1)), (∀ PP, a PP ∈ blockTri (blkOf LT.r LT.t)) → (∀ PP, b PP ∈ blockTri (blkOf LT.r LT.t)) → (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H → (fun PP => upperLeftBlock LT.hr (b PP)) ∈ LT.P.H → (∀ PP : ↥LT.Pg, b PP * redFn βT PP.1 y = a PP) → y ∈ lev D.sp.cm T.gram βT LT := by
  intro D T βT LT y hQ hU hS a b ha hb hHa hHb hab
  have hred : ∀ PP : ↥LT.Pg, redFn βT PP.1 y = (b PP)⁻¹ * a PP := fun PP => by
    rw [← hab PP, inv_mul_cancel_left]
  refine mem_lev.2 ⟨mem_parLev.2 ⟨hU, hS, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
  · rw [hred ⟨PP, hP⟩]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hb ⟨PP, hP⟩)) (ha ⟨PP, hP⟩)
  · rw [hQ] at hP
    exact absurd hP (Finset.notMem_empty PP)
  · have h1 : rTup βT LT y = (fun PP => upperLeftBlock LT.hr (b PP)) ⁻¹ * (fun PP => upperLeftBlock LT.hr (a PP)) := by
      funext PP
      have hb2 := blockTri_blkOf_le LT.r LT.t (hb PP)
      have ha2 := blockTri_blkOf_le LT.r LT.t (ha PP)
      show upperLeftBlock LT.hr (redFn βT PP.1 y) = (upperLeftBlock LT.hr (b PP))⁻¹ * upperLeftBlock LT.hr (a PP)
      rw [hred PP]
      unfold upperLeftBlock
      rw [extendMatrixByIdentityAlongIndices_mul _ (Subgroup.inv_mem _ hb2) ha2, extendOne_inv _ hb2]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hHb) hHa

end GlobalTheory.MemLevRed
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjIntegral

theorem mul_int {R : Type} [CommRing R] (S : Subring R) {n : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) (i j : Fin n) : (A * B) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact S.sum_mem fun k _ => S.mul_mem (hA i k) (hB k j)

theorem conj_int {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (G Gi γ γi : Matrix (Fin n) (Fin n) R) (hG : ∀ i j, G i j ∈ S) (hGi : ∀ i j, Gi i j ∈ S) (hGG : Gi * G = 1)
    (hγ : γ * γi = 1) (hu : (γ.map σ)ᵀ * G * γ = G) (a : R) (ha : ∀ i j, (a • γ) i j ∈ S) :
    ∀ i j, (σ a • γi) i j ∈ S := by
  have e1 : γi = Gi * (γ.map σ)ᵀ * G := by
    calc γi = Gi * G * γi := by rw [hGG, Matrix.one_mul]
      _ = Gi * ((γ.map σ)ᵀ * G * γ) * γi := by rw [hu]
      _ = Gi * (γ.map σ)ᵀ * G * (γ * γi) := by simp only [Matrix.mul_assoc]
      _ = Gi * (γ.map σ)ᵀ * G := by rw [hγ, Matrix.mul_one]
  have e2 : σ a • γi = Gi * ((a • γ).map σ)ᵀ * G := by
    have : (a • γ).map σ = σ a • γ.map σ := by
      ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
    rw [this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, e1]
  have hc : ∀ i j, ((a • γ).map σ)ᵀ i j ∈ S := fun i j => hσ _ (ha j i)
  rw [e2]
  exact mul_int S (mul_int S hGi hc) hG

theorem conj_int_both {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (G Gi γ γi : Matrix (Fin n) (Fin n) R) (hG : ∀ i j, G i j ∈ S) (hGi : ∀ i j, Gi i j ∈ S) (hGG : Gi * G = 1)
    (hγ : γ * γi = 1) (hγ' : γi * γ = 1) (hu : (γ.map σ)ᵀ * G * γ = G) (a : R)
    (ha : ∀ i j, (a • γ) i j ∈ S) (ha' : ∀ i j, (a • γi) i j ∈ S) :
    (∀ i j, (σ a • γ) i j ∈ S) ∧ (∀ i j, (σ a • γi) i j ∈ S) := by
  have hu' : (γi.map σ)ᵀ * G * γi = G := by
    have h1 : (γi.map σ)ᵀ * (γ.map σ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hγ, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
    calc (γi.map σ)ᵀ * G * γi = (γi.map σ)ᵀ * ((γ.map σ)ᵀ * G * γ) * γi := by rw [hu]
      _ = ((γi.map σ)ᵀ * (γ.map σ)ᵀ) * G * (γ * γi) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, hγ, Matrix.one_mul, Matrix.mul_one]
  exact ⟨conj_int S σ hσ G Gi γi γ hG hGi hGG hγ' hu' a ha', conj_int S σ hσ G Gi γ γi hG hGi hGG hγ hu a ha⟩

theorem unit_conj {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (B Bi H J : Matrix (Fin n) (Fin n) R)
    (hB : Bi * B = 1) (hB' : B * Bi = 1) (hH : Formalism.UG.cT σ H * J * H = J) :
    ((Bi * H * B).map σ)ᵀ * (Formalism.UG.cT σ B * J * B) * (Bi * H * B) = Formalism.UG.cT σ B * J * B := by
  have hcT : ∀ A C : Matrix (Fin n) (Fin n) R, Formalism.UG.cT σ (A * C) = Formalism.UG.cT σ C * Formalism.UG.cT σ A := by
    intro A C; simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have e : Formalism.UG.cT σ Bi * Formalism.UG.cT σ B = 1 := by
    rw [← hcT, hB']
    simp only [Formalism.UG.cT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  change Formalism.UG.cT σ (Bi * H * B) * _ * _ = _
  rw [hcT, hcT]
  calc Formalism.UG.cT σ B * (Formalism.UG.cT σ H * Formalism.UG.cT σ Bi) * (Formalism.UG.cT σ B * J * B) * (Bi * H * B)
      = Formalism.UG.cT σ B * (Formalism.UG.cT σ H * (Formalism.UG.cT σ Bi * Formalism.UG.cT σ B) * J * (B * Bi) * H) * B := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ B * J * B := by rw [e, hB', Matrix.mul_one, Matrix.mul_one, hH]

end GlobalTheory.ConjIntegral

namespace GlobalTheory.ConjIntegral



theorem conj_smul_isIntM : ∀ {D : D7} (T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC T ΛT → IsFrame βT ΛT → ∀ (h : GL (Fin T.rank) (EAf D)), h ∈ UA D.sp.cm T.gram → ∀ (γ : GL (Fin T.rank) (EAf D)), γ = βT⁻¹ * h * βT → ∀ (a : AE D), IsIntM (toEAf D a • γ.1) → IsIntM (toEAf D a • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) → IsIntM (toEAf D (cA D a) • γ.1) ∧ IsIntM (toEAf D (cA D a) • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) := by
  intro D T ΛT βT hsd hβ h hh γ hγ a h1 h2
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D T ΛT hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) T.gram βT ΛT hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  have hσ : ∀ x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun _ hx => GlobalTheory.LevSplit.sigR_int hx
  have hGm : ∀ i j, (intGL D.host.F D.host.E T.rank G).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i j => (G.1 i j).2
  have hGi : ∀ i j, (intGL D.host.F D.host.E T.rank G⁻¹).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i j => ((G⁻¹).1 i j).2
  have hGG : (intGL D.host.F D.host.E T.rank G⁻¹).1 * (intGL D.host.F D.host.E T.rank G).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

  have hhu : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) h.1 * T.gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) * h.1 =
      T.gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) := hh
  have hγ1 : γ.1 = (βT⁻¹).1 * h.1 * βT.1 := by rw [hγ]; rfl
  have hu := unit_conj (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) βT.1 (βT⁻¹).1 h.1 _
    (Units.inv_mul βT) (Units.mul_inv βT) hhu
  rw [← hγ1, ← hG] at hu
  have key := conj_int_both _ _ hσ _ _ γ.1 (γ⁻¹).1 hGm hGi hGG (Units.mul_inv γ) (Units.inv_mul γ) hu (toEAf D a) h1 h2
  rw [GlobalTheory.AdelicLatMove.toEAf_cA a]
  exact key

end GlobalTheory.ConjIntegral
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSupp

theorem smul_mul_mul_of_smul_eq {R : Type} [CommRing R] {a b c d : Type} [Fintype b] [Fintype c]
    (r : R) (A : Matrix a b R) (N : Matrix b c R) (B : Matrix c d R) (h : r • N = N) :
    r • (A * N * B) = A * N * B := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]

theorem map_smul_of_smul_eq {R S : Type} [CommRing R] [CommRing S] {a b : Type} (f : R →+* S)
    (r : R) (N : Matrix a b R) (h : r • N = N) : f r • N.map f = N.map f := by
  ext k l
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [← map_mul]
  congr 1
  simpa [Matrix.smul_apply, smul_eq_mul] using congrFun (congrFun h k) l

theorem frMapAdj_supp : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T), e * e = e → IsHalf (cA D e) x → ∀ i j, toEAf D e * frMapAdj S T βS βT x i j = frMapAdj S T βS βT x i j := by
  intro D S T βS βT e x he hx i j
  have hN : e • (x.map (cA D))ᵀ = (x.map (cA D))ᵀ := by
    ext k l
    simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul]
    have h1 := hx l k
    have h2 : cA D (x l k) = e * cA D (x l k) := by
      conv_lhs => rw [← h1]
      rw [map_mul, cA_cA]
    exact h2.symm
  have hM := smul_mul_mul_of_smul_eq e ((S.gram⁻¹).map (incA D)) _ (T.gram.map (incA D)) hN
  have hM' := map_smul_of_smul_eq (toEAf D) e _ hM
  have hF := smul_mul_mul_of_smul_eq (toEAf D e) (βS⁻¹).val _ βT.val hM'
  have := congrFun (congrFun hF i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this

end GlobalTheory.HalfSupp
end
