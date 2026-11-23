module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle736
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle593
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle178
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle046
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle643
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle595
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAtAll
public import Formalism.SharpRestriction.SmoothDesignExistence.ContinuousHom
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle738
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle740
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle356
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle549
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle485
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle045
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle017
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle739
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
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.CardJ

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem isUnit_of_mul_eq_one_add_pow (p : R) (hp : ¬ IsUnit p) {n : ℕ} (hn : 1 ≤ n) {x y z : R}
    (h : x * y = 1 + p ^ n * z) : IsUnit x := by
  have hpm : p ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hp
  have hmem : p ^ n * z ∈ IsLocalRing.maximalIdeal R := by
    apply Ideal.mul_mem_right
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]; exact Ideal.mul_mem_left _ _ hpm
  have hu : IsUnit (1 + p ^ n * z) := by
    by_contra hc
    have h1 : (1 + p ^ n * z) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hc
    have h2 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ h1 hmem
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  rw [← h] at hu
  exact isUnit_of_mul_isUnit_left hu

end GlobalTheory.CardJ

namespace GlobalTheory.CardJ

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem exists_cols_of_rightInv (p : R) (hp : ¬ IsUnit p) (d d' n : ℕ)
    (Q : Matrix (Fin d) (Fin d') R) (S : Matrix (Fin d') (Fin d) R)
    (U Uinv : Matrix (Fin d') (Fin d') R) (J : Finset (Fin d')) (hn : 1 ≤ n)
    (hQS : ∀ i j, p ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) R)) i j) (hUU : Uinv * U = 1) (hUU' : U * Uinv = 1)
    (hJ : ∀ j ∉ J, ∀ i, p ^ n ∣ (Q * U) i j)
    (hker : ∀ v : Fin d' → R, (∀ i, p ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, p ∣ (Uinv *ᵥ v) j) :
    ∃ e : Fin d ≃ J, IsUnit (Q * U.submatrix id (fun k => (e k : Fin d'))) ∧
      ∀ i j, p ^ n ∣ (Q - (Q * U.submatrix id (fun k => (e k : Fin d'))) *
        Uinv.submatrix (fun k => (e k : Fin d')) id) i j := by
  classical
  set I : Ideal R := Ideal.span {p ^ n} with hI
  set π : R →+* R ⧸ I := Ideal.Quotient.mk I with hπ
  have hdvd : ∀ x : R, p ^ n ∣ x ↔ π x = 0 := fun x => by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  have hpm : p ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hp
  have hres0 : IsLocalRing.residue R p = 0 := (IsLocalRing.residue_eq_zero_iff p).2 hpm
  have hres : ∀ x : R, π x = 0 → IsLocalRing.residue R x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hdvd x).2 hx
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [map_mul, map_pow, hres0]
  set M := Q * U with hM
  set S' := Uinv * S with hS'
  have hMS : M * S' = Q * S := by
    rw [hM, hS', Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU', Matrix.one_mul]
  have hQS1 : ∀ i j, π ((Q * S) i j) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i j := by
    intro i j
    have := (hdvd _).1 (hQS i j)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hoff : ∀ j ∉ J, ∀ i, π (M i j) = 0 := fun j hj i => (hdvd _).1 (hJ j hj i)
  have hsum : ∀ (i : Fin d) (x : Fin d' → R ⧸ I),
      ∑ j, π (M i j) * x j = ∑ j : J, π (M i (j : Fin d')) * x j := by
    intro i x
    have h1 := Finset.sum_coe_sort J (fun j => π (M i j) * x j)
    rw [h1]
    symm
    apply Finset.sum_subset (Finset.subset_univ J)
    intro j _ hj; rw [hoff j hj i, zero_mul]

  set MJ : Matrix (Fin d) J R := M.submatrix id (fun j : J => (j : Fin d')) with hMJ
  set SJ : Matrix J (Fin d) R := S'.submatrix (fun j : J => (j : Fin d')) id with hSJ
  have hMJS : ∀ i k, π ((MJ * SJ) i k) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i k := by
    intro i k
    rw [← hQS1, ← hMS]

    simp only [Matrix.mul_apply, map_sum, map_mul, hMJ, hSJ, Matrix.submatrix_apply, id]
    exact (hsum i (fun j => π (S' j k))).symm

  have hE : ∀ j j0 : J, IsLocalRing.residue R ((SJ * MJ) j j0) = (1 : Matrix J J (IsLocalRing.ResidueField R)) j j0 := by
    intro j j0
    set c : Fin d' → R := fun j' => if h : j' ∈ J then (SJ * MJ - (1 : Matrix J J R)) ⟨j', h⟩ j0 else 0 with hc
    have hUc : Uinv *ᵥ (U *ᵥ c) = c := by
      rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
    have hQc : ∀ i, p ^ n ∣ (Q *ᵥ (U *ᵥ c)) i := by
      intro i
      rw [Matrix.mulVec_mulVec, ← hM, hdvd]
      have hA : (MJ.map π) * ((SJ * MJ - (1 : Matrix J J R)).map π) = 0 := by
        have h1 : (MJ.map π) * (SJ.map π) = 1 := by
          ext i k; rw [← Matrix.map_mul]; exact hMJS i k
        rw [Matrix.map_sub _ (fun a b => map_sub π a b), Matrix.map_mul, Matrix.map_one _ (map_zero π) (map_one π), Matrix.mul_sub,
          ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_one, sub_self]
      have h2 := congrFun (congrFun hA i) j0
      rw [Matrix.zero_apply, Matrix.mul_apply] at h2
      rw [← h2]

      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [hsum i (fun j' => π (c j'))]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      simp [hc, hMJ, Matrix.map_apply]
    have hp1 := hker _ hQc j j.2
    rw [hUc] at hp1
    have hcj : c j = (SJ * MJ - (1 : Matrix J J R)) j j0 := by simp [hc]
    rw [hcj] at hp1
    obtain ⟨y, hy⟩ := hp1
    have := congrArg (IsLocalRing.residue R) hy
    rw [Matrix.sub_apply, map_sub, map_mul, hres0, zero_mul, sub_eq_zero] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

  have hcard : Fintype.card J = d := by
    set κ := IsLocalRing.ResidueField R
    set ρ : R →+* κ := IsLocalRing.residue R
    have hAB : (MJ.map ρ) * (SJ.map ρ) = 1 := by
      ext i k
      rw [← Matrix.map_mul, Matrix.map_apply]
      have h := hMJS i k
      have h0 : π ((MJ * SJ - (1 : Matrix (Fin d) (Fin d) R)) i k) = 0 := by
        rw [Matrix.sub_apply, map_sub, h, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
      have := hres _ h0
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    have hBA : (SJ.map ρ) * (MJ.map ρ) = 1 := by
      ext j j0; rw [← Matrix.map_mul, Matrix.map_apply]; exact hE j j0
    have h1 : d ≤ Fintype.card J := by
      have := Matrix.rank_mul_le_left (MJ.map ρ) (SJ.map ρ)
      rw [hAB, Matrix.rank_one, Fintype.card_fin] at this
      exact this.trans (Matrix.rank_le_card_width _)
    have h2 : Fintype.card J ≤ d := by
      have := Matrix.rank_mul_le_left (SJ.map ρ) (MJ.map ρ)
      rw [hBA, Matrix.rank_one] at this
      exact (this.trans (Matrix.rank_le_card_width _)).trans (by rw [Fintype.card_fin])
    omega

  let e : Fin d ≃ J := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e, ?_, ?_⟩
  · set T := Q * U.submatrix id (fun k => (e k : Fin d')) with hT
    set B := S'.submatrix (fun k => (e k : Fin d')) id with hB
    have hTe : ∀ i k, T i k = M i (e k) := by
      intro i k; simp [hT, hM, Matrix.mul_apply]
    have hTB : ∀ i k, π ((T * B) i k) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i k := by
      intro i k
      rw [← hQS1, ← hMS]

      simp only [Matrix.mul_apply, map_sum, map_mul, hTe, hB, Matrix.submatrix_apply, id]
      rw [hsum i (fun j => π (S' j k))]
      exact Equiv.sum_comp e (fun j : J => π (M i (j : Fin d')) * π (S' j k))
    have hdet : π ((T * B).det) = 1 := by
      rw [RingHom.map_det]
      have : π.mapMatrix (T * B) = 1 := by ext i k; exact hTB i k
      rw [this, Matrix.det_one]
    rw [Matrix.det_mul] at hdet
    have h0 : π (T.det * B.det - 1) = 0 := by rw [map_sub, hdet, map_one, sub_self]
    obtain ⟨z, hz⟩ := (hdvd _).2 h0
    rw [Matrix.isUnit_iff_isUnit_det]
    exact GlobalTheory.CardJ.isUnit_of_mul_eq_one_add_pow p hp hn (y := B.det) (z := z) (by rw [← hz]; ring)
  · intro i k
    rw [hdvd, Matrix.sub_apply, map_sub, sub_eq_zero]
    have hQ : Q = M * Uinv := by rw [hM, Matrix.mul_assoc, hUU', Matrix.mul_one]
    conv_lhs => rw [hQ]

    simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.submatrix_apply, id]
    rw [hsum i (fun j => π (Uinv j k))]
    rw [← Equiv.sum_comp e (fun j : J => π (M i (j : Fin d')) * π (Uinv j k))]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp [hM, Matrix.mul_apply]

end GlobalTheory.CardJ

namespace GlobalTheory.CardJ

theorem exists_cols_of_rightInv_WCb : ∀ (l : ℕ) [Fact l.Prime] (d d' n : ℕ) (Q : Matrix (Fin d) (Fin d') (WCb l)) (S : Matrix (Fin d') (Fin d) (WCb l)) (U Uinv : Matrix (Fin d') (Fin d') (WCb l)) (J : Finset (Fin d')), 1 ≤ n → (∀ i j, (l : WCb l) ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → Uinv * U = 1 → U * Uinv = 1 → (∀ j ∉ J, ∀ i, (l : WCb l) ^ n ∣ (Q * U) i j) → (∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, (l : WCb l) ∣ (Uinv *ᵥ v) j) → ∃ e : Fin d ≃ J, IsUnit (Q * U.submatrix id (fun k => (e k : Fin d'))) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Q - (Q * U.submatrix id (fun k => (e k : Fin d'))) * Uinv.submatrix (fun k => (e k : Fin d')) id) i j := by
  intro l _ d d' n Q S U Uinv J hn hQS hUU hUU' hJ hker
  haveI : PerfectRing (Cb l) l := GlobalTheory.OEDvr.perfectRing_Cb
  exact exists_cols_of_rightInv (l : WCb l) (WittVector.irreducible l).not_isUnit d d' n Q S U Uinv J
    hn hQS hUU hUU' hJ hker

end GlobalTheory.CardJ
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.HWL

theorem charRep_crys_jump_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  intro l _ P AI hT K LL hA τ₀ x hx _hφn hF1 hF2 hφj c hc μ hcont hμ
  let ι0 := IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1
  have hsurj : Function.Surjective ι0 := fun y =>
    ⟨⟨y.1, IntermediateField.mem_inf.2 ⟨y.2, hA.1 y.2⟩⟩, Subtype.ext rfl⟩
  obtain ⟨emb, hbij, hemb⟩ := GlobalTheory.HWL.exists_letters l P K 1 LL hA.2.2
  haveI : NeZero (finrank ℚ_[l] ↥(K0 K)) := ⟨by haveI := (P.PD K).finK₀; exact Module.finrank_pos.ne'⟩
  have hit : ∀ (j : ℕ) (i : ZMod (finrank ℚ_[l] ↥(K0 K))) (a : ↥(K0 K)),
      emb i ((⇑(P.PD K).σ)^[j] a) = emb (i - j) a := by
    intro j
    induction j with
    | zero => intro i a; simp
    | succ j ih =>
      intro i a
      rw [Function.iterate_succ_apply, ih]
      have h := DFunLike.congr_fun (hemb (i - j - 1)) a
      rw [sub_add_cancel] at h
      rw [AlgHom.comp_apply] at h
      rw [h]
      congr 1
      push_cast
      ring_nf
  obtain ⟨i₀, hi₀⟩ := hbij.2 (τ₀.comp ι0)
  have hμ' : ∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * (τ₀.comp ι0) ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1 :=
    fun g => hμ g
  have key : ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp ι0),
      ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (if τ = τ₀ then 1 else 0) ∧
      ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) ((if τ = τ₀ then 1 else 0) + 1) := by
    intro τ
    obtain ⟨i, hi⟩ := hbij.2 (τ.comp ι0)
    have hj : ∀ a : ↥(K0 K), (τ.comp ι0) ((⇑(P.PD K).σ)^[(i - i₀).val] a) = (τ₀.comp ι0) a := by
      intro a
      rw [← hi, ← hi₀, hit, ZMod.natCast_zmod_val, sub_sub_cancel]
    by_cases hτ : τ = τ₀
    · subst hτ
      have h0 : (i - i₀).val = 0 := by
        rw [hbij.1 (hi.trans hi₀.symm), sub_self, ZMod.val_zero]
      rw [h0] at hj
      have := GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris l P AI hT K LL x hx c hc μ (τ.comp ι0) (τ.comp ι0) 0 hμ' hj 1
        (by simpa using hF1) (by simpa [show (1 : ℤ) + 1 = 2 by norm_num] using hF2)
      simpa using this
    · have hpos : 0 < (i - i₀).val := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        rw [ZMod.val_eq_zero, sub_eq_zero] at h0
        subst h0
        apply hτ
        have hc' : τ.comp ι0 = τ₀.comp ι0 := hi.symm.trans hi₀
        refine AlgHom.ext fun y => ?_
        obtain ⟨z, rfl⟩ := hsurj y
        exact DFunLike.congr_fun hc' z
      have hlt : (i - i₀).val < finrank ℚ_[l] ↥(K0 K) := ZMod.val_lt _
      obtain ⟨h1, h2⟩ := hφj _ hpos hlt
      have := GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris l P AI hT K LL x hx c hc μ (τ₀.comp ι0) (τ.comp ι0) (i - i₀).val hμ' hj 0
        h1 (by simpa using h2)
      simpa [hτ] using this
  have hcrys := GlobalTheory.T.isCrys_character_of_crystalline_vectors l P AI hT K LL hA μ hcont (fun τ => if τ = τ₀ then 1 else 0) key
  exact ⟨hcrys, GlobalTheory.T.crystalline_character_jumps_of_exact_degree l P AI hT K LL hA μ hcont (fun τ => if τ = τ₀ then 1 else 0) key hcrys⟩

end GlobalTheory.HWL
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Links NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeCharacter_trivialOnSubfield_of_idelicReading : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → (∀ a : (AF D.host.F)ˣ, c (idF D a) = 1) → χ.TrivOn D.host.F := by
  first | exact @GlobalTheory.TrivOnRead.trivOn_of_chrEq | exact GlobalTheory.TrivOnRead.trivOn_of_chrEq | (intros; apply GlobalTheory.TrivOnRead.trivOn_of_chrEq <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ClosingStatement

theorem main : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      BlochKatoDuality.Conclusion1 D ∧ BlochKatoDuality.Conclusion2 D := by
  intro hBK hTD hEC D _ _ _
  have h5 : Formalism.MainNotions.LocalSituation.Conclusion5 D := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D
  have a1 : BlochKatoDuality.adm1 D := dimension_input_one_of_bloch_kato D h5
  have a2 : BlochKatoDuality.adm2 D := dimension_input_two_of_bloch_kato D h5
  have a3 : BlochKatoDuality.adm3 D := fun l _ K => GlobalTheory.T.tate_H2_period_datum hTD l (D.loc l) K
  have a5 : BlochKatoDuality.adm5 D := fun l _ K => GlobalTheory.T.finite_H1_period_datum hTD l (D.loc l) K
  have a6 : BlochKatoDuality.adm6 D := fun l _ K => (GlobalTheory.T.tateDual_deRham_and_filZero_dim_all D l K).1
  exact ⟨BlochKatoDuality.ramification_two_and_conjugation_at_q_and_d D a1 a2 a6, BlochKatoDuality.second_proposition_every_localisation D a1 a2 a3 a5 a6⟩

end GlobalTheory.ClosingStatement
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem universalPart_caseA :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → TruncatedSeriesCountingBounds.adm15 D →
      UnusedSlot80.UniversalComponentCaseA D HW F Cm :=
  fun D HW F Cm hAdm h9 hH h15 => Formalism.MainNotions.UnusedSlot80.universal_general_statement_holds D HW F Cm hAdm h9 hH h15

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 100000 in
theorem wachShift_mem_of_N1used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (y' Y : ℕ) (cO : ℤ → ↥(OL LL)), (∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - (((((HW l).W K 1 LL hA.2.2).χΓ ((HW l).W K 1 LL hA.2.2).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) → ∀ xs : List ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hA.2.2) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ((HW l).W K 1 LL hA.2.2).DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ Y • seq 0 ∈ ((HW l).W K 1 LL hA.2.2).N T → (∀ k < xs.length, ((HW l).W K 1 LL hA.2.2).π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) = ((HW l).W K 1 LL hA.2.2).γD T ((HW l).W K 1 LL hA.2.2).gam (seq k) - seq k) → Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ y' • seq xs.length ∈ ((HW l).W K 1 LL hA.2.2).N T := by
  intro D HW F Cm hN l _ K LL hA
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) := hN.2.2.2.2.2.2.2.2.1 l K 1 LL hA.2.2
  obtain ⟨hRg, hRu, hCr⟩ := GlobalTheory.T.expansion_rules_criterion_odd_root_of_unity_caseA D HW F Cm hN l K LL hA
  have hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 := fun hb V _ _ _ _ _ ρ hc =>
    GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc
  intro T hT i y' Y cO hc xs hxs seq h0 h0N hrec
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := Formalism.MainNotions.UnusedSlot80.exists_prim_of_good D hA.2.2
  have hCase := Formalism.MainNotions.UnusedSlot80.caseA_of_le_Kur_of_ne_two
    (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1
  have hpne : (((D.loc l).PD K).p : ↥LL.1) ≠ 0 := by
    rw [hp]
    exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  exact wachShift_mem_of_exp _ h9 hRg hRu hCr hD hCase hpne ζ (by rw [hp]; exact hζ)
    T hT i y' Y cO (fun x => by rw [hp]; exact hc x) xs hxs seq h0 h0N hrec

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.wachOperatorProduct_shift_mem_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (y' Y : ℕ) (cO : ℤ → ↥(OL LL)), (∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - (((((HW l).W K 1 LL hA.2.2).χΓ ((HW l).W K 1 LL hA.2.2).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) → ∀ xs : List ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hA.2.2) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ((HW l).W K 1 LL hA.2.2).DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ Y • seq 0 ∈ ((HW l).W K 1 LL hA.2.2).N T → (∀ k < xs.length, ((HW l).W K 1 LL hA.2.2).π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) = ((HW l).W K 1 LL hA.2.2).γD T ((HW l).W K 1 LL hA.2.2).gam (seq k) - seq k) → Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ y' • seq xs.length ∈ ((HW l).W K 1 LL hA.2.2).N T := by
  intro D HW F Cm hN l _ K LL hA
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) :=
    hN.2.2.2.2.2.2.2.2.1 l K 1 LL hA.2.2
  obtain ⟨hRg, hRu, hCr⟩ :=
    GlobalTheory.T.expansion_rules_criterion_odd_root_of_unity_caseA D HW F Cm hN l K LL hA
  have hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 :=
    fun hb V _ _ _ _ _ ρ hc =>
      GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc
  intro T hT i y' Y cO hc xs hxs seq h0 h0N hrec
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := Formalism.MainNotions.UnusedSlot80.exists_prim_of_good D hA.2.2
  refine GlobalTheory.wachShift_mem_of_exp _ h9 hRg hRu hCr hD
    (Formalism.MainNotions.UnusedSlot80.caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1)
    ?_ ζ (by rw [hp]; exact hζ) T hT i y' Y cO (fun x => by rw [hp]; exact hc x) xs hxs seq h0 h0N hrec
  rw [hp]
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdm

theorem fontaineProperties_all_places : ∀ (D : D7) (i : D.nd.Loc), Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i :=
  fun D i => Formalism.MainNotions.Pk.font_of_all_places (fun l _ K LL => GlobalTheory.FontaineAll.fontaineAt_all D l K LL) i

end GlobalTheory.FontaineAdm
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem elementDenominator_adm7 : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm7 D := by
  intro D l _ _ K LL _ T _
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  exact @GlobalTheory.T.h1f_generated_lattice l _ (D.loc l) (D.locA l) (D.locT l) K LL (Fintype.ofFinite _) T _

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.blochKatoHypothesis_globalStep_at_qd : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := by
  first | exact @GlobalTheory.BKAtQD.admBK_embeddingTypeJumps | exact GlobalTheory.BKAtQD.admBK_embeddingTypeJumps | (intros; apply GlobalTheory.BKAtQD.admBK_embeddingTypeJumps <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.local_fields_at_auxiliary_primes : ∀ D : D7, EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D := by
  first | exact @GlobalTheory.LocalFieldsQD.main | exact GlobalTheory.LocalFieldsQD.main | (intros; apply GlobalTheory.LocalFieldsQD.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.unramifiedTrivialH1f_of_decl : ∀ (D : D7) (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i), Formalism.MainNotions.EmbeddingTypes.UnramifiedTrivialH1f (D := D) i dc := by
  first | exact @GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces | exact GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces | (intros; apply GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces <;> assumption)
end
