module

public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalRingCardinality.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle038
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle078
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Formalism.LocalRingCardinality.Params
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

section

open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

theorem minor_smul_eq_rowSpace_of_cofVec_orth (K V : Type) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (r : ℕ)
    (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (b₀ : Fin (r + 1)) (u : Fin (r + 1) → V)
    (hu : ∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b • u b = 0) (b : Fin (r + 1)) :
    (Y.submatrix id b₀.succAbove).det • u b =
      ∑ a, Y a b • ∑ c, (Y.submatrix id b₀.succAbove).adjugate c a • u (b₀.succAbove c) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  have hφ : ∀ (x : 𝓞 K) (v : V), φ (x • v) = algebraMap (𝓞 K) K x * φ v := by
    intro x v
    rw [← algebraMap_smul K x v, map_smul, smul_eq_mul]
  have hsub : ∀ b' : Fin (r + 1), (Y.map (algebraMap (𝓞 K) K)).submatrix id b'.succAbove
      = (algebraMap (𝓞 K) K).mapMatrix (Y.submatrix id b'.succAbove) := by
    intro b'; ext i j; simp
  have h0 : ∑ b, φ (u b) * Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Y.map (algebraMap (𝓞 K) K)) b = 0 := by
    have := congrArg φ hu

    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [hφ, mul_comm]
    congr 1
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec
    rw [hsub, ← RingHom.map_det, map_mul, map_pow, map_neg, map_one]
  have h := congrFun ((Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.kernelRowSpace K r (Y.map (algebraMap (𝓞 K) K))).2
    (fun b => φ (u b)) h0 b₀) b
  rw [hsub, ← RingHom.map_det, ← RingHom.map_adjugate] at h

  rw [map_sub, sub_eq_zero, hφ, map_sum]
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [h]

  simp only [Matrix.vecMul, dotProduct, hφ, map_sum, RingHom.mapMatrix_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]

theorem exists_reps_ideal_inv_lattice (K V : Type) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (S0 : Submodule (𝓞 K) V) (J : Ideal (𝓞 K)) (hS : S0.FG)
    (hJ : J ≠ ⊥) :
    ∃ R : Finset V, R.card ≤ Ideal.absNorm J ^ finrank K (Submodule.span K (S0 : Set V)) ∧
      ∀ x : V, (∀ j ∈ J, j • x ∈ S0) → ∃ y ∈ R, x - y ∈ S0 := by
  classical
  let P : Submodule (𝓞 K) V :=
    { carrier := {x | ∀ j ∈ J, j • x ∈ S0}
      add_mem' := fun {a b} ha hb j hj => by
        rw [smul_add]; exact S0.add_mem (ha j hj) (hb j hj)
      zero_mem' := fun j hj => by simp
      smul_mem' := fun c x hx j hj => by
        rw [smul_comm]; exact S0.smul_mem c (hx j hj) }
  obtain ⟨j₀, hj₀, hj₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  have hj₀K : algebraMap (𝓞 K) K j₀ ≠ 0 := fun h => hj₀0 (hinj (by simpa using h))
  have : Module.IsTorsionFree (𝓞 K) V := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c x h => ?_
    rw [← algebraMap_smul K c x, smul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (hinj (by simpa using h))
    · exact Or.inr h
  have : Module.Finite (𝓞 K) S0 := Module.Finite.iff_fg.mpr hS
  let f : P →ₗ[𝓞 K] S0 := (j₀ • P.subtype).codRestrict S0 (fun x => x.2 j₀ hj₀)
  have hf : Function.Injective f := by
    intro x y h
    have h' : j₀ • (x : V) = j₀ • (y : V) := congrArg Subtype.val h
    exact Subtype.ext (smul_right_injective V hj₀0 h')
  have : Module.Finite (𝓞 K) P := Module.Finite.of_injective f hf
  have : Module.FinitePresentation (𝓞 K) P := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 K) P := inferInstance
  have : Module.Projective (𝓞 K) P := Module.Flat.projective_of_finitePresentation
  have hcard := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.projQuotCard K P J hJ
  have hN : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hrk : finrank (𝓞 K) P ≤ finrank K (Submodule.span K (S0 : Set V)) := by
    obtain ⟨g, hg⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := P) le_rfl
    have hmem : ∀ i, (g i : V) ∈ Submodule.span K (S0 : Set V) := by
      intro i
      have h1 : j₀ • (g i : V) ∈ Submodule.span K (S0 : Set V) :=
        Submodule.subset_span ((g i).2 j₀ hj₀)
      rw [← algebraMap_smul K j₀] at h1
      exact (Submodule.smul_mem_iff _ hj₀K).mp h1
    have hg1 : LinearIndependent (𝓞 K) (fun i => (g i : V)) :=
      hg.map' P.subtype (Submodule.ker_subtype P)
    have hg2 : LinearIndependent K (fun i => (g i : V)) :=
      (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hg1
    have hg3 : LinearIndependent K
        (fun i => (⟨g i, hmem i⟩ : Submodule.span K (S0 : Set V))) :=
      LinearIndependent.of_comp (Submodule.span K (S0 : Set V)).subtype hg2
    simpa using hg3.fintype_card_le_finrank
  have : Finite (P ⧸ (J • ⊤ : Submodule (𝓞 K) P)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hN)
  have : Fintype (P ⧸ (J • ⊤ : Submodule (𝓞 K) P)) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : P ⧸ (J • ⊤ : Submodule (𝓞 K) P) => ((Quotient.out q : P) : V)),
    ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hN) hrk
  · intro x hx
    let x' : P := ⟨x, hx⟩
    let q : P ⧸ (J • ⊤ : Submodule (𝓞 K) P) := Submodule.Quotient.mk x'
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ q), ?_⟩
    have h1 : x' - Quotient.out q ∈ (J • ⊤ : Submodule (𝓞 K) P) :=
      (Submodule.Quotient.eq _).mp (Quotient.out_eq q).symm
    have h2 : ∀ z ∈ (J • ⊤ : Submodule (𝓞 K) P), (z : V) ∈ S0 := by
      intro z hz
      refine Submodule.smul_induction_on hz (fun j hj n _ => n.2 j hj) (fun a b ha hb => ?_)
      exact S0.add_mem ha hb
    exact h2 _ h1

theorem exists_reps_cofVec_orth_mod_rowSpace :
    ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (S0 B : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)) (r s : ℕ) (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (b₀ : Fin (r + 1)), S0.FG → finrank K (Submodule.span K (S0 : Set V)) = s → I ≠ ⊥ → I • B ≤ S0 → (Y.submatrix id b₀.succAbove).det ≠ 0 → ∃ reps : Finset (Fin (r + 1) → V), reps.card ≤ Ideal.absNorm (Ideal.span {(Y.submatrix id b₀.succAbove).det} * I) ^ (s * r) ∧ ∀ u : Fin (r + 1) → V, (∀ b, u b ∈ B) → ∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b • u b = 0 → ∃ u₀ ∈ reps, ∃ v : Fin r → V, (∀ a, v a ∈ S0) ∧ ∀ b, u b = u₀ b + ∑ a, Y a b • v a := by
  intro K V _ _ _ _ _ _ _ _ S0 B I r s Y b₀ hS hs hI hIB hd
  classical
  set d := (Y.submatrix id b₀.succAbove).det with hd_def
  have hJ : Ideal.span {d} * I ≠ ⊥ := by
    refine mul_ne_zero ?_ hI
    simpa using hd
  obtain ⟨R, hR, hrep⟩ := exists_reps_ideal_inv_lattice K V S0 _ hS hJ
  rw [hs] at hR
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := fun h =>
    hd (IsFractionRing.injective (𝓞 K) K (by simpa using h))
  refine ⟨(Fintype.piFinset fun _ : Fin r => R).image (fun w b => ∑ a, Y a b • w a), ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    exact Nat.pow_le_pow_left hR r
  · intro u huB hu
    let w : Fin r → V := fun a =>
      ∑ c, (Y.submatrix id b₀.succAbove).adjugate c a • u (b₀.succAbove c)
    have hwB : ∀ a, w a ∈ B := fun a =>
      B.sum_mem fun c _ => B.smul_mem _ (huB _)
    let v' : Fin r → V := fun a => (algebraMap (𝓞 K) K d)⁻¹ • w a
    have hdv : ∀ a, d • v' a = w a := fun a => by
      rw [← algebraMap_smul K d, smul_inv_smul₀ hdK]
    have huv : ∀ b, u b = ∑ a, Y a b • v' a := by
      intro b
      have h := minor_smul_eq_rowSpace_of_cofVec_orth K V r Y b₀ u hu b
      apply smul_right_injective V hdK
      simp only [algebraMap_smul]
      rw [h, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_comm d, hdv]
    have hv' : ∀ a, ∀ j ∈ Ideal.span {d} * I, j • v' a ∈ S0 := by
      intro a j hj
      obtain ⟨i, hi, rfl⟩ := Ideal.mem_span_singleton_mul.mp hj
      rw [mul_comm, mul_smul, hdv]
      exact hIB (Submodule.smul_mem_smul hi (hwB a))
    choose y hyR hy using fun a => hrep (v' a) (hv' a)
    refine ⟨_, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.mpr hyR), fun a => v' a - y a, hy, ?_⟩
    intro b
    rw [huv b, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_add, add_sub_cancel]

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_ideal_coprime_conj_mul_eq_spanSingleton :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
      Formalism.BasicNotions.CMData F E → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 →
      ∀ N : 𝓞 E, N ≠ 0 → ∃ P : Ideal (𝓞 E), P ≠ ⊥ ∧
        P ⊔ P.comap (RingOfIntegers.mapRingHom (starRingEnd E)) = ⊤ ∧
        (∃ t : 𝓞 E, ∃ p ∈ P, t * N + p = 1) ∧
        ∃ α : E, (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c =
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) α := by
  intro F E _ _ _ _ _ _ hcm c hc N hN
  obtain ⟨a, hac, hQ, hp⟩ := GlobalTheory.T.exists_mem_fractionalIdeal_primitive_local_generator' F E hcm.deg2 c hc N hN

  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨p, hpm⟩ := Ideal.exists_maximal (𝓞 F)
    exact hp p hpm (Submodule.zero_mem _)

  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a * c⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hc]
    exact mul_le_mul' (FractionalIdeal.spanSingleton_le_iff_mem.mpr hac) le_rfl
  obtain ⟨P, hP⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hPc : (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a := by
    rw [hP, mul_assoc, inv_mul_cancel₀ hc, mul_one]

  have key : ∀ Q : Ideal (𝓞 E), P ≤ Q → a ∈ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
    intro Q hPQ
    rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← hPc]
    exact mul_le_mul' ((FractionalIdeal.coeIdeal_le_coeIdeal E).mpr hPQ) le_rfl
  have hσσ : ∀ x : 𝓞 E, RingOfIntegers.mapRingHom (starRingEnd E)
      (RingOfIntegers.mapRingHom (starRingEnd E) x) = x := by
    intro x
    ext
    simp
  refine ⟨P, ?_, ?_, ?_, a, hPc⟩
  · rintro rfl
    apply ha
    rw [FractionalIdeal.coeIdeal_bot, zero_mul, eq_comm,
      FractionalIdeal.spanSingleton_eq_zero_iff] at hPc
    exact hPc
  · by_contra htop
    obtain ⟨Q, hQm, hPQ⟩ := Ideal.exists_le_maximal _ htop
    have h1 : P ≤ Q := le_sup_left.trans hPQ
    have h2 : P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E)) := by
      intro x hx
      apply hPQ (Ideal.mem_sup_right _)
      show RingOfIntegers.mapRingHom (starRingEnd E) (RingOfIntegers.mapRingHom (starRingEnd E) x) ∈ P
      rw [hσσ]
      exact hx
    have h3 := GlobalTheory.T.le_map_comap_of_le_conj_maximal_cmData F E hcm P Q hQm h1 h2
    have hpm : (Q.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) Q
    exact hp _ hpm (key _ h3)
  · have htop : P ⊔ Ideal.span {N} = ⊤ := by
      by_contra htop
      obtain ⟨Q, hQm, hPQ⟩ := Ideal.exists_le_maximal _ htop
      exact hQ Q hQm (hPQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self N)))
        (key Q (le_sup_left.trans hPQ))
    have h1 : (1 : 𝓞 E) ∈ P ⊔ Ideal.span {N} := htop ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact ⟨t, y, hy, by rw [add_comm]; exact hyz⟩

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

noncomputable section

namespace GlobalTheory.ConjCoeff

theorem conj_mem_delSq {n : ℕ} (lam : DomWeight n) {p : MvPolynomial (Fin n × Fin n) ℂ}
    (hp : p ∈ delSq ℂ n lam) : MvPolynomial.map (starRingEnd ℂ) p ∈ delSq ℂ n lam := by
  induction hp using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine Submodule.subset_span ⟨v, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

theorem conj_rowAct {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      Formalism.GradedWeylDivisibility.rowAct ℂ (g.map (starRingEnd ℂ)) (MvPolynomial.map (starRingEnd ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : ∀ (h : Matrix (Fin n) (Fin n) ℂ) (b : ℂ), Formalism.GradedWeylDivisibility.rowAct ℂ h (MvPolynomial.C b :
        MvPolynomial (Fin n × Fin n) ℂ) = MvPolynomial.C b := fun h b =>
      (Formalism.GradedWeylDivisibility.rowAct ℂ h).commutes b
    rw [h, MvPolynomial.map_C, h]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.map_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct]

theorem fockF_conj {σ : Type} (p q : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) =
      Formalism.REAL.fockF q p := by
  classical
  have hs : (MvPolynomial.map (starRingEnd ℂ) p).support = p.support :=
    MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective
  unfold Formalism.REAL.fockF
  rw [hs]
  have h1 : ∑ m ∈ p.support, AddMonoidAlgebra.coeff (MvPolynomial.map (starRingEnd ℂ) p) m *
        star (AddMonoidAlgebra.coeff (MvPolynomial.map (starRingEnd ℂ) q) m) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
      ∑ m ∈ p.support ∪ q.support, AddMonoidAlgebra.coeff q m * star (AddMonoidAlgebra.coeff p m) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
    refine Finset.sum_subset_zero_on_sdiff Finset.subset_union_left ?_ ?_
    · intro m hm
      have : AddMonoidAlgebra.coeff p m = 0 := by
        simpa using (Finset.mem_sdiff.1 hm).2
      simp [this]
    · intro m _
      simp only [MvPolynomial.coeff_map]
      simp [mul_comm]
  have h2 : ∑ m ∈ q.support, AddMonoidAlgebra.coeff q m * star (AddMonoidAlgebra.coeff p m) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
      ∑ m ∈ p.support ∪ q.support, AddMonoidAlgebra.coeff q m * star (AddMonoidAlgebra.coeff p m) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
    refine Finset.sum_subset_zero_on_sdiff Finset.subset_union_right ?_ (fun _ _ => rfl)
    intro m hm
    have : AddMonoidAlgebra.coeff q m = 0 := by
      simpa using (Finset.mem_sdiff.1 hm).2
    simp [this]
  rw [h1, h2]

theorem conj_coefficients : ∀ (n : ℕ) (lam : DomWeight n), (∀ p ∈ delSq ℂ n lam, MvPolynomial.map (starRingEnd ℂ) p ∈ delSq ℂ n lam) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ), MvPolynomial.map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) = Formalism.GradedWeylDivisibility.rowAct ℂ (g.map (starRingEnd ℂ)) (MvPolynomial.map (starRingEnd ℂ) p)) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) ℂ, normFock lam (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) = normFock lam q p := by
  intro n lam
  refine ⟨fun p hp => conj_mem_delSq lam hp, conj_rowAct, fun p q => ?_⟩
  rw [normFock, normFock, fockF_conj]

end GlobalTheory.ConjCoeff
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem conjLinear_onto_of_injective_of_le_range :
    ∀ (W M : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (J₀ J₁ : W →ₗ⋆[ℂ] M), (∀ p ∈ S, ∃ ξ, J₀ ξ = p) → Function.Injective J₁ → (∀ ξ, J₁ ξ ∈ S) → ∀ p ∈ S, ∃ ξ, J₁ ξ = p := by
  intro W M _ _ _ _ _ S J₀ J₁ h0 hinj hS
  let f0 : W →ₗ[ℝ] M :=
    { toFun := J₀
      map_add' := J₀.map_add
      map_smul' := fun r x => by
        show J₀ (r • x) = r • J₀ x
        rw [← Complex.coe_smul, J₀.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }
  let f1 : W →ₗ[ℝ] M :=
    { toFun := J₁
      map_add' := J₁.map_add
      map_smul' := fun r x => by
        show J₁ (r • x) = r • J₁ x
        rw [← Complex.coe_smul, J₁.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }

  have hle0 : S.restrictScalars ℝ ≤ LinearMap.range f0 := fun p hp => h0 p hp
  have hle1 : LinearMap.range f1 ≤ S.restrictScalars ℝ := by
    rintro _ ⟨ξ, rfl⟩
    exact hS ξ
  have hf1 : Function.Injective f1 := hinj
  have : FiniteDimensional ℝ (S.restrictScalars ℝ) := Submodule.finiteDimensional_of_le hle0
  have hdim : Module.finrank ℝ (S.restrictScalars ℝ) ≤ Module.finrank ℝ (LinearMap.range f1) := by
    rw [LinearMap.finrank_range_of_inj hf1]
    exact (Submodule.finrank_mono hle0).trans (LinearMap.finrank_range_le f0)

  have heq : LinearMap.range f1 = S.restrictScalars ℝ := Submodule.eq_of_le_of_finrank_le hle1 hdim
  intro p hp
  have hp' : p ∈ LinearMap.range f1 := heq ▸ hp
  obtain ⟨ξ, hξ⟩ := hp'
  exact ⟨ξ, hξ⟩

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem sum_inner_classReps_indep : ∀ (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W), (∀ h v w, ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ) → (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → ∀ (C C' : Type) [Fintype C] [Fintype C'] (s : C → Gf) (s' : C' → Gf), (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s c * (κ : Gf)) → (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s' c * (κ : Gf)) → ∀ φ φ' : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) → (∀ (γ : Γ) (x : Gf) (κ : K), φ' (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ' x)) → ∑ c, ⟪φ (s c), φ' (s c)⟫_ℂ = ∑ c, ⟪φ (s' c), φ' (s' c)⟫_ℂ := by
  intro Γ Gi Gf _ _ _ ιi ιf K ψ W _ _ π hπ hψ C C' _ _ s s' hs hs' φ φ' hφ hφ'
  have hf : ∀ (γ : Γ) (x : Gf) (κ : K),
      ⟪φ (ιf γ * x * κ), φ' (ιf γ * x * κ)⟫_ℂ = ⟪φ x, φ' x⟫_ℂ := by
    intro γ x κ
    rw [hφ, hφ', inner_smul_left, inner_smul_right, hπ, ← mul_assoc]
    have hn : ‖(((ψ κ)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hψ κ, inv_one]
    have : (starRingEnd ℂ) (((ψ κ)⁻¹ : ℂˣ) : ℂ) * (((ψ κ)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [RCLike.conj_mul, hn]; simp
    rw [this, one_mul]
  obtain ⟨g, hg⟩ : ∃ g : C → C', ∀ c, ∃ (γ : Γ) (κ : K), s c = ιf γ * s' (g c) * (κ : Gf) :=
    ⟨fun c => (hs' (s c)).exists.choose, fun c => (hs' (s c)).exists.choose_spec⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro c1 c2 h
      obtain ⟨γ1, κ1, h1⟩ := hg c1
      obtain ⟨γ2, κ2, h2⟩ := hg c2
      rw [h] at h1
      refine (hs (s c2)).unique ?_ ⟨1, 1, by simp⟩
      refine ⟨γ2 * γ1⁻¹, κ1⁻¹ * κ2, ?_⟩
      rw [h2, h1]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro c'
      obtain ⟨c, ⟨γ, κ, h⟩, -⟩ := hs (s' c')
      refine ⟨c, (hs' (s c)).unique (hg c) ⟨γ⁻¹, κ⁻¹, ?_⟩⟩
      rw [h]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  refine Fintype.sum_bijective g hbij _ _ (fun c => ?_)
  obtain ⟨γ, κ, h⟩ := hg c
  have := hf γ (s' (g c)) κ
  rw [← h] at this
  exact this

end GlobalTheory
end
