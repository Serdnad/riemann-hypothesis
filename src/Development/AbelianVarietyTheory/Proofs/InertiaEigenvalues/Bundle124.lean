module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle101
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSigmaStableProdLatticeExtSq
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle102
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.etaleHermitianPair_eventually_isUnit_continuousAt_inverse : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) := by
  first | exact @GlobalTheory.et_units_near_one_inverse_continuousAt | exact GlobalTheory.et_units_near_one_inverse_continuousAt | (intros; apply GlobalTheory.et_units_near_one_inverse_continuousAt <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), M ∈ (B₁.prod B₂).Lin → M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.lin_fst_snd | exact GlobalTheory.UnitLemma.InvAlg.lin_fst_snd | (intros; apply GlobalTheory.UnitLemma.InvAlg.lin_fst_snd <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.transport_selfDualHaarMeasureKernel_addEquiv : ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ), ((SelfDual μ B ∧ ∀ x : V, AEMeasurable (x + ·) μ) → SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y))) ∧ ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
  intro V V' _ _ _ _ _ _ _ _ h hc hs μ B
  obtain ⟨htransport, hfour⟩ := GlobalTheory.transport_selfDual_fourB h hc hs μ B
  exact ⟨fun hsd => (htransport hsd).1, hfour⟩
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.eventually_testFunction_mul_inverse_unit_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ s in 𝓝 a, ∀ t : A.K, IsUnit t → φ' (s * Ring.inverse t, t) = φ' (a * Ring.inverse t, t) := by
  first | exact @GlobalTheory.eventually_testFn_mul_inverse_eq | exact GlobalTheory.eventually_testFn_mul_inverse_eq | (intros; apply GlobalTheory.eventually_testFn_mul_inverse_eq <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.fourierEtaleK_eq_integral_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → ∀ b c : A.K, A.fourK μK ψ φ' (b, c) = fourB μK (A.kerK ψ) (fun c' => A.tilde μK ψ φ' c' c) b := by
  first | exact @GlobalTheory.FourKFub.fourK_eq_fourB_tilde | exact GlobalTheory.FourKFub.fourK_eq_fourB_tilde | (intros; apply GlobalTheory.FourKFub.fourK_eq_fourB_tilde <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_subring_eq_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  first | exact @GlobalTheory.JR.Et.OK_isSubring | exact GlobalTheory.JR.Et.OK_isSubring | (intros; apply GlobalTheory.JR.Et.OK_isSubring <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isCompact_finiteEtaleHermitianPair_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsCompact A.OK := by
  first | exact @GlobalTheory.JR.OKCompact.okCompact | exact GlobalTheory.JR.OKCompact.okCompact | (intros; apply GlobalTheory.JR.OKCompact.okCompact <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isOpen_finiteEtaleHermitianPair_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsOpen A.OK := by
  first | exact @GlobalTheory.JR.OKOpen.isOpen_OK | exact GlobalTheory.JR.OKOpen.isOpen_OK | (intros; apply GlobalTheory.JR.OKOpen.isOpen_OK <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.card_sigma_stable_prod_lattice_ext_sq : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → ∀ (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A), M₁ ∈ B₁.Lin → M₂ ∈ B₂.Lin → Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧ ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧ M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ^ 2 = Nat.card {M : Submodule K.O (B₁.A × B₂.A) // (∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧ M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} := by
  first | exact @GlobalTheory.SigmaExtCount.card_sigma_stable_ext_sq | exact GlobalTheory.SigmaExtCount.card_sigma_stable_ext_sq | (intros; apply GlobalTheory.SigmaExtCount.card_sigma_stable_ext_sq <;> assumption)
end

section

open GlobalTheory.JR MeasureTheory

theorem _root_.GlobalTheory.T.fourB_prod_iterated_alt : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂] [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂] (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm → ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ), Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) → (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) → ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y, fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := by
  first | exact @GlobalTheory.JR.fourB_prod_iterated | exact GlobalTheory.JR.fourB_prod_iterated | (intros; apply GlobalTheory.JR.fourB_prod_iterated <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem charpoly_companion_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F),
    A.IsGen τ p → (companion p).charpoly.Separable := by
  intro F E _ _ _ _ hU A r τ p hG
  haveI : CharZero F := hU.charZero
  set P := (companion p).charpoly with hP
  have hmon : P.Monic := Matrix.charpoly_monic _
  have hdeg : P.natDegree = r := by rw [hP, Matrix.charpoly_natDegree_eq_dim]; simp
  have hroot : Polynomial.aeval τ P = 0 := by
    apply Algebra.leftMulMatrix_injective (bas A hG)
    rw [map_zero, ← Polynomial.aeval_algHom_apply, leftMul_tau A hG]
    exact Matrix.aeval_self_charpoly _
  have hsmall : ∀ Q : Polynomial F, Q.natDegree < r → Polynomial.aeval τ Q = 0 → Q = 0 := by
    intro Q hQ h0
    rw [Polynomial.aeval_eq_sum_range' hQ] at h0
    rw [← Fin.sum_univ_eq_sum_range (fun i => Q.coeff i • τ ^ i) r] at h0
    have := Fintype.linearIndependent_iff.mp hG.1 (fun i => Q.coeff i) h0
    ext n
    by_cases hn : n < r
    · simpa using this ⟨n, hn⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  rw [PerfectField.separable_iff_squarefree]
  intro q hq
  obtain ⟨s, hs⟩ := hq
  by_contra hqu
  have hP0 : P ≠ 0 := hmon.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hqdeg : 0 < q.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_ne_zero_of_nonunit hq0 hqu)
  have hQ0 : q * s ≠ 0 := mul_ne_zero hq0 hs0
  have hdegQ : (q * s).natDegree < r := by
    have : P.natDegree = q.natDegree + (q * s).natDegree := by
      rw [hs, mul_assoc, Polynomial.natDegree_mul hq0 hQ0]
    omega
  apply hQ0
  apply hsmall _ hdegQ
  have hnil : IsNilpotent (Polynomial.aeval τ (q * s)) := ⟨2, by
    rw [pow_two, ← map_mul]
    have : q * s * (q * s) = P * s := by rw [hs]; ring
    rw [this, map_mul, hroot, zero_mul]⟩
  exact hnil.eq_zero

end GlobalTheory.JR.LinDesc
end

section

open Polynomial Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR

theorem charpoly_companion {k : Type} [Field k] {r : ℕ} (p : Fin r → k) :
    (companion p).charpoly = X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) := by
  set P : k[X] := X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) with hP
  have hlt : (∑ i, C (p i) * X ^ (i : ℕ) : k[X]).degree < r := degree_sum_fin_lt p
  have hm : P.Monic := monic_X_pow_add hlt
  have hd : P.natDegree = r := by
    have : P.degree = r := by
      rw [hP, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  let pb := AdjoinRoot.powerBasis' hm
  have hdim : pb.dim = r := hd
  let b : Module.Basis (Fin r) k (AdjoinRoot P) := pb.basis.reindex (finCongr hdim)
  have hb : ∀ i : Fin r, b i = AdjoinRoot.root P ^ (i : ℕ) := by
    intro i
    simp only [b, Module.Basis.reindex_apply, pb.basis_eq_pow]
    rfl
  have hroot : AdjoinRoot.root P ^ r = ∑ i, (- p i) • b i := by
    have h0 := AdjoinRoot.aeval_eq (f := P) P
    rw [AdjoinRoot.mk_self] at h0
    have h2 : aeval (AdjoinRoot.root P) (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : k[X]) = 0 := h0

    simp only [map_add (f := _), map_pow, map_sum, map_mul, aeval_X, aeval_C] at h2
    rw [eq_neg_of_add_eq_zero_left h2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb, neg_smul, Algebra.smul_def]
  have hmat : companion p = Algebra.leftMulMatrix b (AdjoinRoot.root P) := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb, ← pow_succ']
    simp only [companion, Matrix.of_apply]
    by_cases hj : (j : ℕ) + 1 = r
    · rw [if_pos hj, hj, hroot, ← b.equivFun_symm_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    · rw [if_neg hj]
      have hlt' : (j : ℕ) + 1 < r := lt_of_le_of_ne j.2 hj
      have : AdjoinRoot.root P ^ ((j : ℕ) + 1) = b ⟨(j : ℕ) + 1, hlt'⟩ := by rw [hb]
      rw [this, b.repr_self, Finsupp.single_apply]
      by_cases hi : (i : ℕ) = (j : ℕ) + 1
      · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
      · rw [if_neg hi, if_neg (fun h => hi (congrArg Fin.val h).symm)]
  have hP0 : P ≠ 0 := hm.ne_zero
  haveI : Module.Finite k (AdjoinRoot P) := pb.finite
  rw [hmat, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, ← LinearMap.charpoly_toMatrix _ pb.basis,
    ← Algebra.leftMulMatrix_apply]
  have hg : pb.gen = AdjoinRoot.root P := rfl
  rw [← hg, charpoly_leftMulMatrix, hg, AdjoinRoot.minpoly_root hP0, hm.leadingCoeff, inv_one, C_1, mul_one]

theorem exists_et_isGen_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (p : Fin r → F),
    (companion p).charpoly.Separable → ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  intro F E _ _ _ _ _ r p hs
  rw [charpoly_companion] at hs
  exact EtExist.exists_isGen F E r p hs

end GlobalTheory.JR
end
end
