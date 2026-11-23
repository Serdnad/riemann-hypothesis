module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem exists_normCoeff_not_mem {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Finite) (b : B) (hQ₀ : ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥)
    (p : Ideal A) (hp : p.IsPrime) (hb : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) :
    ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by
  classical
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  set K := FractionRing A
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed (K := K) φ hφ b
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hdeg : (charK φ hφ K b).natDegree = P.natDegree := by
    rw [← hP]; exact natDegree_map_eq_of_injective hinj P
  have hmon : P.Monic := by
    have h1 := charK_monic φ hφ K b
    rw [← hP] at h1
    apply hinj
    rw [Monic, leadingCoeff_map_of_injective hinj] at h1
    simpa using h1
  by_contra hcon
  push_neg at hcon

  have hcoeff : ∀ j < P.natDegree, P.coeff j ∈ p := by
    intro j hj
    have hk : 1 ≤ P.natDegree - j := by omega
    have hrev : (charK φ hφ K b).reverse.coeff (P.natDegree - j) = algebraMap A K (P.coeff j) := by
      rw [coeff_reverse, hdeg, revAt_le (by omega), show P.natDegree - (P.natDegree - j) = j by omega,
        ← hP, coeff_map]
    have hex : ∃ a : A, algebraMap A K a = (charK φ hφ K b).reverse.coeff (P.natDegree - j) :=
      ⟨P.coeff j, hrev.symm⟩
    have := algebraMap_normCoeff φ hφ b _ hex
    rw [hrev] at this
    have := hinj this
    rw [← this]
    exact hcon _ hk

  set M := TensorProduct A K B
  have hCH : Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b) = 0 := by
    have h := LinearMap.aeval_self_charpoly (Algebra.lmul K M ((1 : K) ⊗ₜ[A] b))
    have h2 : Algebra.lmul K M (Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b)) = 0 := by
      rw [← Polynomial.aeval_algHom_apply]; exact h
    have h3 := LinearMap.congr_fun h2 1
    simpa using h3
  have hker : Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B) (Polynomial.aeval b P) = 0 := by
    rw [← Polynomial.aeval_algHom_apply, Algebra.TensorProduct.includeRight_apply,
      ← Polynomial.aeval_map_algebraMap K, hP]
    exact hCH

  let I : Ideal B := RingHom.ker (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B))
  have hI : I.comap (algebraMap A B) ≤ p := by
    intro a ha
    obtain ⟨Q₀, hQ₀p, hQ₀c⟩ := hQ₀
    have ha' : (1 : K) ⊗ₜ[A] (algebraMap A B a) = 0 := ha
    have := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)
      (TensorProduct.mk A K B 1)).1 ha'
    obtain ⟨⟨s, hs⟩, hs0⟩ := this
    have hs0' : φ (s * a) = 0 := by
      rw [map_mul]; simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hs0
    have hmem : s * a ∈ Q₀.comap φ := by simp [Ideal.mem_comap, hs0']
    rw [hQ₀c, Ideal.mem_bot] at hmem
    have hs' : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have : a = 0 := by
      rcases mul_eq_zero.1 hmem with h | h
      · exact absurd h hs'
      · exact h
    rw [this]; exact p.zero_mem
  haveI : Algebra.IsIntegral A B := inferInstance
  obtain ⟨Q, hQI, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) p I hI
  have hPQ : Polynomial.aeval b P ∈ Q := hQI (by simpa [I, RingHom.mem_ker] using hker)
  have hbd : b ^ P.natDegree ∈ Q := by
    have hsum := hmon.as_sum

    rw [hsum, map_add (f := _), map_pow, aeval_X, map_sum] at hPQ
    refine (Q.add_mem_iff_left ?_).1 hPQ
    refine Q.sum_mem fun j hj => ?_
    rw [map_mul, aeval_C, aeval_X_pow]
    refine Q.mul_mem_right _ ?_
    have : P.coeff j ∈ Q.comap (algebraMap A B) := by
      change P.coeff j ∈ Ideal.under A Q
      rw [hQc]; exact hcoeff j (Finset.mem_range.1 hj)
    exact this
  exact hb Q hQp hQc (hQp.mem_of_pow_mem _ hbd)

end GlobalTheory.NormalDescent
end

section

open IsDedekindDomain NumberField

theorem _root_.GlobalTheory.T.rayClassGroup_idelic_finiteIndex : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite → ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ GlobalTheory.LevelChars.levSub L S N).FiniteIndex := by
  first | exact @GlobalTheory.LevelChars.rayClass_finite | exact GlobalTheory.LevelChars.rayClass_finite | (intros; apply GlobalTheory.LevelChars.rayClass_finite <;> assumption)
end

section

open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW.MaxWeight

noncomputable def twoDiag (n : ℕ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal (fun i : Fin n => (2 : ℂ) ^ ((n : ℤ) - ((i : ℕ) : ℤ))),
    Matrix.diagonal (fun i : Fin n => ((2 : ℂ) ^ ((n : ℤ) - ((i : ℕ) : ℤ)))⁻¹),
    by
      rw [Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (zpow_ne_zero _ two_ne_zero),
    by
      rw [Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (zpow_ne_zero _ two_ne_zero)⟩

lemma twoDiag_isDiag (n : ℕ) : (twoDiag n).val.IsDiag := Matrix.isDiag_diagonal _

lemma prod_two_zpow {n : ℕ} (ν : Fin n → ℤ) (s : Finset (Fin n)) :
    ∏ i ∈ s, ((2 : ℂ) ^ ((n : ℤ) - ((i : ℕ) : ℤ))) ^ (ν i) =
      (2 : ℂ) ^ (∑ i ∈ s, ((n : ℤ) - ((i : ℕ) : ℤ)) * ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ two_ne_zero, ← _root_.zpow_mul]

lemma two_zpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have h' : ((2 : ℝ) ^ a : ℝ) = (2 : ℝ) ^ b := by
    have ha : ((2 : ℂ) ^ a) = (((2 : ℝ) ^ a : ℝ) : ℂ) := by push_cast; rfl
    have hb : ((2 : ℂ) ^ b) = (((2 : ℝ) ^ b : ℝ) : ℂ) := by push_cast; rfl
    rw [ha, hb] at h
    exact_mod_cast h
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h'

theorem exists_max_weight : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ₀ : Fin n → ℤ), IsWt Φ μ₀ →
    ∃ μ : Fin n → ℤ, IsWt Φ μ ∧ ∀ ν : Fin n → ℤ, IsWt Φ ν →
      ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * ν i ≤ ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * μ i := by
  intro n ι _ _ Φ μ₀ h₀
  let f : (Fin n → ℤ) → ℤ := fun ν => ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * ν i
  let A : Module.End ℂ (ι → ℂ) := Matrix.toLin' (Φ (twoDiag n))
  have heig : ∀ ν, IsWt Φ ν → A.HasEigenvalue ((2 : ℂ) ^ f ν) := by
    rintro ν ⟨w, hw0, hw⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := w)
    refine ⟨?_, hw0⟩
    rw [Module.End.mem_eigenspace_iff]
    simp only [A, Matrix.toLin'_apply]
    rw [hw _ (twoDiag_isDiag n)]
    congr 1
    rw [← prod_two_zpow ν Finset.univ]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [twoDiag, Matrix.diagonal_apply_eq]
  let S : Set ℤ := {k | ∃ ν, IsWt Φ ν ∧ f ν = k}
  have hfin : S.Finite := by
    have hF := Module.End.finite_hasEigenvalue A
    refine (hF.preimage (f := fun k : ℤ => (2 : ℂ) ^ k) (fun a _ b _ h => two_zpow_inj h)).subset ?_
    rintro k ⟨ν, hν, rfl⟩
    exact heig ν hν
  obtain ⟨B, hB⟩ := hfin.bddAbove
  obtain ⟨m, ⟨μ, hμ, rfl⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd (P := fun k => k ∈ S) ⟨B, fun z hz => hB hz⟩ ⟨f μ₀, μ₀, h₀, rfl⟩
  exact ⟨μ, hμ, fun ν hν => hmax _ ⟨ν, hν, rfl⟩⟩

end GlobalTheory.AlgWtHW.MaxWeight
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem eval_upt_eq_zero_of_skew (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hQ : ∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 →
      MvPolynomial.eval (upt (ratPt S)) Q = 0)
    (Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) :
    MvPolynomial.eval (upt Y) Q = 0 := by
  classical
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := fun x => by simp [hc]
  have hσc : ∀ (σ : L →+* ℂ) x, σ (c x) = ComplexEmbedding.conjugate σ x := fun σ x => by
    rw [ComplexEmbedding.conjugate_coe_eq]; exact IsCMField.complexEmbedding_complexConj L σ x

  let B := NumberField.canonicalEmbedding.latticeBasis L
  let b : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → L := fun k => NumberField.integralBasis L k
  have hB : ∀ k, B k = fun σ => σ (b k) := fun k => by
    funext σ; rw [NumberField.canonicalEmbedding.latticeBasis_apply, NumberField.canonicalEmbedding.apply_at]
  have H1 : ∀ σ₀ : L →+* ℂ, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ,
      ∀ σ, ∑ k, a k * σ (b k) = if σ = σ₀ then 1 else 0 := by
    intro σ₀
    refine ⟨B.repr (Pi.single σ₀ 1), fun σ => ?_⟩
    have := congrFun (B.sum_repr (Pi.single σ₀ 1)) σ
    simpa [Finset.sum_apply, hB, Pi.single_apply] using this
  choose a ha using H1

  let S : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → Matrix (Fin n) (Fin n) L := fun J =>
    Matrix.of fun u v => (if u = J.1 ∧ v = J.2.1 then b J.2.2 else 0) -
      (if u = J.2.1 ∧ v = J.1 then c (b J.2.2) else 0)
  let r : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → (L →+* ℂ) × Fin n × Fin n → ℂ :=
    fun J => upt (ratPt (S J))
  have hSk : ∀ J u v, S J u v + c (S J v u) = 0 := by
    intro J u v
    simp only [S, Matrix.of_apply, map_sub]
    split_ifs <;> simp only [map_zero, hcc, sub_zero, zero_sub, add_zero, zero_add] <;>
      first | ring1 | (exfalso; tauto)
  have hskew : ∀ t : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℚ,
      (∑ J, (t J : L) • S J) + ((∑ J, (t J : L) • S J).map c)ᵀ = 0 := by
    intro t; ext u v

    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_ratCast, Matrix.zero_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun J _ => ?_
    rw [← mul_add, hSk, mul_zero]
  have hrat : ∀ t : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℚ,
      (fun p => ∑ J, (t J : ℂ) * r J p) = upt (ratPt (∑ J, (t J : L) • S J)) := by
    intro t; funext p

    simp only [r, upt, ratPt, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul, map_ratCast]

  let Q' := MvPolynomial.bind₁ (fun p => ∑ J, MvPolynomial.X J * MvPolynomial.C (r J p)) Q
  have heval : ∀ z, MvPolynomial.eval z Q' = MvPolynomial.eval (fun p => ∑ J, z J * r J p) Q := by
    intro z
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) z Q' = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q
    rw [MvPolynomial.eval₂Hom_bind₁]
    congr 2
    funext p

    simp [map_sum]
  have hQ' : Q' = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Rat.cast : ℚ → ℂ))
      (fun _ => Set.infinite_range_of_injective Rat.cast_injective) fun z hz => ?_
    choose t ht using fun J => hz J (Set.mem_univ _)
    have hz' : z = fun J => (t J : ℂ) := by funext J; exact (ht J).symm
    rw [heval, hz', hrat, hQ _ (hskew t), map_zero]

  let z : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ :=
    fun J => (1 / 2) * ∑ σ₀, Y σ₀ J.1 J.2.1 * a σ₀ J.2.2
  have key : ∀ u v (τ : L →+* ℂ), ∑ k, z (u, v, k) * τ (b k) = (1 / 2) * Y τ u v := by
    intro u v τ
    calc ∑ k, z (u, v, k) * τ (b k)
        = ∑ k, ∑ σ₀, (1 / 2) * (Y σ₀ u v * (a σ₀ k * τ (b k))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [z, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ₀ _ => ?_
          ring
      _ = ∑ σ₀, (1 / 2) * (Y σ₀ u v * ∑ k, a σ₀ k * τ (b k)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun σ₀ _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = (1 / 2) * Y τ u v := by
          simp only [ha, mul_ite, mul_one, mul_zero]
          simp
  have hcomb : upt Y = fun p => ∑ J, z J * r J p := by
    funext ⟨σ, u, v⟩
    have e1 : ∀ J, r J (σ, u, v) = (if u = J.1 ∧ v = J.2.1 then σ (b J.2.2) else 0) -
        (if u = J.2.1 ∧ v = J.1 then ComplexEmbedding.conjugate σ (b J.2.2) else 0) := by
      intro J
      simp only [r, upt, ratPt, S, Matrix.map_apply, Matrix.of_apply, map_sub]
      simp only [apply_ite σ, map_zero, hσc]
    simp only [e1, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have e2 : ∀ (f : Fin n → Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ) (p q : Fin n),
        (∑ x, ∑ x_1, ∑ x_2, if p = x then if q = x_1 then f x x_1 x_2 else 0 else 0) = ∑ k, f p q k := by
      intro f p q
      rw [Finset.sum_eq_single p (fun x _ hx => by simp [Ne.symm hx]) (by simp),
        Finset.sum_eq_single q (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    have e3 : ∀ (f : Fin n → Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ) (p q : Fin n),
        (∑ x, ∑ x_1, ∑ x_2, if q = x_1 then if p = x then f x x_1 x_2 else 0 else 0) = ∑ k, f p q k := by
      intro f p q
      rw [Finset.sum_eq_single p (fun x _ hx => by simp [Ne.symm hx]) (by simp),
        Finset.sum_eq_single q (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    rw [e2 (fun x x_1 x_2 => z (x, x_1, x_2) * σ (b x_2)),
      e3 (fun x x_1 x_2 => z (x, x_1, x_2) * (ComplexEmbedding.conjugate σ) (b x_2)), key, key, hY σ]
    simp only [upt, Matrix.neg_apply, Matrix.transpose_apply]
    ring
  rw [hcomb, ← heval, hQ', map_zero]

end GlobalTheory.AlgWtHW
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem mulVec_mem_of_cofinite_shift : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (S : Submodule ℂ (ι → ℂ)) (v : ι → ℂ)
    (B : GL (Fin n) ℂ) (F : Set ℂ), F.Finite →
    (∀ s ∉ F, ∀ C : GL (Fin n) ℂ, C.val = B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ) → Φ C *ᵥ v ∈ S) →
    Φ B *ᵥ v ∈ S := by
  intro n ι _ _ Φ hΦ S v B F hF hS
  choose Q hQ using hΦ.poly
  let M : ℂ → Matrix (Fin n) (Fin n) ℂ := fun s => B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ)
  let x : ℂ → ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ :=
    fun s => Sum.elim (fun p => M s p.1 p.2) (fun p => (M s)⁻¹ p.1 p.2)
  let g : ℂ → ι → ℂ := fun s i => ∑ j, MvPolynomial.eval (x s) (Q i j) * v j
  have hMc : Continuous M := by
    fun_prop
  have hdetB : IsUnit (B.val).det := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  have hM0 : M 0 = B.val := by simp [M]
  have hinvc : ContinuousAt (fun s => (M s)⁻¹) 0 := by
    have h1 : ContinuousAt Inv.inv (M 0) := by
      apply continuousAt_matrix_inv
      rw [hM0]
      exact NormedRing.inverse_continuousAt hdetB.unit
    exact h1.comp hMc.continuousAt
  have hxc : ContinuousAt x 0 := by
    rw [continuousAt_pi]
    rintro (p | p)
    · exact ((continuous_apply p.2).comp ((continuous_apply p.1).comp hMc)).continuousAt
    · exact ((continuous_apply p.2).comp (continuous_apply p.1)).continuousAt.comp hinvc
  have hgc : ContinuousAt g 0 := by
    rw [continuousAt_pi]
    intro i
    apply tendsto_finsetSum
    intro j _
    exact (((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp hxc).mul continuousAt_const

  have hgC : ∀ s, ∀ C : GL (Fin n) ℂ, C.val = M s → g s = Φ C *ᵥ v := by
    intro s C hC
    funext i
    simp only [g, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hQ i j C]
    have hx : x s = Sum.elim (fun p => C.val p.1 p.2) (fun p => (C⁻¹).val p.1 p.2) := by
      funext q
      rcases q with p | p
      · simp [x, hC]
      · simp [x, Matrix.coe_units_inv, hC]
    rw [hx]
  have hg0 : g 0 = Φ B *ᵥ v := hgC 0 B hM0.symm
  have hdetev : ∀ᶠ s in nhds (0:ℂ), IsUnit (M s).det := by
    have hc : ContinuousAt (fun s => (M s).det) 0 := hMc.matrix_det.continuousAt
    have : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
    have hne : (M 0).det ≠ 0 := by rw [hM0]; exact hdetB.ne_zero
    filter_upwards [hc.eventually (this.mem_nhds hne)] with s hs
    exact isUnit_iff_ne_zero.2 hs
  have hFev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, s ∉ F := by
    have hcl : IsClosed (F \ {0}) := (hF.diff).isClosed
    have hmem : (F \ {0})ᶜ ∈ nhds (0:ℂ) := hcl.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with s hs1 hs2
    intro hsF
    exact hs1 ⟨hsF, hs2⟩
  have hev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, g s ∈ S := by
    filter_upwards [hFev, nhdsWithin_le_nhds hdetev] with s hs hdet
    rw [hgC s (Matrix.nonsingInvUnit (M s) hdet) rfl]
    exact hS s hs _ rfl
  have ht : Filter.Tendsto g (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (Φ B *ᵥ v)) := by
    rw [← hg0]
    exact hgc.tendsto.mono_left nhdsWithin_le_nhds
  exact (Submodule.closed_of_finiteDimensional S).mem_of_tendsto ht hev

end GlobalTheory.AlgWtHW
end

section

open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem eval_transvection_polynomial_X_entry {n : ℕ} (i j : Fin n) (c : ℂ) (a b : Fin n) :
    Polynomial.eval c ((transvection i j (Polynomial.X : Polynomial ℂ)) a b) = transvection i j c a b := by
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

theorem eval_transvection_polynomial_neg_X_entry {n : ℕ} (i j : Fin n) (c : ℂ) (a b : Fin n) :
    Polynomial.eval c ((transvection i j (-Polynomial.X : Polynomial ℂ)) a b) = transvection i j (-c) a b := by
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

theorem eval_aeval_mv {σ : Type} (g : σ → Polynomial ℂ) (Q : MvPolynomial σ ℂ) (s : ℂ) :
    Polynomial.eval s (MvPolynomial.aeval g Q) = MvPolynomial.eval (fun v => (g v).eval s) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp]

theorem polyRep_transvection_entries_poly :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ →
      ∀ (i j : Fin n), i ≠ j → ∃ P : ι → ι → Polynomial ℂ, ∀ (s : ℂ) (B : GL (Fin n) ℂ),
        B.val = transvection i j s → ∀ a b, Φ B a b = (P a b).eval s := by
  intro n ι _ _ Φ hΦ i j hij
  choose Q hQ using hΦ.poly
  let g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Polynomial ℂ :=
    Sum.elim (fun p => transvection i j (Polynomial.X : Polynomial ℂ) p.1 p.2)
      (fun p => transvection i j (-Polynomial.X : Polynomial ℂ) p.1 p.2)
  refine ⟨fun a b => MvPolynomial.aeval g (Q a b), ?_⟩
  intro s B hB a b
  have hinv : (B⁻¹).val = transvection i j (-s) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hB]
    have := transvection_mul_transvection_same (R := ℂ) i j hij s (-s)
    rw [this, add_neg_cancel, transvection_zero]
  rw [hQ a b B, eval_aeval_mv]
  congr 2
  funext v
  rcases v with p | p
  · simp [g, eval_transvection_polynomial_X_entry, hB]
  · simp [g, eval_transvection_polynomial_neg_X_entry, hinv]

end GlobalTheory
end

section

open Formalism.L2 Formalism.AUTREP ReciprocityTheory.Aut NumberField

theorem _root_.GlobalTheory.T.fixed_vector_of_mem_isotypic_component : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (K : Set (GAf L n)), NG.IsIrrRep ρ S → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) → ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  first | exact @GlobalTheory.IsoFix.fixed_of_isoTyp | exact GlobalTheory.IsoFix.fixed_of_isoTyp | (intros; apply GlobalTheory.IsoFix.fixed_of_isoTyp <;> assumption)
end
