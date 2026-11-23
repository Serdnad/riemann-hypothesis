module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalSubgroupContainingHyperspecialEqTopUnramif
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsTransversalAtComplexPoints
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle115
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem vacuum_sum_selfDual_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M),
    GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a → ∀ Z : Finset (Matrix (Fin n') (Fin n) L),
    (∀ z ∈ Z, ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
      z = u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) →
    (∀ z ∈ Z, ∀ z' ∈ Z, z - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → z = z') →
    (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ z ∈ Z, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - z ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) →
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (∑ z ∈ Z, ρ z s) = ∑ z ∈ Z, ρ z s := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac a hSD Z hZform hZdist hZcov u hu
  classical
  obtain ⟨hU, hodd, hSint, hTint, -, -, hδ, hpsi, -, -, hρ, -, -, -⟩ := hP
  have hσσ := hU.1
  have hσv := hU.2.1
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hodd
  set A : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hA
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef

  have hloc : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      locH σ δ JS JT (w * A) (w' * A) ∈ Formalism.UG.intL L := by
    intro w w' hw hw'
    have hw'σ : ∀ i j, (w'.map σ)ᵀ i j ∈ Formalism.UG.intL L := by
      intro i j
      show Valued.v (σ (w' j i)) ≤ 1
      rw [hσv]; exact hw' j i
    have hJT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := fun i j => glint_entry hTint i j
    have hB : ∀ i j, (A * P * (A.map σ)ᵀ) i j ∈ Formalism.UG.intL L := hSD.2
    have hC : ∀ i j, ((w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w) i j ∈ Formalism.UG.intL L :=
      matMul_int (matMul_int hw'σ hJT) hw
    have e : locH σ δ JS JT (w * A) (w' * A) =
        δ * Matrix.trace ((A * P * (A.map σ)ᵀ) * ((w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w)) := by
      unfold locH
      congr 1
      rw [Matrix.map_mul, Matrix.transpose_mul]
      calc Matrix.trace (P * ((A.map σ)ᵀ * (w'.map σ)ᵀ) * (JT : Matrix (Fin n') (Fin n') L) * (w * A))
          = Matrix.trace ((P * (A.map σ)ᵀ * (w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w) * A) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.trace (A * (P * (A.map σ)ᵀ * (w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w)) :=
            Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e]
    refine (Formalism.UG.intL L).mul_mem (le_of_eq hδ.1) ?_
    unfold Matrix.trace
    exact (Formalism.UG.intL L).sum_mem fun i _ => matMul_int hB hC i i

  have hpair : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      ψ ((locH σ δ JS JT (w * A) (w' * A) + σ (locH σ δ JS JT (w * A) (w' * A))) / 2) = 1 := by
    intro w w' hw hw'
    have hcI := hloc w w' hw hw'
    have hσc : σ (locH σ δ JS JT (w * A) (w' * A)) ∈ Formalism.UG.intL L := by
      show Valued.v (σ _) ≤ 1
      rw [hσv]; exact hcI
    apply hpsi
    · rw [GlobalTheory.Hk3.mem_intL_iff, map_div₀, h2, div_one]
      exact (Formalism.UG.intL L).add_mem hcI hσc
    · rw [map_div₀, map_add (f := _), hσσ, map_ofNat]; ring
  have hcomb : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      ∀ t : M, ρ (w * A) (ρ (w' * A) t) = ρ (w * A + w' * A) t := by
    intro w w' hw hw' t
    have := congrArg (fun f => f t) (hρ (w * A) (w' * A))
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, hpair w w' hw hw', one_smul]
  have key : ∀ z ∈ Z, ∃ z' ∈ Z, ρ (u * A) (ρ z s) = ρ z' s ∧ (u * A + z) - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hZform z hz
    have huv : ∀ i j, (u + v) i j ∈ Formalism.UG.intL L := fun i j => (Formalism.UG.intL L).add_mem (hu i j) (hv i j)
    obtain ⟨z', hz', hdiff⟩ := hZcov (u + v) huv
    obtain ⟨v', hv', rfl⟩ := hZform z' hz'
    refine ⟨v' * A, hz', ?_, by rwa [← Matrix.add_mul]⟩
    have hw : ∀ i j, (u + v - v') i j ∈ Formalism.UG.intL L := fun i j => (Formalism.UG.intL L).sub_mem (huv i j) (hv' i j)
    have hl : ρ ((u + v - v') * A) s = s := by
      apply hvac
      rw [Matrix.sub_mul]
      exact hdiff
    rw [hcomb u v hu hv]
    calc ρ (u * A + v * A) s = ρ (v' * A + (u + v - v') * A) s := by
          congr 1; rw [Matrix.sub_mul, Matrix.add_mul]; abel
      _ = ρ (v' * A) (ρ ((u + v - v') * A) s) := (hcomb v' _ hv' hw s).symm
      _ = ρ (v' * A) s := by rw [hl]
  choose! f hfZ hf hfd using key

  rw [map_sum, Finset.sum_congr rfl hf]
  have hinj : ∀ x ∈ Z, ∀ y ∈ Z, f x = f y → x = y := by
    intro z1 h1 z2 h2 he
    apply hZdist z1 h1 z2 h2
    have := sub_mem (hfd z1 h1) (hfd z2 h2)
    rw [he] at this
    convert this using 1; abel
  have himg : Z.image f = Z := Finset.eq_of_subset_of_card_le
    (fun x hx => by obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx; exact hfZ z hz)
    (by rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)])
  rw [← Finset.sum_image (f := fun z => ρ z s) hinj, himg]

end GlobalTheory.Hk3.HoweG
end

section

open Matrix

noncomputable section

namespace GlobalTheory.SelfDualUnip

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem cT_add' (σ : L →+* L) {n : ℕ} (X Y : Matrix (Fin n) (Fin n) L) :
    Formalism.UG.cT σ (X + Y) = Formalism.UG.cT σ X + Formalism.UG.cT σ Y := by
  unfold Formalism.UG.cT; ext i j; simp

theorem det_cT (σ : L →+* L) {n : ℕ} (X : Matrix (Fin n) (Fin n) L) :
    (Formalism.UG.cT σ X).det = σ X.det := by
  unfold Formalism.UG.cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl

theorem cT_int (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {X : Matrix (Fin n) (Fin n) L}
    (hX : ∀ i j, X i j ∈ Formalism.UG.intL L) (i j : Fin n) : Formalism.UG.cT σ X i j ∈ Formalism.UG.intL L := by
  have h := hX j i
  rw [GlobalTheory.Hk3.mem_intL_iff] at h ⊢
  show Valued.v (σ (X j i)) ≤ 1
  rw [hσ]; exact h

theorem lift_int {n : ℕ} {X : Matrix (Fin n) (Fin n) L} (hX : ∀ i j, X i j ∈ Formalism.UG.intL L) :
    ∃ X' : Matrix (Fin n) (Fin n) (Formalism.UG.intL L), X'.map (Formalism.UG.intL L).subtype = X :=
  ⟨fun i j => ⟨X i j, hX i j⟩, by ext i j; rfl⟩

theorem v_det_eq_one {n : ℕ} {M N : Matrix (Fin n) (Fin n) L} (hM : ∀ i j, M i j ∈ Formalism.UG.intL L)
    (hN : ∀ i j, N i j ∈ Formalism.UG.intL L) (hMN : M * N = 1) : Valued.v M.det = 1 := by
  have hd : Valued.v M.det * Valued.v N.det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, hMN, Matrix.det_one, map_one]
  obtain ⟨M', rfl⟩ := lift_int hM
  obtain ⟨N', rfl⟩ := lift_int hN
  have hdM : (M'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype M'.det :=
    (RingHom.map_det _ _).symm
  have hdN : (N'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype N'.det :=
    (RingHom.map_det _ _).symm
  have hM1 : Valued.v (M'.map (Formalism.UG.intL L).subtype).det ≤ 1 := by
    rw [hdM]; exact (M'.det).2
  have hN1 : Valued.v (N'.map (Formalism.UG.intL L).subtype).det ≤ 1 := by
    rw [hdN]; exact (N'.det).2
  by_contra hne
  have hlt := lt_of_le_of_ne hM1 hne
  have := mul_lt_one_of_lt_of_le hlt hN1
  rw [hd] at this
  exact lt_irrefl _ this

theorem int_of_left_inv {n : ℕ} {G X : Matrix (Fin n) (Fin n) L} (hG : ∀ i j, G i j ∈ Formalism.UG.intL L)
    (hd : Valued.v G.det = 1) (hXG : X * G = 1) : ∀ i j, X i j ∈ Formalism.UG.intL L := by
  obtain ⟨G', rfl⟩ := lift_int hG
  have hdG : (G'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype G'.det :=
    (RingHom.map_det _ _).symm
  have hne : (G'.map (Formalism.UG.intL L).subtype).det ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  have hinv : ((G'.map (Formalism.UG.intL L).subtype).det)⁻¹ ∈ Formalism.UG.intL L := by
    rw [GlobalTheory.Hk3.mem_intL_iff, map_inv₀, hd, inv_one]
  have hu : IsUnit G'.det := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    show (Formalism.UG.intL L).subtype G'.det * ((G'.map (Formalism.UG.intL L).subtype).det)⁻¹ = 1
    rw [← hdG]; exact mul_inv_cancel₀ hne
  have hGY : G'.map (Formalism.UG.intL L).subtype * (G'⁻¹).map (Formalism.UG.intL L).subtype = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv G' hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hX : X = (G'⁻¹).map (Formalism.UG.intL L).subtype := by
    calc X = X * (G'.map (Formalism.UG.intL L).subtype * (G'⁻¹).map (Formalism.UG.intL L).subtype) := by
          rw [hGY, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hXG, Matrix.one_mul]
  intro i j
  rw [hX]; exact (G'⁻¹ i j).2

theorem selfDual_mul_of_skew : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n : ℕ) (JS a k : GL (Fin n) L) (E : Matrix (Fin n) (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) → (∀ i j, E i j ∈ Formalism.UG.intL L) →
  (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (k : Matrix (Fin n) (Fin n) L) = 1 + E →
  (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.SelfDual σ JS (k * a) := by
  intro L _ _ σ hσ n JS a k E hJ ha hE hEint hEa hk hki
  obtain ⟨hG0, hX0⟩ := ha

  have hKint : ∀ i j, (k : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j
    rw [hk, Matrix.add_apply, Matrix.one_apply]
    refine (Formalism.UG.intL L).add_mem ?_ (hEint i j)
    split_ifs
    · exact (Formalism.UG.intL L).one_mem
    · exact (Formalism.UG.intL L).zero_mem
  have hE' : ∀ X : Matrix (Fin n) (Fin n) L, Formalism.UG.cT σ E * ((JS : Matrix (Fin n) (Fin n) L) * X) =
      -((JS : Matrix (Fin n) (Fin n) L) * (E * X)) := by
    intro X; rw [← Matrix.mul_assoc, hE, Matrix.neg_mul, Matrix.mul_assoc]

  have hGeq : Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) =
      Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) +
      Formalism.UG.cT σ (E * (a : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) *
        (E * (a : Matrix (Fin n) (Fin n) L)) := by
    rw [hk, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_add', Formalism.UG.cT_one]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hE',
      Matrix.mul_neg]
    abel
  have hGint : ∀ i j, (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))) i j ∈
      Formalism.UG.intL L := by
    intro i j
    rw [hGeq, Matrix.add_apply]
    exact (Formalism.UG.intL L).add_mem (hG0 i j)
      (GlobalTheory.Hk3.matMul_int (GlobalTheory.Hk3.matMul_int (cT_int σ hσ hEa) hJ) hEa i j)

  have hK1 : Valued.v (k : Matrix (Fin n) (Fin n) L).det = 1 := v_det_eq_one hKint hki k.mul_inv
  have hX0G0 : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) *
      (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) = 1 := by
    have e3 : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, a.inv_mul, Formalism.UG.cT_one]
    calc _ = Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * ((JS : Matrix (Fin n) (Fin n) L) *
          (((a : Matrix (Fin n) (Fin n) L) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [a.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc (JS : Matrix (Fin n) (Fin n) L), JS.mul_inv,
          Matrix.one_mul, e3]
  have hG01 := v_det_eq_one hG0 hX0 hX0G0
  have hdet : Valued.v (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))).det = 1 := by
    have : (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
        (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))).det =
        σ (k : Matrix (Fin n) (Fin n) L).det * (k : Matrix (Fin n) (Fin n) L).det *
        (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)).det := by
      simp only [Matrix.det_mul, det_cT, map_mul]; ring
    rw [this, map_mul, map_mul, hσ, hK1, hG01]; simp

  have hXG : (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))) = 1 := by
    have hka : ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        (k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) := Units.val_mul k a
    rw [← hka]
    have e3 : Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, (k * a).mul_inv, Formalism.UG.cT_one]
    calc _ = (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          Formalism.UG.cT σ ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          ((JS : Matrix (Fin n) (Fin n) L) * ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e3, Matrix.one_mul, ← Matrix.mul_assoc ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), JS.inv_mul, Matrix.one_mul, (k * a).inv_mul]
  refine ⟨?_, int_of_left_inv hGint hdet hXG⟩
  intro i j
  rw [Units.val_mul]
  exact hGint i j

end GlobalTheory.SelfDualUnip
end
end

section

noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem mem_GLint_of_entries' {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

def cTGL {L : Type} [Field L] (σ : L →+* L) {n : ℕ} (a : GL (Fin n) L) : GL (Fin n) L :=
  ⟨Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L), Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L),
    by rw [← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one],
    by rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]⟩

theorem selfDual_eq_unitary_mul_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (JS : GL (Fin n) L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
      ∃ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), ∃ k : GL (Fin n) L, k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧
        a = (g : GL (Fin n) L) * k := by
  intro L _ _ _ ϖ σ q n JS hU _hq hJS hJh a ha
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have cTcT : ∀ M : Matrix (Fin n) (Fin n) L, Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
    intro M; ext i j; simp [Formalism.UG.cT, hσ]
  have hJc : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := by
    ext i j; simp [Formalism.UG.cT, hJh]
  set G : GL (Fin n) L := cTGL σ a * JS * a with hGdef
  have hGv : (G : Matrix (Fin n) (Fin n) L) =
      Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) := rfl
  have hGi : ((G⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [hGdef, _root_.mul_inv_rev, _root_.mul_inv_rev, ← _root_.mul_assoc]; rfl
  have hGint : G ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) :=
    mem_GLint_of_entries' _ G (fun i j => by rw [hGv]; exact ha.1 i j) (fun i j => by rw [hGi]; exact ha.2 i j)
  have hGc : Formalism.UG.cT σ (G : Matrix (Fin n) (Fin n) L) = G := by
    rw [hGv, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cTcT, hJc, Matrix.mul_assoc]
  have hGh : ∀ i j, σ ((G : Matrix (Fin n) (Fin n) L) i j) = (G : Matrix (Fin n) (Fin n) L) j i := by
    intro i j
    have := congrFun (congrFun hGc j) i
    simpa [Formalism.UG.cT] using this
  obtain ⟨P, hP, eP⟩ := GlobalTheory.NormalHyp.frame hU hGint hGh
  obtain ⟨Q, hQ, eQ⟩ := GlobalTheory.NormalHyp.frame hU hJS hJh
  have hU' : a * P * Q⁻¹ ∈ Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) := by
    show Formalism.UG.cT σ ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) *
      ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = JS
    have e1 : Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
    have e2 : (Q : Matrix (Fin n) (Fin n) L) * ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv Q
    rw [hGv] at eP
    calc Formalism.UG.cT σ ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) *
          ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
        = Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            (Formalism.UG.cT σ (P : Matrix (Fin n) (Fin n) L) * (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) *
              (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) * (P : Matrix (Fin n) (Fin n) L)) *
            ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          simp only [Units.val_mul, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            (Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (Q : Matrix (Fin n) (Fin n) L)) *
            ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by rw [eP, eQ]
      _ = (Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L)) *
            (JS : Matrix (Fin n) (Fin n) L) * ((Q : Matrix (Fin n) (Fin n) L) * ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
          simp only [Matrix.mul_assoc]
      _ = JS := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨a * P * Q⁻¹, hU'⟩, Q * P⁻¹, mul_mem hQ (inv_mem hP), ?_⟩
  show a = a * P * Q⁻¹ * (Q * P⁻¹)
  group

end GlobalTheory.Hk3.HoweG

end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
theorem _root_.GlobalTheory.T.exists_forms_transversal_at_complexPoints : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (N : ℕ)
    (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ S : Finset (CxPts p (RingHom.id ℂ)),
    ∃ (n : ℕ) (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ) (hf : ∀ i, f i ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n ∧
      (⨆ i, GlobalTheory.EtProj.fOpen ι (f i) = ⊤) ∧ (∀ i, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (f i)) ∧
      (∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0)) ∧ ∀ j : Fin d,
        CxPts.ev p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0)) (GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) y = 0) ∧
      ∀ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0))),
        (∀ j : Fin d, CxPts.evHom hy (GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) = 0) →
        RingHom.ker (CxPts.evHom hy) ≤ Ideal.span (Set.range fun j : Fin d => GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) ⊔
          RingHom.ker (CxPts.evHom hy) ^ 2 := by
  first | exact @GlobalTheory.EtProj.Transv.exists_forms_transversal | exact GlobalTheory.EtProj.Transv.exists_forms_transversal | exact @GlobalTheory.EtProj.Transv.exists_transversal_forms_first_separate | exact GlobalTheory.EtProj.Transv.exists_transversal_forms_first_separate
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.SplitOfNegPrime

theorem sqrt_neg_not_mem_maximalRealSubfield (L : Type) [Field L] [NumberField L] [IsCMField L]
    (p : ℕ) (δ : L) (hp : 0 < p) (hδ : δ ^ 2 = -(p : L)) : δ ∉ maximalRealSubfield L := by
  intro hmem
  let x : maximalRealSubfield L := ⟨δ, hmem⟩
  have hx : x ^ 2 = -(p : maximalRealSubfield L) := Subtype.ext (by simpa [x] using hδ)
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield L)) := inferInstance
  have hv : v.IsReal := IsTotallyReal.isReal v
  have h := congrArg (InfinitePlace.embedding_of_isReal hv) hx
  rw [map_pow, map_neg, map_natCast] at h
  have h1 : (0 : ℝ) < p := by exact_mod_cast hp
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv x)]

theorem isSplitAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L), 0 < p → δ ^ 2 = -(p : L) → ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 → ∀ w : HeightOneSpectrum (𝓞 L), (q : 𝓞 L) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
  intro L _ _ _ p q δ hp hδ hdvd w hw
  set Lp := maximalRealSubfield L
  set u := w.under (𝓞 Lp)
  obtain ⟨k, hk⟩ := hdvd
  set z : 𝓞 Lp := -(2 * (q : 𝓞 Lp) * (k : 𝓞 Lp)) with hz
  have hq : (q : 𝓞 Lp) ∈ u.asIdeal := by
    change _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  have hzu : z ∈ u.asIdeal := by
    rw [hz]
    exact u.asIdeal.neg_mem_iff.2 (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq))
  have hk' : ((p : ℤ) : 𝓞 Lp) + 1 = (((8 * q : ℕ) : ℤ) : 𝓞 Lp) * (k : 𝓞 Lp) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 Lp) hk
  have hsq : (1 + 4 * z : 𝓞 Lp) = -(p : 𝓞 Lp) := by
    rw [hz]
    push_cast at hk'
    linear_combination hk'
  have h1 := GlobalTheory.HenselSquare.isSquare_one_add_four_mul Lp u z hzu
  rw [hsq] at h1
  refine GlobalTheory.SplitOfSquare.isSplitAt_of_isSquare L (-(p : Lp)) δ (by rw [hδ]; push_cast; rfl)
    (sqrt_neg_not_mem_maximalRealSubfield L p δ hp hδ) w ?_
  simpa using h1

end GlobalTheory.SplitOfNegPrime
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.cuspRep_satakeParameters_unique : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (a : ℕ) (π : CG K a) (w : HeightOneSpectrum (𝓞 K)) (B B' : Multiset ℂˣ), π.HasSat w B → π.HasSat w B' → B = B' := by
  first | exact @GlobalTheory.AboveL.cg_hasSat_unique | exact GlobalTheory.AboveL.cg_hasSat_unique | (intros; apply GlobalTheory.AboveL.cg_hasSat_unique <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ N → (∀ k ∈ Formalism.IndefR.Lev.levG V β L, ∃ n : ℕ, 0 < n ∧ Formalism.IndefR.Lev.levChi V β L k ^ n = 1) ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ g, SuppF V f g → (g ∈ Formalism.IndefR.Lev.levG V β L ↔ g ∈ KsphC V ∅)) ∧ (∀ g ∈ Formalism.IndefR.Lev.levG V β L, SuppF V f g → Formalism.IndefR.Lev.levChi V β L g = 1) ∧ ∀ k ∈ Formalism.IndefR.Lev.levG V β L, ∃ k₁ ∈ Formalism.IndefR.Lev.levG V β L, ∃ k₂ ∈ Formalism.IndefR.Lev.levG V β L, SuppF V f k₁ ∧ SuppF V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  first | exact @GlobalTheory.LevSplit.lev_split | exact GlobalTheory.LevSplit.lev_split | (intros; apply GlobalTheory.LevSplit.lev_split <;> assumption)
end
