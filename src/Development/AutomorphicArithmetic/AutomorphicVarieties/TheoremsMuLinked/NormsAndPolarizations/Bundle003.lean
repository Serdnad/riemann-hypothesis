module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Th.Nm.trZero_inner {K : Type} [Field K] {n : ℕ}
    (D : Matrix (Fin n) (Fin n) K →ₗ[K] Matrix (Fin n) (Fin n) K)
    (hD : ∀ A B, D (A * B) = D A * B + A * D B) : ∃ Y, ∀ A, D A = A * Y - Y * A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun A => Subsingleton.elim _ _⟩
  let o : Fin n := ⟨0, hn⟩
  refine ⟨-∑ i, D (single i o 1) * single o i 1, fun A => ?_⟩
  have h1 : ∀ i, A * single i o (1 : K) = ∑ j, A j i • single j o (1 : K) := by
    intro i
    ext a b
    by_cases hb : o = b
    · subst hb
      simp [Matrix.sum_apply, Matrix.single_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, hb, Matrix.mul_apply]
  have h2 : ∀ j, single o j (1 : K) * A = ∑ i, A j i • single o i (1 : K) := by
    intro j
    ext a b
    by_cases ha : o = a
    · subst ha
      simp [Matrix.sum_apply, Matrix.single_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, ha, Matrix.mul_apply]
  have h3 : ∑ i, single i o (1 : K) * single o i (1 : K) = (1 : Matrix (Fin n) (Fin n) K) := by
    simp only [Matrix.single_mul_single_same, mul_one]
    exact Matrix.sum_single_one
  have h4 : A * ∑ i, D (single i o 1) * single o i 1
      = (∑ i, D (single i o 1) * single o i 1) * A - D A := by
    have e1 : ∀ i, A * (D (single i o 1) * single o i (1 : K))
        = D (A * single i o 1) * single o i 1 - D A * (single i o 1 * single o i 1) := by
      intro i
      rw [hD]; noncomm_ring
    rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_sub_distrib,
      ← Finset.mul_sum, h3, mul_one, Finset.sum_mul]
    congr 1

    simp only [h1, map_sum, map_smul, Finset.sum_mul, mul_assoc, h2, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm
  rw [mul_neg, neg_mul, h4]; abel

theorem UpperTheory.V.Th.Nm.trZero :
    ∀ {K G : Type} [Field K] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) K) (z : G → Matrix (Fin n) (Fin n) K), Submodule.span K (Set.range (mat ρ)) = ⊤ → (∀ g g', z (g * g') = z g + mat ρ g * z g' * mat ρ g⁻¹) → (∀ g, (z g * mat ρ g).trace = 0) → ∃ Y, ∀ g, z g = mat ρ g * Y * mat ρ g⁻¹ - Y := by
  intro K G _ _ n ρ z hsp hc ht
  have hmul : ∀ g h, mat ρ (g * h) = mat ρ g * mat ρ h := by
    intro g h; simp [mat]
  have hone : mat ρ 1 = 1 := by simp [mat]
  have hinv : ∀ g, mat ρ g⁻¹ * mat ρ g = 1 := fun g => by rw [← hmul, inv_mul_cancel, hone]
  have hinv' : ∀ g, mat ρ g * mat ρ g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, hone]
  let d : G → Matrix (Fin n) (Fin n) K := fun g => z g * mat ρ g
  have hd : ∀ g h, d (g * h) = d g * mat ρ h + mat ρ g * d h := by
    intro g h
    simp only [d]
    rw [hc, hmul, add_mul, mul_assoc (mat ρ g * z h), ← mul_assoc (mat ρ g⁻¹), hinv, one_mul]
    simp only [mul_assoc]
  let R := Finsupp.linearCombination K (mat ρ)
  let E := Finsupp.linearCombination K d
  have hR : LinearMap.range R = ⊤ := by rw [Finsupp.range_linearCombination]; exact hsp
  have hker : ∀ y, R y = 0 → E y = 0 := by
    intro y hy
    have key : ∀ h, ∀ y : G →₀ K, (d h * R y).trace + (mat ρ h * E y).trace = 0 := by
      intro h y
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
        simp only [map_add (f := _), mul_add, trace_add]
        linear_combination ha + hb
      | single g a =>
        have := ht (h * g)
        change (d (h * g)).trace = 0 at this
        rw [hd, trace_add] at this
        simp only [R, E, Finsupp.linearCombination_single, mul_smul_comm, trace_smul, smul_eq_mul]
        rw [← mul_add, this, mul_zero]
    have k2 : ∀ A : Matrix (Fin n) (Fin n) K, (A * E y).trace = 0 := by
      intro A
      have hA : A ∈ Submodule.span K (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
      induction hA using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        simpa [hy] using key h y
      | zero => simp
      | add a b _ _ ha hb => simp [add_mul, ha, hb]
      | smul a b _ hb => simp [hb]
    ext i j
    simpa [Matrix.trace_single_mul] using k2 (single j i 1)
  obtain ⟨s, hs⟩ := R.exists_rightInverse_of_surjective hR
  let D := E ∘ₗ s
  have hDg : ∀ g, D (mat ρ g) = d g := by
    intro g
    have h0 : R (s (mat ρ g) - Finsupp.single g 1) = 0 := by
      have := LinearMap.congr_fun hs (mat ρ g)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [map_sub, this]; simp [R]
    have := hker _ h0
    rw [map_sub, sub_eq_zero] at this
    simpa [D, E] using this
  have hD : ∀ A B, D (A * B) = D A * B + A * D B := by
    intro A B
    have hA : A ∈ Submodule.span K (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
    have hB : B ∈ Submodule.span K (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      induction hB using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        rw [← hmul, hDg, hDg, hDg, hd]
      | zero => simp
      | add a b _ _ ha hb => simp only [mul_add, map_add (f := _), ha, hb]; abel
      | smul a b _ hb => simp only [mul_smul_comm, map_smul, hb, smul_add]
    | zero => simp
    | add a b _ _ ha hb => simp only [add_mul, map_add (f := _), ha, hb]; abel
    | smul a b _ hb => simp only [smul_mul_assoc, map_smul, hb, smul_add]
  obtain ⟨Y, hY⟩ := UpperTheory.V.Th.Nm.trZero_inner D hD
  refine ⟨Y, fun g => ?_⟩
  have h1 := hY (mat ρ g)
  rw [hDg] at h1
  have h2 : z g = d g * mat ρ g⁻¹ := by simp only [d]; rw [mul_assoc, hinv', mul_one]
  rw [h2, h1, sub_mul, mul_assoc Y, hinv', mul_one]
end

section

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp
open UpperTheory.V.AlgebraTools.Det

private theorem pairOfRep_cont {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (I : Ideal A)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (h : ∀ a b, AdicCont I fun g => ρ g a b) : (GDet.ofRep ρ).IsCont I := by
  intro i N
  have hl : IsLocallyConstant (fun g : G => fun a b => Ideal.Quotient.mk (I ^ N) (ρ g a b)) := by
    letI : TopologicalSpace (A ⧸ I ^ N) := ⊥
    haveI : DiscreteTopology (A ⧸ I ^ N) := ⟨rfl⟩
    rw [IsLocallyConstant.iff_continuous]
    exact continuous_pi fun a => continuous_pi fun b => (IsLocallyConstant.iff_continuous _).1 (h a b N)
  have key : (fun g => Ideal.Quotient.mk (I ^ N) ((GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1))) =
      (fun M : Fin n → Fin n → A ⧸ I ^ N =>
        Ideal.Quotient.mk (I ^ N) ((-1 : A) ^ i) * (Matrix.of M).charpoly.coeff (n - i)) ∘
        (fun g a b => Ideal.Quotient.mk (I ^ N) (ρ g a b)) := by
    funext g
    simp only [Function.comp_apply, GDet.lam, (repApi ρ).2.1, map_mul]
    congr 1
    rw [← Polynomial.coeff_map, ← Matrix.charpoly_map]
    rfl
  show IsLocallyConstant (fun g => Ideal.Quotient.mk (I ^ N) ((GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1)))
  rw [key]
  exact hl.comp _

private theorem pairOfRep_polar {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type)
    [CommRing R] [Algebra O R] (n : ℕ) (r : F.G₀ →* GL (Fin n) R) (P : GL (Fin n) R) (h : F.IsForm O n r P) (i : ℕ)
    (y : MonoidAlgebra R F.G₀) : (GDet.ofRep (mat r)).lam i (F.star O R n y) = (GDet.ofRep (mat r)).lam i y := by
  have key := (formRep F O R n r P h).1 R y
  have hP : (↑P : Matrix (Fin n) (Fin n) R).map ⇑(algebraMap R R) = ↑P := by
    ext a b
    simp
  rw [hP] at key
  have e : (GDet.repAlg (mat r) R) (F.star O R n y) =
      ((P⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * ((GDet.repAlg (mat r) R) y)ᵀ *
        ((P⁻¹⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    rw [inv_inv, Matrix.mul_assoc, key, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
  unfold GDet.lam
  rw [(repApi (mat r)).1, (repApi (mat r)).1, e, Matrix.coe_units_inv (P⁻¹), Matrix.charpoly_units_conj,
    Matrix.charpoly_transpose]

theorem UpperTheory.V.Th.Nm.pairOfRep :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid F O n) (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (ρ : F.G₀ →* GL (Fin n) A) (P : GL (Fin n) A) (ψ : ∀ v, Fin n → F.Gv v →* Aˣ), 1 ≤ n → (∀ i j, AdicCont (maximalIdeal A) fun g => mat ρ g i j) → (GDet.ofRep (mat ρ)).map (res O A : A →+* ResidueField O) = r.Dbar → F.IsForm O n ρ P → (∀ v i, r.IsPsi v i (ψ v i)) → (∀ v, HasFlag (ρ.comp (F.φ v)) (ψ v)) → (∀ u, ∀ g ∈ r.Ip u, ρ g = 1) → ∃ p : Pair r A, p.D = GDet.ofRep (mat ρ) ∧ p.ψ = ψ := by
  intro l _ n F O _ _ _ r A _ _ _ ρ P ψ hn hc hred hP hψ hfl hI
  refine ⟨⟨GDet.ofRep (mat ρ), ψ, pairOfRep_cont _ _ hc, hred, hψ, fun i g => pairOfRep_polar F O A n ρ P hP i _,
    fun v g h => ?_, fun u g hg h => ?_⟩, rfl, rfl⟩
  · have h2 := oElRep F O A n ρ v _ (hfl v) g
    rw [(repApi _).2.2.1 hn, map_mul, h2, mul_zero, Matrix.trace_zero]
  · have h1 : GDet.repAlg (mat ρ) A (MonoidAlgebra.single g 1 - 1) = 0 := by
      rw [map_sub, map_one]
      simp [GDet.repAlg, mat, hI u g hg]
    rw [(repApi _).2.2.1 hn, map_mul, h1, mul_zero, Matrix.trace_zero]
end
