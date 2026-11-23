module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle100
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Basic
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.RealPlaceAnalysis.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.contDensity_eq_fibre_integral : ∀ (V X : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (f : V → X) (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (B : Set X) (fib : X → Measure V) (φ : V → ℝ) (g : X → ℂ), Continuous f → IsOpen B → IsFibreFamily μ f id Set.univ ν B fib → Continuous φ → HasCompactSupport φ → (∀ v, 0 ≤ φ v) → IsContDensityOn μ f id ν B (fun v => (φ v : ℂ)) g → ∀ b ∈ B, g b = ((∫ v, φ v ∂(fib b) : ℝ) : ℂ) ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) = ENNReal.ofReal (g b).re := by
  first | exact @GlobalTheory.FibreDensity.contDensityOn_eq_fibre_integral | exact GlobalTheory.FibreDensity.contDensityOn_eq_fibre_integral | (intros; apply GlobalTheory.FibreDensity.contDensityOn_eq_fibre_integral <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_fibreMeasures_localHermitianForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E), IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id Set.univ ν {c | c ≠ 0} fib := by
  first | exact @GlobalTheory.HermFibreLocal.exists_isFibreFamily | exact GlobalTheory.HermFibreLocal.exists_isFibreFamily | (intros; apply GlobalTheory.HermFibreLocal.exists_isFibreFamily <;> assumption)
end

section

open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Matrix

namespace GlobalTheory.SA.TransvG

section Det

variable {K : Type} [CommRing K]

theorem det_fromBlocks_swap {n : Type} [Fintype n] [DecidableEq n] (P A B D : Matrix n n K) :
    (fromBlocks P A B D).det = (fromBlocks (-A) P (-D) B).det := by
  have h : fromBlocks (-A) P (-D) B = fromBlocks P A B D * (fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 *
      fromBlocks 1 1 0 1 : Matrix (n ⊕ n) (n ⊕ n) K) := by
    simp [fromBlocks_multiply]
  rw [h]
  simp [det_mul]

theorem det_updateRow_last {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (X.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det = (X.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h : (X.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      X.submatrix Fin.castSucc Fin.castSucc := by
    ext a b
    simp
  simp [Fin.castSucc_ne_last, h, ← two_mul]

theorem det_fromBlocks_single {n : Type} [Fintype n] [DecidableEq n] (l : n) (X Y : Matrix n n K) (t s : K) :
    (fromBlocks X (diagonal fun a => if a = l then t else 0) (diagonal fun a => if a = l then s else 0) Y).det =
      X.det * Y.det - t * s * ((X.updateRow l (Pi.single l 1)).det * (Y.updateRow l (Pi.single l 1)).det) := by
  have e1 : fromBlocks X (diagonal fun a => if a = l then t else 0) (diagonal fun a => if a = l then s else 0) Y =
      (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y).updateRow (Sum.inl l)
        (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y (Sum.inl l) +
          t • Pi.single (Sum.inr l) 1) := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, ha, hb, @eq_comm _ l b]
  have e2 : (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y).updateRow (Sum.inl l)
        (Pi.single (Sum.inr l) 1) =
      (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y).updateRow (Sum.inr l)
        (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y (Sum.inr l) +
          s • Pi.single (Sum.inl l) 1) := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, ha, hb, @eq_comm _ l b]
  have e3 : (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y).updateRow (Sum.inr l)
        (Pi.single (Sum.inl l) 1) =
      (fromBlocks (X.updateRow l (Pi.single l 1)) 0 0 (Y.updateRow l (Pi.single l 1))).submatrix
        (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, Pi.single_apply, Equiv.swap_apply_def, ha, hb, @eq_comm _ l b]
  have e4 : (X.updateRow l 0).det = 0 := det_eq_zero_of_row_eq_zero l fun j => by simp
  rw [e1, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, det_fromBlocks_zero₁₂, e2,
    det_updateRow_add, det_updateRow_smul, updateRow_eq_self, det_fromBlocks_zero₂₁, e3, det_permute,
    det_fromBlocks_zero₂₁, Equiv.Perm.sign_swap (by simp), e4]
  simp
  ring

theorem det_fromBlocks_last {r : ℕ} (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (T T' : K) :
    (fromBlocks (diagonal fun a => if a = Fin.last r then -T else 0) A B
      (diagonal fun a => if a = Fin.last r then -T' else 0)).det =
      (-1) ^ (r + 1) * (A.det * B.det - T * T' *
        ((A.submatrix Fin.castSucc Fin.castSucc).det * (B.submatrix Fin.castSucc Fin.castSucc).det)) := by
  have h : (-diagonal fun a => if a = Fin.last r then -T' else 0) =
      diagonal fun a => if a = Fin.last r then T' else 0 := by
    ext a b
    simp only [Matrix.neg_apply, diagonal_apply]
    split_ifs <;> simp
  have h2 : (-A).submatrix Fin.castSucc Fin.castSucc = -A.submatrix Fin.castSucc Fin.castSucc := rfl
  rw [det_fromBlocks_swap, h, det_fromBlocks_single, det_updateRow_last, det_updateRow_last, h2, det_neg, det_neg]
  simp only [Fintype.card_fin]
  ring

end Det

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

end GlobalTheory.SA.TransvG
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

theorem isIntegral_of_left_eigenvector_of_lattice {E K : Type} [Field E] [NumberField E] [Field K]
    [Algebra E K] [Algebra (𝓞 E) K] [IsScalarTower (𝓞 E) E K] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (B : Matrix (Fin n) (Fin n) E) (c : E) (w : K)
    (v : Fin n → K) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hc : c ≠ 0) (hB : ∀ y ∈ Λ, ∃ z ∈ Λ, B *ᵥ y = c • z) (hv : v ≠ 0)
    (hw : v ᵥ* (B.map (algebraMap E K)) = (algebraMap E K c * w) • v) :
    IsIntegral (𝓞 E) w := by
  let φ : (Fin n → E) →ₗ[E] K :=
    { toFun := fun y => v ⬝ᵥ (fun i => algebraMap E K (y i))
      map_add' := by
        intro x y
        simp [dotProduct, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        simp [dotProduct, Finset.mul_sum, Algebra.smul_def, mul_left_comm] }
  have hφ : ∀ y, φ (B *ᵥ y) = (algebraMap E K c * w) * φ y := by
    intro y
    have h1 : (fun i => algebraMap E K ((B *ᵥ y) i))
        = (B.map (algebraMap E K)) *ᵥ (fun i => algebraMap E K (y i)) := by
      ext i

      simp [Matrix.mulVec, dotProduct, map_sum]
    show v ⬝ᵥ (fun i => algebraMap E K ((B *ᵥ y) i)) = _ * (v ⬝ᵥ (fun i => algebraMap E K (y i)))
    rw [h1, Matrix.dotProduct_mulVec, hw, smul_dotProduct, smul_eq_mul]
  have hcK : algebraMap E K c ≠ 0 := by simpa using hc
  let N : Submodule (𝓞 E) K := Λ.map (φ.restrictScalars (𝓞 E))
  refine isIntegral_of_smul_mem_submodule N ?_ (hfg.map _) w ?_
  · intro hN
    apply hv
    have h0 : ∀ y ∈ Λ, φ y = 0 := by
      intro y hy
      have : φ y ∈ N := ⟨y, hy, rfl⟩
      rw [hN] at this
      simpa using this
    have hk : (⊤ : Submodule E (Fin n → E)) ≤ LinearMap.ker φ := by
      rw [← hsp, Submodule.span_le]
      intro y hy
      exact h0 y hy
    ext i
    have := hk (Submodule.mem_top (x := Pi.single i (1 : E)))
    have h2 : v ⬝ᵥ (fun j => algebraMap E K ((Pi.single i (1 : E) : Fin n → E) j)) = 0 := this
    simpa [dotProduct, Pi.single_apply, apply_ite] using h2
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hyz⟩ := hB y hy
    refine ⟨z, hz, ?_⟩
    have h := hφ y
    rw [hyz, map_smul, Algebra.smul_def, mul_assoc] at h
    have h' := mul_left_cancel₀ hcK h
    simpa using h'

theorem trace_mem_of_nilpotent_mod_radical (E : Type) [Field E] [NumberField E] (n m g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hrad : (Ideal.span {(g : 𝓞 E)}).IsRadical) (hg : 1 ≤ g)
    (hA : ∀ y ∈ Λ, A *ᵥ y ∈ Λ) (hm : ∀ y ∈ Λ, ∃ z ∈ Λ, (A ^ m) *ᵥ y = (g : E) • z) :
    ∃ t : 𝓞 E, A.trace = (g : E) * (t : E) := by
  let K := AlgebraicClosure E
  let f : E →+* K := algebraMap E K
  let R := integralClosure (𝓞 E) K
  have hgE : (g : E) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hgK : (g : K) ≠ 0 := by
    have : f (g : E) ≠ 0 := by simpa only [map_ne_zero] using hgE
    simpa using this
  have hroot : ∀ z ∈ (A.map f).charpoly.roots,
      ∃ r : R, r ∈ (Ideal.span {(g : R)}).radical ∧ (r : K) = z := by
    intro z hz
    have h0 : (Matrix.scalar (Fin n) z - A.map f).det = 0 := by
      rw [← Matrix.eval_charpoly]
      exact (Polynomial.mem_roots'.1 hz).2
    obtain ⟨v, hv, hvz⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    have h1 : v ᵥ* (A.map f) = z • v := by
      rw [Matrix.vecMul_sub, sub_eq_zero] at hvz
      rw [← hvz]
      ext i
      simp [Matrix.vecMul_diagonal, mul_comm]
    have hk : ∀ k : ℕ, v ᵥ* ((A ^ k).map f) = z ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Matrix.map_mul, ← Matrix.vecMul_vecMul, ih, Matrix.smul_vecMul, h1,
          smul_smul, pow_succ]
    have hi1 : IsIntegral (𝓞 E) z :=
      isIntegral_of_left_eigenvector_of_lattice Λ A 1 z v hfg hsp one_ne_zero
        (fun y hy => ⟨_, hA y hy, by simp⟩) hv (by simpa using h1)
    have hi2 : IsIntegral (𝓞 E) (z ^ m / (g : K)) :=
      isIntegral_of_left_eigenvector_of_lattice Λ (A ^ m) (g : E) _ v hfg hsp hgE hm hv (by
        rw [map_natCast, mul_div_cancel₀ _ hgK]
        exact hk m)
    refine ⟨⟨z, hi1⟩, ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hi2⟩, ?_⟩⟩, rfl⟩
    apply Subtype.ext
    show z ^ m / (g : K) * ((g : R) : K) = z ^ m
    have : ((g : R) : K) = (g : K) := by simp
    rw [this, div_mul_cancel₀ _ hgK]
  have hsum : ∃ r : R, r ∈ (Ideal.span {(g : R)}).radical ∧
      (r : K) = (A.map f).charpoly.roots.sum := by
    refine Multiset.sum_induction (fun x : K => ∃ r : R,
      r ∈ (Ideal.span {(g : R)}).radical ∧ (r : K) = x) _ ?_ ⟨0, Ideal.zero_mem _, rfl⟩ hroot
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, Ideal.add_mem _ ha hb, rfl⟩
  rw [← Matrix.trace_eq_sum_roots_charpoly, ← AddMonoidHom.map_trace f A] at hsum
  obtain ⟨r, ⟨N, hN⟩, hr⟩ := hsum
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hN
  have hdown : ∀ x : E, IsIntegral (𝓞 E) (f x) → ∃ t : 𝓞 E, (t : E) = x := by
    intro x hx
    exact IsIntegrallyClosed.isIntegral_iff.1
      ((isIntegral_algebraMap_iff ).1 hx)
  obtain ⟨t₀, ht₀⟩ := hdown A.trace (hr ▸ r.2)
  have hsK : (s : K) * (g : K) = f A.trace ^ N := by
    have := congrArg (fun x : R => (x : K)) hs
    simpa [hr] using this
  obtain ⟨u, hu⟩ := hdown (A.trace ^ N / (g : E)) (by
    rw [map_div₀, map_pow, map_natCast, ← hsK, mul_div_cancel_right₀ _ hgK]
    exact s.2)
  have hmem : t₀ ∈ Ideal.span {(g : 𝓞 E)} := by
    apply hrad
    refine ⟨N, Ideal.mem_span_singleton'.2 ⟨u, ?_⟩⟩
    apply RingOfIntegers.coe_injective
    have h : (u : E) * (g : E) = (t₀ : E) ^ N := by
      rw [hu, ht₀, div_mul_cancel₀ _ hgE]
    simpa using h
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨t, ?_⟩
  rw [← ht₀, ← ht]
  simp [mul_comm]

end GlobalTheory
end
