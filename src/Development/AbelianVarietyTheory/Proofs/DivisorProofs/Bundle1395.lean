module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
public import Development.AbelianVarietyTheory.Counterexamples.AdelicSplittingExamples.LfacDenominatorNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

namespace GlobalTheory.SiegelDense

theorem prod_idem {R : Type} [CommRing R] {e : R} (he : e * e = e) {ι : Type} (s : Finset ι) (a b : ι → R) :
    ∏ i ∈ s, (e * a i + (1 - e) * b i) = e * ∏ i ∈ s, a i + (1 - e) * ∏ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, ih]
    linear_combination (a i * ∏ j ∈ s, a j - a i * ∏ j ∈ s, b j - b i * ∏ j ∈ s, a j + b i * ∏ j ∈ s, b j) * he

theorem det_idem {R : Type} [CommRing R] {e : R} (he : e * e = e) {m : Type} [Fintype m] [DecidableEq m]
    (A B : Matrix m m R) : (e • A + (1 - e) • B).det = e * A.det + (1 - e) * B.det := by
  simp only [Matrix.det_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [prod_idem he]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h] <;> ring

theorem isUnit_mix {R : Type} [CommRing R] {e : R} (he : e * e = e) {a b : R} (ha : IsUnit (e * a + (1 - e)))
    (hb : IsUnit b) : IsUnit (e * a + (1 - e) * b) := by
  obtain ⟨u, rfl⟩ := hb
  have h1 : e * a + (1 - e) * (u : R) = (e * a + (1 - e)) * (e + (1 - e) * (u : R)) := by
    linear_combination (-a + a * (u : R) + 1 - (u : R)) * he
  have h2 : IsUnit (e + (1 - e) * (u : R)) := by
    refine isUnit_iff_exists_inv.mpr ⟨e + (1 - e) * ((u⁻¹ : Rˣ) : R), ?_⟩
    have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
    linear_combination (2 - (u : R) - ((u⁻¹ : Rˣ) : R)) * he + (1 - e) ^ 2 * hu
  rw [h1]
  exact ha.mul h2

theorem mix_corner {R : Type} [CommRing R] {n : ℕ} (e : R) (he : e * e = e) (A : Matrix (Fin n) (Fin n ⊕ Fin n) R)
    (B D' : Matrix (Fin n ⊕ Fin n) (Fin n) R) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (y : Matrix (Fin n) (Fin n) R)
    (hAB : A * B = (2 : R) • 1) (hAD : A * D' = 0) :
    A * (e • G + (1 - e) • 1) * B + A * (e • G + (1 - e) • 1) * D' * (e • y) =
      e • (A * G * B + A * G * D' * y) + (1 - e) • ((2 : R) • (1 : Matrix (Fin n) (Fin n) R)) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hAB, hAD,
    Matrix.zero_mul, smul_zero, add_zero, smul_smul, he, smul_add]
  simp only [Matrix.mul_assoc]
  abel

theorem approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀),
    ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀,
      (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) =
        algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) +
          (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧
      Tendsto q atTop (𝓝 g) :=
  GlobalTheory.T.exists_idempotentCutoff_tendsto_adelicUnitary

theorem unip : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] [Algebra R₀ R] [Invertible (2 : R)] (c : R →ₐ[R₀] R)
    {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (x : Matrix (Fin n) (Fin n) R), xᵀ * J₀ + J₀ * x.map c = 0 →
    ∃ p : UG c (dbl J₀), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * diagCols (Fin n) =
        diagCols (Fin n) * (1 : Matrix (Fin n) (Fin n) R) ∧
      ∀ h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R,
        Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * (h * p.1.1) *
            Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) =
          Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h *
              Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) +
            Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * diagCols (Fin n) * x :=
  GlobalTheory.T.siegelUnipotent_antidiagonal_corner

theorem avoid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (ψ : Polynomial (AE F E)),
    (∀ (Ω : Type) [Field Ω] (φ : AE F E →+* Ω),
      φ (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) = 1 → ψ.map φ ≠ 0) →
    ∃ t : F, IsUnit (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) * ψ.eval (algebraMap F (AE F E) t) +
      (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S))) :=
  GlobalTheory.T.exists_rationalPoint_polynomial_idempotentUnit_value

theorem exists_corner : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] (e : R), e * e = e →
    (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) →
      ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) →
    ∀ {n : ℕ} (D C P Q : Matrix (Fin n) (Fin n) R), D * P + C * Q = 1 →
      ∃ x : Matrix (Fin n) (Fin n) R, IsUnit (e * (D + C * x).det + (1 - e)) :=
  GlobalTheory.T.exists_corner_unit_of_right_inverse'

theorem descend : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (c : R →+* R),
    (∀ r, c (c r) = r) → (∀ t : F, c (algebraMap F R t) = algebraMap F R t) → ∀ (e : R),
    (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) →
      ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) →
    ∀ (ρ : R), IsUnit ρ → c ρ = -ρ → ∀ {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (ε : ℤˣ),
      (J₀.map c)ᵀ = ((ε : ℤ) : R) • J₀ → IsUnit J₀.det →
      ∀ (D C x₀ : Matrix (Fin n) (Fin n) R), IsUnit (e * (D + C * x₀).det + (1 - e)) →
        ∃ x : Matrix (Fin n) (Fin n) R, xᵀ * J₀ + J₀ * x.map c = 0 ∧ IsUnit (e * (D + C * x).det + (1 - e)) :=
  GlobalTheory.T.exists_conj_skew_det_unit_of_avoidance'

theorem dense : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ g : UG (cA σ) (dbl (incM F J)), g ∈ closure {h : UG (cA σ) (dbl (incM F J)) | ∃ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 ∧ IsUnit (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * ((h * p).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))).det} := by
  intro F E _ _ _ _ _ σ hσ n J ε hJ hdet g
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  letI : Invertible (2 : AE F E) := (Invertible.map (algebraMap F (AE F E)) (2 : F)).copy 2 (map_ofNat (algebraMap F (AE F E)) 2).symm
  obtain ⟨q, hq, hlim⟩ := approx F E σ (dbl (incM F J)) g
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun S => ?_)
  have he : algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) * algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)
      = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) := by
    rw [← map_mul, GlobalTheory.LocalGlobalChar.eps_mul_self]
  have hce : cA σ (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) =
      algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) := (cA σ).commutes _
  have hav := avoid F E S

  have hNtN : Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) =
      (2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [Matrix.fromCols_mul_fromRows, two_smul]; simp
  have hNtD : Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = 0 := by
    rw [diagCols, Matrix.fromCols_mul_fromRows]; simp
  have hNN : Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) +
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) =
      (2 : AE F E) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [diagCols, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_add,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp [two_smul]

  obtain ⟨x₀, hx₀⟩ := exists_corner (F := F) _ he hav
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * g.1.1 *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)))
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * g.1.1 *
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)))
    ((⅟2 * ⅟2 : AE F E) • (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      ((g.1⁻¹ : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))))
    ((⅟2 * ⅟2 : AE F E) • (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) *
      ((g.1⁻¹ : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))))
    (by
      have hg : (g.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
          ((g.1⁻¹ : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = 1 := g.1.mul_inv
      rw [show ∀ (A : Matrix (Fin n) (Fin n ⊕ Fin n) (AE F E)) (B : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))
          (N₁ N₂ : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) (T₁ T₂ : Matrix (Fin n) (Fin n ⊕ Fin n) (AE F E))
          (G H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (k : AE F E),
          A * G * N₁ * (k • (T₁ * H * B)) + A * G * N₂ * (k • (T₂ * H * B)) = k • (A * (G * ((N₁ * T₁ + N₂ * T₂) * (H * B)))) from
        fun A B N₁ N₂ T₁ T₂ G H k => by simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, smul_add]]
      rw [hNN, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc (g.1.1 : Matrix _ _ _), hg,
        Matrix.one_mul, hNtN, smul_smul, smul_smul,
        show ((⅟2 * ⅟2 : AE F E) * 2 * 2) = 1 by rw [mul_assoc (⅟2 : AE F E) (⅟2) 2, invOf_mul_self, mul_one, invOf_mul_self],
        one_smul])

  obtain ⟨y, hy⟩ : ∃ y : E, σ y ≠ y := by
    by_contra h
    push_neg at h
    exact GlobalTheory.HeckeObjectExamples.sigma_ne_id hσ (AlgHom.ext h)
  have hinv : ∀ z, σ (σ z) = z := GlobalTheory.HeckeObjectExamples.sigma_invol hσ
  have hcincl : ∀ z : E, cA σ (inclR (F := F) (AF F) z) = inclR (F := F) (AF F) (σ z) := fun z => by
    change Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] z) = (1 : AF F) ⊗ₜ[F] σ z
    rw [Algebra.TensorProduct.map_tmul]; rfl
  have hρu : IsUnit (inclR (F := F) (AF F) (y - σ y)) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hy))).map _
  have hcρ : (cA σ).toRingHom (inclR (F := F) (AF F) (y - σ y)) = -inclR (F := F) (AF F) (y - σ y) := by
    change cA σ _ = _
    rw [hcincl, map_sub, hinv, ← map_neg, neg_sub]
  have hc2 : ∀ r, (cA σ).toRingHom ((cA σ).toRingHom r) = r := fun r => by
    change cA σ (cA σ r) = r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a z => simp [cA, Algebra.TensorProduct.map_tmul, hinv]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hcF : ∀ t : F, (cA σ).toRingHom (algebraMap F (AE F E) t) = algebraMap F (AE F E) t := fun t => by
    change cA σ _ = _
    rw [IsScalarTower.algebraMap_apply F (AF F) (AE F E), AlgHom.commutes]
  have hJm : ((incM F J).map (cA σ).toRingHom)ᵀ = ((ε : ℤ) : AE F E) • incM F J := by
    ext i j
    change cA σ (inclR (F := F) (AF F) (J j i)) = ((ε : ℤ) : AE F E) * inclR (F := F) (AF F) (J i j)
    rw [hcincl, hJ, map_mul, map_intCast]
  have hJdet : IsUnit (incM F J).det := by
    have h := (isUnit_iff_ne_zero.mpr hdet).map (inclR (F := F) (AF F))
    rwa [RingHom.map_det] at h
  obtain ⟨x, hxV, hx⟩ := descend (F := F) (cA σ).toRingHom hc2 hcF _ hav _ hρu hcρ (incM F J) ε hJm hJdet _ _ x₀ hx₀

  have hxV' : (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x)ᵀ * incM F J +
      incM F J * (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x).map (cA σ) = 0 := by
    have h1 : (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x).map (cA σ) =
        algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x.map (cA σ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hce]
    rw [h1, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
    rw [show x.map (cA σ) = x.map (cA σ).toRingHom from rfl, hxV, smul_zero]
  obtain ⟨p, hpD, hcorner⟩ := unip (cA σ) (incM F J) _ hxV'
  refine ⟨p, 1, hpD, ?_⟩
  have hmul : ((q S * p).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = (q S).1.1 * p.1.1 := rfl
  rw [hmul, hcorner, hq S]
  have hk := mix_corner (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) he
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)))
    (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)))
    (diagCols (Fin n)) (g.1.1) x hNtN hNtD
  erw [hk]
  rw [det_idem he, Matrix.det_smul, Matrix.det_one, mul_one]
  exact isUnit_mix he hx ((isUnit_of_invertible (2 : AE F E)).pow _)

end GlobalTheory.SiegelDense
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnitaryInjAtPlace

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    compFin F E v (cA σ x) = sigR (Fv F v) σ (compFin F E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem compFin_inclR (v : Pl (F := F)) (x : E) :
    compFin F E v (inclR (F := F) (AF F) x) = inclR (Fv F v) x := by
  change evFin F v 1 ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] x
  rw [map_one]

theorem eq_tensAt_of_at (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hx : At (evFin F v) x) :
    x = tensAt E v (compFin F E v x) := by
  have h0 : evFin F v (1 - atPlace v 1) = 0 := by rw [map_sub, map_one, evFin_atPlace, sub_self]
  have h1 := hx _ h0
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  have h2 : tensAt E v 1 = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (atPlace v 1) := by
    rw [Algebra.TensorProduct.one_def, tensAt_tmul, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [← one_mul (compFin F E v x), ← tensAt_mul_right, h2, ← Algebra.smul_def]
  exact h1

theorem mat_eq_zero_of_at {n : ℕ} (v : Pl (F := F)) (z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hz : At (evFin F v) z)
    (h0 : z.map (compFin F E v) = 0) : z = 0 := by
  ext i j
  have hij : At (evFin F v) (z i j) := fun u hu => by
    have := congrFun (congrFun (hz u hu) i) j
    simpa using this
  rw [eq_tensAt_of_at v _ hij]
  have := congrFun (congrFun h0 i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at this
  rw [this, map_zero, Matrix.zero_apply]

theorem unitary_at_components {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : Pl (F := F))
    (t : E →ₐ[F] Fv F v) (h : UA σ J) :
    ((mat h).map (piW t))ᵀ * J.map t * (mat h).map (piW (t.comp σ)) = J.map t := by
  have hm : (mat h)ᵀ * incM F J * (mat h).map (cA σ) = incM F J := h.2
  have h1 := congrArg (fun M => (M.map (compFin F E v)).map (splitProj t)) hm
  simp only [Matrix.map_mul, Matrix.transpose_map] at h1
  have e1 : ((incM F J).map (compFin F E v)).map (splitProj t) = J.map t := by
    ext i j
    simp only [incM, Matrix.map_apply]
    rw [compFin_inclR, splitProj_inclR]
  have e2 : (((mat h).map (cA σ)).map (compFin F E v)).map (splitProj t) = (mat h).map (piW (t.comp σ)) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [compFin_cA, ← splitProj_comp]
    rfl
  have e3 : ((mat h)ᵀ.map (compFin F E v)).map (splitProj t) = ((mat h).map (piW t))ᵀ := by
    ext i j
    rfl
  rw [e1, e2] at h1
  rw [← e3]
  exact h1

theorem eq_of_piW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t h₁ hh₁ h₂ hh₂ heq
  have hcm := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  have u₁ := unitary_at_components v t h₁
  have u₂ := unitary_at_components v t h₂
  rw [heq] at u₁
  set A := ((mat h₂).map (piW t))ᵀ * G.W.J.map t with hA
  have hAu : IsUnit A.det := by
    have hd := congrArg Matrix.det u₂
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_left (hd ▸ hJ)
  have hQ : (mat h₁).map (piW (t.comp σ)) = (mat h₂).map (piW (t.comp σ)) := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₁).map (piW (t.comp σ))) hAu,
      ← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₂).map (piW (t.comp σ))) hAu, u₁, u₂]
  have hpi : ∀ (h : UA σ G.W.J) (τ : E →ₐ[F] Fv F v),
      (mat h).map (piW τ) = ((mat h).map (compFin F E v)).map (splitProj τ) := by
    intro h τ; rw [Matrix.map_map]; rfl
  have hY : (mat h₁).map (compFin F E v) = (mat h₂).map (compFin F E v) := by
    refine mat_split_ext hcm t ?_ ?_
    · rw [← hpi, ← hpi, heq]
    · rw [← hpi, ← hpi, hQ]
  have hz : At (evFin F v) (mat h₁ - mat h₂) := by
    intro u hu
    have e : mat h₁ - mat h₂ = (mat h₁ - 1) - (mat h₂ - 1) := by abel
    rw [e, smul_sub, hh₁ u hu, hh₂ u hu, sub_zero]
  have h0 : (mat h₁ - mat h₂).map (compFin F E v) = 0 := by
    rw [Matrix.map_sub _ (fun x y => map_sub _ x y), hY, sub_self]
  have hm := mat_eq_zero_of_at v _ hz h0
  exact Subtype.ext (Units.ext (sub_eq_zero.1 hm))

end GlobalTheory.UnitaryInjAtPlace
end
end

section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.RatUDisc

theorem countable_ratU (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  refine Function.Injective.countable (f := fun x : ratU σ J =>
    (Classical.choose (Subgroup.mem_subgroupOf.1 x.2) : GL (Fin n) E)) ?_
  intro x y h
  have hx := Classical.choose_spec (Subgroup.mem_subgroupOf.1 x.2)
  have hy := Classical.choose_spec (Subgroup.mem_subgroupOf.1 y.2)
  apply Subtype.ext; apply Subtype.ext
  rw [← hx, ← hy]
  exact congrArg _ h

theorem discrete_ratU (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) : DiscreteTopology (ratU σ J) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  obtain ⟨U, hU, h⟩ := GlobalTheory.RationalDiscrete.exists_nhds_zero_inclR (F := F) (E := E)
  refine discreteTopology_of_isOpen_singleton_one ?_
  let f : ratU σ J → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
    fun g => ((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1
  have hf : Continuous f :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have hf1 : f 1 = 0 := sub_self _
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (fun s hs => Filter.mem_of_superset (x := {1}) ?_ (Set.singleton_subset_iff.2 hs)) (pure_le_nhds _)
  have hW : (⋂ i, ⋂ j, (fun g => f g i j) ⁻¹' U) ∈ 𝓝 (1 : ratU σ J) :=
    Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j =>
      (hf.matrix_elem i j).continuousAt.preimage_mem_nhds (by
        show U ∈ 𝓝 (f 1 i j)
        rw [hf1]; exact hU)
  refine Filter.mem_of_superset hW fun g hg => ?_
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 g.2
  have hfg : ∀ i j, f g i j =
      inclR (F := F) (AF F) (((γ : Matrix (Fin n) (Fin n) E) - 1 : Matrix (Fin n) (Fin n) E) i j) := by
    intro i j
    show (((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1) i j = _
    rw [← hγ, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply,
      apply_ite (inclR (F := F) (AF F)), map_one, map_zero]
    rfl
  have hγ1 : γ = 1 := by
    refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h _ ?_))
    rw [Units.val_one, ← hfg]
    exact Set.mem_iInter.1 (Set.mem_iInter.1 hg i) j
  refine Subtype.ext (Subtype.ext ?_)
  rw [← hγ, hγ1, map_one]
  rfl

theorem countable_discrete_ratU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Countable (ratU σ J) ∧ DiscreteTopology (ratU σ J) :=
  fun F E _ _ _ _ _ σ n J => ⟨countable_ratU F E σ n J, discrete_ratU F E σ n J⟩

end GlobalTheory.RatUDisc
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section
open GroundTheory.Global

namespace GlobalTheory.SubstIntertw

variable (F : Type) [Field F] [NumberField F]

def stdChar : AddChar (AF F) ℂ where
  toFun a := (adelicChar F a : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [AddChar.map_add_eq_mul]

theorem stdChar_inl (z : InfiniteAdeleRing F) :
    Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (infiniteAdeleInl z : AF F)) : ℝ)) =
      (adelicChar F (infiniteAdeleInl z) : ℂ) := by
  have h2 : adelicChar F (infiniteAdeleInl z) = Real.fourierChar (-infiniteTrace F z) := adelicChar_infinite z
  rw [h2, GlobalTheory.AdelicSvN.Weyl.trace_eq_mixedTrace, ← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_apply,
    Real.fourierChar_apply]
  congr 1
  have : evI F (infiniteAdeleInl z) = InfiniteAdeleRing.ringEquiv_mixedSpace F z := rfl
  rw [this]
  push_cast
  ring

theorem isStd_stdChar : IsStd (stdChar F) := by
  refine ⟨continuous_subtype_val.comp continuous_adelicChar, fun x => ?_, fun a ha => ?_⟩
  · show (adelicChar F (algebraMap F (AF F) x) : ℂ) = 1
    rw [adelicChar_algebraMap]; rfl
  · have h0 : evI F ((0, 1) : AF F) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
      exact map_zero _
    have h2 : a.2 = 0 := by
      have := congrArg Prod.snd (ha ((0, 1) : AF F) h0)
      have e : (1 : FiniteAdeleRing (𝓞 F) F) * a.2 = 0 := this
      simpa using e
    obtain ⟨z, rfl⟩ : ∃ z : InfiniteAdeleRing F, a = infiniteAdeleInl z := ⟨a.1, Prod.ext rfl h2⟩
    exact (stdChar_inl F z).symm

end GlobalTheory.SubstIntertw

namespace GlobalTheory.SubstIntertw

open GroundTheory.Global


end GlobalTheory.SubstIntertw
end
end
