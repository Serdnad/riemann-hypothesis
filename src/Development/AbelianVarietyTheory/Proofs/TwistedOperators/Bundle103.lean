module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfPositiveCoeffOrthogonalEmbeddings
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFlowCoeffEqOfTaylorSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.RealPlaceAnalysis.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.eq_zero_of_positive_coeff_orthogonal_embeddings : ∀ (p q : ℕ) (T : GrpData p q), (∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) → ∀ (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), Function.Injective j₂ → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') → (∀ Y ∈ pR p q, ∀ w, (inner ℂ (j₁ w) (π₁.π (T.expt Y) (j₁ w))).im = 0 ∧ 0 ≤ (inner ℂ (j₁ w) (π₁.π (T.expt Y) (j₁ w))).re) → (∀ Y ∈ pR p q, ∀ w, (inner ℂ (j₂ w) (π₂.π (T.expt Y) (j₂ w))).im = 0 ∧ 0 ≤ (inner ℂ (j₂ w) (π₂.π (T.expt Y) (j₂ w))).re) → (∀ x y u w : E, MeasureTheory.Integrable (fun g => inner ℂ (j₁ x) (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w)))) T.haar ∧ ∫ g, inner ℂ (j₁ x) (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w))) ∂T.haar = 0) → j₁ = 0 := by
  first | exact @GlobalTheory.PosTrace.eq_zero_of_pos_of_orth | exact GlobalTheory.PosTrace.eq_zero_of_pos_of_orth | (intros; apply GlobalTheory.PosTrace.eq_zero_of_pos_of_orth <;> assumption)
end

section

open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowRho

theorem coeff_rhoVr_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff ((rhoVr emb lam g) v).1 m ∈ Set.range κ := by
  classical
  intro ι _ n E _ emb L _ κ hA0 lam γE v hv0 m
  set A : Subfield ℂ := κ.fieldRange with hAdef
  have hA : ∀ τ x, emb τ x ∈ A := fun τ x => RingHom.mem_fieldRange.2 (hA0 τ x)
  have hv : ∀ m, AddMonoidAlgebra.coeff (v : Formalism.L2.DIV.Pol ℂ ι n) m ∈ A := fun m => RingHom.mem_fieldRange.2 (hv0 m)
  rw [← RingHom.coe_fieldRange]
  show AddMonoidAlgebra.coeff ((rhoVr emb lam γE v : VV ℂ lam) : Formalism.L2.DIV.Pol ℂ ι n) m ∈ A
  let R₀ : Subring (Formalism.L2.DIV.Pol ℂ ι n) := (MvPolynomial.map A.subtype).range
  have memR : ∀ F : Formalism.L2.DIV.Pol ℂ ι n, F ∈ R₀ ↔ ∀ m, AddMonoidAlgebra.coeff F m ∈ A := by
    intro F
    constructor
    · rintro ⟨F', rfl⟩ m
      rw [coeff_map]
      exact (AddMonoidAlgebra.coeff F' m).2
    · intro h
      obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := A.subtype)).2 (fun c hc => by
        obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
        exact ⟨⟨_, h m⟩, rfl⟩)
      exact ⟨F', hF'⟩
  have hblock : ∀ M : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ a b, M τ a b ∈ A) → ∀ F ∈ R₀,
      Formalism.GradedWeylDivisibility.blockAct ℂ M F ∈ R₀ := by
    intro M hM F hF
    obtain ⟨F', rfl⟩ := hF
    induction F' using MvPolynomial.induction_on with
    | C a =>
      rw [map_C, Formalism.GradedWeylDivisibility.blockAct, aeval_C]
      exact ⟨C a, by rw [map_C]; rfl⟩
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hp hq
    | mul_X p w hp =>
      rw [map_mul, map_mul, map_X]
      refine mul_mem hp ?_
      rw [Formalism.GradedWeylDivisibility.blockAct, aeval_X]
      exact sum_mem fun b _ => mul_mem ⟨C ⟨_, hM _ _ _⟩, by rw [map_C]; rfl⟩ ⟨X _, map_X _ _⟩
  have hent : ∀ τ a b, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b ∈ A := by
    intro τ a b
    show ((((Formalism.UG.bc (emb τ) γE)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
    rw [← map_inv]
    exact hA τ _
  have hdet : ∀ τ, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ∈ A := by
    intro τ
    have e := RingHom.map_det A.subtype (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A))
    rw [show A.subtype.mapMatrix (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A)) =
      ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) from Matrix.ext fun a b => rfl] at e
    rw [← e]
    exact SetLike.coe_mem _
  have hdt : detTwK lam (invTrK (embGL emb γE)) ∈ A := by
    unfold detTwK
    refine prod_mem fun τ _ => ?_
    unfold Formalism.BasicNotions.detPow
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
    exact zpow_mem (hdet τ) _
  have htr : Formalism.L2.DIV.trAct (invTrK (embGL emb γE)) (v : Formalism.L2.DIV.Pol ℂ ι n) ∈ R₀ :=
    hblock _ (fun τ a b => hent τ b a) _ ((memR _).2 hv)
  show AddMonoidAlgebra.coeff (Formalism.L2.DIV.actP lam (invTrK (embGL emb γE)) (v : Formalism.L2.DIV.Pol ℂ ι n)) m ∈ A
  rw [Formalism.L2.DIV.actP, LinearMap.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul]
  exact mul_mem hdt ((memR _).1 htr m)

end GlobalTheory.RowRho
end

section

noncomputable section

open Matrix Formalism.L2.DIV

namespace GlobalTheory.ParIndex

variable {κ : Type} [CommRing κ] {n r : ℕ}

def parSub (hr : r ≤ n) (H : Subgroup (GL (Fin r) κ)) : Subgroup (GL (Fin n) κ) where
  carrier := {g | g ∈ blockTri (blk2 r) ∧ upperLeftBlock hr g ∈ H}
  one_mem' := ⟨Subgroup.one_mem _, by
    show ext1 (blockTri (blk2 r)) (blkR hr) 1 ∈ H
    rw [blockDiagonalExtendByOnePrimeField_one]; exact Subgroup.one_mem _⟩
  mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
    show ext1 (blockTri (blk2 r)) (blkR hr) (x * y) ∈ H
    rw [extendMatrixByIdentityAlongIndices_mul _ hx.1 hy.1]; exact Subgroup.mul_mem _ hx.2 hy.2⟩
  inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by
    show ext1 (blockTri (blk2 r)) (blkR hr) x⁻¹ ∈ H
    rw [extendOne_inv _ hx.1]; exact Subgroup.inv_mem _ hx.2⟩

theorem mem_parSub {hr : r ≤ n} {H : Subgroup (GL (Fin r) κ)} {g : GL (Fin n) κ} :
    g ∈ parSub hr H ↔ g ∈ blockTri (blk2 r) ∧ upperLeftBlock hr g ∈ H := Iff.rfl

theorem blockPartitionOf_eq_twoBlock {t : ℕ} (hn : n = r + t) : (blkOf r t : Fin n → ℕ) = blk2 r := by
  funext a
  unfold blkOf blk2
  split_ifs with h
  · rfl
  · have : (a.val - r) / t = 0 := Nat.div_eq_of_lt (by have := a.2; omega)
    rw [this]

theorem blockTri_blkOf_eq {t : ℕ} (hn : n = r + t) :
    blockTri (κ := κ) (n := n) (blkOf r t) = blockTri (blk2 r) := by
  rw [blockPartitionOf_eq_twoBlock hn]

end GlobalTheory.ParIndex

end
end

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.Twist.Boost

theorem reflectionBoost_matrix_conjTranspose_mul_self {n : ℕ} (e v : Fin n → ℂ) (t c : ℂ) (hee : star e ⬝ᵥ e = 1) (hvv : star v ⬝ᵥ v = 1)
    (hev : star e ⬝ᵥ v = t) (hve : star v ⬝ᵥ e = t) (hc : c * (1 + t) = 1) (hcs : star c = c) :
    (1 - c • vecMulVec (e + v) (star (e + v)) + (2 : ℂ) • vecMulVec v (star e))ᴴ *
      (1 - c • vecMulVec (e + v) (star (e + v)) + (2 : ℂ) • vecMulVec v (star e)) = 1 := by
  simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, conjTranspose_vecMulVec,
    star_star, hcs, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, vecMulVec_smul, star_add, add_dotProduct, dotProduct_add,
    hee, hvv, hev, hve]
  have hs2 : star (2 : ℂ) = 2 := by simp
  rw [hs2]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.add_apply, Pi.star_apply, smul_eq_mul]
  linear_combination (2 * c * ((e i + v i) * (star (e j) + star (v j))) - 2 * ((e i + v i) * star (e j)) - 2 * (e i * (star (e j) + star (v j)))) * hc

theorem exists_unitary_col (m : ℕ) (ε : Fin m → Bool) (z : Fin m) (u : Fin m → ℂ) (hz : ε z = true)
    (hneg : ∀ i, ε i = false → u i = 0) (hn : ∑ i, ‖u i‖ ^ 2 = 1) :
    ∃ k ∈ UJset ε, kᴴ * k = 1 ∧ ∀ i, k i z = u i := by
  set t : ℝ := ‖u z‖ with ht
  have t0 : 0 ≤ t := norm_nonneg _
  set φ : ℂ := if u z = 0 then 1 else u z / (t : ℂ) with hφdef
  have hφ : star φ * φ = 1 := by
    by_cases h : u z = 0
    · simp [hφdef, h]
    · have htn : (t : ℂ) ≠ 0 := by simp [ht, h]
      simp only [hφdef, h, if_false, star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [div_mul_div_comm, Complex.conj_mul', ← ht]
      field_simp
  have hφt : star φ * u z = (t : ℂ) := by
    by_cases h : u z = 0
    · simp [hφdef, h, ht]
    · have htn : (t : ℂ) ≠ 0 := by simp [ht, h]
      simp only [hφdef, h, if_false, star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [div_mul_eq_mul_div, Complex.conj_mul', ← ht]
      field_simp
  have hφ' : (starRingEnd ℂ) φ * φ = 1 := by rw [← Complex.star_def]; exact hφ
  have hφt' : (starRingEnd ℂ) φ * u z = (t : ℂ) := by rw [← Complex.star_def]; exact hφt
  set e : Fin m → ℂ := Pi.single z 1 with he
  set v : Fin m → ℂ := fun i => star φ * u i with hv
  have hee : star e ⬝ᵥ e = 1 := by simp [he, dotProduct, Pi.single_apply]
  have hvv : star v ⬝ᵥ v = 1 := by
    have : ∀ i, star (v i) * v i = ((‖u i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      simp only [hv, star_mul, star_star]
      calc star (u i) * φ * (star φ * u i) = (star φ * φ) * (star (u i) * u i) := by ring
        _ = _ := by rw [hφ, one_mul, Complex.star_def, Complex.conj_mul']; push_cast; ring
    simp only [dotProduct, Pi.star_apply, this]
    rw [← Complex.ofReal_sum, hn]; simp
  have hev : star e ⬝ᵥ v = (t : ℂ) := by
    simp [he, dotProduct, Pi.single_apply, hv, hφt, hφt']
  have hve : star v ⬝ᵥ e = (t : ℂ) := by
    simp only [he, dotProduct, Pi.star_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [hv]
    rw [hφt]; simp
  set c : ℂ := ((1 / (1 + t) : ℝ) : ℂ) with hcdef
  have hc : c * (1 + (t : ℂ)) = 1 := by
    have : (1 + t) ≠ 0 := by positivity
    have h2 : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast this
    simp only [hcdef]; push_cast; field_simp
  have hcs : star c = c := by simp [hcdef]
  set T : Matrix (Fin m) (Fin m) ℂ := 1 - c • vecMulVec (e + v) (star (e + v)) + (2 : ℂ) • vecMulVec v (star e) with hT
  have hTu : Tᴴ * T = 1 := reflectionBoost_matrix_conjTranspose_mul_self e v t c hee hvv hev hve hc hcs
  set d : Fin m → ℂ := fun i => if i = z then φ else 1 with hd
  set k : Matrix (Fin m) (Fin m) ℂ := T * diagonal d with hk
  have hdd : (diagonal d)ᴴ * diagonal d = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    by_cases h : i = z
    · simp [hd, h, hφ, hφ']
    · simp [hd, h]
  have hku : kᴴ * k = 1 := by
    rw [hk, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ, hTu, Matrix.one_mul, hdd]
  have hTe : ∀ i j, T i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j - c * ((e i + v i) * star (e j + v j)) + 2 * (v i * star (e j)) := by
    intro i j; simp [hT, vecMulVec_apply]
  have hvneg : ∀ i, ε i = false → v i = 0 := fun i hi => by simp [hv, hneg i hi]
  have heneg : ∀ i, ε i = false → e i = 0 := fun i hi => by
    have : i ≠ z := by rintro rfl; simp [hz] at hi
    simp [he, Pi.single_apply, this]
  have hT0 : ∀ i j, ε i ≠ ε j → T i j = 0 := by
    intro i j hij
    have hne : i ≠ j := by rintro rfl; exact hij rfl
    rw [hTe, one_apply_ne hne]
    cases hi : ε i <;> cases hj : ε j
    · simp [hi, hj] at hij
    · simp [hvneg i hi, heneg i hi]
    · simp [hvneg j hj, heneg j hj]
    · simp [hi, hj] at hij
  have hcomm : Jm ε * k = k * Jm ε := by
    ext i j
    simp only [hk, Jm, diagonal_mul, mul_diagonal]
    by_cases hij : ε i = ε j
    · rw [hij]; ring
    · rw [hT0 i j hij]; ring
  refine ⟨k, ?_, hku, ?_⟩
  · show Formalism.REAL.inUJ ε k
    unfold Formalism.REAL.inUJ
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hku, Matrix.one_mul]
  · intro i
    have hez : e z = 1 := by simp [he]
    have hvz : v z = (t : ℂ) := by simp [hv, hφt, hφt']
    have hTz : T i z = v i := by
      rw [hTe, hez, hvz]
      rw [show star ((1 : ℂ) + (t : ℂ)) = 1 + (t : ℂ) by simp, star_one, mul_one]
      have : c * ((e i + v i) * (1 + (t : ℂ))) = e i + v i := by rw [mul_comm (e i + v i), ← mul_assoc, hc, one_mul]
      rw [this]
      by_cases h : i = z
      · subst h; simp [he]; ring
      · simp [he, Pi.single_apply, h, one_apply_ne h]; ring
    simp only [hk, mul_diagonal, hTz, hd, if_true, hv]
    calc star φ * u i * φ = (star φ * φ) * u i := by ring
      _ = u i := by rw [hφ, one_mul]

end GlobalTheory.Twist.Boost

end
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.unitaryFlow_coeff_eq_of_taylor_series : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : ℝ → (H →L[ℂ] H)) (x : ℕ → H) (y : H) (φ φ₀ : ℝ → ℂ), U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ t v, ‖U t v‖ = ‖v‖) → (∀ m, HasDerivAt (fun t => U t (x m)) (x (m + 1)) 0) → AnalyticOnNhd ℝ φ Set.univ → AnalyticAt ℝ φ₀ 0 → (∀ m, iteratedDeriv m φ 0 = ⟪y, x m⟫_ℂ) → (∀ m, iteratedDeriv m φ₀ 0 = ⟪x 0, x m⟫_ℂ) → ∀ t, φ t = ⟪y, U t (x 0)⟫_ℂ := by
  first | exact @GlobalTheory.SphJet.unitaryFlow_coeff_eq_of_taylor | exact GlobalTheory.SphJet.unitaryFlow_coeff_eq_of_taylor | (intros; apply GlobalTheory.SphJet.unitaryFlow_coeff_eq_of_taylor <;> assumption)
end
