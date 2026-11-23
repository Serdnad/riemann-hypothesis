module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle013
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle011
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def htOf (hd : d.AxH 𝒜) (h : d.S1) : Formalism.MainNotions.Gaps.HeightData.HtData where
  K := K
  D := d.D
  δ := d.del
  i := d.i
  g0 := d.g0
  L := d.wsize d.wL
  G := d.Gc
  PH := d.PHc
  Prw := d.Prw
  Pet := d.Pet
  S := fun k => meanK fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))
  etaPart := True
  Op := fun la => Op d.D d.N la
  SectionSheafQuotient := fun _ => ∀ c, OmS (Ω c) d.D d.N
  mA := fun la =>
    letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
    inferInstance
  A0 := fun la =>
    letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
    Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)
  t := fun _ => d.bvecG hd.sel hd.a4.choose
  Pts := fun la => Σ c, {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) // w ∈ d.PlOver la c}
  ep := fun _ _ => 1
  f := fun _ ζ => d.fze h ζ.1 ζ.2.1
  vEt := fun _ ζ => (d.ord ζ.1 (d.Wres ζ.1 ζ.2.1) (d.n1 • d.wde) (d.et ζ.1) : ℝ)

theorem genericSection_of_axioms (hd : d.AxH 𝒜) : d.S1 := by
  intro c
  have hS := (ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) (hd.fg c) (hd.trdeg c)
    (hd.a1 c)).1
  have key : ∀ {M : Type} (j0 : Fin (d.N + 1)) (a : M) (f : Fin d.N → M),
      Fin.succAboveCases (α := fun _ => M) j0 a f j0 = a ∧
      ∀ k, Fin.succAboveCases (α := fun _ => M) j0 a f (j0.succAbove k) = f k :=
    fun j0 a f => ⟨by exact Fin.insertNth_apply_same (α := fun _ => _) j0 a f,
      fun k => by exact Fin.insertNth_apply_succAbove (α := fun _ => _) j0 a f k⟩
  let σ : Fin (d.N + 1) → Fin (d.N + 1) :=
    Fin.succAboveCases (α := fun _ => Fin (d.N + 1)) (d.jc c) 0 Fin.succ
  let ρ : Fin (d.N + 1) → Fin (d.N + 1) :=
    Fin.cases (motive := fun _ => Fin (d.N + 1)) (d.jc c) (d.jc c).succAbove
  have hρσ : Function.LeftInverse ρ σ := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
    · simp only [σ, ρ, (key _ _ _).1, Fin.cases_zero]
    · simp only [σ, ρ, (key _ _ _).2, Fin.cases_succ]
  let g : TVar d.D d.N → Fin (d.D + 1) × Fin (d.N + 1) := fun p => (p.1, σ p.2)
  have hg : Function.Injective g := by
    intro p q hpq
    simp only [g, Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (hρσ.injective hpq.2)
  have heq : ∀ p, sImg (d.jc c) (d.x c) p = ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c) (g p) := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
    · simp only [sImg, ReciprocityTheory.MultiplicativeHeights.sImage, g, σ, (key _ _ _).1, Fin.cases_zero]
    · simp only [sImg, ReciprocityTheory.MultiplicativeHeights.sImage, g, σ, (key _ _ _).2, Fin.cases_succ]
  have hfun : sImg (d.jc c) (d.x c) = ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c) ∘ g := funext heq
  have hI : AlgebraicIndependent K (sImg (D := d.D) (d.jc c) (d.x c)) := by
    rw [hfun]
    exact hS.comp g hg
  exact hI

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix

theorem hadamard_gram {R : Type*} [Fintype R] [DecidableEq R] {n : ℕ} (hR : Fintype.card R = n)
    (M : R → Fin n → ℂ) (ν : R → ℝ) (s : Fin n → ℝ) (hν : ∀ r, 0 < ν r)
    (hM : ∀ r k, ‖M r k‖ * ν r ≤ s k) :
    ‖(Matrix.of fun k l : Fin n => ∑ r, M r k * M r l).det‖ * ∏ r, ν r ^ 2 ≤
      (n : ℝ) ^ n * ∏ k, s k ^ 2 := by
  classical

  let e : R ≃ Fin n := Fintype.equivFinOfCardEq hR
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => M (e.symm i) k
  let N : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => (ν (e.symm i) : ℂ) * M (e.symm i) k
  have hG : (Matrix.of fun k l : Fin n => ∑ r, M r k * M r l) = Aᵀ * A := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, A]
    exact (Equiv.sum_comp e.symm (fun r => M r k * M r l)).symm
  have hNd : N = Matrix.diagonal (fun i => (ν (e.symm i) : ℂ)) * A := by
    ext i k
    simp [N, A, Matrix.diagonal_mul]
  have hprod : ∏ i, ν (e.symm i) = ∏ r, ν r := Equiv.prod_comp e.symm ν
  have hνpos : 0 ≤ ∏ r, ν r := Finset.prod_nonneg fun r _ => (hν r).le
  have hdetN : ‖N.det‖ = (∏ r, ν r) * ‖A.det‖ := by
    rw [hNd, Matrix.det_mul, Matrix.det_diagonal, norm_mul, norm_prod, ← hprod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hν _)]
  have hleft : ‖(Matrix.of fun k l : Fin n => ∑ r, M r k * M r l).det‖ * ∏ r, ν r ^ 2
      = ‖N.det‖ ^ 2 := by
    rw [hG, Matrix.det_mul, Matrix.det_transpose, norm_mul, hdetN, Finset.prod_pow]
    ring
  rw [hleft]

  have hH : ‖N.det‖ ≤ ∏ k, Real.sqrt (∑ i, ‖N i k‖ ^ 2) := by
    have := hadamard_det_le Nᵀ
    simpa [Matrix.det_transpose, Matrix.transpose_apply] using this
  have hcol : ∀ k, ∑ i, ‖N i k‖ ^ 2 ≤ (n : ℝ) * s k ^ 2 := by
    intro k
    have : ∀ i, ‖N i k‖ ^ 2 ≤ s k ^ 2 := by
      intro i
      have h1 : ‖N i k‖ = ‖M (e.symm i) k‖ * ν (e.symm i) := by
        simp only [N, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hν _)]
        ring
      rw [h1]
      exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (hν _).le) (hM _ _) 2
    calc ∑ i, ‖N i k‖ ^ 2 ≤ ∑ _i : Fin n, s k ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = (n : ℝ) * s k ^ 2 := by simp
  calc ‖N.det‖ ^ 2 ≤ (∏ k, Real.sqrt (∑ i, ‖N i k‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hH 2
    _ = ∏ k, ∑ i, ‖N i k‖ ^ 2 := by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun k _ =>
          Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
    _ ≤ ∏ k, ((n : ℝ) * s k ^ 2) :=
        Finset.prod_le_prod₀ (fun k _ => Finset.sum_nonneg fun i _ => by positivity)
          fun k _ => hcol k
    _ = (n : ℝ) ^ n * ∏ k, s k ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable abbrev sub0 (x : Fin (d.N + 1) → K) : KTp K d.D d.N →ₐ[K] KTp K d.D d.N :=
  MvPolynomial.aeval (fun v : TVar d.D d.N =>
    if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v)



theorem finYX4 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI := d.algLE h c
    letI := (VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1))).toAlgebra
    FiniteDimensional (FractionRing (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase))
      (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c))) := by
  letI := d.algLE h c
  letI := (VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1))).toAlgebra
  letI := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := by
    classical
    obtain ⟨e, -, -, hsp⟩ := hd.a4
    refine ⟨⟨Finset.univ.image (fun k : Fin d.del => algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c))), ?_⟩⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨q, hq, p, hp⟩ := hsp (fun c' => if hc : c' = c then hc ▸ y else 0)
    have hpc : d.sH c q * y = ∑ k, d.sH c (p k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
        (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) := by
      have h1 := hp c
      first
        | (simp only [dif_pos (rfl : c = c)] at h1; exact h1)
        | simpa using h1
    have hq0 := hq c
    have hKT : ∀ r : KTp K d.D d.N, d.KTtoS h c (algebraMap _ _ r) = d.sH c r := fun r => by
      simp [Data.KTtoS]
    have hy : y = ∑ k, (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (p k) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q) •
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) := by
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_div₀, hKT,
        div_mul_eq_mul_div, ← Finset.sum_div, ← hpc]
      first
        | exact (mul_div_cancel_left₀ y hq0).symm
        | field_simp
    rw [hy]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ k))))
  exact Module.Finite.of_equiv_equiv d.eLX4 (d.eEX4 c)
    (RingHom.ext fun q => (d.fieldEquiv_compat_liftY h c q).symm)


theorem decomp_block0 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ (L E : Type) (_ : Field L) (_ : Field E) (_ : Algebra L E) (_ : FiniteDimensional L E)
      (eL : KTf K d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) L))
      (eE : OmS (Ω c) d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) E)),
      (∀ q : KTf K d.D d.N, eE (d.KTtoS h c q) = VariableBasisExtension.liftY (eL q)) ∧
      (∀ r : Ω c, ∃ e : E, eE (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r) =
        algebraMap (MvPolynomial (Fin (d.N + 1)) E) (FractionRing (MvPolynomial (Fin (d.N + 1)) E))
          (MvPolynomial.C e)) ∧
      ∀ l : L, ∃ P Q : KTp K d.D d.N, Q ≠ 0 ∧ (∀ x, d.sub0 x P = P) ∧ (∀ x, d.sub0 x Q = Q) ∧
        eL.symm (algebraMap (MvPolynomial (Fin (d.N + 1)) L)
            (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) (MvPolynomial.C l)) =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P / algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q := by
  letI := d.algLE h c
  refine ⟨d.FracFieldPositiveRowsBase, d.FracFieldPositiveRowsOmega c, inferInstance, inferInstance, inferInstance,
    FractionFieldVariableLift.finiteDimensional_of_liftY (σ := Fin (d.N + 1)) (d.finYX4 hd h c), d.eLX4, d.eEX4 c,
    fun q => d.fieldEquiv_compat_liftY h c q, fun r => ?_, fun l => ?_⟩
  · refine ⟨algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c) (MvPolynomial.C r), ?_⟩
    rw [IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N), MvPolynomial.algebraMap_eq, d.eEX4_algebraMap, FractionFieldVariableLift.hE_C]
    simp only [FractionFieldVariableLift.toFracY, RingHom.comp_apply, MvPolynomial.map_C]
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := d.PolyRingPositiveRowsBase) l
    have hfix : ∀ (x : Fin (d.N + 1) → K) (p : d.PolyRingPositiveRowsBase),
        d.sub0 x (MvPolynomial.rename Subtype.val p) = MvPolynomial.rename Subtype.val p := by
      intro x p
      have hc : (d.sub0 x).comp (MvPolynomial.rename (R := K)
          (Subtype.val : {v : TVar d.D d.N // v.1 ≠ 0} → TVar d.D d.N)) =
          MvPolynomial.rename Subtype.val := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [Data.sub0, v.2]
      exact AlgHom.congr_fun hc p
    refine ⟨MvPolynomial.rename Subtype.val p, MvPolynomial.rename Subtype.val q, ?_,
      fun x => hfix x p, fun x => hfix x q, ?_⟩
    · exact fun h0 => nonZeroDivisors.ne_zero hq
        (MvPolynomial.rename_injective _ Subtype.val_injective (h0.trans (map_zero _).symm))
    · rw [RingEquiv.symm_apply_eq, map_div₀ d.eLX4, d.eLX4_algebraMap, d.eLX4_algebraMap,
        FractionFieldVariableLift.hL_rename, FractionFieldVariableLift.hL_rename]
      simp only [FractionFieldVariableLift.toFracY, RingHom.comp_apply, MvPolynomial.map_C]
      exact map_div₀ ((algebraMap (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase) _).comp MvPolynomial.C) _ _

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder Kronecker

section Gram

variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}

theorem embeddingColumns_conjugate (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    hBm (conjugate σ) b = (hBm σ b).map (starRingEnd ℂ) := by
  ext l j
  simp [hBm, NumberField.ComplexEmbedding.conjugate_coe_eq]

private lemma map_star_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A⁻¹.map (starRingEnd ℂ) = (A.map (starRingEnd ℂ))⁻¹ := by
  have h : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = Mᴴᵀ := by
    intro M
    ext i j
    simp [conjTranspose_apply]
  rw [h, h, ← transpose_nonsing_inv, conjTranspose_nonsing_inv]

theorem orthogonalProjector_conjugate (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm (conjugate σ) b = (hPm σ b).map (starRingEnd ℂ) := by
  unfold hPm
  rw [embeddingColumns_conjugate σ b]
  have h1 : ((hBm σ b).map (starRingEnd ℂ))ᴴ = (hBm σ b)ᴴ.map (starRingEnd ℂ) := by
    ext i j
    simp [conjTranspose_apply]
  rw [h1, ← Matrix.map_mul, ← map_star_inv, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul]

theorem orthogonalProjector_mulVec_conjugate (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (x : Fin r → K) :
    (hPm (conjugate σ) b *ᵥ fun l => (conjugate σ) (x l)) = star (hPm σ b *ᵥ fun l => σ (x l)) := by
  rw [orthogonalProjector_conjugate σ hb]
  ext i

  simp [Matrix.mulVec, dotProduct, NumberField.ComplexEmbedding.conjugate_coe_eq, map_sum,
  mul_comm]

theorem conj_sum_projected_inner (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (a a' : K)
    (x y : Fin r → K) :
    conj (∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l)))) =
      ∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l))) := by

  rw [map_sum]
  have hinv : Function.Involutive (NumberField.ComplexEmbedding.conjugate (K := K)) := by
    intro σ
    ext z
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
  refine Fintype.sum_bijective _ hinv.bijective _ _ (fun σ => ?_)
  rw [orthogonalProjector_mulVec_conjugate σ hb x, orthogonalProjector_mulVec_conjugate σ hb y,
    NumberField.ComplexEmbedding.conjugate_coe_eq, NumberField.ComplexEmbedding.conjugate_coe_eq]

  simp [dotProduct, map_sum, mul_comm, mul_left_comm]

theorem quotientGram_conjTranspose (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) : (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c)ᴴ = ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c := by
  unfold ReciprocityTheory.MultiplicativeHeights.quotGramC
  simp only [gramMatrix_eq_embeddingColumns, crossGram_eq_embeddingColumns, conjTranspose_sub, conjTranspose_mul,
    conjTranspose_conjTranspose, conjTranspose_nonsing_inv, Matrix.mul_assoc]

theorem quotientGram_det_re_eq (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) :
    (((ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re : ℝ) : ℂ) = (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det := by
  have h := quotientGram_conjTranspose σ hb c
  have h2 : star (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det = (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det := by
    rw [← det_conjTranspose, h]
  exact Complex.conj_eq_iff_re.mp h2

end Gram

section GramDet

variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}

noncomputable def hwv (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K) → EuclideanSpace ℝ (hIdx K r) :=
  fun p => hpv b (integralBasis K p.2 • c p.1)

theorem det_gram_projectedLatticeVectors (b : Fin k → Fin r → K) (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) :
    (gram ℝ (hwv b c)).det =
      |(discr K : ℝ)| ^ m * ∏ σ : K →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re := by
  classical
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (K →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank,
      Module.finrank_eq_card_chooseBasisIndex]
  obtain ⟨e⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →+* ℂ)) :=
    ⟨Fintype.equivOfCardEq hcard⟩
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
      (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℂ, Ω = Matrix.of fun q p => e q (integralBasis K p) :=
    ⟨_, rfl⟩

  have hent : ∀ j p j' p', ((gram ℝ (hwv b c) (j, p) (j', p') : ℝ) : ℂ) =
      ∑ q, star (Ω q p) * ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c j j' * Ω q p' := by
    intro j p j' p'
    rw [Matrix.gram_apply]
    simp only [hwv]
    rw [inner_projectedVector_smul, Complex.conj_eq_iff_re.mp (conj_sum_projected_inner b hb _ _ _ _)]
    symm
    refine Fintype.sum_equiv e _ _ (fun q => ?_)
    rw [quotientGram_eq_projector (e q) hb c j j', hΩ]
    simp only [Matrix.of_apply]
    rw [show star ((e q) (integralBasis K p)) = conj ((e q) (integralBasis K p)) from rfl]
    ring
  have hmat : (gram ℝ (hwv b c)).map Complex.ofRealHom =
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω)ᴴ *
        Matrix.blockDiagonal (fun q => ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c) *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω) := by
    ext ⟨j, p⟩ ⟨j', p'⟩
    rw [Matrix.map_apply, Complex.ofRealHom_eq_coe, hent]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Matrix.one_apply, ite_mul, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite (starRingEnd ℂ), map_zero]
  have hdet : ((gram ℝ (hwv b c)).det : ℂ) =
      star ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det *
        (Matrix.blockDiagonal (fun q => ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c)).det *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det := by
    have h := RingHom.map_det Complex.ofRealHom (gram ℝ (hwv b c))
    rw [Complex.ofRealHom_eq_coe] at h
    rw [h, RingHom.mapMatrix_apply, hmat, det_mul, det_mul, det_conjTranspose]
  have hT : ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det = Ω.det ^ m := by
    simp [Matrix.det_kronecker]
  have hdisc : Ω.det ^ 2 = (discr K : ℂ) := by
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis K)
      (e.trans (RingHom.equivRatAlgHom K ℂ))
    rw [← NumberField.coe_discr] at h1
    have h2 : Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis K)
        (e.trans (RingHom.equivRatAlgHom K ℂ)) = Ωᵀ := by
      ext i j
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, hΩ, RingHom.equivRatAlgHom]
    rw [h2, det_transpose] at h1
    rw [← h1]
    simp
  have hnorm : star Ω.det * Ω.det = ((|(discr K : ℝ)| : ℝ) : ℂ) := by
    rw [show star Ω.det = conj Ω.det from rfl, Complex.conj_mul', ← Complex.ofReal_pow, ← norm_pow,
      hdisc, Complex.norm_intCast]
  apply Complex.ofReal_injective
  rw [hdet, hT, Matrix.det_blockDiagonal]
  push_cast
  rw [← Equiv.prod_comp e (fun σ => (((ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re : ℝ) : ℂ))]
  simp_rw [quotientGram_det_re_eq _ hb c]
  rw [star_pow, ← hnorm]
  ring

end GramDet

end ReciprocityTheory.ChartRestriction.G.T0
end
