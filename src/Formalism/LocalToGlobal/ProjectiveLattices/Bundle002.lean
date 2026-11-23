module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

namespace Formalism.L2.Pj.TranscendenceDegreeLemmas

open AlgebraicGeometry CategoryTheory

theorem primeIdealOf_mem_minimalPrimes {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hx : hZ.1.genericPoint ∈ V) :
    (hV.primeIdealOf ⟨_, hx⟩).asIdeal ∈ minimalPrimes Γ(X, V) := by
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen : IsGenericPoint hZ.1.genericPoint Z := by
    have := hZ.1.isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  refine ⟨⟨(hV.primeIdealOf ⟨_, hx⟩).isPrime, bot_le⟩, fun q hq hle => ?_⟩
  let y : PrimeSpectrum Γ(X, V) := ⟨q, hq.1⟩
  have hsp : y ⤳ hV.primeIdealOf ⟨_, hx⟩ := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  have hsp' : hV.fromSpec y ⤳ hZ.1.genericPoint := by
    have := hsp.map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at this
  have hirr : IsIrreducible (closure {hV.fromSpec y}) := isIrreducible_singleton.closure
  have hZle : Z ⊆ closure {hV.fromSpec y} := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp')) isClosed_closure
  have heq : closure {hV.fromSpec y} = Z := (hZ.2 hirr hZle).antisymm hZle
  have hmem : hV.fromSpec y ∈ Z := heq ▸ subset_closure rfl
  have hxy : hV.fromSpec y = hZ.1.genericPoint := (hsp'.antisymm (hgen.specializes hmem)).eq
  have hy : y = hV.primeIdealOf ⟨_, hx⟩ :=
    hV.fromSpec.isOpenEmbedding.injective (hxy.trans (hV.fromSpec_primeIdealOf ⟨_, hx⟩).symm)
  have := congrArg PrimeSpectrum.asIdeal hy
  exact le_of_eq this.symm

theorem fg_residueField_genericPoint {K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) [Algebra K (X.residueField hZ.1.genericPoint)] :
    (⊤ : IntermediateField K (X.residueField hZ.1.genericPoint)).FG := by
  classical
  obtain ⟨U, hU, V, hV, hxV, e, hP⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) hZ.1.genericPoint
  have hUtop : U = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hfx : f hZ.1.genericPoint ∈ U := e hxV
    rwa [Subsingleton.elim y (f hZ.1.genericPoint)]
  subst hUtop
  let e0 : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let ψ : K →+* Γ(X, V) := (f.appLE ⊤ V e).hom.comp (e0 : K →+* _)
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have hsm : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V) :=
    hP.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e0)
  have hmin := primeIdealOf_mem_minimalPrimes hV hZ hxV
  let _ : Algebra Γ(X, V) (X.presheaf.stalk hZ.1.genericPoint) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hZ.1.genericPoint, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨hZ.1.genericPoint, hxV⟩
  let eL := IsLocalization.algEquiv (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨_, hxV⟩).asIdeal) (X.presheaf.stalk hZ.1.genericPoint)
  let eR : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField ≃+* X.residueField hZ.1.genericPoint :=
    IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv
  have hc1 : CharZero (X.residueField hZ.1.genericPoint) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have hc2 : CharZero (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have t1 : IsScalarTower ℚ K (X.residueField hZ.1.genericPoint) :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have t2 : IsScalarTower ℚ K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have f00 : Algebra.IsStandardSmooth K Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have f01 : Algebra.FinitePresentation K Γ(X, V) := inferInstance
  have f0 : Algebra.EssFiniteType K Γ(X, V) := inferInstance
  have f1 : Algebra.EssFiniteType K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp K Γ(X, V) _
  have f2 : Algebra.EssFiniteType ℚ K := inferInstance
  have f3 : Algebra.EssFiniteType ℚ (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp ℚ K _
  have f4 : Algebra.EssFiniteType ℚ (X.residueField hZ.1.genericPoint) :=
    (Algebra.EssFiniteType.iff_of_algEquiv eR.toRatAlgEquiv).1 f3
  have f5 : Algebra.EssFiniteType K (X.residueField hZ.1.genericPoint) := Algebra.EssFiniteType.of_comp ℚ K _
  exact IntermediateField.fg_top K _

end Formalism.L2.Pj.TranscendenceDegreeLemmas
end

section

noncomputable section

namespace Formalism.L2.Pj.DatLin

open Matrix Complex

section Mat

variable {m : Type} [Fintype m] [DecidableEq m]

theorem star_mulVec_dot (A B : Matrix m m ℂ) (u w : m → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (B *ᵥ w) = star u ⬝ᵥ ((Aᴴ * B) *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem star_dot_self_eq (w : m → ℂ) : star w ⬝ᵥ w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, Complex.star_def]

theorem sum_normSq_pos {w : m → ℂ} (hw : w ≠ 0) : 0 < ∑ i, Complex.normSq (w i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩

theorem cplx_str_core (H P Q J : Matrix m m ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hJ2 : J * J = 1) (hJh : Jᴴ = J) (hH : Pᴴ * H * P = J) :
    let K := P * (Complex.I • J) * Q
    (K * K = -1) ∧ (Kᴴ * H * K = H) ∧ (Kᴴ * H = (-Complex.I) • (Qᴴ * Q)) ∧
      K.trace = Complex.I * J.trace := by
  dsimp only
  have hQP' : ∀ X : Matrix m m ℂ, Q * (P * X) = X := fun X => by rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hJ2' : ∀ X : Matrix m m ℂ, J * (J * X) = X := fun X => by rw [← Matrix.mul_assoc, hJ2, Matrix.one_mul]
  have hPQh' : ∀ X : Matrix m m ℂ, Pᴴ * (Qᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one, Matrix.one_mul]

  have hH' : H = Qᴴ * (J * Q) := by
    have hq : Qᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
    calc H = (Qᴴ * Pᴴ) * H * (P * Q) := by rw [hq, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = Qᴴ * ((Pᴴ * H * P) * Q) := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (J * Q) := by rw [hH]
  have hsI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQ, Complex.I_mul_I,
      neg_smul, one_smul]
  · rw [hH']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hJh, hsI, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQh']
    rw [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  · rw [hH']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hJh, hsI, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQh']
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]

theorem exists_cplx_str {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (p q : ℕ)
    (e : n ≃ Fin p ⊕ Fin q) (P : GL (Fin p ⊕ Fin q) ℂ)
    (hP : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ))ᵀ * H.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Matrix.fromBlocks 1 0 0 (-1)) :
    ∃ K : Matrix n n ℂ, (∀ u, K *ᵥ (K *ᵥ u) = -u) ∧
      (∀ u w, star (K *ᵥ u) ⬝ᵥ (H *ᵥ (K *ᵥ w)) = star u ⬝ᵥ (H *ᵥ w)) ∧
      (∀ u : n → ℂ, u ≠ 0 → ∃ ρ : ℝ, 0 < ρ ∧ star (K *ᵥ u) ⬝ᵥ (H *ᵥ u) = -(Complex.I * ρ)) ∧
      K.trace = Complex.I * ((p : ℂ) - q) := by
  set P0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hP0
  set Q0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
    ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQ0
  set J0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hJ0
  have hPh : (P0.map (starRingEnd ℂ))ᵀ = P0ᴴ := rfl
  rw [hPh] at hP
  have hPQ0 : P0 * Q0 = 1 := P.mul_inv
  have hQP0 : Q0 * P0 = 1 := P.inv_mul
  have hJJ0 : J0 * J0 = 1 := by
    simp [hJ0, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  set Pn := P0.submatrix e e
  set Qn := Q0.submatrix e e
  set Jn := J0.submatrix e e
  have hPQ : Pn * Qn = 1 := by rw [Matrix.submatrix_mul_equiv, hPQ0, Matrix.submatrix_one_equiv]
  have hQP : Qn * Pn = 1 := by rw [Matrix.submatrix_mul_equiv, hQP0, Matrix.submatrix_one_equiv]
  have hJ2 : Jn * Jn = 1 := by rw [Matrix.submatrix_mul_equiv, hJJ0, Matrix.submatrix_one_equiv]
  have hJh : Jnᴴ = Jn := by
    simp [Jn, hJ0, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
  have hH : Pnᴴ * H * Pn = Jn := by
    have hH0 : H = (H.reindex e e).submatrix e e := by
      ext i j; simp [Matrix.reindex_apply]
    rw [hH0, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hP]
  obtain ⟨h1, h2, h3, h4⟩ := cplx_str_core H Pn Qn Jn hPQ hQP hJ2 hJh hH
  refine ⟨Pn * (Complex.I • Jn) * Qn, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [Matrix.mulVec_mulVec, h1, Matrix.neg_mulVec, Matrix.one_mulVec]
  · intro u w
    rw [Matrix.mulVec_mulVec, star_mulVec_dot, ← Matrix.mul_assoc, h2]
  · intro u hu
    refine ⟨∑ i, Complex.normSq ((Qn *ᵥ u) i), sum_normSq_pos ?_, ?_⟩
    · intro h0
      apply hu
      have := congrArg (Pn *ᵥ ·) h0
      simpa [Matrix.mulVec_mulVec, hPQ] using this
    · rw [star_mulVec_dot, h3, Matrix.smul_mulVec, dotProduct_smul, ← star_mulVec_dot, star_dot_self_eq,
        smul_eq_mul, neg_mul]
  · rw [h4]
    congr 1
    have ht : Jn.trace = J0.trace := by
      simp only [Matrix.trace, Matrix.diag, Jn, Matrix.submatrix_apply]
      exact Equiv.sum_comp e (fun i => J0 i i)
    rw [ht, hJ0]
    simp [Matrix.trace, Fintype.sum_sum_type, sub_eq_add_neg]

end Mat

section GlobalTheory

variable {ι n : Type} [Fintype ι] [Fintype n]

def blk (N : ι → Matrix n n ℂ) : (ι → n → ℂ) →ₗ[ℝ] (ι → n → ℂ) where
  toFun u τ := N τ *ᵥ u τ
  map_add' u v := by ext τ : 1; simp [Matrix.mulVec_add]
  map_smul' c u := by
    ext τ i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Matrix.mulVec_smul]
    rfl

theorem blk_apply (N : ι → Matrix n n ℂ) (u : ι → n → ℂ) (τ : ι) : blk N u τ = N τ *ᵥ u τ := rfl

theorem blk_comp (N N' : ι → Matrix n n ℂ) : blk N ∘ₗ blk N' = blk (fun τ => N τ * N' τ) := by
  apply LinearMap.ext
  intro u
  funext τ
  simp only [LinearMap.comp_apply, blk_apply, Matrix.mulVec_mulVec]

def blkC (N : ι → Matrix n n ℂ) : (ι → n → ℂ) →ₗ[ℂ] (ι → n → ℂ) where
  toFun u τ := N τ *ᵥ u τ
  map_add' u v := by ext τ : 1; simp [Matrix.mulVec_add]
  map_smul' c u := by ext τ : 1; simp [Matrix.mulVec_smul]

theorem blk_eq_restrict (N : ι → Matrix n n ℂ) : blk N = (blkC N).restrictScalars ℝ := rfl

theorem trace_restrict_complex {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    [IsScalarTower ℝ ℂ M] [Module.Free ℂ M] [Module.Finite ℂ M] (f : M →ₗ[ℂ] M) :
    LinearMap.trace ℝ M (f.restrictScalars ℝ) = 2 * (LinearMap.trace ℂ M f).re := by
  classical
  let c := Module.Free.chooseBasis ℂ M
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower c), LinearMap.trace_eq_matrix_trace ℂ c]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr,
    Fintype.sum_prod_type, LinearMap.restrictScalars_apply, LinearMap.map_smul, map_smul, Finsupp.smul_apply,
    smul_eq_mul, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, Fin.sum_univ_two]
  simp [Complex.re_sum, Finset.mul_sum, Finset.sum_add_distrib, two_mul]

theorem trace_blkC [DecidableEq ι] [DecidableEq n] (N : ι → Matrix n n ℂ) :
    LinearMap.trace ℂ _ (blkC N) = ∑ τ, (N τ).trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis fun _ : ι => Pi.basisFun ℂ n)]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_sigma, blkC, Matrix.mulVec_single_one]

theorem trace_blk [DecidableEq ι] [DecidableEq n] (N : ι → Matrix n n ℂ) :
    LinearMap.trace ℝ _ (blk N) = ∑ τ, 2 * (N τ).trace.re := by
  rw [blk_eq_restrict, trace_restrict_complex, trace_blkC, Complex.re_sum, Finset.mul_sum]

end GlobalTheory

end Formalism.L2.Pj.DatLin
end
end

section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField
open scoped WithZero

namespace Formalism.L2.Pj

section Base

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]

def vLa (la : HeightOneSpectrum R) (x : K) : ℤ := -WithZero.log (la.valuation K x)

end Base

section Dvr

variable (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']

def valV : Valuation K' ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal V).valuation K'

def vV (x : K') : ℤ := -WithZero.log (valV V x)

variable {V}

lemma valV_ne_zero {x : K'} (hx : x ≠ 0) : valV V x ≠ 0 := by
  simpa [valV] using hx

lemma vV_mul {x y : K'} (hx : x ≠ 0) (hy : y ≠ 0) : vV V (x * y) = vV V x + vV V y := by
  simp only [vV, map_mul, WithZero.log_mul (valV_ne_zero hx) (valV_ne_zero hy)]
  ring

lemma min_le_vV_add {x y : K'} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (vV V x) (vV V y) ≤ vV V (x + y) := by
  have h := (valV V).map_add x y
  rcases max_choice (valV V x) (valV V y) with hm | hm <;> rw [hm] at h
  · have := (WithZero.log_le_log (valV_ne_zero hxy) (valV_ne_zero hx)).2 h
    exact (min_le_left _ _).trans (by simp only [vV]; omega)
  · have := (WithZero.log_le_log (valV_ne_zero hxy) (valV_ne_zero hy)).2 h
    exact (min_le_right _ _).trans (by simp only [vV]; omega)

variable (V)

def nval (e : ℕ) (x : K') : EReal :=
  open Classical in if x = 0 then ⊤ else (((vV V x : ℝ) / e : ℝ) : EReal)

variable {V}

lemma nval_zero (e : ℕ) : nval V e (0 : K') = ⊤ := by simp [nval]

lemma nval_of_ne {e : ℕ} {x : K'} (hx : x ≠ 0) :
    nval V e x = (((vV V x : ℝ) / e : ℝ) : EReal) := by
  simp [nval, hx]

lemma nval_ne_bot (e : ℕ) (x : K') : nval V e x ≠ ⊥ := by
  unfold nval; split_ifs <;> simp

lemma nval_add (e : ℕ) (x y : K') : min (nval V e x) (nval V e y) ≤ nval V e (x + y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, nval_zero]; exact le_top
  by_cases hx : x = 0
  · subst hx; simp
  by_cases hy : y = 0
  · subst hy; simp
  rw [nval_of_ne hx, nval_of_ne hy, nval_of_ne hxy]
  rcases min_le_iff.1 (min_le_vV_add (V := V) hx hy hxy) with h | h
  · exact min_le_iff.2 (Or.inl (EReal.coe_le_coe_iff.2
      (div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg e))))
  · exact min_le_iff.2 (Or.inr (EReal.coe_le_coe_iff.2
      (div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg e))))

lemma nval_mul (e : ℕ) (x y : K') : nval V e (x * y) = nval V e x + nval V e y := by
  by_cases hx : x = 0
  · subst hx; rw [zero_mul, nval_zero, EReal.top_add_of_ne_bot (nval_ne_bot e y)]
  by_cases hy : y = 0
  · subst hy; rw [mul_zero, nval_zero, EReal.add_top_of_ne_bot (nval_ne_bot e x)]
  rw [nval_of_ne hx, nval_of_ne hy, nval_of_ne (mul_ne_zero hx hy), vV_mul hx hy,
    Int.cast_add, add_div, EReal.coe_add]

lemma nval_mul_unit (e : ℕ) {u : K'} (hu : u ≠ 0) (hu0 : vV V u = 0) (x : K') :
    nval V e (u * x) = nval V e x := by
  rw [nval_mul, nval_of_ne hu, hu0]; simp

lemma nval_bc {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K'']
    [Algebra V' K''] [IsFractionRing V' K''] (i : K' →+* K'') {r : ℕ} (hr : 0 < r)
    (hi : ∀ x, vV V' (i x) = (r : ℤ) * vV V x) (e : ℕ) (x : K') :
    nval V' (r * e) (i x) = nval V e x := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero, nval_zero, nval_zero]
  rw [nval_of_ne ((map_ne_zero i).2 hx), nval_of_ne hx, hi]
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  congr 1; push_cast; exact mul_div_mul_left _ _ hr'

end Dvr

structure CDVR where

  V : Type
  [cr : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [cpl : IsAdicComplete (IsLocalRing.maximalIdeal V) V]
  [ch0 : CharZero V]

attribute [instance] CDVR.cr CDVR.dom CDVR.dvr CDVR.cpl CDVR.ch0

abbrev CDVR.Fr (T : CDVR) : Type := FractionRing T.V

def CDVR.FinRes (T : CDVR) : Prop := Finite (IsLocalRing.ResidueField T.V)

section Over

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]

def OverLa (la : HeightOneSpectrum R) (V : Type) {K' : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K'] (ι : K →+* K')
    (e : ℕ) : Prop :=
  0 < e ∧ ∀ a : K, vV V (ι a) = (e : ℤ) * vLa la a

variable {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K']

lemma nval_smul {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {a : K} (ha : a ≠ 0) (x : K') :
    nval V e (ι a * x) = (((vLa la a : ℤ) : ℝ) : EReal) + nval V e x := by
  rw [nval_mul, nval_of_ne ((map_ne_zero ι).2 ha), ho.2 a]
  congr 1
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  congr 1; push_cast; field_simp

lemma OverLa.bc {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {V' K'' : Type} [CommRing V']
    [IsDomain V'] [IsDiscreteValuationRing V'] [Field K''] [Algebra V' K''] [IsFractionRing V' K'']
    (i : K' →+* K'') {r : ℕ} (hr : 0 < r) (hi : ∀ x, vV V' (i x) = (r : ℤ) * vV V x) :
    OverLa la V' (i.comp ι) (r * e) :=
  ⟨Nat.mul_pos hr ho.1, fun a => by rw [RingHom.comp_apply, hi, ho.2 a]; push_cast; ring⟩

structure IsEval {W : Type} {Cusp : W → Type} [∀ w, AddCommGroup (Cusp w)] [∀ w, Module K (Cusp w)]
    (wadd : W → W → W) (mulC : ∀ w w', Cusp w → Cusp w' → Cusp (wadd w w')) {F : Type} [Field F]
    (ι : K →+* F) (ev : ∀ w, Cusp w → F) : Prop where
  add : ∀ w f g, ev w (f + g) = ev w f + ev w g
  smul : ∀ w (a : K) f, ev w (a • f) = ι a * ev w f
  mul : ∀ w w' f g, ev (wadd w w') (mulC w w' f g) = ev w f * ev w' g

lemma IsEval.zero {W : Type} {Cusp : W → Type} [∀ w, AddCommGroup (Cusp w)] [∀ w, Module K (Cusp w)]
    {wadd : W → W → W} {mulC : ∀ w w', Cusp w → Cusp w' → Cusp (wadd w w')} {F : Type} [Field F]
    {ι : K →+* F} {ev : ∀ w, Cusp w → F} (h : IsEval wadd mulC ι ev) (w : W) : ev w 0 = 0 := by
  have := h.smul w 0 0
  rwa [zero_smul, map_zero, zero_mul] at this

end Over

section Norm

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

lemma finitePlace_eq_zpow {a : K} (ha : a ≠ 0) :
    FinitePlace.mk la a = (Ideal.absNorm la.asIdeal : ℝ) ^ (-(vLa la a)) := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding',
    WithZeroMulInt.toNNReal_neg_apply _ ((la.valuation K).ne_zero_iff.2 ha)]
  simp [vLa, WithZero.toAdd_unzero_eq_log]

def nrmOf (v : EReal) : ℝ :=
  open Classical in if v = ⊤ then 0 else (Ideal.absNorm la.asIdeal : ℝ) ^ (-v.toReal)

lemma one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm la

lemma nrmOf_smul {a : K} (ha : a ≠ 0) {v : EReal} (hv : v ≠ ⊥) :
    nrmOf la ((((vLa la a : ℤ) : ℝ) : EReal) + v) = FinitePlace.mk la a * nrmOf la v := by
  rw [finitePlace_eq_zpow la ha]
  by_cases ht : v = ⊤
  · subst ht; simp [nrmOf]
  lift v to ℝ using ⟨ht, hv⟩
  simp only [nrmOf, ← EReal.coe_add, EReal.coe_ne_top, if_false, EReal.toReal_coe]
  rw [neg_add, Real.rpow_add (by linarith [one_lt_absNorm_real la]), ← Real.rpow_intCast]
  push_cast; ring_nf

end Norm

end Formalism.L2.Pj
end
end
