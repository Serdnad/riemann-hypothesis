module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle004
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle002
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.locfin :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), h ∈ Pos L N → ∀ B : ℝ,
    ∃ S : Set (Lat L N), S.Finite ∧ ∀ᶠ k in nhds h, ∀ y ∉ S, B < q k y := by
  intro L _ _ N h hh B
  obtain ⟨c, hc, hev⟩ := lowbd L N h hh
  obtain ⟨R, hR⟩ := exists_nat_gt (max (B / c) 1)
  have hR1 : (1 : ℝ) < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRB : B / c < R := lt_of_le_of_lt (le_max_left _ _) hR
  set T := {a : 𝓞 L | ∀ w : InfinitePlace L, ‖embO w a‖ ≤ (R : ℝ)} with hT
  refine ⟨Set.pi Set.univ (fun _ => T), Set.Finite.pi (fun _ => (cntconj L R).1), ?_⟩
  filter_upwards [hev] with k hk
  intro y hy
  have hy' : ∃ a w, (R : ℝ) < ‖embO w (y a)‖ := by
    by_contra hne
    push_neg at hne
    exact hy (fun a _ w => hne a w)
  obtain ⟨a, w, hlt⟩ := hy'
  have hle : ‖embO w (y a)‖ ≤ ‖toR y‖ :=
    (norm_le_pi_norm (toR y w) a).trans (norm_le_pi_norm (toR y) w)
  have hzR : (R : ℝ) < ‖toR y‖ := hlt.trans_le hle
  have hz1 : (1 : ℝ) ≤ ‖toR y‖ := hR1.le.trans hzR.le
  have hsq : ‖toR y‖ ≤ ‖toR y‖ ^ 2 := by nlinarith
  have hB : B < c * ‖toR y‖ := by
    rw [div_lt_iff₀ hc] at hRB
    nlinarith
  exact lt_of_lt_of_le (hB.trans_le (mul_le_mul_of_nonneg_left hsq hc.le)) (hk (toR y))
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.hnfone :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (I : ℕ), 0 < I →
    ∃ S : Finset (Matrix (Fin N) (Fin N) (𝓞 L)), S.card ≤ I ^ (dd L N * N) ∧ ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 → nrmDet A = I →
      ∃ g : Gm L N, (g : Matrix (Fin N) (Fin N) (𝓞 L)) * A ∈ S := by
  classical
  intro L _ _ N I hI
  have hr0 : (I : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hI.ne'
  have hcardQ : Nat.card (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) = I ^ Module.finrank ℚ L := by
    have h1 := Ideal.absNorm_span_singleton (I : 𝓞 L)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    rw [h1, ← map_natCast (algebraMap ℤ (𝓞 L)) I, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank]
    simp
  haveI : Finite (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact pow_ne_zero _ hI.ne')
  letI : Fintype (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) := Fintype.ofFinite _
  have hB : ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 ∧ nrmDet A = I →
      ∃ B, A * B = (I : 𝓞 L) • 1 ∧ B * A = (I : 𝓞 L) • 1 := by
    intro A hA
    obtain ⟨_, B, h1, h2⟩ := scinv L N A hA.1
    rw [hA.2] at h1 h2
    exact ⟨B, h1, h2⟩
  let key : Matrix (Fin N) (Fin N) (𝓞 L) → Matrix (Fin N) (Fin N) (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) :=
    fun A => if h : A.det ≠ 0 ∧ nrmDet A = I then
      (Classical.choose (hB A h)).map (Ideal.Quotient.mk _) else 0
  let rep : Matrix (Fin N) (Fin N) (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) → Matrix (Fin N) (Fin N) (𝓞 L) :=
    fun k => if h : ∃ A, (A.det ≠ 0 ∧ nrmDet A = I) ∧ key A = k then Classical.choose h else 0
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ]
    change Fintype.card (Fin N → Fin N → 𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) = _
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcardQ,
      dd, ← pow_mul, ← pow_mul, mul_assoc]
  · intro A hdet hnrm
    have hA : A.det ≠ 0 ∧ nrmDet A = I := ⟨hdet, hnrm⟩
    have hex : ∃ A', (A'.det ≠ 0 ∧ nrmDet A' = I) ∧ key A' = key A := ⟨A, hA, rfl⟩
    have hrep : rep (key A) = Classical.choose hex := dif_pos hex
    obtain ⟨hA'P, hA'k⟩ := Classical.choose_spec hex
    obtain ⟨h1, h2⟩ := Classical.choose_spec (hB A hA)
    obtain ⟨h1', h2'⟩ := Classical.choose_spec (hB _ hA'P)
    have hkk : (Classical.choose (hB _ hA'P)).map (Ideal.Quotient.mk (Ideal.span {(I : 𝓞 L)})) =
        (Classical.choose (hB A hA)).map (Ideal.Quotient.mk _) := by
      have keyeq : ∀ (M : Matrix (Fin N) (Fin N) (𝓞 L)) (h : M.det ≠ 0 ∧ nrmDet M = I),
          key M = (Classical.choose (hB M h)).map (Ideal.Quotient.mk _) := fun M h => dif_pos h
      exact (keyeq _ hA'P).symm.trans (hA'k.trans (keyeq A hA))
    have hent : ∀ i j, ∃ x, Classical.choose (hB A hA) i j - Classical.choose (hB _ hA'P) i j =
        (I : 𝓞 L) * x := by
      intro i j
      have h := congrFun (congrFun hkk i) j
      simp only [Matrix.map_apply] at h
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      exact ⟨-c, by rw [mul_neg, ← hc, neg_sub]⟩
    choose X hX using hent
    obtain ⟨g, hg⟩ := hnfeq (𝓞 L) N (I : 𝓞 L) hr0 A (Classical.choose hex) _ _ (Matrix.of X)
      h1 h2 h1' h2' (by ext i j; simp [hX])
    refine ⟨g, ?_⟩
    rw [hg, Finset.mem_image]
    exact ⟨key A, Finset.mem_univ _, hrep⟩
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

@[to_additive]
private theorem UpperTheory.V.KT.prod_emb (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L]
    {M : Type} [CommMonoid M] (f : (L →+* ℂ) → M) :
    ∏ φ, f φ = ∏ w : InfinitePlace L, (f w.embedding * f (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk f]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro e
    have := IsTotallyComplex.isComplex w
    rw [InfinitePlace.isComplex_iff] at this
    exact this (ComplexEmbedding.isReal_iff.mpr e.symm)
  rw [← Finset.prod_pair hne]
  congr 1
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rw [← InfinitePlace.mk_embedding w, eq_comm, InfinitePlace.mk_eq_iff] at h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (rfl | rfl)
    · exact InfinitePlace.mk_embedding w
    · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

private theorem UpperTheory.V.KT.det_emb (L : Type) [Field L] [NumberField L] :
    star (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)).det *
      (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)).det =
      (absD L : ℂ) := by
  classical
  have hE : (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) =
      ((basisMatrix L).submatrix (equivReindex L).symm (equivReindex L).symm)ᵀ := by
    ext k i
    simp [canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  rw [hE, det_transpose, det_submatrix_equiv_self]
  have h := congrArg norm (discr_eq_basisMatrix_det_sq L)
  rw [norm_pow, Complex.norm_intCast] at h
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← h, absD, ← Int.cast_abs,
    ← Int.natCast_natAbs]
  rw [Int.cast_natCast, Complex.ofReal_natCast]

theorem UpperTheory.V.KT.gramdet :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (h : HS L N),
    2 ^ dd L N * (gram h).det = (absD L : ℝ) ^ N * (∏ w, (mat h w).det.re) ^ 2 := by
  intro L _ _ _ N h
  classical
  let A : (L →+* ℂ) → Matrix (Fin N) (Fin N) ℂ := fun φ =>
    if φ = (InfinitePlace.mk φ).embedding then mat h (InfinitePlace.mk φ)
    else (mat h (InfinitePlace.mk φ))ᵀ
  have hne : ∀ w : InfinitePlace L, ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
    intro w e
    have := IsTotallyComplex.isComplex w
    rw [InfinitePlace.isComplex_iff] at this
    exact this (ComplexEmbedding.isReal_iff.mpr e)
  have hA1 : ∀ w : InfinitePlace L, A w.embedding = mat h w := by
    intro w; simp [A, InfinitePlace.mk_embedding]
  have hA2 : ∀ w : InfinitePlace L, A (ComplexEmbedding.conjugate w.embedding) = (mat h w)ᵀ := by
    intro w; simp only [A, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg (hne w)]
  have key := UpperTheory.V.KT.blockdet (BI L) N
    (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L))
    (fun k => A ((equivReindex L).symm k))
  rw [UpperTheory.V.KT.det_emb, Equiv.prod_comp (equivReindex L).symm (fun φ => (A φ).det),
    UpperTheory.V.KT.prod_emb L] at key
  have hM : (Matrix.of fun s t : Fin N × BI L => ∑ k,
      star ((Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) k s.2) *
        A ((equivReindex L).symm k) s.1 t.1 *
        (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) k t.2) =
      Complex.ofRealHom.mapMatrix ((2 : ℝ) • gram h) := by
    ext s t
    simp only [of_apply]
    rw [Equiv.sum_comp (equivReindex L).symm (fun φ => star (φ (RingOfIntegers.basis L s.2 : L)) *
      A φ s.1 t.1 * φ (RingOfIntegers.basis L t.2 : L)), UpperTheory.V.KT.sum_emb L]

    simp only [hA1, hA2, RingHom.mapMatrix_apply, map_apply, Matrix.smul_apply, gram, of_apply,
    smul_eq_mul, Finset.mul_sum, map_sum, Complex.ofRealHom_eq_coe]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Complex.add_conj]
    have hh : mat h w t.1 s.1 = star (mat h w s.1 t.1) := ((mat_herm h w).apply t.1 s.1).symm
    simp [embO, hh, ComplexEmbedding.conjugate_coe_eq]
  rw [hM, ← RingHom.map_det, det_smul] at key
  have hc : Fintype.card (Fin N × BI L) = dd L N := by
    rw [Fintype.card_prod, Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex,
      RingOfIntegers.rank, mul_comm]
  have hd : ∀ w, (mat h w).det = ((mat h w).det.re : ℂ) := by
    intro w
    have : star (mat h w).det = (mat h w).det := by
      rw [← det_conjTranspose, (mat_herm h w).eq]
    exact (Complex.conj_eq_iff_re.mp this).symm
  simp only [hA1, hA2, det_transpose, hc] at key
  rw [Finset.prod_congr rfl fun w _ => by rw [hd w]] at key
  apply Complex.ofReal_injective
  rw [← Complex.ofRealHom_eq_coe, key, Finset.prod_mul_distrib]
  push_cast
  ring
end
