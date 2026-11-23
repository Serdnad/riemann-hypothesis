module

public import ReciprocityTheory.SemistableReduction.Bundle002
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.ExistsDualDerivations
public import ReciprocityTheory.SemistableReduction.Bundle012
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Ultra
public import ReciprocityTheory.SemistableReduction.Bundle011
public import ReciprocityTheory.SemistableReduction.Bundle004
public import ReciprocityTheory.SemistableReduction.Bundle010

@[expose] public section

section

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial DerivationAlgebraicIndependence

theorem trdeg_sField {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ) :
    Algebra.trdeg K (SField Ω D m) = Algebra.trdeg K Ω + ((1 + (D + 1) * m : ℕ) : Cardinal) := by
  classical
  haveI : FaithfulSMul K Ω :=
    (faithfulSMul_iff_algebraMap_injective K Ω).2 (algebraMap K Ω).injective
  haveI : FaithfulSMul Ω (MvPolynomial (SVars D m) Ω) :=
    (faithfulSMul_iff_algebraMap_injective Ω _).2 (MvPolynomial.C_injective _ _)
  haveI : FaithfulSMul (MvPolynomial (SVars D m) Ω) (SField Ω D m) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (IsFractionRing.injective (MvPolynomial (SVars D m) Ω) (SField Ω D m))
  have h1 := trdeg_add_eq K (MvPolynomial (SVars D m) Ω) (A := SField Ω D m)
  have h2 := trdeg_add_eq K Ω (A := MvPolynomial (SVars D m) Ω)
  have h3 : Algebra.trdeg (MvPolynomial (SVars D m) Ω) (SField Ω D m) = 0 :=
    trdeg_eq_zero_iff.2
      (IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (SVars D m) Ω)))
  have h4 : Algebra.trdeg Ω (MvPolynomial (SVars D m) Ω) =
      ((1 + (D + 1) * m : ℕ) : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
    congr 1
    simp [SVars, Fintype.card_sum, Fintype.card_prod]
  rw [← h1, h3, add_zero, ← h2, h4]

theorem genericImageFinite : FieldOfSStatement := by
  classical
  unfold FieldOfSStatement
  intro K Ω _ _ _ _ D m x hfg htr hJ
  obtain ⟨J, hJ⟩ := hJ
  set v : Fin D → KaehlerDifferential K Ω := fun a => KaehlerDifferential.D K Ω (x (J a)) with hv
  have hli : LinearIndependent Ω v := hJ
  have hφ : ∀ a : Fin D, ∃ φ : KaehlerDifferential K Ω →ₗ[Ω] Ω,
      ∀ b, φ (v b) = if a = b then 1 else 0 := by
    intro a
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply a).comp hli.repr)
    refine ⟨g, fun b => ?_⟩
    have hb : v b ∈ Submodule.span Ω (Set.range v) := Submodule.subset_span ⟨b, rfl⟩
    have h := congrArg (fun f => f ⟨v b, hb⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h, Finsupp.lapply_apply, hli.repr_eq_single b ⟨v b, hb⟩ rfl, Finsupp.single_apply]
    simp [eq_comm]
  choose φ hφ using hφ
  let δ : Fin D → Derivation K Ω Ω := fun a => (φ a).compDer (KaehlerDifferential.D K Ω)
  have hδ : ∀ a b, δ a (x (J b)) = if a = b then 1 else 0 := fun a b => hφ a b
  have hg := DerivationAlgebraicIndependence.gFam_indep (K := K) x J δ hδ
  have hind : AlgebraicIndependent K (sImage (D := D) x) := by
    have h1 := hg.comp _ (DerivationAlgebraicIndependence.eIdx_injective D m)
    have h2 := h1.map'
      (f := IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m))
      (IsFractionRing.injective _ _)
    convert h2 using 1
    funext p
    simp [DerivationAlgebraicIndependence.sImage_eq]
  refine ⟨hind, ?_⟩
  have htrS : Algebra.trdeg K (SField Ω D m) = (((D + 1) * (m + 1) : ℕ) : Cardinal) := by
    rw [trdeg_sField, htr, ← Nat.cast_add]
    congr 1
    ring
  have hTB : IsTranscendenceBasis K (sImage (D := D) x) := by
    refine hind.isTranscendenceBasis_of_lift_trdeg_le ?_ ?_
    · rw [htrS]
      exact Cardinal.natCast_lt_aleph0
    · rw [htrS]
      simp
  have halg := hTB.isAlgebraic_field
  set E := IntermediateField.adjoin K (Set.range (sImage (D := D) x))
  obtain ⟨s, hs⟩ := hfg
  let f : Ω →ₐ[K] SField Ω D m :=
    (IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m)).comp
      (IsScalarTower.toAlgHom K Ω (MvPolynomial (SVars D m) Ω))
  let S : Set (SField Ω D m) := f '' (s : Set Ω) ∪
    Set.range (fun i => algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (MvPolynomial.X i))
  have hSfin : S.Finite := (s.finite_toSet.image _).union (Set.finite_range _)
  haveI : Finite S := hSfin.to_subtype
  let L := IntermediateField.adjoin E S
  have hK : IntermediateField.adjoin K (f '' (s : Set Ω)) ≤ L.restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact IntermediateField.subset_adjoin E S (Or.inl hz)
  have hω : ∀ ω : Ω, f ω ∈ L := by
    intro ω
    have h1 : f ω ∈ (IntermediateField.adjoin K (s : Set Ω)).map f :=
      (IntermediateField.mem_map _).2 ⟨ω, by rw [hs]; trivial, rfl⟩
    rw [IntermediateField.adjoin_map] at h1
    exact hK h1
  have hP : ∀ p : MvPolynomial (SVars D m) Ω,
      algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) p ∈ L := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h := hω a
      simpa [f, MvPolynomial.algebraMap_eq] using h
    | add p q hp hq =>
      rw [map_add (f := _)]
      exact L.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact L.mul_mem hp (IntermediateField.subset_adjoin E S (Or.inr ⟨i, rfl⟩))
  have htop : L = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (SVars D m) Ω) z
    exact L.div_mem (hP a) (hP b)
  have hfd : FiniteDimensional E L :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end ReciprocityTheory.MultiplicativeHeights
end

section

namespace ReciprocityTheory.MultiplicativeHeights

theorem cauchy_inequality_on_torus : CauchyTorusStatement := by
  intro K _ _ _ K₀ hK₀ n c hc hτ χ
  by_contra hχ
  push_neg at hχ
  have hev : ∀ᶠ ψ in Filter.cofinite, ‖c ψ‖ < 1 / 2 := hc.eventually (gt_mem_nhds (by norm_num))
  have hFfin : {ψ | ¬ ‖c ψ‖ < 1 / 2}.Finite := Filter.eventually_cofinite.1 hev
  set F := hFfin.toFinset with hFdef
  have hχF : χ ∈ F := by
    rw [Set.Finite.mem_toFinset]
    show ¬ ‖c χ‖ < 1 / 2
    linarith
  obtain ⟨χm, hχmF, hmax⟩ := F.exists_max_image (fun ψ => ‖c ψ‖) ⟨χ, hχF⟩
  have hgt : 1 < ‖c χm‖ := lt_of_lt_of_le hχ (hmax χ hχF)
  have hglob : ∀ ψ, ‖c ψ‖ ≤ ‖c χm‖ := by
    intro ψ
    by_cases hψ : ψ ∈ F
    · exact hmax ψ hψ
    · have h2 : ‖c ψ‖ < 1 / 2 := by
        rw [Set.Finite.mem_toFinset] at hψ
        simpa using hψ
      linarith
  set lam := c χm with hlam
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hgt
    linarith
  set a : (Fin n → ℤ) → K := fun ψ => c ψ / lam with hadef
  have ha : ∀ ψ, ‖a ψ‖ ≤ 1 := by
    intro ψ
    simp only [hadef, norm_div]
    exact (div_le_one (norm_pos_iff.2 hlam0)).2 (hglob ψ)
  have ha0 : ‖a χm‖ = 1 := by
    simp only [hadef, norm_div]
    exact div_self (norm_ne_zero_iff.2 hlam0)
  obtain ⟨τ, hτu, hτ1⟩ := exists_torus_point_one_le_norm_sum K₀ hK₀ F a ha χm hχmF ha0
  have hprodnorm : ∀ ψ : Fin n → ℤ, ‖∏ i, τ i ^ ψ i‖ = 1 := by
    intro ψ
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [norm_zpow, (hτu i).2, one_zpow]
  have hSF : ∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i = lam * ∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    simp only [hadef]
    field_simp
  have hSFn : ‖lam‖ ≤ ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ := by
    rw [hSF, norm_mul]
    calc ‖lam‖ = ‖lam‖ * 1 := (mul_one _).symm
      _ ≤ ‖lam‖ * ‖∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i‖ := mul_le_mul_of_nonneg_left hτ1 (norm_nonneg _)
  have hsum : Summable (fun ψ => c ψ * ∏ i, τ i ^ ψ i) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_mul, hprodnorm] using hc
  have hsplit := hsum.sum_add_tsum_compl (s := F)
  have htail : ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ ≤ 1 / 2 := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun ψ => ?_
    rw [norm_mul, hprodnorm, mul_one]
    have hψ : (ψ : Fin n → ℤ) ∉ F := fun h => ψ.2 (Finset.mem_coe.2 h)
    rw [Set.Finite.mem_toFinset] at hψ
    simp only [Set.mem_setOf_eq, not_not] at hψ
    exact le_of_lt hψ
  have hne : ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ ≠
      ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ := by
    intro h
    linarith
  have htot := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [hsplit] at htot
  have h1 := hτ τ hτu
  unfold torusSum at h1
  rw [htot] at h1
  have h3 := le_max_left ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖
    ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖
  linarith

end ReciprocityTheory.MultiplicativeHeights
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors

theorem hermForm_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (u w : Fin r → K) : S.h (a • u) w = S.c a * S.h u w := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermForm_eq_mulVec {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (u w : Fin r → K) : S.h u w = ∑ b, (∑ a, S.c (u a) * S.G a b) * w b := by
  simp only [HermForm.h, Finset.sum_mul]
  rw [Finset.sum_comm]

def rowMat {K : Type} [Field K] {k : ℕ} (z : Fin k → Fin k → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i a => z i a

theorem det_rowMat {K : Type} [Field K] {k : ℕ} (z : Fin k → Fin k → K)
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1) : (rowMat z).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [rowMat, hdiag]
  · intro i j hji
    exact htri i j hji

theorem hermForm_rows {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (z : Fin k → Fin k → K) (i : Fin k) (v : Fin k → K) :
    S.h (z i) v = (((rowMat z).map S.c * S.G) *ᵥ v) i := by
  rw [hermForm_eq_mulVec]
  simp [mulVec, dotProduct, Matrix.mul_apply, rowMat]

theorem smul_mem_of_split {K : Type} [Field K] [NumberField K] {k : ℕ}
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (hin : ∀ t : Fin k → K, (∀ i, t i ∈ C i) → ∑ i, t i • z i ∈ X) (j : Fin k) {a : K}
    (ha : a ∈ C j) : a • z j ∈ X := by
  classical
  have h := hin (Pi.single j a) (fun i => by
    by_cases hij : i = j
    · subst hij; simpa using ha
    · simp [hij])
  simpa [Pi.single_apply] using h

theorem integral_of_mem_one {K : Type} [Field K] [NumberField K] {x : K}
    (hx : x ∈ (1 : Submodule (𝓞 K) K)) : IsIntegralElt x := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 hx
  exact ⟨a, ha⟩

theorem split_integral {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1)
    (hin : ∀ t : Fin k → K, (∀ i, t i ∈ C i) → ∑ i, t i • z i ∈ X) (hint : IsIntegralOn S X)
    (s t : Fin k → K) (hs : ∀ i, S.c (s i) ∈ C i) (ht : ∀ i, t i ∈ C i) :
    (∏ i, s i) * S.G.det * (∏ i, t i) ∈ (1 : Submodule (𝓞 K) K) := by
  let M : Matrix (Fin k) (Fin k) K :=
    Matrix.of fun i j => S.h (S.c (s i) • z i) (t j • z j)
  have hM : M = Matrix.diagonal s * (((rowMat z).map S.c * S.G) * (rowMat z)ᵀ) *
      Matrix.diagonal t := by
    ext i j
    simp only [M, Matrix.of_apply, hermForm_smul_smul, S.c_invol, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    rw [hermForm_rows]
    simp [mulVec, dotProduct, Matrix.mul_apply, rowMat]
    ring
  have hdet : M.det = (∏ i, s i) * S.G.det * (∏ i, t i) := by
    have : ((rowMat z).map S.c).det = 1 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_rowMat z htri hdiag, map_one]
    rw [hM]
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
      det_rowMat z htri hdiag, this]
    ring
  have hent : ∀ i j, ∃ m : 𝓞 K, algebraMap (𝓞 K) K m = M i j := fun i j =>
    hint _ (smul_mem_of_split hin i (hs i)) _ (smul_mem_of_split hin j (ht j))
  choose m hm using hent
  have : M = (Matrix.of m).map (algebraMap (𝓞 K) K) := by
    ext i j
    simp [hm]
  rw [← hdet, this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact Submodule.mem_one.2 ⟨_, rfl⟩

theorem split_selfDual {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1)
    (hdec : ∀ x ∈ X, ∃ t : Fin k → K, (∀ i, t i ∈ C i) ∧ x = ∑ i, t i • z i)
    (hsd : IsSelfDual S X) (hG : S.G.det ≠ 0) (u : Fin k → K)
    (hu : ∀ j, ∀ w, S.c w ∈ C j → u j * w ∈ (1 : Submodule (𝓞 K) K)) :
    ∏ j, u j ∈ Submodule.span (𝓞 K) {S.G.det} * ∏ i, C i := by
  classical
  set Q : Matrix (Fin k) (Fin k) K := (rowMat z).map S.c * S.G with hQ
  have hQdet : Q.det = S.G.det := by
    rw [hQ, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      det_rowMat z htri hdiag, map_one, one_mul]
  have hQu : IsUnit Q.det := by rw [hQdet]; exact isUnit_iff_ne_zero.2 hG
  let y : Fin k → Fin k → K := fun j => Q⁻¹ *ᵥ Pi.single j (u j)
  have hQy : ∀ j, Q *ᵥ y j = Pi.single j (u j) := fun j => by
    simp only [y, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQu, Matrix.one_mulVec]
  have hy : ∀ j, y j ∈ X := by
    intro j
    refine hsd.2 _ fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := hdec x hx
    rw [← hermForm_conj]
    have : S.h (∑ i, t i • z i) (y j) = S.c (t j) * u j := by
      rw [hermForm_sum_left]
      simp only [hermForm_smul_left, hermForm_rows, ← hQ, hQy, Pi.single_apply]
      simp
    rw [this]
    refine integral_of_mem_one (mem_one_map S.c ?_)
    rw [mul_comm]
    exact hu j _ (by rw [S.c_invol]; exact ht j)
  choose T hT hTy using fun j => hdec (y j) (hy j)
  let Tm : Matrix (Fin k) (Fin k) K := Matrix.of fun i j => T j i
  have hY1 : (Matrix.of fun a j => y j a) = (rowMat z)ᵀ * Tm := by
    ext a j
    simp only [Matrix.of_apply]
    rw [hTy j]
    simp [Tm, rowMat, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  have hY2 : (Matrix.of fun a j => y j a) = Q⁻¹ * Matrix.diagonal u := by
    ext a j
    simp [y, Matrix.mul_diagonal, mul_comm]
  have hdet : (∏ j, u j) = S.G.det * Tm.det := by
    have h1 := congrArg Matrix.det hY1
    rw [hY2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_rowMat z htri hdiag,
      one_mul, Matrix.det_nonsing_inv, Matrix.det_diagonal, hQdet, Ring.inverse_eq_inv'] at h1
    rw [← h1]
    field_simp
  rw [hdet]
  exact Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _)
    (det_mem_prod_sub C Tm fun i j => hT j i)

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

theorem residueTrdeg_holds (hTR : TRStatement) : ResidueTrdegStatement := by
  intro K Ω U _ _ _ _ _ D hD σ _ t V ht τ _ u p hp hcard hpu hind
  letI _iW := residueAlgebra V (algebraMap Ω U)
  letI _io := residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
  letI : Algebra (IsLocalRing.ResidueField
      ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (IsLocalRing.ResidueField V) :=
    ((algebraMap _ (IsLocalRing.ResidueField V)).comp
      (algebraMap _ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
  have hTRW := hTR K Ω (V.comap (algebraMap Ω U))
  rw [hD] at hTRW
  have hST : IsScalarTower
      (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) (IsLocalRing.ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hres : ∀ j, IsLocalRing.residue V (u j) =
      aeval (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) (gaussRed V (p j) (hp j)) := by
    intro j
    obtain ⟨h, he⟩ := gaussRed_eval t V ht (p j) (hp j)
    have : u j = ⟨aeval t (p j), h⟩ := Subtype.ext (hpu j).symm
    rw [this, he]
  have hcardc : Cardinal.mk τ = ((Fintype.card σ + D : ℕ) : Cardinal) := by
    rw [Cardinal.mk_fintype, hcard]
  have hσ := Cardinal.mk_fintype σ
  have hmemW : ∀ j, IsLocalRing.residue V (u j) ∈
      Algebra.adjoin (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (Set.range fun s => IsLocalRing.residue V ⟨t s, ht s⟩) := by
    intro j
    rw [hres j]
    exact gauss_aeval_mem _ _ (Algebra.adjoin _ _).toSubring
      (fun α => Subalgebra.algebraMap_mem _ _) (fun s => Algebra.subset_adjoin ⟨s, rfl⟩)
  have hW := gauss_card_le_trdeg_add _ _ hind hmemW
  rw [hcardc] at hW
  obtain ⟨h2, h3⟩ := gauss_card_arith hW hTRW (hσ ▸ gauss_trdeg_adjoin_le _)
  refine ⟨?_, h2, gauss_indep_of_le_trdeg _ (hσ.trans h3.symm).le⟩
  intro k₁ hk₁
  letI : Algebra k₁ (IsLocalRing.ResidueField V) :=
    ((algebraMap (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
      (IsLocalRing.ResidueField V)).comp (algebraMap k₁ _)).toAlgebra
  have hST1 : IsScalarTower
      (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      k₁ (IsLocalRing.ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmem1 : ∀ j, IsLocalRing.residue V (u j) ∈
      Algebra.adjoin k₁ (Set.range fun s => IsLocalRing.residue V ⟨t s, ht s⟩) := by
    intro j
    rw [hres j]
    refine gauss_aeval_mem _ _ (Algebra.adjoin k₁ _).toSubring (fun α => ?_)
      (fun s => Algebra.subset_adjoin ⟨s, rfl⟩)
    have hc : (gaussRed V (p j) (hp j)).coeff α ∈ k₁ := by
      rw [gaussRed_coeff]; exact hk₁ j α
    exact Subalgebra.algebraMap_mem (Algebra.adjoin k₁ _) (⟨_, hc⟩ : k₁)
  have h1 := @gauss_card_le_trdeg_add _ _ _ _ _ _ _ _ _ hST1 _ _ _ _ hind hmem1
  rw [hcardc] at h1
  have hk : Algebra.trdeg _ k₁ ≤ (D : Cardinal) :=
    (trdeg_le_of_injective k₁.val Subtype.val_injective).trans hTRW
  exact (gauss_card_arith h1 hk (hσ ▸ gauss_trdeg_adjoin_le _)).1

end ReciprocityTheory.MultiplicativeHeights
end
