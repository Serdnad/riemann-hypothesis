module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle012
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.RealPlaceAnalysis.Bundle001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPTorsionIntegralAndDistinctMod
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Formalism.RealPlaceAnalysis.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.SemistableReduction.Bundle019

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.frobenius_fixes_of_splitsCompletely_intermediate : ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K)), {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard = Module.finrank K M → ∀ (σ : N ≃ₐ[K] N), GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x ∈ M, σ x = x := by
  first | exact @GlobalTheory.SplitCriterion.frob_fix_of_ncard_primes_eq_finrank | exact GlobalTheory.SplitCriterion.frob_fix_of_ncard_primes_eq_finrank | (intros; apply GlobalTheory.SplitCriterion.frob_fix_of_ncard_primes_eq_finrank <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.ncard_primes_eq_finrank_of_frobenius_fixes : ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K)), (∀ (σ : N ≃ₐ[K] N), GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x ∈ M, σ x = x) → {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard = Module.finrank K M := by
  first | exact @GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix | exact GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix | (intros; apply GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix <;> assumption)
end

section

open MeasureTheory Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.UpqUnimodular

theorem isMulRightInvariant_of_continuousMulEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]
    (e : G ≃ₜ* H) (μ : Measure G) (h : (μ.map e).IsMulRightInvariant) :
    μ.IsMulRightInvariant := by
  have he : Measurable e := e.continuous.measurable
  have hs : Measurable e.symm := e.symm.continuous.measurable
  have hμ : μ = (μ.map e).map e.symm := by
    rw [Measure.map_map hs he]
    have : (e.symm : H → G) ∘ e = id := by ext x; simp
    rw [this, Measure.map_id]
  refine ⟨fun g => ?_⟩
  have h1 := h.map_mul_right_eq_self (e g)
  have hc : (fun x : G => x * g) ∘ (e.symm : H → G) = (e.symm : H → G) ∘ (fun y : H => y * e g) := by
    ext y; simp
  conv_lhs => rw [hμ]
  rw [Measure.map_map (measurable_mul_const g) hs, hc,
    ← Measure.map_map hs (measurable_mul_const _), h1, ← hμ]

def signs (P Q : ℕ) : Fin (P + Q) → Bool := fun i => (finSumFinEquiv.symm i).isLeft

theorem reindex_Jpq (P Q : ℕ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Formalism.UG.Jpq P Q) = Formalism.REAL.Jm (signs P Q) := by
  ext i j
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, signs, Formalism.UG.Jpq]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply] <;> split_ifs <;> simp

def reindexUnits (P Q : ℕ) :
    GL (Fin P ⊕ Fin Q) ℂ ≃ₜ* (Matrix (Fin (P + Q)) (Fin (P + Q)) ℂ)ˣ where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv).toMulEquiv
  continuous_toFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := P) (n := Q))).toMulEquiv.toMonoidHom))
    (continuous_id.matrix_reindex _ _)
  continuous_invFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := P) (n := Q))).toMulEquiv.symm.toMonoidHom))
    ((continuous_id.matrix_reindex (finSumFinEquiv (m := P) (n := Q)).symm
      (finSumFinEquiv (m := P) (n := Q)).symm).congr fun _ => rfl)

theorem reindexUnits_val (P Q : ℕ) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    (reindexUnits P Q g : Matrix (Fin (P + Q)) (Fin (P + Q)) ℂ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := rfl

theorem reindexUnits_mem_iff (P Q : ℕ) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    reindexUnits P Q g ∈ Formalism.REAL.UJ (signs P Q) ↔ g ∈ Formalism.UG.Upq P Q := by
  change Formalism.REAL.inUJ (signs P Q) (reindexUnits P Q g : Matrix (Fin (P + Q)) (Fin (P + Q)) ℂ) ↔
    (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).conjTranspose * Formalism.UG.Jpq P Q *
      (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = Formalism.UG.Jpq P Q
  rw [Formalism.REAL.inUJ, reindexUnits_val, ← reindex_Jpq, Matrix.conjTranspose_reindex]
  rw [← (Matrix.reindex (α := ℂ) (finSumFinEquiv (m := P) (n := Q))
    (finSumFinEquiv (m := P) (n := Q))).injective.eq_iff]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

def modelEquiv (P Q : ℕ) : UpqT P Q ≃ₜ* Formalism.REAL.UJ (signs P Q) where
  toFun g := ⟨reindexUnits P Q (g : Formalism.UG.Upq P Q).1,
    (reindexUnits_mem_iff P Q _).2 (g : Formalism.UG.Upq P Q).2⟩
  invFun h := (⟨(reindexUnits P Q).symm h.1,
    (reindexUnits_mem_iff P Q _).1 (by simpa using h.2)⟩ : Formalism.UG.Upq P Q)
  left_inv g := Subtype.ext ((reindexUnits P Q).symm_apply_apply _)
  right_inv h := Subtype.ext ((reindexUnits P Q).apply_symm_apply _)
  map_mul' g h := Subtype.ext (map_mul (reindexUnits P Q) _ _)
  continuous_toFun :=
    ((reindexUnits P Q).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((reindexUnits P Q).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem isMulRightInvariant_of_isHaarMeasure (P Q : ℕ) (μ : Measure (UpqT P Q))
    (hμ : μ.IsHaarMeasure) : μ.IsMulRightInvariant := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  refine isMulRightInvariant_of_continuousMulEquiv (modelEquiv P Q) μ ?_
  haveI : (μ.map (modelEquiv P Q)).IsHaarMeasure := (modelEquiv P Q).isHaarMeasure_map μ
  haveI : (Formalism.REAL.muG (signs P Q)).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  rw [Measure.isMulLeftInvariant_eq_smul (μ.map (modelEquiv P Q)) (Formalism.REAL.muG (signs P Q))]
  infer_instance

end GlobalTheory.UpqUnimodular
end
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.TorsionIntegralPos
open GlobalTheory.TorsionIntegral


open IsLocalRing in
theorem torsion_integral_distinct_of_pos : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (m : ℕ),
    (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W →
    0 < m → (m : ℂ)⁻¹ ∈ W →
    (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W) ∧
    ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice →
      t' ∉ L.lattice → L.weierstrassP t - L.weierstrassP t' ∈ W.nonunits →
      t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice := by
  intro L W m h2 _ hg2 hg3 hΔ hpos hm
  have hI : ∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W :=
    fun t a b => integral L W m h2 hg2 hg3 hpos.ne' hm a b
  refine ⟨hI, fun t t' a b a' b' hn => ?_⟩
  by_contra hc
  have hne : L.weierstrassP t ≠ L.weierstrassP t' := mt (GlobalTheory.weierstrassP_eq_iff L b b').1 hc
  rw [not_or] at hc
  obtain ⟨hs, hp⟩ := sum_prod L b b' hne
  let x1 : W := ⟨_, hI t a b⟩
  let x2 : W := ⟨_, hI t' a' b'⟩
  let x3 : W := ⟨_, hI (t + t') (by rw [mul_add]; exact add_mem a a') hc.2⟩
  let x4 : W := ⟨_, hI (t - t') (by rw [mul_sub]; exact sub_mem a a') hc.1⟩
  let g2 : W := ⟨L.g₂, hg2⟩
  let g3 : W := ⟨L.g₃, hg3⟩
  let h : W := ⟨2⁻¹, h2⟩
  let e : W := ⟨_, hΔ⟩
  have c2 : ((2 : W) : ℂ) = 2 := rfl
  have c27 : ((27 : W) : ℂ) = 27 := rfl
  have e1 : (x3 + x4) * (x1 - x2) ^ 2 = 2 * x1 * x2 * (x1 + x2) - g2 * h * (x1 + x2) - g3 := by
    apply Subtype.ext
    simp [x1, x2, x3, x4, g2, g3, h, c2]
    linear_combination hs
  have e2 : x3 * x4 * (x1 - x2) ^ 2 = (x1 * x2 + g2 * h ^ 2) ^ 2 + g3 * (x1 + x2) := by
    apply Subtype.ext
    simp [x1, x2, x3, x4, g2, g3, h]
    linear_combination hp
  have e3 : 2 * h = 1 := by
    apply Subtype.ext
    simp [h, c2]
  have e4 : (g2 ^ 3 - 27 * g3 ^ 2) * e = 1 := by
    apply Subtype.ext
    simp [g2, g3, e, c27, disc L]
  have e5 : residue W (x1 - x2) = 0 :=
    (residue_eq_zero_iff _).2 (ValuationSubring.coe_mem_nonunits_iff.1 hn)
  have f1 := congrArg (residue W) e1
  have f2 := congrArg (residue W) e2
  have f3 := congrArg (residue W) e3
  have f4 := congrArg (residue W) e4
  simp only [map_mul, map_add (f := _), map_sub, map_pow, map_ofNat, map_one] at f1 f2 f3 f4 e5
  rw [sub_eq_zero] at e5
  rw [← e5] at f1 f2
  generalize residue W x1 = x at *
  generalize residue W g2 = A at *
  generalize residue W g3 = B at *
  generalize residue W h = u at *
  have k1 : 4 * x ^ 3 - A * x - B = 0 := by linear_combination (A * x) * f3 - f1
  have k2 : (4 * x ^ 2 + A) ^ 2 + 32 * B * x = 0 := by
    have hA : 4 * (x * x + A * u ^ 2) = 4 * x ^ 2 + A := by
      linear_combination A * (2 * u + 1) * f3
    rw [← hA]; linear_combination -16 * f2
  have k3 : A ^ 3 - 27 * B ^ 2 = 0 := by
    linear_combination (A - 3 * x ^ 2) * k2 + (12 * x ^ 3 + 5 * A * x + 27 * B) * k1
  rw [k3, zero_mul] at f4
  exact zero_ne_one f4

end GlobalTheory.TorsionIntegralPos
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.weierstrassP_torsion_integral_and_distinct_mod : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (m : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → Odd m → (m : ℂ)⁻¹ ∈ W → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W) ∧ ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → L.weierstrassP t - L.weierstrassP t' ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice := by
  first | exact @GlobalTheory.TorsionIntegral.torsion_integral_distinct | exact GlobalTheory.TorsionIntegral.torsion_integral_distinct | (intros; apply GlobalTheory.TorsionIntegral.torsion_integral_distinct <;> assumption)
end

section

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct


open NumberField in
open scoped TensorProduct in
open scoped IntermediateField.algebraAdjoinAdjoin in
theorem _root_.GlobalTheory.exists_linearIndependent_D_iff_trdeg_adjoin_eq {K Ω κ : Type} [Field K] [CharZero K]
    [Field Ω] [Algebra K Ω] {D : ℕ} (hD : Algebra.trdeg K Ω = D) (x : κ → Ω) :
    (∃ J : Fin D → κ, LinearIndependent Ω fun k => KaehlerDifferential.D K Ω (x (J k))) ↔
      Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) = D := by
  constructor
  · rintro ⟨J, hJ⟩
    have hind : AlgebraicIndependent K fun k => x (J k) := _root_.ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence K Ω D (fun k => x (J k)) hJ
    let y : Fin D → IntermediateField.adjoin K (Set.range x) :=
      fun k => ⟨x (J k), IntermediateField.subset_adjoin K _ ⟨J k, rfl⟩⟩
    have hy : AlgebraicIndependent K y :=
      AlgebraicIndependent.of_comp (IntermediateField.adjoin K (Set.range x)).val hind
    apply le_antisymm
    · rw [← hD]
      exact trdeg_le_of_injective _ (IntermediateField.adjoin K (Set.range x)).val.injective
    · simpa using hy.cardinalMk_le_trdeg
  · intro h
    set L := IntermediateField.adjoin K (Set.range x) with hL
    set s : Set L := Subtype.val ⁻¹' Set.range x with hs
    have hmem : ∀ z : L, z ∈ IntermediateField.adjoin K s := by
      intro z
      have hle : L ≤ (IntermediateField.adjoin K s).map L.val := by
        refine IntermediateField.adjoin_le_iff.mpr ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩,
          IntermediateField.subset_adjoin K _ ⟨i, rfl⟩, rfl⟩
      obtain ⟨m, hm, hmz⟩ := hle z.2
      rwa [show m = z from Subtype.ext hmz] at hm
    haveI : Algebra.IsAlgebraic (Algebra.adjoin K s) L := ⟨fun z => by
      have hz := isAlgebraic_algebraMap (R := IntermediateField.adjoin K s) (A := L) ⟨z, hmem z⟩
      exact IntermediateField.isAlgebraic_adjoin_iff.mp hz⟩
    obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := K) (A := L) s
    have hcard : Cardinal.mk t = D := by rw [ht.cardinalMk_eq_trdeg, h]
    obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hcard
    let v : t → Ω := fun z => ((z : L) : Ω)
    have hv : AlgebraicIndependent K v := ht.1.map' (f := L.val) Subtype.val_injective
    haveI : Finite t := Finite.of_equiv _ e.symm
    have hvb : IsTranscendenceBasis K v := by
      refine hv.isTranscendenceBasis_of_lift_trdeg_le ?_ ?_
      · rw [hD]; exact Cardinal.natCast_lt_aleph0
      · rw [hD, hcard]
    haveI := hvb.isAlgebraic_field
    haveI : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) Ω :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨b, hb⟩ := _root_.GlobalTheory.exists_basis_kaehler_of_algebraicIndependent hv
    have hex : ∀ k : Fin D, ∃ i, x i = (((e.symm k : t) : L) : Ω) := fun k => hts (e.symm k).2
    choose J hJ using hex
    refine ⟨J, ?_⟩
    have hfun : (fun k => KaehlerDifferential.D K Ω (x (J k))) = b ∘ e.symm := by
      funext k
      rw [Function.comp_apply, hb, hJ k]
    rw [hfun]
    exact b.linearIndependent.comp _ e.symm.injective

section Ratios

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

end Ratios

open NumberField in
private theorem sImg_eq_sImage_finSuccEquiv_reindex {Ω : Type} [Field Ω] {D N : ℕ} (j : Fin (N + 1))
    (x : Fin N → Ω) (p : _root_.ReciprocityTheory.ChartRestriction.G.T0.TVar D N) :
    _root_.ReciprocityTheory.ChartRestriction.G.T0.sImg j x p = _root_.ReciprocityTheory.MultiplicativeHeights.sImage x (p.1, ((finSuccEquiv' j).trans (finSuccEquiv N).symm) p.2) := by
  rcases p with ⟨a, i⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.sImg _root_.ReciprocityTheory.MultiplicativeHeights.sImage
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩
  · simp only [Equiv.trans_apply, finSuccEquiv'_at, finSuccEquiv_symm_none, Fin.cases_zero]
    exact congrArg _ (Fin.insertNth_apply_same i _ _)
  · simp only [Equiv.trans_apply, finSuccEquiv'_succAbove, finSuccEquiv_symm_some, Fin.cases_succ]
    exact congrArg _ (Fin.insertNth_apply_succAbove j _ _ k)


open NumberField in
theorem _root_.GlobalTheory.differentials_iff_trdegD_and_genericSection : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (_𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : _root_.ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A), ∀ c : ι, (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 → ((∃ J : Fin d.D → Fin d.N, LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) ↔ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c) ∧ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c → Function.Injective (d.sH c) ∧ FiniteDimensional (d.KT c) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS (Ω c) d.D d.N)) := by
  intro K _ _ ι _ Ω _ _ WT _ A _ _ _ _ _𝒜 d c hfg hD hw
  have hadj : IntermediateField.adjoin K
      (Set.range fun j => _root_.ReciprocityTheory.ChartRestriction.G.T0.ratio (d.w j c) (d.w (d.jc c) c)) =
      IntermediateField.adjoin K (Set.range (d.x c)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · show _root_.ReciprocityTheory.ChartRestriction.G.T0.ratio (d.w (d.jc c) c) (d.w (d.jc c) c) ∈ _
        rw [_root_.ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.ratio_eq hw (one_smul _ _).symm]
        exact one_mem _
      · exact IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨k, rfl⟩
      exact ⟨(d.jc c).succAbove k, rfl⟩
  have htr : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c ↔ Algebra.trdeg K (IntermediateField.adjoin K (Set.range (d.x c))) = d.D := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD
    rw [hadj]
  have key := _root_.GlobalTheory.exists_linearIndependent_D_iff_trdeg_adjoin_eq hD (d.x c)
  refine ⟨key.trans htr.symm, fun hT => ?_⟩
  obtain ⟨hind, hfin⟩ := _root_.ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) hfg hD (key.mpr (htr.mp hT))
  let e := (finSuccEquiv' (d.jc c)).trans (finSuccEquiv d.N).symm
  let σ : _root_.ReciprocityTheory.ChartRestriction.G.T0.TVar d.D d.N → Fin (d.D + 1) × Fin (d.N + 1) := fun p => (p.1, e p.2)
  have hσ : Function.Bijective σ := ((Equiv.refl (Fin (d.D + 1))).prodCongr e).bijective
  have hcomp : _root_.ReciprocityTheory.ChartRestriction.G.T0.sImg (d.jc c) (d.x c) = _root_.ReciprocityTheory.MultiplicativeHeights.sImage (d.x c) ∘ σ :=
    funext fun p => sImg_eq_sImage_finSuccEquiv_reindex _ _ p
  constructor
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.Data.sH _root_.ReciprocityTheory.ChartRestriction.G.T0.sHom
    rw [hcomp]
    exact hind.comp σ hσ.1
  · have hrange : Set.range (_root_.ReciprocityTheory.ChartRestriction.G.T0.sImg (d.jc c) (d.x c)) = Set.range (_root_.ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c)) := by
      rw [hcomp, Set.range_comp, hσ.2.range_eq, Set.image_univ]
    have hKT : d.KT c = IntermediateField.adjoin K (Set.range (_root_.ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c))) := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.Data.KT
      rw [hrange]
    rw [hKT]
    exact hfin

end GlobalTheory
end
