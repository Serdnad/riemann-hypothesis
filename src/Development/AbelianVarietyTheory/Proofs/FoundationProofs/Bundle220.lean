module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLKBasis
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle211
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Formalism.PairingDivisors.StatementH
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormOneScalar

theorem exists_of_anti {E : Type} [Field E] [CharZero E] (c : E →+* E) (s : E) (hs : s ≠ 0) (hc : c s = -s)
    (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) : ∃ z : E, z * c z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  have hm : ∀ k : ℕ, ((k : E) + 1) - s ≠ 0 := by
    intro k h
    have h1 : s = (k : E) + 1 := by linear_combination -h
    have h2 : c s = s := by rw [h1]; simp
    apply hs
    have : (2 : E) * s = 0 := by linear_combination hc - h2
    simpa using this
  have hp : ∀ k : ℕ, ((k : E) + 1) + s ≠ 0 := by
    intro k h
    have h1 : s = -((k : E) + 1) := by linear_combination h
    have h2 : c s = s := by rw [h1]; simp
    apply hs
    have : (2 : E) * s = 0 := by linear_combination hc - h2
    simpa using this
  let f : ℕ → E := fun k => (((k : E) + 1) + s) / (((k : E) + 1) - s)
  have hf : Function.Injective f := by
    intro a b h
    have h' := (div_eq_div_iff (hm a) (hm b)).1 h
    have : (2 : E) * s * ((a : E) - b) = 0 := by linear_combination -h'
    have h3 : (a : E) - b = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hs)
      · exact h
    exact_mod_cast sub_eq_zero.1 h3
  have hP : γ.charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := γ)
    rw [h] at this
    simp at this
  have hfin : {z : E | γ.charpolyRev.IsRoot z}.Finite := Polynomial.finite_setOfPred_isRoot hP
  obtain ⟨z, ⟨k, rfl⟩, hz⟩ := (Set.infinite_range_of_injective hf).exists_notMem_finite hfin
  refine ⟨f k, ?_, ?_, ?_⟩
  · have h1 := hm k
    have h2 := hp k
    simp only [f, map_div₀, map_add (f := _), map_sub, map_natCast, map_one, hc, sub_neg_eq_add, ← sub_eq_add_neg]
    field_simp
  · intro h
    have h' := (div_eq_one_iff_eq (hm k)).1 h
    apply hs
    have : (2 : E) * s = 0 := by linear_combination h'
    simpa using this
  · intro h
    apply hz
    show Polynomial.eval (f k) γ.charpolyRev = 0
    rw [← h, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij] <;> exact mul_comm _ _

theorem exists_norm_one_det_ne_zero : ∀ (D : D7) (n : ℕ) (γ : Matrix (Fin n) (Fin n) D.host.E),
    ∃ z : D.host.E, z * D.host.conj z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  intro D n γ
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have h1 := D.host.sqrtMinusD_sq
    rw [h] at h1
    have h2 : (D.host.d : D.host.E) = 0 := by linear_combination h1
    exact D.host.hyp.2.1.ne_zero (by exact_mod_cast h2)
  exact exists_of_anti (D.host.conj : D.host.E →+* D.host.E) D.host.sqrtMinusD hs D.host.conj_sqrtMinusD n γ

end GlobalTheory.NormOneScalar
end

section

open NumberField MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.StdLatSpan

variable (K : Type) [Field K] [NumberField K]

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma nabStd_fg' (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) : (_root_.Formalism.L2.DIV.nabStd K lam).FG := by
  classical
  unfold _root_.Formalism.L2.DIV.nabStd
  choose b hb _ using fun τ : ι => _root_.Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n (lam τ).natW
  have hinj : LinearMap.ker (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K))
  have hwb : ∀ τ, LinearIndependent (𝓞 K) (b τ) ∧
      Submodule.span (𝓞 K) (Set.range (b τ)) = _root_.Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n (lam τ).natW := by
    intro τ
    have h := hb τ
    unfold _root_.Formalism.GradedWeylDivisibility.IsWeightBasis at h
    exact ⟨h.1, h.2.1⟩
  haveI : ∀ τ, Finite ↑(_root_.Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) := fun τ => (_root_.Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  obtain ⟨-, hspan⟩ := _root_.Formalism.GradedWeylDivisibility.tensorBasis (𝓞 K) K ι n n (fun τ => ↑(_root_.Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW))
    (fun τ => Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.nablaSq (𝓞 K) n (lam τ)))
    (fun τ i => _root_.Formalism.L2.DIV.toK K (Fin n × Fin n) (b τ i))
    (fun τ => (hwb τ).1.map' _ hinj)
    (fun τ => by
      rw [Set.range_comp' (g := _root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (f := b τ), ← Submodule.map_span, (hwb τ).2]
      rfl)
  rw [← hspan]
  exact Submodule.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma prod_image_blockEmb_eq_setOf_prod {K : Type} [Field K] {S : Type} [Fintype S] {k n : ℕ}
    (X : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    (∏ s ∈ Finset.univ, (_root_.Formalism.GradedWeylDivisibility.blockEmb K s : MvPolynomial (Fin k × Fin n) K → _) '' X s) =
      {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ X s) ∧
        P = ∏ s, _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s)} := by
  ext P
  rw [Set.mem_finsetProd]
  constructor
  · rintro ⟨g, hg, rfl⟩
    choose F hF hFe using fun s => hg (Finset.mem_univ s)
    exact ⟨F, hF, Finset.prod_congr rfl fun s _ => (hFe s).symm⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨fun s => _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s), fun {s} _ => ⟨F s, hF s, rfl⟩, rfl⟩

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_setOf_prod_blockEmb_eq_prod_map_span {K : Type} [Field K] {S : Type} [Fintype S] {k n : ℕ}
    (X : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    Submodule.span K {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ X s) ∧
        P = ∏ s, _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s)} =
      ∏ s, Submodule.map (_root_.Formalism.GradedWeylDivisibility.blockEmb K s).toLinearMap (Submodule.span K (X s)) := by
  rw [← prod_image_blockEmb_eq_setOf_prod, ← Submodule.prod_span]
  simp only [Submodule.map_span, AlgHom.coe_toLinearMap]

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_tensorLat_eq_prod_map_span {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S]
    {k n : ℕ} (L : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) :
    Submodule.span K (_root_.Formalism.GradedWeylDivisibility.tensorLat R K L : Set (MvPolynomial (S × Fin k × Fin n) K)) =
      ∏ s, Submodule.map (_root_.Formalism.GradedWeylDivisibility.blockEmb K s).toLinearMap (Submodule.span K (L s : Set _)) := by
  unfold _root_.Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_span_of_tower]
  exact span_setOf_prod_blockEmb_eq_prod_map_span (K := K) (k := k) (n := n)
    fun s => (L s : Set (MvPolynomial (Fin k × Fin n) K))

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_map_toK_nablaSq_eq_nablaSq (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : _root_.Formalism.BasicNotions.DomWeight n) :
    Submodule.span K (Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.nablaSq (𝓞 K) n μ) : Set _) =
      _root_.Formalism.BasicNotions.nablaSq K n μ := by
  unfold _root_.Formalism.BasicNotions.nablaSq
  obtain ⟨b, hb, -⟩ := _root_.Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n μ.natW
  rw [← _root_.Formalism.GradedWeylDivisibility.span_map_weightBasis_eq_dualWeyl (K := K) hb]
  have hspan : Submodule.span (𝓞 K) (Set.range b) = _root_.Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n μ.natW := by
    unfold _root_.Formalism.GradedWeylDivisibility.IsWeightBasis at hb
    exact hb.2.1
  rw [← hspan, Submodule.map_span, Submodule.span_span_of_tower, ← Set.range_comp]
  rfl

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_map_toK_delSq_eq_nablaSq (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : _root_.Formalism.BasicNotions.DomWeight n) :
    Submodule.span K (Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.delSq (𝓞 K) n μ) : Set _) =
      _root_.Formalism.BasicNotions.nablaSq K n μ := by
  rw [_root_.Formalism.L2.Col.nablaSq_eq_delSq]
  unfold _root_.Formalism.BasicNotions.delSq _root_.Formalism.GradedWeylDivisibility.weyl
  rw [Submodule.map_span, Submodule.span_span_of_tower, ← Set.range_comp]
  congr 2
  funext w
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [← _root_.Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, _root_.Formalism.GradedWeylDivisibility.lclosedeq_hw_map]


open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
theorem _root_.GlobalTheory.StdLatSpan.std_fg_span : ∀ (K : Type) [Field K] [NumberField K] (ι : Type)
    [Fintype ι] (n : ℕ) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n),
    (_root_.Formalism.L2.DIV.nabStd K lam).FG ∧ (_root_.Formalism.L2.DIV.delStd K lam).FG ∧
      Submodule.span K (_root_.Formalism.L2.DIV.nabStd K lam : Set (_root_.Formalism.L2.DIV.Pol K ι n)) = _root_.Formalism.L2.DIV.VV K lam ∧
      Submodule.span K (_root_.Formalism.L2.DIV.delStd K lam : Set (_root_.Formalism.L2.DIV.Pol K ι n)) = _root_.Formalism.L2.DIV.VV K lam := by
  intro K _ _ ι _ n lam
  have hnab := nabStd_fg' K ι n lam
  refine ⟨hnab, hnab.of_le (_root_.Formalism.L2.DIV.delStd_le_nabStd K lam), ?_, ?_⟩
  · unfold _root_.Formalism.L2.DIV.nabStd _root_.Formalism.L2.DIV.VV
    rw [span_tensorLat_eq_prod_map_span, ← Submodule.span_eq (_root_.Formalism.GradedWeylDivisibility.tensorLat K K _), span_tensorLat_eq_prod_map_span]
    simp only [span_map_toK_nablaSq_eq_nablaSq, Submodule.span_eq]
  · unfold _root_.Formalism.L2.DIV.delStd _root_.Formalism.L2.DIV.VV
    rw [span_tensorLat_eq_prod_map_span, ← Submodule.span_eq (_root_.Formalism.GradedWeylDivisibility.tensorLat K K _), span_tensorLat_eq_prod_map_span]
    simp only [span_map_toK_delSq_eq_nablaSq, Submodule.span_eq]

end GlobalTheory.StdLatSpan
end
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.ExtremalNorm

theorem weight_colW_apply {r n : ℕ} (mo : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) mo t = ∑ a, mo (a, t) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem fockS_extremal_eq_nat : ∀ (n : ℕ) (lam : DomWeight n) (R : ℕ), (∀ i, lam.natW i ≤ R) → ∃ s : ℕ, 0 < s ∧ s ≤ (n.factorial) ^ (2 * R) * (R.factorial) ^ n ∧ ∀ (K : Type) [Field K] [StarRing K] [CharZero K], fockS (extremal K n lam) (extremal K n lam) = (s : K) := by
  intro n lam R hR
  have hanti := Formalism.L2.DIV.natW_antitone lam
  set f : MvPolynomial (Fin n × Fin n) ℤ := extremal ℤ n lam with hf
  have hmem : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) f lam.natW :=
    (Formalism.GradedWeylDivisibility.hwMem ℤ n n le_rfl _ hanti).1
  have hne : f ≠ 0 := Formalism.GradedWeylDivisibility.hwNe ℤ n n le_rfl _
  have hl1 : ∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs ≤ (n.factorial) ^ R :=
    GlobalTheory.IntMvPolynomialCoeffAbsSum.highestWeightVector_coeff_natAbs_sum_le_factorial_pow n lam.natW R hanti hR
  refine ⟨∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs ^ 2 * mfact mo, ?_, ?_, ?_⟩
  · refine Finset.sum_pos (fun mo hmo => ?_) (support_nonempty.mpr hne)
    have h1 : 0 < (AddMonoidAlgebra.coeff f mo).natAbs := Int.natAbs_pos.mpr (mem_support_iff.mp hmo)
    have h2 : 0 < mfact mo := Finset.prod_pos fun k _ => Nat.factorial_pos _
    positivity
  · calc ∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs ^ 2 * mfact mo
        ≤ ∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs * (n.factorial ^ R * R.factorial ^ n) := by
          refine Finset.sum_le_sum fun mo hmo => ?_
          have h1 : (AddMonoidAlgebra.coeff f mo).natAbs ≤ n.factorial ^ R :=
            (Finset.single_le_sum (f := fun mo => (AddMonoidAlgebra.coeff f mo).natAbs)
              (fun _ _ => Nat.zero_le _) hmo).trans hl1
          have h2 : mfact mo ≤ R.factorial ^ n := by
            refine GlobalTheory.TestLat.mfact_le_factorial_pow n lam.natW R hR mo fun t => ?_
            rw [← weight_colW_apply, hmem (mem_support_iff.mp hmo)]
          rw [pow_two, mul_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
      _ ≤ n.factorial ^ R * (n.factorial ^ R * R.factorial ^ n) := by
          rw [← Finset.sum_mul]
          exact Nat.mul_le_mul_right _ hl1
      _ = _ := by rw [two_mul, pow_add, mul_assoc]
  · intro K _ _ _
    have hinj : Function.Injective (Int.castRingHom K) := Int.cast_injective
    rw [← Formalism.L2.DIV.map_extremal (Int.castRingHom K) n lam, ← hf]
    unfold fockS
    rw [support_map_of_injective _ hinj, Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h : (((AddMonoidAlgebra.coeff f m).natAbs ^ 2 : ℕ) : K) = ((AddMonoidAlgebra.coeff f m : ℤ) : K) * ((AddMonoidAlgebra.coeff f m : ℤ) : K) := by
      rw [← Int.cast_natCast, Nat.cast_pow, Int.natAbs_sq, pow_two, Int.cast_mul]
    rw [Nat.cast_mul, h]
    simp only [coeff_map, eq_intCast, star_intCast]

end GlobalTheory.ExtremalNorm
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.polyAction_mem_locP_delStd_of_isBasisAt : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  first | exact @GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd | exact GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd | (intros; apply GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd <;> assumption)
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.lattice_extension_along_field_embedding_duals : TauLatLattice ∧ TauLatDual ∧ RoundLat := by
  first | exact @GlobalTheory.TauLat.tauLat_lattice_dual_round | exact GlobalTheory.TauLat.tauLat_lattice_dual_round | (intros; apply GlobalTheory.TauLat.tauLat_lattice_dual_round <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchMean

theorem sum_comp_algHom (K M : Type) [Field K] [Field M] [Algebra ℚ K] [Algebra ℚ M] [Algebra K M]
    [IsScalarTower ℚ K M] [FiniteDimensional ℚ K] [FiniteDimensional ℚ M]
    (F : (K →ₐ[ℚ] ℂ) → ℝ) :
    ∑ ρ : M →ₐ[ℚ] ℂ, F (ρ.comp (IsScalarTower.toAlgHom ℚ K M)) =
      (Module.finrank K M : ℝ) * ∑ φ : K →ₐ[ℚ] ℂ, F φ := by
  haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  haveI : CharZero K := algebraRat.charZero K
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun ρ : M →ₐ[ℚ] ℂ => ρ.comp (IsScalarTower.toAlgHom ℚ K M)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F φ)
    (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]
  congr 2
  letI : Algebra K ℂ := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq fun q => (φ.commutes q).symm
  rw [← AlgHom.card K M ℂ, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun ψ _ => ψ.restrictScalars ℚ) ?_ ?_ ?_
  · intro ψ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext a
    exact ψ.commutes a
  · intro a _ b _ h
    exact AlgHom.restrictScalars_injective ℚ h
  · intro ρ hρ
    have h := (Finset.mem_filter.1 hρ).2
    exact ⟨{ ρ.toRingHom with commutes' := fun a => DFunLike.congr_fun h a },
      Finset.mem_univ _, rfl⟩

theorem sum_algHom_eq (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (f : InfinitePlace K → ℝ) :
    ∑ φ : K →ₐ[ℚ] ℂ, f (InfinitePlace.mk φ.toRingHom) = 2 * ∑ v, f v := by
  have h1 : ∑ φ : K →ₐ[ℚ] ℂ, f (InfinitePlace.mk φ.toRingHom)
      = ∑ φ : K →+* ℂ, f (InfinitePlace.mk φ) :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ fun _ => rfl
  rw [h1, ← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun φ : K →+* ℂ => InfinitePlace.mk φ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f v)
    (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]
  congr 1
  have := InfinitePlace.card_filter_mk_eq v
  rw [IsTotallyComplex.mult_eq] at this
  exact_mod_cast this

theorem posLog_sum_le {ι : Type} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) (a b : ι → ℂ) :
    Real.posLog ‖∑ i, (w i : ℂ) * (a i * b i)‖ ≤
      (Real.posLog (∑ i, (w i : ℝ) * ‖a i‖ ^ 2) + Real.posLog (∑ i, (w i : ℝ) * ‖b i‖ ^ 2)) / 2 := by
  have hw' : ∀ i, (0 : ℝ) ≤ w i := fun i => by exact_mod_cast hw i
  have h1 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ≤
      ∑ i, (Real.sqrt (w i) * ‖a i‖) * (Real.sqrt (w i) * ‖b i‖) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    have h := Real.mul_self_sqrt (hw' i)
    rw [norm_mul, norm_mul, Complex.norm_ratCast, abs_of_nonneg (hw' i)]
    linear_combination (-(‖a i‖ * ‖b i‖)) * h
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i) * ‖a i‖) (fun i => Real.sqrt (w i) * ‖b i‖)
  simp only [mul_pow, Real.sq_sqrt (hw' _)] at h2
  have h3 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ^ 2 ≤
      (∑ i, (w i : ℝ) * ‖a i‖ ^ 2) * ∑ i, (w i : ℝ) * ‖b i‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have h4 := (Real.posLog_le_posLog (le_trans (by norm_num) (sq_nonneg _)) h3).trans Real.posLog_mul
  rw [Real.posLog_pow] at h4
  push_cast at h4
  linarith

theorem meanInf_posLog_le :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) (x : K) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] [IsGalois ℚ M] (ι : Type) [Fintype ι] (w : ι → ℚ) (z : ι → M), (∀ a, σ a ∈ M) → (∀ i, 0 ≤ w i) → σ x = ∑ i, (w i : ℂ) * ((z i : ℂ) * starRingEnd ℂ (z i : ℂ)) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (∑ i, (w i : ℝ) * ‖ρ (z i)‖ ^ 2)) / (Module.finrank ℚ M : ℝ) := by
  intro K _ _ _ σ x M _ _ ι _ w z hσ hw hx
  let σ' : K →+* M := σ.codRestrict M hσ
  letI : Algebra K M := σ'.toAlgebra
  haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let j : M →ₐ[ℚ] ℂ := ((starRingEnd ℂ).toRatAlgHom).comp M.val
  have hj : ∀ y : M, starRingEnd ℂ (y : ℂ) ∈ M := fun y => by
    have : j y ∈ j.fieldRange := ⟨y, rfl⟩
    exact (@AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ M (IsGalois.to_normal (F := ℚ) (E := M)) j).le this
  let c : M →ₐ[ℚ] M := (j.toRingHom.codRestrict M hj).toRatAlgHom
  have hc : ∀ y : M, (c y : ℂ) = starRingEnd ℂ (y : ℂ) := fun _ => rfl
  have hcc : ∀ y, c (c y) = y := fun y => Subtype.ext (by rw [hc, hc, Complex.conj_conj])
  have hxM : algebraMap K M x = ∑ i, (w i : M) * (z i * c (z i)) := by
    apply Subtype.ext
    change σ x = M.val _

    rw [hx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_ratCast]
    rfl
  set A : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => Real.posLog (∑ i, (w i : ℝ) * ‖ρ (z i)‖ ^ 2) with hA
  have hinv : Function.Involutive (fun ρ : M →ₐ[ℚ] ℂ => ρ.comp c) := fun ρ => by
    ext y
    simp [hcc]
  have hsum : ∑ ρ : M →ₐ[ℚ] ℂ, A (ρ.comp c) = ∑ ρ, A ρ :=
    Fintype.sum_equiv hinv.toPerm _ _ fun _ => rfl
  have h1 := sum_comp_algHom K M (fun φ => Real.posLog ‖φ x‖)
  have h2 := sum_algHom_eq K (fun v => Real.posLog ‖v.embedding x‖)
  have h3 : ∑ φ : K →ₐ[ℚ] ℂ, Real.posLog ‖φ x‖ =
      2 * ∑ v : InfinitePlace K, Real.posLog ‖v.embedding x‖ := by
    rw [← h2]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
    rfl
  have h4 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog ‖(ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x‖
      ≤ ∑ ρ, A ρ := by
    calc _ ≤ ∑ ρ : M →ₐ[ℚ] ℂ, (A ρ + A (ρ.comp c)) / 2 := by
          refine Finset.sum_le_sum fun ρ _ => ?_
          have : (ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x
              = ∑ i, (w i : ℂ) * (ρ (z i) * ρ (c (z i))) := by
            change ρ (algebraMap K M x) = _

            rw [hxM, map_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_mul, map_mul, map_ratCast]
          rw [this]
          exact posLog_sum_le w hw _ _
      _ = ∑ ρ, A ρ := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, hsum]; ring
  rw [h1, h3] at h4
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hM : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  have ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K M
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [le_div_iff₀ hM, ← ht]
  refine le_trans (le_of_eq ?_) h4
  field_simp

end GlobalTheory.ArchMean
end
