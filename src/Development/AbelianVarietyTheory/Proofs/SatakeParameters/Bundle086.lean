module

public import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle002
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.Bundle008
public import Formalism.LocalRingCardinality.Bundle003
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

namespace GlobalTheory.GO.SplitGlue

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}


omit [StarRing E] in
theorem exists_smul_le {N N' : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsFullLattice E N)
    (hN' : Submodule.IsLattice E N') : ∃ a : 𝓞 E, a ≠ 0 ∧ ∀ x ∈ N', a • x ∈ N := by
  classical
  have h0 : ∀ x : Sp E n, ∃ a : 𝓞 E, a ≠ 0 ∧ a • x ∈ N := by
    intro x
    have hx : x ∈ Submodule.span E (N : Set (Sp E n)) := Submodule.IsFullLattice.span_eq_top (self := hN) ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (N : Set (Sp E n)) x hx
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
  obtain ⟨s, rfl⟩ := hN'.fg
  choose a ha0 ha using h0
  refine ⟨∏ y ∈ s, a y, Finset.prod_ne_zero_iff.mpr fun y _ => ha0 y, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ hy, mul_smul]
    exact N.smul_mem _ (ha y)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact N.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact N.smul_mem _ hy


omit [StarRing E] in
theorem mem_of_forall (N : Submodule (𝓞 E) (Sp E n)) {x : Sp E n}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), ∃ s ∉ w.asIdeal, s • x ∈ N) : x ∈ N := by
  by_contra hx
  have hI : N.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x) ≠ ⊤ := by
    intro h1
    have : (1 : 𝓞 E) ∈ N.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x) := h1 ▸ Submodule.mem_top
    exact hx (by simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, hm0⟩
  exact hs (hle (by simpa using hsx))


omit [StarRing E] in
theorem eq_of_sameAt {N N' : Submodule (𝓞 E) (Sp E n)} (h : ∀ w, SameAt w N N') : N = N' := by
  apply le_antisymm
  · intro x hx
    refine mem_of_forall N' fun w => ?_
    obtain ⟨_, _, a', ha', _, h2⟩ := h w
    exact ⟨a', ha', h2 x hx⟩
  · intro x hx
    refine mem_of_forall N fun w => ?_
    obtain ⟨a, ha, _, _, h1, _⟩ := h w
    exact ⟨a, ha, h1 x hx⟩

omit [NumberField E] [StarRing E] in
theorem sameAt_symm {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt Q N' N := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  exact ⟨a', ha', a, ha, h2, h1⟩

omit [NumberField E] [StarRing E] in
theorem sameAt_trans {Q : HeightOneSpectrum (𝓞 E)} {N N' N'' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (h' : SameAt Q N' N'') : SameAt Q N N'' := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  obtain ⟨b, hb, b', hb', h3, h4⟩ := h'
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]; exact h1 _ (h3 x hx)
  · rw [mul_smul]; exact h4 _ (h2 x hx)

theorem conjP_conjP (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext r
  rw [mem_conjP, mem_conjP, cO_cO]

theorem sameAt_dual {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt (conjPrime₂ Q) (dual (hStd E n) N) (dual (hStd E n) N') := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  refine ⟨cO E a', by rwa [mem_conjP, cO_cO], cO E a, by rwa [mem_conjP, cO_cO], fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_dual] at hx ⊢
    intro y hy
    rw [← hStd_osmul_left]
    exact hx _ (h2 y hy)
  · rw [mem_dual] at hx ⊢
    intro y hy
    rw [← hStd_osmul_left]
    exact hx _ (h1 y hy)

theorem exists_glue {L L' : Submodule (𝓞 E) (Sp E n)} (hL : Submodule.IsFullLattice E L) (hL' : Submodule.IsFullLattice E L')
    (P : HeightOneSpectrum (𝓞 E)) : ∃ L'' : Submodule (𝓞 E) (Sp E n), Submodule.IsFullLattice E L'' ∧ SameAt P L' L'' ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q L L'' := by
  classical
  obtain ⟨a, ha0, ha⟩ := exists_smul_le hL hL'.toIsLattice
  obtain ⟨b, hb0, hb⟩ := exists_smul_le hL' hL.toIsLattice
  have hI : Ideal.span {a * b} ≠ ⊥ := by simpa using ⟨ha0, hb0⟩
  obtain ⟨J, hJ, hdJ⟩ := Ideal.eq_prime_pow_mul_coprime hI P.asIdeal (hpm := P.isMaximal)
  generalize Multiset.count P.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a * b})) = k at hdJ
  have hdvd : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∃ c, r * s = c * (a * b) := by
    intro r hr s hs
    have := Ideal.mul_mem_mul hr hs
    rw [← hdJ, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  have h1 : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∀ x ∈ L, (r * s) • x ∈ L' := by
    intro r hr s hs x hx
    obtain ⟨c, hc⟩ := hdvd r hr s hs
    rw [hc, ← mul_assoc, mul_smul]
    exact L'.smul_mem _ (hb x hx)
  have h2 : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∀ x ∈ L', (r * s) • x ∈ L := by
    intro r hr s hs x hx
    obtain ⟨c, hc⟩ := hdvd r hr s hs
    rw [hc, mul_comm a b, ← mul_assoc, mul_smul]
    exact L.smul_mem _ (ha x hx)
  obtain ⟨s, hsJ, hsP⟩ : ∃ s ∈ J, s ∉ P.asIdeal := by
    by_contra H
    push Not at H
    have : P.asIdeal ⊔ J ≤ P.asIdeal := sup_le le_rfl H
    rw [hJ] at this
    exact P.isPrime.ne_top (top_le_iff.1 this)
  have hs0 : s ≠ 0 := by rintro rfl; exact hsP P.asIdeal.zero_mem
  let L'' : Submodule (𝓞 E) (Sp E n) := J • L' ⊔ (P.asIdeal ^ k) • L
  have hA : ∀ x ∈ L', s • x ∈ L'' := fun x hx => Submodule.mem_sup_left (Submodule.smul_mem_smul hsJ hx)
  have hB : ∀ x ∈ L'', s • x ∈ L' := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine L'.add_mem (L'.smul_mem _ (Submodule.smul_le_right hy)) ?_
    refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [← mul_smul, mul_comm]; exact h1 r hr s hsJ u hu
    · rw [smul_add]; exact L'.add_mem hu hv
  refine ⟨L'', ?_, ⟨s, hsP, s, hsP, hB, hA⟩, fun Q hQ => ?_⟩
  · have hsup : Submodule.IsLattice E (L' ⊔ L) :=
      ⟨hL'.fg.sup hL.fg, by
        intro s hs hli
        exact (LinearIndependent.iff_fractionRing _ _).mp hli⟩
    let : Submodule.IsLattice E L'' := lattice_of_smul hL'.toIsLattice hsup (sup_le_sup Submodule.smul_le_right Submodule.smul_le_right) hs0 hA
    refine { span_eq_top := ?_ }
    apply top_unique
    intro x hx
    have hx' : x ∈ Submodule.span E (L' : Set (Sp E n)) :=
      Submodule.IsFullLattice.span_eq_top (self := hL') ▸ Submodule.mem_top
    have hspan : ∀ y ∈ L', y ∈ Submodule.span E (L'' : Set (Sp E n)) := by
      intro y hy
      have hsE : (algebraMap (𝓞 E) E s) ≠ 0 :=
        fun h => hs0 ((IsFractionRing.injective (𝓞 E) E) (by simpa using h))
      have hy' : s • y ∈ Submodule.span E (L'' : Set (Sp E n)) := Submodule.subset_span (hA y hy)
      rw [← IsScalarTower.algebraMap_smul E s y] at hy'
      have := (Submodule.span E (L'' : Set (Sp E n))).smul_mem (algebraMap (𝓞 E) E s)⁻¹ hy'
      rw [← mul_smul, inv_mul_cancel₀ hsE, one_smul] at this
      exact this
    exact (Submodule.span_le.mpr hspan) hx' 
  · obtain ⟨t, htP, htQ⟩ := exists_mem_notMem hQ.symm
    have ht : t ^ k ∈ P.asIdeal ^ k := Ideal.pow_mem_pow htP k
    have ht' : t ^ k ∉ Q.asIdeal := fun h => htQ (Q.isPrime.mem_of_pow_mem k h)
    refine ⟨t ^ k, ht', t ^ k, ht', fun x hx => ?_, fun x hx => Submodule.mem_sup_right (Submodule.smul_mem_smul ht hx)⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine L.add_mem ?_ (L.smul_mem _ (Submodule.smul_le_right hz))
    refine Submodule.smul_induction_on hy (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [← mul_smul]; exact h2 _ ht r hr u hu
    · rw [smul_add]; exact L.add_mem hu hv

theorem exists_selfDual_prescribed (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
    (N M : Submodule (𝓞 E) (Sp E n)) (Q : HeightOneSpectrum (𝓞 E)) (hQ : conjPrime₂ Q ≠ Q) (hN : Submodule.IsFullLattice E N)
    (hu : IsUnimodular (hStd E n) N) (hM : Submodule.IsFullLattice E M) :
    ∃ N' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N' ∧ IsUnimodular (hStd E n) N' ∧
      localization₂ Q.asIdeal N' = localization₂ Q.asIdeal M ∧
      ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q → Q' ≠ conjPrime₂ Q → localization₂ Q'.asIdeal N' = localization₂ Q'.asIdeal N := by
  have hsymm : (hStd E n).IsSymm := ⟨fun x y => by
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, starRingEnd_apply, star_star]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩
  have hdual := Formalism.HermitianLatticesTheory.dualLattice
    (𝓞 E) E (Sp E n) (hStd E n) hsymm hStd_nondeg star_range M hM
  obtain ⟨L, hL, hLQ, hLo⟩ := exists_glue hN hM Q
  obtain ⟨N', hN', hc, ho⟩ := exists_glue hL hdual.1 (conjPrime₂ Q)
  have h1 : SameAt Q M N' := sameAt_trans hLQ (ho Q hQ.symm)
  have h2 : ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q → Q' ≠ conjPrime₂ Q → SameAt Q' N N' :=
    fun Q' a b => sameAt_trans (hLo Q' a) (ho Q' b)
  refine ⟨N', hN'.toIsLattice, ?_, h1.localization_eq, fun Q' a b => (h2 Q' a b).localization_eq⟩
  refine eq_of_sameAt fun w => ?_
  by_cases hw : w = Q
  · subst hw
    have := sameAt_dual hc
    rw [conjP_conjP, hdual.2.1] at this
    exact sameAt_trans (sameAt_symm this) h1
  by_cases hw' : w = conjPrime₂ Q
  · subst hw'
    exact sameAt_trans (sameAt_symm (sameAt_dual h1)) hc
  have := sameAt_dual (h2 (conjPrime₂ w) (fun h => hw' (by rw [← h, conjP_conjP]))
    (fun h => hw (by rw [← conjP_conjP w, h, conjP_conjP])))
  rw [conjP_conjP, show dual (hStd E n) N = N from hu] at this
  exact sameAt_trans (sameAt_symm this) (h2 w hw hw')

end GlobalTheory.GO.SplitGlue
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

noncomputable section

namespace GlobalTheory.GO.UniExt

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

private theorem mem_localization_iff_exists_smul_mem {N : Submodule (𝓞 E) (Sp E n)} (Q : HeightOneSpectrum (𝓞 E))
    (x : Sp E n) : x ∈ localization₂ Q.asIdeal N ↔ ∃ s ∉ Q.asIdeal, s • x ∈ N := by
  unfold localization₂ locS
  exact Iff.rfl

private theorem mem_iff_hStd_integral_of_isUnimodular {N : Submodule (𝓞 E) (Sp E n)}
    (hu : IsUnimodular (hStd E n) N) (x : Sp E n) :
    x ∈ N ↔ ∀ y ∈ N, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = hStd E n y x := by
  unfold IsUnimodular dual at hu
  conv_lhs => rw [← hu]
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]

private theorem hStd_smul_left (a : 𝓞 E) (y z : Sp E n) :
    hStd E n (a • y) z = algebraMap (𝓞 E) E (cO E a) * hStd E n y z := by
  rw [← algebraMap_smul E a y, LinearMap.map_smulₛₗ₂, smul_eq_mul]
  rfl

private theorem hStd_smul_right (a : 𝓞 E) (y z : Sp E n) :
    hStd E n y (a • z) = algebraMap (𝓞 E) E a * hStd E n y z := by
  rw [← algebraMap_smul E a z, map_smul, smul_eq_mul]

private theorem cO_mem_conjP_iff (P : HeightOneSpectrum (𝓞 E)) (t : 𝓞 E) :
    cO E t ∈ (conjPrime₂ P).asIdeal ↔ t ∈ P.asIdeal := by
  unfold conjPrime₂
  show cO E t ∈ Ideal.comap (cO E) P.asIdeal ↔ _
  rw [Ideal.mem_comap]
  have htt : cO E (cO E t) = t := RingOfIntegers.ext (star_star (t : E))
  rw [htt]

theorem mem_localization_conj_iff {N : Submodule (𝓞 E) (Sp E n)} (hl : N.FG) (hu : IsUnimodular (hStd E n) N)
    (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ localization₂ (conjPrime₂ P).asIdeal N ↔ ∀ y ∈ localization₂ P.asIdeal N, IntAt (conjPrime₂ P) (hStd E n y x) := by
  rw [mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, hsx⟩ y hy
    obtain ⟨t, ht, hty⟩ := (mem_localization_iff_exists_smul_mem P y).1 hy
    obtain ⟨r, hr⟩ := (mem_iff_hStd_integral_of_isUnimodular hu (s • x)).1 hsx (t • y) hty
    unfold IntAt
    refine ⟨r, cO E t * s, ?_, ?_⟩
    · intro hmem
      rcases (conjPrime₂ P).isPrime.mem_or_mem hmem with h | h
      · exact ht ((cO_mem_conjP_iff P t).1 h)
      · exact hs h
    · rw [hr, hStd_smul_left, hStd_smul_right, map_mul]
      ring
  · intro H
    classical
    obtain ⟨S, hS⟩ := hl
    have hloc : ∀ y ∈ S, ∃ s : 𝓞 E, s ∉ (conjPrime₂ P).asIdeal ∧
        ∃ r : 𝓞 E, algebraMap (𝓞 E) E s * hStd E n y x = algebraMap (𝓞 E) E r := by
      intro y hy
      have hyN : y ∈ N := hS ▸ Submodule.subset_span hy
      have hyl : y ∈ localization₂ P.asIdeal N :=
        (mem_localization_iff_exists_smul_mem P y).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by rwa [one_smul]⟩
      have hint := H y hyl
      unfold IntAt at hint
      obtain ⟨r, s, hs, h⟩ := hint
      exact ⟨s, hs, r, h⟩
    choose! u hu0 w hw using hloc
    refine ⟨∏ y ∈ S, u y, ?_, ?_⟩
    · intro hmem
      obtain ⟨y, hy, hyu⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (conjPrime₂ P).isPrime)).1 hmem
      exact hu0 y hy hyu
    · rw [mem_iff_hStd_integral_of_isUnimodular hu]
      intro y hy
      rw [← hS] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        refine ⟨(∏ y ∈ S.erase z, u y) * w z, ?_⟩
        rw [hStd_smul_right, ← Finset.mul_prod_erase S u hz, map_mul, map_mul, ← hw z hz]
        ring
      | zero => exact ⟨0, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨ra, hra⟩ := ha
        obtain ⟨rb, hrb⟩ := hb
        exact ⟨ra + rb, by rw [map_add (f := _), hra, hrb, map_add (f := _), LinearMap.add_apply]⟩
      | smul a z _ hz =>
        obtain ⟨rz, hrz⟩ := hz
        exact ⟨cO E a * rz, by rw [hStd_smul_left, map_mul, hrz]⟩

theorem conjP_involutive (Q : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ Q) = Q := by
  unfold conjPrime₂
  apply HeightOneSpectrum.ext
  simp only [Ideal.comap_comap]
  unfold cO
  have hid : (RingOfIntegers.mapRingHom (starRingEnd E)).comp
      (RingOfIntegers.mapRingHom (starRingEnd E)) = RingHom.id (𝓞 E) :=
    RingHom.ext fun x => RingOfIntegers.ext (star_star (x : E))
  rw [hid, Ideal.comap_id]

theorem le_of_forall_localized_eq {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N') : N ≤ N' := by
  intro x hx
  by_contra hnx
  let I : Ideal (𝓞 E) := N'.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x)
  have hI : I ≠ ⊤ := by
    intro htop
    apply hnx
    have h1 : (1 : 𝓞 E) ∈ I := htop ▸ Submodule.mem_top
    simpa [I] using h1
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hMb : M ≠ ⊥ := by
    rintro rfl
    exact RingOfIntegers.not_isField (K := E) (Ring.isField_iff_maximal_bot.2 hM)
  let Q : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hMb⟩
  have hxQ : x ∈ localization₂ Q.asIdeal N' := by
    rw [← h Q]
    exact (mem_localization_iff_exists_smul_mem Q x).2 ⟨1, (Ideal.ne_top_iff_one _).1 hM.ne_top, by rwa [one_smul]⟩
  obtain ⟨s, hs, hsx⟩ := (mem_localization_iff_exists_smul_mem Q x).1 hxQ
  exact hs (hIM (by simpa [I] using hsx))

theorem unimodular_ext : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N N' : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E N → IsUnimodular (hStd E n) N → Submodule.IsLattice E N' → IsUnimodular (hStd E n) N' → (∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' → localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N') ∧ ((∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' ∨ localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N') → N = N') := by
  intro E _ _ _ n N N' hl hu hl' hu'
  have part1 : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' →
      localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N' := by
    intro Q hQ
    ext x
    rw [mem_localization_conj_iff hl.fg hu Q x, mem_localization_conj_iff hl'.fg hu' Q x, hQ]
  refine ⟨part1, fun hor => ?_⟩
  have hall : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' := by
    intro Q
    rcases hor Q with h | h
    · exact h
    · have h' := part1 (conjPrime₂ Q) h
      rwa [conjP_involutive] at h'
  exact le_antisymm (le_of_forall_localized_eq hall) (le_of_forall_localized_eq fun Q => (hall Q).symm)

end GlobalTheory.GO.UniExt
end
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem use₂ {Kf K ι : Type} [Field Kf] [Field K] [Fintype ι] {n : ℕ} (eK : K →+* Kf) (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map eK (actP lam B F) = actP lam (fun τ => Formalism.UG.bc eK (B τ)) (MvPolynomial.map eK F) := by
  have h1 : (MvPolynomial.map eK).comp (trAct B).toRingHom =
      (trAct (fun τ => Formalism.UG.bc eK (B τ))).toRingHom.comp (MvPolynomial.map eK) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, blockAct_X, bc_coe]
  have h2 : MvPolynomial.map eK (trAct B F) = trAct (fun τ => Formalism.UG.bc eK (B τ)) (MvPolynomial.map eK F) :=
    congrArg (fun φ : Pol K ι n →+* Pol Kf ι n => φ F) h1
  have h3 : eK (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc eK (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h2, h3]

end GlobalTheory.ValCmp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.absIrrDistinct_of_isSS_absIrr_mapRep_nonIso : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → (∀ W, IsIrrSub ρ W → AbsIrrSub ρ W) → (∀ W₁ W₂, IsIrrSub (mapRep f ρ) W₁ → IsIrrSub (mapRep f ρ) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep f ρ) W₁ W₂) → AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ)) := by
  first | exact @GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct | exact GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct | (intros; apply GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) r) := by
  first | exact @GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois | exact GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois | (intros; apply GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UnUnitCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

section Units

variable {l : ℕ} [Fact l.Prime] {lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l]}

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem emb_mem {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (x : K) : φ x ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (φ : H.E →+* ℂ) {N : ℕ} (g : GL (Fin N) (Ad H))

end Units

section Rescale

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

end Rescale

section Ties

variable {D : D7} {Dx : DivX D} {Tw : TwForms D} {C : CharFrame D} {nch : NChoice D}

variable (E : KerEnt D Dx Tw) (Tp : TupTied D C nch) (g : ∀ u μ, Reps D u μ) (fr : ∀ u μ, Frames D u μ)

end Ties

end GlobalTheory.UnUnitCmp
end
end
