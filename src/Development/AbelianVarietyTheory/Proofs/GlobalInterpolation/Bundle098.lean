module

public import Formalism.GradedWeylDivisibility.StatementA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle087
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rowDiv_raise_eq_zero (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) k) (hf : f ∈ dualWeyl k N N ν)
    (hwt : IsWeightedHomogeneous (rowW N N) f ν) (a b : Fin N) (hab : a < b) (j : ℕ) (hj : 1 ≤ j) :
    rowDiv k a b j f = 0 := by
  classical
  by_contra hne
  have hg : rowDiv k a b j f ∈ dualWeyl k N N ν := rowDivStable k N N ν a b j f hf
  have hZ : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) f (fun i => (ν i : ℤ)) := by
    intro d hd
    funext i
    rw [GlobalTheory.LvT.KerLat.weight_rowZ, hwt hd]
  have hsh := GlobalTheory.LvT.KerLat.rowDiv_shift k (fun i => (ν i : ℤ)) a b j f hZ
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have e := hsh hm
  have dom := (GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ hg m (mem_support_iff.mpr hm)).1 (a.val + 1)
  have hrow : ∀ i, ((rowDeg m i : ℕ) : ℤ) = (ν i : ℤ) + (j : ℤ) * ((Pi.single a (1:ℤ) : Fin N → ℤ) i - (Pi.single b (1:ℤ) : Fin N → ℤ) i) := by
    intro i
    have := congrFun e i
    rw [GlobalTheory.LvT.KerLat.weight_rowZ, GlobalTheory.LvT.KerLat.weight_rowW] at this
    rw [this]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hcast : ((∑ i : Fin N with i.val < a.val + 1, rowDeg m i : ℕ) : ℤ) =
      ((∑ i : Fin N with i.val < a.val + 1, ν i : ℕ) : ℤ) + j := by
    push_cast
    simp only [hrow]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    have ha : (∑ i : Fin N with i.val < a.val + 1, (Pi.single a (1:ℤ) : Fin N → ℤ) i) = 1 := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro i _ hi; simp [Pi.single_apply, hi]
      · intro h; simp at h
    have hb : (∑ i : Fin N with i.val < a.val + 1, (Pi.single b (1:ℤ) : Fin N → ℤ) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have : i ≠ b := by
        intro h; subst h
        simp at hi
        have : a.val < i.val := hab
        omega
      simp [Pi.single_apply, this]
    rw [ha, hb]; ring
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have : ((∑ i : Fin N with i.val < a.val + 1, rowDeg m i : ℕ) : ℤ) ≤
      ((∑ i : Fin N with i.val < a.val + 1, ν i : ℕ) : ℤ) := by exact_mod_cast dom
  omega

theorem hw_line_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ f ∈ dualWeyl k N N ν,
    IsWeightedHomogeneous (rowW N N) f ν → ∃ c : k, f = c • hw k le_rfl ν := by
  intro k _ N ν hν f hf hwt
  classical
  let K := AlgebraicClosure k
  let φ : k →+* K := algebraMap k K
  have hgK : map φ f ∈ dualWeyl K N N ν := dualWeylMap k K φ N N ν f hf
  have hrK : ∀ a b : Fin N, a < b → ∀ j : ℕ, 1 ≤ j → rowDiv K a b j (map φ f) = 0 := by
    intro a b hab j hj
    rw [lclosedeq_rowDiv_map, rowDiv_raise_eq_zero k N ν f hf hwt a b hab j hj, map_zero]
  obtain ⟨c, hc⟩ := hwLine K N N le_rfl ν hν (map φ f) hgK hrK
  obtain ⟨m, hm⟩ := ne_zero_iff.mp (hwNe k N N le_rfl ν)
  refine ⟨AddMonoidAlgebra.coeff f m / AddMonoidAlgebra.coeff (hw k le_rfl ν) m, ?_⟩
  have hcm := congrArg (AddMonoidAlgebra.coeff · m) hc
  rw [coeff_map, MvPolynomial.coeff_smul, ← lclosedeq_hw_map φ, coeff_map, smul_eq_mul] at hcm
  have hφ : φ (AddMonoidAlgebra.coeff (hw k le_rfl ν) m) ≠ 0 := (map_ne_zero φ).mpr hm
  have hcv : c = φ (AddMonoidAlgebra.coeff f m / AddMonoidAlgebra.coeff (hw k le_rfl ν) m) := by
    rw [map_div₀, hcm, mul_div_cancel_right₀ _ hφ]
  apply map_injective φ φ.injective
  rw [hc, hcv, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, lclosedeq_hw_map]

end GlobalTheory.Alc
end
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.ConjPlace

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_le_one_of_int {q : ℕ} [Fact q.Prime] {K : Type} [Field K] (j : K →+* ℂ_[q]) (y : 𝓞 K) :
    ‖j (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by convert map_isIntegral_int j (RingOfIntegers.isIntegral_coe y); exact Subsingleton.elim _ _)

theorem norm_intCast_eq (q : ℕ) [Fact q.Prime] (n : ℤ) : ‖((n : ℤ) : ℂ_[q])‖ = ‖((n : ℤ) : ℚ_[q])‖ := by
  have e : ((n : ℤ) : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] ((n : ℤ) : ℚ_[q]) := (map_intCast _ n).symm
  rw [e]
  exact PadicComplex.norm_extends' (p := q) _

theorem norm_intCast_lt_one_iff (q : ℕ) [Fact q.Prime] (n : ℤ) : ‖((n : ℤ) : ℂ_[q])‖ < 1 ↔ (q : ℤ) ∣ n := by
  rw [norm_intCast_eq]
  exact Padic.norm_intCast_lt_one_iff

theorem exists_sq_add (q : ℕ) [Fact q.Prime] (d : ℕ) (h : jacobiSym (-(d : ℤ)) q = 1) :
    ¬ (q : ℤ) ∣ d ∧ ∃ t : ℤ, (q : ℤ) ∣ t ^ 2 + d := by
  have hl : legendreSym q (-(d : ℤ)) = 1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact h
  have h0 : ((-(d : ℤ) : ℤ) : ZMod q) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff q _).2 h0] at hl
    exact zero_ne_one hl
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff q h0).1 hl
  refine ⟨?_, ⟨(r.val : ℤ), ?_⟩⟩
  · intro hd
    apply h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_neg.2 hd)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    rw [ZMod.natCast_zmod_val]
    linear_combination (-1 : ZMod q) * hr

theorem exists_small_not_conj {E : Type} [Field E] [CharZero E] (K : IntermediateField ℚ E) (φ : E →+* ℂ) (c : E ≃ₐ[ℚ] E)
    (d q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hj : jacobiSym (-(d : ℤ)) q = 1) (ι : ℂ ≃+* ℂ_[q])
    (s : K) (hs : s * s = -(d : K)) (hc : c (algebraMap K E s) = -algebraMap K E s) :
    ∃ y : 𝓞 K, ‖ι (φ ((y : K) : E))‖ < 1 ∧ 1 ≤ ‖ι (φ (c ((y : K) : E)))‖ := by
  obtain ⟨hnd, t, ht⟩ := exists_sq_add q d hj
  have hint : IsIntegral ℤ s :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, by simp [sq, hs]⟩
  let B : 𝓞 K := ⟨s, hint⟩
  let j : E →+* ℂ_[q] := ι.toRingHom.comp φ
  let jK : K →+* ℂ_[q] := j.comp (algebraMap K E)
  have hc' : c (s : E) = -(s : E) := hc
  have hsE : (s : E) * (s : E) = -(d : E) := by
    have := congrArg (fun x : K => (x : E)) hs
    simpa using this
  have hcoe : ∀ u : ℤ, (((B + u : 𝓞 K) : K) : E) = (s : E) + (u : E) := by
    intro u; push_cast; rfl
  have hle : ∀ y : 𝓞 K, ‖j ((y : K) : E)‖ ≤ 1 := fun y => norm_le_one_of_int jK y

  have hodd : ∀ u : ℤ, (q : ℤ) ∣ 2 * u → (q : ℤ) ∣ u := by
    intro u h
    rcases (Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)).dvd_or_dvd h with h2 | h2
    · exfalso
      have : q ∣ 2 := by exact_mod_cast h2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
    · exact h2
  have key : ∀ u : ℤ, (u = t ∨ u = -t) → ‖j (((B + u : 𝓞 K) : K) : E)‖ < 1 →
      1 ≤ ‖j (c (((B + u : 𝓞 K) : K) : E))‖ := by
    intro u hu h1
    by_contra h2
    push_neg at h2
    have e2 : c (((B + u : 𝓞 K) : K) : E) = -(s : E) + (u : E) := by
      rw [hcoe, map_add (f := _), map_intCast, hc']
    have hsum : j (((B + u : 𝓞 K) : K) : E) + j (c (((B + u : 𝓞 K) : K) : E)) = (((2 * u : ℤ)) : ℂ_[q]) := by
      rw [e2, hcoe, ← map_add (f := _)]
      have : (s : E) + (u : E) + (-(s : E) + (u : E)) = ((2 * u : ℤ) : E) := by push_cast; ring
      rw [this, map_intCast]
    have hlt : ‖(((2 * u : ℤ)) : ℂ_[q])‖ < 1 := by
      rw [← hsum]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)
    have hdu : (q : ℤ) ∣ u := hodd u ((norm_intCast_lt_one_iff q _).1 hlt)
    have hdt : (q : ℤ) ∣ t := by
      rcases hu with rfl | rfl
      · exact hdu
      · exact dvd_neg.1 hdu
    exact hnd ((dvd_add_right (dvd_pow hdt two_ne_zero)).1 ht)
  have hprod : j (((B + t : 𝓞 K) : K) : E) * j (((B + (-t : ℤ) : 𝓞 K) : K) : E) = ((-(t ^ 2 + d) : ℤ) : ℂ_[q]) := by
    rw [← map_mul, hcoe, hcoe]
    have : ((s : E) + (t : E)) * ((s : E) + ((-t : ℤ) : E)) = ((-(t ^ 2 + d) : ℤ) : E) := by
      push_cast
      linear_combination hsE
    rw [this, map_intCast]
  have hpl : ‖((-(t ^ 2 + d) : ℤ) : ℂ_[q])‖ < 1 := (norm_intCast_lt_one_iff q _).2 (dvd_neg.2 ht)
  by_cases h1 : ‖j (((B + t : 𝓞 K) : K) : E)‖ < 1
  · exact ⟨B + t, h1, key t (Or.inl rfl) h1⟩
  · push_neg at h1
    have h2 : ‖j (((B + (-t : ℤ) : 𝓞 K) : K) : E)‖ < 1 := by
      by_contra h2
      push_neg at h2
      rw [← hprod, norm_mul] at hpl
      nlinarith
    exact ⟨B + (-t : ℤ), h2, key (-t) (Or.inr rfl) h2⟩

theorem conj_place_ne : ∀ (D : D7) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 →
    ∀ ι : ℂ ≃+* ℂ_[q], ∃ y : 𝓞 D.host.K, ‖ι (D.host.φ₀ ((y : D.host.K) : D.host.E))‖ < 1 ∧
      1 ≤ ‖ι (D.host.φ₀ (D.host.conj ((y : D.host.K) : D.host.E)))‖ := by
  intro D q _ hq2 hj ι
  obtain ⟨s, h1, h2⟩ := sqrtInK D
  exact exists_small_not_conj D.host.K D.host.φ₀ D.host.conj D.host.d q hq2 hj ι s h1 h2

end GlobalTheory.ConjPlace
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.BadPrimes

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_cofactor {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    ∃ P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal := by
  obtain ⟨Q, Q', hQ, hm⟩ := hs
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, Ideal.map_le_iff_le_comap, ← hP]
  rcases P.isPrime.mul_le.1 hle with h | h
  · have : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
    subst this
    exact ⟨Q', hQ, hm⟩
  · have : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
    subst this
    exact ⟨Q, hQ.symm, hm.trans (mul_comm _ _)⟩

theorem absNorm_eq_of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v)
    (hq : (Ideal.absNorm v.asIdeal).Prime) {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨P', -, hm⟩ := exists_cofactor hs hP
  have h1 : Ideal.absNorm P.asIdeal * Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E), ← h2,
      Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E]
  have hP1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hP2 : Ideal.absNorm P'.asIdeal ≠ 1 := fun h => P'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  exact (((Nat.Prime.mul_eq_prime_sq_iff hq hP1 hP2).1 h1)).1

theorem notMem_sq_of_split {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) {a : 𝓞 F} (ha : a ∉ v.asIdeal ^ 2)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    algebraMap (𝓞 F) (𝓞 E) a ∉ P.asIdeal ^ 2 := by
  intro hm2
  obtain ⟨P', hne, hm⟩ := exists_cofactor hs hP
  have hav : a ∈ v.asIdeal := by
    rw [← hP, Ideal.under_def, Ideal.mem_comap]
    exact Ideal.pow_le_self two_ne_zero hm2
  obtain ⟨J, hJ⟩ := Ideal.dvd_span_singleton.2 hav
  have h1 : P.asIdeal * P.asIdeal ∣ P.asIdeal * (P'.asIdeal * Ideal.map (algebraMap (𝓞 F) (𝓞 E)) J) := by
    rw [← mul_assoc, ← hm, ← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton, Ideal.dvd_span_singleton, ← sq]
    exact hm2
  have h3 := (mul_dvd_mul_iff_left P.ne_bot).1 h1
  rcases P.prime.dvd_or_dvd h3 with h | h
  · exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top (Ideal.le_of_dvd h))).symm
  · have h4 : J ≤ v.asIdeal := by
      rw [← hP, Ideal.under_def, ← Ideal.map_le_iff_le_comap]
      exact Ideal.le_of_dvd h
    apply ha
    rw [← Ideal.span_singleton_le_iff_mem, hJ, sq]
    exact Ideal.mul_mono_right h4

end Split


open GlobalTheory.Proof.NarrowJetMoments in
theorem bad_primes : ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (u : Pr.Word), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 ∧ (((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal ↔ P ∈ Pr.vT u) := by
  classical
  intro X Pr sel S mu u hX hPr hsel hT hg P hP
  have hoff : ∀ Q ∈ rowSG Pr sel mu, ((Pr.T u : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := fun Q hQ =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hQ
  have hmem : ∀ Q, Q ∈ Sall sel mu u ↔ Q ∈ Pr.vT u ∨ Q ∈ rowSG Pr sel mu := fun Q => by
    unfold Sall
    exact Finset.mem_union
  rcases (hmem P).1 hP with h | h
  · have hTP := T_mem hPr u ⟨P, h⟩
    refine ⟨fun hc => ?_, ?_, ?_, fun _ => h, fun _ => hTP⟩
    · rcases (hmem _).1 hc with h' | h'
      · apply conj_piT_notMem hPr u ⟨P, h⟩
        exact (mem_conjP P _).1 (decoFin_mem_of_mem_divs h')
      · exact hoff _ h' (natCast_mem_conjP.2 hTP)
    · rw [hPr.vT_norm u P h]
      exact hPr.T_prime u
    · rw [hPr.vT_norm u P h]
      exact (T_unif hX hPr u ⟨P, h⟩).2
  · have hn := hoff P h
    refine ⟨fun hc => ?_, ?_⟩
    · rcases (hmem _).1 hc with h' | h'
      · exact hn (natCast_mem_conjP.1 (T_mem hPr u ⟨_, h'⟩))
      · exact conjP_notMem_rowSG hX hPr hsel hg h h'
    have hlast : ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal ↔ P ∈ Pr.vT u :=
      ⟨fun h' => absurd h' hn, fun h' => T_mem hPr u ⟨P, h'⟩⟩
    rcases Finset.mem_union.1 h with h1 | h1
    · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h1
      rw [hPr.vG_norm i P hi]
      refine ⟨hPr.g_prime i, ?_, hlast⟩
      have hrk : 2 * X.f = Module.finrank ℚ X.E := by
        rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
        rfl
      have hcc : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := cO_cO _
      refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E (cO X.E) (X.conjO (Pr.piG i)) (Pr.g i) cO_cO (hPr.g_prime i) ?_ ?_ ?_
        (hPr.vG_norm i) P hi
      · rw [hcc, mul_comm, hPr.piG_norm i]
      · rw [hcc]
        exact (hPr.piG_cop i).symm
      · rw [← hrk, ← hPr.vG_card i]
        rfl
    · obtain ⟨v, ⟨hs, ⟨hq, hq2⟩, -⟩, rfl⟩ := good_of_mem_QE h1
      rw [absNorm_eq_of_split hX.rankE hs hq (hsel v)]
      refine ⟨hq, ?_, hlast⟩
      have := notMem_sq_of_split hs hq2 (hsel v)
      rwa [map_natCast] at this

end GlobalTheory.ThetaMove.BadPrimes
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.Proof.AbsNormSplitPlace

open GlobalTheory.Proof.NarrowJetMoments

theorem absNorm_of_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) (hl : (Ideal.absNorm v.asIdeal).Prime)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨Q, Q', -, hm⟩ := hs
  have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, Ideal.absNorm_algebraMap]
    congr 1
    rw [← h2]
    exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm
  have h1 : ∀ R : HeightOneSpectrum (𝓞 E), Ideal.absNorm R.asIdeal ≠ 1 := fun R h =>
    R.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hb := (hl.mul_eq_prime_sq_iff (h1 Q) (h1 Q')).1 hN
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, ← hP, Ideal.under_def]
    exact Ideal.map_comap_le
  rcases P.isPrime.mul_le.1 hle with h | h
  · rw [← Q.isMaximal.eq_of_le P.isPrime.ne_top h, hb.1]
  · rw [← Q'.isMaximal.eq_of_le P.isPrime.ne_top h, hb.2]

theorem plc_eq_absNorm {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (hl : (Ideal.absNorm v.asIdeal).Prime) : ringChar (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  have h6 : ringChar (𝓞 F ⧸ v.asIdeal) ∣ Ideal.absNorm v.asIdeal := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  haveI := v.isPrime
  exact ((Nat.dvd_prime hl).1 h6).resolve_left CharP.ringChar_ne_one

theorem main : ∀ (Z : Dat) (u : Z.Pr.Word) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S), Z.Ok → IsSel Z.X sel → Z.Pr.T u ∈ S → (∀ i, Z.Pr.g i ∈ S) → (∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u) ∧ ∀ P ∈ rowSG Z.Pr sel mu, (Formalism.L2.Col.qOf P).Prime ∧ Formalism.L2.Col.qOf P ≠ Z.Pr.T u ∧ ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal ∧ ((∃ i, Formalism.L2.Col.qOf P = Z.Pr.g i) ∨ Formalism.L2.Col.qOf P ∉ S) := by
  intro Z u sel S mu hZ hsel hT hg
  have hPr := hZ.primes
  have hTn : ∀ P ∈ rowSG Z.Pr sel mu, ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal := fun P hP =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hP
  refine ⟨fun P hP hP' => ?_, fun P hP => ?_⟩
  · rcases (mem_Sall sel mu u P).1 hP with h | h <;> rcases (mem_Sall sel mu u _).1 hP' with h' | h'
    · refine conj_piT_notMem hPr u ⟨conjPrime₂ P, h'⟩ ?_
      change cO Z.X.E (Z.Pr.piT u) ∈ (conjPrime₂ P).asIdeal
      rw [mem_conjP, cO_cO]
      exact decoFin_mem_of_mem_divs h
    · exact hTn _ h' (natCast_mem_conjP.2 (T_mem hPr u ⟨P, h⟩))
    · exact hTn _ h (natCast_mem_conjP.1 (T_mem hPr u ⟨conjPrime₂ P, h'⟩))
    · exact conjP_notMem_rowSG hZ.fields hPr hsel hg h h'
  · have key : (Formalism.L2.Col.qOf P).Prime ∧ ((∃ i, Formalism.L2.Col.qOf P = Z.Pr.g i) ∨ Formalism.L2.Col.qOf P ∉ S) := by
      classical
      rcases Finset.mem_union.1 hP with h | h
      · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
        have e : Formalism.L2.Col.qOf P = Z.Pr.g i := hPr.vG_norm i P hi
        exact ⟨e ▸ hPr.g_prime i, Or.inl ⟨i, e⟩⟩
      · obtain ⟨v, hv, e⟩ := good_of_mem_QE h
        have e1 : Formalism.L2.Col.qOf P = Ideal.absNorm v.asIdeal :=
          absNorm_of_split hZ.fields.rankE hv.1 hv.2.1.1 (e ▸ hsel v)
        refine ⟨e1 ▸ hv.2.1.1, Or.inr ?_⟩
        rw [e1, ← plc_eq_absNorm hv.2.1.1]
        exact hv.2.2
    refine ⟨key.1, fun e => hTn P hP ?_, hTn P hP, key.2⟩
    rw [← e]
    exact Ideal.absNorm_mem _

end GlobalTheory.Proof.AbsNormSplitPlace
end
