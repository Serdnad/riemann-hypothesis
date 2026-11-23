module

public import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemIffForallMemLocalizeRingOfIntegers
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle058
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle057
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section

namespace GlobalTheory.OverCompare

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ u ∈ _root_.Formalism.BasicNotions.intV E v, u * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) = 1 := by
  have hc0 : (c : F) ≠ 0 := by
    intro h
    apply hc
    rw [show c = 0 from RingOfIntegers.coe_eq_zero_iff.mp h]
    exact v.asIdeal.zero_mem
  have hmem : algebraMap F (v.adicCompletion F) (c : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [_root_.GlobalTheory.LocalLattice.algebraMap_mem_adicCompletionIntegers_iff,
      _root_.GlobalTheory.LocalLattice.mem_localRing_iff]
    refine ⟨c, hc, ?_⟩
    rw [Algebra.smul_def, show algebraMap (𝓞 F) F c = (c : F) from rfl, mul_inv_cancel₀ hc0]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  refine ⟨1 ⊗ₜ[F] algebraMap F (v.adicCompletion F) (c : F)⁻¹, ?_, ?_⟩
  · unfold _root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt _root_.Formalism.UG.intOE
    exact Subring.subset_closure (Or.inr ⟨⟨_, hmem⟩, rfl⟩)
  · unfold _root_.Formalism.UG.inclE
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, ← Algebra.TensorProduct.algebraMap_apply,
      ← Algebra.TensorProduct.algebraMap_apply', ← map_mul, inv_mul_cancel₀ hc0, map_one]

end GlobalTheory.OverCompare
end

section

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

theorem exists_smul_mem_of_mem_locW (D : D7) (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (L : Submodule (𝓞 D.what₂.LL) V) {x : V}
    (hx : x ∈ locW D.what₂.places w L) : ∃ d : 𝓞 D.what₂.LL, d ∉ (D.plEq w).asIdeal ∧ d • x ∈ L := by
  have h1 : (1 : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal :=
    fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  unfold locW at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, h1, by simpa using hy⟩
  | zero => exact ⟨1, h1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, hy⟩ := hy
    obtain ⟨e, he, hz⟩ := hz
    refine ⟨d * e, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hy
    · rw [mul_smul]; exact L.smul_mem _ hz
  | smul r y _ hy =>
    obtain ⟨d, hd, hy⟩ := hy
    have hr : (D.plEq w).valuation D.what₂.LL (r : D.what₂.LL) ≤ 1 := (D.val_nonneg_iff w r).1 r.2
    obtain ⟨n, e, hne⟩ := (D.plEq w).exists_primeCompl_mul_eq_of_integer (r : D.what₂.LL) hr
    refine ⟨d * e, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hd e.2, ?_⟩
    have : (d * (e : 𝓞 D.what₂.LL)) • r • y = n • d • y := by
      rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL (d * (e : 𝓞 D.what₂.LL)), ← algebraMap_smul D.what₂.LL n,
        ← algebraMap_smul D.what₂.LL d y, smul_smul, smul_smul, ← hne, map_mul]
      congr 1; ring
    rw [this]; exact L.smul_mem _ hy

theorem mem_of_forall_locW (D : D7) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (L : Submodule (𝓞 D.what₂.LL) V) {x : V}
    (hx : ∀ w, x ∈ locW D.what₂.places w L) : x ∈ L := by
  let I : Ideal (𝓞 D.what₂.LL) := L.comap (LinearMap.toSpanSingleton (𝓞 D.what₂.LL) V x)
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL) :=
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem_of_mem_locW D (D.plEq.symm v) L (hx _)
    rw [Equiv.apply_symm_apply] at hd
    exact hd (hIM (show d ∈ I from hdx))
  have h1 : (1 : 𝓞 D.what₂.LL) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}

end GlobalTheory.LvT
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

theorem exists_hSpace_sigOK_sig :
    ∀ (D : D7) (P Q : ℕ), ∃ U : HSpace D.host.E, U.SigOK ∧ ∀ τ, U.sig τ = (P, Q) := by
  intro D P Q
  refine ⟨bandSpace D (P + Q) P (P + Q), bandSpace_sigOK D (P + Q) P (P + Q) le_rfl, fun τ => ?_⟩
  show (P + Q - (P + Q - P), P + Q - P) = (P, Q)
  congr 1 <;> omega

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory

theorem pow_dvd_of_mul_natCast_eq_of_notMem_prime {R : Type} [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R)
    (hI : I.IsPrime) {q : ℕ} (hq : q.Prime) (hqI : (q : R) ∈ I) {s : R} (hs : s ∉ I) :
    ∀ (d i : ℕ) (r : R), s * (i : R) = (q : R) ^ d * r → q ^ d ∣ i := by
  intro d
  induction d with
  | zero => intro i r _; simp
  | succ d ih =>
    intro i r h
    have hiI : (i : R) ∈ I := by
      have : s * (i : R) ∈ I := by
        rw [h, pow_succ', mul_assoc]
        exact I.mul_mem_right _ hqI
      exact (hI.mem_or_mem this).resolve_left hs
    have hdvd : q ∣ i := by
      by_contra hn
      have hc : IsCoprime (q : R) (i : R) := by
        have := (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)).map (Int.castRingHom R)
        simpa using this
      obtain ⟨a, b, hab⟩ := hc
      exact hI.one_notMem (hab ▸ I.add_mem (I.mul_mem_left a hqI) (I.mul_mem_left b hiI))
    obtain ⟨j, rfl⟩ := hdvd
    have hq0 : (q : R) ≠ 0 := by exact_mod_cast hq.ne_zero
    have h' : s * (j : R) = (q : R) ^ d * r := by
      apply mul_left_cancel₀ hq0
      push_cast at h
      linear_combination h
    rw [pow_succ']
    exact Nat.mul_dvd_mul_left q (ih j r h')

theorem sum_valsQ_eq_of_support_intAt : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (K : Type) [Field K] (f : E → K) (A₀ : ℕ), (∀ a, f a ≠ 0 → IntAt P ((qOf P : E) ^ A₀ * a)) → ∀ A B : ℕ, A₀ ≤ A → ∑ a ∈ LocE.valsQ E (qOf P) A B, f a = ∑ a ∈ LocE.valsQ E (qOf P) A₀ B, f a := by
  intro E _ _ P hq K _ f A₀ hf A B hA
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hA
  have hqP : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  generalize qOf P = q at *
  have hq0 : (q : E) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hpos : 0 < q ^ d := pow_pos hq.pos d
  symm
  apply Finset.sum_subset
  · intro a ha
    simp only [LocE.valsQ, Finset.mem_image, Finset.mem_range] at ha ⊢
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨q ^ d * i, ?_, ?_⟩
    · have : q ^ (A₀ + d + B) = q ^ d * q ^ (A₀ + B) := by ring
      rw [this]
      exact Nat.mul_lt_mul_of_pos_left hi hpos
    · push_cast
      field_simp
      ring
  · intro a ha hna
    by_contra hfa
    apply hna
    simp only [LocE.valsQ, Finset.mem_image, Finset.mem_range] at ha ⊢
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨r, s, hs, hrs⟩ := hf _ hfa
    have h1 : s * (i : 𝓞 E) = (q : 𝓞 E) ^ d * r := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      simp only [map_mul, map_pow, map_natCast]
      rw [← hrs]
      field_simp
      ring
    obtain ⟨j, rfl⟩ := pow_dvd_of_mul_natCast_eq_of_notMem_prime P.asIdeal P.isPrime hq hqP hs d i r h1
    refine ⟨j, ?_, ?_⟩
    · have : q ^ (A₀ + d + B) = q ^ d * q ^ (A₀ + B) := by ring
      rw [this] at hi
      exact Nat.lt_of_mul_lt_mul_left hi
    · push_cast
      field_simp
      ring

end GlobalTheory
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Proof.NormalFormAtPrime

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Arith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem degOne_of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) (hv : DegOne v)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) : DegOne P := by
  have key : ∀ Q Q' : HeightOneSpectrum (𝓞 E), Q ≠ Q' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal → Q.asIdeal.under (𝓞 F) = v.asIdeal → DegOne Q := by
    intro Q Q' hne hm hQ
    have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← map_mul, ← hm, Ideal.absNorm_algebraMap, ← h2]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm
    have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have h1' : Ideal.absNorm Q'.asIdeal ≠ 1 := fun h => Q'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have hq : Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal :=
      (((Nat.Prime.mul_eq_prime_sq_iff hv.1 h1 h1').1 hN).1)
    refine ⟨hq ▸ hv.1, ?_⟩
    rw [hq]
    intro hmem
    have hqv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
    obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} :=
      Ideal.dvd_span_singleton.2 hqv
    have hd : Q.asIdeal ^ 2 ∣ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)}) := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
      exact Ideal.dvd_span_singleton.2 hmem
    rw [hI, Ideal.map_mul, hm, pow_two, mul_assoc, mul_dvd_mul_iff_left Q.ne_bot] at hd
    rcases (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime).dvd_or_dvd hd with h | h
    · exact hne (HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le Q.isPrime.ne_top (Ideal.le_of_dvd h)).symm)
    · have hle : I ≤ v.asIdeal := by
        rw [← hQ]
        exact Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
      apply hv.2
      rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]
      exact Ideal.mul_mono_right hle
  obtain ⟨Q, Q', hne, hm⟩ := hs
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, ← hP]
    exact Ideal.map_comap_le
  rcases P.isPrime.mul_le.1 hle with h | h
  · obtain rfl : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
    exact key _ _ hne hm hP
  · obtain rfl : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
    exact key _ _ hne.symm (by rw [hm, mul_comm]) hP

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  have : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast this

theorem intAt_pow_mul {P : HeightOneSpectrum (𝓞 E)} (k : ℕ) {a : E} (ha : IntAt P a) : IntAt P ((qOf P : E) ^ k * a) := by
  refine IntAt.mul ?_ ha
  simpa using IntAt.coe P ((qOf P : 𝓞 E) ^ k)

theorem intAt_pow_mono {P : HeightOneSpectrum (𝓞 E)} {A A' : ℕ} (h : A ≤ A') {a : E} (ha : IntAt P ((qOf P : E) ^ A * a)) :
    IntAt P ((qOf P : E) ^ A' * a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have := intAt_pow_mul k ha
  rwa [← mul_assoc, ← pow_add, add_comm] at this

end Arith

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem sameDC_refl (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : SameDC (Pr := Pr) sharp j P h h :=
  ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem sameDC_trans {sharp : Bool} {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h h₁ h₂ : AutY X R j}
    (a : SameDC (Pr := Pr) sharp j P h h₁) (b : SameDC (Pr := Pr) sharp j P h₁ h₂) : SameDC (Pr := Pr) sharp j P h h₂ := by
  obtain ⟨r, hr, k, hk, rfl⟩ := a
  obtain ⟨r', hr', k', hk', rfl⟩ := b
  exact ⟨r' * r, mul_mem hr' hr, k * k', mul_mem hk hk', by simp only [mul_assoc]⟩

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

def TwistDegOne (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) : Prop :=
  ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → DegOne P.1

theorem twistDegOne_of_isSel (h2 : Module.finrank X.F X.E = 2) (hsel : IsSel X sel) : TwistDegOne Pr sel mu := by
  classical
  rintro ⟨P, hP⟩ hn
  have hQ : P ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.1 hP).resolve_left hn
  unfold QE at hQ
  split_ifs at hQ with hf
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hQ
    have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := hf.mem_toFinset.1 hv
    have hg : GoodPl X.E S v := by
      by_contra hg
      have := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 mu.2.2 v)) hg
      exact hv' this
    exact degOne_of_split h2 hg.1 hg.2.1 (hsel v)
  · simp at hQ

variable {Ch sel mu}

variable (Ch sel mu)

end GlobalTheory.Proof.NormalFormAtPrime
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory

theorem sum_range_mul_of_periodic {K : Type} [Field K] (g : ℕ → K) (N : ℕ)
    (hg : ∀ i, g (N + i) = g i) (k : ℕ) :
    ∑ i ∈ Finset.range (N * k), g i = (k : K) * ∑ i ∈ Finset.range N, g i := by
  first
  | exact @_root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic
  | exact _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic
  | (apply _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> assumption)
  | (intros; apply _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic ..)

theorem sum_valsQ_of_invariant (E : Type) [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) (K : Type) [Field K] (f : E → K) (B₀ : ℕ)
    (hf : ∀ a u, IntAt P u → f (a + (qOf P : E) ^ B₀ * u) = f a) (A B : ℕ) (hB : B₀ ≤ B) :
    ∑ a ∈ LocE.valsQ E (qOf P) A B, f a
      = (qOf P : K) ^ (B - B₀) * ∑ a ∈ LocE.valsQ E (qOf P) A B₀, f a := by
  classical
  have hq : (qOf P : E) ≠ 0 := by
    have : qOf P ≠ 0 := by
      unfold qOf
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact P.ne_bot
    exact_mod_cast this
  have key : ∀ C : ℕ, ∑ a ∈ LocE.valsQ E (qOf P) A C, f a
      = ∑ i ∈ Finset.range (qOf P ^ (A + C)), f ((i : E) / (qOf P : E) ^ A) := by
    intro C
    unfold LocE.valsQ
    rw [Finset.sum_image]
    intro i _ j _ hij
    have := (div_left_inj' (pow_ne_zero A hq)).1 hij
    exact_mod_cast this
  rw [key, key]
  have e : qOf P ^ (A + B) = qOf P ^ (A + B₀) * qOf P ^ (B - B₀) := by
    rw [← pow_add]; congr 1; omega
  rw [e, sum_range_mul_of_periodic (fun i : ℕ => f ((i : E) / (qOf P : E) ^ A))]
  · push_cast; rfl
  · intro i
    have h1 : IntAt P (1 : E) := by simpa using IntAt.coe P 1
    have := hf ((i : E) / (qOf P : E) ^ A) 1 h1
    rw [← this]
    congr 1
    push_cast
    field_simp
    ring

end GlobalTheory
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.unitaryPairPullback_lattices_translates : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), letI := D.host.cmStar; ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), ∃ g : VC D N N' →L[ℂ] VC D N N', (∀ x ∈ La D (tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M'), g x ∈ La D (tor0 D cc δ) M M') ∧ ∀ (t : VC D N N') (G : VC D N N' → ℂ), U D (tor0 D cc δ) t (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G) = fun z => U D (tor0 D cc δ) (g t) G (g z) := by
  first | exact @GlobalTheory.MomPull.pull_unitary | exact GlobalTheory.MomPull.pull_unitary | (intros; apply GlobalTheory.MomPull.pull_unitary <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.exists_realAdele_coordinates_cmType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∃ r : Ainf F ≃+* (T → ℝ), Continuous r ∧ Continuous r.symm ∧ (∀ a ρ, ((r a ρ : ℝ) : ℂ) = θ ρ (a ⊗ₜ[F] (1 : E))) ∧ (∀ a, LocalAdditiveCharacterDual.stdInf F a = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * ∑ ρ, r a ρ : ℝ) : ℂ))) ∧ ∀ a, (∀ w, a w ≠ 0) ↔ ∀ ρ, r a ρ ≠ 0 := by
  first | exact @GlobalTheory.RealAdeleCoord.exists_realCoord | exact GlobalTheory.RealAdeleCoord.exists_realCoord | (intros; apply GlobalTheory.RealAdeleCoord.exists_realCoord <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.MomN

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem weakApprox_split : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → letI := D.host.cmStar; ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' M M' ∧ EqAt D p (StandardLatticesGL3.stdL D N) M ∧ EqAt D p (StandardLatticesGL3.stdL D N') M' ∧ L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧ L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M' := by
  intro D p _ _ _ N N' L L' hAdm
  let _ := D.host.cmStar
  obtain ⟨hN, hN', hL, hL'⟩ := hAdm
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hp : p.Prime := Fact.out
  obtain ⟨γ, M, hM, hEq, hLM⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N' L' hL'
  exact ⟨γ, γ', M, M', ⟨hN, hN', hM, hM'⟩, hEq, hEq', hLM, hLM'⟩

end GlobalTheory.MomN
end
end
