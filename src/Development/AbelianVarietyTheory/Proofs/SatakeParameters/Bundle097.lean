module

public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Formalism.GaussJetBounds.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle095
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct

theorem _root_.GlobalTheory.T.integralAt_of_component_zero_under_prime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), (∀ v : HeightOneSpectrum (𝓞 F), IsOver v P → prV (E := E) v z = 0) → IntAtA (F := F) P z := by
  first | exact @GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero | exact GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero | (intros; apply GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.TypePrimeUnif


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq {X : _root_.Formalism.L2.Col.Fields} (hX : X.Ok) {Pr : _root_.Formalism.L2.Col.Primes X}
    (hP : Pr.Ok) (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E))
    (hv : P ∈ Pr.vG i) : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 := by
  classical
  refine ⟨hP.g_mem hv, fun hsq => ?_⟩
  have hdiv : ∀ Q ∈ Pr.vG i, X.conjO (Pr.piG i) ∈ Q.asIdeal := fun Q hQ =>
    _root_.Formalism.L2.Col.decoFin_mem_of_mem_divs (show Q ∈ _root_.Formalism.L2.Col.divs (X.conjO (Pr.piG i)) from hQ)
  have hg1 : 1 < Pr.g i := (hP.g_prime i).one_lt
  have hN : Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)}) = Pr.g i ^ X.f := by
    have h1 : Ideal.absNorm (Ideal.span {Pr.piG i}) * Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)})
        = Pr.g i ^ (2 * X.f) := by
      rw [← map_mul, Ideal.span_singleton_mul_span_singleton, hP.piG_norm i, X.absNorm_nat, hX.rankQ]
    rw [X.absNorm_conjO, ← sq, pow_mul'] at h1
    rw [X.absNorm_conjO]
    exact Nat.pow_left_injective two_ne_zero h1
  have hπP : Pr.piG i ∉ P.asIdeal := fun h => by
    obtain ⟨a, b, hab⟩ := hP.piG_cop i
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left a h) (P.asIdeal.mul_mem_left b (hdiv P hv))
  have hcop : IsCoprime (P.asIdeal ^ 2) (Ideal.span {Pr.piG i}) := by
    apply IsCoprime.pow_left
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have heq := P.isMaximal.eq_of_le h le_sup_left
    exact hπP (by rw [heq]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hP2 : P.asIdeal ^ 2 ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    have h : P.asIdeal ^ 2 ∣ Ideal.span {Pr.piG i} * Ideal.span {X.conjO (Pr.piG i)} := by
      rw [Ideal.span_singleton_mul_span_singleton, hP.piG_norm i, Ideal.dvd_span_singleton]
      exact hsq
    first
      | exact hcop.dvd_of_dvd_mul_left h
      | exact hcop.dvd_of_dvd_mul_right h
  let e : HeightOneSpectrum (𝓞 X.E) → ℕ := fun Q => if Q = P then 2 else 1
  have hall : ∏ Q ∈ Pr.vG i, Q.asIdeal ^ e Q ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    apply Finset.prod_dvd_of_coprime
    · intro Q _ Q' _ hne
      simp only [Function.onFun]
      apply IsCoprime.pow
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne Q.isMaximal Q'.isMaximal
        (fun h => hne (HeightOneSpectrum.ext h))
    · intro Q hQ
      by_cases h : Q = P
      · subst h
        simpa [e] using hP2
      · simpa [e, h, Ideal.dvd_span_singleton] using hdiv Q hQ
  have hnorm := map_dvd Ideal.absNorm hall
  rw [map_prod, hN] at hnorm
  have hcount : ∏ Q ∈ Pr.vG i, Ideal.absNorm (Q.asIdeal ^ e Q) = Pr.g i ^ (X.f + 1) := by
    rw [Finset.prod_congr rfl (fun Q hQ => show Ideal.absNorm (Q.asIdeal ^ e Q) = Pr.g i ^ e Q by
      rw [map_pow, hP.vG_norm i Q hQ]), Finset.prod_pow_eq_pow_sum]
    congr 1
    have he : ∀ Q, e Q = 1 + if Q = P then 1 else 0 := fun Q => by
      by_cases h : Q = P <;> simp [e, h]
    simp only [he, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.sum_ite_eq', hv, if_true, hP.vG_card i]
  rw [hcount] at hnorm
  have := (Nat.pow_dvd_pow_iff_le_right hg1).mp hnorm
  omega


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (g : 𝓞 E)
    (h1 : g ∈ w.asIdeal) (h2 : g ∉ w.asIdeal ^ 2) (a : E) (ha : _root_.Formalism.L2.Col.IntAt w a) (h0 : _root_.Formalism.L2.Col.redP w a = 0) :
    _root_.Formalism.L2.Col.IntAt w (a / algebraMap (𝓞 E) E g) := by
  haveI := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have key : ∃ c r, ∃ s ∉ w.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk w.asIdeal s * c = Ideal.Quotient.mk w.asIdeal r := by
    obtain ⟨r, s, hs, hsr⟩ := ha
    have hs0 : Ideal.Quotient.mk w.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact ⟨(Ideal.Quotient.mk w.asIdeal s)⁻¹ * Ideal.Quotient.mk w.asIdeal r, r, s, hs, hsr,
      mul_inv_cancel_left₀ hs0 _⟩
  unfold _root_.Formalism.L2.Col.redP at h0
  rw [dite_eq_left key] at h0
  have hspec := key.choose_spec
  rw [h0] at hspec
  obtain ⟨r, s, hs, hsr, hc⟩ := hspec
  rw [mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hc
  obtain ⟨J, hJ⟩ := (Ideal.dvd_span_singleton (I := w.asIdeal) (x := g)).mpr h1
  have hJw : ¬ J ≤ w.asIdeal := fun hle => h2 (by
    rw [sq]
    exact Ideal.mul_mono_right hle (hJ ▸ Ideal.mem_span_singleton_self g))
  obtain ⟨t, htJ, htw⟩ := Set.not_subset.mp hJw
  have hrt : r * t ∈ Ideal.span {g} := hJ ▸ Ideal.mul_mem_mul hc htJ
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hrt
  have hg0 : algebraMap (𝓞 E) E g ≠ 0 := by
    intro h
    apply h2
    rw [(IsFractionRing.injective (𝓞 E) E) (h.trans (map_zero _).symm)]
    exact zero_mem _
  refine ⟨x, s * t, fun hst => (w.isPrime.mem_or_mem hst).elim hs htw, ?_⟩
  have hxE : algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g =
      algebraMap (𝓞 E) E r * algebraMap (𝓞 E) E t := by
    rw [← map_mul, ← map_mul, hx]
  have hmain : algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E t * a =
      algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g := by
    linear_combination algebraMap (𝓞 E) E t * hsr - hxE
  calc algebraMap (𝓞 E) E (s * t) * (a / algebraMap (𝓞 E) E g)
      = algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E t * a / algebraMap (𝓞 E) E g := by
        rw [map_mul]; ring
    _ = algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g / algebraMap (𝓞 E) E g := by rw [hmain]
    _ = algebraMap (𝓞 E) E x := mul_div_cancel_right₀ _ hg0


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypePrimeUnif.intAt_div_qOf : ∀ (X : _root_.Formalism.L2.Col.Fields) (Pr : _root_.Formalism.L2.Col.Primes X), X.Ok → Pr.Ok →
    ∀ w ∈ Pr.vGs, ∀ a : X.E, _root_.Formalism.L2.Col.IntAt w a →
    _root_.Formalism.L2.Col.redP w a = 0 → _root_.Formalism.L2.Col.IntAt w (a / (_root_.Formalism.L2.Col.qOf w : X.E)) := by
  classical
  intro X Pr hX hP w hw a ha h0
  have hw' : w ∈ Pr.vG 0 ∪ Pr.vG 1 := hw
  obtain ⟨i, hv⟩ : ∃ i, w ∈ Pr.vG i := by
    rcases Finset.mem_union.mp hw' with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hq : (_root_.Formalism.L2.Col.qOf w : X.E) = algebraMap (𝓞 X.E) X.E ((Pr.g i : ℕ) : 𝓞 X.E) := by
    unfold _root_.Formalism.L2.Col.qOf
    rw [map_natCast, hP.vG_norm i w hv]
  have hgw := _root_.GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hP i w hv
  rw [hq]
  exact _root_.GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq w _ hgw.1 hgw.2 a ha h0

end GlobalTheory.TypePrimeUnif
end

section

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.GO.ChRoot

section Loc

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_natCast (k : ℕ) : IntAt P (k : E) := by simpa using IntAt.coe P (k : 𝓞 E)

theorem intAt_zero' : IntAt P (0 : E) := by simpa using intAt_natCast (P := P) 0

theorem intAt_one' : IntAt P (1 : E) := by simpa using intAt_natCast (P := P) 1

theorem qOf_pos (P : HeightOneSpectrum (𝓞 E)) : 0 < qOf P :=
  Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

variable [StarRing E]

theorem mem_stdAt' {n : ℕ} {x : Sp E n} : x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

theorem mem_lamY_zero {q n c : ℕ} {x : Sp E (n + c)} : x ∈ LocE.lamY P q n c 0 ↔ x ∈ stdAt E (n + c) P := by
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt', mem_stdAt']
  refine forall_congr' fun i => ?_
  simp [LocE.scE]

theorem eN_mem {N i : ℕ} : Loc.eN E N i ∈ stdAt E N P := by
  rw [mem_stdAt']
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one'
  · exact intAt_zero'

theorem intAt_n1Arg {n c : ℕ} (a : E) (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (h : ∀ x ∈ stdAt E (n + c) P, a • r x ∈ stdAt E (n + c) P) : IntAt P (a * Loc.n1Arg r) := by
  unfold Loc.n1Arg
  rw [Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_
  unfold Loc.atN
  split_ifs with hi
  · exact mem_stdAt'.1 (h _ eN_mem) ⟨n + i, hi⟩
  · simpa using intAt_zero'


omit [StarRing E] in
theorem unitV_root {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) (h : LocE.unitV χ a ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ LocE.unitV χ a ^ k = 1 := by
  unfold LocE.unitV at h ⊢
  split_ifs at h ⊢ with hu
  · have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
    refine ⟨Nat.card (𝓞 E ⧸ P.asIdeal)ˣ, Nat.card_pos, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  · exact absurd rfl h

end Loc

theorem psi_root {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB} (hc : c.Ok) (P : SB) (x : X.E)
    (hx : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * x)) : c.psi P x ^ (qOf P.1 ^ c.D P) = 1 := by
  have key : ∀ k : ℕ, c.psi P ((k : X.E) * x) = c.psi P x ^ k := by
    intro k
    induction k with
    | zero => simpa using hc.psi_int P 0 intAt_zero'
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ hx, ih, pow_succ]
      rw [mul_left_comm]
      exact (intAt_natCast k).mul hx
  rw [← key]
  exact hc.psi_int P _ (by simpa using hx)

theorem lam_root {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (hj : j ≤ m2 + 1) (b : L.β j)
    (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (hP : P.1 ∉ Pr.vGs) (g : (L.levQ j b P).H) :
    ∃ k : ℕ, 0 < k ∧ (L.levQ j b P).lam g ^ k = 1 := by
  classical
  have hg := Subgroup.mem_subgroupOf.1 ((hL.grpQ j b P).le g.2)
  obtain ⟨r, hr, hrg⟩ := hg
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  obtain ⟨h, hh⟩ : ∃ h, h = L.h j b P' := ⟨_, rfl⟩
  have hχ : (((L.levQ j b P).lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P' (L.h j b P') r := hL.chrQ j b P g r hr hrg
  replace hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h := hh ▸ hr
  rw [← hh] at hχ
  have hb := hL.boundQ j b P' hP
  have hD := hL.depthQ' P' hP
  have hm := hL.hm
  simp only [lamYat, show P'.1 ∉ Pr.vGs from hP, if_false, mem_lamY_zero] at hb
  have hκ := hr.2
  simp only [Jat, hP, if_false] at hκ
  have hκ' : ∀ x, (h⁻¹ * r * h) x ∈ stdAt X.E _ P.1 ↔ x ∈ stdAt X.E _ P.1 := by
    intro x
    exact hκ.1 x
  have hint : IntAt P.1 ((qOf P.1 : X.E) ^ j * Loc.n1Arg r) := by
    refine intAt_n1Arg _ r fun x hx => ?_
    have h1 := (hb _ ((hκ' _).2 (hb x hx).1)).2
    have h2 : h ((h⁻¹ * r * h) (h⁻¹ x)) = r x := by
      change (h * (h⁻¹ * r * h) * h⁻¹) x = r x
      congr 1
      group
    rwa [← hh, h2] at h1
  have hint' : IntAt P'.1 ((qOf P'.1 : X.E) ^ cst.D P' * Loc.n1Arg r) := by
    obtain ⟨d, hd⟩ : ∃ d, cst.D P' = d + j := ⟨cst.D P' - j, by omega⟩
    rw [hd, pow_add, mul_assoc, ← Nat.cast_pow]
    exact (intAt_natCast _).mul hint
  have h1 := psi_root hL.cst_ok P' _ hint'
  simp only [chiInv, lamRow, show P'.1 ∉ Pr.vGs from hP, if_false, LocE.lamQB] at hχ
  have hne := ((L.levQ j b P).lam g).ne_zero
  rw [hχ] at hne
  obtain ⟨k, hk, h2⟩ := unitV_root _ _ (fun h0 => right_ne_zero_of_mul hne (inv_eq_zero.2 h0))
  refine ⟨qOf P'.1 ^ cst.D P' * k, Nat.mul_pos (pow_pos (qOf_pos _) _) hk, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hχ, mul_pow, inv_pow, inv_pow, pow_mul, h1, one_pow, mul_comm _ k, pow_mul, h2, one_pow]
  simp

end GlobalTheory.GO.ChRoot
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.FrameDeco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}


omit [StarRing E] in
theorem exists_inv_mod (P : HeightOneSpectrum (𝓞 E)) {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    ∃ a p : 𝓞 E, p ∈ P.asIdeal ∧ a * s + p = 1 := by
  obtain ⟨a, p, hp, h⟩ := P.isMaximal.exists_inv hs
  exact ⟨a, p, hp, h⟩

theorem smul_localizationAt_le (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) :
    P.asIdeal • localization₂ P.asIdeal N ≤ localization₂ P.asIdeal (P.asIdeal • N) := by
  rw [Submodule.smul_le]
  intro r hr x hx
  obtain ⟨t, ht, htx⟩ := (mem_locP P N x).1 hx
  refine (mem_locP P _ _).2 ⟨t, ht, ?_⟩
  rw [smul_comm]
  exact Submodule.smul_mem_smul hr htx

theorem mem_smul_of_mem_locP (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    {y : Sp E n} (hy : y ∈ N) (h : y ∈ localization₂ P.asIdeal (P.asIdeal • N)) : y ∈ P.asIdeal • N := by
  obtain ⟨t, ht, hty⟩ := (mem_locP P _ _).1 h
  obtain ⟨a, p, hp, e⟩ := exists_inv_mod P ht
  have : y = a • (t • y) + p • y := by
    rw [smul_smul, ← add_smul, e, one_smul]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hty) (Submodule.smul_mem_smul hp hy)

theorem redV_add (P : HeightOneSpectrum (𝓞 E)) {x y : Sp E n}
    (hx : x ∈ stdAt E n P) (hy : y ∈ stdAt E n P) : redV P (x + y) = redV P x + redV P y := by
  funext i
  exact reduction_add ((mem_localization_standardLattice _ _).1 hx _) ((mem_localization_standardLattice _ _).1 hy _)

theorem redV_osmul (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) {x : Sp E n}
    (hx : x ∈ stdAt E n P) :
    redV P (a • x) = Ideal.Quotient.mk P.asIdeal a • redV P x := by
  funext i
  exact redP_osmul a ((mem_localization_standardLattice _ _).1 hx _)

theorem exists_deco_of_frames : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := ∅)) (f : SG → (Sp E n ≃ₗ[E] Sp E n)), (∀ (w : SG) (x : Sp E n), f w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) → ∃ d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), d'.1.N = d.1.N ∧ d'.1.f = d.1.f ∧ ∀ w : SG, ∀ x ∈ stdAt E n w.1, d'.1.be w (f w x) = redV w.1 x := by
  classical
  intro E _ _ _ n ST SG d f hf
  have hf' : ∀ (w : SG) (y : Sp E n), y ∈ d.1.at w.1 → (f w).symm y ∈ stdAt E n w.1 := by
    intro w y hy
    exact (hf w _).1 (by simpa using hy)
  let D : Deco E n ST SG :=
    { N := d.1.N
      f := d.1.f
      be := fun w y => if y ∈ d.1.at w.1 then redV w.1 ((f w).symm y) else 0 }
  have hbe : ∀ (w : SG) (y : Sp E n), y ∈ d.1.at w.1 → D.be w y = redV w.1 ((f w).symm y) :=
    fun w y hy => if_pos hy
  have hsm : ∀ (w : SG) (a : 𝓞 E), ∀ x ∈ d.1.at w.1,
      D.be w (a • x) = Ideal.Quotient.mk w.1.asIdeal a • D.be w x := by
    intro w a x hx
    rw [hbe w _ (Submodule.smul_mem _ a hx), hbe w _ hx, equiv_osmul, redV_osmul _ _ (hf' w x hx)]
  have hD : D.Ok :=
    { lat := d.2.lat
      uni := d.2.uni
      f_add := d.2.f_add
      f_smul := d.2.f_smul
      f_off := d.2.f_off
      f_ne := d.2.f_ne
      be_add := by
        intro w x hx y hy
        replace hx : x ∈ d.1.at w.1 := hx
        replace hy : y ∈ d.1.at w.1 := hy
        rw [hbe w _ (Submodule.add_mem _ hx hy), hbe w _ hx, hbe w _ hy, map_add (f := _),
          redV_add _ (hf' w x hx) (hf' w y hy)]
      be_smul := hsm
      be_off := fun w x hx => if_neg hx
      be_surj := by
        intro w c
        choose r hr using fun i => Ideal.Quotient.mk_surjective (c i)
        have h1 : (fun i => algebraMap (𝓞 E) E (r i) : Sp E n) ∈ stdLat E n :=
          (mem_stdLat _).2 fun i => ⟨r i, rfl⟩
        have h2 := (hf w _).2 (le_locP _ _ h1)
        obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 h2
        obtain ⟨a, p, hp, e⟩ := exists_inv_mod w.1 hs
        refine ⟨a • s • _, Submodule.smul_mem _ a hsy, ?_⟩
        have e' : Ideal.Quotient.mk w.1.asIdeal (a * s) = 1 := by
          have := congrArg (Ideal.Quotient.mk w.1.asIdeal) e
          rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero, map_one] at this
        rw [smul_smul, hsm w _ _ h2, e', one_smul, hbe w _ h2, LinearEquiv.symm_apply_apply]
        funext i
        exact (reduction_coe _ _).trans (hr i)
      be_ker := by
        intro w y hy h0
        replace hy : y ∈ d.1.N := hy
        have hy' : y ∈ d.1.at w.1 := le_locP _ _ hy
        rw [hbe w _ hy'] at h0
        have hx := hf' w y hy'
        obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hx
        have h0' : redV w.1 (s • (f w).symm y) = 0 := by
          rw [redV_osmul _ _ hx, h0, smul_zero]
        choose r hr using (mem_stdLat _).1 hsx
        have hmem : ∀ i, r i ∈ w.1.asIdeal := by
          intro i
          have h3 : redP w.1 ((s • (f w).symm y) i) = 0 := congrFun h0' i
          rw [← hr i, reduction_coe] at h3
          exact Ideal.Quotient.eq_zero_iff_mem.1 h3
        have h4 : s • (f w).symm y
            = ∑ i, r i • (Pi.single i (algebraMap (𝓞 E) E 1) : Sp E n) := by
          generalize s • (f w).symm y = x at hr
          funext j
          simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
        have h5 : s • y ∈ w.1.asIdeal • d.1.at w.1 := by
          have : s • y = f w (s • (f w).symm y) := by
            rw [equiv_osmul, LinearEquiv.apply_symm_apply]

          rw [this, h4, map_sum]
          refine Submodule.sum_mem _ fun i _ => ?_
          rw [equiv_osmul]
          exact Submodule.smul_mem_smul (hmem i)
            ((hf w _).2 (le_locP _ _ (single_mem_stdLat i 1)))
        obtain ⟨t, ht, hts⟩ := (mem_locP _ _ _).1 (smul_localizationAt_le w.1 d.1.N h5)
        refine mem_smul_of_mem_locP w.1 d.1.N hy ((mem_locP _ _ _).2 ⟨t * s, ?_, ?_⟩)
        · exact fun hm => (w.1.isPrime.mem_or_mem hm).elim ht hs
        · rwa [mul_smul] }
  refine ⟨⟨D, hD⟩, rfl, rfl, fun w x hx => ?_⟩
  change D.be w (f w x) = _
  rw [hbe w _ ((hf w x).2 hx), LinearEquiv.symm_apply_apply]

end GlobalTheory.FrameDeco
end

section

open Formalism.MainNotions Classical

theorem _root_.GlobalTheory.T.kvalGe_zero_of_integral_jets : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]), Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  first | exact @GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | exact GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | (intros; apply GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.lowCoefficients_of_parameterCoefficients : ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] (Un : (ι →₀ ℕ) → MvPowerSeries ι (K0 p)), (∀ n, inParam p (Un n) = MvPowerSeries.monomial n 1 ∧ (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m (Un n) = 0)) → ∀ (U : MvPowerSeries ι K1) (d : ℕ) (S : Finset (ι →₀ ℕ)), (∀ n : ι →₀ ℕ, n.degree ≤ d → n ∈ S) → ∀ m : ι →₀ ℕ, m.degree ≤ d → MvPowerSeries.coeff m U = ∑ n ∈ S, MvPowerSeries.coeff n (inParamK p K1 U) * algebraMap (K0 p) K1 (MvPowerSeries.coeff m (Un n)) := by
  first | exact @GlobalTheory.TwU.low_coeff_of_param | exact GlobalTheory.TwU.low_coeff_of_param | (intros; apply GlobalTheory.TwU.low_coeff_of_param <;> assumption)
end
