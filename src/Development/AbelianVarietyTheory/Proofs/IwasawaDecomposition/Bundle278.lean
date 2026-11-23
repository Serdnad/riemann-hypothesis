module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContained
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle231
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle263
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.BasePrimes

section General

variable {E : Type} [Field E] [NumberField E]

theorem prod_absNorm_divs_dvd {a : 𝓞 E} (ha : a ≠ 0) :
    ∏ P ∈ divs a, Ideal.absNorm P.asIdeal ∣ Ideal.absNorm (Ideal.span {a}) := by
  rw [← map_prod]
  apply map_dvd
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro P _ Q _ hPQ
    exact (HeightOneSpectrum.isCoprime_of_ne P Q hPQ)
  · intro P hP
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact (mem_divs ha P).1 hP

theorem le_absNorm_of_mem {p : ℕ} (hp : p.Prime) (P : HeightOneSpectrum (𝓞 E)) (h : (p : 𝓞 E) ∈ P.asIdeal) :
    p ≤ Ideal.absNorm P.asIdeal := by
  have h1 : Ideal.absNorm P.asIdeal ∣ p ^ Module.finrank ℚ E := by
    rw [← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h1
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk
    exact absurd hk P.isPrime.ne_top
  · rw [hk]
    exact Nat.le_self_pow hk0.ne' p

theorem absNorm_eq_of_split {p : ℕ} (hp : p.Prime) (h : (divs (p : 𝓞 E)).card = Module.finrank ℚ E)
    (P : HeightOneSpectrum (𝓞 E)) (hP : (p : 𝓞 E) ∈ P.asIdeal) : Ideal.absNorm P.asIdeal = p := by
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 := prod_absNorm_divs_dvd hp0
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, ← h] at h1
  have h2 := Nat.le_of_dvd (pow_pos hp.pos _) h1
  by_contra hne
  have hlt : p < Ideal.absNorm P.asIdeal := lt_of_le_of_ne (le_absNorm_of_mem hp P hP) (Ne.symm hne)
  have h3 : ∏ _Q ∈ divs (p : 𝓞 E), p < ∏ Q ∈ divs (p : 𝓞 E), Ideal.absNorm Q.asIdeal :=
    Finset.prod_lt_prod₀ (fun _ _ => hp.pos) (fun Q hQ => le_absNorm_of_mem hp Q ((mem_divs hp0 Q).1 hQ))
      ⟨P, (mem_divs hp0 P).2 hP, hlt⟩
  rw [Finset.prod_const] at h3
  omega

theorem card_divs_map_le (s : 𝓞 E →+* 𝓞 E) (hs : Function.Surjective s) {a : 𝓞 E} (ha : a ≠ 0) (hsa : s a ≠ 0) :
    (divs (s a)).card ≤ (divs a).card := by
  refine Finset.card_le_card_of_injOn (fun P => HeightOneSpectrum.comap s hs P) ?_ ?_
  · intro P hP
    have h1 := (mem_divs hsa P).1 hP
    exact (mem_divs ha _).2 h1
  · intro P _ Q _ hPQ
    apply HeightOneSpectrum.ext
    exact Ideal.comap_injective_of_surjective s hs (congrArg HeightOneSpectrum.asIdeal hPQ)

theorem split_facts (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) {p f : ℕ} (hp : p.Prime)
    (hf : Module.finrank ℚ E = 2 * f) (h : (placesOver E p).ncard = Module.finrank ℚ E) {a : 𝓞 E}
    (ha : a * s a = (p : 𝓞 E)) :
    IsCoprime a (s a) ∧ ((divs a).card = f ∧ ∀ P ∈ divs a, Ideal.absNorm P.asIdeal = p) ∧
      ((divs (s a)).card = f ∧ ∀ P ∈ divs (s a), Ideal.absNorm P.asIdeal = p) := by
  classical
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (ha ▸ hp0)
  have hb0 : s a ≠ 0 := right_ne_zero_of_mul (ha ▸ hp0)
  have hsurj : Function.Surjective s := fun x => ⟨s x, hs x⟩
  have hc : (divs (p : 𝓞 E)).card = Module.finrank ℚ E := by
    rw [← h, ← Set.ncard_coe_finset]
    congr 1
    ext P
    exact mem_divs hp0 P
  have hna : ∀ P ∈ divs a, Ideal.absNorm P.asIdeal = p := fun P hP =>
    absNorm_eq_of_split hp hc P (ha ▸ Ideal.mul_mem_right _ _ ((mem_divs ha0 P).1 hP))
  have hnb : ∀ P ∈ divs (s a), Ideal.absNorm P.asIdeal = p := fun P hP =>
    absNorm_eq_of_split hp hc P (ha ▸ Ideal.mul_mem_left _ _ ((mem_divs hb0 P).1 hP))
  have hU : divs (p : 𝓞 E) = divs a ∪ divs (s a) := by
    ext P
    rw [Finset.mem_union, mem_divs hp0, mem_divs ha0, mem_divs hb0, ← ha]
    exact P.isPrime.mul_mem_iff_mem_or_mem
  have hle : (divs a).card + (divs (s a)).card ≤ Module.finrank ℚ E := by
    have h1 := prod_absNorm_divs_dvd ha0
    have h2 := prod_absNorm_divs_dvd hb0
    rw [Finset.prod_congr rfl hna, Finset.prod_const] at h1
    rw [Finset.prod_congr rfl hnb, Finset.prod_const] at h2
    have h3 := mul_dvd_mul h1 h2
    rw [← pow_add, ← map_mul, Ideal.span_singleton_mul_span_singleton, ha, Ideal.absNorm_span_natCast,
      RingOfIntegers.rank] at h3
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h3
  have hui := Finset.card_union_add_card_inter (divs a) (divs (s a))
  rw [← hU, hc] at hui
  have e1 := card_divs_map_le s hsurj ha0 hb0
  have e2 := card_divs_map_le s hsurj hb0 (by rw [hs]; exact ha0)
  rw [hs] at e2
  have hint : divs a ∩ divs (s a) = ∅ := Finset.card_eq_zero.1 (by omega)
  refine ⟨?_, ⟨by omega, hna⟩, ⟨by omega, hnb⟩⟩
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨M, hM, hle'⟩ := Ideal.exists_le_maximal _ hne
  have haM : a ∈ M := hle' (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))
  have hbM : s a ∈ M := hle' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (s a)))
  have hM0 : M ≠ ⊥ := fun h0 => ha0 (by rwa [h0, Ideal.mem_bot] at haM)
  have hmem : (⟨M, hM.isPrime, hM0⟩ : HeightOneSpectrum (𝓞 E)) ∈ divs a ∩ divs (s a) :=
    Finset.mem_inter.2 ⟨(mem_divs ha0 _).2 haM, (mem_divs hb0 _).2 hbM⟩
  rw [hint] at hmem
  exact Finset.notMem_empty _ hmem

theorem modEq_one_of_dvd (s : 𝓞 E →+* 𝓞 E) {a : 𝓞 E} {T c : ℕ} (ha : a * s a = (T : 𝓞 E))
    (h : (c : 𝓞 E) ∣ a - 1) : T ≡ 1 [MOD c] := by
  obtain ⟨y, hy⟩ := h
  have h1 : a = 1 + (c : 𝓞 E) * y := by
    rw [← hy]
    ring
  have h2 : s a = 1 + (c : 𝓞 E) * s y := by
    rw [h1, map_add (f := _), map_one, map_mul, map_natCast]
  have h3 : (c : 𝓞 E) ∣ (((T : ℤ) - 1 : ℤ) : 𝓞 E) := by
    refine ⟨y + s y + (c : 𝓞 E) * (y * s y), ?_⟩
    push_cast
    rw [← ha, h2]
    nth_rewrite 1 [h1]
    ring
  exact (Nat.modEq_iff_dvd.2 (Primes.natCast_dvd_intCast h3)).symm

end General

theorem conjO_conjO (B : Base) (x : 𝓞 B.fields.E) : B.fields.conjO (B.fields.conjO x) = x := by
  letI := B.fields.starE
  apply RingOfIntegers.ext
  exact star_star (x : B.fields.E)

theorem finrank_E (B : Base) : Module.finrank ℚ B.fields.E = 2 * B.fields.f := by
  rw [B.fields_f]
  show Module.finrank ℚ B.host.E = _
  rw [B.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

theorem mem_Kq (B : Base) {x : B.host.E} (hx : x ∈ B.host.K) : x ∈ B.fields.Kq := by
  intro τ τ'
  rw [B.fields_emb_apply, B.fields_emb_apply, Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K B.host _ τ.2 x hx,
    Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K B.host _ τ'.2 x hx]

theorem primes_ok : ∀ (B : Base) (X : PreX B.toPre), (B.primes X).Ok ∧ (B.primes X).PiGCong := by
  intro B X
  have hG := fun i => split_facts B.fields.conjO (conjO_conjO B) (B.host.g_prime i) (finrank_E B)
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ (B.host.g_prime i) (B.g_cond i)).1 (B.primes_piG_norm X i)
  have hT := fun u => split_facts B.fields.conjO (conjO_conjO B) (B.T_prime u) (finrank_E B)
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ (B.T_prime u) (B.T_cond u)).1 (B.primes_piT_norm X u)
  refine ⟨?_, B.primes_piGCong X⟩
  refine
    { g_prime := B.host.g_prime
      piG_Kq := fun i => mem_Kq B (X.piG_K i)
      piG_norm := B.primes_piG_norm X
      piG_cop := fun i => (hG i).1
      vG_card := fun i => (hG i).2.2.1
      vG_norm := fun i => (hG i).2.2.2
      g_cong := (B.primes_piGCong X).g_cong (B.primes_piG_norm X)
      g_ne := B.host.g_ne
      T_prime := B.T_prime
      piT_Kq := fun u => mem_Kq B (X.piT_K u)
      piT_norm := B.primes_piT_norm X
      piT_cop := fun u => (hT u).1
      vT_card := fun u => (hT u).2.1.1
      vT_norm := fun u => (hT u).2.1.2
      piT_cong := X.piT_cong
      T_ne_g := fun u i hi => ?_ }
  have h1 := modEq_one_of_dvd B.fields.conjO (B.primes_piT_norm X u) (X.piT_cong u)
  have hd : B.host.g i ∣ B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 := by
    refine Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have h2 : B.host.g i ≡ 1 [MOD B.host.g i] := by
    have h3 := h1.of_dvd hd
    rwa [hi] at h3
  have h4 : B.host.g i ∣ 1 := (Nat.modEq_zero_iff_dvd.1 (h2.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)))
  exact (B.host.g_prime i).one_lt.ne' (Nat.dvd_one.1 h4)

end GlobalTheory.BasePrimes
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.ellipticTorsionPointCoordinates_finite : ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ), n ≠ 0 → (torsionCoords W n).Finite := by
  first | exact @GlobalTheory.finite_torsionCoords | exact GlobalTheory.finite_torsionCoords | (intros; apply GlobalTheory.finite_torsionCoords <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.isAlgebraic_of_ellipticTorsionCoordinates_finite : ∀ (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (A : WeierstrassCurve F) (n : ℕ), (torsionCoords (A.baseChange ℂ) n).Finite → ∀ z ∈ torsionCoords (A.baseChange ℂ) n, IsAlgebraic ℚ z := by
  first | exact @GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite | exact GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite | (intros; apply GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.heckeCharacter_finiteIdele_value_mem_field : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (M : IntermediateField ℚ ℂ), valueField χ 0 ≤ M → (∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x, (∀ w : InfinitePlace E, (x.val : AdeleRing (𝓞 E) E).1 w = 1) → ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  first | exact @GlobalTheory.HeckeValField.mem_of_inf_eq_one | exact GlobalTheory.HeckeValField.mem_of_inf_eq_one | (intros; apply GlobalTheory.HeckeValField.mem_of_inf_eq_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3


theorem _root_.GlobalTheory.T.exists_congruence_level_maps_into_lattice_congruence : ∀ (D : D7) (V : HSp D) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (hF : D.host.F = maximalRealSubfield D.host.E), StdFrame hF P → ∀ N : ℕ, 0 < N → ∃ N' : ℕ, 0 < N' ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N' κ → GlobalTheory.Member.FinCong V N (P.ψ κ) := by
  first | exact @GlobalTheory.StdFrameCong.exists_cong_finCong | exact GlobalTheory.StdFrameCong.exists_cong_finCong | (intros; apply GlobalTheory.StdFrameCong.exists_cong_finCong <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3


theorem _root_.GlobalTheory.T.principal_congruence_level_contained : ∀ (D : D7) (V : HSp D) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (hF : D.host.F = maximalRealSubfield D.host.E), StdFrame hF P → ∀ N : ℕ, 0 < N → ∃ N' : ℕ, 0 < N' ∧ ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N' k → k ∈ principalLevelFrame.levN P N := by
  first | exact @GlobalTheory.LatCongImage.finCong_mem_levN | exact GlobalTheory.LatCongImage.finCong_mem_levN | (intros; apply GlobalTheory.LatCongImage.finCong_mem_levN <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.MetBase

open Formalism.HermitianLatticesTheory

section Polar

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem fcoord_smul_emb (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x : V) : fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
    funext i; simp [vecAt, map_mul]
  simp only [fcoord, hv, Matrix.mulVec_smul]

theorem fcoord_add_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
    funext i; simp [vecAt, map_add (f := _)]
  simp only [fcoord, hv, Matrix.mulVec_add]

theorem majAt_add_left_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x x' y : V) : majAt b X v (x + x') y = majAt b X v x y + majAt b X v x' y := by
  simp only [majAt, fcoord_add_of b X v x x', Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem majAt_add_right_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y y' : V) : majAt b X v x (y + y') = majAt b X v x y + majAt b X v x y' := by
  simp only [majAt, fcoord_add_of b X v y y', Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem majAt_smul_left_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : majAt b X v (a • x) y = star (v.embedding a) * majAt b X v x y := by
  simp only [majAt, fcoord_smul_emb, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem majAt_smul_right_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : majAt b X v x (a • y) = v.embedding a * majAt b X v x y := by
  simp only [majAt, fcoord_smul_emb, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem majAt_self_eq (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    majAt b X v x x = (((normAt b X v x) ^ 2 : ℝ) : ℂ) := by
  unfold normAt cnorm majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

theorem majAt_eq_of_diag {V' ι' : Type} [AddCommGroup V'] [Module K V'] [Fintype ι'] [DecidableEq ι']
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Module.Basis ι' K V')
    (X' : InfinitePlace K → Matrix ι' ι' ℂ) (v : InfinitePlace K) (e : V' →ₗ[K] V)
    (hv : ∃ a : K, star (v.embedding a) ≠ v.embedding a)
    (h : ∀ x, majAt b X v (e x) (e x) = majAt b' X' v x x) (x y : V') :
    majAt b X v (e x) (e y) = majAt b' X' v x y := by
  have hadd : ∀ x y : V', (majAt b X v (e x) (e y) - majAt b' X' v x y) +
      (majAt b X v (e y) (e x) - majAt b' X' v y x) = 0 := by
    intro x y
    have h0 := h (x + y)
    have h1 := h x
    have h2 := h y
    simp only [map_add (f := _), majAt_add_left_of, majAt_add_right_of] at h0
    linear_combination h0 - h1 - h2
  obtain ⟨a, ha⟩ := hv
  have h3 := hadd x (a • y)
  simp only [map_smul, majAt_smul_left_of, majAt_smul_right_of] at h3
  have h4 := hadd x y
  have h5 : (v.embedding a - star (v.embedding a)) * (majAt b X v (e x) (e y) - majAt b' X' v x y) = 0 := by
    linear_combination h3 - star (v.embedding a) * h4
  have h6 : v.embedding a - star (v.embedding a) ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_left h6)

end Polar

theorem exists_nonreal {K : Type} [Field K] (v : InfinitePlace K) (hv : v.IsComplex) :
    ∃ a : K, star (v.embedding a) ≠ v.embedding a := by
  by_contra hc
  push_neg at hc
  apply InfinitePlace.not_isReal_iff_isComplex.2 hv
  rw [InfinitePlace.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq]
  exact hc a

end GlobalTheory.Mem.R3.MetBase

namespace GlobalTheory.Mem.R3.MetBase



theorem metric_base_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →
    ∀ x y, Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s0Of R F).XE A3.A.v0 x y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH x y
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have h2 : (R.toCx3 F).H2 F.cr false := (hCx.what₂ false).1
  have hE : R.models_HE := hP.char.base.models.HE
  have hn : 0 < RealDat.nP F.lv2 false := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have hv0 : A3.A.v0 = InfinitePlace.mk D.what₂.embLL := R.hv0
  have hcx : ∃ a : D.what₂.LL, star (A3.A.v0.embedding a) ≠ A3.A.v0.embedding a := by
    haveI := (GlobalTheory.ptField_main D).1
    exact exists_nonreal _ (IsTotallyComplex.isComplex _)
  refine majAt_eq_of_diag _ _ _ _ _ Z.eRR0.toLinearMap hcx ?_ x y
  intro x
  have hR := PrincipalLevelLattice.majorant_at_base_place_eq_inner (R.toCx3 F) F.cr false h2 hn x x

  set w := (R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding x) with hw
  set z := X0.s.jEE (Z.eRR0 x) with hz
  set u : R.HE.H := Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) w with hu
  have hjE := Z.jEE0 x
  rw [← hz] at hjE
  change _ = PiTensorProduct.lift (R.HE.e u) at hjE
  have hee := Y.tied.base.ee z z
  have hnorm := X0.s.jEE_norm (Z.eRR0 x)
  have hL : Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 x) = ⟪z, z⟫_ℂ := by
    rw [majAt_self_eq, hv0, hnorm, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hK : ⟪z, z⟫_ℂ = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ⟪u, u⟫_ℂ := by
    by_cases hT : R.HE.e (u) = 0
    · have h0 : u = 0 := hE.1 (hT.trans (map_zero _).symm)
      have hz0 : Y.Iz.jE z = 0 := by
        apply Subtype.ext
        rw [hjE, hT, map_zero]
        rfl
      have hz1 : z = 0 := Y.Iz.jE.map_eq_zero_iff.1 hz0
      rw [hz1, h0]
      simp
    · obtain ⟨v, hv⟩ := GlobalTheory.KapRedII.exists_vec_of_ne hT
      rw [hee]
      show ipMT (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 false)⁻¹ • R.ν0) R.fd0 _ _ = _
      rw [hjE, ipMT, LinearEquiv.symm_apply_apply, GlobalTheory.KapRedII.ipM_smul_of_vec _ _ _ _ _ (inv_pos.2 hn) v hv, ← hE.2.2]
  change Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 x) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).XE F.cr false) A3.fam3.base3.v0 x x
  rw [hL, hK]
  erw [hR]
  have hc : ∀ (s : Bool) (c : ℂ), starRingEnd ℂ c = c → Formalism.IndefR.Links.cj s c = c := by
    intro s c h
    cases s <;> simp [Formalism.IndefR.Links.cj, h]
  change _ = _ * Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) ⟪u, u⟫_ℂ
  rw [hc _ _ (inner_conj_symm u u)]
  rfl

end GlobalTheory.Mem.R3.MetBase
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.hilbert_inner_liftForms_eq_base_level_hermitian : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (i : Fin D.R.m) (t : T) (x y : Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL), (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) := by
  first | exact @GlobalTheory.Mem.R3.liftForm_inner_eq_hform | exact GlobalTheory.Mem.R3.liftForm_inner_eq_hform | (intros; apply GlobalTheory.Mem.R3.liftForm_inner_eq_hform <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (x y : Fin (rDim D A (F.lvl b).P (F.lvl b).ψ t) → D.what₂.LL), (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * ⟪R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x), R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A (F.lvl b).P (F.lvl b).ψ t) x y) := by
  first | exact @GlobalTheory.Mem.TopGram.topGram | exact GlobalTheory.Mem.TopGram.topGram | (intros; apply GlobalTheory.Mem.TopGram.topGram <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.liftLevelForm_orthogonal_killed_by_thetaMap : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0 := by
  first | exact @GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth | exact GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth | (intros; apply GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.weilFock_vector_eigen_of_finite_step_eigen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (t : T) (k : ℕ), k + 1 < D.R.m → ∀ κ ∈ GfC (Yc D k), ∀ κ' ∈ GfC (Yc D (k + 1)), ∀ c : ℂ, R.ωY t k (κ, κ') (R.vY t k) = c • R.vY t k → ∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ := by
  first | exact @GlobalTheory.Mem.R3.DTheta.StepLevFock.om_ptY_of_finite | exact GlobalTheory.Mem.R3.DTheta.StepLevFock.om_ptY_of_finite | (intros; apply GlobalTheory.Mem.R3.DTheta.StepLevFock.om_ptY_of_finite <;> assumption)
end
