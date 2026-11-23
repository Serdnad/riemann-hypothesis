module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section InterNumPointLemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem interNumPoint_restrLen_eq_finrank (y : Fin (N + 1) → Ω) {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (F : SubSystem k y Ω) : restrLen (primeOf (S := k) y) F = Module.finrank k F.secs := by
  have hid : ∀ I : Chart y, idealMod (x := y) (primeOf (S := k) y) I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
    rw [(mem_primeOf_of_isHomogeneous y hfe).mp hf, zero_div]
  have hbot : ∀ I : Chart y, (F.twist (idealSys y (primeOf (S := k) y))).sub I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨q, hq, z, _, rfl⟩
    have hq' : q ∈ idealMod (x := y) (primeOf (S := k) y) I := hq
    rw [hid I, Submodule.mem_bot] at hq'
    rw [hq', zero_smul]
  have hsecs : (F.twist (idealSys y (primeOf (S := k) y))).secs = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have h1 := (Submodule.mem_iInf _).mp hz (singleChart hyj)
    rw [Submodule.restrictScalars_mem, hbot] at h1
    exact h1
  unfold restrLen
  rw [hsecs, Submodule.comap_bot, Submodule.ker_subtype,
    (Submodule.quotEquivOfEqBot (⊥ : Submodule k F.secs) rfl).length_eq, Module.length_eq_rank]
  rfl

theorem interNumPoint_interSum_eq (y : Fin (N + 1) → Ω) {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (L : Fin 0 → SubSystem k y Ω) (c : ℕ) :
    interSum (primeOf (S := k) y) L c = Module.finrank k (twistSys k y (c : ℤ)).secs := by
  have huniv : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by decide
  have h0 : tensorSub L ∅ = twistSys k y 0 := rfl
  rw [interSum, huniv, Finset.sum_singleton, h0, twistSys_zero_twist,
    interNumPoint_restrLen_eq_finrank y hyj]
  simp

end InterNumPointLemmas

theorem InterNumPoint.proof (hHP : HilbertPoint.Statement.{u, w}) : InterNumPoint.Statement.{u, w} := by
  intro k _ Ω _ _ N y hsub L
  obtain ⟨_, hdim, hsecs⟩ := hHP k Ω N y hsub
  obtain ⟨j, hj⟩ := hsub.relevant
  have hyj : y j ≠ 0 := by
    intro h
    apply hj
    rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j), aeval_X]
    exact h
  have hev : (fun _ : ℕ => (Module.finrank k (funField (k := k) y) : ℤ)) =ᶠ[atTop]
      interSum (primeOf (S := k) y) L := by
    filter_upwards [hdim, hsecs] with n hn hs
    rw [interNumPoint_interSum_eq y hyj, hs, hn]
  exact (tendsto_const_nhds.congr' hev).limUnder_eq

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

section RestrictGenAux

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {K' : Type} [Field K'] [Algebra F K']
  (R : Subalgebra F Ω) (σ : R →ₐ[F] K')


open Classical in
def RestrictGen.resid (a : Ω) : K' := if h : a ∈ R then σ ⟨a, h⟩ else 0

theorem RestrictGen.resid_of_mem {a : Ω} (h : a ∈ R) : RestrictGen.resid R σ a = σ ⟨a, h⟩ := dif_pos h

theorem RestrictGen.resid_zero : RestrictGen.resid R σ 0 = 0 := by
  rw [RestrictGen.resid_of_mem R σ (zero_mem R)]
  exact map_zero σ

theorem RestrictGen.resid_add {a b : Ω} (ha : a ∈ R) (hb : b ∈ R) :
    RestrictGen.resid R σ (a + b) = RestrictGen.resid R σ a + RestrictGen.resid R σ b := by
  rw [RestrictGen.resid_of_mem R σ ha, RestrictGen.resid_of_mem R σ hb,
    RestrictGen.resid_of_mem R σ (add_mem ha hb), ← map_add]
  rfl

theorem RestrictGen.resid_mul {a b : Ω} (ha : a ∈ R) (hb : b ∈ R) :
    RestrictGen.resid R σ (a * b) = RestrictGen.resid R σ a * RestrictGen.resid R σ b := by
  rw [RestrictGen.resid_of_mem R σ ha, RestrictGen.resid_of_mem R σ hb,
    RestrictGen.resid_of_mem R σ (mul_mem ha hb), ← map_mul]
  rfl

end RestrictGenAux


open RestrictGen in
theorem RestrictGen.proof : RestrictGen.Statement := by
  intro F _ N Ω _ _ x K' _ _ x' hxy R σ hσ Q Q' c H ρ w w' hw' hQ hQ' hH
  classical
  have hσ' : ∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 →
      aeval x f / aeval x g ∈ R ∧ resid R σ (aeval x f / aeval x g) = aeval x' f / aeval x' g := by
    intro f g m hf hg hg'
    obtain ⟨h, e⟩ := hσ f g m hf hg hg'
    exact ⟨h, by rw [resid_of_mem R σ h, e]⟩
  by_cases hx' : ∃ j, x' j ≠ 0
  swap
  · simp only [not_exists, not_not] at hx'
    have hI : IsEmpty (Kleiman.Chart x') := ⟨fun I => by
      obtain ⟨i, hi⟩ := I.2.1
      exact (Kleiman.mem_support x').mp (I.2.2 hi) (hx' i)⟩
    exact ⟨0, ⟨fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I⟩⟩
  obtain ⟨j, hj⟩ := hx'
  have hxj : x j ≠ 0 := hxy j hj
  set r : Ω → K' := fun q => resid R σ (q * x j ^ c * w) / (x' j ^ c * w') with hr

  have hrat : ∀ i, x' i ≠ 0 → (x j / x i) ^ c ∈ R ∧ resid R σ ((x j / x i) ^ c) = (x' j / x' i) ^ c := by
    intro i hi
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have := hσ' (X j ^ n) (X i ^ n) n (isHomogeneous_X_pow (R := F) j n) (isHomogeneous_X_pow (R := F) i n)
        (by simpa using pow_ne_zero n hi)
      simp only [map_pow, aeval_X] at this
      simpa [zpow_natCast, div_pow] using this
    · have := hσ' (X i ^ n) (X j ^ n) n (isHomogeneous_X_pow (R := F) i n) (isHomogeneous_X_pow (R := F) j n)
        (by simpa using pow_ne_zero n hj)
      simp only [map_pow, aeval_X] at this
      simpa [zpow_neg, zpow_natCast, div_pow, inv_div] using this

  have hchart : ∀ (I : Kleiman.Chart x') (a : Ω), a ∈ Kleiman.chartRing F x (Kleiman.liftChart hxy I) →
      a ∈ R ∧ resid R σ a ∈ Kleiman.chartRing F x' I := by
    rintro I a ⟨f, s, e, hs, hf, hse, rfl⟩
    obtain ⟨h1, h2⟩ := hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)
    exact ⟨h1, h2 ▸ ⟨f, s, e, hs, hf, hse, rfl⟩⟩

  have hspan : ∀ (I : Kleiman.Chart x') (z : Ω),
      z ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H →
      z * w ∈ R ∧ resid R σ (z * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
    intro I z hz
    induction hz using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨hm, e⟩ := hH h hh
      refine ⟨hm, ?_⟩
      rw [resid_of_mem R σ hm, e, mul_div_cancel_right₀ _ hw']
      exact Submodule.subset_span ⟨h, hh, rfl⟩
    | zero =>
      rw [zero_mul, resid_zero, zero_div]
      exact ⟨zero_mem R, zero_mem _⟩
    | add a b _ _ ha hb =>
      refine ⟨by rw [add_mul]; exact add_mem ha.1 hb.1, ?_⟩
      rw [add_mul, resid_add R σ ha.1 hb.1, add_div]
      exact add_mem ha.2 hb.2
    | smul a z _ hz =>
      obtain ⟨ha1, ha2⟩ := hchart I a a.2
      rw [Kleiman.chartRing_smul_def, mul_assoc]
      refine ⟨mul_mem ha1 hz.1, ?_⟩
      rw [resid_mul R σ ha1 hz.1, mul_div_assoc]
      exact Submodule.smul_mem _ (⟨_, ha2⟩ : Kleiman.chartRing F x' I) hz.2

  have hkey : ∀ (I : Kleiman.Chart x') (i : Fin (N + 1)), i ∈ I.1 → ∀ q ∈ Q.sub (Kleiman.liftChart hxy I),
      q * x j ^ c * w ∈ R ∧ r q * x' i ^ c = resid R σ (x i ^ c * q * w) / w' ∧
      resid R σ (x i ^ c * q * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
    intro I i hi q hq
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    have hxi : x i ≠ 0 := hxy i hx'i
    have hz : x i ^ c * q ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H := by
      rw [← hQ (Kleiman.liftChart hxy I)]
      exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mpr ⟨q, hq, rfl⟩
    obtain ⟨hz1, hz2⟩ := hspan I _ hz
    obtain ⟨hr1, hr2⟩ := hrat i hx'i
    have heq : q * x j ^ c * w = (x j / x i) ^ c * (x i ^ c * q * w) := by
      rw [div_zpow]
      field_simp
    refine ⟨heq ▸ mul_mem hr1 hz1, ?_, hz2⟩
    rw [hr]
    dsimp only
    rw [heq, resid_mul R σ hr1 hz1, hr2, div_zpow]
    field_simp
  have hmem : ∀ (I : Kleiman.Chart x'), ∀ q ∈ Q.sub (Kleiman.liftChart hxy I), r q ∈ Q'.sub I := by
    intro I q hq
    obtain ⟨i, hi⟩ := I.2.1
    obtain ⟨-, e, hm⟩ := hkey I i hi q hq
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    rw [← hQ' I] at hm
    obtain ⟨y, hy, hy'⟩ := (TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mp hm
    have h' : r q * x' i ^ c = y * x' i ^ c := by
      rw [e, hy', smul_eq_mul, mul_comm]
    rw [mul_right_cancel₀ (zpow_ne_zero c hx'i) h']
    exact hy
  refine ⟨r, ⟨hmem, ?_, ?_, ?_⟩⟩
  · intro I q hq q' hq'
    obtain ⟨i, hi⟩ := I.2.1
    have h1 := (hkey I i hi q hq).1
    have h2 := (hkey I i hi q' hq').1
    rw [hr]
    dsimp only
    rw [add_mul, add_mul, resid_add R σ h1 h2, add_div]
  · intro I q hq f s e hs hf hse
    obtain ⟨i, hi⟩ := I.2.1
    have h1 := (hkey I i hi q hq).1
    obtain ⟨ha1, ha2⟩ := hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)
    have hm : aeval x f / aeval x s * q * x j ^ c * w = aeval x f / aeval x s * (q * x j ^ c * w) := by ring
    rw [hr]
    dsimp only
    rw [hm, resid_mul R σ ha1 h1, ha2, mul_div_assoc]
  · intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      exact hmem I q hq
    · intro t ht
      have ht' : x' i ^ c * t ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
        rw [← hQ' I]
        exact (TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mpr ⟨t, ht, rfl⟩
      have hall : ∀ u ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H),
          x' i ^ (-c) * u ∈ Submodule.span (Kleiman.chartRing F x' I) (r '' Q.sub (Kleiman.liftChart hxy I)) := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨h, hh, rfl⟩ := hu
          have hh' : h ∈ (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub (Kleiman.liftChart hxy I) := by
            rw [hQ]
            exact Submodule.subset_span hh
          obtain ⟨y, hy, rfl⟩ :=
            (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mp hh'
          obtain ⟨hm, e⟩ := hH _ hh
          obtain ⟨-, e', -⟩ := hkey I i hi y hy
          have e'' : resid R σ (x i ^ c * y * w) = ρ (x i ^ c • y) * w' := (resid_of_mem R σ hm).trans e
          rw [e'', mul_div_cancel_right₀ _ hw'] at e'
          have : x' i ^ (-c) * ρ (x i ^ c • y) = r y := by
            rw [← e', zpow_neg]
            field_simp
          rw [this]
          exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero => rw [mul_zero]; exact zero_mem _
        | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
        | smul a u _ hu =>
          rw [Kleiman.chartRing_smul_def, mul_left_comm]
          exact Submodule.smul_mem _ a hu
      have := hall _ ht'
      rwa [← mul_assoc, ← zpow_add₀ hx'i, neg_add_cancel, zpow_zero, one_mul] at this

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem interSum_one (pp : Ideal (Poly S N)) (L : SubSystem S x Ω) (c : ℕ) :
    interSum pp ![L] c = restrLen pp (L.twist (twistSys S x (c : ℤ))) -
      restrLen pp ((twistSys S x 0).twist (twistSys S x (c : ℤ))) := by
  have h0 : tensorSub ![L] ∅ = twistSys S x 0 := by simp [tensorSub]
  have h1 : tensorSub ![L] {0} = L := by
    simp [tensorSub, List.finRange_succ, twistSys_zero_twist]
  have huniv : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  rw [interSum, huniv, Finset.sum_pair (by decide), h0, h1]
  simp only [Finset.card_empty, Finset.card_singleton]
  norm_num
  ring

theorem restrLen_of_irrelevant (pp : Ideal (Poly S N)) (hX : ∀ i, (X i : Poly S N) ∈ pp)
    (F : SubSystem S x Ω) : restrLen pp F = 0 := by
  have hle : F.secs ≤ (F.twist (idealSys x pp)).secs := by
    intro y hy
    simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
      Submodule.subset_span ⟨X i, X i, 1, hX i, X_mem_monos hi, isHomogeneous_X S i,
        isHomogeneous_X S i, by rw [aeval_X, div_self hxi]⟩
    exact Submodule.subset_span ⟨1, h1, y, hy I, (one_smul Ω y).symm⟩
  have hs : Subsingleton (F.secs ⧸ ((F.twist (idealSys x pp)).secs).comap F.secs.subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    intro y _
    exact hle y.2
  unfold restrLen
  rw [Module.length_eq_zero_iff.mpr hs]
  rfl

theorem ringKrullDim_quot_succ_le {G pp : Ideal (Poly S N)} [G.IsPrime] (hle : G ≤ pp) {f : Poly S N}
    (hfp : f ∈ pp) (hfG : f ∉ G) : ringKrullDim (Poly S N ⧸ pp) + 1 ≤ ringKrullDim (Poly S N ⧸ G) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ f) ?_ ?_
  · apply mem_nonZeroDivisors_of_ne_zero
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hfp

theorem withBot_le_one_of_le_two {a : WithBot ℕ∞} (h2 : a ≤ 2)
    (hne : a ≠ ((1 + 1 : ℕ) : WithBot ℕ∞)) : a ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h2 (by decide)
    | coe n =>
      have h2a : (n : ℕ∞) ≤ 2 := WithBot.coe_le_coe.mp h2
      have h2' : n ≤ 2 := by exact_mod_cast h2a
      have hne' : n ≠ 2 := fun h => hne (by rw [h]; rfl)
      have h1 : (n : ℕ∞) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
      exact WithBot.coe_le_coe.mpr h1

theorem withBot_not_succ_le {a b : WithBot ℕ∞} (ha : a = ((1 + 1 : ℕ) : WithBot ℕ∞)) (hab : a + 1 ≤ b)
    (hb : b ≤ 2) : False := by
  subst ha
  have := hab.trans hb
  exact absurd this (by decide)

end Lemmas


open Classical in
theorem CycleSplit.proof (hF : CycleSplit.Filt.Statement.{u, w}) (hCu : CycleSplit.Curve.Statement.{u, w})
    (hSm : CycleSplit.Small.Statement.{u, w}) : CycleSplit.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x M 𝔪 h𝔪 J hJhom hJle hJm hdim
  obtain ⟨n, pp, d, hpp, hcount, hres⟩ := hF S Ω N x 𝔪 h𝔪 J hJhom hJle hJm

  let v : Ideal (Poly S N) → ℤ := fun G => if IsSubvar x G 1 then interNum G ![M.toSubSystem] else 0

  have hdimj : ∀ j, ringKrullDim (Poly S N ⧸ pp j) ≤ 2 := by
    intro j
    have := (hpp j).1
    obtain ⟨G, hG, hGle⟩ := Ideal.exists_minimalPrimes_le (hpp j).2.2
    exact (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hGle)
      (Ideal.Quotient.factor_surjective hGle)).trans (hdim G hG)

  have hmin : ∀ j, IsSubvar x (pp j) 1 → pp j ∈ J.minimalPrimes := by
    intro j hsv
    have := (hpp j).1
    obtain ⟨G, hG, hGle⟩ := Ideal.exists_minimalPrimes_le (hpp j).2.2
    by_cases hGe : G = pp j
    · rw [← hGe]; exact hG
    · exfalso
      have : G.IsPrime := hG.1.1
      obtain ⟨f, hfp, hfG⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hGle hGe)
      exact withBot_not_succ_le hsv.dim (ringKrullDim_quot_succ_le hGle hfp hfG) (hdim G hG)

  have hpiece : ∀ j, ∀ᶠ c : ℕ in atTop, interSum (pp j) ![M.toSubSystem] c = v (pp j) := by
    intro j
    obtain ⟨hjp, hjh, hJj⟩ := hpp j
    by_cases hsv : IsSubvar x (pp j) 1
    · simp only [v, if_pos hsv]
      exact hCu S Ω N x M 𝔪 h𝔪 (pp j) hsv (hJm.trans hJj)
    · simp only [v, if_neg hsv]
      by_cases hrel : ∃ i, (X i : Poly S N) ∉ pp j
      · refine hSm S Ω N x M 𝔪 h𝔪 (pp j) hjp hjh (hJle.trans hJj) (hJm.trans hJj) ?_
        exact withBot_le_one_of_le_two (hdimj j) fun h => hsv ⟨hjp, hjh, hJle.trans hJj, hrel, h⟩
      · push Not at hrel
        exact Eventually.of_forall fun c => by
          rw [interSum_one, restrLen_of_irrelevant _ hrel, restrLen_of_irrelevant _ hrel, sub_zero]

  have hshift : ∀ j, ∀ᶠ c : ℕ in atTop,
      0 ≤ (c : ℤ) + d j ∧ interSum (pp j) ![M.toSubSystem] ((c : ℤ) + d j).toNat = v (pp j) := by
    intro j
    have ht : Tendsto (fun c : ℕ => ((c : ℤ) + d j).toNat) atTop atTop := by
      refine tendsto_atTop_atTop.mpr fun b => ⟨b + (d j).natAbs, fun a ha => ?_⟩
      omega
    exact ((eventually_ge_atTop (d j).natAbs).and (ht.eventually (hpiece j))).mono
      fun c hc => ⟨by omega, hc.2⟩
  have hall := Filter.eventually_all.mpr hshift
  filter_upwards [hall, hres M, hres (twistBundle S x 0)] with c hc hM h0
  have h0' : restrLen J ((twistSys S x 0).twist (twistSys S x (c : ℤ))) =
      ∑ j, restrLen (pp j) ((twistSys S x 0).twist (twistSys S x ((c : ℤ) + d j))) := h0

  have hsum : interSum J ![M.toSubSystem] c = ∑ j, v (pp j) := by
    rw [interSum_one, hM, h0', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← (hc j).2, interSum_one, Int.toNat_of_nonneg (hc j).1]
  rw [hsum, Finset.sum_comp (fun G => v G) pp]

  symm
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image pp) ?_]
  · refine Finset.sum_congr rfl fun G hG => ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hG
    by_cases hsv : IsSubvar x (pp j) 1
    · have hm := hmin j hsv
      have : (pp j).IsPrime := (hpp j).1
      rw [dite_eq_left ⟨hm, hsv⟩, nsmul_eq_mul]
      simp only [v, if_pos hsv]
      rw [← hcount (pp j) hm, ENat.toNat_natCast]
    · rw [dite_eq_right fun h => hsv h.2]
      simp only [v, if_neg hsv, smul_zero]
  · intro G hG
    rw [Function.mem_support] at hG
    split_ifs at hG with h
    · have : G.IsPrime := h.1.1.1
      have hc0 : (cutMult J G).toNat ≠ 0 := by
        intro h0; rw [h0] at hG; simp at hG
      rw [← hcount G h.1, ENat.toNat_natCast] at hc0
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc0)
      rw [Finset.mem_filter] at hj
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact ⟨j, hj.2⟩
    · exact absurd rfl hG

end GroundTheory.Heights₂.Heights.Kleiman
end
