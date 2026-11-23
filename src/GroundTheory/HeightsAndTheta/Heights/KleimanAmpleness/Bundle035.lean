module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropTerm
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeAway
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle003

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftRelDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
      relDim (segreLift ι F W) = relDim W

theorem SegreLiftRelDim.hyps : IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :=
  NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

theorem CycleSplit.Filt.telescope : ∀ {n : ℕ} (a : Fin (n + 1) → ℤ) (b : Fin n → ℤ),
    (∀ l : Fin n, a l.castSucc = a l.succ + b l) → a 0 = a (Fin.last n) + ∑ l, b l
  | 0, a, b, _ => by simp
  | n + 1, a, b, h => by
    have ih := CycleSplit.Filt.telescope (fun m => a m.castSucc) (fun l => b l.castSucc)
      (fun l => by
        have := h l.castSucc
        simpa only [Fin.succ_castSucc] using this)
    have hl := h (Fin.last n)
    rw [Fin.succ_last] at hl
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_zero] at ih
    linarith


open SectionCount.Drop.Filt in
theorem CycleSplit.Filt.proof (hS : CycleSplit.Filt.Step.Statement.{u, w}) :
    CycleSplit.Filt.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x 𝔪 h𝔪 J hJhom hJx hJ𝔪

  have hkill : ∀ p ∈ primeOf (S := S) x, ∀ m : Poly S N ⧸ J, p • m = 0 := by
    intro p hp m
    obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
    change Ideal.Quotient.mk J (p * m) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (J.mul_mem_right m (hJx hp))
  obtain ⟨⟨Fl⟩, hcount⟩ := PrimeFiltration.Exists.proof.{u, u, w} S Ω N x (Poly S N ⧸ J)
    (quotGraded J hJhom) (finite_quot J) hkill
  rw [Ideal.annihilator_quotient] at hcount
  have hann : ∀ l, J ≤ Fl.prime l := fun l => by
    have := Fl.ann_le l; rwa [Ideal.annihilator_quotient] at this

  have hlift : ∀ l : Fin Fl.n, ∃ (g : Poly S N) (e : ℕ), g.IsHomogeneous e ∧
      Ideal.Quotient.mk J g = Fl.gen l := by
    intro l
    obtain ⟨g, hg, hgm⟩ := mem_quotGraded_piece.mp (Fl.gen_mem l)
    by_cases h0 : 0 ≤ Fl.deg l
    · refine ⟨g, (Fl.deg l).toNat, isHomogeneous_of_isWeightedHomogeneous_one ?_, hgm⟩
      rwa [Int.toNat_of_nonneg h0]
    · refine ⟨0, 0, isHomogeneous_zero _ _ _, ?_⟩
      have hg0 : g = 0 := by
        ext m
        by_contra hne
        have h1 := hg hne
        rw [weight_one_int] at h1
        omega
      rw [← hgm, hg0]
  choose g eK hgH hgm using hlift

  let Jk : Fin (Fl.n + 1) → Ideal (Poly S N) := fun l => (Fl.step l).comap J.mkQ
  have hJ0 : Jk 0 = J := by
    simp only [Jk, Fl.step_zero, Submodule.comap_bot, Submodule.ker_mkQ]
  have hJlast : Jk (Fin.last _) = ⊤ := by
    simp only [Jk, Fl.step_last, Submodule.comap_top]
  have hmkQ : ∀ (c : Poly S N) (l : Fin Fl.n), J.mkQ (c * g l) = c • Fl.gen l := by
    intro c l
    rw [← hgm l]
    rfl
  have hJsucc : ∀ l : Fin Fl.n, Jk l.succ = Jk l.castSucc ⊔ Ideal.span {g l} := by
    intro l
    ext f
    simp only [Jk, Fl.step_succ, Submodule.mem_comap]
    constructor
    · intro hf
      obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.mp hf
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      have h1 : f - c * g l ∈ (Fl.step l.castSucc).comap J.mkQ := by
        rw [Submodule.mem_comap, map_sub, hmkQ, ← hay, add_sub_cancel_right]
        exact ha
      have h2 := Submodule.add_mem_sup h1 (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self (g l)))
      rwa [sub_add_cancel] at h2
    · intro hf
      obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      rw [map_add (f := _), hmkQ]
      exact Submodule.add_mem_sup ha (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hJkp : ∀ (l : Fin Fl.n) (f : Poly S N), f ∈ Fl.prime l ↔ f * g l ∈ Jk l.castSucc := by
    intro l f
    rw [Fl.mem_prime, ← hgm l]
    exact Iff.rfl
  have hJk_ge : ∀ l, J ≤ Jk l := fun l f hf => by
    simp only [Jk, Submodule.mem_comap, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero J).mpr hf, zero_mem]
  have hJk_hom : ∀ l, ∀ f ∈ Jk l, ∀ d : ℕ, homogeneousComponent d f ∈ Jk l := by
    intro l
    induction l using Fin.induction with
    | zero => rw [hJ0]; exact hJhom
    | succ l ih =>
      rw [hJsucc l]
      exact hom_sup ih (hom_span fun g' hg' => ⟨eK l, by rw [Set.mem_singleton_iff.mp hg']; exact hgH l⟩)
  refine ⟨Fl.n, Fl.prime, fun l => -((eK l : ℕ) : ℤ),
    fun l => ⟨Fl.isPrime l, Fl.isHomogeneous l, hann l⟩, fun G _ hG => hcount Fl G hG, fun Q => ?_⟩

  have hstep : ∀ l : Fin Fl.n, ∀ᶠ c : ℕ in atTop,
      restrLen (Jk l.castSucc) (Q.twist (twistSys S x (c : ℤ))) =
        restrLen (Jk l.succ) (Q.twist (twistSys S x (c : ℤ))) +
          restrLen (Fl.prime l) (Q.twist (twistSys S x ((c : ℤ) - (eK l : ℕ)))) := by
    intro l
    rw [hJsucc l]
    exact hS S Ω N x 𝔪 h𝔪 (Jk l.castSucc) (Fl.prime l) (g l) (eK l) (hJk_hom _)
      (hJx.trans (hJk_ge _)) (hJ𝔪.trans (hJk_ge _)) (hgH l) (Fl.isHomogeneous l) (hJkp l) Q
  filter_upwards [Filter.eventually_all.mpr hstep] with c hc
  have htel := CycleSplit.Filt.telescope
    (fun m => restrLen (Jk m) (Q.twist (twistSys S x (c : ℤ))))
    (fun l => restrLen (Fl.prime l) (Q.twist (twistSys S x ((c : ℤ) - (eK l : ℕ))))) hc
  simp only [hJ0, hJlast, restrLen_of_irrelevant ⊤ (fun i => Submodule.mem_top), zero_add] at htel
  rw [htel]
  simp only [sub_eq_add_neg]

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem SectionNonvanish.proof : SectionNonvanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hpp _ hle ⟨i, hi⟩ D hD
  have hxi : x i ≠ 0 := fun h0 =>
    hi (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i)).mpr (by rw [aeval_X, h0])))
  refine not_forall_not.mp fun hcon => ?_
  let I : Chart x := singleChart hxi
  have hsec : ∀ s ∈ D.toSubSystem.secs, s ∈ idealMod pp I * D.toSubSystem.sub I := by
    intro s hs
    by_contra hs'
    refine hcon s ⟨hs, I, ?_⟩
    rwa [SubSystem.twist_sub_eq_mul_of_line]
  obtain ⟨P, hP⟩ := D.invertible I
  have hsub : D.toSubSystem.sub I ≤ idealMod pp I * D.toSubSystem.sub I := by
    rw [← hD I, Submodule.span_le]
    intro s hs
    rw [hD I]
    exact hsec s hs
  have hone : (1 : Submodule (chartRing k x I) Ω) ≤ idealMod pp I :=
    calc (1 : Submodule (chartRing k x I) Ω) = D.toSubSystem.sub I * P := hP.symm
      _ ≤ idealMod pp I * D.toSubSystem.sub I * P := mul_le_mul' hsub le_rfl
      _ = idealMod pp I := by rw [mul_assoc]; erw [hP]; rw [mul_one]
  have h1 : (1 : Ω) ∈ idealMod pp I := hone (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  refine SectionCount.Drop.Term.one_not_mem_idealMod hpp hle (I := I) (fun j hj => ?_) h1
  obtain rfl : j = i := Finset.mem_singleton.mp hj
  exact hi

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SectionMulInj

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_of_mem_idealMod (J : Ideal (Poly S N)) (I : Chart x) {z : Ω} (hz : z ∈ idealMod (x := x) J I) :
    ∃ (G m : Poly S N) (e : ℕ), G ∈ J ∧ m ∈ monos I.1 ∧ G.IsHomogeneous e ∧ m.IsHomogeneous e ∧
      z = aeval x G / aeval x m := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero => exact ⟨0, 1, 0, J.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨G, m, e, hG, hm, hGe, hme, rfl⟩ := ha
    obtain ⟨G', m', e', hG', hm', hGe', hme', rfl⟩ := hb
    refine ⟨G * m' + m * G', m * m', e + e', J.add_mem (J.mul_mem_right _ hG) (J.mul_mem_left _ hG'),
      mul_mem hm hm', (hGe.mul hme').add (hme.mul hGe'), hme.mul hme', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hm) (eval_ne_zero_of_mem_monos I hm')]
    simp only [map_add (f := _), map_mul]
  | smul r a _ ha =>
    obtain ⟨F, m₀, e₀, hm₀, hF, hm₀e, hr⟩ := r.2
    obtain ⟨G, m, e, hG, hm, hGe, hme, rfl⟩ := ha
    refine ⟨F * G, m₀ * m, e₀ + e, J.mul_mem_left _ hG, mul_mem hm₀ hm, hF.mul hGe, hm₀e.mul hme, ?_⟩
    rw [chartRing_smul_def, hr, map_mul, map_mul, div_mul_div_comm]


omit [Algebra S Ω] in
theorem not_mem_of_mem_monos {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) {I : Chart x}
    (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {m : Poly S N} (hm : m ∈ monos I.1) : m ∉ pp := by
  induction hm using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    exact hX j (by exact_mod_cast hj)
  | one => exact fun h => hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  | mul a b _ _ ha hb => exact fun h => (hpp.mem_or_mem h).elim ha hb

theorem mem_of_div_mem_idealMod {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {F m : Poly S N} {e : ℕ} (hm : m ∈ monos I.1)
    (hF : F.IsHomogeneous e) (hme : m.IsHomogeneous e) (h : aeval x F / aeval x m ∈ idealMod (x := x) pp I) :
    F ∈ pp := by
  obtain ⟨G, m', e', hG, hm', hGe, hme', heq⟩ := exists_of_mem_idealMod pp I h
  have h0 := eval_ne_zero_of_mem_monos I hm
  have h0' := eval_ne_zero_of_mem_monos I hm'
  have hdiff : F * m' - m * G ∈ primeOf (S := S) x := by
    have hhom : (F * m' - m * G).IsHomogeneous (e + e') := (hF.mul hme').sub (hme.mul hGe)
    rw [mem_primeOf_of_isHomogeneous x hhom, map_sub, map_mul, map_mul, sub_eq_zero]
    rw [div_eq_div_iff h0 h0'] at heq
    rw [heq, mul_comm]
  have hFm : F * m' ∈ pp := by
    have := pp.add_mem (hZ hdiff) (pp.mul_mem_left m hG)
    rwa [sub_add_cancel] at this
  exact (hpp.mem_or_mem hFm).resolve_right (not_mem_of_mem_monos hpp hX hm')

theorem mem_or_mem {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) (a b : chartRing S x I)
    (h : (a : Ω) * b ∈ idealMod (x := x) pp I) :
    (a : Ω) ∈ idealMod (x := x) pp I ∨ (b : Ω) ∈ idealMod (x := x) pp I := by
  obtain ⟨F, m, e, hm, hF, hme, ha⟩ := a.2
  obtain ⟨F', m', e', hm', hF', hme', hb⟩ := b.2
  rw [ha, hb, div_mul_div_comm, ← map_mul, ← map_mul] at h
  have := mem_of_div_mem_idealMod hpp hZ hX (mul_mem hm hm') (hF.mul hF') (hme.mul hme') h
  refine (hpp.mem_or_mem this).imp (fun hF0 => ?_) (fun hF0 => ?_)
  · rw [ha]; exact Submodule.subset_span ⟨F, m, e, hF0, hm, hF, hme, rfl⟩
  · rw [hb]; exact Submodule.subset_span ⟨F', m', e', hF0, hm', hF', hme', rfl⟩

end SectionMulInj


open SectionMulInj in
theorem SectionMulInj.proof : SectionMulInj.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hpp hhom hZ D M s ⟨f, hf, hfp⟩ I y hy hsy
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change y ∈ idealMod (x := x) pp I * M.sub I
  by_cases hX : ∃ j ∈ I.1, (X j : Poly k N) ∈ pp
  · obtain ⟨j, hj, hXj⟩ := hX
    have := StepThree.OnW.Gen.sub_le_twist_idealSys_of_mem M.toSubSystem I hj hXj hy
    rwa [SubSystem.twist_sub_eq_mul_of_line] at this
  push Not at hX
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)

  obtain ⟨e, he⟩ : ∃ e, homogeneousComponent e f ∉ pp := by
    by_contra hall
    push Not at hall
    exact hfp (by rw [← sum_homogeneousComponent f]; exact pp.sum_mem fun d _ => hall d)
  set g : chartRing k x I := ⟨_, StepThree.Away.div_pow_mem_chartRing I hi
    (homogeneousComponent_isHomogeneous e f)⟩ with hg
  have hgI : (g : Ω) ∉ idealMod (x := x) pp I := fun h => he <| by
    refine mem_of_div_mem_idealMod hpp hZ hX (pow_mem (X_mem_monos hi) e)
      (homogeneousComponent_isHomogeneous e f) (isHomogeneous_X_pow i e) ?_
    rw [map_pow, aeval_X]; exact h

  have hgD : Submodule.span (chartRing k x I) {(g : Ω)} * D.sub I ≤ Submodule.span _ {s} := by
    rw [Submodule.mul_le]
    intro a ha δ hδ
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
      (StepThree.Away.homogeneousComponent_mul_mem D.toSubSystem s I hi hf e δ hδ)
    rw [Submodule.mem_span_singleton]
    refine ⟨r * t, ?_⟩
    have hpow : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    rw [chartRing_smul_def] at ht
    change ((r * t : chartRing k x I) : Ω) * s = ((r : Ω) * (g : Ω)) * δ
    rw [Subalgebra.coe_mul, hg]
    change (r : Ω) * t * s = (r : Ω) * (aeval x (homogeneousComponent e f) / x i ^ e) * δ
    rw [mul_assoc (r : Ω), mul_assoc (r : Ω)]
    congr 1
    rw [div_mul_eq_mul_div, eq_div_iff hpow, ← ht]
    ring
  obtain ⟨D', hD'⟩ := D.invertible I
  obtain ⟨M', hM'⟩ := M.invertible I
  have h1D : (1 : Ω) ∈ D.sub I * D' := by rw [hD']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩

  have hgs : (g : Ω) ∈ Submodule.span (chartRing k x I) {s} * D' := by
    have := Submodule.mul_mem_mul (Submodule.mem_span_singleton_self (g : Ω)) h1D
    rw [mul_one, ← mul_assoc] at this
    exact mul_le_mul' hgD le_rfl this
  have hsy' : s * y ∈ idealMod (x := x) pp I * (D.sub I * M.sub I) := by
    rw [SubSystem.twist_sub_eq_mul_of_line, SubSystem.twist_sub_eq_mul_of_line] at hsy
    exact hsy
  have hgy : Submodule.span (chartRing k x I) {(g : Ω) * y} ≤ idealMod (x := x) pp I * M.sub I := by
    calc Submodule.span (chartRing k x I) {(g : Ω) * y}
        ≤ Submodule.span (chartRing k x I) {s} * D' * Submodule.span _ {y} := by
          rw [Submodule.span_le, Set.singleton_subset_iff]
          exact Submodule.mul_mem_mul hgs (Submodule.mem_span_singleton_self y)
      _ = D' * Submodule.span _ {s * y} := by
          rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span]; ring
      _ ≤ D' * (idealMod (x := x) pp I * (D.sub I * M.sub I)) := by
          gcongr
          rw [Submodule.span_le, Set.singleton_subset_iff]; exact hsy'
      _ = idealMod (x := x) pp I * M.sub I * (D.sub I * D') := by ring
      _ = idealMod (x := x) pp I * M.sub I := by rw [hD', mul_one]

  have hyM : Submodule.span (chartRing k x I) {y} * M' ≤ idealMod (x := x) pp I := by
    intro z hz
    have hz1 : z ∈ (1 : Submodule (chartRing k x I) Ω) := by
      rw [← hM']
      refine (mul_le_mul' ?_ le_rfl : _ ≤ M.sub I * M') hz
      rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hz1
    have hgz : (g : Ω) * algebraMap (chartRing k x I) Ω r ∈ idealMod (x := x) pp I := by
      have hle : Submodule.span (chartRing k x I) {(g : Ω)} * (Submodule.span _ {y} * M') ≤
          idealMod (x := x) pp I := by
        calc Submodule.span (chartRing k x I) {(g : Ω)} * (Submodule.span _ {y} * M')
            = Submodule.span _ {(g : Ω) * y} * M' := by
              rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span]; ring
          _ ≤ idealMod (x := x) pp I * M.sub I * M' := by gcongr
          _ = idealMod (x := x) pp I := by rw [mul_assoc, hM', mul_one]
      exact hle (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) hz)
    exact ((mem_or_mem hpp hZ hX g r hgz).resolve_left hgI)
  have hle : Submodule.span (chartRing k x I) {y} ≤ idealMod (x := x) pp I * M.sub I :=
    calc Submodule.span (chartRing k x I) {y}
        = Submodule.span (chartRing k x I) {y} * M' * M.sub I := by
          rw [mul_assoc, mul_comm M', hM', mul_one]
      _ ≤ idealMod (x := x) pp I * M.sub I := by gcongr
  exact hle (Submodule.mem_span_singleton_self y)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem VeryAmpleEmbed.Numbers.proof (hSecs : VeryAmpleSecs.Statement.{u, w})
    (hHilb : VeryAmpleHilbert.Statement.{u, w}) : VeryAmpleEmbed.Numbers.Statement.{u, w} := by
  intro k _ Ω _ _ N y Q r h hV n hZ
  exact ⟨VeryAmpleDim.proof k Ω N y n Q r h hZ hV,
    VeryAmpleDegree.proof VeryAmpleDim.proof hSecs hHilb k Ω N y n Q r h hZ hV⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

theorem ZChartSmul.proof : ZChartSmul.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hh J j hj I a ha z hz
  classical
  have hmem : ∀ l, h l ∈ H.sub I := fun l => (Submodule.mem_iInf _).mp (hh l) I
  refine Submodule.span_induction (p := fun z _ => a • z ∈ secsOnZChart G H h I J) ?_ ?_ ?_ ?_ hz
  · rintro e ⟨m, hm⟩
    obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha I
    rw [one_mul] at hn
    set u := ∏ l ∈ J.1.erase j, h l with hu
    have hxu : xProd J = h j * u := (Finset.mul_prod_erase J.1 h hj).symm
    have hk : J.1.card = (J.1.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    have hun : u ^ n ∈ (H.pow ((J.1.erase j).card * n)).sub I :=
      AmpleTwistLocal.pow_mem_pow H I (VeryAmpleZTwist.prod_mem_pow H I hmem _) n
    have hw : a * h j ^ n * u ^ n ∈ (H.pow (n + (J.1.erase j).card * n)).sub I :=
      AmpleTwistLocal.mul_mem_pow H I hn _ hun
    have h1 := VeryAmpleZTwist.smul_mem_twist_pow G H I hw hm
    refine Submodule.subset_span ⟨m + n, ?_⟩
    have e1 : xProd J ^ (m + n) • a • e = (a * h j ^ n * u ^ n) • xProd J ^ m • e := by
      rw [smul_smul, smul_smul, hxu]; ring_nf
    have e2 : J.1.card * (m + n) = J.1.card * m + (n + (J.1.erase j).card * n) := by
      rw [hk]; ring
    rw [e1, e2]
    exact h1
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro b c _ _ hb hc; rw [smul_add]; exact Submodule.add_mem _ hb hc
  · intro s y _ hy; rw [smul_comm]; exact Submodule.smul_mem _ s hy

end

end GroundTheory.Heights₂.Heights.Kleiman
end
