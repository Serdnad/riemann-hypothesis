module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSections
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section CutZeroNotLeAux

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_zeroIdeal_div_eq (D : SubFamily S x Ω) (hfg : ∀ K, (D.sub K).FG) (I : Chart x)
    {σ y : Ω} (hσ : σ ∈ D.sub I) (hy : ∀ δ ∈ D.sub I, y * δ ∈ chartRing S x I) :
    ∃ (g t : Poly S N) (n : ℕ), g ∈ zeroIdeal D.toSubSystem σ ∧ t ∈ monos I.1 ∧
      g.IsHomogeneous n ∧ t.IsHomogeneous n ∧ σ * y = aeval x g / aeval x t := by
  classical

  obtain ⟨f, s, n, hs, hf, hsn, hz⟩ := hy σ hσ
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hfz : y * σ * aeval x s = aeval x f := (eq_div_iff hs0).mp hz

  have hyU := mul_mem_chartRing_union D I
  choose G hG using hfg
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing S x (chartUnion I p.1) := fun p =>
    hyU p.1 y hy _ (D.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := S) I p.1 (y * (p.2 : Ω)) (hgen p)

  obtain ⟨U, hUdef⟩ : ∃ U : Poly S N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := S) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod S x (dU : ℤ) p.1 := by
    intro p
    have hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q := by
      rw [hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q := by
      rw [hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have h2 := aeval_mem_twistMod (x := x)
      (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1
    have h3 := twistMod_mul_mem (hud p) h2
    rw [hsplit, hdsplit, map_mul, Nat.cast_add]
    convert h3 using 1
    ring
  have hUK : ∀ (K : Chart x), ∀ δ ∈ D.sub K, aeval x U * (y * δ) ∈ twistMod S x (dU : ℤ) K := by
    intro K δ hδ
    rw [← hG K] at hδ
    induction hδ using Submodule.span_induction with
    | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
    | smul a b _ hb =>
      rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
        ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hb
  have hU0 := eval_ne_zero_of_mem_monos I hUm

  have hfU : f * U ∈ zeroIdeal D.toSubSystem σ := by
    refine Ideal.subset_span ⟨n + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x s * (aeval x U * (y * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod hsn K) (hUK K δ hδ)
    · rw [map_mul, ← hfz]
      ring
  refine ⟨f * U, s * U, n + dU, hfU, mul_mem hs hUm, hf.mul hUh, hsn.mul hUh, ?_⟩
  rw [map_mul, map_mul, ← hfz]
  field_simp

end CutZeroNotLeAux

theorem CutZeroNotLe.proof : CutZeroNotLe.Statement.{u, w} := by
  intro k _ Ω _ _ N x e pp L s _ hs ⟨I, hI⟩
  have hsI : s ∈ L.sub I := (Submodule.mem_iInf _).mp hs I
  obtain ⟨P, hP⟩ := L.invertible I

  have hex : ∃ y ∈ P, s * y ∉ idealMod pp I := by
    by_contra hcon
    push Not at hcon
    apply hI
    rw [SubSystem.twist_sub_eq_mul_sub]
    have hle : Submodule.span (chartRing k x I) {s} * P ≤ idealMod pp I := by
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c (hcon b hb)
    have hmem : s ∈ Submodule.span (chartRing k x I) {s} * P * L.sub I := by
      rw [mul_assoc, mul_comm P, hP, mul_one]
      exact Submodule.mem_span_singleton_self s
    exact mul_le_mul' hle le_rfl hmem
  obtain ⟨y, hyP, hsy⟩ := hex
  have hy : ∀ δ ∈ L.sub I, y * δ ∈ chartRing k x I := by
    intro δ hδ
    have h := Submodule.mul_mem_mul hδ hyP
    rw [hP] at h
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp h
    rw [mul_comm, ← ha]
    exact a.2
  obtain ⟨g, t, n, hg, ht, hgn, htn, hst⟩ := exists_zeroIdeal_div_eq L.toSubFamily L.fg I hsI hy
  refine ⟨g, hg, fun hgp => hsy ?_⟩
  rw [hst]
  exact Submodule.subset_span ⟨g, t, n, hgp, ht, hgn, htn, rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

theorem SnapperFinite.proof (hE : Extension.Statement.{u, v, w}) (hEL : Extension.Statement.{u, w, w})
    (hT : TwistTilde.Statement.{u, v, w}) (hTL : TwistTilde.Statement.{u, w, w})
    (hS : TildeShift.Statement.{u, v, w}) (hF : TildeFiniteE.Statement.{u, v, w}) :
    SnapperFinite.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF0 t L n c i

  have hpow : ∀ (Lb : LineBundle k x) (m : ℕ), ∃ Q : FinGradedSub (S := k) (x := x) Ω,
      Lb.toSubSystem.pow m = Q.tildeSys 0 := by
    intro Lb m
    induction m with
    | zero =>
      refine ⟨coordGraded k x, ?_⟩
      change twistSys k x 0 = _
      rw [← coordGraded_tildeSys_twist (twistSys k x 0), SubSystem.twist_twistSys_zero]
    | succ m ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨QL, -, hQL⟩ := hEL k Ω N x Ω Lb.toSubFamily Lb.fg
      obtain ⟨P, -, hP⟩ := hTL k Ω N x Ω Q QL
      refine ⟨P, ?_⟩
      have hL : Lb.toSubSystem = QL.tildeSys 0 := SubSystem.ext_sub fun I => (hQL I).symm
      change (Lb.toSubSystem.pow m).twist Lb.toSubSystem = _
      rw [hQ, hL]
      exact SubSystem.ext_sub hP

  have hpows : ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∃ P : FinGradedSub (S := k) (x := x) E,
        F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n = P.tildeSys 0 := by
    intro t
    induction t with
    | zero =>
      intro L n
      obtain ⟨M, -, hM⟩ := hE k Ω N x E F hF0
      exact ⟨M, SubSystem.ext_sub fun I => (hM I).symm⟩
    | succ t ih =>
      intro L n
      obtain ⟨P, hP⟩ := ih (fun j => L j.castSucc) (fun j => n j.castSucc)
      obtain ⟨Q, hQ⟩ := hpow (L (Fin.last t)) (n (Fin.last t))
      obtain ⟨P', -, hP'⟩ := hT k Ω N x E P Q
      refine ⟨P', ?_⟩
      change (F.toSubSystem.twistPows t (fun j => (L j.castSucc).toSubSystem)
        (fun j => n j.castSucc)).twist ((L (Fin.last t)).toSubSystem.pow (n (Fin.last t))) = _
      rw [hP, hQ]
      exact SubSystem.ext_sub hP'
  obtain ⟨P, hP⟩ := hpows t L n
  rw [hP, ← hS k Ω N x E P c]
  exact hF k Ω N x E P i c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ChartIdeal

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

abbrev idealChart (J : Ideal (Poly k N)) (I : Chart x) : Ideal (chartRing k x I) :=
  (idealMod (x := x) J I).comap (Algebra.linearMap (chartRing k x I) Ω)

theorem idealMod_le_range (J : Ideal (Poly k N)) (I : Chart x) :
    idealMod (x := x) J I ≤ LinearMap.range (Algebra.linearMap (chartRing k x I) Ω) := by
  rw [idealMod, Submodule.span_le]
  rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
  exact ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩

theorem idealMod_mono {J J' : Ideal (Poly k N)} (h : J ≤ J') (I : Chart x) :
    idealMod (x := x) J I ≤ idealMod (x := x) J' I := by
  refine Submodule.span_mono ?_
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  exact ⟨f, s, e, h hf, hs, hfe, hse, rfl⟩

theorem idealMod_mul_le (J J' : Ideal (Poly k N)) (I : Chart x) :
    idealMod (x := x) J I * idealMod (x := x) J' I ≤ idealMod (x := x) (J * J') I := by
  rw [idealMod, idealMod, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨f, s, e, hf, hs, hfe, hse, rfl⟩, _, ⟨f', s', e', hf', hs', hfe', hse', rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨f * f', s * s', e + e', Ideal.mul_mem_mul hf hf', mul_mem hs hs',
    hfe.mul hfe', hse.mul hse', ?_⟩
  simp only [map_mul, div_mul_div_comm]

theorem idealChart_mul_le (J J' : Ideal (Poly k N)) (I : Chart x) :
    idealChart J I * idealChart J' I ≤ idealChart (x := x) (J * J') I :=
  Ideal.mul_le.mpr fun a ha b hb => by
    have := idealMod_mul_le (x := x) J J' I (Submodule.mul_mem_mul ha hb)
    simpa using this

theorem idealChart_top (I : Chart x) : idealChart (x := x) (⊤ : Ideal (Poly k N)) I = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  refine Submodule.subset_span ⟨1, 1, 0, Submodule.mem_top, one_mem _, isHomogeneous_one _ _,
    isHomogeneous_one _ _, ?_⟩
  simp

theorem idealChart_prod_le {ι : Type*} (s : Finset ι) (P : ι → Ideal (Poly k N)) (I : Chart x) :
    ∏ i ∈ s, idealChart (P i) I ≤ idealChart (x := x) (∏ i ∈ s, P i) I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Ideal.one_eq_top, idealChart_top, le_refl]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (Ideal.mul_mono_right ih).trans (idealChart_mul_le _ _ I)

theorem idealChart_pow_le (P : Ideal (Poly k N)) (I : Chart x) (n : ℕ) :
    idealChart P I ^ n ≤ idealChart (x := x) (P ^ n) I := by
  induction n with
  | zero => simp only [pow_zero, Ideal.one_eq_top, idealChart_top, le_refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono_left ih).trans (idealChart_mul_le _ _ I)

theorem twist_idealSys_le (F : SubSystem k x Ω) (pp : Ideal (Poly k N)) (I : Chart x) :
    (F.twist (idealSys x pp)).sub I ≤ idealChart pp I • F.sub I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨q, hq, y, hy, rfl⟩
  obtain ⟨a, rfl⟩ := idealMod_le_range pp I hq
  exact Submodule.smul_mem_smul (show a ∈ idealChart pp I from hq) hy

end ChartIdeal

section Algebra

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

theorem le_sup_mul_smul {G F : Submodule A M} {P Q : Ideal A} (hP : F ≤ G ⊔ P • F)
    (hQ : F ≤ G ⊔ Q • F) : F ≤ G ⊔ (P * Q) • F := by
  calc F ≤ G ⊔ P • F := hP
    _ ≤ G ⊔ P • (G ⊔ Q • F) := sup_le_sup_left (Submodule.smul_mono le_rfl hQ) _
    _ ≤ G ⊔ (P * Q) • F := by
      rw [Submodule.smul_sup, Submodule.mul_smul, ← sup_assoc]
      exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _

theorem le_sup_prod_smul {ι : Type*} {G F : Submodule A M} (s : Finset ι) (P : ι → Ideal A)
    (h : ∀ i ∈ s, F ≤ G ⊔ P i • F) : F ≤ G ⊔ (∏ i ∈ s, P i) • F := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact le_sup_mul_smul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem le_sup_pow_smul {G F : Submodule A M} {P : Ideal A} (h : F ≤ G ⊔ P • F) (n : ℕ) :
    F ≤ G ⊔ (P ^ n) • F := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
  | succ n ih => rw [pow_succ]; exact le_sup_mul_smul ih h

end Algebra

theorem StepThree.proof (hAway : StepThree.Away.Statement.{u, w})
    (hOnW : StepThree.OnW.Statement.{u, w}) : StepThree.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK
  classical
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly k N) T.J
  choose! c₀ hc₀ using hOnW k Ω N x T hK
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg T.J (IsNoetherian.noetherian _)
  set s := hfin.toFinset
  refine ⟨∑ p ∈ s, |c₀ p|, fun b hb I => ?_⟩
  have hc : 0 ≤ ∑ p ∈ s, |c₀ p| := Finset.sum_nonneg fun p _ => abs_nonneg _
  set F := (T.L.pow b).twist (twistSys k x (∑ p ∈ s, |c₀ p|))
  set G := Submodule.span (chartRing k x I) (F.secs : Set Ω)
  refine le_antisymm (Submodule.span_le.mpr fun z hz => ?_) ?_
  · exact (Submodule.mem_iInf _).mp hz I
  have h1 : ∀ p ∈ s, F.sub I ≤ G ⊔ idealChart p I • F.sub I := fun p hp => by
    have hp' := hfin.mem_toFinset.mp hp
    refine (hc₀ p hp' b _ hb ?_ I).trans (sup_le_sup_left (twist_idealSys_le F p I) _)
    exact (le_abs_self _).trans (Finset.single_le_sum (fun q _ => abs_nonneg (c₀ q)) hp)
  have h2 := le_sup_pow_smul (le_sup_prod_smul s _ h1) (n * b)
  have hrad : ∏ p ∈ s, p ≤ T.J.radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact le_sInf fun q hq => Ideal.prod_le_inf.trans (Finset.inf_le (hfin.mem_toFinset.mpr hq))
  have h3 : (∏ p ∈ s, idealChart p I) ^ (n * b) ≤ idealChart T.J I ^ b := by
    rw [pow_mul]
    refine Ideal.pow_right_mono ?_ b
    refine (Ideal.pow_right_mono (idealChart_prod_le s (fun p => p) I) n).trans
      ((idealChart_pow_le _ I n).trans ?_)
    exact Submodule.comap_mono (idealMod_mono ((Ideal.pow_right_mono hrad n).trans hn) I)
  have h4 := hAway k Ω N x T b _ hc I
  exact h2.trans (sup_le le_rfl ((Submodule.smul_mono_left h3).trans h4))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section VeryAmpleEmbedSectionsProof

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {y : Fin (N + 1) → Ω}

theorem vaes_ampleBase_le_chartRing {r : ℕ} {h : Fin (r + 1) → Ω} {j : Fin (r + 1)} (hj : h j ≠ 0) :
    ampleBase (S := k) h j ≤ chartRing k h (singleChart hj) :=
  Algebra.adjoin_le (by rintro _ ⟨l, rfl⟩; exact (ratio (S := k) hj l).2)

theorem vaes_mem_pow_of_forall (Q : LineBundle k y) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Q.toSubSystem h) (I : Chart y) {m : ℕ} {s : Ω}
    (hs : ∀ j, h j ≠ 0 → ∃ e : ℕ, s * h j ^ e ∈ (Q.toSubSystem.pow (m + e)).sub I) :
    s ∈ (Q.toSubSystem.pow m).sub I := by
  have hs' : ∀ j, h j ≠ 0 → ∃ e : ℕ, s * h j ^ e ∈ Q.toSubSystem.sub I ^ (m + e) := fun j hj => by
    obtain ⟨e, he⟩ := hs j hj
    exact ⟨e, by rw [← SubSystem.pow_sub_eq_pow Q.toSubSystem]; exact he⟩
  rw [SubSystem.pow_sub_eq_pow Q.toSubSystem]
  clear hs
  obtain ⟨P', hPP'⟩ := Q.invertible I
  set P := Q.toSubSystem.sub I with hP
  let c : Ideal (chartRing k y I) := (P ^ m).comap (LinearMap.toSpanSingleton _ Ω s)
  have hc : ∀ a, a ∈ c ↔ (a : Ω) * s ∈ P ^ m := fun a => by
    change a • s ∈ P ^ m ↔ _; rw [chartRing_smul_def]
  have key : ∀ j, ∀ q ∈ P', ∀ a : chartRing k y I, (a : Ω) = h j * q → a ∈ c.radical := by
    intro j q hq a ha
    by_cases hj : h j = 0
    · have : a = 0 := Subtype.ext (by rw [ha, hj, zero_mul]; rfl)
      rw [this]; exact Ideal.zero_mem _
    obtain ⟨e, he⟩ := hs' j hj
    refine ⟨e, (hc _).mpr ?_⟩
    have hmem := Submodule.mul_mem_mul he (Submodule.pow_mem_pow P' hq e)
    rw [pow_add, mul_assoc, ← mul_pow, hPP', one_pow, mul_one] at hmem
    rw [Subalgebra.coe_pow, ha]
    convert hmem using 1
    ring
  let M : Submodule (chartRing k y I) Ω := Submodule.map (Algebra.linearMap (chartRing k y I) Ω) c.radical
  have hle : P * P' ≤ M := by
    refine Submodule.mul_le.mpr fun p hp q hq => ?_
    rw [hP, ← hv.generates I] at hp
    induction hp using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      have h1 : h j * q ∈ P * P' := Submodule.mul_mem_mul
        (by rw [hP, ← hv.generates I]; exact Submodule.subset_span ⟨j, rfl⟩) hq
      rw [hPP'] at h1
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp h1
      exact ⟨a, key j q hq a ha, ha⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
    | smul a u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hu
  have h1 : (1 : Ω) ∈ M := hle (by rw [hPP']; exact Submodule.one_le.mp le_rfl)
  obtain ⟨a, ha, ha1⟩ := h1
  have : a = 1 := Subtype.ext ha1
  have ha' : (1 : chartRing k y I) ∈ c.radical := this ▸ ha
  rw [← Ideal.eq_top_iff_one, Ideal.radical_eq_top, Ideal.eq_top_iff_one, hc] at ha'
  simpa using ha'

end VeryAmpleEmbedSectionsProof

theorem VeryAmpleEmbed.Sections.proof : VeryAmpleEmbed.Sections.Statement.{u, w} := by
  intro k _ Ω _ _ N y Q r h _ hv m
  apply le_antisymm
  · intro s hs
    refine (Submodule.mem_iInf _).mpr fun J => ?_
    obtain ⟨j, hjJ⟩ := J.2.1
    have hj : h j ≠ 0 := (mem_support h).mp (J.2.2 hjJ)
    have hsI : ∀ I, s ∈ (Q.toSubSystem.pow m).sub I := fun I =>
      (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs I)
    have hb : s / h j ^ m ∈ ampleRing Q.toSubSystem 1 (h j) := Set.mem_iInter.mpr fun I =>
      ⟨m, by rw [one_mul, div_mul_cancel₀ _ (pow_ne_zero _ hj)]; exact hsI I⟩
    have hbc := vaes_ampleBase_le_chartRing hj (hv.closed j hj hb)
    have hmem : s ∈ twistMod k h (m : ℤ) (singleChart hj) := by
      rw [twistMod_eq_span _ _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton]
      exact ⟨⟨_, hbc⟩, by rw [chartRing_smul_def, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ hj)]⟩
    exact (Submodule.restrictScalars_mem k _ _).mpr ((twistSys k h (m : ℤ)).mono (singleChart hj) J
      (Finset.singleton_subset_iff.mpr hjJ) s hmem)
  · intro s hs
    refine (Submodule.mem_iInf _).mpr fun I => (Submodule.restrictScalars_mem k _ _).mpr ?_
    refine vaes_mem_pow_of_forall Q hv I fun j hj => ?_
    have hsj : s ∈ twistMod k h (m : ℤ) (singleChart hj) :=
      (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs _)
    obtain ⟨g, t, e, ht, hte, hg, hgt⟩ := exists_rep_of_mem_twistMod h m hj hsj
    have ht' : t ∈ Submonoid.closure {(X j : MvPolynomial (Fin (r + 1)) k)} := by
      have : ((fun i => (X i : MvPolynomial (Fin (r + 1)) k)) ''
          ((({j} : Finset (Fin (r + 1))) : Set (Fin (r + 1))))) = {X j} := by simp
      rw [← this]; exact ht
    obtain ⟨d, rfl⟩ := Submonoid.mem_closure_singleton.mp ht'
    have hde : e = d := hte.inj_right (isHomogeneous_X_pow j d) (by
      rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
    subst hde
    refine ⟨e, ?_⟩
    have := aeval_mem_pow Q.toSubSystem hv.mem_secs I hg
    rwa [hgt, map_pow, aeval_X, add_comm] at this

end

end GroundTheory.Heights₂.Heights.Kleiman
end
