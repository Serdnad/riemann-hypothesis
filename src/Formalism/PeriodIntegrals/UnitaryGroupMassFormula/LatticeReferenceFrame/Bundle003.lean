module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle002
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.TH

variable (I : Formalism.MainNotions.S.AutInst)

theorem spanG_ne (g : ℕ) (hg : 1 ≤ g) : Ideal.span {(g : 𝓞 I.E)} ≠ 0 := by
  have hg0 : (g : 𝓞 I.E) ≠ 0 := by
    intro h
    have h2 := congrArg (fun x : 𝓞 I.E => (x : I.E)) h
    have h3 : (g : I.E) = 0 := by simpa using h2
    have h4 : g = 0 := by exact_mod_cast h3
    omega
  rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact hg0

def primesG (g : ℕ) (hg : 1 ≤ g) : Finset (HeightOneSpectrum (𝓞 I.E)) :=
  (Ideal.finite_factors (spanG_ne I g hg)).toFinset

theorem mem_primesG (g : ℕ) (hg : 1 ≤ g) (P : HeightOneSpectrum (𝓞 I.E)) :
    P ∈ primesG I g hg ↔ (g : 𝓞 I.E) ∈ P.asIdeal := by
  unfold primesG
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]

theorem prod_le_radical (g : ℕ) (hg : 1 ≤ g) :
    (∏ P ∈ primesG I g hg, P.asIdeal) ≤ (Ideal.span {(g : 𝓞 I.E)}).radical := by
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J hJ => ?_
  obtain ⟨hJle, hJp⟩ := hJ
  have hgJ : (g : 𝓞 I.E) ∈ J := hJle (Ideal.mem_span_singleton_self _)
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply spanG_ne I g hg
    rw [Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    rw [h] at hgJ
    exact (Submodule.mem_bot _).mp hgJ
  let Q : HeightOneSpectrum (𝓞 I.E) := ⟨J, hJp, hJ0⟩
  have hQ : Q ∈ primesG I g hg := (mem_primesG I g hg Q).mpr hgJ
  exact Ideal.prod_le_inf.trans (Finset.inf_le hQ)

private lemma sk_GE_of_mem_span_natCast (g : ℕ) (z : 𝓞 I.E) (hz : z ∈ Ideal.span {(g : 𝓞 I.E)}) :
    PI.ScRefExists.Sk.GE I g (z : I.E) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨t, ?_⟩
  rw [← ht]
  first
    | (push_cast; ring)
    | simp [mul_comm]

theorem theta_series_existence : PI.ScRefExists.Sk.ThetaEx := by
  intro I g hg hS
  classical
  letI : LinearOrder (HeightOneSpectrum (𝓞 I.E)) := by
    first
      | exact linearOrderOfSTO WellOrderingRel
      | exact IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (∏ P ∈ primesG I g hg, P.asIdeal) ^ N ≤ Ideal.span {(g : 𝓞 I.E)} := by
    first
      | exact Ideal.exists_pow_le_of_le_radical_of_fg (prod_le_radical I g hg) (IsNoetherian.noetherian _)
      | exact Ideal.exists_pow_le_of_le_radical_of_fg (IsNoetherian.noetherian _) (prod_le_radical I g hg)
  obtain ⟨θ, hθ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := primesG I g hg)
    (fun P : HeightOneSpectrum (𝓞 I.E) => P.asIdeal) (fun _ => N) (fun P _ => P.prime)
    (fun P _ Q _ h e => h (HeightOneSpectrum.ext e))
    (fun P => if (P : HeightOneSpectrum (𝓞 I.E)) < cj I P then (1 : 𝓞 I.E) else 0)
  have h1 : ∀ P ∈ primesG I g hg, P < cj I P → θ - 1 ∈ P.asIdeal ^ N := by
    intro P hP h
    simpa [h] using hθ P hP
  have h0 : ∀ P ∈ primesG I g hg, ¬ P < cj I P → θ ∈ P.asIdeal ^ N := by
    intro P hP h
    simpa [h] using hθ P hP
  have hcjS : ∀ P ∈ primesG I g hg, cj I P ∈ primesG I g hg := by
    intro P hP
    rw [mem_primesG] at hP ⊢
    rw [mem_cj, map_natCast]
    exact hP
  have hsg : ∀ (P : HeightOneSpectrum (𝓞 I.E)) (z : 𝓞 I.E), z ∈ (cj I P).asIdeal ^ N →
      sg I z ∈ P.asIdeal ^ N := by
    intro P z hz
    have h2 := Ideal.mem_map_of_mem (sg I) hz
    rwa [Ideal.map_pow, show (cj I P).asIdeal = P.asIdeal.comap (sg I) from rfl,
      Ideal.map_comap_of_surjective _ (fun y => ⟨sg I y, sg_sg I y⟩)] at h2
  have hloc : ∀ P ∈ primesG I g hg, θ * θ - θ ∈ P.asIdeal ^ N ∧ θ * sg I θ ∈ P.asIdeal ^ N ∧
      1 - θ - sg I θ ∈ P.asIdeal ^ N := by
    intro P hP
    have hne : cj I P ≠ P := cj_ne I g hg hS P ((mem_primesG I g hg P).mp hP)
    by_cases hlt : P < cj I P
    · have ha := h1 P hP hlt
      have hb : θ ∈ (cj I P).asIdeal ^ N :=
        h0 (cj I P) (hcjS P hP) (by rw [cj_cj]; exact lt_asymm hlt)
      have hb' := hsg P θ hb
      refine ⟨?_, ?_, ?_⟩
      · have e : θ * θ - θ = (θ - 1) * θ := by ring
        rw [e]
        exact Ideal.mul_mem_right _ _ ha
      · exact Ideal.mul_mem_left _ _ hb'
      · have e : 1 - θ - sg I θ = -(θ - 1) - sg I θ := by ring
        rw [e]
        exact Ideal.sub_mem _ (Submodule.neg_mem _ ha) hb'
    · have ha := h0 P hP hlt
      have hlt' : cj I P < cj I (cj I P) := by
        rw [cj_cj]
        exact lt_of_le_of_ne (not_lt.mp hlt) hne
      have hb' := hsg P _ (h1 (cj I P) (hcjS P hP) hlt')
      rw [map_sub, map_one] at hb'
      refine ⟨?_, ?_, ?_⟩
      · have e : θ * θ - θ = θ * (θ - 1) := by ring
        rw [e]
        exact Ideal.mul_mem_right _ _ ha
      · exact Ideal.mul_mem_right _ _ ha
      · have e : 1 - θ - sg I θ = -θ - (sg I θ - 1) := by ring
        rw [e]
        exact Ideal.sub_mem _ (Submodule.neg_mem _ ha) hb'
  have key : (primesG I g hg).inf (fun P : HeightOneSpectrum (𝓞 I.E) => P.asIdeal ^ N) =
      (∏ P ∈ primesG I g hg, P.asIdeal) ^ N := by
    rw [← Finset.prod_pow]
    exact IsDedekindDomain.inf_pow_eq_prod_of_prime _ _ _ (fun P _ => P.prime)
      (fun P _ Q _ h e => h (HeightOneSpectrum.ext e))
  have hmem : ∀ z : 𝓞 I.E, (∀ P ∈ primesG I g hg, z ∈ P.asIdeal ^ N) →
      z ∈ Ideal.span {(g : 𝓞 I.E)} := by
    intro z hz
    apply hN
    rw [← key]
    exact (Ideal.span_singleton_le_iff_mem _).mp
      (Finset.le_inf fun P hP => (Ideal.span_singleton_le_iff_mem _).mpr (hz P hP))
  refine ⟨θ, ?_, ?_, ?_⟩
  · have e : ((θ * θ - θ : 𝓞 I.E) : I.E) = (θ : I.E) * θ - θ := by push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).1)
  · have e : ((θ * sg I θ : 𝓞 I.E) : I.E) = (θ : I.E) * star (θ : I.E) := by
      rw [← sg_coe]; push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).2.1)
  · have e : ((1 - θ - sg I θ : 𝓞 I.E) : I.E) = 1 - (θ : I.E) - star (θ : I.E) := by
      rw [← sg_coe]; push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).2.2)

end PI.ScRefExists.TH
end
end

section

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Id

theorem fixInt : FixInt := by
  intro I s hs
  obtain ⟨a, ha⟩ := (I.cm.fixed (s : I.E)).mp hs
  have hs' : IsIntegral ℤ ((algebraMap I.F I.E).toIntAlgHom a) := by
    show IsIntegral ℤ (algebraMap I.F I.E a)
    rw [ha]
    exact NumberField.RingOfIntegers.isIntegral_coe s
  have hint : IsIntegral ℤ a :=
    (isIntegral_algHom_iff (algebraMap I.F I.E).toIntAlgHom (algebraMap I.F I.E).injective).mp hs'
  exact ⟨⟨a, hint⟩, ha⟩

theorem intF {F : Type} [Field F] [NumberField F] (r : 𝓞 F) :
    algebraMap F (Af F) (r : F) ∈ Formalism.UG.intAd F := by
  show ∀ v, _
  intro v
  rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
  exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

section Ten

variable (I : Formalism.MainNotions.S.AutInst)

def iA : Af I.F →ₐ[I.F] I.E ⊗[I.F] Af I.F := Algebra.TensorProduct.includeRight

def iE : I.E →+* I.E ⊗[I.F] Af I.F := Formalism.UG.inclE (F := I.F) (Af I.F)

theorem iA_apply (x : Af I.F) : iA I x = (1 : I.E) ⊗ₜ[I.F] x :=
  Algebra.TensorProduct.includeRight_apply x

theorem iE_apply (e : I.E) : iE I e = e ⊗ₜ[I.F] (1 : Af I.F) :=
  Algebra.TensorProduct.includeLeftRingHom_apply e

theorem iE_alg (x : I.F) : iE I (algebraMap I.F I.E x) = iA I (algebraMap I.F (Af I.F) x) := by
  rw [iE_apply, iA_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]

theorem sig_iA (x : Af I.F) : sigA I (iA I x) = iA I x := by
  rw [iA_apply]
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) ((1 : I.E) ⊗ₜ[I.F] x) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem sig_iE (e : I.E) : sigA I (iE I e) = iE I (star e) := by
  rw [iE_apply, iE_apply]
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (e ⊗ₜ[I.F] (1 : Af I.F)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem iE_mem (θ : 𝓞 I.E) : iE I (θ : I.E) ∈ IntAf I.F I.E := by
  rw [iE_apply]
  exact Subring.subset_closure (Or.inl ⟨⟨(θ : I.E), θ, rfl⟩, rfl⟩)

theorem iA_mem {x : Af I.F} (hx : x ∈ Formalism.UG.intAd I.F) : iA I x ∈ IntAf I.F I.E := by
  rw [iA_apply]
  exact Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)

end Ten

theorem tenStep : TenStep := by
  intro hAd hFix I g θ hg _hsp hθ
  obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩, ⟨t3, ht3⟩⟩ := hθ
  have hgE : ((g : ℕ) : I.E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs2 : star (t2 : I.E) = t2 := by
    have h1 : star ((θ : I.E) * star (θ : I.E)) = (θ : I.E) * star (θ : I.E) := by
      rw [star_mul, star_star]
    rw [ht2, star_mul, star_natCast, mul_comm] at h1
    exact mul_left_cancel₀ hgE h1
  have hs3 : star (t3 : I.E) = t3 := by
    have h1 : star (1 - (θ : I.E) - star (θ : I.E)) = 1 - (θ : I.E) - star (θ : I.E) := by
      rw [star_sub, star_sub, star_one, star_star]
      ring
    rw [ht3, star_mul, star_natCast, mul_comm] at h1
    exact mul_left_cancel₀ hgE h1
  obtain ⟨a2, ha2⟩ := hFix I t2 hs2
  obtain ⟨a3, ha3⟩ := hFix I t3 hs3
  have hαi : -algebraMap I.F (Af I.F) (a3 : I.F) ∈ Formalism.UG.intAd I.F :=
    (Formalism.UG.intAd I.F).neg_mem (intF a3)
  have hβi : algebraMap I.F (Af I.F) (a2 : I.F) ∈ Formalism.UG.intAd I.F := intF a2
  obtain ⟨C₁, C₂, hC₁, hC₂, hi, hii, hiii⟩ := hAd I.F g _ _ hg hαi hβi
  obtain ⟨W, hWd⟩ : ∃ W : Af I.F, W = 1 + (g : Af I.F) * C₁ := ⟨_, rfl⟩
  obtain ⟨Q, hQd⟩ : ∃ Q : Af I.F, Q = (g : Af I.F) * C₂ := ⟨_, rfl⟩
  obtain ⟨A0, hA0d⟩ : ∃ A0 : Af I.F,
      A0 = 1 + (g : Af I.F) * -algebraMap I.F (Af I.F) (a3 : I.F) := ⟨_, rfl⟩
  obtain ⟨B0, hB0d⟩ : ∃ B0 : Af I.F, B0 = (g : Af I.F) * algebraMap I.F (Af I.F) (a2 : I.F) :=
    ⟨_, rfl⟩
  rw [← hWd, ← hQd, ← hA0d] at hi
  rw [← hWd, ← hQd, ← hB0d] at hii
  rw [← hWd, ← hQd, ← hA0d, ← hB0d] at hiii
  have hi' := congrArg (iA I) hi
  have hii' := congrArg (iA I) hii
  have hiii' := congrArg (iA I) hiii
  simp only [map_mul, map_add (f := _), map_sub, map_pow, map_neg, map_ofNat, map_zero] at hi' hii' hiii'
  have hA : iA I A0 = iE I (θ : I.E) + iE I (star (θ : I.E)) := by
    have e1 : A0 = algebraMap I.F (Af I.F) (1 - (g : I.F) * (a3 : I.F)) := by
      rw [hA0d, map_sub, map_one, map_mul, map_natCast]
      ring
    have e2 : algebraMap I.F I.E (1 - (g : I.F) * (a3 : I.F)) = (θ : I.E) + star (θ : I.E) := by
      rw [map_sub, map_one, map_mul, map_natCast, ha3]
      linear_combination ht3
    rw [e1, ← iE_alg, e2, map_add (f := _)]
  have hB : iA I B0 = iE I (θ : I.E) * iE I (star (θ : I.E)) := by
    have e1 : B0 = algebraMap I.F (Af I.F) ((g : I.F) * (a2 : I.F)) := by
      rw [hB0d, map_mul, map_natCast]
    have e2 : algebraMap I.F I.E ((g : I.F) * (a2 : I.F)) = (θ : I.E) * star (θ : I.E) := by
      rw [map_mul, map_natCast, ha2, ht2]
    rw [e1, ← iE_alg, e2, map_mul]
  rw [hA] at hi' hiii'
  rw [hB] at hii' hiii'
  have hWi : W ∈ Formalism.UG.intAd I.F := by
    rw [hWd]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ g) hC₁)
  have hQi : Q ∈ Formalism.UG.intAd I.F := by
    rw [hQd]
    exact mul_mem (natCast_mem _ g) hC₂
  refine ⟨iE I (θ : I.E) * iA I W - iA I Q, ?_, ?_, ?_, ?_⟩
  · exact sub_mem (mul_mem (iE_mem I θ) (iA_mem I hWi)) (iA_mem I hQi)
  · linear_combination (iE I (θ : I.E)) * hi' + hii'
  · rw [map_sub, map_mul, sig_iE, sig_iA, sig_iA]
    linear_combination hiii'
  · refine ⟨iE I (θ : I.E) * iA I C₁ - iA I C₂,
      sub_mem (mul_mem (iE_mem I θ) (iA_mem I hC₁)) (iA_mem I hC₂), ?_⟩
    have hW' : iA I W = 1 + (g : I.E ⊗[I.F] Af I.F) * iA I C₁ := by
      rw [hWd, map_add (f := _), map_one, map_mul, map_natCast]
    have hQ' : iA I Q = (g : I.E ⊗[I.F] Af I.F) * iA I C₂ := by
      rw [hQd, map_mul, map_natCast]
    show iE I (θ : I.E) * iA I W - iA I Q - iE I (θ : I.E) = _
    rw [hW', hQ']
    ring

end PI.ScRefExists.Id
end
end

section

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.Id

section Ad

variable {F : Type} [Field F] [NumberField F]

theorem memO {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} :
    x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := by
  first
    | exact Iff.rfl
    | exact HeightOneSpectrum.mem_adicCompletionIntegers F v
    | simp [HeightOneSpectrum.mem_adicCompletionIntegers]

def evA (v : HeightOneSpectrum (𝓞 F)) : Af F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evA_apply (v : HeightOneSpectrum (𝓞 F)) (a : Af F) : evA v a = a v := rfl

theorem eq_of_evA {a b : Af F} (h : ∀ v, evA v a = evA v b) : a = b := by
  first
    | (ext v; exact h v)
    | exact Subtype.ext (funext h)
    | exact RestrictedProduct.ext h

def mkA (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (hc : ∀ v, Valued.v (c v) ≤ 1) :
    Af F :=
  ⟨c, Filter.Eventually.of_forall fun v => memO.2 (hc v)⟩

theorem mkA_apply (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, Valued.v (c v) ≤ 1) (v : HeightOneSpectrum (𝓞 F)) : mkA c hc v = c v := rfl

theorem mkA_mem (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, Valued.v (c v) ≤ 1) : mkA c hc ∈ Formalism.UG.intAd F := by
  unfold Formalism.UG.intAd
  show ∀ v, mkA c hc v ∈ HeightOneSpectrum.adicCompletionIntegers F v
  intro v
  rw [mkA_apply]
  exact memO.2 (hc v)

theorem natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) :
    Valued.v ((g : ℕ) : v.adicCompletion F) ≤ 1 := memO.1 (natCast_mem _ g)

end Ad

theorem adOfLoc : AdOfLoc := by
  unfold AdOfLoc LocIdem AdIdem
  intro hL F _ _ g α β hg hα hβ
  have hα' : ∀ v, Valued.v (α v) ≤ 1 := by
    intro v
    have h0 := (show ∀ v, α v ∈ HeightOneSpectrum.adicCompletionIntegers F v from hα) v
    exact memO.1 h0
  have hβ' : ∀ v, Valued.v (β v) ≤ 1 := by
    intro v
    have h0 := (show ∀ v, β v ∈ HeightOneSpectrum.adicCompletionIntegers F v from hβ) v
    exact memO.1 h0
  have key : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c₁ c₂ : v.adicCompletion F,
      Valued.v c₁ ≤ 1 ∧ Valued.v c₂ ≤ 1 ∧
      (1 + (g : v.adicCompletion F) * α v) * (1 + (g : v.adicCompletion F) * c₁) ^ 2
          - 2 * (1 + (g : v.adicCompletion F) * c₁) * ((g : v.adicCompletion F) * c₂)
        = 1 + (g : v.adicCompletion F) * c₁ ∧
      ((g : v.adicCompletion F) * c₂) ^ 2
          - (g : v.adicCompletion F) * β v * (1 + (g : v.adicCompletion F) * c₁) ^ 2
        = -((g : v.adicCompletion F) * c₂) ∧
      ((g : v.adicCompletion F) * c₂) ^ 2
          - (1 + (g : v.adicCompletion F) * α v) * ((g : v.adicCompletion F) * c₂)
            * (1 + (g : v.adicCompletion F) * c₁)
          + (g : v.adicCompletion F) * β v * (1 + (g : v.adicCompletion F) * c₁) ^ 2 = 0 := by
    intro v
    by_cases hv : Valued.v ((g : ℕ) : v.adicCompletion F) < 1
    · exact hL F v g (α v) (β v) hg hv (hα' v) (hβ' v)
    · have h1 : Valued.v ((g : ℕ) : v.adicCompletion F) = 1 :=
        le_antisymm (natCast_le_one v g) (not_lt.mp hv)
      have hg0 : ((g : ℕ) : v.adicCompletion F) ≠ 0 := by
        intro h
        rw [h, map_zero] at h1
        exact zero_ne_one h1
      have hu : 1 + (g : v.adicCompletion F) * -((g : v.adicCompletion F))⁻¹ = 0 := by
        rw [mul_neg, mul_inv_cancel₀ hg0, add_neg_cancel]
      refine ⟨-((g : v.adicCompletion F))⁻¹, 0, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Valuation.map_neg, map_inv₀, h1, inv_one]
      · rw [map_zero]
        exact zero_le'
      · rw [hu]
        simp
      · rw [hu]
        simp
      · rw [hu]
        simp
  choose c₁ c₂ h1 h2 e1 e2 e3 using key
  refine ⟨mkA c₁ h1, mkA c₂ h2, mkA_mem c₁ h1, mkA_mem c₂ h2, ?_, ?_, ?_⟩
  · apply eq_of_evA
    intro v
    simp only [map_add (f := _), map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      evA_apply, mkA_apply]
    exact e1 v
  · apply eq_of_evA
    intro v
    simp only [map_add (f := _), map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      evA_apply, mkA_apply]
    exact e2 v
  · apply eq_of_evA
    intro v
    simp only [map_add (f := _), map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      map_zero, evA_apply, mkA_apply]
    exact e3 v

end PI.ScRefExists.Id
end
end
