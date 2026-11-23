module

public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Columns.Bundle013
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

section Pad

variable {R : Type} [CommRing R] {n : ℕ}

end Pad

section Ad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem til_tmv_int_of_iA {a : E} (h : iA F E a ∈ Formalism.L2.Herm.intAf F E) : ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = a := by
  have h1 : (fun _ : Fin 1 => a) ∈ Formalism.UG.CS.globLat (F := F) (1 : GL (Fin 1) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E 1) := by
    rw [mem_globLat]
    intro i
    rw [pullV_one]
    exact h
  rw [globLat_one_std, mem_stdLat] at h1
  exact h1 0

private lemma mk_mul_reduction_eq_mk (P : HeightOneSpectrum (𝓞 E)) {x : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E r) :
    Ideal.Quotient.mk P.asIdeal s * redP P x = Ideal.Quotient.mk P.asIdeal r := by
  classical
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, h, by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]⟩
  unfold redP
  rw [dite_eq_left hex]
  obtain ⟨r', s', hs', h', hc'⟩ := hex.choose_spec
  have hs'0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have key : s * r' = s' * r := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, map_mul, ← h', ← h]
    ring
  apply mul_left_cancel₀ hs'0
  rw [mul_left_comm, hc', ← map_mul, ← map_mul, key]

variable {n : ℕ} [NeZero n] (ST SG : Finset (Pl E))

private lemma reduction_mul_of_integral' (P : Pl E) (b : 𝓞 E) {a : E} (ha : IntAt P a) :
    redP P (algebraMap (𝓞 E) E b * a) = Ideal.Quotient.mk P.asIdeal b * redP P a := by
  obtain ⟨r, s, hs, h⟩ := ha
  haveI : P.asIdeal.IsPrime := P.isPrime
  have h1 := mk_mul_reduction_eq_mk P hs h
  have h2 := mk_mul_reduction_eq_mk P (x := algebraMap (𝓞 E) E b * a) (r := b * r) hs (by rw [map_mul, ← h]; ring)
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hs0
  rw [h2, mul_left_comm, h1, map_mul]

end Ad

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt redFn resS)

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem updn_den {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P) (a : E ⊗[F] Formalism.L2.Herm.Af F)
    (h : prV (E := E) v a ∈ Formalism.BasicNotions.intV E v) :
    ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ iA F E (algebraMap (𝓞 E) E t) * a ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨D, hD, hDa⟩ := levelaf_denom (E := E) a
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  set DE : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) D with hDE
  have hDE0 : DE ≠ 0 := by
    rw [hDE, Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hD
  have hI : (Ideal.span {p * DE} : Ideal (𝓞 E)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hp0 hDE0
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) _ hI (Ideal.Quotient.mk _ (Formalism.L2.DIV.lc_eps E v))
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hq' : Ideal.Quotient.mk (Formalism.L2.DIV.idS F (Ideal.span {p * DE})) (Formalism.L2.DIV.oToS F E t) =
      Ideal.Quotient.mk _ (Formalism.L2.DIV.lc_eps E v) := hq
  have hd := Ideal.Quotient.eq.1 hq'
  unfold Formalism.L2.DIV.idS at hd
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hd
  obtain ⟨y, hy⟩ := hd
  have ht : Formalism.L2.DIV.oToS F E t = Formalism.L2.DIV.lc_eps E v + y * Formalism.L2.DIV.oToS F E p * Formalism.L2.DIV.oToS F E DE := by
    rw [mul_assoc, ← map_mul, hy]; ring
  refine ⟨t, ?_, ?_⟩
  · intro htP
    have h1 := congrArg (resS F P) ht
    rw [map_add (f := _), map_mul, map_mul, Formalism.L2.DIV.lc_res_eps P v hov, Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_oToS,
      Ideal.Quotient.eq_zero_iff_mem.2 htP, Ideal.Quotient.eq_zero_iff_mem.2 hp, mul_zero, zero_mul, add_zero] at h1
    exact zero_ne_one h1
  · have hC : ((Formalism.L2.DIV.oToS F E DE : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = levelafC E D := by
      rw [Formalism.L2.DIV.levelafC_eq_incl, ← iA_coe, hDE, ← IsScalarTower.algebraMap_apply]
    rw [iA_coe, ht]
    have e : ((Formalism.L2.DIV.lc_eps E v + y * Formalism.L2.DIV.oToS F E p * Formalism.L2.DIV.oToS F E DE : Formalism.L2.Herm.intAf F E) :
        E ⊗[F] Formalism.L2.Herm.Af F) * a = afsplitIE v (prV (E := E) v a) +
          ((y * Formalism.L2.DIV.oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * (levelafC E D * a) := by
      rw [afsplit_decomp, ← hC, Subring.coe_add, Subring.coe_mul, add_mul, mul_assoc]
      rfl
    rw [e]
    exact add_mem (afsplit_IE_int v _ h) (mul_mem (y * Formalism.L2.DIV.oToS F E p).2 hDa)

variable {n : ℕ}

theorem updn_prV_pullV {v : HeightOneSpectrum (𝓞 F)} {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') (z : Fin n → E) (i : Fin n) :
    prV (E := E) v (pullV x z i) = prV (E := E) v (pullV x' z i) := by
  have h' : bc (prV (E := E) v) x⁻¹ = bc (prV (E := E) v) x'⁻¹ := by rw [map_inv, map_inv, h]
  unfold pullV
  simp only [Matrix.mulVec, dotProduct]

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul]
  congr 1
  exact congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h'

variable [StarRing E]

theorem localized_globalLattice_le {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) ≤ localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) := by
  classical
  intro z hz
  obtain ⟨s, hs, hsz⟩ := (mem_locP P _ z).1 hz
  have h1 : ∀ i, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧
      iA F E (algebraMap (𝓞 E) E t) * pullV x' (s • z) i ∈ Formalism.L2.Herm.intAf F E := fun i =>
    updn_den hov _ (by
      rw [← updn_prV_pullV h]
      exact afsplit_prV_int v _ ((mem_globLat x _).1 hsz i))
  choose t ht hti using h1
  have hT : (∏ i, t i) ∉ P.asIdeal := by
    intro hm
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
    exact ht i hi
  refine (mem_locP P _ z).2 ⟨(∏ i, t i) * s, fun hm => (P.isPrime.mem_or_mem hm).elim hT hs, ?_⟩
  rw [mul_smul, mem_globLat]
  intro i
  rw [pullV_osmul, ← Finset.prod_erase_mul Finset.univ t (Finset.mem_univ i), map_mul, map_mul, mul_assoc]
  exact mul_mem (iA_mem _) (hti i)

theorem updn_mem_loc {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) = localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) :=
  le_antisymm (localized_globalLattice_le hov h) (localized_globalLattice_le hov h.symm)

theorem updn_red_loc {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') {z : Fin n → E}
    (hz : z ∈ localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))) (i : Fin n) :
    redA P (pullV x z i) = redA P (pullV x' z i) := by
  have hz' : z ∈ localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) := localized_globalLattice_le hov h hz
  obtain ⟨s, hs, hsz⟩ := pullV_den hz
  obtain ⟨s', hs', hsz'⟩ := pullV_den hz'
  have hss : s * s' ∉ P.asIdeal := fun hm => (P.isPrime.mem_or_mem hm).elim hs hs'
  have m1 : iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x z i ∈ Formalism.L2.Herm.intAf F E := by
    rw [mul_comm s s', map_mul, map_mul, mul_assoc]
    exact mul_mem (iA_mem _) (hsz i)
  have m2 : iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x' z i ∈ Formalism.L2.Herm.intAf F E := by
    rw [map_mul, map_mul, mul_assoc]
    exact mul_mem (iA_mem _) (hsz' i)
  apply mul_left_cancel₀ (mk_ne_zero hss)
  rw [redA_spec P hss m1, redA_spec P hss m2, ← sub_eq_zero, ← map_sub]
  refine Formalism.L2.DIV.resS_eq_zero_of_prV P v hov _ ?_
  show prV (E := E) v (iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x z i -
    iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x' z i) = 0
  rw [map_sub, map_mul (prV (E := E) v), map_mul (prV (E := E) v), updn_prV_pullV h, sub_self]

variable [NeZero n] (ST SG : Finset (Pl E))

theorem updn_f_loc {v : HeightOneSpectrum (𝓞 F)} (P : ST) (hov : IsOver v P.1)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    (decoRaw ST SG x).f P = (decoRaw ST SG x').f P := by
  funext z
  show (open Classical in if z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
      then redA P.1 (pullV x z (lastIdx n)) else 0) =
    (open Classical in if z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n))
      then redA P.1 (pullV x' z (lastIdx n)) else 0)
  rw [← updn_mem_loc hov h]
  by_cases hz : z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
  · rw [if_pos hz, if_pos hz, updn_red_loc hov h hz]
  · rw [if_neg hz, if_neg hz]

theorem updn_be_loc {v : HeightOneSpectrum (𝓞 F)} (w : SG) (hov : IsOver v w.1)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    (decoRaw ST SG x).be w = (decoRaw ST SG x').be w := by
  funext z
  show (open Classical in if z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
      then fun i => redA w.1 (pullV x z i) else 0) =
    (open Classical in if z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n))
      then fun i => redA w.1 (pullV x' z i) else 0)
  rw [← updn_mem_loc hov h]
  by_cases hz : z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
  · rw [if_pos hz, if_pos hz]
    funext i
    exact updn_red_loc hov h hz i
  · rw [if_neg hz, if_neg hz]

structure Deco.SameOff (v : HeightOneSpectrum (𝓞 F)) (d d' : Deco E n ST SG) : Prop where
  N : ∀ Q : Pl E, ¬ IsOver v Q → localization₂ Q.asIdeal d.N = localization₂ Q.asIdeal d'.N
  f : ∀ Q : ST, ¬ IsOver v Q.1 → d.f Q = d'.f Q
  be : ∀ w : SG, ¬ IsOver v w.1 → d.be w = d'.be w

end Loc

section Move

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG (E := E) (n := n) (SG := SG)))

end Move

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Host

section TBig

variable {X : Fields} {Pr : Primes X}

end TBig

section Gen

open GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

end Gen

section ColsRam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColsRam

section Delta

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end Delta

section ColsUD

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColsUD

section SeenEx

variable {X : Fields} {Pr : Primes X}

end SeenEx

section Pos

open ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

def GSD.pairEmb (σ : K →+* ℂ) (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

theorem GSD.map_pair (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (x y : S.V) :
    σ (S.pair x y) = S.pairEmb σ x y := by
  conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
  starRingEnd_apply, map_mul, hσ, GSD.pairEmb, GSD.gramV, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def GSD.ipEmb (h : S.Ok) (σ : K →+* ℂ) (φ ψ : S.D → S.V) : ℂ :=
  letI : Fintype S.Cl := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ * S.pairEmb σ (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))

theorem GSD.ipAt_eq_ipEmb (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.D → S.V) :
    S.ipAt h v φ ψ = S.ipEmb h v.embedding φ ψ := rfl

theorem GSD.map_ip (h : S.Ok) (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (φ ψ : S.D → S.V) :
    σ (S.ip h φ ψ) = S.ipEmb h σ φ ψ := by
  let _ : Fintype S.Cl := h.fintypeCl
  unfold GSD.ip GSD.ipOf GSD.ipEmb CSD.csum

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  congr 1
  exact S.map_pair σ hσ _ _

end Pos

section ColPos

open ComplexOrder

variable {X : Fields}

variable {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColPos

section LatGen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

end LatGen

section ColLat

variable {X : Fields}

variable {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColLat

section Cert

end Cert

section GaussInst

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end GaussInst

def ndIota : Qb →+* ℂ :=
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Qb)).toRingHom

section OfSizes

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end OfSizes

section InstThms

open ComplexOrder

end InstThms

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

section PhiLaw

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

def PhiGSLaw (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) : Prop :=
  ∀ γ ∈ LocE.JGsym P q k₀ rS r t n c, ∀ κ ∈ LocE.JGsym P q k₀ rS r t n' c', ∀ x : HomE E (n' + c') (n + c),
    LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) =
      LocE.lamGBS q ψ₀ χ k₀ r t j n c γ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det γ : Eˣ) : E))⁻¹ *
        (LocE.lamGBS q ψ₀ χ k₀ r t (j - 1) n' c' κ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det κ : Eˣ) : E))⁻¹) *
          LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n x

structure PhiGSLawHyp (P : HeightOneSpectrum (𝓞 E)) (q k₀ rS r t j c' n' c n : ℕ) : Prop where
  hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal
  hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2
  hj : 1 ≤ j
  hk' : k₀ ≤ n'
  hk : k₀ ≤ n
  hr : k₀ + rS < r
  ht : 0 < t
  hsrc : n' + c' = r + (j - 1) * t
  htgt : n + c = r + j * t

end PhiLaw

end Formalism.L2.Col
end
end

section

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def ocbBEnt {E : Type} [Field E] {N' N : ℕ} (n' n q : ℕ) (y : HomE E N' N) (l s : ℕ) : E :=
  Loc.atN (y (Loc.eN E N' s)) l * (q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l)

theorem ocbBEnt_entB {E : Type} [Field E] [NumberField E] {N' N : ℕ} (q k₀ c' n' c n : ℕ) (y : HomE E N' N) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) y p p' = ocbBEnt n' n q y (LocE.fIdx k₀ c n p) (LocE.fIdx k₀ c' n' p') := rfl

end Formalism.L2.Col
end
end
