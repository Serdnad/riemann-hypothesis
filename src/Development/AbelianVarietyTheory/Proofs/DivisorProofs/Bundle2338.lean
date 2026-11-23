module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimePart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.BotClassDict GlobalTheory.NormSum.VacInt

variable {D : D7}

theorem idem_orth {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D w ε') (hv : v ≠ w) : ε * ε' = 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨α', rfl, k1, k0⟩ := h'
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext _ fun u => ?_)
  change α u * α' u = 0
  by_cases hu : u = v
  · subst hu
    exact (congrArg (α u * ·) (k0 u hv)).trans (mul_zero _)
  · exact (congrArg (· * α' u) (h0 u hu)).trans (zero_mul _)

theorem cut_mul_cut {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {e f : R} (h : e * f = 0) (A : Matrix n n R) :
    (e • A + (1 - e • (1 : Matrix n n R))) * (f • A + (1 - f • (1 : Matrix n n R))) =
      (e + f) • A + (1 - (e + f) • (1 : Matrix n n R)) := by
  have h' : f * e = 0 := by rw [mul_comm, h]
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, smul_sub, smul_add,
    h, h', zero_smul, add_smul]
  abel

theorem mt_mul (V : HSp D) (x y : GA D V) :
    Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_prod (V : HSp D) (g : GA D V) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F)
    (hε : ∀ v, IsPlaceIdem D v (ε v)) (L : List (HeightOneSpectrum (𝓞 D.host.F))) (hL : L.Nodup) :
    Formalism.L2.Theta.mt V (L.map fun v => GlobalTheory.VacStab.locPart V v g).prod =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (L.map ε).sum • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (L.map ε).sum • 1) := by
  induction L with
  | nil =>
    rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil, RingHom.map_zero, zero_smul, zero_smul, zero_add, sub_zero]
    rfl
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    have h0 : ε v * (L.map ε).sum = 0 := by
      rw [← List.sum_map_mul_left]
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact idem_orth (hε v) (hε w) fun e => hL.1 (e ▸ hw)
    rw [List.map_cons, List.prod_cons, mt_mul, GlobalTheory.VacStab.mt_locPart V (hε v), ih hL.2, List.map_cons, List.sum_cons,
      RingHom.map_add]
    exact cut_mul_cut (by rw [← RingHom.map_mul, h0, RingHom.map_zero]) _

theorem natCast_mem_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : ℕ)
    (Q : HeightOneSpectrum (𝓞 E)) : (q : 𝓞 F) ∈ (Q.under (𝓞 F)).asIdeal ↔ (q : 𝓞 E) ∈ Q.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 E) _ ∈ Q.asIdeal ↔ _
  rw [map_natCast]

theorem finQ_sum_idem {q : ℕ} (hq : q.Prime) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : ∀ v, v ∈ S ↔ (q : 𝓞 D.host.F) ∈ v.asIdeal) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F)
    (hε : ∀ v, IsPlaceIdem D v (ε v)) :
    finQ D (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (∑ v ∈ S, ε v)) = eps D.host.E fun p => p = q := by
  apply (GlobalTheory.BotFormula.toFinE D).injective
  refine FiniteAdeleRing.ext _ fun Q => ?_
  have hev : ∀ w : HeightOneSpectrum (𝓞 D.host.F), (∑ v ∈ S, ε v).2 w = if w ∈ S then 1 else 0 := by
    intro w
    have e1 : (∑ v ∈ S, ε v).2 w = ∑ v ∈ S, evalV D.host.F w (sndA D.host.F (ε v)) := by

      rw [← map_sum, ← map_sum]
      rfl
    have e2 : ∀ v, evalV D.host.F w (sndA D.host.F (ε v)) = if w = v then 1 else 0 := by
      intro v
      obtain ⟨α, h, h1, h0⟩ := hε v
      rw [h]
      change evalV D.host.F w α = _
      split_ifs with hw
      · subst hw; exact h1
      · exact h0 w hw
    rw [e1, Finset.sum_congr rfl fun v _ => e2 v, Finset.sum_ite_eq]
  have hr : GlobalTheory.BotFormula.toFinE D (eps D.host.E fun p => p = q) Q =
      GlobalTheory.AdeleBaseChange.locMap ℚ Q (if pr (Q.under (𝓞 ℚ)) = q then 1 else 0) := by
    have := toFinE_tmul (D := D) 1 (idem fun p => p = q)
    rw [map_one, one_mul] at this
    refine (congrArg (fun x : FiniteAdeleRing (𝓞 D.host.E) D.host.E => x Q) this).trans ?_
    refine (GlobalTheory.AdeleBaseChange.adMap_apply _ Q).trans (congrArg _ ?_)
    rw [idem, mkInt_apply]
    congr
  have hiff : Q.under (𝓞 D.host.F) ∈ S ↔ pr (Q.under (𝓞 ℚ)) = q := by
    rw [hS, natCast_mem_under, ← Nat.prime_dvd_prime_iff_eq (pr_prime _) hq, pr_dvd_iff, natCast_mem_under]
  rw [GlobalTheory.ZeroAtPlaces.comp_base, hev, hr]
  by_cases h : Q.under (𝓞 D.host.F) ∈ S
  · rw [if_pos h, if_pos (hiff.1 h), map_one, map_one]
  · rw [if_neg h, if_neg (fun e => h (hiff.2 e)), map_zero, map_zero]

theorem exists_prod_eq_part : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (q : ℕ), q.Prime → ∀ g : Formalism.L2.Theta.GA D V, ∃ l : List (Formalism.L2.Theta.GA D V), (∀ h ∈ l, ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), Formalism.L2.Theta.IsPlaceIdem D v ε ∧ (q : 𝓞 D.host.F) ∈ v.asIdeal ∧ GlobalTheory.WeilParts.SuppPl ε V h) ∧ GlobalTheory.BotClassDict.finStd V hG l.prod = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) (GlobalTheory.BotClassDict.finStd V hG g) := by
  intro D V hG q hq g
  have hI : Ideal.span {(q : 𝓞 D.host.F)} ≠ ⊥ := by simpa using hq.ne_zero
  let S : Finset (HeightOneSpectrum (𝓞 D.host.F)) := (Ideal.finite_factors hI).toFinset
  have hS : ∀ v, v ∈ S ↔ (q : 𝓞 D.host.F) ∈ v.asIdeal := fun v => by
    simp [S, Ideal.dvd_span_singleton]
  choose ε hε using fun v : HeightOneSpectrum (𝓞 D.host.F) => GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  refine ⟨S.toList.map fun v => GlobalTheory.VacStab.locPart V v g, ?_, ?_⟩
  · intro h hh
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hh
    exact ⟨v, ε v, hε v, (hS v).1 (Finset.mem_toList.1 hv), GlobalTheory.VacStab.suppPl_locPart V (hε v) g⟩
  · have hm := mt_prod V g ε hε S.toList (Finset.nodup_toList S)
    rw [Finset.sum_map_toList] at hm
    have he := finQ_sum_idem hq S hS ε hε
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    have h1 : finQ D ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) i j) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · exact RingHom.map_one _
      · exact RingHom.map_zero _
    change finQ D (Formalism.L2.Theta.mt V _ i j) = eps D.host.E (fun p => p = q) * finQ D (Formalism.L2.Theta.mt V g i j) +
      (1 - eps D.host.E fun p => p = q) * (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j
    rw [hm, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, he, h1, sub_mul, one_mul]

end GlobalTheory.PrimePart

end
end

section

open IsLocalRing

namespace GlobalTheory.FiniteLocalCompleteness

theorem precomplete_of_finite {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (M : Type) [AddCommGroup M]
    [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨a • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    have : AdicCompletion.of I R a = algebraMap R (AdicCompletion I R) a := rfl
    rw [this, algebraMap_smul]
  | add s t hs ht =>
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

theorem precomplete_of_pow_le {S : Type} [CommRing S] (I J : Ideal S) [hI : IsPrecomplete I S] (hIJ : I ≤ J) (k : ℕ)
    (hk : J ^ (k + 1) ≤ I) : IsPrecomplete J S := by
  refine ⟨fun f hf => ?_⟩
  have h1 : ∀ n, (J ^ ((k + 1) * n) • ⊤ : Submodule S S) ≤ I ^ n • ⊤ := fun n => by
    refine Submodule.smul_mono_left ?_
    rw [pow_mul]
    exact Ideal.pow_right_mono hk n
  obtain ⟨L, hL⟩ := hI.prec (f := fun n => f ((k + 1) * n))
    (fun {m n} h => (hf (Nat.mul_le_mul_left _ h)).mono (h1 m))
  refine ⟨L, fun n => ?_⟩
  refine (hf (show n ≤ (k + 1) * n by nlinarith)).trans ((hL n).mono ?_)
  exact Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)

theorem isLocalRing_of_complete {S : Type} [CommRing S] [IsDomain S] (I : Ideal S) [IsAdicComplete I S]
    [IsArtinianRing (S ⧸ I)] : IsLocalRing S := by
  have hjac := IsAdicComplete.le_jacobson_bot I
  have hu : ∀ z ∈ I, IsUnit (1 - z) := fun z hz => by
    have := Ideal.mem_jacobson_bot.1 (hjac (I.neg_mem hz)) 1
    simpa [sub_eq_add_neg, add_comm] using this
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨n, y', hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I x) (1 : S ⧸ I)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
  simp only [smul_eq_mul, mul_one] at hy
  set X := Ideal.Quotient.mk I x with hX
  set Y := Ideal.Quotient.mk I y with hY
  have hk : ∀ k : ℕ, X ^ n * (X * Y) ^ k = X ^ n := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      calc X ^ n * (X * Y) ^ (k + 1) = (X ^ (n + 1) * Y) * (X * Y) ^ k := by ring
        _ = X ^ n := by rw [Nat.succ_eq_add_one] at hy; rw [hy, ih]
  have he : ((X * Y) ^ n) ^ 2 = (X * Y) ^ n := by
    calc ((X * Y) ^ n) ^ 2 = (X ^ n * (X * Y) ^ n) * Y ^ n := by ring
      _ = (X * Y) ^ n := by rw [hk]; ring
  have hE : Ideal.Quotient.mk I ((x * y) ^ n) = (X * Y) ^ n := by simp [hX, hY]
  obtain ⟨a, ha, hae⟩ := HenselianRing.is_henselian (I := I) (Polynomial.X ^ 2 - Polynomial.X : Polynomial S)
    (by monicity!) ((x * y) ^ n)
    (by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, map_sub]
      rw [map_pow, hE, he, sub_self])
    (by
      have : Ideal.Quotient.mk I (Polynomial.eval ((x * y) ^ n)
          (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X : Polynomial S))) = 2 * (X * Y) ^ n - 1 := by
        rw [← hE]
        simp [one_add_one_eq_two, map_ofNat]
      rw [this]
      exact IsUnit.of_mul_eq_one (2 * (X * Y) ^ n - 1) (by linear_combination 4 * he))
  have ha' : a * (a - 1) = 0 := by
    have : a ^ 2 - a = 0 := by simpa using ha
    linear_combination this
  rcases mul_eq_zero.1 ha' with h0 | h0
  · right
    subst h0
    have h2 : (X * Y) ^ n = 0 := by
      rw [← hE, Ideal.Quotient.eq_zero_iff_mem]
      simpa using hae
    have h3 : x ^ n ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← hX, ← hk n, h2, mul_zero]
    exact isUnit_of_dvd_unit (one_sub_dvd_one_sub_pow x n) (hu _ h3)
  · obtain rfl : a = 1 := sub_eq_zero.1 h0
    have h2 := hu _ hae
    rw [sub_sub_cancel] at h2
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h3 := hk 1
      left
      have h4 : 1 - x * y ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simp only [pow_zero, pow_one, one_mul] at h3
        rw [map_sub, map_one, map_mul, ← hX, ← hY, h3, sub_self]
      have h5 := hu _ h4
      rw [sub_sub_cancel] at h5
      exact isUnit_of_mul_isUnit_left h5
    · left
      exact isUnit_of_mul_isUnit_left ((isUnit_pow_iff hn.ne').1 h2)

theorem local_complete_of_finite (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] :
    ∃ _ : IsLocalRing S, IsAdicComplete (maximalIdeal S) S := by
  haveI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  haveI : IsPrecomplete (maximalIdeal R) S := precomplete_of_finite _ S
  haveI : IsAdicComplete (maximalIdeal R) S := ⟨⟩
  set I := (maximalIdeal R).map (algebraMap R S) with hI
  haveI : IsAdicComplete I S := (IsAdicComplete.map_algebraMap_iff _ _).2 inferInstance
  haveI : IsArtinianRing (S ⧸ I) := by
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ I) := Module.Finite.of_restrictScalars_finite R _ _
    exact IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  haveI hl : IsLocalRing S := isLocalRing_of_complete I
  refine ⟨hl, ?_⟩
  have hne : I ≠ ⊤ := by
    intro h
    have := IsAdicComplete.le_jacobson_bot I
    rw [h, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at this
    exact (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 this)
  have hrad : maximalIdeal S ≤ I.radical := by
    intro x hx
    obtain ⟨n, y', hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I x) (1 : S ⧸ I)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
    simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
    have hu : IsUnit (1 - x * y) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right y (maximalIdeal S) hx)
    refine ⟨n, (Ideal.mul_unit_mem_iff_mem I hu).1 ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_mul, map_pow, map_sub, map_one]
    linear_combination -hy
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal S) S :=
    precomplete_of_pow_le I _ (le_maximalIdeal hne) k ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk)
  exact ⟨⟩

theorem exists_normal (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : Type) [CommRing D] [IsDomain D]
    [Algebra R D] [Module.Finite R D] [FaithfulSMul R D] (hR : GlobalTheory.TorRef.IsCN R) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : D →+* R'),
      GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp (algebraMap R D) = ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := hR
  letI : Algebra (FractionRing R) (FractionRing D) := FractionRing.liftAlgebra R (FractionRing D)
  haveI : IsScalarTower R (FractionRing R) (FractionRing D) := FractionRing.isScalarTower_liftAlgebra R _
  haveI : FiniteDimensional (FractionRing R) (FractionRing D) :=
    Module.Finite.of_isLocalization R D (nonZeroDivisors R) (Rₚ := FractionRing R) (Sₚ := FractionRing D)
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  haveI : Algebra.IsIntegral (FractionRing R) (FractionRing D) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (FractionRing R) (FractionRing D) := Algebra.IsSeparable.of_integral _ _
  let S := integralClosure R (FractionRing D)
  haveI : Module.Finite R S := IsIntegralClosure.finite R (FractionRing R) (FractionRing D) S
  haveI : IsIntegrallyClosed S := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  have hL : Function.Injective (algebraMap R (FractionRing D)) := FaithfulSMul.algebraMap_injective R _
  have hS : Function.Injective (algebraMap R S) := fun a b h => hL (congrArg Subtype.val h)
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hS
  obtain ⟨hl, hc⟩ := local_complete_of_finite R S
  let ψ : D →ₐ[R] FractionRing D := IsScalarTower.toAlgHom R D _
  let σ : D →ₐ[R] S := ψ.codRestrict S fun c => (Algebra.IsIntegral.isIntegral c).map ψ
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite _ _
  refine ⟨S, inferInstance, inferInstance, hl, algebraMap R S, σ.toRingHom,
    ⟨IsNoetherianRing.of_finite R S, inferInstance, hc, charZero_of_injective_algebraMap hS⟩, hS,
    RingHom.finite_algebraMap.2 inferInstance, Algebra.IsIntegral.isLocalHom R S, σ.comp_algebraMap⟩

theorem main (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : Type) [CommRing C] (φ : R →+* C)
    (hR : GlobalTheory.TorRef.IsCN R) (hφ : Function.Injective φ) (hfin : φ.Finite) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : C →+* R'),
      GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp φ = ρ := by
  letI : Algebra R C := φ.toAlgebra
  haveI : Module.Finite R C := hfin
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := R) (S := C) (⊥ : Ideal R) ⊥
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]; exact ((RingHom.injective_iff_ker_eq_bot _).1 hφ).le)
  have hD : Function.Injective (algebraMap R (C ⧸ P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ P.comap (algebraMap R C) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    change a ∈ Ideal.under R P at this
    rwa [hPc] at this
  haveI : FaithfulSMul R (C ⧸ P) := (faithfulSMul_iff_algebraMap_injective _ _).2 hD
  obtain ⟨R', i1, i2, i3, ρ, σ, h1, h2, h3, h4, h5⟩ := exists_normal R (C ⧸ P) hR
  exact ⟨R', i1, i2, i3, ρ, σ.comp (Ideal.Quotient.mk P), h1, h2, h3, h4, h5⟩

end GlobalTheory.FiniteLocalCompleteness
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixExp

theorem pow_mul_le_of_cls_eq {k : Type} [Field k] {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)]
    (h : Published.NefProductNonneg) (hp : IsProjOver (strHom k (X := Y))) {e : ℕ}
    (hD : topologicalKrullDim Y = e) {N N' N₀ : LB Y} (hN : IsNef k N) (hN' : IsNef k N')
    (h₀ : N₀.IsLB) (a b : ℕ) (hc : cls N₀ h₀ = a • cls N hN.isLB + b • cls N' hN'.isLB) :
    (a : ℤ) ^ e * interNum k (structureModule Y) (fun _ : Fin e => N) ≤
      interNum k (structureModule Y) (fun _ : Fin e => N₀) := by
  have := isNoetherian_of_isProjOver hp
  have H := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k Y) (structureModule Y) hp
    (d := e) (by rw [suppDim_structureModule, hD])
  have hL : ∀ j, IsNef k ((![N, N'] : Fin 2 → LB Y) j) := fun j => by
    fin_cases j
    exacts [hN, hN']
  have e₁ := H.interNum_of_cls_eq_sum (L := ![N, N']) (fun j => (hL j).isLB)
    (Q := fun _ => N₀) (fun _ => h₀) (fun _ => ![(a : ℤ), (b : ℤ)])
    (fun _ => by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, natCast_zsmul]
      exact hc)
  have e₂ := Finset.single_le_sum
    (f := fun c : Fin e → Fin 2 =>
      (∏ i, (![(a : ℤ), (b : ℤ)] : Fin 2 → ℤ) (c i)) *
        interNum k (structureModule Y) (![N, N'] ∘ c))
    (fun c _ => mul_nonneg (Finset.prod_nonneg fun i _ => by
        generalize c i = j
        fin_cases j <;> simp)
      (h.interNum_nonneg (N := ![N, N'] ∘ c) hp hD fun i => hL (c i)))
    (Finset.mem_univ fun _ => 0)
  rw [e₁]
  refine le_trans (le_of_eq ?_) e₂
  simp only [Matrix.cons_val_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

end GlobalTheory.MixExp


open GlobalTheory.MixExp in
theorem GlobalTheory.mixExp_interNumRed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' N₀ : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (h₀ : N₀.IsLB) (a b : ℕ) (Z : Closeds X) (e : ℕ), IsNef k N → IsNef k N' → cls N₀ h₀ = a • cls N hN + b • cls N' hN' → topologicalKrullDim (Z : Set X) = e → (a : ℤ) ^ e * interNumRed k Z (fun _ : Fin e => N) ≤ interNumRed k Z (fun _ : Fin e => N₀) := by
  intro h k _ X q hq
  letI := algebraΓOfHom q
  intro N N' N₀ hN hN' h₀ a b Z e hnef hnef' hc hZ
  have hp : IsProjOver (strHom k (X := X)) := by rwa [strHom_eq (f := q) fun _ => rfl]
  letI := algebraΓAlong k (redι Z)
  have hi := appTop_algebraMap_along k (redι Z)
  have hpZ : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    obtain ⟨n, f, hf, hs⟩ := hp
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs, comp_strHom hi]⟩
  change (a : ℤ) ^ e * interNumOn k (redι Z) (fun _ : Fin e => N) ≤
    interNumOn k (redι Z) (fun _ : Fin e => N₀)
  rw [interNumOn_eq_interNum_pull hi fun _ => hN, interNumOn_eq_interNum_pull hi fun _ => h₀]
  refine pow_mul_le_of_cls_eq h.1 hpZ ((topologicalKrullDim_red Z).trans hZ)
    (hnef.pull_of_isClosedImmersion (redι Z) hi) (hnef'.pull_of_isClosedImmersion (redι Z) hi)
    (LB.isLB_pull h₀ (redι Z)) a b ?_
  rw [cls_pull h₀, cls_pull hN, cls_pull hN', hc, map_add (f := _), map_nsmul, map_nsmul]
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem nef_big_of_cls_eq_smul_add_smul : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (a b : ℕ), IsNef k N → IsBig k N → IsNef k N' → 0 < a → ∃ (N₀ : LB X) (h₀ : N₀.IsLB), cls N₀ h₀ = a • cls N hN + b • cls N' hN' ∧ IsNef k N₀ ∧ IsBig k N₀ := by
  intro hNN k _ X _ q hq
  letI := algebraΓOfHom q
  intro N N' hN hN' a b hNn hNb hN'n ha
  have hp : IsProjOver (strHom k (X := X)) := by
    rwa [strHom_eq (f := q) fun _ => rfl]
  obtain ⟨_, hH⟩ := exists_isAmpleLB_of_isProjOver hq
  refine ⟨tens (lbPow N a) (lbPow N' b), isLB_tens (isLB_lbPow hN a) (isLB_lbPow hN' b), ?_, ?_, ?_⟩
  · rw [cls_tens (isLB_lbPow hN a) (isLB_lbPow hN' b), cls_lbPow hN, cls_lbPow hN']
  · exact (hNn.pow hH a).tens (hN'n.pow hH b) hH
  · exact (hNb.pow (fun _ => rfl) hq ha).tens_nef hNN hp (hNn.pow hH a) (hN'n.pow hH b)

end GlobalTheory
end
