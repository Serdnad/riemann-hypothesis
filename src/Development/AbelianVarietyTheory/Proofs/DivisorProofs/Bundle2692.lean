module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle498
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle530
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle553
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadFromLocalization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle183
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle058
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle123
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle683
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle007
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem relAmple_local {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O]
    (t : SAB H (Sp O)) (hprop : IsProper t.G.hom) (hpol : GlobalTheory.LN.PolAt t (Out.jK O)) :
    Out.RelAmple t.G t.PP.L := by
  by_cases hf : _root_.IsField O
  · obtain ⟨u, ⟨mu⟩⟩ := GlobalTheory.PolLocal.exists_pull (Out.jK O) t
    obtain ⟨hA, hK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mu hpol
    haveI : IsIso (Out.jK O) := GlobalTheory.PolLocal.isIso_spMap _ (GlobalTheory.PolLocal.algebraMap_fractionRing_bijective O hf)
    exact (GlobalTheory.PolLocal.ample_kTriv_of_iso mu hA hK).1
  obtain ⟨V, _, _, _, ρ, hρ, hloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hf
  obtain ⟨tV, ⟨mV⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap ρ) t
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap V (FractionRing V))) tV
  have hpV : GlobalTheory.LN.PolAt tV (Out.jK V) := GlobalTheory.PolNormal.polAt_generic_pull ρ hρ mV hpol
  obtain ⟨hAK, hKK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mK hpV
  obtain ⟨hAV, hKV⟩ := GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre GlobalTheory.HomExtExamples.homExtSt_holds GlobalTheory.allSixLaws.1
    GlobalTheory.allSixLaws.2.1 E H V (FractionRing V) tV tK mK (GlobalTheory.PolLocal.isProper_of_map mV hprop) hAK hKK
  obtain ⟨uk, ⟨mk⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (IsLocalRing.residue V)) tV
  obtain ⟨hAk, hKk⟩ := GlobalTheory.PolLocal.pull_ample_kTriv mk hAV hKV
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mV mk
  let β : O →+* IsLocalRing.ResidueField V := (IsLocalRing.residue V).comp ρ
  have hpβ : GlobalTheory.LN.PolAt t (spMap β) := by
    rw [GlobalTheory.PolLocal.spMap_comp]
    exact GlobalTheory.LocM.PolFibre.polAt_of_map n (by haveI := hprop; infer_instance) hAk hKk
  obtain ⟨r, hr, hA⟩ := GlobalTheory.PolNearAmple.relAmple_near_of_polAt E H O t hprop (IsLocalRing.ResidueField V) β hpβ
  have hu : IsUnit r := isUnit_of_map_unit ρ r ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hr)
  obtain ⟨m₀, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  have e : spMap (RingHom.id O) = 𝟙 (Sp O) := by
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  exact hA O (RingHom.id O) hu t (e ▸ m₀)

theorem relAmple_kTriv_of_generic {S : Type} [CommRing S] [IsDomain S] [CharZero S] [IsNoetherianRing S]
    (t : SAB H (Sp S)) (hp : IsProper t.G.hom) (hg : GlobalTheory.LN.PolAt t (Out.jK S)) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  have hA : Out.RelAmple t.G t.PP.L := by
    have := t.semi.quasiCompact
    have := t.semi.separated
    refine GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance fun q => ?_
    have : q.asIdeal.IsPrime := q.isPrime
    let O := Localization.AtPrime q.asIdeal
    obtain ⟨tO, ⟨m⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap S O)) t
    have hi : Function.Injective (algebraMap S O) :=
      IsLocalization.injective O q.asIdeal.primeCompl_le_nonZeroDivisors
    have : CharZero O := charZero_of_injective_algebraMap hi
    have hA := relAmple_local tO (GlobalTheory.PolLocal.isProper_of_map m hp) (GlobalTheory.PolNormal.polAt_generic_pull _ hi m hg)
    obtain ⟨w, hw, -⟩ := m.lin
    exact GlobalTheory.AmpleSpreadAt.relAmple_spread_at S q t.G t.PP.L hp t.PP.isLB tO.G m.φ tO.PP.L m.cart.1 tO.PP.isLB
      ⟨w, hw⟩ hA
  exact ⟨hA, GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic E H S t hp hA hg⟩

theorem isProper_relAmple_kTriv_of_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (S : Scheme.{0}) (x : S ⟶ Sp R) (t' : SAB H S), (∀ s : S, ∏ i, tt i ∉ (x s).asIdeal) → Nonempty (SABMap t' t x) → IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab S x t' hx ⟨mx⟩
  have : CharZero R := algebraRat.charZero R
  have hf : ∏ i, tt i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => htt i
  generalize ∏ i, tt i = f at hf hab hx
  let Rf := Localization.Away f
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hi : Function.Injective (algebraMap R Rf) := IsLocalization.injective Rf hle
  have : IsDomain Rf := IsLocalization.isDomain_localization hle
  have : CharZero Rf := charZero_of_injective_algebraMap hi
  obtain ⟨tf, ⟨mf⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap R Rf)) t
  have hrange : Set.range (spMap (algebraMap R Rf)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range Rf f
  have habf : abLocus tf.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi mf.cart.1 z).1 ((hab _).2 (hrange.le ⟨z, rfl⟩))
  have hg : GlobalTheory.LN.PolAt tf (Out.jK Rf) := GlobalTheory.PolNormal.polAt_generic_pull _ hi mf (GlobalTheory.DatUniq.polAt_of_unif P)
  have hpf : IsProper tf.G.hom := GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H Rf tf hg habf
  obtain ⟨hA, hK⟩ := relAmple_kTriv_of_generic tf hpf hg
  have : IsOpenImmersion (spMap (algebraMap R Rf)) := by
    unfold spMap
    exact IsOpenImmersion.of_isLocalization f
  have hr : Set.range x ⊆ Set.range (spMap (algebraMap R Rf)) := by
    rintro _ ⟨s, rfl⟩
    exact hrange.ge (hx s)
  obtain ⟨m', -⟩ := GlobalTheory.ArcObj.exists_sab_fac mf mx (g := IsOpenImmersion.lift _ x hr)
    (IsOpenImmersion.lift_fac _ _ hr).symm
  obtain ⟨w, hw, -⟩ := m'.lin
  exact ⟨GlobalTheory.PolLocal.isProper_of_map m' hpf,
    GlobalTheory.AmpleLocalBase.relAmple_baseChange m'.cart.1 tf.PP.isLB t'.PP.isLB ⟨w, hw⟩ hA,
    kTriv_pull m'.cart tf.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) hK⟩

end GlobalTheory.AbLocusPol
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsionLattice_moves_by_ringAction_completeDVR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt P.D.toPre K m) (x x' : TFK (R := V) K ⟶ P.A.A), 1 ≤ m → QkToAkU P.U.toUnifPre K m pk x → QkToAkU P.U.toUnifPre K m pk' x' → x' = x ≫ P.oA.act a → CongMod m pk'.y (a • pk.y) := by
  first | exact @GlobalTheory.UPoinc.qk_lattice_oAct | exact GlobalTheory.UPoinc.qk_lattice_oAct | (intros; apply GlobalTheory.UPoinc.qk_lattice_oAct <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory.PrincDvr

def powInf {B : Type} [CommRing B] (ϖ : B) : Ideal B := ⨅ n : ℕ, Ideal.span {ϖ ^ n}

variable {B : Type} [CommRing B] [IsLocalRing B] {ϖ : B}

theorem pow_not_mem_span_succ (hm : maximalIdeal B = Ideal.span {ϖ}) (hϖ : ϖ ∈ nonZeroDivisors B) (n : ℕ) :
    ϖ ^ n ∉ Ideal.span {ϖ ^ (n + 1)} := by
  intro h
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  have hn : ϖ ^ n ∈ nonZeroDivisors B := pow_mem hϖ n
  have e : (b * ϖ - 1) * ϖ ^ n = 0 := by linear_combination hb
  have e1 : b * ϖ - 1 = 0 := (mem_nonZeroDivisors_iff.1 hn).2 _ e
  have hmem : ϖ ∈ maximalIdeal B := by rw [hm]; exact Ideal.mem_span_singleton_self ϖ
  exact (mem_maximalIdeal _).1 hmem (isUnit_iff_exists_inv.2 ⟨b, by rw [mul_comm]; exact sub_eq_zero.1 e1⟩)

theorem exists_unit_mul_pow (hm : maximalIdeal B = Ideal.span {ϖ}) (x : B) (hx : x ∉ powInf ϖ) :
    ∃ (n : ℕ) (u : Bˣ), x = u * ϖ ^ n := by
  classical
  have hex : ∃ n, ¬ ϖ ^ n ∣ x := by
    by_contra h
    push_neg at h
    exact hx (Ideal.mem_iInf.2 fun n => Ideal.mem_span_singleton.2 (h n))
  obtain ⟨N, hN, hmin⟩ : ∃ N, ¬ ϖ ^ N ∣ x ∧ ∀ m < N, ϖ ^ m ∣ x :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_not.1 (Nat.find_min hex hm)⟩
  clear hex
  have hN0 : N ≠ 0 := by
    intro h0; apply hN; rw [h0, pow_zero]; exact one_dvd x
  obtain ⟨u, hu⟩ : ϖ ^ (N - 1) ∣ x := hmin _ (Nat.sub_lt (Nat.pos_of_ne_zero hN0) one_pos)
  have hu' : IsUnit u := by
    by_contra hu'
    have hmem : u ∈ Ideal.span {ϖ} := by rw [← hm]; exact (mem_maximalIdeal u).2 hu'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hmem
    apply hN
    refine ⟨c, ?_⟩
    rw [hu, hc, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)]
  exact ⟨N - 1, hu'.unit, by rw [hu, IsUnit.unit_spec, mul_comm]⟩

theorem isPrime_powInf (hm : maximalIdeal B = Ideal.span {ϖ}) (hϖ : ϖ ∈ nonZeroDivisors B) :
    (powInf ϖ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    exact pow_not_mem_span_succ hm hϖ 0 (by simpa using Ideal.mem_iInf.1 h 1)
  · intro a b hab
    by_contra h
    push_neg at h
    obtain ⟨m, u, rfl⟩ := exists_unit_mul_pow hm a h.1
    obtain ⟨k, v, rfl⟩ := exists_unit_mul_pow hm b h.2
    have hmem := Ideal.mem_iInf.1 hab (m + k + 1)
    apply pow_not_mem_span_succ hm hϖ (m + k)
    have e1 : (u : B) * ϖ ^ m * (v * ϖ ^ k) = ((u * v : Bˣ) : B) * ϖ ^ (m + k) := by push_cast; ring
    have e : ϖ ^ (m + k) = (((u * v)⁻¹ : Bˣ) : B) * ((u : B) * ϖ ^ m * (v * ϖ ^ k)) := by
      rw [e1, Units.inv_mul_cancel_left]
    rw [e]
    exact Ideal.mul_mem_left _ _ hmem

theorem exists_cDvr_localHom : ∀ (B : Type) [CommRing B] [IsLocalRing B] (ϖ : B), maximalIdeal B = Ideal.span {ϖ} →
    ϖ ∈ nonZeroDivisors B → CharZero (ResidueField B) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W)
    (_ : IsLocalRing W) (h : B →+* W), GlobalTheory.LN.CDvr W ∧ IsLocalHom h ∧ h ϖ ≠ 0 := by
  intro B _ _ ϖ hm hϖ h0
  haveI := isPrime_powInf hm hϖ
  have hp0 : Ideal.Quotient.mk (powInf ϖ) ϖ ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    exact pow_not_mem_span_succ hm hϖ 1 (by simpa using Ideal.mem_iInf.1 h 2)
  have hnu : ∀ a : B, ¬ IsUnit a → ∃ c, Ideal.Quotient.mk (powInf ϖ) a =
      Ideal.Quotient.mk (powInf ϖ) ϖ * Ideal.Quotient.mk (powInf ϖ) c := by
    intro a ha
    have hmem : a ∈ Ideal.span {ϖ} := by rw [← hm]; exact (mem_maximalIdeal a).2 ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨c, by rw [← hc, map_mul, mul_comm]⟩
  have hpu : ¬ IsUnit (Ideal.Quotient.mk (powInf ϖ) ϖ) := by
    rintro ⟨w, hw⟩
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (w⁻¹ : (B ⧸ powInf ϖ)ˣ).val
    have e : Ideal.Quotient.mk (powInf ϖ) (ϖ * c) = Ideal.Quotient.mk (powInf ϖ) 1 := by
      rw [map_mul, hc, ← hw, Units.mul_inv, map_one]
    have h1 := Ideal.mem_iInf.1 (Ideal.Quotient.eq.1 e) 1
    rw [pow_one] at h1
    have h2 : (1 : B) ∈ Ideal.span {ϖ} := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self ϖ)) h1
      simpa using this
    exact pow_not_mem_span_succ hm hϖ 0 (by simpa using h2)
  have hirr : Irreducible (Ideal.Quotient.mk (powInf ϖ) ϖ) := by
    refine irreducible_iff.2 ⟨hpu, fun a b hab => ?_⟩
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    by_cases ha : IsUnit a'
    · exact Or.inl (ha.map _)
    · obtain ⟨c, hc⟩ := hnu a' ha
      right
      rw [hc, mul_assoc] at hab
      have e := mul_left_cancel₀ hp0 ((mul_one _).trans hab)
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact e.symm⟩
  have hfac : ∀ {x : B ⧸ powInf ϖ}, x ≠ 0 → ∃ n, Associated (Ideal.Quotient.mk (powInf ϖ) ϖ ^ n) x := by
    intro x hx
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : x' ∉ powInf ϖ := fun h => hx (Ideal.Quotient.eq_zero_iff_mem.2 h)
    obtain ⟨n, u, rfl⟩ := exists_unit_mul_pow hm x' hx'
    refine ⟨n, Units.map (Ideal.Quotient.mk (powInf ϖ)).toMonoidHom u, ?_⟩
    simp only [map_mul, map_pow, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring
  haveI : IsDiscreteValuationRing (B ⧸ powInf ϖ) :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, hfac⟩
  have hle : powInf ϖ ≤ RingHom.ker (residue B) := by
    intro a ha
    rw [RingHom.mem_ker, residue_eq_zero_iff, hm]
    simpa using Ideal.mem_iInf.1 ha 1
  have hc0 : CharZero (B ⧸ powInf ϖ) := RingHom.charZero (Ideal.Quotient.lift (powInf ϖ) (residue B) hle)
  have hloc : IsLocalHom (Ideal.Quotient.mk (powInf ϖ)) := ⟨fun a ha => by
    by_contra h
    obtain ⟨c, hc⟩ := hnu a h
    rw [hc] at ha
    exact hpu (isUnit_of_mul_isUnit_left ha)⟩
  obtain ⟨W, _, _, _, g, hW, hinj, hg⟩ := GlobalTheory.LocalCompletion.exists_cDvr_embedding (B ⧸ powInf ϖ) inferInstance
    PrincipalIdealRing.isNoetherianRing (IsDiscreteValuationRing.ringKrullDim_eq_one _) hc0
  refine ⟨W, inferInstance, inferInstance, inferInstance, g.comp (Ideal.Quotient.mk (powInf ϖ)), hW, ?_, ?_⟩
  · haveI := hloc; haveI := hg; infer_instance
  · intro h
    exact hp0 (hinj (by rw [map_zero]; exact h))

end GlobalTheory.PrincDvr
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.KeyEven.fractionRing_norm_one_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (C : Type) [NormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ a : FractionRing V, ‖algebraMap (FractionRing V) C a‖ = 1 → ∃ u : Vˣ, a = algebraMap V (FractionRing V) u := by
  intro V _ _ _ C _ _ hC a ha
  have key : ∀ x : V, ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖ = 1 → IsUnit x := by
    intro x hx
    by_contra hu
    have hm : x ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal x).2 hu
    have := hC.2 x hm
    rw [hx] at this
    exact lt_irrefl _ this
  rcases ValuationRing.isInteger_or_isInteger V a with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hu := key x (by rw [hx]; exact ha)
    exact ⟨hu.unit, by simp [hx]⟩
  · have hx' : ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖ = 1 := by
      rw [hx, map_inv₀, norm_inv, ha, inv_one]
    have hu := key x hx'
    refine ⟨hu.unit⁻¹, ?_⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    have h1 : algebraMap V (FractionRing V) (↑hu.unit⁻¹ : V) * algebraMap V (FractionRing V) x = 1 := by
      rw [← map_mul]
      have : (↑hu.unit⁻¹ : V) * x = 1 := by
        have := hu.unit.inv_mul
        simpa using this
      rw [this, map_one]
    rw [hx] at h1
    field_simp at h1
    exact h1.symm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.IntGauge

theorem exists_ball (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := by
  refine ⟨{ carrier := {x | ‖x‖ ≤ 1}
            mul_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq, norm_mul] at *
              exact mul_le_one₀ ha (norm_nonneg _) hb
            one_mem' := by simp
            add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
            zero_mem' := by simp
            neg_mem' := fun {a} ha => by simpa using ha
            mem_or_inv_mem' := fun x => by
              by_cases h : ‖x‖ ≤ 1
              · exact Or.inl h
              · right
                show ‖x⁻¹‖ ≤ 1
                rw [norm_inv]
                exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h)) }, fun x => Iff.rfl⟩

theorem exists_intN : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∃ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN := by
  intro V _ _ _ _ _ D C _ _ _ _ _ _ hC
  obtain ⟨S, hS⟩ := exists_ball C
  obtain ⟨N, ν, hν⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.firstFiveLaws.1 V D.toPre D.psi_even D.tau_bimult
    C S (fun r => (hS _).2 (hC.1 r))
  exact ⟨N, ν, S, hS, hν⟩

end GlobalTheory.IntGauge
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.CompleteDvrToComplex

theorem norm_lt_one_of_mem_maximalIdeal {W C : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [NormedField C] (g : W →+* C) (hg : ∀ a, ‖g a‖ ≤ 1) {b : W}
    (hb0 : b ≠ 0) (hb : ‖g b‖ < 1) {a : W} (ha : a ∈ IsLocalRing.maximalIdeal W) : ‖g a‖ < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n := Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)
  have h : ‖g a‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, hc, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)
  exact lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)

theorem norm_le_one_padicComplexInt (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  have hv : ((Valued.v (x : ℂ_[p]) : NNReal) : ℝ) = ‖(x : ℂ_[p])‖ := by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, (show Valuation.RankLeOne.hom' Valued.v = MonoidWithZeroHom.ValueGroup₀.embedding from rfl),
      Valuation.embedding_restrict]
  rw [← hv]
  have : Valued.v (x : ℂ_[p]) ≤ 1 := x.2
  exact_mod_cast this

theorem norm_natCast_prime_lt_one (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have hc : ((p : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := by push_cast; rfl
  rw [hc] at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem exists_complete_closed_field :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : Algebra (FractionRing V) C), CExt V (IsLocalRing.maximalIdeal V) C ∧ Nonempty (C ≃+* ℂ) := by
  intro V _ _ _ _ hc hf
  let T : Formalism.L2.Pj.CDVR := { V := V }
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hf
  letI : Algebra (FractionRing V) ℂ_[p] := k.toAlgebra
  obtain ⟨eC⟩ := GlobalTheory.MomOne.Inh.nonempty_iso p
  refine ⟨ℂ_[p], inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, this, ⟨?_, ?_⟩, ⟨eC.symm⟩⟩
  · have hle : ∀ r : V, ‖k (algebraMap V (FractionRing V) r)‖ ≤ 1 := fun r => by
      rw [← hk r]
      exact norm_le_one_padicComplexInt p (kO r)
    exact hle
  · have hle : ∀ r : V, ‖(k.comp (algebraMap V (FractionRing V))) r‖ ≤ 1 := fun r => by
      rw [RingHom.comp_apply, ← hk r]
      exact norm_le_one_padicComplexInt p (kO r)
    have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    have hpl : ‖(k.comp (algebraMap V (FractionRing V))) (p : V)‖ < 1 := by
      rw [map_natCast]; exact norm_natCast_prime_lt_one p
    intro r hr
    exact norm_lt_one_of_mem_maximalIdeal _ hle hp0 hpl hr

end GlobalTheory.CompleteDvrToComplex
end
