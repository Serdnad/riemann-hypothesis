module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle098
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle100
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_isEps_for_inj (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, ?_, ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro hh
    have := h 1
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val hh

theorem eq_zero_of_mem_span_pow_away {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (r ξ : A)
    [IsLocalization.Away r B] (hs : ∀ n : ℕ, ∀ a : A, ξ ^ n ∣ r * a → ξ ^ n ∣ a)
    (hh : ∀ a : A, (∀ n : ℕ, ξ ^ n ∣ a) → a = 0) (x : B)
    (hx : ∀ n : ℕ, x ∈ Ideal.span {algebraMap A B ξ} ^ n) : x = 0 := by
  have hs' : ∀ n m : ℕ, ∀ a : A, ξ ^ n ∣ r ^ m * a → ξ ^ n ∣ a := by
    intro n m
    induction m with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      apply ih
      apply hs
      rwa [← mul_assoc, ← pow_succ']
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) x
  have ha : a = 0 := by
    apply hh
    intro n
    have h1 : algebraMap A B a ∈ Ideal.map (algebraMap A B) (Ideal.span {ξ ^ n}) := by
      rw [Ideal.map_span, Set.image_singleton, map_pow, ← Ideal.span_singleton_pow,
        ← IsLocalization.mk'_spec B a s]
      exact Ideal.mul_mem_right _ _ (hx n)
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers r)] at h1
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ := h1
    exact hs' n m a (Ideal.mem_span_singleton.1 hm)
  simp [ha]

theorem algebraMap_AinfP_BdRp_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  obtain ⟨e, he⟩ := exists_isEps_for_inj l
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_mem_span_pow_away (l : Per.Ainf l) (xi e)
    (fun n a h => XiHaus.xi_sat he n a h) (GlobalTheory.MemLoc.eq_zero_of_forall_xi_pow_dvd l e he) x fun n => ?_
  rw [← GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he, ← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
    GlobalTheory.RingIface.ev_alg l n x
  rw [← h1, hx, map_zero]

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FilPrincipal

section General
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}

theorem evalₐ_eq_zero_iff (h : I = Ideal.span {a}) (n : ℕ) (y : AdicCompletion I R) :
    AdicCompletion.evalₐ I n y = 0 ↔ algebraMap R (AdicCompletion I R) a ^ n ∣ y := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : (I ^ n).map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a ^ n} := by
    have : I ^ n = Ideal.span {a ^ n} := by rw [h, Ideal.span_singleton_pow]
    rw [this, Ideal.map_span, Set.image_singleton, map_pow]
  rw [← Ideal.mem_span_singleton, ← e, ← Submodule.restrictScalars_mem R,
    ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective

theorem evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem regular_of_isDomain [IsDomain R] (h : I = Ideal.span {a}) (ha : a ≠ 0) (y : AdicCompletion I R)
    (hy : algebraMap R (AdicCompletion I R) a * y = 0) : y = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [map_zero, evalₐ_eq_zero_iff h]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
  have h1 : algebraMap R (AdicCompletion I R) a ^ (n + 1) ∣ y - algebraMap R _ r := by
    rw [← evalₐ_eq_zero_iff h, map_sub, evalₐ_algebraMap, hr, sub_self]
  have h2 := congrArg (AdicCompletion.evalₐ I (n + 1)) hy
  rw [map_mul, map_zero, evalₐ_algebraMap, ← hr, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h2
  have h3 : I ^ (n + 1) = Ideal.span {a ^ (n + 1)} := by rw [h, Ideal.span_singleton_pow]
  rw [h3, Ideal.mem_span_singleton, pow_succ', mul_dvd_mul_iff_left ha] at h2
  have h4 : algebraMap R (AdicCompletion I R) a ^ n ∣ algebraMap R _ r := by
    rw [← map_pow]; exact map_dvd _ h2
  have h5 := dvd_add ((pow_dvd_pow _ (Nat.le_succ n)).trans h1) h4
  rwa [sub_add_cancel] at h5

theorem isAdicComplete_span (h : I = Ideal.span {a}) :
    IsAdicComplete (Ideal.span {algebraMap R (AdicCompletion I R) a}) (AdicCompletion I R) := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : I.map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a} := by
    have : ∀ J : Ideal R, J = Ideal.span {a} → J.map (algebraMap R (AdicCompletion I R)) =
        Ideal.span {algebraMap R (AdicCompletion I R) a} := by
      rintro J rfl
      rw [Ideal.map_span, Set.image_singleton]
    exact this I h
  rw [← e, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete hfg

end General

theorem xi_ne_zero {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (he : IsEps e) : xi e ≠ 0 := by
  intro h0
  set a := (frobeniusEquiv (Per.Fl l) l).symm e with ha
  have h1 : xi e * (Per.tm a - 1) = Per.tm a ^ l - 1 := geom_sum_mul _ _
  rw [h0, zero_mul, eq_comm, sub_eq_zero, ← map_pow] at h1
  have h2 := congrArg (fun w : Per.Ainf l => w.coeff 0) h1
  simp only [WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h2
  have h3 : a = 1 := by
    apply (frobeniusEquiv (Per.Fl l) l).injective
    rw [frobeniusEquiv_apply, frobenius_def, h2, map_one]
  apply he.2
  rw [← ha, h3, map_one]

end GlobalTheory.MemLoc.FilPrincipal


open GlobalTheory.MemLoc.FilPrincipal in
theorem GlobalTheory.MemLoc.filtration_eq_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e →
    (∀ (n : ℕ) (y : Per.BdRp l), y ∈ Per.FilP l n ↔ aDp l (xi e) ^ n ∣ y) ∧
    (∀ y : Per.BdRp l, aDp l (xi e) * y = 0 → y = 0) ∧
    IsAdicComplete (Ideal.span {aDp l (xi e)}) (Per.BdRp l) ∧
    (∀ n : ℕ, Function.Surjective (Per.ev l n)) := by
  intro l _ e he
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  obtain ⟨-, hd, hinj⟩ := GlobalTheory.T.usage l
  have hne : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ≠ 0 := fun h =>
    xi_ne_zero e he (hinj (h.trans (map_zero _).symm))
  obtain ⟨E, hE, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have ha : E (aDp l (xi e)) = algebraMap (Per.AinfP l) (AdicCompletion (Per.kerP l) (Per.AinfP l))
      (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) := by
    rw [aDp, RingHom.comp_apply, hE]
  refine ⟨fun n y => ?_, fun y hy => ?_, ?_, fun n => GlobalTheory.RingIface.ev_surj l n⟩
  · rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← hev, evalₐ_eq_zero_iff hk n (E y), ← ha, ← map_pow]
    exact map_dvd_iff E
  · have h1 := congrArg E hy
    rw [map_mul, map_zero, ha] at h1
    exact E.injective ((regular_of_isDomain hk hne (E y) h1).trans (map_zero E).symm)
  · rw [← IsAdicComplete.congr_ringEquiv _ E, Ideal.map_span, Set.image_singleton, ha]
    exact isAdicComplete_span hk
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 → ∃ (t u : Per.Acris l), IsLogA e t ∧ IsUnit u ∧ t = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) * u := by
  first | exact @GlobalTheory.MemLoc.exists_isLogA | exact GlobalTheory.MemLoc.exists_isLogA | (intros; apply GlobalTheory.MemLoc.exists_isLogA <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ (l : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ IsAdicComplete (Ideal.span {(l : Per.Ainf l ⧸ Ideal.span {xi e ^ n})}) (Per.Ainf l ⧸ Ideal.span {xi e ^ n}) := by
  first | exact @GlobalTheory.MemLoc.XiSat.xi_sat | exact GlobalTheory.MemLoc.XiSat.xi_sat | (intros; apply GlobalTheory.MemLoc.XiSat.xi_sat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem IsTwist.mul_twist {S : Set ℕ} {ξ ξ' : HChar H.E} (h : IsTwist H S ξ) (h' : IsTwist H S ξ') :
    IsTwist H S (ξ * ξ') := by
  obtain ⟨⟨n, hn, ho⟩, ht, hl, hr⟩ := h
  obtain ⟨⟨n', hn', ho'⟩, ht', hl', hr'⟩ := h'
  refine ⟨⟨n * n', Nat.mul_pos hn hn', ?_⟩, ht.mul ht', fun v => HChar.LevelLe.mul (hl v) (hl' v), fun v hv => ?_⟩
  · unfold Formalism.L2.Host.HChar.OrderDvd at ho ho' ⊢
    rw [mul_pow, pow_mul, ho, one_pow, one_mul, mul_comm n n', pow_mul, ho', one_pow]
  · by_cases h1 : ξ.UnrAt v
    · exact hr' v fun h2 => hv (h1.mul h2)
    · exact hr v h1

theorem isTwist_of_isDelta {S : Set ℕ} {p : ℕ} {δ : HChar H.E} (hp : p.Prime) (hs : SplitsC H.E p) (hS : p ∉ S)
    (h : IsDelta (H := H) p δ) : IsTwist H S δ := by
  refine ⟨h.fin, h.triv, h.tame, fun v hv => ?_⟩
  have hv' : OverP H p v := by
    by_contra hn
    exact hv (h.unr v hn)
  obtain ⟨h1, h2, h3, -⟩ := splitsC_main R H p hp hs v hv'
  rw [h1]
  exact ⟨h3, hp, h2, hS⟩

end GlobalTheory.Mem.Chr
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.completelySplitPrime_host_place_properties : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → SplitsC H.E p → ∀ v : HeightOneSpectrum (𝓞 H.E), OverP H p v → Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ IsSplitPl H v ∧ ∀ (Q : HeightOneSpectrum (𝓞 H.K)), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal → ∀ v', ConjPl H.conj.toRingEquiv v v' → OverP H p v' ∧ (v.under (𝓞 H.K) = Q ↔ v'.under (𝓞 H.K) ≠ Q) := by
  first | exact @GlobalTheory.Mem.Chr.splitsC_main | exact GlobalTheory.Mem.Chr.splitsC_main | (intros; apply GlobalTheory.Mem.Chr.splitsC_main <;> assumption)
end

section

open CategoryTheory Polynomial

theorem _root_.GlobalTheory.T.finsum_centralIdempotentOfIrrCharacter_eq_simple : ∀ {G : Type} [Group G] [Fintype G] (Q : (G → ℂ) → Prop), ∑ᶠ χ ∈ {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}, GlobalTheory.GLq.zOf χ = ∑ᶠ (z : MonoidAlgebra ℂ G) (_ : ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character), z := by
  first | exact @GlobalTheory.SerCmp.finsum_zOf_eq_finsum_zIdem | exact GlobalTheory.SerCmp.finsum_zOf_eq_finsum_zIdem | (intros; apply GlobalTheory.SerCmp.finsum_zOf_eq_finsum_zIdem <;> assumption)
end

section

open CategoryTheory Polynomial

theorem _root_.GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0) := by
  first | exact @GlobalTheory.GLq.ConstIff.constituent_hcRep_iff | exact GlobalTheory.GLq.ConstIff.constituent_hcRep_iff | (intros; apply GlobalTheory.GLq.ConstIff.constituent_hcRep_iff <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField Matrix
open scoped InnerProductSpace ComplexOrder Classical

namespace GlobalTheory.Mem.RowsBundle

section Infl

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

theorem fibre_eq (q : Q) :
    ∃ t : I.Gf, {x | x ∈ I.Kset ∧ ρ.toFun x = q} = (fun y => t * y) ⁻¹' I.Kg g := by
  obtain ⟨t, ht, rfl⟩ := ρ.surj q
  have ht' : t⁻¹ ∈ I.Kset := (Ksub I).inv_mem ht
  refine ⟨t⁻¹, Set.ext fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine (ρ.ker _ ((Ksub I).mul_mem ht' h.1)).1 ?_
    rw [ρ.map_mul _ ht' _ h.1, ρ.map_inv ht, h.2, inv_mul_cancel]
  · have h1 : t⁻¹ * x ∈ I.Kset := h.1
    have hx : x ∈ I.Kset := ((Ksub I).mul_mem_cancel_left ht').1 h1
    have h2 := (ρ.ker _ h1).2 h
    rw [ρ.map_mul _ ht' _ hx, ρ.map_inv ht, inv_mul_eq_one] at h2
    exact ⟨hx, h2.symm⟩

theorem integral_inflate [Fintype Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (F : Q → ℂ) :
    Integrable (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) μf ∧
      ∫ x, (if x ∈ I.Kset then F (ρ.toFun x) else 0) ∂μf = ((μf (I.Kg g)).toReal : ℂ) * ∑ q, F q := by
  have hU : IsOpen (I.Kg g) := I.topf_open g hg
  have hfin : μf (I.Kg g) ≠ ⊤ :=
    ((measure_mono (show I.Kg g ⊆ I.Kset from fun x hx => hx.1)).trans_lt
      (GlobalTheory.adelicStab_isCompact_isOpen I).1.measure_lt_top).ne
  have hm : ∀ q, MeasurableSet {x | x ∈ I.Kset ∧ ρ.toFun x = q} ∧
      μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) := fun q => by
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨(hU.preimage (by fun_prop)).measurableSet, measure_preimage_mul μf t _⟩
  have e : (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) =
      fun x => ∑ q, {x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q) x := by
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [if_pos hx, Finset.sum_eq_single (ρ.toFun x)]
      · rw [Set.indicator_of_mem]
        exact ⟨hx, rfl⟩
      · exact fun q _ hq => Set.indicator_of_notMem (by exact fun h => hq h.2.symm) _
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [if_neg hx]
      exact (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (by exact fun h => hx h.1) _).symm
  have hi : ∀ q, Integrable ({x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q)) μf := fun q =>
    (integrable_indicator_iff (hm q).1).2 (integrableOn_const ((hm q).2 ▸ hfin))
  rw [e]
  refine ⟨integrable_finsetSum _ fun q _ => hi q, ?_⟩
  rw [integral_finsetSum _ fun q _ => hi q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hm q).1, Measure.real, (hm q).2, Complex.real_smul]

theorem integrable_lift [Finite Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a : MonoidAlgebra ℂ Q) :
    Integrable (ρ.lift μf a) μf := by
  letI := Fintype.ofFinite Q
  exact (integral_inflate ρ μf hg fun q => a.coeff q / ((μf (I.Kg g)).toReal : ℂ)).1

theorem lift_biinv (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (x : I.Gf) (k : I.Gf) (hk : k ∈ I.Kg g)
    (k' : I.Gf) (hk' : k' ∈ I.Kg g) : ρ.lift μf a (k * x * k') = ρ.lift μf a x := by
  by_cases hx : x ∈ I.Kset
  · have h1 : k * x ∈ I.Kset := (Ksub I).mul_mem hk.1 hx
    rw [ρ.lift_of_mem μf a hx, ρ.lift_of_mem μf a ((Ksub I).mul_mem h1 hk'.1), ρ.map_mul _ h1 _ hk'.1,
      ρ.map_mul _ hk.1 _ hx, (ρ.ker _ hk.1).2 hk, (ρ.ker _ hk'.1).2 hk', one_mul, mul_one]
  · rw [ρ.lift_of_notMem μf a hx, ρ.lift_of_notMem μf a fun h => hx
      (((Ksub I).mul_mem_cancel_left hk.1).1 (((Ksub I).mul_mem_cancel_right hk'.1).1 h))]

end Infl

section Tens

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

end Tens

end GlobalTheory.Mem.RowsBundle
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

theorem _root_.GlobalTheory.T.eq_of_proportional_to_generating_sections : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ ψ' : W ⟶ PSpace R m), GeneratesAlong ⊤ σ g → ψ ≫ PSpace.str R m = ψ' ≫ PSpace.str R m → Proportional σ g ψ → Proportional σ g ψ' → ψ = ψ' := by
  first | exact @GlobalTheory.ProjBlowup.eq_of_proportional | exact GlobalTheory.ProjBlowup.eq_of_proportional | (intros; apply GlobalTheory.ProjBlowup.eq_of_proportional <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

theorem _root_.GlobalTheory.T.effCartier_of_proportional_sections : ∀ (R : Type) [CommRing R] (X W T : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (d : T ⟶ W), GeneratesAlong I σ g → Proportional σ g ψ → IsSchemeTheoreticallyDominant d → QuasiCompact d → (∀ t : T, d t ∉ I.support) → FinalTheorems.EffCartier I := by
  first | exact @GlobalTheory.ProjBlowup.effCartier_of_proportional | exact GlobalTheory.ProjBlowup.effCartier_of_proportional | (intros; apply GlobalTheory.ProjBlowup.effCartier_of_proportional <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

namespace GlobalTheory.SatInd

section HeckeTransport

theorem hecke_comp_of_inverse {G G' : Type} [Group G] [Group G'] (φ : G →* G') (ψ : G' →* G)
    (hψφ : ∀ y, ψ (φ y) = y) {K : Subgroup G} {K' : Subgroup G'} (hφK : ∀ a ∈ K, φ a ∈ K')
    (hψK : ∀ a ∈ K', ψ a ∈ K) (h' : G' → ℂ) (hh : h' ∈ Formalism.UG.Hecke ℂ K') :
    (fun y => h' (φ y)) ∈ Formalism.UG.Hecke ℂ K := by
  classical
  have hh' : Formalism.UG.IsBiInv K' h' ∧ Formalism.UG.FinDosetSupp K' h' := hh
  obtain ⟨hbi, S', hS'⟩ := hh'
  show Formalism.UG.IsBiInv K (fun y => h' (φ y)) ∧ Formalism.UG.FinDosetSupp K (fun y => h' (φ y))
  refine ⟨fun a b y => ?_, S'.image ψ, fun y hy => ?_⟩
  · show h' (φ ((a : G) * y * b)) = h' (φ y)
    rw [map_mul, map_mul]
    exact hbi ⟨φ a, hφK a a.2⟩ ⟨φ b, hφK b b.2⟩ (φ y)
  · obtain ⟨s, hs, a, b, e⟩ := hS' (φ y) hy
    refine ⟨ψ s, Finset.mem_image_of_mem _ hs, ⟨ψ a, hψK a a.2⟩, ⟨ψ b, hψK b b.2⟩, ?_⟩
    show y = ψ a * ψ s * ψ b
    rw [← map_mul, ← map_mul, ← e, hψφ]

end HeckeTransport

section KUTransport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem guMap_mem_KU (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K → g x ∈ intL K) (n : ℕ) (a : GU σ n) (ha : a ∈ KU σ n) :
    guMap g hg n a ∈ KU σ' n := by
  simp only [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf, MonoidHom.mem_range] at ha ⊢
  obtain ⟨-, b, hb⟩ := ha
  refine ⟨(guMap g hg n a).2, ?_⟩
  let gi : intL K →+* intL K :=
    ((g : K →+* K).comp (intL K).subtype).codRestrict (intL K) (fun x => hint x x.2)
  refine ⟨bc (n := Fin n) gi b, ?_⟩
  apply Units.ext
  ext i j
  have hij := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K) i j) hb
  simp only [bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at hij ⊢
  rw [guMap_val, Matrix.map_apply, ← hij]
  rfl

theorem guMap_symm_guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hg' : ∀ x, g.symm (σ' x) = σ (g.symm x)) (n : ℕ) (y : GU σ n) :
    guMap g.symm hg' n (guMap g hg n y) = y := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [guMap_val, guMap_val]
  simp

theorem guMap_hecke_comap : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (n : ℕ) (h' : GU σ' n → ℂ), h' ∈ Hecke ℂ (KU σ' n) → (fun y => h' (guMap g hg n y)) ∈ Hecke ℂ (KU σ n) := by
  intro K _ _ g σ σ' hg hint n h' hh
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [RingEquiv.apply_symm_apply, hg, RingEquiv.apply_symm_apply]
  have hint' : ∀ x, x ∈ intL K → g.symm x ∈ intL K := by
    intro x hx
    rw [hint (g.symm x), RingEquiv.apply_symm_apply]
    exact hx
  exact hecke_comp_of_inverse (guMap g hg n) (guMap g.symm hg' n) (guMap_symm_guMap g hg hg' n)
    (fun a ha => guMap_mem_KU g hg (fun x => (hint x).1) n a ha)
    (fun a ha => guMap_mem_KU g.symm hg' hint' n a ha) h' hh

end KUTransport

end GlobalTheory.SatInd
end
end
