module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Formalism.LocalRingCardinality.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle054
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInternalStableDecompositionDescendsToSubfi
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle050

public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
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
import Mathlib.RingTheory.KrullDimension.PID
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline

@[expose] public section

section

namespace GlobalTheory.LocalInv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem weightRegular_definite : ∀ (D : D7), GlobalTheory.LocalInv.WeightRegular D.nd D.naut :=
  fun D => weightRegular_of_ext D.nd D.naut D.nbc

end GlobalTheory.LocalInv
end

section

open Formalism.BasicNotions NumberField

namespace GlobalTheory

theorem exists_prime_ge_dvd_absNorm {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] {p : ℕ} (hp : p.Prime) (I : Ideal S) (hI : I ≠ ⊥)
    (h : p ∣ Ideal.absNorm I) :
    ∃ P : Ideal S, P.IsPrime ∧ I ≤ P ∧ p ∣ Ideal.absNorm P := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ J hJ =>
    rw [Ideal.isUnit_iff.1 hJ, Ideal.absNorm_top] at h
    exact absurd (Nat.dvd_one.1 h) hp.one_lt.ne'
  | h₃ J P hJ hP ih =>
    rw [map_mul] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact ⟨P, Ideal.isPrime_of_prime hP, Ideal.mul_le_left, h⟩
    · obtain ⟨Q, hQ, hle, hd⟩ := ih hJ h
      exact ⟨Q, hQ, Ideal.mul_le_right.trans hle, hd⟩

theorem coprime_absNorm_ccK_of_gIdx :
    ∀ (D : D7) (T p : ℕ), GIdx D.host T p → Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  intro D T p h
  obtain ⟨hp, -, hc, -⟩ := h
  have hj : jacobiSym (-(D.host.d : ℤ)) p ≠ 1 :=
    ((primeClass_eq_inert_iff _).1 hc).2.2.2.1
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  obtain ⟨P, hP, hle, hdP⟩ := exists_prime_ge_dvd_absNorm hp _ D.host.ccK_ne_bot hd
  obtain ⟨h1, h2⟩ := D.host.ccK_split P hP hle
  rw [← (Nat.prime_dvd_prime_iff_eq hp h1).1 hdP] at h2
  exact hj h2

end GlobalTheory
end

section

open Formalism.BasicNotions IsDedekindDomain NumberField

noncomputable section
namespace GlobalTheory.InertOfConj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unram (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv
        (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

end GlobalTheory.InertOfConj
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Col

noncomputable section
namespace GlobalTheory.GprimUnder

theorem conjO_conjO (X : Fields) (a : 𝓞 X.E) : X.conjO (X.conjO a) = a := by
  apply RingOfIntegers.ext
  show star (star (a : X.E)) = (a : X.E)
  exact star_star _

theorem conjO_algebraMap (X : Fields) (hX : X.Ok) (x : 𝓞 X.F) :
    X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) x) = algebraMap (𝓞 X.F) (𝓞 X.E) x := by
  apply RingOfIntegers.ext
  show star ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E)
  have : ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = algebraMap X.F X.E (x : X.F) := rfl
  rw [this]
  exact hX.star_F _

theorem mem_divs_iff {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} (ha : a ≠ 0) (P : HeightOneSpectrum A) :
    P ∈ divs a ↔ a ∈ P.asIdeal := by
  have hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite := by
    have h0 : Ideal.span {a} ≠ ⊥ := by simpa using ha
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  unfold divs
  rw [dite_eq_left hfin, Set.Finite.mem_toFinset]
  rfl

def conjPrime (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := P.asIdeal.comap X.conjO
  isPrime := Ideal.comap_isPrime X.conjO P.asIdeal
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have h1 : X.conjO x ∈ P.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, conjO_conjO]
      exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0
    rw [← conjO_conjO X x, h1, map_zero]

theorem mem_conjPrime (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) (a : 𝓞 X.E) :
    a ∈ (conjPrime X P).asIdeal ↔ X.conjO a ∈ P.asIdeal := Ideal.mem_comap

theorem under_conjPrime (X : Fields) (hX : X.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime X P).under (𝓞 X.F) = P.under (𝓞 X.F) := by
  apply HeightOneSpectrum.ext
  ext x
  show algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ (conjPrime X P).asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.asIdeal
  rw [mem_conjPrime, conjO_algebraMap X hX]

theorem exists_vG_under : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)),
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ P' ∈ Pr.vG i, P'.under (𝓞 X.F) = P.under (𝓞 X.F) := by
  intro X Pr hX hPr i P hP
  have hg0 : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero
  have hc0 : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have h1 := hPr.piG_norm i
    rw [h, mul_zero] at h1
    exact hg0 h1.symm
  have hvG : ∀ v, v ∈ Pr.vG i ↔ X.conjO (Pr.piG i) ∈ v.asIdeal := fun v => mem_divs_iff hc0 v
  rw [← hPr.piG_norm i] at hP
  rcases P.isPrime.mem_or_mem hP with h | h
  · refine ⟨conjPrime X P, (hvG _).2 ?_, under_conjPrime X hX P⟩
    rw [mem_conjPrime, conjO_conjO]
    exact h
  · exact ⟨P, (hvG P).2 h, rfl⟩

end GlobalTheory.GprimUnder
end
end

section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.unitary_mem_integralUnitary_doubleCoset_of_GLn_doubleCoset : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (σ : v.adicCompletion K →+* v.adicCompletion K) (n : ℕ), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) → ∀ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)), ∀ g' ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)), ∀ h ∈ GLint (Fin n) (Ov K v), ∀ k ∈ GLint (Fin n) (Ov K v), g' = h * g * k → ∃ k₁ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v), ∃ k₂ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v), g' = k₁ * g * k₂ := by
  first | exact @GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL | exact GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL | (intros; apply GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.LocalFrobeniusOrbit

theorem norm_algHom_eq {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

theorem exists_aut_comp {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} [Fact l.Prime]
    (c ρ : E →+* PadicAlgCl l) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ρ x = c (g x) := by
  let Φ : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] PadicAlgCl l) := fun g => c.toRatAlgHom.comp g.toAlgHom
  have hinj : Function.Injective Φ := by
    intro g h hgh
    ext x
    have := congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hgh
    exact c.injective this
  have hcard : Nat.card (E →ₐ[ℚ] PadicAlgCl l) ≤ Nat.card (E ≃ₐ[ℚ] E) := by
    rw [Nat.card_eq_fintype_card, AlgHom.card, IsGalois.card_aut_eq_finrank]
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨g, hg⟩ := hbij.2 ρ.toRatAlgHom
  exact ⟨g, fun x => (congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hg).symm⟩

theorem embeddings_orbit : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (K : Loc.FinExt l) (hc : ∀ x, c x ∈ K.1), (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] (s : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ s P → Module.finrank ℚ_[l] ↥K.1 = orderOf (H.galE s) ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l, ∃! i : ZMod (orderOf (H.galE s)), ∀ x : H.E, τ ⟨c x, hc x⟩ = c ((s ^ i.val) x) := by
  intro R H l _ h2 hq hd c K hc hcl P _ _ s hs
  haveI hG : IsGalois ℚ H.E := H.hostE_isGalois
  have hN0 : ¬ l ∣ H.condN := by
    rw [H.dvd_condN_iff_small Fact.out]; tauto
  have hF := H.der.frob l hN0
  have hco : Nat.Coprime l H.condN := (Fact.out : l.Prime).coprime_iff_not_dvd.2 hN0
  obtain ⟨v, hvl, hv⟩ := GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding l H.E c
  have hp : l.Prime := Fact.out
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI := v.isPrime
  haveI hvo : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hvl)
  have hsv : IsArithFrobAt ℤ s v.asIdeal := (H.frob_iff l hco v.asIdeal s).2 ((H.frob_iff l hco P s).1 hs)
  have hstab : MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) v.asIdeal = Subgroup.zpowers s := by
    refine le_antisymm (fun σ hσ => ?_) (Subgroup.zpowers_le.2 hsv.mem_stabilizer)
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul l v.asIdeal s σ hsv hσ
    rw [((hF v.asIdeal).2.2.2 ρ).1 hρ, one_mul]
    exact Subgroup.npow_mem_zpowers s k
  have hord : orderOf s = orderOf (H.galE s) :=
    (H.gal.orderOf_eq s).symm
  set N := orderOf (H.galE s) with hN
  have hNpos : 0 < N := hord ▸ orderOf_pos s
  haveI : NeZero N := ⟨hNpos.ne'⟩
  refine ⟨?_, ?_⟩
  · have hK : K.1 = IntermediateField.adjoin ℚ_[l] (Set.range c) := GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' l H.E c K.1 hc K.2 hcl
    have hdeg := GlobalTheory.T.finrank_local_field_eq_card_decomposition_group l H.E c v hv
    rw [← hord, ← Nat.card_zpowers, ← hstab, ← hdeg, hK]
  · intro τ
    let ρ : H.E →+* PadicAlgCl l := (τ : ↥K.1 →+* PadicAlgCl l).comp (c.codRestrict K.1 hc)
    obtain ⟨g, hg⟩ := exists_aut_comp c ρ
    have hρx : ∀ x, ρ x = τ ⟨c x, hc x⟩ := fun x => rfl
    have hgs : g ∈ Subgroup.zpowers s := by
      rw [← hstab]
      refine Formalism.FrobeniusOrbits.Decomp.mem_stab_of g v.asIdeal (fun z => ?_)
      rw [hv, hv]
      have h1 : c ((g • z : 𝓞 H.E) : H.E) = τ ⟨c z, hc z⟩ := by
        rw [← hρx, hg]; rfl
      rw [h1, norm_algHom_eq]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgs
    have hpow : ∀ j : ZMod N, s ^ j.val = s ^ ((j.val : ℤ)) := fun j => (zpow_natCast s j.val).symm
    refine ⟨(k : ZMod N), fun x => ?_, fun j hj => ?_⟩
    · rw [← hρx, hg, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]
    · have hgj : g = s ^ j.val := by
        refine AlgEquiv.ext fun x => c.injective ?_
        rw [← hg, hρx, hj]
      apply ZMod.val_injective
      have h3 : s ^ j.val = s ^ (k : ZMod N).val := by
        rw [← hgj, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]
      have h4 := pow_inj_mod.1 h3
      rw [hord, Nat.mod_eq_of_lt (ZMod.val_lt j), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h4
      exact h4

end GlobalTheory.LocalFrobeniusOrbit
end

section

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

theorem _root_.GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Us : Fin n → Submodule L (Fin a → L)), DirectSum.IsInternal Us → (∀ m, IsIrrSub τ (Us m)) → ∀ W, IsIrrSub τ W → ∃ m, IsoSub τ W (Us m) := by
  first | exact @GlobalTheory.SplitField.isoSub_summand_of_isInternal | exact GlobalTheory.SplitField.isoSub_summand_of_isInternal | (intros; apply GlobalTheory.SplitField.isoSub_summand_of_isInternal <;> assumption)
end

section

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

theorem _root_.GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield : ∀ {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Vs : Fin n → Submodule E (Fin a → E)), DirectSum.IsInternal Vs → (∀ m, IsInv (mapRep f τ) (Vs m)) → (∀ m, Vs m ≤ Submodule.span E ((fun v => f ∘ v) '' {v : Fin a → L | f ∘ v ∈ Vs m})) → ∃ Us : Fin n → Submodule L (Fin a → L), DirectSum.IsInternal Us ∧ ∀ m, IsInv τ (Us m) ∧ Submodule.span E ((fun v => f ∘ v) '' (Us m : Set (Fin a → L))) = Vs m := by
  first | exact @GlobalTheory.SplitField.descend_decomp | exact GlobalTheory.SplitField.descend_decomp | (intros; apply GlobalTheory.SplitField.descend_decomp <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits
open TensorProduct

namespace GlobalTheory.SubSumJumps

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem map_mem_FilV (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x
      ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f LinearMap.id y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem map_mem_DdRE (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] BdR)
    (hx : x ∈ DdRE PD ρ τ) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ DdRE PD ρ' τ := by
  have h1 : ∀ (g : G) (y : V ⊗[Qp] BdR),
      actVdR PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y)
        = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (actVdR PD ρ g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVdR, hf]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have h2 : ∀ (c : K) (y : V ⊗[Qp] BdR),
      mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL) c
        (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y)
        = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)
          (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c y) := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVdR]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  simp only [DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at hx ⊢
  refine ⟨fun g => ?_, fun c => ?_⟩
  · rw [h1, hx.1 g]
  · rw [h2, hx.2 c, map_smul]

theorem FilV_anti (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

end

theorem jumpsInV_of_isSubOfSums : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (τ : K →ₐ[Qp] LL) (J : Set ℤ), IsSubOfSums ρ (fun x g => Ms x g) → (∀ x, JumpsInV PD (matRep (Ms x)) τ J) → JumpsInV PD ρ τ J := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ ι k Ms τ J
    hsub hJ a ha
  by_contra haJ
  apply ha
  obtain ⟨m, xs, j, hj, hje⟩ := hsub
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hj)
  have hrv : ∀ v, r (j v) = v := fun v => LinearMap.congr_fun hr v
  apply le_antisymm
  · exact inf_le_inf_left _ (FilV_anti PD a)
  intro x hx
  refine ⟨hx.1, ?_⟩
  let p : Fin m → (V →ₗ[LL] (Fin k → LL)) := fun b => (LinearMap.proj b).comp j
  let s : Fin m → ((Fin k → LL) →ₗ[LL] V) := fun b =>
    r.comp (LinearMap.single LL (fun _ : Fin m => Fin k → LL) b)
  have hdec : ∀ y : V ⊗[Qp] BdR, y = ∑ b, AlgebraTensorModule.map (s b)
      (LinearMap.id : BdR →ₗ[Qp] BdR)
      (AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, ← TensorProduct.sum_tmul]
      congr 1

      simp only [s, p, LinearMap.comp_apply, ← map_sum]
      conv_lhs => rw [← hrv v]
      congr 1
      exact (Finset.univ_sum_single (j v)).symm
    | add y z hy hz =>
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [← hy, ← hz]
  rw [hdec x]
  refine Submodule.sum_mem _ fun b _ => map_mem_FilV PD (s b) (a + 1) _ ?_
  have heq : FildR PD (matRep (Ms (xs b))) τ (a + 1) = FildR PD (matRep (Ms (xs b))) τ a := by
    by_contra h
    exact haJ (hJ (xs b) a h)
  have hm : AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) x
      ∈ FildR PD (matRep (Ms (xs b))) τ a := by
    refine ⟨map_mem_DdRE PD ρ _ (p b) (fun g v => ?_) τ x hx.1, map_mem_FilV PD (p b) a x hx.2⟩
    simp [p, hje, matRep, Matrix.toLinAlgEquiv'_apply]
  rw [← heq] at hm
  exact hm.2

end GlobalTheory.SubSumJumps
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.card_decomposition_group_eq_local_degree : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (v w : HeightOneSpectrum (𝓞 E)), v ∈ placesOver E l → w ∈ placesOver E l → Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) = locDeg E w := by
  first | exact @GlobalTheory.DecompCard.card_stabilizer_eq_locDeg | exact GlobalTheory.DecompCard.card_stabilizer_eq_locDeg | (intros; apply GlobalTheory.DecompCard.card_stabilizer_eq_locDeg <;> assumption)
end
