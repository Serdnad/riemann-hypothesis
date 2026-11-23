module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle172
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle283
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle308
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LFun.SplitChart

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

theorem continuous_complMap (h : w.under (𝓞 F) = v) : Continuous (complMap h) := by
  subst h
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp k :=
    ⟨_, (WithZero.exp_log h0).symm⟩
  filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := F) (w.under (𝓞 F)) (-((k.natAbs + 1 : ℕ) : ℤ))).mem_nhds
    (by simp)] with a ha
  rw [Valuation.restrict_lt_iff_lt_embedding, hk]
  exact (GlobalTheory.AdeleBaseChange.locMap_valued w _ a ha).trans_lt (WithZero.exp_lt_exp.2 (by omega))

theorem exists_splitPrime_eq (hc : IsCMExt F E σ) (hv : IsSplit (E := E) v) (h : w.under (𝓞 F) = v) :
    ∃ τ : E →ₐ[F] Fv F v, splitPrime τ = w := by
  obtain ⟨P, Q, hne, hP, hQ⟩ := hv
  by_cases e : w = P
  · exact (existsUnique_splitPrime_eq hc (e ▸ hne) h (HeightOneSpectrum.ext hQ)).exists
  · exact (existsUnique_splitPrime_eq hc e h (HeightOneSpectrum.ext hP)).exists

theorem exists_equiv_complMap (τ : E →ₐ[F] Fv F v) (h : (splitPrime τ).under (𝓞 F) = v) :
    ∃ ψ : Fv F v ≃+* (splitPrime τ).adicCompletion E, (∀ a, ψ a = complMap h a) ∧
      (∀ x : E, ψ (τ x) = algebraMap E _ x) ∧ (∀ a, Valued.v (ψ a) = Valued.v a) ∧ Continuous ψ ∧
      Continuous ψ.symm := by
  obtain ⟨φ, h1, h2, h3, h4⟩ := GlobalTheory.SplitCompletion.exists_ringEquiv_splitPrime τ
  have h5 : ∀ x : E, φ.symm (τ x) = algebraMap E _ x := fun x => by rw [← h1, φ.symm_apply_apply]
  refine ⟨φ.symm, congrFun ((HeightOneSpectrum.denseRange_algebraMap F v).equalizer h4 (continuous_complMap h)
    (funext fun a => ?_)), h5, fun a => by rw [← h2, φ.apply_symm_apply], h4, h3⟩
  exact ((congrArg φ.symm (τ.commutes a).symm).trans (h5 _)).trans (complMap_algebraMap h a).symm

section Transport

variable {τ : E →ₐ[F] Fv F v} {h : w.under (𝓞 F) = v} {ψ : Fv F v ≃+* w.adicCompletion E}

theorem toCompl_eq (h1 : ∀ a, ψ a = complMap h a) (h2 : ∀ x : E, ψ (τ x) = algebraMap E _ x)
    (y : Fv F v ⊗[F] E) : toCompl h y = ψ (splitProj τ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rw [toCompl_tmul, splitProj_tmul, map_mul, h1, h2]

omit [Algebra F E] in
theorem map_mem_Ov_iff (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) {a : Fv F v} :
    ψ a ∈ Ov E w ↔ a ∈ v.adicCompletionIntegers F := by
  change Valued.v (ψ a) ≤ 1 ↔ Valued.v a ≤ 1
  rw [h3]

theorem map_mem_latAt_iff (h2 : ∀ x : E, ψ (τ x) = algebraMap E _ x) (h3 : ∀ a, Valued.v (ψ a) = Valued.v a)
    {u : Fin n → Fv F v} : (fun i => ψ (u i)) ∈ latAt w L ↔ u ∈ splitLat τ L := by
  constructor
  · intro hu
    have key : ∀ y ∈ latAt w L, (fun i => ψ.symm (y i)) ∈ splitLat τ L := fun y hy => by
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        refine ⟨_, tmul_mem_latLoc (one_mem _) hz, funext fun i => ?_⟩
        change splitProj τ (1 ⊗ₜ[F] z i) = ψ.symm (algebraMap E _ (z i))
        rw [splitProj_tmul, one_mul, ← h2, ψ.symm_apply_apply]
      | zero => exact (funext fun _ => map_zero ψ.symm : (fun i => ψ.symm ((0 : Fin n → _) i)) = 0) ▸ zero_mem _
      | add a b _ _ ha hb =>
        have := add_mem ha hb
        convert this using 1
        exact funext fun i => map_add ψ.symm _ _
      | smul a b _ hb =>
        have := (splitLat τ L).smul_mem ⟨ψ.symm a, (map_mem_Ov_iff h3).1 (by rw [ψ.apply_symm_apply]; exact a.2)⟩ hb
        convert this using 1
        exact funext fun i => map_mul ψ.symm _ _
    simpa using key _ hu
  · rintro ⟨y, hy, rfl⟩
    refine latLoc_induction (p := fun y => (fun i => ψ (splitVec τ y i)) ∈ latAt w L) (fun a ha x hx => ?_) ?_
      (fun y z hy hz => ?_) (fun y hy => ?_) hy
    · have := (latAt w L).smul_mem ⟨ψ a, (map_mem_Ov_iff h3).2 ha⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
      convert this using 1
      funext i
      change ψ (a * τ (x i)) = ψ a * algebraMap E _ (x i)
      rw [map_mul, h2]
    · convert zero_mem (latAt w L) using 1
      funext i
      simp [splitVec]
    · convert add_mem hy hz using 1
      funext i
      simp [splitVec]
    · convert neg_mem hy using 1
      funext i
      simp [splitVec]

theorem isFrameAt_bc (h2 : ∀ x : E, ψ (τ x) = algebraMap E _ x) (h3 : ∀ a, Valued.v (ψ a) = Valued.v a)
    {β : GL (Fin n) (Fv F v)} (hβ : IsSplitBasis τ L β) : IsFrameAt w L (bc ψ.toRingHom β) := fun y => by
  obtain ⟨u, rfl⟩ : ∃ u : Fin n → Fv F v, y = fun i => ψ (u i) := ⟨fun i => ψ.symm (y i), by simp⟩
  have e : (bc ψ.toRingHom β).1 *ᵥ (fun i => ψ (u i)) = fun i => ψ ((β.1 *ᵥ u) i) :=
    funext fun i => (RingHom.map_mulVec ψ.toRingHom β.1 u i).symm
  simp only [e, map_mem_Ov_iff h3, map_mem_latAt_iff h2 h3]
  exact hβ u

omit [Algebra F E] in
theorem bc_mem_KGL_iff (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) {x : GL (Fin n) (Fv F v)} :
    bc ψ.toRingHom x ∈ KGL w (n := n) ↔ x ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring := by
  rw [mem_GLint_iff, mem_GLint_iff]
  exact and_congr (forall₂_congr fun _ _ => map_mem_Ov_iff h3) (forall₂_congr fun _ _ => map_mem_Ov_iff h3)

end Transport

theorem continuous_bc {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    {f : A →+* B} (hf : Continuous f) : Continuous (bc (n := Fin n) f) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map hf, Units.continuous_coe_inv.matrix_map hf⟩

theorem exists_isSplitChart (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : L.FG)
    (hL' : Submodule.span E (L : Set (Fin n → E)) = ⊤) (h : w.under (𝓞 F) = v) (hv : IsSplit (E := E) v)
    (hd : IsSelfDualAt σ J L v) : ∃ e, IsSplitChart σ J L h e ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨τ, rfl⟩ := exists_splitPrime_eq hc hv h
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := exists_equiv_complMap τ h
  letI : Submodule.IsFullLattice E L :=
    { toIsLattice := Submodule.IsLattice.of_fg E hL, span_eq_top := hL' }
  obtain ⟨β, hβ⟩ := exists_isSplitBasis τ L hc
  refine ⟨(splitEquivIn hc hJ τ β).toMulEquiv.trans (Units.mapEquiv ψ.mapMatrix.toMulEquiv),
    ⟨⟨_, isFrameAt_bc h2 h3 hβ, fun g => ?_⟩, fun g => ?_⟩,
    (continuous_bc (f := ψ.toRingHom) h4).comp (splitEquivIn hc hJ τ β).continuous,
    (splitEquivIn hc hJ τ β).symm.continuous.comp (continuous_bc (f := ψ.symm.toRingHom) h5)⟩
  · change bc ψ.toRingHom (β⁻¹ * splitHom σ J τ g * β) = _
    rw [map_mul, map_mul, map_inv]
    congr 2
    exact Units.ext (Matrix.ext fun i j => (toCompl_eq h1 h2 _).symm)
  · exact (mem_stabLoc_iff_GLint hc hJ hd hβ).trans (bc_mem_KGL_iff h3).symm

theorem absNorm_splitPrime (τ : E →ₐ[F] Fv F v) :
    Ideal.absNorm (splitPrime τ).asIdeal = Ideal.absNorm v.asIdeal := by
  have hle : v.asIdeal = (splitPrime τ).asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) :=
    (Ideal.ext (algebraMap_mem_splitPrime τ)).symm
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_eq_of_bijective (Ideal.quotientMap _ _ hle.le) ⟨Ideal.quotientMap_injective' hle.ge, fun y => ?_⟩).symm
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := ReciprocityTheory.Aut.adic_exists_approx v (τ x) (apply_coe_mem τ x)
  refine ⟨Ideal.Quotient.mk _ a, (Ideal.Quotient.eq.2 ((mem_splitPrime τ _).2 ?_)).symm⟩
  exact ((map_sub τ (x : E) (algebraMap F E a)).trans (congrArg _ (τ.commutes (a : F)))) ▸ ha

theorem exists_conj_place (hc : IsCMExt F E σ) (h : w.under (𝓞 F) = v) (hv : IsSplit (E := E) v) :
    ∃ w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ (∀ u, u.under (𝓞 F) = v ↔ u = w ∨ u = w') ∧
      Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal ∧
      w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (σ : E →+* E)) := by
  obtain ⟨τ, rfl⟩ := exists_splitPrime_eq hc hv h
  refine ⟨splitPrime (τ.comp σ), (splitPrime_comp_ne hc τ).symm, fun u => ⟨fun hu => ?_, ?_⟩, absNorm_splitPrime τ,
    absNorm_splitPrime _, Ideal.ext (mem_splitPrime_comp τ σ)⟩
  · obtain ⟨ρ, rfl⟩ := exists_splitPrime_eq hc hv hu
    exact (eq_or_eq_comp_conj hc τ ρ).imp (congrArg _) (congrArg _)
  · rintro (rfl | rfl) <;> exact splitPrime_under _

theorem split_chart_and_places (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : L.FG)
    (hL' : Submodule.span E (L : Set (Fin n → E)) = ⊤) (h : w.under (𝓞 F) = v) (hv : IsSplit (E := E) v)
    (hd : IsSelfDualAt σ J L v) :
    (∃ e, IsSplitChart σ J L h e ∧ Continuous e ∧ Continuous e.symm) ∧
      ∃ w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ (∀ u, u.under (𝓞 F) = v ↔ u = w ∨ u = w') ∧
        Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal ∧
        w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (σ : E →+* E)) :=
  ⟨exists_isSplitChart hc hJ hL hL' h hv hd, exists_conj_place hc h hv⟩

theorem isSplit_of_algHom (hc : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : IsSplit (E := E) v :=
  ⟨splitPrime (τ.comp σ), splitPrime τ, splitPrime_comp_ne hc τ, Ideal.ext (algebraMap_mem_splitPrime _),
    Ideal.ext (algebraMap_mem_splitPrime _)⟩

end GlobalTheory.LFun.SplitChart

end
end

section

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GlobalTheory.CMPrimeIdele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace EulerTie


variable (F E) in
def finComp : AE F E →+* FiniteAdeleRing (𝓞 E) E := (toFinAd F E).comp (finPart F E)

omit [NumberField E] in
theorem parts_extZero (y : Af F ⊗[F] E) :
    infPart F E (extZero F E y) = 0 ∧ finPart F E (extZero F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, and_self]
  | tmul a x => exact ⟨TensorProduct.zero_tmul _ _, rfl⟩
  | add a b ha hb => simp only [map_add (f := _), ha.1, ha.2, hb.1, hb.2, add_zero, and_self]

theorem comp_finComp : Comp (finComp F E) := by
  let c := (Algebra.TensorProduct.comm F E (Af F)).toRingEquiv
  have hι : ∀ x a, ((toFinAd F E).comp c.toRingHom) (x ⊗ₜ[F] a) =
      algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F E a := fun x a => (toFinAd_tmul a x).trans (mul_comm _ _)
  have hs : ∀ y, ((toFinAd F E).comp c.toRingHom) (swapAf F E y) = toFinAd F E y := fun y =>
    congrArg (toFinAd F E) ((Algebra.TensorProduct.comm F (Af F) E).symm_apply_apply y)
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨fun z h1 h2 => ?_, fun s => ?_, fun x => ?_, fun z => ?_, fun a Q => ?_⟩
  · have h3 : finPart F E z = 0 := toFinAd_bijective.1 (h2.trans (map_zero _).symm)
    apply e.injective
    rw [map_zero]
    exact Prod.ext ((he z).1.trans h1) ((he z).2.trans h3)
  · obtain ⟨y, rfl⟩ := (toFinAd_bijective (F := F)).2 s
    exact ⟨_, (parts_extZero y).1, congrArg (toFinAd F E) (parts_extZero y).2⟩
  · change toFinAd F E ((1 : Af F) ⊗ₜ[F] x) = _
    rw [toFinAd_tmul, map_one, one_mul]
  · rw [mem_intAE_iff]
    refine ⟨fun h => ?_, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_⟩
    · have := GlobalTheory.AdeleBaseChange.map_mem_int hι h
      rw [hs] at this
      exact this
    · rw [hs]; exact h
  · change toFinAd F E (a.2 ⊗ₜ[F] (1 : E)) Q = _
    rw [toFinAd_tmul, map_one, mul_one]
    rfl

theorem parts_locIdele (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    infPart F E (locIdele F P u : AE F E) = 1 ∧
      finComp F E (locIdele F P u : AE F E) = (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 E) E) := by
  have e : (locIdele F P u : AE F E) = 1 - extZero F E 1 +
      extZero F E ((finAdEquiv F E).symm (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 E) E)) := rfl
  rw [e]
  constructor
  · rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, (parts_extZero _).1, (parts_extZero _).1, sub_zero, add_zero]
  · change toFinAd F E (finPart F E _) = _
    rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, (parts_extZero _).2, (parts_extZero _).2, sub_self, zero_add]
    exact (finAdEquiv F E).apply_symm_apply _

theorem comp_glue {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (he : IsDelta (finComp F E) P e) (a : AE F E) :
    infPart F E (e * a + (1 - e)) = 1 ∧ finComp F E (e * a + (1 - e)) P = finComp F E a P ∧
      ∀ Q, Q ≠ P → finComp F E (e * a + (1 - e)) Q = 1 := by
  have h : ∀ Q, finComp F E (e * a + (1 - e)) Q = finComp F E e Q * finComp F E a Q + (1 - finComp F E e Q) :=
    fun Q => by rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one]; rfl
  refine ⟨?_, ?_, fun Q hQ => ?_⟩
  · rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, he.1, zero_mul, sub_zero, zero_add]
  · rw [h, he.2.1, one_mul, sub_self, add_zero]
  · rw [h, he.2.2 Q hQ, zero_mul, sub_zero, zero_add]

theorem finComp_locIdele_self (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    finComp F E (locIdele F P u : AE F E) P = u := by
  rw [(parts_locIdele P u).2, GlobalTheory.CMVal.single_self]

theorem finComp_locIdele_ne {P Q : HeightOneSpectrum (𝓞 E)} (h : Q ≠ P) (u : (P.adicCompletion E)ˣ) :
    finComp F E (locIdele F P u : AE F E) Q = 1 := by
  classical
  rw [(parts_locIdele P u).2, GlobalTheory.CMVal.single_apply]
  exact Function.update_of_ne h _ _

theorem glue_eq_locIdele {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (he : IsDelta (finComp F E) P e) {a : AE F E}
    {u : (P.adicCompletion E)ˣ} (h : finComp F E a P = u) : e * a + (1 - e) = (locIdele F P u : AE F E) := by
  obtain ⟨h1, h2, h3⟩ := comp_glue he a
  refine comp_finComp.ext' (h1.trans (parts_locIdele P u).1.symm) fun Q => ?_
  by_cases hQ : Q = P
  · subst hQ; rw [h2, h, finComp_locIdele_self]
  · rw [h3 Q hQ, finComp_locIdele_ne hQ]

theorem locIdele_int_iff (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    finPart F E (locIdele F P u : AE F E) ∈ intAE F E ↔ Valued.v (u : P.adicCompletion E) ≤ 1 := by
  rw [comp_finComp.2.2.2.1]
  refine ⟨fun h => ?_, fun h Q => ?_⟩
  · have := h P
    rwa [finComp_locIdele_self] at this
  · by_cases hQ : Q = P
    · subst hQ; rw [finComp_locIdele_self]; exact h
    · rw [finComp_locIdele_ne hQ]; exact one_mem _

theorem isUnitAt_iff (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    Formalism.L2.Host.IsUnitAt P u ↔ Valued.v (u : P.adicCompletion E) ≤ 1 ∧
      Valued.v ((u⁻¹ : (P.adicCompletion E)ˣ) : P.adicCompletion E) ≤ 1 := by
  have h0 : 0 < Valued.v (u : P.adicCompletion E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 u.ne_zero)
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ h0]
  exact le_antisymm_iff

variable {σ : E →ₐ[F] E}

theorem isDelta_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E} (h : IsPrimeIdem σ P e f) :
    IsDelta (finComp F E) P e := by
  rcases h with ⟨⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩, -⟩ | ⟨-, ⟨v, ε, hε, h3⟩, ht⟩
  · refine (tie_iff comp_finComp h1 ?_ P).1 ht
    have : e = e * algebraMap (AF F) (AE F E) ε := by rw [← h3, mul_add, h1, h2, add_zero]
    rw [this, RingHom.map_mul, (place_comp (comp_finComp (E := E)) hε).1, mul_zero]
  · obtain ⟨k0, k1, k2⟩ := place_comp (comp_finComp (E := E)) hε
    rw [← h3] at k0 k1 k2
    refine (tie_iff comp_finComp (comp_finComp.ext' (by rw [RingHom.map_mul, k0, mul_zero]) fun Q => ?_) k0 P).1 ht
    rw [ev_mul]
    by_cases hQ : Q.under (𝓞 F) = v
    · rw [k1 Q hQ, mul_one]
    · rw [k2 Q hQ, mul_zero]

theorem valuation_of_mem_notMem_sq (P : HeightOneSpectrum (𝓞 E)) {a : 𝓞 E} (h1 : a ∈ P.asIdeal)
    (h2 : a ∉ P.asIdeal ^ 2) : P.valuation E (a : E) = WithZero.exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have k1 : P.intValuation a ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; simpa using h1
  have k2 : ¬ P.intValuation a ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact h2
  have h0 : P.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero P a ha
  refine (HeightOneSpectrum.valuation_of_algebraMap P a).trans ?_
  rw [← WithZero.exp_log h0] at k1 k2 ⊢
  rw [WithZero.exp_le_exp] at k1 k2
  congr 1
  omega

theorem exists_of_isUnifIdele {P : HeightOneSpectrum (𝓞 E)} {x : (AE F E)ˣ} (h : IsUnifIdele σ P x) :
    ∃ u, Formalism.L2.Host.IsUnifAt P u ∧ x = locIdele F P u := by
  obtain ⟨e, f, ϖ, he, h1, h2, hx⟩ := h
  have hv : Valued.v (algebraMap E (P.adicCompletion E) (ϖ : E)) = WithZero.exp (-1 : ℤ) :=
    (Formalism.UG.P.levelaf_valued_algebraMap _ _).trans (valuation_of_mem_notMem_sq P h1 h2)
  have h0 : algebraMap E (P.adicCompletion E) (ϖ : E) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  refine ⟨Units.mk0 _ h0, hv, Units.ext (hx.trans (glue_eq_locIdele (isDelta_of_isPrimeIdem he) ?_))⟩
  rw [comp_finComp.2.2.1]
  rfl

end EulerTie

open EulerTie

variable {σ : E →ₐ[F] E}

theorem isUnramAt_iff_unrAt (hσ : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) :
    IsUnramAt σ χ P ↔ UnrAt χ P := by
  constructor
  · rintro ⟨e, f, he, h⟩ u hu
    obtain ⟨h1, h2⟩ := (isUnitAt_iff P u).1 hu
    have := h (locIdele F P u) (glue_eq_locIdele (isDelta_of_isPrimeIdem he) (finComp_locIdele_self P u)).symm
      ((locIdele_int_iff P u).2 h1) (by rw [← map_inv]; exact (locIdele_int_iff P u⁻¹).2 h2)
    exact (congrArg Circle.toUnits this).trans (map_one _)
  · intro h
    obtain ⟨e, f, -, he⟩ := exists_isPrimeIdem hσ P
    refine ⟨e, f, he, fun x hx h1 h2 => ?_⟩
    let π : AE F E →+* P.adicCompletion E := (evalV E P).toRingHom.comp (finComp F E)
    obtain ⟨u, rfl⟩ : ∃ u, x = locIdele F P u :=
      ⟨Units.map π.toMonoidHom x, Units.ext (hx.trans (glue_eq_locIdele (isDelta_of_isPrimeIdem he) rfl))⟩
    rw [← map_inv] at h2
    have := h u ((isUnitAt_iff P u).2 ⟨(locIdele_int_iff P u).1 h1, (locIdele_int_iff P u⁻¹).1 h2⟩)
    exact Circle.ext (congrArg Units.val this)

theorem chiAt_eq_val (hσ : IsCMExt F E σ) {χ : (AE F E)ˣ →* Circle} {P : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ P) :
    chiAt σ χ P = (val χ P : ℂ) := by
  have hc : IsUnramAt σ χ P ∧ ∃ x, IsUnifIdele σ P x := ⟨(isUnramAt_iff_unrAt hσ χ P).2 h, exists_isUnifIdele hσ P⟩
  obtain ⟨u, hu, e⟩ := exists_of_isUnifIdele hc.2.choose_spec
  rw [chiAt, dite_eq_left hc, e, ← h.locChar_eq_val hu]
  rfl

theorem chiAt_eq_zero (hσ : IsCMExt F E σ) {χ : (AE F E)ˣ →* Circle} {P : HeightOneSpectrum (𝓞 E)}
    (h : ¬ UnrAt χ P) : chiAt σ χ P = 0 :=
  dif_neg fun hc => h ((isUnramAt_iff_unrAt hσ χ P).1 hc.1)

theorem lfac_eq_locL (hσ : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    lfac σ χ P s = locL (charFam χ) P s := by
  unfold lfac locL charFam
  split_ifs with h
  · rw [chiAt_eq_val hσ h, eulerFac_singleton]; rfl
  · rw [chiAt_eq_zero hσ h, eulerFac_zero, zero_mul, sub_zero, inv_one]

end GlobalTheory.LFun

end
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiEx

theorem kum_sum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    {ι : Type} (s : Finset ι) (r : ι → ℤ_[l]) (x : ι → X.Khat l) (χ : ι → SL(2, ℤ) → ZMod (l ^ n))
    (h : ∀ i, H3.Kum X l n (x i) (χ i)) :
    H3.Kum X l n (∑ i ∈ s, r i • x i) (fun δ => ∑ i ∈ s, PadicInt.toZModPow n (r i) * χ i δ) := by
  classical
  obtain ⟨hadd, hzero, -⟩ := GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact hzero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hadd _ _ _ _ (GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n (r a) (x a) (χ a) (h a)) ih

theorem exists_betti_cocycle {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (_hε : Function.Injective ε) (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero))
    (N l w : ℕ) [Fact l.Prime] (hl : l ≠ 2) (hN : 5 ≤ N) (hc : Nat.Coprime N l) (hw : Odd w) :
    ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := by
  rintro b ⟨⟨c, hcA, hb⟩, hinv⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hJ : H3.JHol X := by
    obtain ⟨φ, h1, h2⟩ := hj
    exact ⟨φ, h2, h1⟩
  have hlN : ¬ l ∣ N := (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hc.symm
  obtain ⟨Φ, hΦ, hK⟩ := GlobalTheory.T.kummerCharacters_invariant_compatible_family Ω ε X l hJ N w c hcA
    (fun γ hγ => GlobalTheory.T.binaryForm_coeff_of_gamma1CapGamma0_invariant Ω ε X l N w b c hb γ hγ (hinv γ hγ))
  obtain ⟨z, hz, hnear⟩ := GlobalTheory.T.exists_padic_cocycle_of_compatible_poly_family N l w (by omega) hl hlN hw Φ hΦ
  refine ⟨fun δ => z δ, ⟨fun γ => hz.1 γ γ.2, fun γ δ => hz.2 γ γ.2 δ δ.2⟩, fun n u => ?_⟩
  obtain ⟨M, hM, hMn⟩ := hnear n
  have hk := kum_sum X l n Finset.univ (fun i : Fin (w + 1) => u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) c _ (hK n)
  rw [← hb u] at hk
  refine ⟨_, hk, M, hM, fun δ hδ => ?_⟩
  obtain ⟨-, hexp, -, hev, -⟩ := GlobalTheory.KZ.H3.mon_expand (ZMod (l ^ n)) w
  have e := hMn δ hδ
  simp only at e ⊢
  rw [e]
  conv_lhs => rw [hexp (Φ n δ) (hΦ.1 n δ)]

  simp only [map_sum, map_mul, map_pow, MvPolynomial.eval_C, hev]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.KZ.BettiEx
end
end
