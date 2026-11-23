module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
public import Formalism.LocalRingCardinality.DataForced
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle130
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle101
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.GaussJetBounds.Bundle001
public import Formalism.GaussJetBounds.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.IsPairFrame
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementG
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitUnif

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (φ : E →+* v.adicCompletion F)


omit [NumberField E] [Algebra F E] in
theorem map_mem (x : 𝓞 E) : φ x ∈ v.adicCompletionIntegers F := by
  have h2 : IsIntegral (v.adicCompletionIntegers F) (φ x) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) φ (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.adicCompletionIntegers F)
    (K := v.adicCompletion F)).1 h2
  rw [← hy]
  exact y.2

theorem lt_one_iff (x : WithZero (Multiplicative ℤ)) : x < 1 ↔ x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem mem_max (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (x : v.adicCompletion F) < 1 :=
  Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))

theorem irreducible_of_valued (p : v.adicCompletionIntegers F)
    (hp : Valued.v (p : v.adicCompletion F) = WithZero.exp (-1)) : Irreducible p := by
  have hp0 : (p : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext x
  rw [mem_max, lt_one_iff, Ideal.mem_span_singleton', ← hp]
  constructor
  · intro h
    refine ⟨⟨(x : v.adicCompletion F) / p, ?_⟩, Subtype.ext (div_mul_cancel₀ _ hp0)⟩
    show Valued.v ((x : v.adicCompletion F) / p) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ h zero_le
  · rintro ⟨a, rfl⟩
    show Valued.v ((a : v.adicCompletion F) * p) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' a.2

variable (P : HeightOneSpectrum (𝓞 E))
  (hφ : ∀ t : F, φ (algebraMap F E t) = algebraMap F (v.adicCompletion F) t)
  (hP : ∀ x : 𝓞 E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1)

include hφ hP in
theorem valued_unif (ϖ : 𝓞 E) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    Valued.v (φ ϖ) = WithZero.exp (-1) := by
  refine le_antisymm ((lt_one_iff _).1 ((hP ϖ).1 h1)) ?_
  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  let s : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) t
  have hs : Valued.v (φ s) = WithZero.exp (-1) := by
    have e1 : (s : E) = algebraMap F E (algebraMap (𝓞 F) F t) := rfl
    have e2 : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F t)) =
        v.valuation F (algebraMap (𝓞 F) F t) := v.valuedAdicCompletion_eq_valuation' _
    rw [e1, hφ, e2, HeightOneSpectrum.valuation_of_algebraMap, ht]
  have hsP : s ∈ P.asIdeal := by rw [hP, lt_one_iff, hs]
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h
    apply h2
    rw [show ϖ = 0 from Subtype.ext h]
    exact zero_mem _
  have hle : P.intValuation s ≤ P.intValuation ϖ := by
    have a1 := (P.intValuation_le_pow_iff_mem s 1).2 (by simpa using hsP)
    have a2 := mt (P.intValuation_le_pow_iff_mem ϖ 2).1 h2
    have a3 : P.intValuation ϖ ≠ 0 := P.intValuation_ne_zero ϖ (fun h => hϖ0 (by rw [h]; rfl))
    refine a1.trans ?_
    rw [← WithZero.exp_log a3, WithZero.exp_le_exp] at a2 ⊢
    push_cast at a2 ⊢
    omega
  have hx : P.valuation E ((s : E) / ϖ) ≤ 1 := by
    rw [map_div₀]
    refine div_le_one_of_le₀ ?_ zero_le
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact hle
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer _ hx
  have hd : Valued.v (φ ((d : 𝓞 E) : E)) = 1 :=
    le_antisymm (map_mem v φ d) (not_lt.1 (mt (hP d).2 d.2))
  have h3 : (s : E) * ((d : 𝓞 E) : E) = (n : E) * ϖ := by
    have h' : (s : E) / ϖ * ((d : 𝓞 E) : E) = (n : E) := h
    rw [← h']
    field_simp
  have h4 := congrArg (fun z => Valued.v (φ z)) h3
  simp only [map_mul] at h4
  rw [hd, mul_one, hs] at h4
  rw [h4]
  exact mul_le_of_le_one_left' (map_mem v φ n)

include hφ hP in
theorem card_residueField :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm P.asIdeal := by
  let ψ : 𝓞 E →+* v.adicCompletionIntegers F :=
    (φ.comp (algebraMap (𝓞 E) E)).codRestrict _ (map_mem v φ)
  let χ : 𝓞 E →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp ψ
  have hker : RingHom.ker χ = P.asIdeal := by
    ext x
    rw [RingHom.mem_ker, hP]
    show IsLocalRing.residue _ (ψ x) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, mem_max]
    rfl
  have hsurj : Function.Surjective χ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := Formalism.UG.P.glint_exists_approx v x
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r, ?_⟩
    show IsLocalRing.residue _ (ψ _) = _
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max]
    have e1 : ((ψ (algebraMap (𝓞 F) (𝓞 E) r) : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap (𝓞 F) (v.adicCompletion F) r := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← hφ]
      rfl
    rw [AddSubgroupClass.coe_sub, e1]
    exact hr
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

end General

theorem unif_chart : ∀ {D : D7} (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → Chart e v π → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (∃ p : Ov D v, algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D (ϖ : D.host.E)) ∧ Irreducible p) ∧ Nat.card (IsLocalRing.ResidueField (Ov D v)) = Ideal.absNorm P.asIdeal := by
  intro D e P v π he hc ϖ h1 h2
  let φ : D.host.E →+* v.adicCompletion D.host.F := π.comp (incA D)
  have hφ : ∀ t : D.host.F, φ (algebraMap D.host.F D.host.E t) =
      algebraMap D.host.F (v.adicCompletion D.host.F) t := by
    intro t
    have e1 : incA D (algebraMap D.host.F D.host.E t) =
        algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t
    show π (incA D _) = _
    rw [e1, hc.2.2.1, AlgHom.commutes, AlgHom.commutes]
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, hc.2.2.2, isInt_Ov]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  exact ⟨⟨⟨φ ϖ, map_mem v φ ϖ⟩, rfl, irreducible_of_valued v _ (valued_unif v φ P hφ hP ϖ h1 h2)⟩,
    card_residueField v φ P hφ hP⟩

end GlobalTheory.SplitUnif

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.SecondOrbits

section Abstract

variable {V H : Type} [AddCommGroup H] [Finite H] {h : H} {bs : H → H}

omit [Finite H] in
theorem inv_nsmul {Z : Type} {f : H → Z} (hf : ∀ t, f (t + h) = f t) (t : H) (i : ℕ) : f (t + i • h) = f t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, hf, ih]

theorem exists_back (a : H) (i : ℕ) : ∃ k, k < addOrderOf h ∧ a + i • h + k • h = a := by
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  refine ⟨(i * (addOrderOf h - 1)) % addOrderOf h, Nat.mod_lt _ hpos, ?_⟩
  rw [mod_addOrderOf_nsmul, add_assoc, ← add_nsmul]
  have : i + i * (addOrderOf h - 1) = i * addOrderOf h := by
    obtain ⟨m, hm⟩ : ∃ m, addOrderOf h = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hm, Nat.add_sub_cancel]; ring
  rw [this, mul_comm, mul_nsmul, addOrderOf_nsmul_eq_zero, nsmul_zero, add_zero]

theorem second_orbits [Fintype V] [Fintype H] [DecidableEq V] [DecidableEq H] (n' : V → ℕ) (hn : ∀ v, n' v = addOrderOf h)
    (π : (Σ v, Fin (n' v)) ≃ Bool × H) (β : V → Bool) (r : V → H)
    (hπ : ∀ v s, π ⟨v, s⟩ = (β v, r v + s.val • h))
    (horb : ∀ t, ∃ i : ℕ, bs t + i • h = t) (hstep : ∀ t, bs (t + h) = bs t) (vOf : H → V)
    (hv : ∀ t0 ∈ Finset.univ.image bs, ∀ s, π ⟨vOf t0, s⟩ = (false, t0 + s.val • h)) :
    (∀ v, v ∉ (Finset.univ.image bs).image vOf → β v = true) ∧
      ∀ f : H → ℝ, (∀ t, f (t + h) = f t) →
        ∑ v ∈ Finset.univ \ (Finset.univ.image bs).image vOf, f (r v) = ∑ t ∈ Finset.univ.image bs, f t := by
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  have reach : ∀ v, ∃ s, π ⟨v, s⟩ = (β v, bs (r v)) := fun v => by
    obtain ⟨i, hi⟩ := horb (r v)
    obtain ⟨k, hk, hk'⟩ := exists_back (h := h) (bs (r v)) i
    refine ⟨⟨k, by rw [hn]; exact hk⟩, ?_⟩
    rw [hπ]
    rw [hi] at hk'
    simp only [hk']
  have h1 : ∀ v, v ∉ (Finset.univ.image bs).image vOf → β v = true := fun v hvn => by
    by_contra hb
    have hb' : β v = false := by simpa using hb
    obtain ⟨s, hs⟩ := reach v
    have hm : bs (r v) ∈ Finset.univ.image bs := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have h0 := hv _ hm ⟨0, by rw [hn]; exact hpos⟩
    simp only [zero_smul, add_zero] at h0
    rw [hb', ← h0] at hs
    have := congrArg Sigma.fst (π.injective hs)
    exact hvn (Finset.mem_image.2 ⟨_, hm, this.symm⟩)
  refine ⟨h1, fun f hf => ?_⟩
  refine Finset.sum_bij (fun v _ => bs (r v)) (fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_ ?_ ?_
  · intro v hv1 v' hv2 he
    obtain ⟨s, hs⟩ := reach v
    obtain ⟨s', hs'⟩ := reach v'
    rw [h1 v (Finset.mem_sdiff.1 hv1).2] at hs
    rw [h1 v' (Finset.mem_sdiff.1 hv2).2] at hs'
    have he' : bs (r v) = bs (r v') := he
    rw [he', ← hs'] at hs
    exact congrArg Sigma.fst (π.injective hs)
  · intro t0 ht0
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 ht0
    obtain ⟨⟨v, s⟩, hvs⟩ := π.surjective (true, bs t)
    refine ⟨v, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hm => ?_⟩, ?_⟩
    · obtain ⟨t1, ht1, rfl⟩ := Finset.mem_image.1 hm
      rw [hv t1 ht1] at hvs
      cases congrArg Prod.fst hvs
    · rw [hπ] at hvs
      have e1 : r v + s.val • h = bs t := congrArg Prod.snd hvs
      obtain ⟨i, hi⟩ := horb t
      show bs (r v) = bs t
      rw [← inv_nsmul hstep (r v) s.val, e1, ← inv_nsmul hstep (bs t) i, hi]
  · intro v _
    obtain ⟨i, hi⟩ := horb (r v)
    rw [← inv_nsmul hf (bs (r v)) i, hi]

end Abstract

open NumberField GlobalTheory.InertCompare

theorem orderOf_iotaH (φ : Formalism.HC.Frame) (t : φ.A) : orderOf (φ.iota t) = addOrderOf t :=
  orderOf_ofAdd_eq_addOrderOf t

theorem eTau_tauPl (D : D7) (z : Bool × HH D) : ((D.eTau (tauPl D z) : D.R.Psi) : D.R.GG) = plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem eq_tauPl (D : D7) {τ : D.what₂.Tau} {z : Bool × HH D} (h : ((D.eTau τ : D.R.Psi) : D.R.GG) = plGG D z) :
    τ = tauPl D z :=
  D.eTau.injective (Subtype.ext (h.trans (eTau_tauPl D z).symm))

theorem orbit_positions (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (v : Fin (D.gat u w hg).P.nV) :
    (D.gat u w hg).P.n' v = addOrderOf (hP D (D.what₂.places.resChar w)) ∧
      ∃ z : Bool × HH D, ∀ s : Fin ((D.gat u w hg).P.n' v),
        hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) z s.val) := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨hg.1⟩
  have hc : IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w) := Or.inl hg.2.2.1
  have : (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hg.1.ne_zero)).2 (Nat.prime_iff_prime_int.1 hg.1)
  obtain ⟨⟨P, hP1, hP2⟩⟩ := (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)}).nonempty_primesOver (S := 𝓞 D.host.E)
  obtain ⟨φ, hφ, hstep⟩ := exists_frob_step D _ hc P
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D _ hc
  have hn : (D.gat u w hg).P.n' v = addOrderOf (hP D (D.what₂.places.resChar w)) := by
    rw [hT.gat_n u w hg v P φ hφ, galE_frob_snd D _ h2 hq hd P φ hφ, orderOf_iotaH]
  have hpos : 0 < (D.gat u w hg).P.n' v := by rw [hn]; exact addOrderOf_pos _
  obtain ⟨z, hz⟩ := (tauPl_bijective D).2 (hT.gat_pos u w hg ⟨v, ⟨0, hpos⟩⟩)
  refine ⟨hn, z, ?_⟩
  rintro ⟨s, hs⟩
  induction s with
  | zero => rw [posPl_zero, hz]
  | succ s ih =>
    have hs' : s < (D.gat u w hg).P.n' v := Nat.lt_of_succ_lt hs
    have e1 : (⟨s + 1, hs⟩ : Fin ((D.gat u w hg).P.n' v)) = posAdd ⟨s, hs'⟩ 1 := Fin.ext (Nat.mod_eq_of_lt hs).symm
    refine eq_tauPl D ?_
    show _ = plGG D (posPl D _ z (s + 1))
    rw [e1, hT.gat_step u w hg v ⟨s, hs'⟩ P φ hφ, ih hs', eTau_tauPl, ← posPl_add, hstep]

theorem places_off_first_orbits : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D), LatTied hT X Y → ∃ r : Fin (D.gat u w hg).P.nV → HH D, (∀ v, v ∉ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg) → (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) ∧ (Y.Fl u w hg).TT v = ∅ ∧ ∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, r v) s.val)) ∧ ∀ f : HH D → ℝ, (∀ t, f (t + hP D (D.what₂.places.resChar w)) = f t) → ∑ v ∈ Finset.univ \ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg), f (r v) = ∑ t ∈ reps X (D.what₂.places.resChar w), f t := by
  intro D u w hg L hT X Y hL
  have hs : ¬ IsSg D (D.what₂.places.resChar w) := fun hs => by
    have := hg.2.2.1.symm.trans hs
    cases this
  have hstepP : stepP D (D.what₂.places.resChar w) = hP D (D.what₂.places.resChar w) := if_neg hs
  have hnP : nP D (D.what₂.places.resChar w) = addOrderOf (hP D (D.what₂.places.resChar w)) := if_neg hs
  have hpos : ∀ (z : Bool × HH D) (e : ℕ), posPl D (D.what₂.places.resChar w) z e =
      (z.1, z.2 + e • hP D (D.what₂.places.resChar w)) := fun z e => by
    simp [posPl, partner, hs]
  have hn := fun v => (orbit_positions D u w hg hT v).1
  choose z hz using fun v => (orbit_positions D u w hg hT v).2
  obtain ⟨-, -, -, -, -, hT2, hT1⟩ := hL u w hg
  have hreps : reps X (D.what₂.places.resChar w) = Finset.univ.image (X.bs (hP D (D.what₂.places.resChar w))) := by
    unfold reps
    rw [hstepP]
  have key := second_orbits (h := hP D (D.what₂.places.resChar w)) (bs := X.bs (hP D (D.what₂.places.resChar w)))
    (D.gat u w hg).P.n' hn ((hT.gat_pos u w hg).trans (plEquiv D).symm) (fun v => (z v).1) (fun v => (z v).2)
    (fun v s => by
      rw [Equiv.trans_apply, Equiv.symm_apply_eq, hz, hpos]
      rfl)
    (X.bs_orb _) (X.bs_step _) (Y.vOf u w hg)
    (fun t0 ht0 s => by
      rw [Equiv.trans_apply, Equiv.symm_apply_eq]
      exact eq_tauPl D ((hT1 t0 (hreps ▸ ht0)).2 s).1)
  rw [hreps]
  refine ⟨fun v => (z v).2, fun v hv => ?_, key.2⟩
  have hb : z v = (true, (z v).2) := Prod.ext (key.1 v hv) rfl
  refine ⟨(hn v).trans hnP.symm, ?_, fun s => by rw [hz, ← hb]⟩
  refine Finset.eq_empty_of_forall_notMem fun s => (hT2 v s ((z v).2 + s.val • hP D (D.what₂.places.resChar w)) ?_).1
  rw [hz, eTau_tauPl, hpos, hb]
  rfl

end GlobalTheory.SecondOrbits
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.IntegralAtPlace

theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : ℂ_[p]}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := ℂ_[p])).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_le_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (φ : D.host.E →+* ℂ_[p]) (a : D.host.E), a ∈ D.host.AA0 → ‖φ a‖ ≤ 1 := by
  intro D p hpF hpd φ a ha
  obtain ⟨-, -, hqd, -, hd2⟩ := hypOdd_of_hostHyp D.host.hyp
  have hint : ∀ y : 𝓞 D.host.E, ‖φ (y : D.host.E)‖ ≤ 1 := fun y => by
    have h : IsIntegral ℤ (φ (y : D.host.E)) := by
      obtain ⟨f, hf, hx⟩ := RingOfIntegers.isIntegral_coe y
      refine ⟨f, hf, ?_⟩
      have := congrArg φ hx
      rw [Polynomial.hom_eval₂, map_zero] at this
      rwa [RingHom.ext_int (φ.comp (algebraMap ℤ D.host.E)) (algebraMap ℤ ℂ_[p])] at this
    exact norm_le_one_of_isIntegral h
  let Q : Ideal (𝓞 D.host.E) :=
    { carrier := {y | ‖φ (y : D.host.E)‖ < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at *
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        rw [norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hint c)) hx }
  have hmem : ∀ y, y ∈ Q ↔ ‖φ (y : D.host.E)‖ < 1 := fun y => Iff.rfl
  haveI hQ : Q.IsPrime := by
    refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
    · have h1 := (hmem 1).1 (h ▸ Submodule.mem_top)
      simp at h1
    · rw [hmem, show ((x * y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) * y from rfl, map_mul,
        norm_mul] at hxy
      by_contra hc
      push_neg at hc
      rw [hmem, hmem, not_lt, not_lt] at hc
      have := mul_le_mul hc.1 hc.2 zero_le_one (norm_nonneg _)
      linarith
  have hpQ : (p : 𝓞 D.host.E) ∈ Q := by
    rw [hmem]
    have e : ((p : 𝓞 D.host.E) : D.host.E) = (p : D.host.E) := by simp
    rw [e, map_natCast]
    have : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨z, hz, hden⟩ := GlobalTheory.AAUnitAway.exists_den D Q hpF.out (by rw [hpd]; exact UpperTheory.Small.d_not_mem D.host)
    (by rw [hpd]; exact hqd.symm) hpQ
  have hz1 : ‖φ (z : D.host.E)‖ = 1 := le_antisymm (hint z) (not_lt.1 ((hmem z).not.1 hz))
  obtain ⟨w, hw⟩ := hden a ha
  have := hint w
  rwa [hw, map_mul, norm_mul, hz1, mul_one] at this

end GlobalTheory.IntegralAtPlace
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.EigenGenerator

theorem norm_dgen_eq_one : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (p : ℕ) [Fact p.Prime] (lm : Qbar →+* ℂ_[p]), p = D.host.d → ∀ τ, ‖lamC lm (cD τ)‖ = 1 := by
  intro D cD hD p _ lm hp τ
  obtain ⟨M, hMnf, hM, hs⟩ := hD
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have hh := D.host.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hh
  have h2 : p ∉ D.host.small := hp ▸ UpperTheory.Small.d_not_mem D.host
  have hq : p ≠ D.host.q := by omega
  rw [← hsc]
  exact norm_generator_eq_one D p lm h2 hq M hM τ s hsp

end GlobalTheory.EigenGenerator
end
