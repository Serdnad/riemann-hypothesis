module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle086
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle162
import Formalism.LocalRingCardinality.DataHost
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Unramified.Locus
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle117
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedAdjoinSqrtOfNotMem
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
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle161
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle001
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

noncomputable section

namespace GlobalTheory.KernelScalarUnit

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts GlobalTheory.UnUnitCmp
open scoped nonZeroDivisors

section Ideals

variable {K : Type} [Field K] [NumberField K]

theorem exists_pow_eq_span {𝔞 𝔟 : Submodule (𝓞 K) K} (h : 𝔞 * 𝔟 = 1) :
    ∃ (n : ℕ) (a : K), 0 < n ∧ 𝔞 ^ n = Submodule.span (𝓞 K) {a} := by
  have hu : IsUnit 𝔞 := IsUnit.of_mul_eq_one 𝔟 h
  have hv : IsUnit 𝔟 := IsUnit.of_mul_eq_one 𝔞 (by rw [mul_comm]; exact h)
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨𝔞, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hu)⟩
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨𝔟, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hv)⟩
  have hIJ : I * J = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]
    exact h
  let U : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mkOfMulEqOne I J hIJ
  have h1 : ClassGroup.mk K (U ^ Fintype.card (ClassGroup (𝓞 K))) = 1 := by rw [map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := ClassGroup.mk_eq_one_iff.1 h1
  refine ⟨_, a, Fintype.card_pos (α := ClassGroup (𝓞 K)), ?_⟩
  rw [← ha, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

omit [NumberField K] in
theorem map_mem_one (c : K →+* K) {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : c x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨⟨c r, map_isIntegral_int c r.isIntegral_coe⟩, rfl⟩

omit [NumberField K] in
theorem map_mem_pow (c : K →+* K) {𝔞 𝔟 : Submodule (𝓞 K) K} (h : ∀ x ∈ 𝔞, c x ∈ 𝔟) :
    ∀ (n : ℕ), ∀ x ∈ 𝔞 ^ n, c x ∈ 𝔟 ^ n
  | 0, x, hx => by rw [pow_zero] at *; exact map_mem_one c hx
  | n + 1, x, hx => by
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul c]
      exact Submodule.mul_mem_mul (map_mem_pow c h n a ha) (h b hb)
    · rw [map_add c]
      exact add_mem ha hb

theorem exists_pow_eq_span_normOne (c : K →+* K) (hc : ∀ x, c (c x) = x) {𝔞 𝔟 : Submodule (𝓞 K) K}
    (hb : ∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) (h : 𝔞 * 𝔟 = 1) :
    ∃ (n : ℕ) (z : K), 0 < n ∧ c z * z = 1 ∧ 𝔞 ^ n = Submodule.span (𝓞 K) {z} := by
  obtain ⟨n, a, hn, ha⟩ := exists_pow_eq_span h
  have hb' : 𝔟 ^ n = Submodule.span (𝓞 K) {c a} := by
    apply le_antisymm
    · intro y hy
      have h1 := map_mem_pow c (fun x hx => (hb x).1 hx) n y hy
      rw [ha, Submodule.mem_span_singleton] at h1
      obtain ⟨r, hr⟩ := h1
      refine Submodule.mem_span_singleton.2 ⟨⟨c r, map_isIntegral_int c r.isIntegral_coe⟩, ?_⟩
      rw [← hc y, ← hr, Algebra.smul_def r, map_mul]
      rfl
    · rw [Submodule.span_singleton_le_iff_mem]
      exact map_mem_pow c (fun x hx => (hb _).2 (by rwa [hc])) n a (ha ▸ Submodule.mem_span_singleton_self a)
  have h2 : Submodule.span (𝓞 K) {a * c a} = 1 := by
    rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span, ← ha, ← hb', ← mul_pow, h, one_pow]
  have h0 : a * c a ≠ 0 := fun h0 => by
    rw [h0, Submodule.span_singleton_eq_bot.2 rfl] at h2
    have : (1 : K) ∈ (⊥ : Submodule (𝓞 K) K) := h2 ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
    simp at this
  have a0 : a ≠ 0 := left_ne_zero_of_mul h0
  have c0 : c a ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨n + n, a / c a, by omega, ?_, ?_⟩
  · rw [map_div₀, hc]; field_simp
  · rw [pow_add, ha, Submodule.span_mul_span, Set.singleton_mul_singleton, ← mul_one (Submodule.span (𝓞 K) {a / c a}), ← h2,
      Submodule.span_mul_span, Set.singleton_mul_singleton]
    congr 2
    field_simp

end Ideals

theorem normOne_pow (D : D7) : NormOnePowerPrincipal D := by
  let := D.host.cmStar
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rintro 𝔞 ⟨𝔟, hb, h⟩
  obtain ⟨n, z, hn, hz, e⟩ := exists_pow_eq_span_normOne (D.host.conj : D.host.E →+* D.host.E)
    (fun x => by change D.host.conj (D.host.conj x) = x; rw [← hs, ← hs, star_star]) hb h
  have hz' : star z * z = 1 := by rw [hs]; exact hz
  exact ⟨n, ⟨z, hz', by rw [mul_comm]; exact hz'⟩, hn, e⟩

section Local

variable {K : Type} [Field K] [NumberField K] {C : Type} [NormedField C] [IsUltrametricDist C] (ψ : K →+* C)

omit [NumberField K] in
theorem norm_int_le (a : 𝓞 K) : ‖ψ (a : K)‖ ≤ 1 := norm_le_one_of_isIntegral (map_isIntegral_int ψ a.isIntegral_coe)

def ball (r : ℝ) (hr : 0 ≤ r) : Submodule (𝓞 K) K where
  carrier := {x | ‖ψ x‖ ≤ r}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simpa using hr
  smul_mem' := fun c a ha => by
    simp only [Set.mem_ofPred_eq, Algebra.smul_def, map_mul, norm_mul] at *
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le ψ c)).trans ha

end Local

section Det

variable (D : D7) {l : ℕ} [Fact l.Prime] (ψ : D.host.E →+* ℂ_[l]) {N : ℕ}
  {L₀ L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {P : Matrix (Fin N) (Fin N) D.host.E}

end Det

section Power

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def lamTau (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] :=
  lam.comp ((embT D τ).codRestrict Qbar (emb_mem (embT D τ)))

theorem tauEmb_eq (τ : D.what₂.Tau) : tauEmb D lam τ = lamTau D lam τ := by
  funext x
  unfold tauEmb lamC
  rw [dite_eq_left (emb_mem (embT D τ) x)]
  rfl

end Power

section Main

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

variable (E : KerEnt D Dx Tw) (O : ∀ u μ, LiftObj D (D.chTw u μ))

end Main

end GlobalTheory.KernelScalarUnit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → ∀ i (l : ℂ) w, h i w = l • w → op i (LinearMap.adjoint Θ w) = l • LinearMap.adjoint Θ w := by
  first | exact @GlobalTheory.HkUp.eigen_up_along_adjoint | exact GlobalTheory.HkUp.eigen_up_along_adjoint | (intros; apply GlobalTheory.HkUp.eigen_up_along_adjoint <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory

theorem natCast_mem_heightOneSpectrum_coprime :
    ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (P : HeightOneSpectrum (𝓞 E)), ((p : ℕ) : 𝓞 E) ∉ P.asIdeal → ∃ ℓ : ℕ, 0 < ℓ ∧ ((ℓ : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ Nat.Coprime ℓ p := by
  intro E _ _ p hp P hpP
  have hN : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  haveI : P.asIdeal.IsPrime := P.isPrime
  have hmem : ∀ n : ℕ, ((n : 𝓞 E) ∈ P.asIdeal ↔ ringChar (𝓞 E ⧸ P.asIdeal) ∣ n) := by
    intro n
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.spec _ n
  have hq0 : ringChar (𝓞 E ⧸ P.asIdeal) ≠ 0 := by
    intro h0
    have := (hmem _).1 (Ideal.absNorm_mem P.asIdeal)
    rw [h0, zero_dvd_iff] at this
    exact hN this
  have hqp : (ringChar (𝓞 E ⧸ P.asIdeal)).Prime :=
    (CharP.char_is_prime_or_zero (𝓞 E ⧸ P.asIdeal) _).resolve_right hq0
  refine ⟨ringChar (𝓞 E ⧸ P.asIdeal), hqp.pos, (hmem _).2 dvd_rfl, ?_⟩
  refine (Nat.coprime_primes hqp hp).2 ?_
  intro hq
  exact hpP ((hmem p).2 (hq ▸ dvd_rfl))

end GlobalTheory
end

section

open NumberField IsDedekindDomain

theorem GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal := by
  intro E _ _ _
  obtain ⟨d, s, hs, hsn, -⟩ := GlobalTheory.CMGen.exists_sqrt_totallyNegative E
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hsn
    have : s = 0 := by simpa using hs
    rw [this]
    exact zero_mem _
  have h2d : (2 * d : 𝓞 (maximalRealSubfield E)) ≠ 0 := mul_ne_zero two_ne_zero hd0
  refine ⟨Ideal.absNorm (Ideal.span {2 * d}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h2d
  intro K _ _ _ _ w hw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {2 * d}))
  haveI : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  have hint : ∀ x : 𝓞 (maximalRealSubfield E),
      IsIntegral ℤ (algebraMap E K ((x : maximalRealSubfield E) : E)) := fun x =>
    (RingOfIntegers.isIntegral_coe x).map
      ((algebraMap E K).comp (maximalRealSubfield E).subtype).toIntAlgHom
  have hmem : algebraMap E K ((d : maximalRealSubfield E) : E) ∈ maximalRealSubfield K :=
    (GlobalTheory.algebraMap_mem_maximalRealSubfield_iff _).2 (d : maximalRealSubfield E).2
  have hai : IsIntegral ℤ (⟨_, hmem⟩ : maximalRealSubfield K) :=
    (isIntegral_algHom_iff (maximalRealSubfield K).subtype.toIntAlgHom Subtype.val_injective).1 (hint d)
  let a : 𝓞 (maximalRealSubfield K) := ⟨_, hai⟩
  refine GlobalTheory.unramified_adjoin_sqrt_of_not_mem K a (algebraMap E K s) ?_ ?_ w ?_
  · rw [← map_pow, hs]; rfl
  · exact fun h => hsn ((GlobalTheory.algebraMap_mem_maximalRealSubfield_iff _).1 h)
  · intro h
    apply hw
    have h1 : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) (2 * a) ∈ w.asIdeal := h
    let c' : 𝓞 K := ⟨_, hint c⟩
    have h2 : ((Ideal.absNorm (Ideal.span {2 * d}) : ℕ) : 𝓞 K)
        = c' * algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) (2 * a) := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      let f : 𝓞 (maximalRealSubfield E) →+* K :=
        ((algebraMap E K).comp (maximalRealSubfield E).subtype).comp (algebraMap _ _)
      have h3 := congrArg f hc
      rw [map_natCast, map_mul, map_mul, map_ofNat] at h3
      rw [map_natCast, ← h3, map_mul, map_mul, map_mul, map_ofNat, map_ofNat]
      rfl
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
end
