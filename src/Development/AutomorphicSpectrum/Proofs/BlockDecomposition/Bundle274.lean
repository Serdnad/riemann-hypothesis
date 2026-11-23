module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle262
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle266
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle250
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle265
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle269
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle261
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem dvd_pow_qOf_sub_self : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), (Ideal.span {π}).IsMaximal →
    Finite (↥(OL K) ⧸ Ideal.span {π}) → ∀ c : ↥(OL K), π ∣ c ^ qOf π - c := by
  intro l _ K π hmax hfin c
  set_option synthInstance.maxHeartbeats 200000 in
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
      map_sub (Ideal.Quotient.mk _), map_pow (Ideal.Quotient.mk _), sub_eq_zero]
  letI := Ideal.Quotient.field (Ideal.span {π})
  letI := Fintype.ofFinite (↥(OL K) ⧸ Ideal.span {π})
  rw [qOf, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card _

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem resfield_of_irreducible : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    (Ideal.span {π}).IsMaximal ∧ Finite (↥(OL K) ⧸ Ideal.span {π}) ∧ ∃ f : ℕ, 0 < f ∧ qOf π = l ^ f := by
  intro l _ K π hπ
  obtain ⟨⟨⟨hD, hV, -⟩, -⟩, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l K
  have hlp : l.Prime := Fact.out
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL K)) := by
    intro a b hab
    have h1 : algebraMap ℤ_[l] ↥K.1 a = algebraMap ℤ_[l] ↥K.1 b := congrArg Subtype.val hab
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1 b] at h1
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] ↥K.1).injective h1)
  have hi : Algebra.IsIntegral ℤ_[l] ↥(OL K) := integralClosure.algebraIsIntegral
  have hf : FaithfulSMul ℤ_[l] ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hl : ¬ IsUnit ((l : ℕ) : ↥(OL K)) := by
    intro hu
    rw [← map_natCast (algebraMap ℤ_[l] ↥(OL K))] at hu
    letI : Algebra.IsIntegral ℤ_[l] ↥(OL K) := hi
    letI : FaithfulSMul ℤ_[l] ↥(OL K) := hf
    letI : IsLocalHom (algebraMap ℤ_[l] ↥(OL K)) :=
      Algebra.IsIntegral.isLocalHom ℤ_[l] ↥(OL K)
    exact PadicInt.irreducible_p.not_isUnit (isUnit_of_map_unit _ _ hu)
  have hdvd : π ∣ ((l : ℕ) : ↥(OL K)) := by
    have hm : ((l : ℕ) : ↥(OL K)) ∈ IsLocalRing.maximalIdeal ↥(OL K) := hl
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have hle : Ideal.span {((l : ℕ) : ↥(OL K)) ^ 1} ≤ Ideal.span {π} := by
    rw [pow_one, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hmax : (Ideal.span {π}).IsMaximal := by
    rw [← hπ.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hfinQ : Finite (↥(OL K) ⧸ Ideal.span {π}) := by
    have := hfin 1
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  refine ⟨hmax, hfinQ, ?_⟩
  letI : Field (↥(OL K) ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  haveI : Fintype (↥(OL K) ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hz : ((l : ℕ) : ↥(OL K) ⧸ Ideal.span {π}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
    exact hdvd
  haveI : Nontrivial (↥(OL K) ⧸ Ideal.span {π}) :=
    (Ideal.Quotient.nontrivial_iff (I := Ideal.span {π})).2 hmax.ne_top
  haveI : CharP (↥(OL K) ⧸ Ideal.span {π}) l :=
    (CharP.charP_iff_prime_eq_zero (R := ↥(OL K) ⧸ Ideal.span {π}) hlp).2 hz
  obtain ⟨n, -, hn⟩ := FiniteField.card (↥(OL K) ⧸ Ideal.span {π}) l
  refine ⟨n, n.pos, ?_⟩
  rw [qOf, Nat.card_eq_fintype_card, hn]

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.Glue

section Abs

variable {B : Type} [CommRing B]

def InMul (S : Subring B) (ϖ z : B) : Prop := ∃ s ∈ S, z = ϖ * s

theorem InMul.add {S : Subring B} {ϖ z w : B} (hz : InMul S ϖ z) (hw : InMul S ϖ w) :
    InMul S ϖ (z + w) := by
  obtain ⟨s, hs, rfl⟩ := hz
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨s + t, S.add_mem hs ht, by ring⟩

theorem InMul.sub {S : Subring B} {ϖ z w : B} (hz : InMul S ϖ z) (hw : InMul S ϖ w) :
    InMul S ϖ (z - w) := by
  obtain ⟨s, hs, rfl⟩ := hz
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨s - t, S.sub_mem hs ht, by ring⟩

theorem InMul.mul {S : Subring B} {ϖ z w : B} (hz : InMul S ϖ z) (hw : w ∈ S) :
    InMul S ϖ (z * w) := by
  obtain ⟨s, hs, rfl⟩ := hz
  exact ⟨s * w, S.mul_mem hs hw, by ring⟩

theorem inMul_zero (S : Subring B) (ϖ : B) : InMul S ϖ 0 :=
  ⟨0, S.zero_mem, by ring⟩

theorem pow_sub_pow_inMul {S : Subring B} {ϖ T f s : B} (hϖ : ϖ ∈ S) (hT : T ∈ S) (hs : s ∈ S)
    (h : T = ϖ * s + f) (k : ℕ) : InMul S ϖ (T ^ k - f ^ k) := by
  have hf : f ∈ S := by
    have : f = T - ϖ * s := by rw [h]; ring
    rw [this]
    exact S.sub_mem hT (S.mul_mem hϖ hs)
  induction k with
  | zero => simpa using inMul_zero S ϖ
  | succ k ih =>
    have e : T ^ (k + 1) - f ^ (k + 1) = (T ^ k - f ^ k) * T + (ϖ * s) * f ^ k := by
      rw [pow_succ, pow_succ]
      have : f ^ k * f = f ^ k * (T - ϖ * s) := by rw [h]; ring
      rw [this]; ring
    rw [e]
    exact (ih.mul hT).add ⟨s * f ^ k, S.mul_mem hs (S.pow_mem hf k), by ring⟩

theorem evalMod_of_lift {R T : Type} [CommRing R] [CommRing T] (S : Subring B) (F : ℕ → Ideal B)
    (ϖ : B) (h : R →+* B) (τ : T →* B) (r : R →+* T) (hτ0 : τ 0 = 0) (hτS : ∀ a, τ a ∈ S)
    (hϖ : ϖ ∈ S) (hadd : ∀ a b, InMul S ϖ (τ (a + b) - τ a - τ b))
    (hcoef : ∀ c, InMul S ϖ (h c - τ (r c))) (hF : ∀ k, ∀ f ∈ F 1, f ^ k ∈ F k)
    (x y : T) (φ : PowerSeries R)
    (hy : ∀ D, x ^ D ∣ y - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i)
    (M : ℕ) (s : B) (hs : s ∈ S) (hM : τ x ^ M - ϖ * s ∈ F 1) (k : ℕ) :
    ∃ D, ∀ D' ≥ D, Near S ϖ (F k) 1
      ((∑ i ∈ Finset.range D', h (PowerSeries.coeff i φ) * τ x ^ i) - τ y) := by
  have hsum : ∀ D, InMul S ϖ ((∑ i ∈ Finset.range D, h (PowerSeries.coeff i φ) * τ x ^ i) -
      τ (∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i)) := by
    intro D
    induction D with
    | zero => simpa [hτ0] using inMul_zero S ϖ
    | succ D ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      generalize hA : (∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i) = A at ih ⊢
      generalize hP : (∑ i ∈ Finset.range D, h (PowerSeries.coeff i φ) * τ x ^ i) = P at ih ⊢
      have e1 : P + h (PowerSeries.coeff D φ) * τ x ^ D -
          τ (A + r (PowerSeries.coeff D φ) * x ^ D) =
          (P - τ A) + (h (PowerSeries.coeff D φ) - τ (r (PowerSeries.coeff D φ))) * τ x ^ D -
          (τ (A + r (PowerSeries.coeff D φ) * x ^ D) - τ A -
            τ (r (PowerSeries.coeff D φ) * x ^ D)) := by
        rw [map_mul τ, map_pow τ]; ring
      rw [e1]
      exact (ih.add ((hcoef _).mul (S.pow_mem (hτS x) D))).sub (hadd _ _)
  refine ⟨M * k, fun D' hD' => ?_⟩
  obtain ⟨b, hb⟩ := hy D'
  have hP := hsum D'
  generalize (∑ i ∈ Finset.range D', r (PowerSeries.coeff i φ) * x ^ i) = A at hb hP
  generalize (∑ i ∈ Finset.range D', h (PowerSeries.coeff i φ) * τ x ^ i) = P at hP ⊢
  have hyA : y = A + x ^ D' * b := by rw [← hb]; ring
  obtain ⟨a, ha, hT⟩ := pow_sub_pow_inMul hϖ (S.pow_mem (hτS x) M) hs
    (f := τ x ^ M - ϖ * s) (by ring) k
  obtain ⟨u, hu, hPu⟩ := hP
  obtain ⟨v, hv, hv'⟩ := hadd A (x ^ D' * b)
  have hg : (τ x ^ M - ϖ * s) ^ k ∈ F k := hF k _ hM
  set g := (τ x ^ M - ϖ * s) ^ k with hgdef
  have hpow : τ x ^ D' = (τ x ^ M) ^ k * τ x ^ (D' - M * k) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hw : τ x ^ (D' - M * k) * τ b ∈ S := S.mul_mem (S.pow_mem (hτS x) _) (hτS b)
  obtain ⟨w, hwdef⟩ : ∃ w, w = τ x ^ (D' - M * k) * τ b := ⟨_, rfl⟩
  rw [← hwdef] at hw
  have hC : τ (x ^ D' * b) = (τ x ^ M) ^ k * w := by
    rw [map_mul τ, map_pow τ, hpow, hwdef]; ring
  refine ⟨u - v - a * w, S.sub_mem (S.sub_mem hu hv) (S.mul_mem ha hw), ?_⟩
  have e : P - τ y - ϖ ^ 1 * (u - v - a * w) = -(g * w) := by
    rw [hyA]
    linear_combination hPu - hv' - hC - w * hT
  rw [e]
  exact (F k).neg_mem (Ideal.mul_mem_right w (F k) hg)

end Abs

section Conc

variable (l : ℕ) [Fact l.Prime]

def tchHom : Tl l →* Formalism.Per6.BdRp l :=
  ((wB l : Wl l →+* Formalism.Per6.BdRp l) : Wl l →* Formalism.Per6.BdRp l).comp (WittVector.teichmuller l)

theorem tchHom_apply (a : Tl l) : tchHom l a = tch l a := rfl

theorem tchHom_zero : tchHom l 0 = 0 := by
  simp [tchHom]

theorem teichmuller_add_sub (a b : Tl l) : ∃ w : Wl l,
    WittVector.teichmuller l (a + b) - WittVector.teichmuller l a - WittVector.teichmuller l b
      = w * (l : Wl l) := by
  set z : Wl l := WittVector.teichmuller l (a + b) - WittVector.teichmuller l a -
    WittVector.teichmuller l b with hz
  have h0 : z.coeff 0 = 0 := by
    have : WittVector.constantCoeff z = 0 := by
      simp [hz, map_sub]
    simpa using this
  have h1 : z = WittVector.verschiebung (z.shift 1) := by
    have := WittVector.eq_iterate_verschiebung (n := 1) (x := z) (by
      intro i hi
      obtain rfl : i = 0 := by omega
      exact h0)
    simpa using this
  obtain ⟨u, hu⟩ := (WittVector.frobenius_bijective l (Tl l)).2 (z.shift 1)
  refine ⟨u, ?_⟩
  rw [h1, ← hu, WittVector.verschiebung_frobenius]

end Conc

theorem evalMod_teichmuller : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (π : ↥(OL K)) (S : Subring (Formalism.Per6.BdRp l)),
    (∀ a, wB l a ∈ S) → (∀ c, oB K μ c ∈ S) → PerEnv S (FB l) (oB K μ π) → π ∣ (l : ↥(OL K)) →
    ∀ (r : ↥(OL K) →+* Tl l), (∀ c, ∃ c', tch l (r c) = oB K μ (c + π * c')) →
    ∀ (x y : Tl l), ‖thB l (tch l x)‖ < 1 → ∀ (φ : PowerSeries ↥(OL K)),
      (∀ D, x ^ D ∣ y - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i) →
      EvalMod S (FB l) (oB K μ π) (oB K μ) φ (tch l x) (tch l y) 1 := by
  intro l _ K μ π S hw ho env hπ r hr x y hx φ hy k
  obtain ⟨e, he⟩ := hπ
  have hl : ((l : ℕ) : Formalism.Per6.BdRp l) = oB K μ π * oB K μ e := by
    rw [← map_mul, ← he, map_natCast]
  have hadd : ∀ a b, InMul S (oB K μ π) (tchHom l (a + b) - tchHom l a - tchHom l b) := by
    intro a b
    obtain ⟨w, hw'⟩ := teichmuller_add_sub l a b
    refine ⟨wB l w * oB K μ e, S.mul_mem (hw _) (ho _), ?_⟩
    have := congrArg (wB l) hw'
    simp only [map_sub, map_mul, map_natCast] at this
    simp only [tchHom_apply, tch]
    rw [this, hl]; ring
  have hcoef : ∀ c, InMul S (oB K μ π) (oB K μ c - tchHom l (r c)) := by
    intro c
    obtain ⟨c', hc'⟩ := hr c
    refine ⟨- oB K μ c', S.neg_mem (ho _), ?_⟩
    rw [tchHom_apply, hc', map_add (f := _), map_mul]; ring
  have hϖ0 : thB l (oB K μ π) ≠ 0 := (env.unit.map (thB l)).ne_zero
  obtain ⟨M, -, s, hs, hM⟩ := GlobalTheory.T.teichmuller_near_power_exists S hw (oB K μ π) hϖ0 x hx
  rw [pow_one] at hM
  exact evalMod_of_lift S (FB l) (oB K μ π) (oB K μ) (tchHom l) r (tchHom_zero l)
    (fun a => hw _) env.mem hadd hcoef
    (fun k f hf => Ideal.pow_mem_pow (by simpa [FB] using hf) k) x y φ hy M s hs hM k

end GlobalTheory.CompanionTheory.LTPer.Glue
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.period_product_filtration_levels : ∀ {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (t : ι → Formalism.Per6.BdRp l) (i₀ : ι), i₀ ∈ s →
    ∀ u : (Formalism.Per6.BdRp l)ˣ, ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l * (u : Formalism.Per6.BdRp l) →
      thB l (t i₀) = 0 →
      ∀ μ ∈ s, (μ = i₀ → t μ ∉ FB l 2) ∧ (μ ≠ i₀ → t μ ∉ FB l 1) := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.prod_eq_t_mul_unit_count | exact GlobalTheory.CompanionTheory.LTPer.prod_eq_t_mul_unit_count | (intros; apply GlobalTheory.CompanionTheory.LTPer.prod_eq_t_mul_unit_count <;> assumption)
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.regular_representation_continuous : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ x : Lp V 2 μ, Continuous (fun h : G n => rR μ V h x) ∧ Continuous (fun y : G n => lT μ V y x) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.translations_strongly_continuous | exact GlobalTheory.CompanionTheory.PresSobA.translations_strongly_continuous | (intros; apply GlobalTheory.CompanionTheory.PresSobA.translations_strongly_continuous <;> assumption)
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.derivative_right_basis_expansion : ∀ n : ℕ, ∃ A : (Bool × Fin n × Fin n) → Mat n → CLof (Mat n) ℝ, (∀ p, ContDiffOn ℝ ∞ (A p) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (D : CLof (Mat n) V), ∀ z ∈ GLs n, D = ∑ p, (A p z).smulRight (D (z * bs p)) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.Frame.frame | exact GlobalTheory.CompanionTheory.PresSobA.Frame.frame | (intros; apply GlobalTheory.CompanionTheory.PresSobA.Frame.frame <;> assumption)
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.pairing_restriction_natural : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] (P : ℕ → Cx.{1} K) (Q T : ℕ → Sy.{1} K ι) (pr : ∀ (S : Finset ι) {a a' c : ℕ}, a + a' = c → CxPairing (P a) ((Q a').K S) ((T c).K S)), (∀ {S S' : Finset ι} (h : S ⊆ S') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : ((Q a').K S).X j), ((T c).res h).f n ((pr S ha).μ hn x y) = (pr S' ha).μ hn x (((Q a').res h).f j y)) → (∀ a, (Q a).Desc) → (∀ c, (T c).Desc) → (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha)) → KunE (P := P) (Q := fun a => (Q a).K ∅) (T := fun c => (T c).K ∅) (fun {a a' c} ha => pr ∅ ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_glue | exact GlobalTheory.CompanionTheory.KunGlue.kun_glue | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_glue <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.AdelicThetaSeries

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

namespace ThcInt

theorem scalC_mul (a b : IdeleGroup k) :
    (scalC (a * b) : GL ι 𝔸[k]) = scalC a * scalC b := by
  simp only [scalC, map_mul]

theorem scalC_commute (a : IdeleGroup k) (A : GL ι 𝔸[k]) :
    (scalC a : GL ι 𝔸[k]) * A = A * scalC a := by
  apply Units.ext
  simp only [Units.val_mul, scalC, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact (Matrix.scalar_commute _ (fun r ↦ Commute.all _ r) _)

theorem continuous_scalC : Continuous (scalC : IdeleGroup k → GL ι 𝔸[k]) := by
  refine Continuous.units_map _ ?_
  refine continuous_matrix fun i j ↦ ?_
  by_cases h : i = j
  · subst h
    simpa [Matrix.scalar_apply] using continuous_id'
  · simpa [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h] using continuous_const

theorem thetaC_ltr (A h : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    thetaC (ltr A F) h = thetaC F (A * h) := by
  simp only [thetaC, ltr, Units.val_mul, Matrix.mulVec_mulVec]

theorem ltr_apply_zero (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) : ltr A F 0 = F 0 := by
  simp [ltr]

theorem continuousOn_thetaC {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι))
    {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) : ContinuousOn (thetaC F) C := by
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF hC
  refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hb h hh ξ
  refine (continuous_of_mem_schwartzBruhatPi hF).comp ?_
  exact Units.continuous_val.matrix_mulVec continuous_const

theorem continuous_char (ω : HeckeCharacter k) :
    Continuous fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ) :=
  continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_subtype_val)

theorem integrableOn_thetaCIntegrand {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι))
    (A : GL ι 𝔸[k]) (ω : HeckeCharacter k) (s : IdeleGroup k) :
    IntegrableOn (fun u : normOneSubgroup k ↦
      thetaC (ltr A F) (scalC (s * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have hφ : Continuous fun u : normOneSubgroup k ↦
      A * (scalC (s * (u : IdeleGroup k)) : GL ι 𝔸[k]) :=
    continuous_const.mul (continuous_scalC.comp (continuous_const.mul continuous_subtype_val))
  have h1 : ContinuousOn (fun u : normOneSubgroup k ↦
      thetaC (ltr A F) (scalC (s * (u : IdeleGroup k))))
      (closure (normOneFundamentalDomain k)) := by
    simp only [thetaC_ltr]
    exact (continuousOn_thetaC hF (hE.image hφ)).comp hφ.continuousOn (Set.mapsTo_image _ _)
  exact ((h1.mul (continuous_char ω).continuousOn).integrableOn_compact hE).mono_set subset_closure

theorem integrableOn_char' (ω : HeckeCharacter k) :
    IntegrableOn (fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) :=
  ((continuous_char ω).continuousOn.integrableOn_compact
    (isCompact_closure_normOneFundamentalDomain k)).mono_set subset_closure

theorem thetaCInt_ltr_sub_thetaCConst (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (A : GL ι 𝔸[k]) (ω : HeckeCharacter k)
    (t : {r : ℝ // 0 < r}) :
    thetaCInt w (ltr A F) ω t - thetaCConst (ltr A F) ω =
      ∫ u in normOneFundamentalDomain k,
        (thetaC (ltr A F) (scalC (moduleSection w t * (u : IdeleGroup k))) - ltr A F 0) *
          (ω.toIdele (u : IdeleGroup k) : ℂ) ∂normOneMeasure k := by
  rw [thetaCInt, thetaCConst, volChar, ← integral_const_mul,
    ← integral_sub (integrableOn_thetaCIntegrand hF A ω _) ((integrableOn_char' ω).const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  simp only []
  ring

end ThcInt


open ThcInt in
theorem exists_norm_thetaCInt_sub_le (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) {C : Set (GL ι 𝔸[k])}
    (hC : IsCompact C) (r : ℕ) :
    ∃ M : ℝ, ∀ A ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖thetaCInt w (ltr A Ψ) ω t - thetaCConst (ltr A Ψ) ω‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have hS : Continuous fun p : normOneSubgroup k × GL ι 𝔸[k] ↦
      p.2 * (scalC (p.1 : IdeleGroup k) : GL ι 𝔸[k]) :=
    continuous_snd.mul (continuous_scalC.comp (continuous_subtype_val.comp continuous_fst))
  obtain ⟨M, hM⟩ := GlobalTheory.T.theta_sub_value_zero_rapid_decay w hΨ ((hE.prod hC).image hS) r
  refine ⟨M * (normOneMeasure k).real (normOneFundamentalDomain k), fun A hA t ht ↦ ?_⟩
  rw [thetaCInt_ltr_sub_thetaCConst w hΨ A ω t, ← mul_assoc]
  refine norm_setIntegral_le_of_norm_le_const (normOneMeasure_normOneFundamentalDomain_lt_top k)
    fun u hu ↦ ?_
  have hc : A * (scalC (moduleSection w t * (u : IdeleGroup k)) : GL ι 𝔸[k]) =
      scalC (moduleSection w t) * (A * scalC (u : IdeleGroup k)) := by
    rw [scalC_mul, ← mul_assoc, ← mul_assoc, scalC_commute]
  rw [norm_mul, Circle.norm_coe, mul_one, thetaC_ltr, ltr_apply_zero, hc]
  exact hM _ ⟨(u, A), ⟨subset_closure hu, hA⟩, rfl⟩ t ht

end GlobalTheory.CompanionTheory.AdelicThetaSeries
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.crystalline_filtration_saturated : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0), (l : A.Acr0) * z ∈ A.Fil0 r → z ∈ A.Fil0 r := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated | exact GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated | (intros; apply GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated <;> assumption)
end

section


theorem _root_.GlobalTheory.T.kernel_localization : PositivityTheory.RgBcC.Fc.KerLoc := by
  first | exact @GlobalTheory.CompanionTheory.WaveLoc.kerLoc | exact GlobalTheory.CompanionTheory.WaveLoc.kerLoc | (intros; apply GlobalTheory.CompanionTheory.WaveLoc.kerLoc <;> assumption)
end
