module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitIdem

theorem idem_alg {T : Type} [CommRing T] (p U R w m : T) (hU : p * U = U) (hR : R * R - R + m * p = 0)
    (hδ : U - 2 * (U * R) = p) (hw : w * w - w + m = 0) :
    (U * w - U * R) * (U * w - U * R) = U * w - U * R ∧
      (U * w - U * R) * (U * (1 - w) - U * R) = 0 ∧
      (U * w - U * R) + (U * (1 - w) - U * R) = p := by
  have h2 : (U * w - U * R) * (U * (1 - w) - U * R) = 0 := by
    linear_combination U * U * hR - U * U * hw - m * U * hU
  refine ⟨?_, h2, by linear_combination hδ⟩
  linear_combination (U * w - U * R) * hδ - h2 + (w - R) * hU

theorem idem_tensor {F A E K : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E]
    [CommRing K] (φ : K →ₙ+* A) (c : A ⊗[F] E →+* A ⊗[F] E) (ω : E) (m : ℕ) (r u : K)
    (hc1 : ∀ a : A, c (a ⊗ₜ 1) = a ⊗ₜ 1) (hcω : ∀ a : A, c (a ⊗ₜ ω) = a ⊗ₜ (1 - ω))
    (hω : ω * ω - ω + m = 0) (hr : r * r - r + m = 0) (hu : u * (1 - 2 * r) = 1)
    (e : A ⊗[F] E) (he : e = φ u ⊗ₜ ω + φ (-(u * r)) ⊗ₜ 1) :
    e * e = e ∧ e * c e = 0 ∧ e + c e = algebraMap A (A ⊗[F] E) (φ 1) := by
  let j : A →+* A ⊗[F] E := algebraMap A _
  let k : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E)
  have hjk : ∀ a x, a ⊗ₜ[F] x = j a * k x := fun a x => by
    simp [j, k, Algebra.TensorProduct.tmul_mul_tmul]
  have h1 : e = j (φ u) * k ω - j (φ u) * j (φ r) := by
    rw [he, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  have h2 : c e = j (φ u) * (1 - k ω) - j (φ u) * j (φ r) := by
    rw [he, map_add (f := _), hc1, hcω, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one, map_sub, map_one]; ring
  rw [h2, h1]
  refine idem_alg (j (φ 1)) _ _ _ (m : A ⊗[F] E) ?_ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, one_mul]
  · have : φ r * φ r - φ r + m * φ 1 = 0 := by
      rw [← nsmul_eq_mul, ← map_nsmul, ← map_mul, ← map_sub, ← map_add (f := _), nsmul_eq_mul, mul_one, hr, map_zero]
    simpa using congrArg j this
  · have : φ u - 2 * (φ u * φ r) = φ 1 := by
      rw [two_mul, ← map_mul, ← map_add (f := _), ← map_sub, ← hu]; congr 1; ring
    have h := congrArg j this
    rwa [map_sub, map_mul, map_mul, map_ofNat] at h
  · have h := congrArg k hω
    rwa [map_add, map_sub, map_mul, map_natCast, map_zero] at h

section Local

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem evalV_singleV_same (y : Fv F v) : evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_singleV_ne (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem af_ext {a b : Af F} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  RestrictedProduct.ext _ _ h

def placeHom : Fv F v →ₙ+* AF F where
  toFun y := pairA F 0 (singleV F v y)
  map_zero' := Prod.ext rfl (af_ext F fun w => by
    change evalV F w (singleV F v 0) = evalV F w 0
    by_cases hw : w = v
    · subst hw; rw [evalV_singleV_same, map_zero]
    · rw [evalV_singleV_ne F v _ hw, map_zero])
  map_add' x y := Prod.ext (add_zero _).symm (af_ext F fun w => by
    change evalV F w (singleV F v (x + y)) = evalV F w (singleV F v x + singleV F v y)
    by_cases hw : w = v
    · subst hw; simp only [map_add (f := _), evalV_singleV_same]
    · simp only [map_add (f := _), evalV_singleV_ne F v _ hw, add_zero])
  map_mul' x y := Prod.ext (mul_zero _).symm (af_ext F fun w => by
    change evalV F w (singleV F v (x * y)) = evalV F w (singleV F v x * singleV F v y)
    by_cases hw : w = v
    · subst hw; simp only [map_mul, evalV_singleV_same]
    · simp only [map_mul, evalV_singleV_ne F v _ hw, mul_zero])

theorem singleV_mem_intAf (y : v.adicCompletionIntegers F) : singleV F v (y : Fv F v) ∈ intAf F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_singleV_same]; exact y.2
  · rw [evalV_singleV_ne F v _ hw]; exact zero_mem _

theorem exists_root (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (k : ℕ) :
    ∃ r u : v.adicCompletionIntegers F, r * r - r + ((2 * k : ℕ) : v.adicCompletionIntegers F) = 0 ∧
      u * (1 - 2 * r) = 1 := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : (2 : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      ← map_ofNat (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) 2, GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
    exact fun h => h h2
  obtain ⟨r, hr, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k : ℕ) : v.adicCompletionIntegers F)) (by monicity!) 0
    (by simpa using Ideal.mul_mem_right _ _ hm) (by simp)
  have hunit : IsUnit (1 - 2 * r) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right r _ hm)
  obtain ⟨u, hu⟩ := hunit.exists_left_inv
  refine ⟨r, u, ?_, hu⟩
  simpa [Polynomial.IsRoot, pow_two] using hr

end Local

theorem exists_omega (D : D7) : ∃ (ω : 𝓞 D.host.E) (k : ℕ),
    (ω : D.host.E) * ω - ω + ((2 * k : ℕ) : D.host.E) = 0 ∧ D.host.conj ω = 1 - ω := by
  obtain ⟨k, hm⟩ : ∃ k : ℕ, D.host.d + 1 = 4 * (2 * k) := ⟨(D.host.d + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  generalize hmm : 2 * k = m at hm
  set c : D.host.E := (1 + D.host.sqrtMinusD) / 2
  have hc : c ^ 2 - c + (m : D.host.E) = 0 := by
    have e : ((D.host.d : ℕ) : D.host.E) + 1 = 4 * (m : D.host.E) := by exact_mod_cast hm
    have hs := D.host.sqrtMinusD_sq
    simp only [c]
    linear_combination (1 / 4 : D.host.E) * hs - (1 / 4 : D.host.E) * e
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  refine ⟨⟨c, hint⟩, k, ?_, ?_⟩
  · show c * c - c + _ = 0
    rw [hmm, ← pow_two, hc]
  · show D.host.conj c = 1 - c
    simp only [c, map_div₀, map_add (f := _), map_one, D.host.conj_sqrtMinusD, map_ofNat]
    ring

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := D.host.conjE_apply _ _
  rw [h1]
  haveI := D.host.isCMField_hostE
  exact IsCMField.complexEmbedding_complexConj _ _ _

theorem exists_split_idempotent : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (2 : 𝓞 D.host.F) ∈ v.asIdeal → ∃ e : Formalism.L2.Theta.AE D, e * e = e ∧ e * cA D e = 0 ∧ e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) ∧ ∃ α ∈ intAf D.host.F, ∃ β ∈ intAf D.host.F, ∃ ω : 𝓞 D.host.E, e = pairA D.host.F 0 α ⊗ₜ[D.host.F] (ω : D.host.E) + pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E) := by
  intro D v h2
  obtain ⟨ω, k, hω, hc⟩ := exists_omega D
  obtain ⟨r, u, hr, hu⟩ := exists_root D.host.F v h2 k
  have hcA : ∀ (a : AF D.host.F) (x : D.host.E), cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x := fun _ _ => rfl
  have key := idem_tensor (placeHom D.host.F v) (cA D) (ω : D.host.E) (2 * k) (r : Fv D.host.F v) (u : Fv D.host.F v)
    (fun a => by rw [hcA, star_one]) (fun a => by rw [hcA, star_eq_conj, hc]) hω
    (congrArg Subtype.val hr) (congrArg Subtype.val hu) _ rfl
  exact ⟨_, key.1, key.2.1, key.2.2, _, singleV_mem_intAf D.host.F v u, _,
    singleV_mem_intAf D.host.F v (-(u * r)), ω, rfl⟩

end GlobalTheory.SplitIdem

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVac

theorem evalV_singleV_same (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (singleV F v 1) = 1 := by
  classical
  exact RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1

theorem evalV_singleV_ne (F : Type) [Field F] [NumberField F] (v v' : HeightOneSpectrum (𝓞 F))
    (h : v' ≠ v) : evalV F v' (singleV F v 1) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h

theorem half_mem_adicCompletionIntegers (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (h : (2 : 𝓞 F) ∉ v.asIdeal) : algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  rw [h2, map_inv₀, h1, inv_one]

theorem one_eq_sum_singleV_add_two_mul : ∀ (F : Type) [Field F] [NumberField F], ∃ P : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ P, (2 : 𝓞 F) ∈ v.asIdeal) ∧ (∀ v : HeightOneSpectrum (𝓞 F), singleV F v 1 ∈ intAf F ∧ evalV F v (singleV F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV F v' (singleV F v 1) = 0) ∧ ∃ β ∈ intAf F, (1 : Af F) = ∑ v ∈ P, singleV F v 1 + 2 * β := by
  intro F _ _
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {(2 : 𝓞 F)}) (by simp)
    refine h.subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  refine ⟨hfin.toFinset, fun v hv => by simpa using hv, fun v => ⟨fun w => ?_, evalV_singleV_same F v,
    evalV_singleV_ne F v⟩, algebraMap F (Af F) (2 : F)⁻¹ * (1 - ∑ v ∈ hfin.toFinset, singleV F v 1),
    fun w => ?_, ?_⟩
  · by_cases hw : w = v
    · subst hw
      rw [evalV_singleV_same]; exact one_mem _
    · rw [evalV_singleV_ne F v w hw]; exact zero_mem _
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sub, map_one, map_sum, AlgHom.commutes]
    by_cases hw : w ∈ hfin.toFinset
    · rw [Finset.sum_eq_single_of_mem w hw fun b _ hb => evalV_singleV_ne F b w hb.symm,
        evalV_singleV_same, sub_self, mul_zero]
      exact zero_mem _
    · rw [Finset.sum_eq_zero fun b hb => evalV_singleV_ne F b w fun h => hw (h ▸ hb), sub_zero, mul_one]
      exact half_mem_adicCompletionIntegers F w (by simpa using hw)
  · have h2 : (2 : Af F) * algebraMap F (Af F) (2 : F)⁻¹ = 1 := by
      rw [← map_ofNat (algebraMap F (Af F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    rw [← mul_assoc, h2, one_mul, add_sub_cancel]

end GlobalTheory.LatVac
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct Topology

namespace GlobalTheory.IntDense

theorem mem_of_isClosed (F : Type) [Field F] [NumberField F] {C : Set (FiniteAdeleRing (𝓞 F) F)}
    (hC : IsClosed C) (h : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ C)
    (α : FiniteAdeleRing (𝓞 F) F) (hα : ∀ v, α v ∈ v.adicCompletionIntegers F) : α ∈ C := by
  by_contra hn
  have hc : Continuous fun y : FiniteAdeleRing (𝓞 F) F => α - y := continuous_const.sub continuous_id
  have hU : (fun y : FiniteAdeleRing (𝓞 F) F => α - y) ⁻¹' Cᶜ ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    (hC.isOpen_compl.preimage hc).mem_nhds (by simpa using hn)
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hU
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 α hα
  refine hNU β hβ ?_
  change α - N • β ∈ C
  rw [e, add_sub_cancel_right]
  exact h a

theorem addChar_eq_one_of_integral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : F, (∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1) → ∀ α ∈ intAf F, ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := by
  intro F _ _ ψ hψ x h α hα
  have hp : Continuous fun y : Af F => pairA F 0 (y * algebraMap F (Af F) x) :=
    Continuous.prodMk continuous_const (continuous_id.mul continuous_const)
  refine mem_of_isClosed F (C := {y | ψ (pairA F 0 (y * algebraMap F (Af F) x)) = 1})
    (isClosed_eq (hψ.comp hp) continuous_const) (fun a => ?_) α hα
  have := h a
  rwa [map_mul] at this

end GlobalTheory.IntDense
end
