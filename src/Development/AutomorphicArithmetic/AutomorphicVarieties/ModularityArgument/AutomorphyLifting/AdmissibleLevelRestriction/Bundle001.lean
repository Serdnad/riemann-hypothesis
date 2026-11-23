module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN.V UpperTheory.V.Z.Win

namespace UpperTheory.V.Z.Win.A4

section
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ}

private theorem place_under {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 ℚ)) := fun x => by
  rw [IsScalarTower.algebraMap_apply ℚ K Ω]
  exact h (algebraMap (𝓞 ℚ) (𝓞 K) x)

private theorem exists_over (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 ℚ) = v := by
  haveI := v.isMaximal
  have hker : RingHom.ker (algebraMap (𝓞 ℚ) (𝓞 K)) ≤ v.asIdeal := by
    rw [RingOfIntegers.ker_algebraMap_eq_bot]
    exact bot_le
  obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) v.asIdeal hker
  refine ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, ?_⟩
  exact HeightOneSpectrum.ext hc

private def resD (A : ValuationSubring Ω) : ↥(Dec (F := K) A) →* ↥(Dec (F := ℚ) A) where
  toFun u := ⟨(AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω) u, u.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

private theorem resD_surj {A : ValuationSubring Ω}
    (h : ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) (s : ↥(Dec (F := ℚ) A)) :
    ∃ u : ↥(Dec (F := K) A), resD A u = s := by
  let t : G K Ω := { (s : G ℚ Ω).toRingEquiv with commutes' := h s s.2 }
  have ht : (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω) t = s := by
    ext x
    rfl
  have hm : t ∈ Dec (F := K) A := by
    have := s.2
    rw [← ht] at this
    exact this
  exact ⟨⟨t, hm⟩, Subtype.ext ht⟩

private theorem unl_res (r : G ℚ Ω →* GL (Fin n) (Qbar l))
    (hK : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A, ∀ x : K,
      g (algebraMap K Ω x) = algebraMap K Ω x)
    (hU : UnlAll r) (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    Unl1 (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) w := by
  intro A hA
  have hl : A.valuation (l : Ω) < 1 := by
    have h := (hA (l : 𝓞 K)).2 hw
    change A.valuation (algebraMap K Ω (l : K)) < 1 at h
    rwa [map_natCast] at h
  have hv : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := Ideal.mem_comap.2 (by simpa using hw)
  obtain ⟨κ, ⟨g, hg⟩, hne⟩ := hU (w.under (𝓞 ℚ)) hv A (place_under hA)
  refine ⟨fun i => (κ i).comp (resD A), ⟨g, fun u => hg (resD A u)⟩, fun i j e => hne i j ?_⟩
  refine MonoidHom.ext fun s => ?_
  obtain ⟨u, rfl⟩ := resD_surj (hK A hl) s
  exact DFunLike.congr_fun e u

end

theorem potQ :
    FlagLaws → SplitIrr → PotQ := by
  intro hF hS Ω _ _ _ l _ ι n r hc hirr haut hU v hv
  obtain ⟨K, _, _, _, _, _, hrank, hK, hdec⟩ := hS Ω l n r hirr
  have hflag : Flagged r := fun u hu A hA => (hU u hu A hA).imp fun κ h => h.1
  obtain ⟨w, rfl⟩ := exists_over K v
  have hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by simpa using Ideal.mem_comap.1 hv
  have hpot := (haut hc K hrank hK).2.1 w hw (unl_res r hdec hU w hw)
  obtain ⟨-, -, -, hlast⟩ := hF ℚ Ω l n r
  exact (((hlast K).2.2 w hw).2 hflag).1 hpot

end UpperTheory.V.Z.Win.A4
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.GalN.V
open UpperTheory.V UpperTheory.V.Z.Win
open scoped Pointwise

namespace UpperTheory.V.Z.Win.A4

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

private def conjDec (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) :
    ↥(Dec (F := F) B) →* ↥(Dec (F := F) A) where
  toFun u := ⟨γ⁻¹ * u * γ, by
    have hu := mem_Dec.1 u.2
    rw [mem_Dec, mul_smul, mul_smul, h, hu, ← h, inv_smul_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem conjDec_coe (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) (u : ↥(Dec (F := F) B)) :
    ((conjDec A B γ h u : ↥(Dec (F := F) A)) : G F Ω) = γ⁻¹ * u * γ := rfl

private theorem conjDec_surj (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) (s : ↥(Dec (F := F) A)) :
    ∃ u, conjDec A B γ h u = s := by
  refine ⟨⟨γ * s * γ⁻¹, ?_⟩, ?_⟩
  · rw [mem_Dec, ← h, mul_smul, mul_smul, inv_smul_smul, mem_Dec.1 s.2]
  · apply Subtype.ext
    rw [conjDec_coe]
    simp [mul_assoc]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (f : Γ →* C) (γ s : Γ) :
    f (γ⁻¹ * s * γ) = f s := by
  rw [map_mul, map_mul, map_inv, mul_comm (f γ)⁻¹ (f s), inv_mul_cancel_right]

private theorem flag_conj {r : G F Ω →* GL (Fin n) (Qbar l)} {A B : ValuationSubring Ω} {γ : G F Ω} (h : γ • A = B)
    {κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ} (hκ : IsFlagOn r (Dec (F := F) A) κ) :
    IsFlagOn r (Dec (F := F) B) fun i => (κ i).comp (conjDec A B γ h) := by
  obtain ⟨g, hg⟩ := hκ
  refine ⟨g * r γ⁻¹, fun u => ?_⟩
  have key : g * r γ⁻¹ * r ↑u * (g * r γ⁻¹)⁻¹ = g * r ↑(conjDec A B γ h u) * g⁻¹ := by
    rw [conjDec_coe, map_mul, map_mul, map_inv]
    group
  rw [key]
  exact hg (conjDec A B γ h u)

end UpperTheory.V.Z.Win.A4

open UpperTheory.V.Z.Win.A4 in
theorem UpperTheory.V.Z.Win.A4.unlOfOne :
    UnlOfOne := by
  intro F Ω _ _ _ _ _ l _ n r v A hA κ hκ hne B hB
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hA hB
  refine ⟨fun i => (κ i).comp (conjDec A B γ hγ), flag_conj hγ hκ, fun i j e => hne i j ?_⟩
  refine MonoidHom.ext fun s => ?_
  obtain ⟨u, rfl⟩ := conjDec_surj A B γ hγ s
  have e1 := DFunLike.congr_fun e u
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at e1 ⊢
  rw [e1, conjDec_coe, char_conj]
end
end
