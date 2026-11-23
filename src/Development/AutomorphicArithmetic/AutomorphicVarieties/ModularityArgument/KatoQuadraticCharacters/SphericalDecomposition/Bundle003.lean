module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
open scoped Pointwise

section Res

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra ℚ K] [Algebra K Ω] [IsScalarTower ℚ K Ω]

private abbrev rs : G K Ω →* G ℚ Ω := AlgEquiv.restrictScalarsHom ℚ

private theorem rs_smul (s : G K Ω) (A : ValuationSubring Ω) : (rs s : G ℚ Ω) • A = s • A := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

private theorem rs_mem_Dec {s : G K Ω} {A : ValuationSubring Ω} :
    (rs s : G ℚ Ω) ∈ Dec (F := ℚ) A ↔ s ∈ Dec (F := K) A := by
  rw [mem_Dec, mem_Dec, rs_smul]

private theorem rs_mem_Ine {s : G K Ω} {A : ValuationSubring Ω} (hs : s ∈ Ine (F := K) A) :
    (rs s : G ℚ Ω) ∈ Ine (F := ℚ) A :=
  ⟨rs_mem_Dec.2 hs.1, hs.2⟩

private theorem isFrob_of_rs {s : G K Ω} {A : ValuationSubring Ω} {q : ℕ} (hs : IsFrob A q (rs s : G ℚ Ω)) :
    IsFrob A q s :=
  ⟨rs_mem_Dec.1 hs.1, hs.2⟩

private theorem exists_rs (σ : G ℚ Ω) (h : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x) :
    ∃ s : G K Ω, rs s = σ :=
  ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) h, AlgEquiv.ext fun _ => rfl⟩

private theorem cycBar_rs (l : ℕ) [Fact l.Prime] (s : G K Ω) : cycBar ℚ Ω l (rs s) = cycBar K Ω l s := by
  have h : MulSemiringAction.toRingAut (G ℚ Ω) Ω (rs s) = MulSemiringAction.toRingAut (G K Ω) Ω s :=
    RingEquiv.ext fun _ => rfl
  simp only [cycBar, cycZ, MonoidHom.comp_apply, h]

private def resDec (A : ValuationSubring Ω) : ↥(Dec (F := K) A) →* ↥(Dec (F := ℚ) A) :=
  (rs.comp (Dec (F := K) A).subtype).codRestrict (Dec (F := ℚ) A) fun s => rs_mem_Dec.2 s.2

private theorem exact_res {l : ℕ} [Fact l.Prime] {e : ℕ} {V : G ℚ Ω →* GL (Fin 2) (Qbar l)}
    {A : ValuationSubring Ω} {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ} (h : Exact e V A κ) :
    Exact e (V.comp (rs : G K Ω →* G ℚ Ω)) A fun i => (κ i).comp (resDec A) := by
  obtain ⟨⟨g, hg⟩, hI⟩ := h
  refine ⟨⟨g, fun s => hg (resDec A s)⟩, fun s hs => ?_⟩
  have h2 := hI (resDec A s) (rs_mem_Ine hs)
  have h3 : cycBar ℚ Ω l ((resDec A s : ↥(Dec (F := ℚ) A)) : G ℚ Ω) = cycBar K Ω l s := cycBar_rs l (s : G K Ω)
  rw [h3] at h2
  exact h2

private theorem frobIn_res {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {e q : ℕ} {A : ValuationSubring Ω}
    {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ} {B : Multiset ℂˣ}
    (hfix : ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x)
    (h : FrobIn ι e q A (fun i => (κ i).comp (resDec (K := K) A)) B) : FrobIn ι e q A κ B := by
  intro σ hσ
  obtain ⟨s, hs⟩ := exists_rs (K := K) (σ : G ℚ Ω) (hfix _ σ.2)
  have hd : s ∈ Dec (F := K) A := rs_mem_Dec.1 (hs ▸ σ.2)
  have hr : resDec A (⟨s, hd⟩ : ↥(Dec (F := K) A)) = σ := Subtype.ext hs
  obtain ⟨b, hb, he⟩ := h ⟨s, hd⟩ (isFrob_of_rs (by rw [hs]; exact hσ))
  refine ⟨b, hb, ?_⟩
  have h3 : cycBar ℚ Ω l (σ : G ℚ Ω) = cycBar K Ω l s := by rw [← hs]; exact cycBar_rs l s
  rw [h3]
  have h4 : ((κ 0).comp (resDec (K := K) A)) ⟨s, hd⟩ = κ 0 σ := by
    rw [MonoidHom.comp_apply, hr]
  rw [← h4]
  exact he

end Res

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.locQ :
    PlainRec → PlainOf → RecTExists → BcSplit → PotOf → LocK → LocQ := by
  intro hPR hPO hRT hBC hPot hLK l _ hl2 Ω _ _ _ ι e he V π hc hirr hM hreg hatt v A κ hlv hA hE hor
  obtain ⟨K, _, _, _, _, _, _, P, w, hfr, hirrK, hregP, hpol, hattP, hAw, hlw, hnorm, hfix, hsat⟩ :=
    hBC l hl2 Ω ι V π hc hirr hM hreg hatt v A hlv hA
  have hEx := exact_res (K := K) hE
  have hcK : Continuous (V.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) :=
    hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom _ _ _)
  have hWP : PlainAt P w := by
    rcases hor with hW | ⟨B, hB⟩
    · have hWA := hW K hfr hirrK
      obtain ⟨rc, hrc⟩ := hRT K Ω A w hAw
      have hpu := hPot K Ω l e he _ w A _ hlw hAw hEx
      intro σ hσ
      exact (guard_of hPR hregP hattP hWA (Or.inr (Or.inr hpu)) hrc hσ).1
    · exact (hPO K 2 (by norm_num) P w).2 ⟨B, (hsat B).1 hB⟩
  obtain ⟨⟨B₀, hB₀⟩, hF⟩ := hLK K Ω l hl2 ι e he _ P hcK hregP hpol hattP w A _ hlw hAw hEx hWP
  refine ⟨⟨B₀, (hsat B₀).2 hB₀⟩, fun B hB => ?_⟩
  have h := hF B ((hsat B).1 hB)
  rw [hnorm] at h
  exact frobIn_res hfix h
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
open scoped Pointwise

private theorem gap_pow {C : Type} [CommGroup C] (x : C) (a b : ℤ) (m : ℕ)
    (h : (x ^ a) ^ m = (x ^ b * x) ^ m) : x ^ ((m : ℤ) * (a - b - 1)) = 1 := by
  have h' : x ^ (a * m) = x ^ ((b + 1) * m) := by
    rw [zpow_mul, zpow_mul, zpow_add_one, zpow_natCast, zpow_natCast, h]
  have hc : (m : ℤ) * (a - b - 1) = a * m - (b + 1) * m := by ring
  rw [hc, zpow_sub, h', mul_inv_cancel]

private theorem exp_ne (e : ℕ) (he : 1 ≤ e) (m : ℕ) (hm : 1 ≤ m) (i j : Fin 2) :
    (m : ℤ) * ((![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i - (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) j - 1) ≠ 0 := by
  refine mul_ne_zero (by exact_mod_cast (by omega : m ≠ 0)) ?_
  fin_cases i <;> fin_cases j <;> simp <;> omega

private def decConj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) :
    ↥(Dec (F := F) B) →* ↥(Dec (F := F) A) where
  toFun u := ⟨γ⁻¹ * u * γ, by
    have hu := mem_Dec.1 u.2
    rw [mem_Dec, mul_smul, mul_smul, h, hu, ← h, inv_smul_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.potOf :
    PotOf := by
  intro F Ω _ _ _ _ _ l _ e he r w A κ hl hA hE
  obtain ⟨⟨g, hg⟩, hI⟩ := hE
  have hvA : A.valuation (l : Ω) < 1 := by
    have h1 := (hA (l : 𝓞 F)).2 hl
    change A.valuation (algebraMap F Ω (l : F)) < 1 at h1
    rwa [map_natCast] at h1
  have hv : ∀ (t : Dec (F := F) A), (t : G F Ω) ∈ Ine A → ∀ i : Fin 2,
      κ i t = cycBar F Ω l ↑t ^ ((![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i) := by
    intro t ht i
    fin_cases i
    · exact (hI t ht).1
    · exact (hI t ht).2
  intro A' hA'
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hA'
  refine ⟨fun i => (κ i).comp (decConj A A' σ hσ), ?_, ?_⟩
  · refine ⟨g * r σ⁻¹, fun s => ?_⟩
    have hc : ((decConj A A' σ hσ s : Dec (F := F) A) : G F Ω) = σ⁻¹ * ↑s * σ := rfl
    have key : g * r σ⁻¹ * r ↑s * (g * r σ⁻¹)⁻¹ = g * r ↑(decConj A A' σ hσ s) * g⁻¹ := by
      rw [hc, map_mul, map_mul, map_inv]
      group
    rw [key]
    exact hg _
  · intro i j m hm heq
    obtain ⟨g0, hg0, hn⟩ := Ws.Pt.cycIne F Ω l A hvA _ (exp_ne e he m hm i j)
    have hA'σ : σ⁻¹ • A' = A := by rw [← hσ, inv_smul_smul]
    have hg1 : σ * g0 * σ⁻¹ ∈ Ine A' := by
      have h2 := (Two.ineConj F Ω σ⁻¹).1 A' g0 (by rw [hA'σ]; exact hg0)
      rwa [inv_inv] at h2
    have ht : decConj A A' σ hσ ⟨σ * g0 * σ⁻¹, Ine_le_Dec A' hg1⟩ = ⟨g0, Ine_le_Dec A hg0⟩ :=
      Subtype.ext (by
        show σ⁻¹ * (σ * g0 * σ⁻¹) * σ = g0
        group)
    have hcyc : cycBar F Ω l (σ * g0 * σ⁻¹) = cycBar F Ω l g0 := by
      rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    have h3 := DFunLike.congr_fun heq ⟨σ * g0 * σ⁻¹, Ine_le_Dec A' hg1⟩
    simp only [MonoidHom.pow_apply, MonoidHom.mul_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype] at h3
    rw [ht, hv _ hg0 i, hv _ hg0 j, hcyc] at h3
    exact hn (gap_pow (cycBar F Ω l g0) _ _ m h3)
end
