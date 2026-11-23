module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Bundle002
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceC
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd Formalism.L2.Host.CT

private theorem exists_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ M : Subgroup Γ, M.Normal ∧ M.index.Prime := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : M.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ M := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using M.mul_mem h1 hn⟩
  refine ⟨M, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ M)) (mt Subgroup.index_eq_one.1 hM.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) = ⊤ := by
    refine hM.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M g
      have hx : x ∈ M := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective M) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp

private theorem closure_tower (K E Ω : Type) [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [Algebra.IsAlgebraic K E] [IsAlgClosure E Ω] : IsAlgClosure K Ω :=
  { isAlgClosed := IsAlgClosure.isAlgClosed E, isAlgebraic := Algebra.IsAlgebraic.trans K E Ω }

private theorem up_one (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    (h1 : Module.finrank F E = 1) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (ha : IsAutC ι r) (hi : IsIrr (r.comp (galEmb F E Ω))) :
    IsAutC ι (r.comp (galEmb F E Ω)) := by
  obtain ⟨π, hreg, -, hat⟩ := ha
  let j : E ≃+* F := (RingEquiv.ofBijective (algebraMap F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)).symm
  refine ⟨UpperTheory.V.FieldIso.pullSub j π, UpperTheory.V.FieldIso.isRegAlg_pullSub j hreg,
    (UpperTheory.galoisRep_irreducibility_criterion.1 _ (_root_.Formalism.ConjugateSelfDual.G E Ω) _ n _).2.1 hi, ?_⟩
  filter_upwards [(plMap_injective j).tendsto_cofinite.eventually hat] with w hw
  obtain ⟨B, hB, hF⟩ := hw
  have hu : w.under (𝓞 F) = plMap j w := HeightOneSpectrum.ext (Ideal.ext fun x => Iff.rfl)
  have hn : normV w = normV (plMap j w) := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using (absNorm_plMap j w).symm
  refine ⟨B, UpperTheory.V.FieldIso.hasSat_pullSub j hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w 1 (by rw [hu, pow_one, hn])).1 n r _ (hu ▸ hF)
  rw [hn, ← hu]
  simp only [pow_one, Multiset.map_id'] at h3
  exact h3
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Z.Bc

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Places

private theorem infOf_ne {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) : infOf m ≠ infOf m' := by
  intro e
  have h1 : (((2 : ℕ) : ℂ) - 1) / 2 + (m 0 : ℂ) ∈ infOf m := Multiset.mem_map.2 ⟨0, Finset.mem_univ_val _, rfl⟩
  rw [e] at h1
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 h1
  have h2 : m' i = m 0 := Int.cast_injective (add_left_cancel hi)
  fin_cases i
  · exact absurd (@h 2 0 h2) (by decide)
  · exact absurd (@h 3 0 h2) (by decide)

open UpperTheory.CBC UpperTheory.CBC.SConjSpaceCAux in
private theorem not_conjIso {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    [IsGalois K M] (π : CuspSub M 2) (hm : MixWtC K π) : ¬ ∀ σ : M ≃ₐ[K] M, (Cusp.cx π).ConjIso σ.toRingEquiv := by
  intro h
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  obtain ⟨m, m', τ, τ', -, h1, h2, k1, k2, hinj⟩ := hm φ
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := K) τ τ' (h1.trans h2.symm)
  obtain ⟨s, hs⟩ := SGalAdEx_holds M σ.toRingEquiv
  obtain ⟨P', hsp, hiso⟩ := h σ s hs
  obtain ⟨d, hd, hd'⟩ := exists_GD _ s hs
  cases P' with
  | re π' => exact hiso.elim
  | cx π' =>
    have e : τ.comp (d.σ.symm : M →+* M) = τ' := by
      rw [hd']
      exact hσ
    have k3 : π'.HasInfChar τ (infOf m') := by
      refine ⟨k2.1, fun u x hx => ?_⟩
      have hx' : x.1 ∈ (Cusp.cx π').space := ⟨x, hx, rfl⟩
      rw [hsp] at hx'
      obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx'
      obtain rfl : x = pull d 2 y := Subtype.ext (by rw [← hxy, ← hd]; rfl)
      rw [cap_pull, e, k2.2 u y hy, map_smul]
    exact infOf_ne hinj (k1.unique (CuspSub.Iso.hasInfChar hiso k3))
end
