module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixOfStabilizerTrivial
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LocalEmbedding

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (φ : ↥K →ₐ[ℚ_[l]] ↥L) (y : ↥K) : ‖((φ y : ↥L) : PadicAlgCl l)‖ = ‖(y : PadicAlgCl l)‖ := by
  have h1 : minpoly ℚ_[l] ((φ y : ↥L) : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq (L.val.comp φ) (L.val.comp φ).toRingHom.injective y
  have h2 : minpoly ℚ_[l] (y : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq K.val K.val.toRingHom.injective y
  change spectralNorm ℚ_[l] (PadicAlgCl l) _ = spectralNorm ℚ_[l] (PadicAlgCl l) _
  unfold spectralNorm
  rw [h1, h2]

theorem mem_place_iff (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : 𝓞 D.host.E) :
    x ∈ w.asIdeal ↔ ‖(D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))‖ < 1 := by
  apply _root_.GlobalTheory.TypeDegOne.mem_place_iff <;> assumption

theorem inducesW_and_exists_emb : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (τ : D.host.E →+* Qbar (D.nd.l i)), (∀ x : D.host.E, τ x = ((τ' (Br.cEw D.nbr i w hw x) : ↥LL'.1) : Om (D.nd.l i))) → InducesW D.nd i τ w ∧ ∃ g : D.R.GG, (D.naut.iotaQC i).toRingHom.comp τ = D.host.emb g := by
  intro D i w hw LL' τ' τ h
  refine ⟨fun x => ?_, ?_⟩
  · rw [mem_place_iff D i w hw x, h, norm_algHom τ']
    exact Iff.rfl
  · obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ((D.naut.iotaQC i).toRingHom.comp τ)
    exact ⟨g, hg.symm⟩

end GlobalTheory.LocalEmbedding

end
