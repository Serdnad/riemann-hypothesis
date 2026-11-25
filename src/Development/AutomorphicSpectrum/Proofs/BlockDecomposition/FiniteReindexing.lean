module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteEulerProductOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.SecReindex

open PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_under (v : PlF E) : ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  apply _root_.GlobalTheory.CompanionTheory.EulerAsm.exists_above <;> assumption

def secEquiv {S : Set (Pl E)} (hS : IsSection S) : S ≃ PlF E :=
  Equiv.ofBijective (fun w => w.1.under (𝓞 (maximalRealSubfield E))) (by
    constructor
    · rintro ⟨u, hu⟩ ⟨u', hu'⟩ h
      exact Subtype.ext ((hS u).unique ⟨hu, rfl⟩ ⟨hu', h.symm⟩)
    · intro v
      obtain ⟨w, rfl⟩ := exists_under v
      obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS w
      exact ⟨⟨u, hu⟩, huw⟩)

theorem secPl_eq {S : Set (Pl E)} (hS : IsSection S) (u : S) :
    secPl S (secEquiv hS u) = some u.1 := by
  have hv : secEquiv hS u = u.1.under (𝓞 (maximalRealSubfield E)) := rfl
  have h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = secEquiv hS u := ⟨u.1, u.2, hv.symm⟩
  rw [secPl, dite_eq_left h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  exact congrArg some ((hS u.1).unique ⟨h1, h2.trans hv⟩ ⟨u.2, rfl⟩)

theorem reindex : Reindex := by
  intro E _ _ _ S hS g
  rw [show (∏ᶠ (w : Pl E) (_ : w ∈ S), g w) = ∏ᶠ u : S, g u from
    (finprod_set_coe_eq_finprod_mem S).symm]
  exact finprod_eq_of_bijective (secEquiv hS) (secEquiv hS).bijective
    (fun u => by rw [secPl_eq hS u] <;> rfl)

end GlobalTheory.CompanionTheory.SecReindex

end
