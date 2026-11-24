module

import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.GoingDown
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def extC (𝔭 : Ideal (MvPolynomial σ ℚ)) : Ideal (MvPolynomial σ ℂ) :=
  Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭

theorem comap_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := by
  apply ReciprocityTheory.AnForm.R.BaseChangeC.comap_of_mem_minimalPrimes_map <;> assumption

theorem ringKrullDim_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by
  have hQp : Q.IsPrime := hQ.1.1
  have hh := BaseChangeC.height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ
  have h1 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℂ Q
  have h2 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℚ 𝔭
  rw [hh] at h1
  exact BaseChangeC.withBot_enat_cancel h1 h2

end ReciprocityTheory.AnForm.R
