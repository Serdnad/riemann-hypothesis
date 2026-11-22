import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PtrScalar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PartialTrace
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Helpers
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tpsc_single_mem {S : Submodule ℂ M} {x : M} (hx : x ∈ S) (c : Fin n) :
    (Pi.single c x : Fin n → M) ∈ tensSub S := by
  exact ReciprocityTheory.ChartRestriction.DS.tpsc_single_mem hx c

theorem tpsc_coord_mem {S : Submodule ℂ M} {f : Fin n → M} (hf : f ∈ tensSub S) (c : Fin n) : f c ∈ S :=
  Submodule.mem_pi.1 hf c (Set.mem_univ _)

theorem tpsc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensV E a b (Pi.single c x) = Pi.single c (E a b x) + if b = c then Pi.single a x else 0 := by
  exact ReciprocityTheory.ChartRestriction.DS.tpsc_tensV_single E a b c x

theorem tpsc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensVd E a b (Pi.single c x) = Pi.single c (E a b x) - if a = c then Pi.single b x else 0 := by
  exact ReciprocityTheory.ChartRestriction.DS.tpsc_tensVd_single E a b c x

end Helpers

def tpscK (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ := cond dual (star (k c d)) (k c d)

theorem tpscK_rows {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (c c' : Fin n) : ∑ d, tpscK dual k c' d * star (tpscK dual k c d) = if c' = c then 1 else 0 := by
  exact ReciprocityTheory.ChartRestriction.DS.tpscK_rows hk dual c c'

theorem tpscK_cols {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (e d : Fin n) : ∑ c, tpscK dual k c d * star (tpscK dual k c e) = if e = d then 1 else 0 := by
  exact ReciprocityTheory.ChartRestriction.DS.tpscK_cols hk dual e d

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D} {A : Module.End ℂ (Fin n → D)}

theorem ptr_mem {dual : Bool} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ x ∈ genSub E V, ptr A x ∈ genSub E V := by
  exact ReciprocityTheory.ChartRestriction.DS.ptr_mem hA

theorem ptr_comm {dual : Bool} (hE : IsGlRep E) (hA : IsGKEndo dual ε σ E (genSub E V) A) (a b : Fin n) :
    ∀ x ∈ genSub E V, ptr A (E a b x) = E a b (ptr A x) := by
  exact ReciprocityTheory.ChartRestriction.DS.ptr_comm hE hA a b

theorem tpsc_kDiag (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) (c : Fin n) :
    kDiag dual σ k f c = ∑ d, tpscK dual k c d • σ k (f d) := rfl

theorem ptr_kcomm {dual : Bool} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, (y : H) = σ k (x : H) →
      ((ptr A y : D) : H) = σ k ((ptr A x : D) : H) := by
  exact ReciprocityTheory.ChartRestriction.DS.ptr_kcomm hσ hD hA

end

theorem ptr_scalar (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∃ c : ℂ, ∀ x ∈ genSub E V, ptr A x = c • x :=
  data_end_scalar hgap hσ hD hV hc hVK (ptr A) (ptr_mem hA) (fun a b => ptr_comm hD.glRep hA a b)
    (ptr_kcomm hσ hD hA)

end ReciprocityTheory.ChartRestriction.DS.G2
