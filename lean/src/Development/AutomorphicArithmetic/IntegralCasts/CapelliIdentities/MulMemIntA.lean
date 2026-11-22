import Mathlib

open scoped TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace UpperTheory.Reformulated.B.Uc13

abbrev Af (F : Type) [inst : Field F] [inst_1 : NumberField F] := FiniteAdeleRing (𝓞 F) F

abbrev Fv (F : Type) [inst : Field F] [inst_1 : NumberField F] (v : HeightOneSpectrum (𝓞 F)) :=
  v.adicCompletion F

theorem aux3 (F : Type) [inst : Field F] [inst_1 : NumberField F] (i : HeightOneSpectrum (𝓞 F)) :
    SubringClass (ValuationSubring (Fv F i)) (Fv F i) := inferInstance

theorem aux4 (F : Type) [inst : Field F] [inst_1 : NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
      (algebraMap F (Af F) x) = algebraMap F (Fv F v) x := rfl

def evalV (F : Type) [inst : Field F] [inst_1 : NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Af F →ₐ[F] Fv F v :=
  { RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v with
    commutes' := aux4 F v }

def intAf (F : Type) [inst : Field F] [inst_1 : NumberField F] : Set (Af F) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}

def intA (F E : Type) [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] :
    AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

private theorem intAf_mul (F : Type) [inst : Field F] [inst_1 : NumberField F] {a b : Af F}
    (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

theorem mul_mem_intA (F E : Type) [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E]
    {x y : Af F ⊗[F] E} (hx : x ∈ intA F E) (hy : y ∈ intA F E) : x * y ∈ intA F E := by
  unfold intA at *
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, s, rfl⟩ := hx
    obtain ⟨b, hb, t, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a * b, intAf_mul F ha hb, s * t, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero_left x hx => rw [zero_mul]; exact zero_mem _
  | zero_right x hx => rw [mul_zero]; exact zero_mem _
  | add_left x y z hx hy hz h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right y z x hy hz hx h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg_left x y hx hy h => rw [neg_mul]; exact neg_mem h
  | neg_right x y hx hy h => rw [mul_neg]; exact neg_mem h

end UpperTheory.Reformulated.B.Uc13
