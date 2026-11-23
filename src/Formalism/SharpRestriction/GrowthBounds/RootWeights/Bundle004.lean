module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle013
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Mathlib.Data.Int.NatAbs

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section wt
variable {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSp_iff_diagonal_apply (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem linearMap_ext_on_weightSpaces {V' : Type} [AddCommGroup V'] [Module K V'] (E : GLOps n K V) (hE : IsGLRep E)
    (f g : V →ₗ[K] V') (h : ∀ mu, ∀ x ∈ weightSp E mu, f x = g x) : f = g := by
  have hle : (⨆ mu, weightSp E mu) ≤ LinearMap.eqLocus f g := iSup_le fun mu x hx => h mu x hx
  ext x
  have : x ∈ (⨆ mu, weightSp E mu) := by rw [hE.2.2]; trivial
  exact hle this


open Classical in
def lagrangeWeightFactor (E : GLOps n K V) (mu nu : Fin n → ℤ) : Module.End K V :=
  if h : ∃ a, nu a ≠ mu a then
    (((mu h.choose : K) - (nu h.choose : K))⁻¹) • (E h.choose h.choose - (nu h.choose : K) • (1 : Module.End K V))
  else 1

def lagrangeOperator (E : GLOps n K V) (mu : Fin n → ℤ) : List (Fin n → ℤ) → Module.End K V
  | [] => 1
  | nu :: l => lagrangeWeightFactor E mu nu * lagrangeOperator E mu l

theorem lagrangeFactor_acts_by_scalar (E : GLOps n K V) (mu nu ka : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ka) :
    ∃ c : K, lagrangeWeightFactor E mu nu x = c • x := by
  unfold lagrangeWeightFactor
  split_ifs with h
  · refine ⟨((mu h.choose : K) - (nu h.choose : K))⁻¹ * ((ka h.choose : K) - (nu h.choose : K)), ?_⟩
    simp [(mem_weightSp_iff_diagonal_apply E ka x).1 hx, sub_smul, mul_smul, smul_sub]
  · exact ⟨1, by simp⟩

theorem lagrangeFactor_fixes_own_weight [CharZero K] (E : GLOps n K V) (mu nu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    lagrangeWeightFactor E mu nu x = x := by
  unfold lagrangeWeightFactor
  split_ifs with h
  · have hne : ((mu h.choose : K) - (nu h.choose : K)) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast (h.choose_spec).symm
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, (mem_weightSp_iff_diagonal_apply E mu x).1 hx, Module.End.one_apply]
    rw [← sub_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · simp

theorem lagrangeFactor_kills_other_weight (E : GLOps n K V) (mu nu : Fin n → ℤ) (hne : nu ≠ mu) (x : V) (hx : x ∈ weightSp E nu) :
    lagrangeWeightFactor E mu nu x = 0 := by
  have h : ∃ a, nu a ≠ mu a := by
    by_contra hc; exact hne (funext fun a => by_contra fun h => hc ⟨a, h⟩)
  unfold lagrangeWeightFactor
  rw [dite_eq_left h]
  simp [(mem_weightSp_iff_diagonal_apply E nu x).1 hx]

theorem lagrangeFactor_preserves_stable (E : GLOps n K V) (mu nu : Fin n → ℤ) (W : Submodule K V)
    (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W) (x : V) (hx : x ∈ W) : lagrangeWeightFactor E mu nu x ∈ W := by
  unfold lagrangeWeightFactor
  split_ifs with h
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    exact W.smul_mem _ (W.sub_mem (hW _ x hx) (W.smul_mem _ hx))
  · simpa using hx

theorem lagrangeOperator_acts_by_scalar (E : GLOps n K V) (mu ka : Fin n → ℤ) (l : List (Fin n → ℤ)) (x : V)
    (hx : x ∈ weightSp E ka) : ∃ c : K, lagrangeOperator E mu l x = c • x := by
  induction l with
  | nil => exact ⟨1, by simp [lagrangeOperator]⟩
  | cons nu l ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨c', hc'⟩ := lagrangeFactor_acts_by_scalar E mu nu ka x hx
    exact ⟨c * c', by simp [lagrangeOperator, hc, hc', smul_smul]⟩

theorem lagrangeOperator_fixes_own_weight [CharZero K] (E : GLOps n K V) (mu : Fin n → ℤ) (l : List (Fin n → ℤ)) (x : V)
    (hx : x ∈ weightSp E mu) : lagrangeOperator E mu l x = x := by
  induction l with
  | nil => simp [lagrangeOperator]
  | cons nu l ih => simp [lagrangeOperator, ih, lagrangeFactor_fixes_own_weight E mu nu x hx]

theorem lagrangeOperator_kills_listed (E : GLOps n K V) (mu ka : Fin n → ℤ) (hne : ka ≠ mu) (l : List (Fin n → ℤ))
    (hl : ka ∈ l) (x : V) (hx : x ∈ weightSp E ka) : lagrangeOperator E mu l x = 0 := by
  induction l with
  | nil => simp at hl
  | cons nu l ih =>
    obtain ⟨c, hc⟩ := lagrangeOperator_acts_by_scalar E mu ka l x hx
    rcases List.mem_cons.1 hl with h | h
    · subst h
      simp [lagrangeOperator, hc, lagrangeFactor_kills_other_weight E mu ka hne x hx]
    · simp [lagrangeOperator, ih h]

theorem lagrangeOperator_preserves_stable (E : GLOps n K V) (mu : Fin n → ℤ) (l : List (Fin n → ℤ)) (W : Submodule K V)
    (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W) (x : V) (hx : x ∈ W) : lagrangeOperator E mu l x ∈ W := by
  induction l with
  | nil => simpa [lagrangeOperator] using hx
  | cons nu l ih => simpa [lagrangeOperator] using lagrangeFactor_preserves_stable E mu nu W hW _ ih

theorem finitely_many_weights_span [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) :
    ∃ s : Finset (Fin n → ℤ), (⨆ mu ∈ s, weightSp E mu) = ⊤ := by
  have hc : IsCompactElement (⊤ : Submodule K V) :=
    (Submodule.fg_iff_compact _).1 (Module.finite_def.1 inferInstance)
  obtain ⟨s, hs⟩ := IsCompactElement.exists_finset_of_le_iSup hc (weightSp E) (by rw [hE.2.2])
  exact ⟨s, top_le_iff.1 hs⟩

theorem weightSpace_eq_bot_outside_support [CharZero K] (E : GLOps n K V) (s : Finset (Fin n → ℤ))
    (hs : (⨆ mu ∈ s, weightSp E mu) = ⊤) (ka : Fin n → ℤ) (hk : ka ∉ s) : weightSp E ka = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : lagrangeOperator E ka s.toList x = x := lagrangeOperator_fixes_own_weight E ka _ x hx
  have hle : (⨆ mu ∈ s, weightSp E mu) ≤ LinearMap.ker (lagrangeOperator E ka s.toList) := by
    refine iSup₂_le fun mu hmu y hy => ?_
    exact lagrangeOperator_kills_listed E ka mu (fun h => hk (h ▸ hmu)) _ (Finset.mem_toList.2 hmu) y hy
  have h2 : x ∈ (⨆ mu ∈ s, weightSp E mu) := by rw [hs]; trivial
  have h3 := hle h2
  rw [LinearMap.mem_ker, h1] at h3
  simpa using h3

theorem weight_projections_exist [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) :
    ∃ (s : Finset (Fin n → ℤ)) (π : (Fin n → ℤ) → Module.End K V),
      (∀ mu, IsWtProj E mu (π mu)) ∧
      (∀ mu, ∀ W : Submodule K V, (∀ a, ∀ x ∈ W, E a a x ∈ W) → ∀ x ∈ W, π mu x ∈ W) ∧
      (∀ mu, mu ∉ s → weightSp E mu = ⊥) ∧
      (∀ mu x, π mu x ∈ weightSp E mu) ∧
      (∀ x, ∑ mu ∈ s, π mu x = x) := by
  classical
  obtain ⟨s, hs⟩ := finitely_many_weights_span E hE
  have hbot := weightSpace_eq_bot_outside_support E s hs
  have hπ : ∀ mu, IsWtProj E mu (lagrangeOperator E mu s.toList) := by
    intro mu
    refine ⟨fun x hx => lagrangeOperator_fixes_own_weight E mu _ x hx, fun nu hnu x hx => ?_⟩
    by_cases hm : nu ∈ s
    · exact lagrangeOperator_kills_listed E mu nu hnu _ (Finset.mem_toList.2 hm) x hx
    · rw [hbot nu hm] at hx
      rw [(Submodule.mem_bot K).1 hx, map_zero]
  refine ⟨s, fun mu => lagrangeOperator E mu s.toList, hπ, fun mu W hW x hx => lagrangeOperator_preserves_stable E mu _ W hW x hx, hbot, ?_, ?_⟩
  · intro mu x
    have : LinearMap.range (lagrangeOperator E mu s.toList) ≤ weightSp E mu := by
      rw [LinearMap.range_eq_map, ← hE.2.2, Submodule.map_iSup]
      refine iSup_le fun nu => ?_
      rintro _ ⟨y, hy, rfl⟩
      by_cases h : nu = mu
      · subst h; rw [(hπ nu).1 y hy]; exact hy
      · rw [(hπ mu).2 nu h y hy]; exact Submodule.zero_mem _
    exact this ⟨x, rfl⟩
  · intro x
    have : (∑ mu ∈ s, lagrangeOperator E mu s.toList) = (1 : Module.End K V) := by
      refine linearMap_ext_on_weightSpaces E hE _ _ fun nu y hy => ?_
      rw [LinearMap.sum_apply, Module.End.one_apply]
      by_cases hm : nu ∈ s
      · rw [Finset.sum_eq_single nu (fun mu _ hmu => (hπ mu).2 nu (Ne.symm hmu) y hy) (fun h => absurd hm h)]
        exact (hπ nu).1 y hy
      · rw [hbot nu hm] at hy
        rw [(Submodule.mem_bot K).1 hy]; simp
    have h2 := congrArg (fun f : Module.End K V => f x) this
    simpa [LinearMap.sum_apply] using h2

end wt

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section abs

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem isotypic_stable_gl_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) (x : V) (hx : x ∈ isoSub E mu) :
    E a b x ∈ isoSub E mu := by
  first | exact UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator .. | (apply UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b x hx | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b x | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n

theorem commuting_enveloping_monoid (E : GLOps n K V) (X : Module.End K V) (hX : ∀ c d, X * E c d = E c d * X)
    (u : Module.End K V) (hu : u ∈ Umon E) : X * u = u * X := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction with
  | mem u hu => obtain ⟨ab, rfl⟩ := hu; exact hX _ _
  | one => simp
  | mul u v _ _ hu hv => rw [← mul_assoc, hu, mul_assoc, hv, mul_assoc]

theorem isotypic_stable_commuting (E : GLOps n K V) (X : Module.End K V) (hX : ∀ c d, X * E c d = E c d * X)
    (mu : Fin n → ℤ) (x : V) (hx : x ∈ isoSub E mu) : X x ∈ isoSub E mu := by
  unfold isoSub at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    have h1 : X (u v) = u (X v) := by
      have := congrArg (fun f : Module.End K V => f v) (commuting_enveloping_monoid E X hX u hu)
      simpa using this
    rw [h1]
    by_cases h0 : X v = 0
    · rw [h0, map_zero]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨u, hu, X v, ⟨h0, ?_, ?_⟩, rfl⟩
      · rw [mem_weightSpace_iff_diag]
        intro a
        have h2 := congrArg (fun f : Module.End K V => f v) (hX a a)
        have h3 := (mem_weightSpace_iff_diag E mu v).1 hv.2.1 a
        simp only [Module.End.mul_apply] at h2
        rw [← h2, h3, map_smul]
      · intro a b hab
        have h2 := congrArg (fun f : Module.End K V => f v) (hX a b)
        simp only [Module.End.mul_apply] at h2
        rw [← h2, hv.2.2 a b hab, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem isotypic_projector_commutes (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (lam : Fin n → ℤ)
    (e : Module.End K V) (he : IsIsoProj E lam e) (X : Module.End K V)
    (hX : ∀ mu, ∀ x ∈ isoSub E mu, X x ∈ isoSub E mu) : e * X = X * e := by
  ext x
  have hx : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  simp only [Module.End.mul_apply]
  induction hx using Submodule.iSup_induction' with
  | mem mu x hx =>
    by_cases h : mu = lam
    · subst h
      rw [he.1 x hx, he.1 _ (hX _ x hx)]
    · rw [he.2 mu h x hx, he.2 mu h _ (hX _ x hx), map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]

theorem isotypic_projector_selfAdjoint (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (lam : Fin n → ℤ)
    (e : Module.End K V) (he : IsIsoProj E lam e) (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ lam mu : Fin n → ℤ, lam ≠ mu → ∀ x ∈ isoSub E lam, ∀ y ∈ isoSub E mu, B x y = 0) (x y : V) :
    B (e x) y = B x (e y) := by
  have hx : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  have hy : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  induction hx using Submodule.iSup_induction' with
  | mem mu x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem nu y hy =>
      by_cases h : mu = lam
      · subst h
        rw [he.1 x hx]
        by_cases h' : nu = mu
        · subst h'; rw [he.1 y hy]
        · rw [he.2 nu h' y hy, map_zero, hB mu nu (Ne.symm h') x hx y hy]
      · rw [he.2 mu h x hx, map_zero, LinearMap.zero_apply]
        by_cases h' : nu = lam
        · subst h'; rw [he.1 y hy, hB mu nu h x hx y hy]
        · rw [he.2 nu h' y hy, map_zero]
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add (f := _), hy, hz]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add (f := _), LinearMap.add_apply, hx, hz]

end abs

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem choose_factorial_identity (α β f : ℕ) (h : f ≤ β) :
    β.choose f * ((β - f).factorial * (α + f).factorial) = (α + f).choose f * (β.factorial * α.factorial) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial h
  have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left f α)
  rw [Nat.add_sub_cancel] at h2
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos f)
  calc f.factorial * (β.choose f * ((β - f).factorial * (α + f).factorial))
      = (β.choose f * f.factorial * (β - f).factorial) * (α + f).factorial := by ring
    _ = β.factorial * (α + f).factorial := by rw [h1]
    _ = β.factorial * ((α + f).choose f * f.factorial * α.factorial) := by rw [h2]
    _ = f.factorial * ((α + f).choose f * (β.factorial * α.factorial)) := by ring

theorem product_two_coordinates_swap {n : ℕ} (g g' : Fin n → ℕ) (a b : Fin n) (hab : a ≠ b)
    (h : ∀ c, c ≠ a → c ≠ b → g' c = g c) :
    (∏ c, g' c) * (g a * g b) = (∏ c, g c) * (g' a * g' b) := by
  classical
  have hs : ∀ f : Fin n → ℕ, ∏ c, f c = f a * f b * ∏ c ∈ (univ.erase a).erase b, f c := by
    intro f
    rw [← Finset.mul_prod_erase univ f (mem_univ a),
      ← Finset.mul_prod_erase (univ.erase a) f (mem_erase.2 ⟨hab.symm, mem_univ b⟩)]
    ring
  have hrest : ∏ c ∈ (univ.erase a).erase b, g' c = ∏ c ∈ (univ.erase a).erase b, g c :=
    prod_congr rfl fun c hc => h c (ne_of_mem_erase (mem_of_mem_erase hc)) (ne_of_mem_erase hc)
  rw [hs g', hs g, hrest]
  ring

theorem sum_single_apply_section {ι : Type} {n : ℕ} (g : ι → ι × Fin n) (hg : ∀ l, (g l).1 = l) (f : ι →₀ ℕ)
    (v : ι × Fin n) [Decidable (v = g v.1)] :
    (∑ l ∈ f.support, Finsupp.single (g l) (f l)) v = if v = g v.1 then f v.1 else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  have key : ∀ l, g l = v → l = v.1 ∧ v = g v.1 := by
    rintro l rfl
    exact ⟨(hg l).symm, by rw [hg l]⟩
  split_ifs with hv
  · rw [Finset.sum_eq_single v.1]
    · rw [← hv, Finsupp.single_eq_same]
    · intro l _ hl
      rw [Finsupp.single_apply, if_neg]
      exact fun h => hl (key l h).1
    · intro hnot
      simp only [Finsupp.mem_support_iff, not_not] at hnot
      simp [hnot]
  · refine Finset.sum_eq_zero fun l _ => ?_
    rw [Finsupp.single_apply, if_neg]
    exact fun h => hv (key l h).2

theorem exponent_factorial_eq_prod {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) :
    expFact m = ∏ l : ι, ∏ c : Fin n, (m (l, c)).factorial := by
  classical
  unfold expFact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]

theorem exponent_factorial_ne_zero {σ : Type} (m : σ →₀ ℕ) : expFact m ≠ 0 := by
  unfold expFact Finsupp.prod
  exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _

theorem divided_power_padic_valuation_bound {ι : Type} [Fintype ι] {n : ℕ} (p : ℕ) [Fact p.Prime] (src dst : ι → ι × Fin n)
    (hs : ∀ l, (src l).1 = l) (hd : ∀ l, (dst l).1 = l) (hne : ∀ l, src l ≠ dst l)
    (m : ι × Fin n →₀ ℕ) (f : ι →₀ ℕ) (zf : ι → ℤ) (hz : ∀ l, (zf l).natAbs = (m (src l)).choose (f l)) :
    (∏ l ∈ f.support, zf l) = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p (∏ l ∈ f.support, zf l) +
      padicValNat p (expFact ((m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
        ∑ l ∈ f.support, Finsupp.single (dst l) (f l))) := by
  classical
  by_cases hall : ∀ l ∈ f.support, f l ≤ m (src l)
  swap
  ·
    left
    push_neg at hall
    obtain ⟨l, hl, hlt⟩ := hall
    apply Finset.prod_eq_zero hl
    have := hz l
    rw [Nat.choose_eq_zero_of_lt hlt] at this
    exact Int.natAbs_eq_zero.1 this
  have hall' : ∀ l, f l ≤ m (src l) := fun l => by
    by_cases hl : l ∈ f.support
    · exact hall l hl
    · simp only [Finsupp.mem_support_iff, not_not] at hl
      rw [hl]
      exact Nat.zero_le _
  right
  have hm' : ∀ x : ι × Fin n, ((m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
      ∑ l ∈ f.support, Finsupp.single (dst l) (f l)) x =
      (m x - (if x = src x.1 then f x.1 else 0)) + (if x = dst x.1 then f x.1 else 0) := by
    intro x
    rw [Finsupp.add_apply, Finsupp.tsub_apply, sum_single_apply_section src hs f x, sum_single_apply_section dst hd f x]
  set m' : ι × Fin n →₀ ℕ := (m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
      ∑ l ∈ f.support, Finsupp.single (dst l) (f l) with hm'def

  have hrow : ∀ l, (∏ c, (m (l, c)).factorial) * (m (dst l) + f l).choose (f l) =
      (∏ c, (m' (l, c)).factorial) * (m (src l)).choose (f l) := by
    intro l
    obtain ⟨a, ha⟩ : ∃ a, src l = (l, a) := ⟨(src l).2, Prod.ext (hs l) rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, dst l = (l, b) := ⟨(dst l).2, Prod.ext (hd l) rfl⟩
    have hab : a ≠ b := fun h => hne l (by rw [ha, hb, h])
    have hma : m' (l, a) = m (l, a) - f l := by
      rw [hm']; simp [ha, hb, hab]
    have hmb : m' (l, b) = m (l, b) + f l := by
      rw [hm']; simp [ha, hb, hab, Ne.symm hab]
    have hmc : ∀ c, c ≠ a → c ≠ b → m' (l, c) = m (l, c) := by
      intro c hca hcb
      rw [hm']; simp [ha, hb, hca, hcb]
    have hF : f l ≤ m (l, a) := ha ▸ hall' l
    have h2 := product_two_coordinates_swap (fun c => (m (l, c)).factorial) (fun c => (m' (l, c)).factorial) a b hab
      (fun c hca hcb => by simp only [hmc c hca hcb])
    beta_reduce at h2
    rw [hma, hmb] at h2
    have h3 := choose_factorial_identity (m (l, b)) (m (l, a)) (f l) hF
    rw [ha, hb]
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.mul_pos (Nat.factorial_pos (m (l, a))) (Nat.factorial_pos (m (l, b))))
    calc (∏ c, (m (l, c)).factorial) * (m (l, b) + f l).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial)
        = (∏ c, (m (l, c)).factorial) * ((m (l, b) + f l).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial)) := by ring
      _ = (∏ c, (m (l, c)).factorial) * ((m (l, a)).choose (f l) *
          ((m (l, a) - f l).factorial * (m (l, b) + f l).factorial)) := by rw [h3]
      _ = (m (l, a)).choose (f l) * ((∏ c, (m (l, c)).factorial) *
          ((m (l, a) - f l).factorial * (m (l, b) + f l).factorial)) := by ring
      _ = (m (l, a)).choose (f l) * ((∏ c, (m' (l, c)).factorial) *
          ((m (l, a)).factorial * (m (l, b)).factorial)) := by rw [h2]
      _ = (∏ c, (m' (l, c)).factorial) * (m (l, a)).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial) := by ring
  have htot : expFact m * ∏ l, (m (dst l) + f l).choose (f l) =
      expFact m' * ∏ l, (m (src l)).choose (f l) := by
    rw [exponent_factorial_eq_prod m, exponent_factorial_eq_prod m', ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun l _ => hrow l
  have hY : (∏ l ∈ f.support, zf l).natAbs = ∏ l, (m (src l)).choose (f l) := by
    have hnat : (∏ l ∈ f.support, zf l).natAbs = ∏ l ∈ f.support, (zf l).natAbs := by
      first
        | exact map_prod Int.natAbsHom zf f.support
        | simpa using map_prod Int.natAbsHom zf f.support
    rw [hnat, Finset.prod_congr rfl (fun l _ => hz l)]
    refine Finset.prod_subset (Finset.subset_univ _) fun l _ hl => ?_
    simp only [Finsupp.mem_support_iff, not_not] at hl
    rw [hl, Nat.choose_zero_right]
  have hX0 : ∏ l, (m (dst l) + f l).choose (f l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => (Nat.choose_pos (Nat.le_add_left _ _)).ne'
  have hY0 : ∏ l, (m (src l)).choose (f l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => (Nat.choose_pos (hall' l)).ne'
  have hv := congrArg (padicValNat p) htot
  rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (exponent_factorial_ne_zero m) hX0, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (exponent_factorial_ne_zero m') hY0] at hv
  rw [show padicValInt p (∏ l ∈ f.support, zf l) =
    padicValNat p (∏ l ∈ f.support, zf l).natAbs from by
      rw [padicValInt, Nat.padicValNat_def], hY]
  omega

end Formalism.MainNotions.G.GLWeightTheory
end
end
