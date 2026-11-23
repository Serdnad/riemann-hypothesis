module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle013
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IrreducibleStableContainsEqTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def loweringMonoid (E : GLOps n K V) : Submonoid (Module.End K V) :=
  Submonoid.closure {g | ∃ c d : Fin n, d < c ∧ g = E c d}

def hwvLoweringSpan (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ loweringMonoid E, ∃ w, IsHWV E mu w ∧ x = u w}

theorem isotypic_stable_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V} (hx : x ∈ isoSub E mu) :
    E a b x ∈ isoSub E mu := by
  first | exact UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator .. | (apply UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b x hx | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b x | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n

theorem hwv_lowering_span_lower (E : GLOps n K V) (mu : Fin n → ℤ) {a b : Fin n} (hab : b < a) {x : V}
    (hx : x ∈ hwvLoweringSpan E mu) : E a b x ∈ hwvLoweringSpan E mu := by
  first | exact UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower .. | (apply UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab x hx | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab x | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n

theorem lowering_word_hwv_operator_mem {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) {w : V} (hw : IsHWV E mu w)
    {u : Module.End K V} (hu : u ∈ loweringMonoid E) : ∀ c d : Fin n, E c d (u w) ∈ hwvLoweringSpan E mu := by
  unfold loweringMonoid at hu
  induction hu using Submonoid.closure_induction_left with
  | one =>
    intro c d
    rw [Module.End.one_apply]
    rcases lt_trichotomy c d with h | h | h
    · rw [hw.2.2 c d h]; exact Submodule.zero_mem _
    · subst h
      rw [(mem_weightSpace_iff_diagonal_rep E mu w).1 hw.2.1 c]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, (loweringMonoid E).one_mem, w, hw, rfl⟩)
    · exact Submodule.subset_span ⟨E c d, Submonoid.subset_closure ⟨c, d, h, rfl⟩, w, hw, rfl⟩
  | mul_left g hg y _ ih =>
    obtain ⟨b, a, hab, rfl⟩ := hg
    intro c d
    rw [Module.End.mul_apply, gl_commutation_apply hE c d b a (y w)]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (hwv_lowering_span_lower E mu hab (ih c d)) ?_) ?_
    · split_ifs
      · exact ih c a
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih b d
      · exact Submodule.zero_mem _

theorem hwv_lowering_span_stable {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) (c d : Fin n) {x : V}
    (hx : x ∈ hwvLoweringSpan E mu) : E c d x ∈ hwvLoweringSpan E mu := by
  have hx' := hx
  unfold hwvLoweringSpan at hx'
  induction hx' using Submodule.span_induction with
  | mem x hx1 =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx1
    exact lowering_word_hwv_operator_mem hE mu hv hu c d
  | zero => simp
  | add x y hx1 hy1 hx2 hy2 =>
    rw [map_add (f := _)]; exact Submodule.add_mem _ (hx2 hx1) (hy2 hy1)
  | smul c x hx1 hx2 => rw [map_smul]; exact Submodule.smul_mem _ _ (hx2 hx1)

theorem isotypic_le_lowering_span {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) : isoSub E mu ≤ hwvLoweringSpan E mu := by
  unfold isoSub
  rw [Submodule.span_le]
  rintro x ⟨u, hu, v, hv, rfl⟩
  unfold Umon at hu
  induction hu using Submonoid.closure_induction_left with
  | one => exact Submodule.subset_span ⟨1, (loweringMonoid E).one_mem, v, hv, rfl⟩
  | mul_left g hg y _ ih =>
    obtain ⟨ab, rfl⟩ := hg
    exact hwv_lowering_span_stable hE mu ab.1 ab.2 ih

theorem hwv_orthogonal_lowering_span [CharZero K] {E : GLOps n K V} (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ a b x y, B (E a b x) y = B x (E b a y)) {lam mu : Fin n → ℤ} (hne : lam ≠ mu) {v : V}
    (hv : IsHWV E lam v) {z : V} (hz : z ∈ hwvLoweringSpan E mu) : B v z = 0 := by
  unfold hwvLoweringSpan at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    unfold loweringMonoid at hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      rw [Module.End.one_apply]
      obtain ⟨a, ha⟩ : ∃ a, lam a ≠ mu a := by
        by_contra h
        push_neg at h
        exact hne (funext h)
      have h1 := hB a a v w
      rw [(mem_weightSpace_iff_diagonal_rep E lam v).1 hv.2.1 a, (mem_weightSpace_iff_diagonal_rep E mu w).1 hw.2.1 a, map_smul, map_smul,
        LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
      have h2 : ((lam a : K) - (mu a : K)) * B v w = 0 := by rw [sub_mul, h1, sub_self]
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exfalso; apply ha
        have : (lam a : K) = (mu a : K) := sub_eq_zero.1 h3
        exact_mod_cast this
      · exact h3
    | mul_left g hg y _ _ =>
      obtain ⟨c, d, hcd, rfl⟩ := hg
      rw [Module.End.mul_apply, ← hB d c v (y w), hv.2.2 d c hcd]
      simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

theorem contravariant_orthogonality_holds : ContravariantIsotypicOrthogonal := by
  intro K V _ _ _ _ n E hE B hB lam mu hne x hx
  unfold isoSub at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    unfold Umon at hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      intro y hy
      exact hwv_orthogonal_lowering_span B hB hne hv (isotypic_le_lowering_span hE mu hy)
    | mul_left g hg u' _ ih =>
      obtain ⟨ab, rfl⟩ := hg
      intro y hy
      rw [Module.End.mul_apply]
      show B (E ab.1 ab.2 (u' v)) y = 0
      rw [hB]
      exact ih _ (isotypic_stable_operator E mu _ _ hy)
  | zero => intro y _; simp
  | add x y _ _ hx hy => intro z hz; rw [map_add (f := _), LinearMap.add_apply, hx z hz, hy z hz, add_zero]
  | smul c x _ hx => intro z hz; rw [map_smul, LinearMap.smul_apply, hx z hz, smul_zero]

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def ValuationProperties (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  vK p (0 : KK O) = ⊤ ∧
  (∀ x y : KK O, vK p (x * y) = vK p x + vK p y) ∧
  (∀ x y : KK O, min (vK p x) (vK p y) ≤ vK p (x + y)) ∧
  (∀ m : ℕ, m ≠ 0 → vK p (m : KK O) = ((padicValNat p m : ℚ) : WithTop ℚ)) ∧
  (∀ x : KK O, vK p (-x) = vK p x) ∧
  (∀ x : KK O, 0 ≤ vK p x ↔ ∃ o : O, x = algebraMap O (KK O) o)

def FockLatticeClosure (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ σ : Type,
    InBB (O := O) p (0 : MvPolynomial σ (KK O)) ∧
    (∀ F G : MvPolynomial σ (KK O), InBB (O := O) p F → InBB (O := O) p G → InBB (O := O) p (F + G)) ∧
    (∀ (o : O) (F : MvPolynomial σ (KK O)), InBB (O := O) p F → InBB (O := O) p (o • F)) ∧
    (∀ (m : σ →₀ ℕ) (c : KK O), InBB (O := O) p (monomial m c) ↔
      0 ≤ vK p c + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ)) ∧
    (∀ F : MvPolynomial σ (KK O), InBB (O := O) p F ↔ ∀ m, InBB (O := O) p (monomial m (F.coeff m))) ∧
    (∀ u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O),
      (∀ m c, InBB (O := O) p (monomial m c) → InBB (O := O) p (u (monomial m c))) →
      ∀ F, InBB (O := O) p F → InBB (O := O) p (u F)) ∧
    (∀ (m m' : σ →₀ ℕ) (c : KK O) (z : ℤ), InBB (O := O) p (monomial m c) →
      (z = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m')) →
      InBB (O := O) p (monomial m' (c * (z : KK O)))) ∧
    (∀ u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O),
      (∀ m, u (monomial m 1) ∈ IntPol O σ) → ∀ F ∈ IntPol O σ, u F ∈ IntPol O σ) ∧
    (∀ (m : σ →₀ ℕ) (z : ℤ), monomial m (z : KK O) ∈ IntPol O σ) ∧
    (∀ F : MvPolynomial σ (KK O), F ∈ IntPol O σ ↔ ∀ m, ∃ o : O, F.coeff m = algebraMap O (KK O) o)

def PolynomialIntegralFormPreservesLattices (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι),
    PolUZStable LL S (IntPol O (ι × Fin n)) ∧
        ∀ u ∈ polUZgens (KK O) LL S, ∀ F : MvPolynomial (ι × Fin n) (KK O),
          InBB (O := O) p F → InBB (O := O) p (u F)

def IntegralFormGeneratorsPreserveLattices (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι), ∀ u ∈ UZgens (glOps (KK O) n LL S),
        (∀ F ∈ IntPol O (ι × Fin n), u F ∈ IntPol O (ι × Fin n)) ∧
        ∀ F : MvPolynomial (ι × Fin n) (KK O), InBB (O := O) p F → InBB (O := O) p (u F)

def FockLatticeFiniteSpanning (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι],
      ∃ BBs : Submodule O (MvPolynomial (ι × Fin n) (KK O)), (∀ F, F ∈ BBs ↔ InBB (O := O) p F) ∧
        ∀ d : ι → ℕ, (latticeMultidegreePart (IntPol O (ι × Fin n)) d).FG ∧ MQ (K := KK O) (latticeMultidegreePart (IntPol O (ι × Fin n)) d) = ⊤ ∧
          (latticeMultidegreePart BBs d).FG ∧ MQ (K := KK O) (latticeMultidegreePart BBs d) = ⊤

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem coeff_weightComponent {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (nu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (weightComponent LL S nu F) m = if wtS LL S m = nu then AddMonoidAlgebra.coeff F m else 0 := by
  classical
  unfold weightComponent
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
  by_cases h1 : wtS LL S m = nu <;> by_cases h2 : AddMonoidAlgebra.coeff F m = 0 <;> simp [h1, h2]

section bwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)
  {L : Type} [Field L] (φ : R →+* L) (W : Submodule R (MvPolynomial (ι × Fin n) R))

def scalarExtension : Submodule L (MvPolynomial (ι × Fin n) L) :=
  Submodule.span L ((MvPolynomial.map φ) '' (W : Set (MvPolynomial (ι × Fin n) R)))

def SubstitutionPreservesExtension (h h' : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ x ∈ scalarExtension φ W, matrixSubst LL S (RingHom.id L) h h' x ∈ scalarExtension φ W

theorem scalarExtension_monomial_weights (hGr : BinomialStableContainsComponents) (hW2 : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) :
    ∀ z ∈ scalarExtension φ W, ∀ m ∈ z.support, wtS LL S m ∈ polWts LL S W := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    intro m hm
    have hm' : m ∈ w.support := MvPolynomial.support_map_subset φ w hm
    simp only [polWts, Set.mem_setOf_eq]
    refine ⟨weightComponent LL S (wtS LL S m) w, hGr R ι LL n S W hW2 w hw _, ?_, ?_⟩
    · intro h0
      have e := congrArg (AddMonoidAlgebra.coeff · m) h0
      rw [coeff_weightComponent, if_pos rfl, MvPolynomial.coeff_zero] at e
      exact (MvPolynomial.mem_support_iff.1 hm') e
    · intro m' hm''
      rw [MvPolynomial.mem_support_iff, coeff_weightComponent] at hm''
      by_contra hne
      exact hm'' (if_neg hne)
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    classical
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (MvPolynomial.support_smul hm)

end bwd

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def weightHeightAscending (nu : Fin n → ℤ) : ℤ := ∑ c : Fin n, ((c : ℕ) : ℤ) * nu c

theorem weightHeightAscending_add_root (nu : Fin n → ℤ) (a b : Fin n) :
    weightHeightAscending (nu + rootW a b) = weightHeightAscending nu + (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  unfold weightHeightAscending rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem irreducible_lowering_word_weight [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    {u : Module.End (KK O) V} (hu : u ∈ loweringOperatorMonoid E) :
    ∃ nu, u v ∈ weightSp E nu ∧ ((nu = lam ∧ u v = v) ∨ weightHeightAscending lam < weightHeightAscending nu) ∧
      nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n) := by
  have hE : IsGLRep E := hI.1
  have hv : v ∈ weightSp E lam := hI.2.2.1.2.1
  unfold loweringOperatorMonoid at hu
  induction hu using Submonoid.closure_induction_left with
  | one => exact ⟨lam, hv, Or.inl ⟨rfl, rfl⟩, le_rfl, le_rfl⟩
  | mul_left g hg w _ ih =>
    obtain ⟨a, b, hba, rfl⟩ := hg
    obtain ⟨nu, hnu, hor, h0, hl⟩ := ih
    refine ⟨nu + rootW a b, gl_rep_operator_weight_shift hE hnu a b, Or.inr ?_, ?_, ?_⟩
    · have hab : ((b : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast hba
      rw [weightHeightAscending_add_root]
      rcases hor with ⟨rfl, -⟩ | h
      · linarith
      · linarith
    · have ha0 : a ≠ 0 := by
        intro h; rw [h] at hba; exact absurd hba (Fin.not_lt_zero _)
      have : (nu + rootW a b) 0 ≤ nu 0 := by
        simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm ha0)]
        split_ifs <;> omega
      exact this.trans h0
    · have hbl : b ≠ lastIdx n := by
        intro h
        have : (a : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt a.isLt
        have hb : (b : ℕ) = n - 1 := by rw [h]; rfl
        have : (b : ℕ) < (a : ℕ) := hba
        omega
      have : nu (lastIdx n) ≤ (nu + rootW a b) (lastIdx n) := by
        simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm hbl)]
        split_ifs <;> omega
      exact hl.trans this

theorem top_le_line_sup_higher_weights [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    (⊤ : Submodule (KK O) V) ≤ Submodule.span (KK O) {v} ⊔ ⨆ nu, ⨆ (_ : weightHeightAscending lam < weightHeightAscending nu), weightSp E nu := by
  rw [← irreducible_lowering_span_top hI, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨nu, hnu, h1 | h1, -⟩ := irreducible_lowering_word_weight hI hu
  · rw [h1.2]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem h1 hnu))

theorem top_le_end_bounded_weights [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    (⊤ : Submodule (KK O) V) ≤ ⨆ nu, ⨆ (_ : nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n)), weightSp E nu := by
  rw [← irreducible_lowering_span_top hI, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨nu, hnu, -, h0, hl⟩ := irreducible_lowering_word_weight hI hu
  exact Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem ⟨h0, hl⟩ hnu)

theorem irreducible_weight_end_bounds [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) :
    nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n) := by
  by_contra hn
  exact h0 (weight_support_sum_eq_zero E (fun mu => mu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ mu (lastIdx n)) hx
    (top_le_end_bounded_weights hI Submodule.mem_top) hn)

theorem irreducible_highest_weight_line [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) {x : V} (hx : x ∈ weightSp E lam) : ∃ c : KK O, x = c • v := by
  have hx2 := top_le_line_sup_higher_weights hI (Submodule.mem_top (x := x))
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx2
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hv : v ∈ weightSp E lam := hI.2.2.1.2.1
  have hzw : z ∈ weightSp E lam := by
    have e : z = (c • v + z) - c • v := by abel
    rw [e]
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ c hv)
  have hz0 : z = 0 := weight_support_sum_eq_zero E (fun nu => weightHeightAscending lam < weightHeightAscending nu) hzw hz (lt_irrefl _)
  exact ⟨c, by rw [hz0, add_zero]⟩

theorem highest_line_isCompl_other_weights [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) : IsCompl (Submodule.span (KK O) {v}) (otherWts E lam) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact weight_support_sum_eq_zero E (fun mu => mu ∈ {mu | mu ≠ lam}) (Submodule.smul_mem _ c hI.2.2.1.2.1) hx2
      (fun h => h rfl)
  · rw [codisjoint_iff, eq_top_iff, ← hI.1.2.2, iSup_le_iff]
    intro mu x hx
    by_cases h : mu = lam
    · subst h
      obtain ⟨c, rfl⟩ := irreducible_highest_weight_line hI hx
      exact Submodule.mem_sup_left (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v))
    · apply Submodule.mem_sup_right
      show x ∈ ⨆ mu ∈ {mu | mu ≠ lam}, weightSp E mu
      exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem h hx)

theorem exists_highest_coordinate_functional [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) : ∃ xi : V →ₗ[KK O] KK O, xi v = 1 ∧ (∀ w ∈ otherWts E lam, xi w = 0) ∧
      ∀ x, x - xi x • v ∈ otherWts E lam := by
  have hc := highest_line_isCompl_other_weights hI
  have hv0 : v ≠ 0 := hI.2.2.1.1
  let P := Submodule.linearProjOfIsCompl _ _ hc
  let e := LinearEquiv.toSpanNonzeroSingleton (KK O) V v hv0
  refine ⟨e.symm.toLinearMap ∘ₗ P, ?_, ?_, ?_⟩
  · have h1 : P v = ⟨v, Submodule.mem_span_singleton_self v⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hc ⟨v, Submodule.mem_span_singleton_self v⟩
    show e.symm (P v) = 1
    rw [h1, LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  · intro w hw
    have h2 : P w = 0 := Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
    show e.symm (P w) = 0
    rw [h2, map_zero]
  · intro x
    have h8 : ∀ s : KK O, ((e s : Submodule.span (KK O) {v}) : V) = s • v := fun s => by
      first
        | rfl
        | simp [e, LinearEquiv.toSpanNonzeroSingleton_apply]
    have h3 : (e.symm (P x)) • v = (P x : V) := by
      rw [← h8, LinearEquiv.apply_symm_apply]
    show x - (e.symm (P x)) • v ∈ otherWts E lam
    rw [h3]
    have hPP : P (P x : V) = P x := Submodule.linearProjOfIsCompl_apply_left hc (P x)
    have h5 : P (x - (P x : V)) = 0 := by
      rw [map_sub, hPP, sub_self]
    have h6 := LinearMap.mem_ker.mpr h5
    have h7 := Submodule.linearProjOfIsCompl_ker hc
    rw [SetLike.ext_iff] at h7
    exact (h7 _).mp h6

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end
