module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle004
public import Mathlib.Algebra.Module.Lattice.Basic
public import Lemmata.GeneralBFactLeftVersion.Imports
public import Mathlib.Algebra.Module.Lattice.Full
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag_action (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, sub_eq_zero]

theorem gl_operator_commutator {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have hx : E a b (E c d x) - E c d (E a b x) = (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
    have h1 := LinearMap.congr_fun (hrel a b c d) x
    split_ifs at h1 ⊢ <;> simpa using h1
  rw [← hx]
  abel

theorem operator_shifts_weight_by_root {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (a b : Fin n) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [mem_weightSpace_iff_diag_action] at hx ⊢
  intro c
  rw [gl_operator_commutator hrel c c a b x, hx c, map_smul]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb; simp [rootW]
  · subst hca; simp [rootW, Pi.single_apply, hcb, Ne.symm hcb, add_smul]
  · subst hcb; simp [rootW, Pi.single_apply, hca, sub_smul, add_smul]
  · simp [rootW, Pi.single_apply, hca, hcb, Ne.symm hcb]

inductive LoweringWordAlt (E : GLOps n K V) (h : V) : ℕ → V → Prop
  | zero : LoweringWordAlt E h 0 h
  | succ {k : ℕ} {x : V} {a b : Fin n} : b < a → LoweringWordAlt E h k x → LoweringWordAlt E h (k + 1) (E a b x)

def loweringSpan (E : GLOps n K V) (h : V) : Submodule K V := Submodule.span K {x | ∃ k, LoweringWordAlt E h k x}

private theorem c14D_Low_mem_lemma {E : GLOps n K V} {h : V} {k : ℕ} {x : V}
    (hx : LoweringWordAlt E h k x) : x ∈ loweringSpan E h := by
  unfold loweringSpan
  exact Submodule.subset_span ⟨k, hx⟩

theorem lowering_span_stable_lowering (E : GLOps n K V) (h : V) {a b : Fin n} (hab : b < a) (z : V) (hz : z ∈ loweringSpan E h) :
    E a b z ∈ loweringSpan E h := by
  have key : loweringSpan E h ≤ (loweringSpan E h).comap (E a b) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨k, hk⟩
    exact Submodule.mem_comap.mpr (c14D_Low_mem_lemma (LoweringWordAlt.succ hab hk))
  exact key hz

theorem mem_highestWeight_iff (E : GLOps n K V) (lam : Fin n → ℤ) (h : V) :
    h ∈ highestWeightVectors E lam ↔ h ∈ weightSp E lam ∧ ∀ a b, a < b → E a b h = 0 := by
  simp only [highestWeightVectors, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem lowering_word_operator_mem_span {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ highestWeightVectors E lam) (k : ℕ) (x : V) (hx : LoweringWordAlt E h k x) :
    ∀ c d, E c d x ∈ loweringSpan E h := by
  induction hx with
  | zero =>
    intro c d
    have hh' := (mem_highestWeight_iff E lam h).1 hh
    rcases lt_trichotomy c d with hcd | hcd | hcd
    · rw [hh'.2 c d hcd]
      exact Submodule.zero_mem _
    · subst hcd
      rw [(mem_weightSpace_iff_diag_action E lam h).1 hh'.1 c]
      exact Submodule.smul_mem _ _ (c14D_Low_mem_lemma LoweringWordAlt.zero)
    · exact c14D_Low_mem_lemma (LoweringWordAlt.succ hcd LoweringWordAlt.zero)
  | @succ k y a b hab hk ih =>
    intro c d
    rw [gl_operator_commutator hrel c d a b y]
    refine Submodule.add_mem _ (lowering_span_stable_lowering E h hab _ (ih c d)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih c b
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih a d
      · exact Submodule.zero_mem _

theorem lowering_span_stable_all {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ highestWeightVectors E lam) (c d : Fin n) (z : V) (hz : z ∈ loweringSpan E h) :
    E c d z ∈ loweringSpan E h := by
  have key : loweringSpan E h ≤ (loweringSpan E h).comap (E c d) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨k, hk⟩
    exact Submodule.mem_comap.mpr (lowering_word_operator_mem_span hrel lam h hh k y hk c d)
  exact key hz

theorem enveloping_monoid_preserves_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W)
    (u : Module.End K V) (hu : u ∈ Umon E) : ∀ z ∈ W, u z ∈ W := by
  let S : Submonoid (Module.End K V) :=
    { carrier := {f | ∀ z ∈ W, f z ∈ W}
      mul_mem' := by
        intro f g hf hg
        show ∀ z ∈ W, (f * g) z ∈ W
        intro z hz
        exact hf _ (hg z hz)
      one_mem' := by
        show ∀ z ∈ W, (1 : Module.End K V) z ∈ W
        intro z hz
        exact hz }
  have hle : Umon E ≤ S := by
    unfold Umon
    rw [Submonoid.closure_le]
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show ∀ z ∈ W, E a b z ∈ W
    exact hW a b
  exact hle hu

theorem generated_le_lowering_span {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ highestWeightVectors E lam) : generatedSubrep E h ≤ loweringSpan E h := by
  refine Submodule.span_le.mpr ?_
  rintro y ⟨u, hu, rfl⟩
  exact enveloping_monoid_preserves_stable E (loweringSpan E h) (fun a b z hz => lowering_span_stable_all hrel lam h hh a b z hz) u hu h
    (c14D_Low_mem_lemma LoweringWordAlt.zero)

def weightHeightSum (mu : Fin n → ℤ) : ℤ := ∑ a : Fin n, (a.val : ℤ) * mu a

theorem heightSum_add_root (mu : Fin n → ℤ) (a b : Fin n) :
    weightHeightSum (mu + rootW a b) = weightHeightSum mu + ((a.val : ℤ) - (b.val : ℤ)) := by
  simp only [weightHeightSum, Pi.add_apply, rootW, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp [Pi.single_apply]

theorem lowering_word_weight_and_monoid {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ weightSp E lam) (k : ℕ) (x : V) (hx : LoweringWordAlt E h k x) :
    (∃ mu, x ∈ weightSp E mu ∧ weightHeightSum lam + k ≤ weightHeightSum mu) ∧ (∃ u ∈ Umon E, x = u h) ∧ (k = 0 → x = h) := by
  induction hx with
  | zero =>
    refine ⟨⟨lam, hh, by simp⟩, ⟨1, one_mem _, rfl⟩, fun _ => rfl⟩
  | @succ k y a b hab hk ih =>
    obtain ⟨⟨mu, hmu, hht⟩, ⟨u, hu, hyu⟩, -⟩ := ih
    have hE : E a b ∈ Umon E := by
      unfold Umon
      exact Submonoid.subset_closure ⟨(a, b), rfl⟩
    refine ⟨⟨mu + rootW a b, operator_shifts_weight_by_root hrel a b mu y hmu, ?_⟩, ⟨E a b * u, mul_mem hE hu, ?_⟩,
      fun h0 => absurd h0 (Nat.succ_ne_zero k)⟩
    · rw [heightSum_add_root]
      have hab' : b.val < a.val := hab
      push_cast
      omega
    · subst hyu
      rfl

end

theorem hwv_generated_multiple_of_hwv : GeneratedMultipleOfHWV := by
  intro K V _ _ _ n E hE lam h hh
  have hrel := hE.1
  refine le_trans (generated_le_lowering_span hrel lam h hh) ?_
  refine Submodule.span_le.mpr ?_
  rintro x ⟨k, hk⟩
  rw [SetLike.mem_coe]
  obtain ⟨⟨mu, hmu, hht⟩, ⟨u, hu, hxu⟩, h0⟩ :=
    lowering_word_weight_and_monoid hrel lam h ((mem_highestWeight_iff E lam h).1 hh).1 k x hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [h0 hk0]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self h)
  · apply Submodule.mem_sup_right
    have hne : mu ≠ lam := by
      rintro rfl
      omega
    have hg : x ∈ generatedSubrep E h := by
      unfold generatedSubrep
      exact Submodule.subset_span ⟨u, hu, hxu⟩
    have hx : x ∈ weightSp E mu ⊓ generatedSubrep E h := Submodule.mem_inf.mpr ⟨hmu, hg⟩
    exact Submodule.mem_iSup_of_mem mu
      (Submodule.mem_iSup_of_mem (show mu ∈ {mu : Fin n → ℤ | mu ≠ lam} from hne) hx)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

@[simp] theorem restrictRepresentation_coe (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) (a b : Fin n) (x : W) :
    ((restrictRepresentation E W h a b x : W) : V) = E a b x := rfl

@[simp] theorem homRepresentation_apply (E : GLOps n K V) (E' : GLOps n K V') (a b : Fin n) (f : V →ₗ[K] V') (x : V) :
    homRepresentation E E' a b f x = E' a b (f x) - f (E a b x) := by
  simp [homRepresentation]

theorem restrict_mem_weightSpace_iff (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) (mu : Fin n → ℤ) (x : W) :
    x ∈ weightSp (restrictRepresentation E W h) mu ↔ (x : V) ∈ weightSp E mu := by
  rw [mem_weightSp_iff_diagonal_apply, mem_weightSp_iff_diagonal_apply]
  constructor
  · intro hx a
    have e := congrArg Subtype.val (hx a)
    simpa using e
  · intro hx a
    ext
    simpa using hx a

theorem restrictRepresentation_isRep [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V)
    (h : IsSubrepresentation E W) : IsGLRep (restrictRepresentation E W h) := by
  refine ⟨fun a b c d => ?_, fun x => ⟨⊤, inferInstance, Submodule.mem_top,
    fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  · refine LinearMap.ext fun x => Subtype.ext ?_
    have e := congrArg (fun f => f (x : V)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, restrictRepresentation_coe]
    rw [e]
    split_ifs <;> simp
  · obtain ⟨s, π, -, hinv, -, hmem, hsum⟩ := weight_projections_exist E hE
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ mu ∈ s, (⟨π mu x, hinv mu W (fun a y hy => h a a y hy) x x.2⟩ : W) := by
      ext
      simp [hsum]
    rw [hx]
    refine Submodule.sum_mem _ fun mu _ => ?_
    refine Submodule.mem_iSup_of_mem mu ?_
    rw [restrict_mem_weightSpace_iff]
    exact hmem mu x

theorem weightProjection_diagonal_apply_eq_smul [CharZero K] (E : GLOps n K V) (hE : IsGLRep E) (nu : Fin n → ℤ) (π : Module.End K V)
    (hπ : IsWtProj E nu π) (a : Fin n) (x : V) : π (E a a x) = (nu a : K) • π x := by
  have hx : x ∈ (⨆ mu, weightSp E mu) := hE.2.2 ▸ Submodule.mem_top
  refine Submodule.iSup_induction (p := weightSp E) (motive := fun y => π (E a a y) = (nu a : K) • π y) hx
    (fun mu y hy => ?_) ?_ (fun y w hy hw => ?_)
  · rw [(mem_weightSp_iff_diagonal_apply E mu y).1 hy a, map_smul]
    by_cases hmu : mu = nu
    · subst hmu
      rfl
    · rw [hπ.2 mu hmu y hy, smul_zero, smul_zero]
  · simp
  · simp only [map_add (f := _), hy, hw, smul_add]

theorem homRepresentation_isRep [CharZero K] [FiniteDimensional K V] [FiniteDimensional K V'] (E : GLOps n K V)
    (E' : GLOps n K V') (hE : IsGLRep E) (hE' : IsGLRep E') : IsGLRep (homRepresentation E E') := by
  refine ⟨fun a b c d => ?_, fun f => ⟨⊤, inferInstance, Submodule.mem_top,
    fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  · ext f x
    have h1 := congrArg (fun g => g (f x)) (hE'.1 a b c d)
    have h2 := congrArg (fun g => f (g x)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub] at h1 h2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, homRepresentation_apply, map_sub]
    split_ifs at h1 h2 ⊢ <;>
      simp only [LinearMap.zero_apply, map_zero, sub_zero, zero_sub, homRepresentation_apply, map_sub,
        map_neg] at h1 h2 ⊢ <;>
      (rw [eq_add_of_sub_eq h1, eq_add_of_sub_eq h2]; abel)
  · obtain ⟨s, π, hπ, -, -, -, hsum⟩ := weight_projections_exist E hE
    obtain ⟨s', π', -, -, -, hmem', hsum'⟩ := weight_projections_exist E' hE'
    rw [eq_top_iff]
    intro f _
    have hf : f = ∑ mu ∈ s, ∑ mu' ∈ s', (π' mu').comp (f.comp (π mu)) := by
      ext x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      rw [Finset.sum_comm]

      simp only [← map_sum]
      rw [hsum x, hsum' (f x)]
    rw [hf]
    refine Submodule.sum_mem _ fun mu _ => Submodule.sum_mem _ fun mu' _ => ?_
    refine Submodule.mem_iSup_of_mem (mu' - mu) ?_
    rw [mem_weightSp_iff_diagonal_apply]
    intro a
    ext x
    simp only [homRepresentation_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [weightProjection_diagonal_apply_eq_smul E hE mu (π mu) (hπ mu) a x, map_smul, map_smul,
      (mem_weightSp_iff_diagonal_apply E' mu' _).1 (hmem' mu' _) a]
    simp only [Pi.sub_apply, Int.cast_sub, sub_smul]

theorem root_differences_bddAbove [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V) :
    BddAbove {k : ℕ | ∃ mu ∈ wtsOf E W, ∃ nu ∈ wtsOf E W, ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} := by
  obtain ⟨s, hs⟩ := finitely_many_weights_span E hE
  refine ⟨s.sup fun mu => s.sup fun nu => Finset.univ.sup fun a => (mu a - nu a).toNat, ?_⟩
  rintro k ⟨mu, hmu, nu, hnu, a, b, hab, heq⟩
  have hmu' : mu ∈ s := by
    by_contra hc
    apply hmu
    rw [weightSpace_eq_bot_outside_support E s hs mu hc, bot_inf_eq]
  have hnu' : nu ∈ s := by
    by_contra hc
    apply hnu
    rw [weightSpace_eq_bot_outside_support E s hs nu hc, bot_inf_eq]
  have hk : mu a - nu a = (k : ℤ) := by
    have e := congrFun heq a
    simp only [Pi.sub_apply, Pi.smul_apply, rootW, Pi.single_eq_same, Pi.single_eq_of_ne hab,
      sub_zero, smul_eq_mul, mul_one] at e
    exact e
  have hk' : k ≤ (mu a - nu a).toNat := by omega
  exact Finset.le_sup_of_le hmu' (Finset.le_sup_of_le hnu' (Finset.le_sup_of_le (Finset.mem_univ a) hk'))

end

theorem restriction_is_representation : RestrictionIsRepresentation := by
  intro n K V _ _ _ _ _ E hE W h
  exact restrictRepresentation_isRep E hE W h

theorem hom_space_is_representation : HomSpaceIsRepresentation := by
  intro n K V V' _ _ _ _ _ _ _ _ E E' hE hE'
  exact homRepresentation_isRep E E' hE hE'

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem finite_full_submodule_isLattice {O : Type} [CommRing O] [IsDomain O]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (M : Submodule O V) (hfg : M.FG) (hM : MQ (K := KK O) M = ⊤) : Submodule.IsLattice (KK O) M :=
  Submodule.IsLattice.of_fg (KK O) hfg

theorem exists_nonzero_multiple_mem_lattice {O : Type} [CommRing O] [IsDomain O]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (M : Submodule O V) (hM : MQ (K := KK O) M = ⊤) (x : V) : ∃ a : O, a ≠ 0 ∧ a • x ∈ M := by
  first | exact Bl.general_b_fact_left_version.goal1 .. | (apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_version.goal1 <;> first | assumption | infer_instance)

theorem dual_lattice_values_mem_scaled : DualLatticeDivisibility := by
  intro O _ _ _ V _ _ _ _ _ M hfg hM t z hz
  have : Submodule.IsFullLattice (KK O) M :=
    { toIsLattice := finite_full_submodule_isLattice M hfg hM
      span_eq_top := hM }
  have : Module.Free O M := Submodule.IsLattice.free (KK O) M
  have : Module.Finite O M := Submodule.IsLattice.finite (KK O) M
  let b := Module.finBasis O M
  let B := b.extendOfIsFullLattice (KK O)
  have hB : ∀ i, B i = ((b i : M) : V) := fun i =>
    Module.Basis.extendOfIsFullLattice_apply (KK O) b i
  have hcoord : ∀ i, ∀ x ∈ M, ∃ o : O, B.coord i x = algebraMap O (KK O) o := by
    intro i x hx
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 : x = ∑ j, (algebraMap O (KK O) (b.repr ⟨x, hx⟩ j)) • B j := by
      have h2 := congrArg (fun y : M => (y : V)) (b.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      refine h2.symm.trans ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hB, algebraMap_smul]
    conv_lhs => rw [h1]
    simp [Module.Basis.coord_apply, Finsupp.single_apply, Algebra.algebraMap_eq_smul_one]
  choose o ho using fun i => hz (B.coord i) (hcoord i)
  refine ⟨∑ i, o i • ((b i : M) : V), M.sum_mem fun i _ => M.smul_mem _ (b i).2, ?_⟩
  rw [← B.sum_repr z, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := ho i
  rw [Module.Basis.coord_apply] at this
  rw [this, hB, mul_smul, algebraMap_smul]

theorem lattice_inter_subspace_basis : LatticeSubspaceBasis := by
  intro O _ _ _ V _ _ _ _ _ M hfg hM H
  let N : Submodule O H := M.comap (H.subtype.restrictScalars O)
  have hmemN : ∀ x : H, x ∈ N ↔ (x : V) ∈ M := fun x => Iff.rfl
  have hNoeM : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hfg
  let φ : N →ₗ[O] M :=
    { toFun := fun x => ⟨((x : H) : V), (hmemN x.1).1 x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hφ : Function.Injective φ := by
    intro x y hxy
    have : ((x : H) : V) = ((y : H) : V) := congrArg (fun w : M => (w : V)) hxy
    exact Subtype.ext (Subtype.ext this)
  have hNoeN : IsNoetherian O N := isNoetherian_of_injective φ hφ
  have hNfg : N.FG := (Module.Finite.iff_fg).1 inferInstance
  have hNspan : Submodule.span (KK O) (N : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_nonzero_multiple_mem_lattice M hM (x : V)
    have ha1 : algebraMap O (KK O) a ≠ 0 :=
      (map_ne_zero_iff (algebraMap O (KK O)) (IsFractionRing.injective O (KK O))).2 ha
    have hmem : a • x ∈ N := (hmemN _).2 (by simpa using hax)
    have hx : x = (algebraMap O (KK O) a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul (KK O) a x, smul_smul, inv_mul_cancel₀ ha1, one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have : Submodule.IsFullLattice (KK O) N :=
    { toIsLattice := Submodule.IsLattice.of_fg (KK O) hNfg
      span_eq_top := hNspan }
  have : Module.Free O N := Submodule.IsLattice.free (KK O) N
  let b := Module.finBasis O N
  let B := b.extendOfIsFullLattice (KK O)
  have hB : ∀ i, B i = ((b i : N) : H) := fun i =>
    Module.Basis.extendOfIsFullLattice_apply (KK O) b i
  refine ⟨Module.finrank O N, fun j => (((b j : N) : H) : V), fun j => ⟨(hmemN _).1 (b j).2, (b j : H).2⟩, ?_, ?_, ?_⟩
  · have h1 := B.linearIndependent.map' H.subtype (Submodule.ker_subtype H)
    have h2 : (fun j => (((b j : N) : H) : V)) = (H.subtype ∘ B) := by
      funext j
      simp [hB]
    rw [h2]
    exact h1
  · intro x hx
    have h1 := congrArg (fun y : H => (y : V)) (B.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_⟩)
    simp [hB]
  · intro x hxM hxH
    refine ⟨fun j => b.repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩ j, ?_⟩
    have h1 := congrArg (fun y : N => ((y : H) : V)) (b.sum_repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm

end Formalism.MainNotions.G.GLWeightTheory
end
end
