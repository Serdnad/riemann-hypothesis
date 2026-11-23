module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.Qk16.Jm :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦ Matrix.diagonal fun (a : Fin n) ↦ if ε a = Bool.true then (1 : ℂ) else (-1 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qk16.inUJ :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) ↦
      g.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * g = UpperTheory.Reformulated.B.Qk16.Jm ε

theorem UpperTheory.Reformulated.B.Qk16.aux3 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
          g * h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g h hg hh
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk16.inUJ] at hg hh ⊢
  rw [Units.val_mul, Matrix.conjTranspose_mul]
  calc (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        UpperTheory.Reformulated.B.Qk16.Jm ε * ((g : Matrix (Fin n) (Fin n) ℂ) * (h : Matrix (Fin n) (Fin n) ℂ))
      = (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose * ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        UpperTheory.Reformulated.B.Qk16.Jm ε * (g : Matrix (Fin n) (Fin n) ℂ)) * (h : Matrix (Fin n) (Fin n) ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = UpperTheory.Reformulated.B.Qk16.Jm ε := by rw [hg, hh]

theorem UpperTheory.Reformulated.B.Qk16.aux4 :
    ∀ {n : ℕ} (ε : Fin n → Bool),
      (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε *
          (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        UpperTheory.Reformulated.B.Qk16.Jm ε := by
  intro n ε
  simp

theorem UpperTheory.Reformulated.B.Qk16.aux5 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        g⁻¹ ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g hg
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk16.inUJ] at hg ⊢
  have h1 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv g
  generalize ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = B at h1 ⊢
  generalize (g : Matrix (Fin n) (Fin n) ℂ) = A at h1 hg
  calc B.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * B
      = B.conjTranspose * (A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A) * B := by rw [hg]
    _ = (A * B).conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * (A * B) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = UpperTheory.Reformulated.B.Qk16.Jm ε := by rw [h1]; simp

noncomputable def UpperTheory.Reformulated.B.Qk16.UJ :
    {n : ℕ} → (Fin n → Bool) → Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦
      { carrier := {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)},
        mul_mem' := @UpperTheory.Reformulated.B.Qk16.aux3 n ε, one_mem' := UpperTheory.Reformulated.B.Qk16.aux4 ε,
        inv_mem' := @UpperTheory.Reformulated.B.Qk16.aux5 n ε : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ }

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk16.toM :
    {n : ℕ} → {ε : Fin n → Bool} → ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} {ε : Fin n → Bool} (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦
      (↑(↑g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

private theorem UpperTheory.Reformulated.B.Qk16.Jm_mul_Jm {n : ℕ} (ε : Fin n → Bool) :
    UpperTheory.Reformulated.B.Qk16.Jm ε * UpperTheory.Reformulated.B.Qk16.Jm ε = 1 := by
  unfold UpperTheory.Reformulated.B.Qk16.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

private theorem UpperTheory.Reformulated.B.Qk16.left_inv {n : ℕ} (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : UpperTheory.Reformulated.B.Qk16.inUJ ε A) :
    UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = 1 := by
  have h : A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = UpperTheory.Reformulated.B.Qk16.Jm ε := hA
  calc UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A
      = UpperTheory.Reformulated.B.Qk16.Jm ε * (A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, UpperTheory.Reformulated.B.Qk16.Jm_mul_Jm]

theorem UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM :
    ∀ {n : ℕ} (ε : Fin n → Bool), Topology.IsClosedEmbedding fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g := by
  intro n ε
  have hc : Continuous fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g :=
    Units.continuous_val.comp continuous_subtype_val
  refine ⟨?_, ?_⟩
  · let F : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
      fun A ↦ (A, MulOpposite.op (UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε))
    have hF : Continuous F :=
      continuous_id.prodMk (MulOpposite.continuous_op.comp
        ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
    refine Topology.IsEmbedding.of_comp hc hF ?_
    have he : Topology.IsEmbedding
        ((Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘
          (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ)) :=
      Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
    have heq : (F ∘ fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g) =
        ((Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘
          (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ)) := by
      funext g
      have hg : UpperTheory.Reformulated.B.Qk16.inUJ ε (g.1 : Matrix (Fin n) (Fin n) ℂ) := g.2
      have h := Units.inv_eq_of_mul_eq_one_left (UpperTheory.Reformulated.B.Qk16.left_inv ε hg)
      rw [Function.comp_apply, Function.comp_apply, Units.embedProduct_apply, h]
    rw [heq]
    exact he
  · have hr : Set.range (fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g) =
        {A | A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = UpperTheory.Reformulated.B.Qk16.Jm ε} := by
      ext A
      constructor
      · rintro ⟨g, rfl⟩
        exact g.2
      · intro hA
        have h := UpperTheory.Reformulated.B.Qk16.left_inv ε (A := A) hA
        exact ⟨⟨⟨A, _, mul_eq_one_comm.mp h, h⟩, hA⟩, rfl⟩
    rw [hr]
    exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
end

section

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.GlRel.{u_1} :
    {A : Type u_1} → [Ring A] → {n : ℕ} → (Fin n → Fin n → A) → Prop :=
    fun {A : Type u_1} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) ↦
      ∀ (a b c d : Fin n),
        E a b * E c d - E c d * E a b = (if b = c then E a d else (0 : A)) - if d = a then E c b else (0 : A)

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.KUnit :
    {n : ℕ} →
      {V : Type} →
        [inst : NormedAddCommGroup V] →
          [inst_1 : InnerProductSpace ℂ V] → (Fin n → Bool) → (Fin n → Fin n → Module.End ℂ V) → Prop :=
    fun {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
        (E : Fin n → Fin n → Module.End ℂ V) ↦
      ∀ (a b : Fin n), ε a = ε b → ∀ (x y : V), Inner.inner ℂ ((E a b : V → V) x) y = Inner.inner ℂ x ((E b a : V → V) y)

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.KStab :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Bool) → (Fin n → Fin n → Module.End ℂ V) → Submodule ℂ V → Prop :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
        (S : Submodule ℂ V) ↦
      ∀ (a b : Fin n), ε a = ε b → ∀ v ∈ S, (E a b : V → V) v ∈ S

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.IsWeight.{u_1} :
    {V : Type u_1} →
      [inst : AddCommGroup V] →
        [inst_1 : _root_.Module ℂ V] → {n : ℕ} → (Fin n → Fin n → Module.End ℂ V) → (Fin n → ℝ) → V → Prop :=
    fun {V : Type u_1} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ)
        (w : V) ↦
      ∀ (a : Fin n), (E a a : V → V) w = (↑(μ a) : ℂ) • w

theorem UpperTheory.Reformulated.B.WeightsCompactStabilizer.exists_weight :
    ∀ {n : ℕ} {ε : Fin n → Bool} {V : Type} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℂ V]
      {E : Fin n → Fin n → Module.End ℂ V},
      UpperTheory.Reformulated.B.WeightsCompactStabilizer.GlRel E →
        UpperTheory.Reformulated.B.WeightsCompactStabilizer.KUnit ε E →
          ∀ {Q : Submodule ℂ V} [FiniteDimensional ℂ ↥Q],
            UpperTheory.Reformulated.B.WeightsCompactStabilizer.KStab ε E Q → Q ≠ ⊥ → ∃ (ν : Fin n → ℝ), ∃ x ∈ Q, x ≠ (0 : V) ∧ UpperTheory.Reformulated.B.WeightsCompactStabilizer.IsWeight E ν x := by
  intro n ε V _ _ E hG hU Q _ hS hQ
  classical
  let T : Fin n → Module.End ℂ Q := fun a => (E a a).restrict (fun v hv => hS a a rfl v hv)
  have hT : ∀ a (x : Q), ((T a x : Q) : V) = E a a x := fun a x => rfl
  have hsym : ∀ a, (T a).IsSymmetric := by
    intro a x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hT, hT]
    exact hU a a rfl x y
  have hcomm : Pairwise (Function.onFun Commute T) := by
    intro a b hab
    have h := hG a a b b
    rw [if_neg hab, if_neg hab.symm, sub_zero, sub_eq_zero] at h
    change T a * T b = T b * T a
    ext x
    have := congrArg (fun f : Module.End ℂ V => f x) h
    simpa [hT] using this
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  have hex : ∃ α : Fin n → ℂ, (⨅ j, Module.End.eigenspace (T j) (α j)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    rw [iSup_eq_bot.mpr hcon] at htop
    have : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
    exact bot_ne_top htop
  obtain ⟨α, hα⟩ := hex
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  have hx' : ∀ a, x ∈ Module.End.eigenspace (T a) (α a) := fun a =>
    (Submodule.mem_iInf _).mp hx a
  have hre : ∀ a, (((α a).re : ℝ) : ℂ) = α a := fun a =>
    Complex.conj_eq_iff_re.mp
      ((hsym a).conj_eigenvalue_eq_self
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx' a, hx0⟩))
  refine ⟨fun a => (α a).re, x, x.2, fun h => hx0 (Subtype.ext h), fun a => ?_⟩
  have h := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp (hx' a))
  rw [hT] at h
  rw [hre a, h]
  rfl
end

section

noncomputable def UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn.{u_1, u_3} :
    {E : Type u_1} →
      {V : Type u_3} →
        [inst : NormedAddCommGroup E] →
          [NormedSpace ℝ E] → [inst : NormedAddCommGroup V] → [NormedSpace ℝ V] → Set E → (E → V) → Prop :=
    fun {E : Type u_1} {V : Type u_3} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
        (A : Set E) (f : E → V) ↦
      ∀ a ∈ A, ∃ (U : Set E) (F : E → V), IsOpen U ∧ a ∈ U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧ ∀ g ∈ U, g ∈ A → f g = F g

namespace UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers

private lemma smOn_zero {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : Set E) :
    UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (fun _ : E => (0 : V)) := by
  intro a _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

private lemma smOn_add {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Set E} {f g : E → V}
    (hf : UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A f) (hg : UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A g) :
    UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (fun x => f x + g x) := by
  intro a ha
  obtain ⟨U1, F1, hU1, ha1, hF1, he1⟩ := hf a ha
  obtain ⟨U2, F2, hU2, ha2, hF2, he2⟩ := hg a ha
  refine ⟨U1 ∩ U2, fun x => F1 x + F2 x, hU1.inter hU2, ⟨ha1, ha2⟩,
    (hF1.mono Set.inter_subset_left).add (hF2.mono Set.inter_subset_right), ?_⟩
  intro x hx hxA
  simp only [he1 x hx.1 hxA, he2 x hx.2 hxA]

end UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers

open UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers in
theorem UpperTheory.Reformulated.B.SmoothOnAdditive.main.{u_1, u_2, u_3} :
    ∀ {E : Type u_1} {V : Type u_2} {ι : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
      [inst_2 : NormedAddCommGroup V] [inst_3 : NormedSpace ℝ V] {A : Set E} {f : ι → E → V} (s : Finset ι),
      (∀ i ∈ s, UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (f i)) → UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A fun (a : E) ↦ ∑ i ∈ s, f i a := by
  intro E V ι _ _ _ _ A f s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using (smOn_zero (V := V) A)
  | insert j s hj ih =>
    intro h
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := smOn_add h1 h2
    simpa [Finset.sum_insert hj] using this
end

section

open MeasureTheory

private theorem UpperTheory.Reformulated.B.SetIntegralDifferentiability.hasFDerivAt_setIntegral
    {X P E F : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K) {a : X → E} (ha : Continuous a)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : P × E → F)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (p₀ : P) :
    HasFDerivAt (fun p : P ↦ ∫ x in K, Ψ (p, a x) ∂μ)
      (∫ x in K, (fderiv ℝ Ψ (p₀, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ) p₀ := by
  haveI : ProperSpace P := FiniteDimensional.proper_real P
  have hc : Continuous Ψ := hΨ.continuous
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hD : Continuous fun z : P × E ↦
      (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inl ℝ P E) :=
    (hΨ.continuous_fderiv (by simp)).clm_comp continuous_const
  have hcomp : IsCompact (Metric.closedBall p₀ 1 ×ˢ (a '' K)) :=
    (isCompact_closedBall p₀ 1).prod (hK.image ha)
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hD.continuousOn
  have hsec : ∀ p : P, Continuous fun x : X ↦ (p, a x) := fun p ↦ continuous_const.prodMk ha
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p x ↦ Ψ (p, a x))
    (F' := fun p x ↦ (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E))
    (bound := fun _ ↦ C) (s := Metric.closedBall p₀ 1)
    (Metric.closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun p ↦
      ((hc.comp (hsec p)).continuousOn.integrableOn_compact hK).aestronglyMeasurable
  · exact (hc.comp (hsec p₀)).continuousOn.integrableOn_compact hK
  · exact ((hD.comp (hsec p₀)).continuousOn.integrableOn_compact hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx p hp
    exact hC (p, a x) ⟨hp, Set.mem_image_of_mem a hx⟩
  · exact (continuous_const (y := C)).continuousOn.integrableOn_compact hK
  · refine Filter.Eventually.of_forall fun x p _ ↦ ?_
    exact (hd (p, a x)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p (a x))

theorem UpperTheory.Reformulated.B.SetIntegralDifferentiability.contDiff_setIntegral_nat :
    ∀ {X P E : Type} [inst : TopologicalSpace X] [T2Space X]
    [inst_2 : MeasurableSpace X] [BorelSpace X] [inst_4 : NormedAddCommGroup P] [inst_5 : NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [inst_7 : NormedAddCommGroup E] [inst_8 : NormedSpace ℝ E] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasureOnCompacts μ] {K : Set X},
    IsCompact K →
      ∀ {a : X → E},
        Continuous a →
          ∀ (m : ℕ) {F : Type} [inst : NormedAddCommGroup F] [inst_10 : NormedSpace ℝ F] [CompleteSpace F]
            (Ψ : P × E → F),
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ →
              ContDiff ℝ (↑m : WithTop ℕ∞) fun (p : P) ↦ ∫ (x : X) in K, Ψ (p, a x) ∂μ := by
  intro X P E _ _ _ _ _ _ _ _ _ μ _ K hK a ha m
  induction m with
  | zero =>
    intro F _ _ _ Ψ hΨ
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun p ↦
      (UpperTheory.Reformulated.B.SetIntegralDifferentiability.hasFDerivAt_setIntegral μ hK ha Ψ hΨ p).continuousAt
  | succ n ih =>
    intro F _ _ _ Ψ hΨ
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z : P × E ↦
        (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inl ℝ P E) :=
      (contDiff_infty_iff_fderiv.1 hΨ).2.clm_comp contDiff_const
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    exact ⟨_, ih _ hD, fun p ↦ UpperTheory.Reformulated.B.SetIntegralDifferentiability.hasFDerivAt_setIntegral μ hK ha Ψ hΨ p⟩
end

section

namespace EqOneOfPowersNearOne

private lemma key {R : Type} [NormedRing R] [NormedAlgebra ℂ R] {a : R}
    (h : ∀ (p : ℕ), ‖a ^ p - (1 : R)‖ < (1 / 2 : ℝ)) (N : ℕ) :
    (N : ℝ) * ‖a - 1‖ < ‖a - 1‖ * (N / 2) + 1 / 2 := by
  set S : R := ∑ k ∈ Finset.range N, a ^ k with hS
  have hgeom : S * (a - 1) = a ^ N - 1 := geom_sum_mul a N
  have hdiff : (N : R) - S = ∑ k ∈ Finset.range N, ((1 : R) - a ^ k) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hbound : ‖(N : R) - S‖ ≤ N / 2 := by
    rw [hdiff]
    calc ‖∑ k ∈ Finset.range N, ((1 : R) - a ^ k)‖
        ≤ ∑ k ∈ Finset.range N, ‖(1 : R) - a ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range N, (1 / 2 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_sub_rev]; exact (h k).le
      _ = N / 2 := by simp; ring
  have hnorm : ‖(N : R) * (a - 1)‖ = (N : ℝ) * ‖a - 1‖ := by
    have : (N : R) * (a - 1) = (N : ℂ) • (a - 1) := by
      rw [Algebra.smul_def]; simp
    rw [this, norm_smul]; simp
  have hsplit : (N : R) * (a - 1) = ((N : R) - S) * (a - 1) + S * (a - 1) := by
    rw [sub_mul]; abel
  calc (N : ℝ) * ‖a - 1‖ = ‖(N : R) * (a - 1)‖ := hnorm.symm
    _ ≤ ‖((N : R) - S) * (a - 1)‖ + ‖S * (a - 1)‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖(N : R) - S‖ * ‖a - 1‖ + ‖a ^ N - 1‖ := by
        rw [hgeom]; gcongr; exact norm_mul_le _ _
    _ < ‖a - 1‖ * (N / 2) + 1 / 2 := by
        have := h N
        nlinarith [norm_nonneg (a - 1)]

end EqOneOfPowersNearOne

theorem UpperTheory.Reformulated.B.Yhd7.main :
    ∀ {R : Type} [inst : NormedRing R] [NormedAlgebra ℂ R] {a : R},
      (∀ (p : ℕ), ‖a ^ p - (1 : R)‖ < (1 / 2 : ℝ)) → a = (1 : R) := by
  intro R _ _ a h
  by_contra hne
  have hpos : 0 < ‖a - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖a - 1‖)
  have hk := EqOneOfPowersNearOne.key h N
  have h1 : 1 < (N : ℝ) * ‖a - 1‖ := by
    rw [div_lt_iff₀ hpos] at hN; linarith
  nlinarith
end

section

theorem UpperTheory.Reformulated.B.Rc4.exists_bound_poly_mul_exp :
    ∀ (c : ℝ),
    (0 : ℝ) < c →
      ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r → ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : (1 + r) ^ N ≤ Real.exp r ^ N := by
    apply pow_le_pow_left₀ (by linarith)
    linarith [Real.add_one_le_exp r]
  have h2 : (N : ℝ) * r + -(c * r ^ 2) ≤ (N : ℝ) ^ 2 / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((N : ℝ) - 2 * c * r)]
  calc (1 + r) ^ N * Real.exp (-(c * r ^ 2))
      ≤ Real.exp r ^ N * Real.exp (-(c * r ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ 2)) := by
        rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := Real.exp_le_exp.mpr h2
end

section

theorem UpperTheory.Reformulated.B.Rd2.exists_bound_poly_mul_exp :
    ∀ (c : ℝ),
    (0 : ℝ) < c →
      ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r → ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : (1 + r) ^ N ≤ Real.exp ((N : ℝ) * r) := by
    rw [Real.exp_nat_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    linarith [Real.add_one_le_exp r]
  have h2 : (N : ℝ) * r + -(c * r ^ 2) ≤ (N : ℝ) ^ 2 / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((N : ℝ) - 2 * c * r)]
  calc (1 + r) ^ N * Real.exp (-(c * r ^ 2))
      ≤ Real.exp ((N : ℝ) * r) * Real.exp (-(c * r ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ 2)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := Real.exp_le_exp.mpr h2
end

section

theorem UpperTheory.Reformulated.B.Qi18.norm_pow_sub_pow_le.{u_1} :
    ∀ {K : Type u_1} [inst : NormedField K]
    [IsUltrametricDist K] (x y : K), ‖x‖ ≤ (1 : ℝ) → ‖y‖ ≤ (1 : ℝ) → ∀ (e : ℕ), ‖x ^ e - y ^ e‖ ≤ ‖x - y‖ := by
  intro K _ _ x y hx hy e
  induction e with
  | zero => simp
  | succ n ih =>
    have h : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans ih
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)
end
