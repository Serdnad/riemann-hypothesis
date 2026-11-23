module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Algebra.Order.Round

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem entries_bounded_of_conj_spanning_bounded :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), Submodule.span ℂ (Set.range g) = ⊤ → ∀ C : ℝ, ∃ C' : ℝ, ∀ P : Matrix ι ι ℂ, P.det = 1 → (∀ s i j, ‖(P * g s * P⁻¹) i j‖ ≤ C) → ∀ i j, ‖P i j‖ ≤ C' := by
  intro ι _ _ σ _ g hg C
  have hmem : ∀ k l : ι, ∃ a : σ → ℂ, ∑ s, a s • g s = Matrix.single k l (1 : ℂ) := by
    intro k l
    have : Matrix.single k l (1 : ℂ) ∈ Submodule.span ℂ (Set.range g) := by
      rw [hg]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).1 this
  choose a ha using hmem
  set C₁ : ℝ := ∑ k, ∑ l, ∑ s, ‖a k l s‖ * |C| with hC₁
  refine ⟨max 1 ((Nat.factorial (Fintype.card ι)) • C₁ ^ Fintype.card ι), ?_⟩
  intro P hP hb i k
  have hent : ∀ l j, ‖P i k * P⁻¹ l j‖ ≤ C₁ := by
    intro l j
    have h1 : P i k * P⁻¹ l j = ∑ s, a k l s * (P * g s * P⁻¹) i j := by
      have h2 : (P * Matrix.single k l (1 : ℂ) * P⁻¹) i j = P i k * P⁻¹ l j := by
        simp [Matrix.mul_apply, Matrix.single, ite_and]
      rw [← h2, ← ha k l, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    have h3 : ‖P i k * P⁻¹ l j‖ ≤ ∑ s, ‖a k l s‖ * |C| := by
      rw [h1]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((hb s i j).trans (le_abs_self C)) (norm_nonneg _)
    refine h3.trans ?_
    calc ∑ s, ‖a k l s‖ * |C| ≤ ∑ l, ∑ s, ‖a k l s‖ * |C| :=
          Finset.single_le_sum (f := fun l => ∑ s, ‖a k l s‖ * |C|)
            (fun l _ => by positivity) (Finset.mem_univ l)
      _ ≤ C₁ :=
          Finset.single_le_sum (f := fun k => ∑ l, ∑ s, ‖a k l s‖ * |C|)
            (fun k _ => by positivity) (Finset.mem_univ k)
  have hdetinv : (P⁻¹).det = 1 := by
    rw [Matrix.det_nonsing_inv, hP]; simp
  have hdet := Matrix.det_le (A := P i k • P⁻¹) (abv := NormedField.toAbsoluteValue ℂ) (x := C₁)
    (fun l j => hent l j)
  rw [Matrix.det_smul, hdetinv, mul_one] at hdet
  have hdet' : ‖P i k‖ ^ Fintype.card ι ≤
      (Nat.factorial (Fintype.card ι)) • C₁ ^ Fintype.card ι := by
    rw [← norm_pow]; exact hdet
  have hN : Fintype.card ι ≠ 0 := (Fintype.card_pos_iff.2 ⟨i⟩).ne'
  rcases le_total ‖P i k‖ 1 with h | h
  · exact h.trans (le_max_left _ _)
  · exact ((le_self_pow₀ h hN).trans hdet').trans (le_max_right _ _)

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {V : Type} [AddCommGroup V] [Module ℂ V] in
private lemma projection_comm_of_mapsTo {p q : Submodule ℂ V} (h : IsCompl p q)
    (T : V →ₗ[ℂ] V) (hp : ∀ v ∈ p, T v ∈ p) (hq : ∀ v ∈ q, T v ∈ q) (v : V) :
    p.projection q h (T v) = T (p.projection q h v) := by
  have hv : v ∈ p ⊔ q := by
    rw [h.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have e1 := (Submodule.IsCompl.projection_eq_self_iff h a).mpr ha
  have e2 := (Submodule.IsCompl.projection_eq_self_iff h (T a)).mpr (hp a ha)
  have e3 := (Submodule.IsCompl.projection_apply_eq_zero_iff h).mpr hb
  have e4 := (Submodule.IsCompl.projection_apply_eq_zero_iff h).mpr (hq b hb)
  simp only [map_add (f := _), e1, e2, e3, e4, add_zero]

variable {V : Type} [AddCommGroup V] [Module ℂ V] in
private lemma sub_projection_mem' {p q : Submodule ℂ V} (h : IsCompl p q) (v : V) :
    v - p.projection q h v ∈ q := by
  rw [← Submodule.IsCompl.projection_apply_eq_zero_iff h, map_sub,
    (Submodule.IsCompl.projection_eq_self_iff h _).mpr
      (Submodule.IsCompl.projection_apply_mem h v), sub_self]


variable {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible (V : Type) [AddCommGroup V] [Module ℂ V]
    (S : Set (V →ₗ[ℂ] V)) :
    (∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, (s : V → V) v ∈ U) →
      ∃ U' : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U', (s : V → V) v ∈ U') ∧ IsCompl U U') →
    ∃ Rey : V →ₗ[ℂ] V,
      (∀ v : V, ∀ s ∈ S, (s : V → V) ((Rey : V → V) v) = (Rey : V → V) v) ∧
      (∀ v : V, (∀ s ∈ S, (s : V → V) v = v) → (Rey : V → V) v = v) ∧
      (∀ v : V, ∀ s ∈ S, (Rey : V → V) ((s : V → V) v) = (Rey : V → V) v) ∧
      (∀ v : V, v - (Rey : V → V) v ∈
        Submodule.span ℂ {x : V | ∃ s ∈ S, ∃ w : V, x = (s : V → V) w - w}) ∧
      (∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v : V, (T : V → V) ((s : V → V) v) = (s : V → V) ((T : V → V) v)) →
        ∀ v : V, (Rey : V → V) ((T : V → V) v) = (T : V → V) ((Rey : V → V) v)) ∧
      ∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, (s : V → V) v ∈ U) →
        ∀ v ∈ U, (Rey : V → V) v ∈ U := by
  intro hS
  let W : Submodule ℂ V := Submodule.span ℂ {x : V | ∃ s ∈ S, ∃ w : V, x = (s : V → V) w - w}
  have hWgen : ∀ s ∈ S, ∀ w, (s : V → V) w - w ∈ W := fun s hs w =>
    Submodule.subset_span ⟨s, hs, w, rfl⟩
  have hWT : ∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v ∈ W, T v ∈ W := by
    intro T hT v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, hs, w, rfl⟩ := hx
      rw [map_sub, hT s hs]
      exact hWgen s hs (T w)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact W.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact W.smul_mem a hx
  have hWS : ∀ s ∈ S, ∀ v ∈ W, (s : V → V) v ∈ W := by
    intro s hs v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s', hs', w, rfl⟩ := hx
      have e : s (s' w - w) = (s (s' w) - s' w) + (s' w - w) - (s w - w) := by
        rw [map_sub]
        abel
      rw [e]
      exact W.sub_mem (W.add_mem (hWgen s hs _) (hWgen s' hs' w)) (hWgen s hs w)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact W.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact W.smul_mem a hx
  let Fix : Submodule ℂ V :=
    { carrier := {x | ∀ s ∈ S, (s : V → V) x = x}
      add_mem' := fun ha hb s hs => by simp [map_add (f := _), ha s hs, hb s hs]
      zero_mem' := fun s _ => map_zero s
      smul_mem' := fun c x hx s hs => by simp [map_smul, hx s hs] }
  have hFixW : ∀ v ∈ Fix, v ∈ W → v = 0 := by
    intro v hvF hvW
    have hZS : ∀ s ∈ S, ∀ x ∈ Fix ⊓ W, (s : V → V) x ∈ Fix ⊓ W := by
      intro s hs x hx
      rw [hx.1 s hs]
      exact hx
    obtain ⟨Z', hZ'S, hZZ'⟩ := hS (Fix ⊓ W) hZS
    let Q := (Fix ⊓ W).projection Z' hZZ'
    have hQS : ∀ s ∈ S, ∀ x, Q (s x) = s (Q x) := fun s hs x =>
      projection_comm_of_mapsTo hZZ' s (hZS s hs) (hZ'S s hs) x
    have hQW : W ≤ LinearMap.ker Q := by
      rw [Submodule.span_le]
      rintro _ ⟨s, hs, w, rfl⟩
      have hmem := Submodule.IsCompl.projection_apply_mem hZZ' w
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hQS s hs, Q]
      rw [hmem.1 s hs, sub_self]
    have h1 : Q v = v := (Submodule.IsCompl.projection_eq_self_iff hZZ' v).mpr ⟨hvF, hvW⟩
    have h2 : Q v = 0 := hQW hvW
    rw [← h1, h2]
  obtain ⟨W', hW'S, hWW'⟩ := hS W hWS
  have hW'Fix : ∀ v ∈ W', v ∈ Fix := by
    intro v hv s hs
    have h1 : (s : V → V) v - v ∈ W := hWgen s hs v
    have h2 : (s : V → V) v - v ∈ W' := W'.sub_mem (hW'S s hs v hv) hv
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hWW'.disjoint _ h1 h2)
  let P := W'.projection W hWW'.symm
  have hPfix : ∀ v ∈ Fix, P v = v := by
    intro v hv
    have hd : v - P v ∈ Fix := Fix.sub_mem hv (hW'Fix _ (Submodule.IsCompl.projection_apply_mem _ v))
    exact (sub_eq_zero.mp (hFixW _ hd (sub_projection_mem' hWW'.symm v))).symm
  have hPT : ∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v, P (T v) = T (P v) := by
    intro T hT v
    refine projection_comm_of_mapsTo hWW'.symm T (fun x hx => ?_) (hWT T hT) v
    have hTx : T x ∈ Fix := fun s hs => by rw [← hT s hs, hW'Fix x hx s hs]
    rw [← hPfix _ hTx]
    exact Submodule.IsCompl.projection_apply_mem _ _
  refine ⟨P, fun v s hs => hW'Fix _ (Submodule.IsCompl.projection_apply_mem _ v) s hs,
    fun v hv => hPfix v hv, fun v s hs => ?_, fun v => sub_projection_mem' hWW'.symm v,
    hPT, fun U hU v hv => ?_⟩
  · have h0 : P ((s : V → V) v - v) = 0 :=
      (Submodule.IsCompl.projection_apply_eq_zero_iff _).mpr (hWgen s hs v)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  · obtain ⟨U', hU'S, hUU'⟩ := hS U hU
    let Q := U.projection U' hUU'
    have hQ : ∀ s ∈ S, ∀ x, Q (s x) = s (Q x) := fun s hs x =>
      projection_comm_of_mapsTo hUU' s (hU s hs) (hU'S s hs) x
    have hQv : Q v = v := (Submodule.IsCompl.projection_eq_self_iff hUU' v).mpr hv
    have e := hPT Q hQ v
    rw [hQv] at e
    rw [e]
    exact Submodule.IsCompl.projection_apply_mem hUU' _

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open scoped MonoidAlgebra

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
open scoped MonoidAlgebra in
private theorem subalgebra_end_eq_whole_of_isSimpleModule {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSimpleModule A V] :
    A = ⊤ := by
  classical
  have schur : ∀ f : V →ₗ[A] V, ∃ c : ℂ, ∀ y, f y = c • y := by
    intro f
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) ℂ).2 f
    exact ⟨c, fun y => by rw [← hc]; rfl⟩
  let b := Module.finBasis ℂ V
  let ι := Fin (Module.finrank ℂ V)
  let N : Submodule A (ι → V) := Submodule.span A {fun i => b i}
  obtain ⟨W, hW⟩ := exists_isCompl N
  let P : (ι → V) →ₗ[A] (ι → V) := N.subtype.comp (Submodule.linearProjOfIsCompl N W hW)
  have hPN : ∀ x, P x ∈ N := fun x => (Submodule.linearProjOfIsCompl N W hW x).2
  have hPfix : ∀ x ∈ N, P x = x := fun x hx => by
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hW ⟨x, hx⟩)
  have hcomm : ∀ (T : Module.End ℂ V) (x : ι → V), P (fun i => T (x i)) = fun i => T (P x i) := by
    intro T x
    have hsingle : ∀ (i j : ι) (y : V), P (Pi.single j (T y)) i = T (P (Pi.single j y) i) := by
      intro i j y
      obtain ⟨c, hc⟩ := schur ((LinearMap.proj i).comp (P.comp (LinearMap.single A (fun _ : ι => V) j)))
      have h1 := hc (T y)
      have h2 := hc y
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply] at h1 h2
      rw [h1, h2, map_smul]
    funext i

    conv_lhs => rw [← Finset.univ_sum_single (fun i => T (x i)), map_sum]

    conv_rhs => rw [← Finset.univ_sum_single x, map_sum]

    simp only [Finset.sum_apply, map_sum, hsingle]
  ext T
  simp only [Algebra.mem_top, iff_true]
  have hmem : (fun i => T (b i)) ∈ N := by
    have hfix : P (fun i => T (b i)) = fun i => T (b i) := by
      rw [hcomm T (fun i => b i), hPfix _ (Submodule.mem_span_singleton_self _)]
    rw [← hfix]
    exact hPN _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  have hT : T = (a : Module.End ℂ V) := by
    refine b.ext fun i => ?_
    have := congrFun ha i
    exact this.symm
  rw [hT]
  exact a.2


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
open scoped MonoidAlgebra in
theorem _root_.GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) [FiniteDimensional ℂ V], ρ.IsIrreducible → Submodule.span ℂ (Set.range ρ) = ⊤ := by
  intro G _ V _ _ ρ _ h
  let A : Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range ρ)
  have hρA : ∀ g, ρ g ∈ A := fun g => Algebra.subset_adjoin ⟨g, rfl⟩
  have hspan : Subalgebra.toSubmodule A = Submodule.span ℂ (Set.range ρ) := by
    rw [Algebra.adjoin_eq_span]
    congr 1
    have : Set.range ρ = ((MonoidHom.mrange ρ : Submonoid (Module.End ℂ V)) : Set (Module.End ℂ V)) :=
      (MonoidHom.coe_mrange ρ).symm
    rw [this, Submonoid.closure_eq]
  let φ : Submodule A V → Subrepresentation ρ := fun M =>
    ⟨M.restrictScalars ℂ, fun g v hv => M.smul_mem (⟨ρ g, hρA g⟩ : A) hv⟩
  haveI : IsSimpleModule A V := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun M => ?_ }
    · obtain ⟨S, S', hS'⟩ := h.exists_pair_ne
      have hzero : ∀ x : V, x = 0 := fun x => by
        have : x ∈ (⊤ : Submodule A V) := Submodule.mem_top
        rw [← hbt] at this
        exact (Submodule.mem_bot A).1 this
      have hall : ∀ T U : Subrepresentation ρ, T = U := fun T U => by
        apply Subrepresentation.ext
        ext x
        rw [hzero x]
        exact ⟨fun _ => U.toSubmodule.zero_mem, fun _ => T.toSubmodule.zero_mem⟩
      exact hS' (hall S S')
    · rcases h.eq_bot_or_eq_top (φ M) with hM | hM
      · left
        have := congrArg Subrepresentation.toSubmodule hM
        exact (Submodule.restrictScalars_eq_bot_iff ℂ A V).1 this
      · right
        have := congrArg Subrepresentation.toSubmodule hM
        exact (Submodule.restrictScalars_eq_top_iff ℂ A V).1 this
  rw [← hspan, subalgebra_end_eq_whole_of_isSimpleModule A]
  ext x
  simp

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem isNilpotent_of_forall_algHom_eq_zero (T : Type) [CommRing T] [Algebra ℂ T]
    [Algebra.FiniteType ℂ T] (x : T) (h : ∀ ω : T →ₐ[ℂ] ℂ, ω x = 0) : IsNilpotent x := by
  have hJ : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := ℂ)
  have h1 : x ∈ Ideal.jacobson (⊥ : Ideal T) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    let := Ideal.Quotient.field m
    have hfin : Module.Finite ℂ (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (T ⧸ m)
    have hb : Function.Bijective (algebraMap ℂ (T ⧸ m)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : ℂ ≃ₐ[ℂ] (T ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ m)) hb
    have := h ((e.symm : (T ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m))
    have h0 : e.symm (Ideal.Quotient.mk m x) = 0 := this
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ e.symm.injective).mp h0)
  have h2 : x ∈ Ideal.radical (⊥ : Ideal T) := by
    have := IsJacobsonRing.out hJ (Ideal.radical_isRadical (⊥ : Ideal T))
    rw [← this]
    exact Ideal.jacobson_mono Ideal.le_radical h1
  exact h2

theorem isNilpotent_tmul_sub_tmul_of_const_on_fibres :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A] [Algebra.FiniteType ℂ A] (f : A), (∀ χ χ' : A →ₐ[ℂ] ℂ, (∀ b : B, χ (algebraMap B A b) = χ' (algebraMap B A b)) → χ f = χ' f) → IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f) := by
  intro B A _ _ _ _ _ _ _ f h
  have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A
  have : Algebra.FiniteType A (A ⊗[B] A) := inferInstance
  have : Algebra.FiniteType ℂ (A ⊗[B] A) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  apply isNilpotent_of_forall_algHom_eq_zero
  intro ω
  let l : A →ₐ[ℂ] A ⊗[B] A := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[ℂ] A ⊗[B] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).restrictScalars ℂ
  have := h (ω.comp l) (ω.comp r) (fun b => by
    simp only [AlgHom.comp_apply, l, r, Algebra.TensorProduct.includeLeft_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])
  rw [map_sub, sub_eq_zero]
  exact this

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem unipotent_size_reduction_column {N : ℕ} (n : Matrix (Fin N) (Fin N) ℝ)
    (h1 : ∀ i, n i i = 1) (h0 : ∀ i j, j < i → n i j = 0) (j : Fin N) (k : ℕ) :
    ∃ z : Fin N → ℤ, z j = 1 ∧ (∀ l, j < l → z l = 0) ∧
      ∀ i, i < j → (j : ℕ) ≤ i + k → |∑ l, n i l * (z l : ℝ)| ≤ 1 / 2 := by
  induction k with
  | zero =>
    refine ⟨Pi.single j 1, by simp, fun l hl => by simp [Pi.single_apply, hl.ne'], ?_⟩
    intro i hi hk
    exact absurd hk (by have : (i : ℕ) < j := hi; omega)
  | succ k ih =>
    obtain ⟨z, hz1, hz0, hz⟩ := ih
    by_cases hk : k + 1 ≤ (j : ℕ)
    · let i0 : Fin N := ⟨j - (k + 1), by have := j.2; omega⟩
      have hi0v : (i0 : ℕ) = j - (k + 1) := rfl
      have hi0 : i0 < j := by
        show (i0 : ℕ) < j
        omega
      set c : ℤ := -round (∑ l, n i0 l * (z l : ℝ)) with hc
      have key : ∀ i, ∑ l, n i l * (((z + Pi.single i0 c : Fin N → ℤ) l : ℤ) : ℝ)
          = ∑ l, n i l * (z l : ℝ) + n i i0 * c := by
        intro i
        simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single i0]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · simp
      refine ⟨z + Pi.single i0 c, ?_, ?_, ?_⟩
      · simp [Pi.single_apply, hi0.ne', hz1]
      · intro l hl
        simp [Pi.single_apply, (hi0.trans hl).ne', hz0 l hl]
      · intro i hi hik
        rw [key]
        by_cases h : i = i0
        · subst h
          rw [h1, one_mul, hc, Int.cast_neg, ← sub_eq_add_neg]
          exact abs_sub_round _
        · have hne : (i : ℕ) ≠ i0 := fun e => h (Fin.ext e)
          have hlt : i0 < i := by
            show (i0 : ℕ) < i
            omega
          rw [h0 i i0 hlt, zero_mul, add_zero]
          exact hz i hi (by omega)
    · exact ⟨z, hz1, hz0, fun i hi _ => hz i hi (by omega)⟩

theorem unipotent_size_reduction :
    ∀ (N : ℕ) (n : Matrix (Fin N) (Fin N) ℝ), (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) →
      ∃ ν : Matrix (Fin N) (Fin N) ℤ, (∀ i, ν i i = 1) ∧ (∀ i j, j < i → ν i j = 0) ∧
        ∀ i j, i < j → |(n * ν.map (Int.cast : ℤ → ℝ)) i j| ≤ 1 / 2 := by
  intro N n h1 h0
  choose z hz1 hz0 hz using fun j => unipotent_size_reduction_column n h1 h0 j N
  refine ⟨Matrix.of fun i j => z j i, fun i => hz1 i, fun i j h => hz0 j i h, ?_⟩
  intro i j hij
  rw [Matrix.mul_apply]
  exact hz j i hij (by have := j.2; omega)

end GlobalTheory.ClassFin
end
