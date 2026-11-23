module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.MeasureTheory.Group.FundamentalDomain
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

namespace GlobalTheory

open Representation

theorem intertwiner_sum_eq_zero_imp {G : Type} [Group G] {N X : Type} [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hirr : π.IsIrreducible)
    (hschur : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) :
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
      ∀ w : Fin m → N, ∑ j, φ j (w j) = 0 → w = 0 := by
  intro m
  induction m with
  | zero => intro φ _ w _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro φ hφ
    let Φ : (Fin (m+1) → N) →ₗ[ℂ] X := ∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j
    have hΦ : ∀ w, Φ w = ∑ j, φ j (w j) := by intro w; simp [Φ, LinearMap.sum_apply]
    let K := LinearMap.ker Φ
    have hK : ∀ w, w ∈ K ↔ ∑ j, φ j (w j) = 0 := by intro w; simp [K, hΦ]
    have hφ' : LinearIndependent ℂ (fun j : Fin m => φ j.castSucc) :=
      hφ.comp _ (Fin.castSucc_injective m)
    have claimA : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) = 0 → w = 0 := by
      intro w hw hl
      rw [Fin.sum_univ_castSucc, hl, map_zero, add_zero] at hw
      have := ih _ hφ' (fun j => w j.castSucc) hw
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hl
      · exact congrFun this j
    have hstable : ∀ (g : G) (w : Fin (m+1) → N), ∑ j, φ j (w j) = 0 →
        ∑ j, φ j (π g (w j)) = 0 := by
      intro g w hw
      simp_rw [IntertwiningMap.isIntertwining]

      rw [← map_sum, hw, map_zero]
    let P : Subrepresentation π :=
      { toSubmodule := K.map (LinearMap.proj (Fin.last m))
        apply_mem_toSubmodule := by
          rintro g _ ⟨w, hw, rfl⟩
          refine ⟨fun j => π g (w j), ?_, rfl⟩
          rw [SetLike.mem_coe, hK] at hw ⊢
          exact hstable g w hw }
    have hmemP : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) ∈ P := fun w hw =>
      show w (Fin.last m) ∈ K.map (LinearMap.proj (Fin.last m)) from ⟨w, (hK w).2 hw, rfl⟩
    rcases hirr.eq_bot_or_eq_top P with hP | hP
    · intro w hw
      apply claimA w hw
      have := hmemP w hw
      rw [hP] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exfalso
      have hsurj : ∀ n : N, ∃ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 ∧ w (Fin.last m) = n := by
        intro n
        have : n ∈ P := by rw [hP]; exact Submodule.mem_top
        obtain ⟨w, hw, rfl⟩ := (show n ∈ K.map (LinearMap.proj (Fin.last m)) from this)
        exact ⟨w, (hK w).1 hw, rfl⟩
      have huniq : ∀ w w' : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → ∑ j, φ j (w' j) = 0 →
          w (Fin.last m) = w' (Fin.last m) → w = w' := by
        intro w w' hw hw' hl
        have := claimA (w - w') (by simp [map_sub, Finset.sum_sub_distrib, hw, hw'])
          (by simp [hl])
        exact sub_eq_zero.mp this
      let p : K →ₗ[ℂ] N := LinearMap.proj (Fin.last m) ∘ₗ K.subtype
      have hp : Function.Bijective p := by
        constructor
        · intro a b hab
          exact Subtype.ext (huniq a.1 b.1 ((hK _).1 a.2) ((hK _).1 b.2) hab)
        · intro n
          obtain ⟨w, hw, hl⟩ := hsurj n
          exact ⟨⟨w, (hK w).2 hw⟩, hl⟩
      let e := LinearEquiv.ofBijective p hp
      let s : N →ₗ[ℂ] (Fin (m+1) → N) := K.subtype ∘ₗ e.symm.toLinearMap
      have hsK : ∀ n, ∑ j, φ j (s n j) = 0 := fun n => (hK _).1 (e.symm n).2
      have hsl : ∀ n, s n (Fin.last m) = n := fun n => e.apply_symm_apply n
      have hsg : ∀ (g : G) (n : N), s (π g n) = fun j => π g (s n j) := by
        intro g n
        apply huniq _ _ (hsK _) (hstable g _ (hsK n))
        simp only [hsl]
      have hc : ∀ j : Fin m, ∃ c : ℂ, ∀ n, s n j.castSucc = c • n := by
        intro j
        let f : π.IntertwiningMap π :=
          { toLinearMap := LinearMap.proj j.castSucc ∘ₗ s
            isIntertwining' := by
              intro g; ext n; simp [hsg] }
        obtain ⟨c, hc⟩ := hschur f
        refine ⟨c, fun n => ?_⟩
        have := congrArg (fun L => L n) hc
        simpa [f] using this
      choose c hc using hc
      have hrel : ∑ j : Fin m, c j • φ j.castSucc + φ (Fin.last m) = 0 := by
        ext n
        have := hsK n
        rw [Fin.sum_univ_castSucc] at this
        simp only [hc, hsl, map_smul] at this
        simpa [IntertwiningMap.sum_apply] using this
      have := (Fintype.linearIndependent_iff.mp hφ) (Fin.snoc c 1) (by
        rw [Fin.sum_univ_castSucc]; simpa using hrel)
      have h1 := this (Fin.last m)
      simp at h1

theorem intertwiners_indep_injective : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible →
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
    Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) := by
  intro G _ N X _ _ _ _ π ρ hirr hschur m φ hφ a b hab
  have := intertwiner_sum_eq_zero_imp π ρ hirr hschur m φ hφ (a - b)
    (by simpa [map_sub, Finset.sum_sub_distrib, sub_eq_zero] using hab)
  exact sub_eq_zero.mp this

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory.MultilinFubini

theorem aestronglyMeasurable_pi_of_forall {α : Type*} {m0 : MeasurableSpace α} {ν : Measure α}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    {f : ∀ i, α → E i} (hf : ∀ i, AEStronglyMeasurable (f i) ν) :
    AEStronglyMeasurable (fun x i => f i x) ν := by
  have key : ∀ s : Finset ι,
      AEStronglyMeasurable (fun x (i : ι) => if i ∈ s then f i x else 0) ν := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, if_false]; exact aestronglyMeasurable_const
    | insert a s ha ih =>
      have hc : Continuous (fun p : E a × (∀ i, E i) => Function.update p.2 a p.1) :=
        continuous_snd.update a continuous_fst
      refine (hc.comp_aestronglyMeasurable ((hf a).prodMk ih)).congr (ae_of_all _ fun x => ?_)
      funext i
      by_cases hi : i = a
      · subst hi; simp
      · simp [Function.update_of_ne hi, hi]
  simpa using key Finset.univ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
  {E : ι → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

def vecOn (g : ∀ i, X i → E i) (s : Finset ι) (m : ∀ i, E i) (x : ∀ i : s, X i) : ∀ i, E i :=
  fun i => if h : i ∈ s then g i (x ⟨i, h⟩) else m i

theorem integrable_vecOn (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i) (hg : ∀ i, Integrable (g i) (μ i))
    (s : Finset ι) (m : ∀ i, E i) :
    Integrable (fun x => Φ (vecOn g s m x)) (Measure.pi fun i : s => μ i) := by
  have hmeas : AEStronglyMeasurable (fun x => vecOn g s m x) (Measure.pi fun i : s => μ i) := by
    refine aestronglyMeasurable_pi_of_forall (f := fun i x => vecOn g s m x i) fun i => ?_
    by_cases hi : i ∈ s
    · simp only [vecOn, dif_pos hi]
      exact (hg i).1.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun j : s => μ j) ⟨i, hi⟩)
    · simp only [vecOn, dif_neg hi]; exact aestronglyMeasurable_const
  have hdom : Integrable (fun x : ∀ j : s, X j => ‖Φ‖ * ((∏ j : s, ‖g j (x j)‖) * ∏ i ∈ sᶜ, ‖m i‖))
      (Measure.pi fun i : s => μ i) :=
    ((Integrable.fintype_prod_dep (f := fun (j : s) (y : X j) => ‖g j y‖)
      fun j => (hg j).norm).mul_const _).const_mul _
  refine hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => ?_)
  refine (Φ.le_opNorm _).trans (le_of_eq ?_)
  congr 1
  rw [← Finset.prod_mul_prod_compl s]
  congr 1
  · rw [← Finset.prod_coe_sort s]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [vecOn, j.2]
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp [vecOn, Finset.mem_compl.1 hi]

theorem integral_vecOn (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, CompleteSpace (E i)] [CompleteSpace F]
    (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i) (hg : ∀ i, Integrable (g i) (μ i))
    (s : Finset ι) : ∀ m : ∀ i, E i,
    ∫ x, Φ (vecOn g s m x) ∂(Measure.pi fun i : s => μ i) =
      Φ (fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro m
    rw [Measure.pi_of_empty (x := fun i => isEmptyElim i)]
    have hc : (fun x : ∀ i : (∅ : Finset ι), X i => Φ (vecOn g ∅ m x)) = fun _ => Φ m := by
      funext x; congr 1
    rw [hc]; simp
  | insert a s ha ih =>
    intro m
    rw [Finset.insert_eq]
    have hd : Disjoint ({a} : Finset ι) s := Finset.disjoint_singleton_left.2 ha
    have hmp := measurePreserving_piFinsetUnion hd μ
    letI : Unique ↥({a} : Finset ι) :=
      ⟨⟨⟨a, Finset.mem_singleton_self a⟩⟩, fun j => Subtype.ext (Finset.mem_singleton.1 j.2)⟩
    have hpt : ∀ p : (∀ i : ({a} : Finset ι), X i) × (∀ i : s, X i),
        vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p) =
          vecOn g s (Function.update m a (g a (p.1 default))) p.2 := by
      rintro ⟨y, z⟩
      have he : (MeasurableEquiv.piFinsetUnion X hd (y, z) : ∀ i : ↥({a} ∪ s), X i) =
          Equiv.piFinsetUnion X hd (y, z) := rfl
      funext i
      by_cases hia : i = a
      · subst hia
        have h1 : i ∈ ({i} : Finset ι) ∪ s := by simp
        simp only [vecOn, dif_pos h1, dif_neg ha, Function.update_self, he]
        rw [Equiv.piFinsetUnion_left X hd (Finset.mem_singleton_self i)]
        rfl
      · by_cases his : i ∈ s
        · have h1 : i ∈ ({a} : Finset ι) ∪ s := by simp [his]
          simp only [vecOn, dif_pos h1, dif_pos his, he]
          rw [Equiv.piFinsetUnion_right X hd his]
        · have h1 : i ∉ ({a} : Finset ι) ∪ s := by simp [his, hia]
          simp only [vecOn, dif_neg h1, dif_neg his, Function.update_of_ne hia]
    have hint : Integrable (fun p => Φ (vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p)))
        ((Measure.pi fun i : ({a} : Finset ι) => μ i).prod (Measure.pi fun i : s => μ i)) :=
      (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2
        (integrable_vecOn μ Φ g hg _ m)
    rw [← hmp.integral_comp', integral_prod _ hint]
    simp only [hpt, ih]
    set w : ∀ i, E i := fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i with hw
    have hupd : ∀ c : E a, (fun i => if i ∈ s then ∫ y, g i y ∂μ i else Function.update m a c i) =
        Function.update w a c := by
      intro c; funext i
      by_cases hia : i = a
      · subst hia; simp [hw, ha]
      · by_cases his : i ∈ s
        · simp [hw, his, Function.update_of_ne hia]
        · simp [hw, his, Function.update_of_ne hia]
    simp only [hupd]
    have hL : ∀ c : E a, Φ (Function.update w a c) = Φ.toContinuousLinearMap w a c := fun c => rfl
    simp only [hL]
    have h1 := (measurePreserving_piUnique (fun i : ({a} : Finset ι) => μ i)).integral_comp'
      (fun t => Φ.toContinuousLinearMap w a (g a t))
    rw [show (∫ x : ∀ i : ({a} : Finset ι), X i, Φ.toContinuousLinearMap w a (g a (x default))
        ∂Measure.pi fun i : ({a} : Finset ι) => μ i) = ∫ t, Φ.toContinuousLinearMap w a (g a t) ∂μ a from h1]
    rw [(Φ.toContinuousLinearMap w a).integral_comp_comm (hg a), ← hL]
    congr 1
    funext i
    by_cases hia : i = a
    · subst hia; simp [hw]
    · by_cases his : i ∈ s
      · simp [hw, his, Function.update_of_ne hia]
      · simp [hw, his, hia, Function.update_of_ne hia]

theorem integral_multilinear_pi : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (E : ι → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i), (∀ i, Integrable (g i) (μ i)) → Integrable (fun x : ∀ i, X i => Φ fun i => g i (x i)) (Measure.pi μ) ∧ ∫ x, Φ (fun i => g i (x i)) ∂Measure.pi μ = Φ fun i => ∫ y, g i y ∂μ i := by
  intro ι _ _ X _ μ _ E _ _ _ F _ _ _ Φ g hg
  constructor
  · have hmeas : AEStronglyMeasurable (fun x : ∀ i, X i => fun i => g i (x i)) (Measure.pi μ) :=
      aestronglyMeasurable_pi_of_forall (f := fun i (x : ∀ i, X i) => g i (x i)) fun i =>
        (hg i).1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)
    have hdom : Integrable (fun x : ∀ i, X i => ‖Φ‖ * ∏ i, ‖g i (x i)‖) (Measure.pi μ) :=
      (Integrable.fintype_prod_dep (f := fun i (y : X i) => ‖g i y‖) fun i => (hg i).norm).const_mul _
    exact hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => Φ.le_opNorm _)
  · let e : (↥(Finset.univ : Finset ι)) ≃ ι := Equiv.subtypeUnivEquiv Finset.mem_univ
    have hmp := measurePreserving_piCongrLeft μ e
    rw [← hmp.integral_comp']
    have hpt : ∀ z : ∀ i : (Finset.univ : Finset ι), X i,
        (fun i => g i (MeasurableEquiv.piCongrLeft X e z i)) = vecOn g Finset.univ 0 z := by
      intro z; funext i
      have h := Equiv.piCongrLeft_apply_apply X e z ⟨i, Finset.mem_univ i⟩
      simp only [vecOn, dif_pos (Finset.mem_univ i)]
      rw [MeasurableEquiv.coe_piCongrLeft]
      exact congrArg (g i) h
    refine ((integral_congr_ae (ae_of_all _ fun z => congrArg Φ (hpt z))).trans
      (integral_vecOn μ Φ g hg Finset.univ 0)).trans ?_
    simp

end GlobalTheory.MultilinFubini
end

section

namespace GlobalTheory.TwistDual

open Matrix

variable {E : Type} [Field E] [StarRing E] [CharZero E]

theorem fromCols_mulVec_eq_zero {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0)
    (u : Fin r ⊕ Fin m → E) (hu : Matrix.fromCols C B *ᵥ u = 0) : u = 0 := by
  have hBC : Bᴴ * G * C = 0 := by
    have := congrArg conjTranspose hCB
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hsplit : C *ᵥ (u ∘ Sum.inl) + B *ᵥ (u ∘ Sum.inr) = 0 := by
    rw [← hu]; funext i
    simp [mulVec, dotProduct, Fintype.sum_sum_type]
  have hb : u ∘ Sum.inr = 0 := by
    have h2 := congrArg (fun w => (Bᴴ * G) *ᵥ w) hsplit
    simp only [mulVec_add, mulVec_mulVec, hBC, zero_mulVec, zero_add, mulVec_zero] at h2
    exact Matrix.eq_zero_of_mulVec_eq_zero hBB h2
  have ha : u ∘ Sum.inl = 0 := by
    rw [hb, mulVec_zero, add_zero] at hsplit
    have hC' := Fintype.linearIndependent_iff.1 hC
    funext k
    refine hC' _ ?_ k
    rw [← hsplit]; funext i
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  funext x
  rcases x with k | k
  · exact congrFun ha k
  · exact congrFun hb k

theorem mulVec_surjective {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G) (hGd : G.det ≠ 0)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0) :
    Function.Surjective ((Matrix.fromCols C B)ᴴ * G).mulVecLin := by
  set M := (Matrix.fromCols C B)ᴴ * G
  have hinj : Function.Injective Mᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    rw [Matrix.mulVecLin_apply, mulVec_transpose] at hw
    have h1 := congrArg star hw
    rw [star_vecMul, star_zero, conjTranspose_mul, hG, conjTranspose_conjTranspose, ← mulVec_mulVec] at h1
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hGd h1
    have h3 := fromCols_mulVec_eq_zero hG hC hBB hCB _ h2
    simpa using congrArg star h3
  have hr : Mᵀ.rank = Fintype.card (Fin r ⊕ Fin m) := by
    rw [← Matrix.finrank_range_mulVecLin, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  rw [Matrix.rank_transpose] at hr
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← hr]
  exact Matrix.finrank_range_mulVecLin _

theorem exists_dual {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G) (hGd : G.det ≠ 0)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hCC : Cᴴ * G * C = 0) (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0) :
    ∃ C' : Matrix (Fin n) (Fin r) E, Cᴴ * G * C' = 1 ∧ C'ᴴ * G * C' = 0 ∧ C'ᴴ * G * B = 0 := by
  have hs := mulVec_surjective hG hGd hC hBB hCB
  choose v hv using fun k : Fin r => hs (Pi.single (Sum.inl k) (1 : E))
  set C₁ : Matrix (Fin n) (Fin r) E := Matrix.of fun i k => v k i
  have key : ∀ a k, ∑ i, ((Matrix.fromCols C B)ᴴ * G) a i * C₁ i k = (Pi.single (Sum.inl k) (1 : E) : Fin r ⊕ Fin m → E) a := by
    intro a k
    rw [← hv k]
    simp only [C₁, Matrix.mulVecLin_apply, mulVec, dotProduct, Matrix.of_apply]
  have hC1 : Cᴴ * (G * C₁) = 1 := by
    ext j k
    have := key (Sum.inl j) k
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inl] at this ⊢
    rw [this, Pi.single_apply, Matrix.one_apply]
    simp [eq_comm]
  have hB1 : Bᴴ * (G * C₁) = 0 := by
    ext j k
    have := key (Sum.inr j) k
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inr] at this ⊢
    rw [this]
    simp
  have hGc : ∀ (p q : ℕ) (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E),
      Yᴴ * (G * X) = (Xᴴ * (G * Y))ᴴ := by
    intro p q X Y
    simp [conjTranspose_mul, hG, Matrix.mul_assoc]
  have hCC' : Cᴴ * (G * C) = 0 := by rw [← Matrix.mul_assoc]; exact hCC
  have hCB' : Cᴴ * (G * B) = 0 := by rw [← Matrix.mul_assoc]; exact hCB
  have h1C : C₁ᴴ * (G * C) = 1 := by rw [hGc, hC1, conjTranspose_one]
  have h1B : C₁ᴴ * (G * B) = 0 := by
    have := congrArg conjTranspose hB1
    rw [conjTranspose_zero, ← hGc] at this
    exact this
  set S := C₁ᴴ * (G * C₁) with hSdef
  have hS : Sᴴ = S := by rw [hSdef, ← hGc]
  set X : Matrix (Fin r) (Fin r) E := (2 : E)⁻¹ • S with hXdef
  have hX : Xᴴ = X := by
    rw [hXdef, conjTranspose_smul, hS, star_inv₀, star_ofNat]
  have hXX : X + X = S := by
    rw [hXdef, ← add_smul, ← two_mul, mul_inv_cancel₀ (two_ne_zero), one_smul]
  have a1 : ∀ Y : Matrix (Fin r) (Fin r) E, Cᴴ * (G * (C * Y)) = 0 := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, hCC', Matrix.zero_mul]
  have a2 : ∀ Y : Matrix (Fin r) (Fin r) E, C₁ᴴ * (G * (C * Y)) = Y := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, h1C, Matrix.one_mul]
  refine ⟨C₁ - C * X, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hC1, a1, sub_zero]
  · simp only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      hC1, a1, a2, Matrix.mul_one, Matrix.mul_zero, sub_zero]
    rw [← hSdef, ← hXX]; abel
  · simp only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.sub_mul, Matrix.mul_assoc, h1B, hCB',
      Matrix.mul_zero, sub_zero]

end GlobalTheory.TwistDual
end

section

open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory

theorem haar_map_mul_right_eq_of_fundamentalDomain (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ N : Subgroup H) (hΓ : Countable Γ) (hNc : IsClosed (N : Set H)) (κ : Measure N) (𝓝 : Set N)
    (hκ : κ.IsHaarMeasure) (h𝓝 : IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ) (hfin : κ 𝓝 ≠ ⊤) (n₀ : N) :
    κ.map (· * n₀) = κ := by
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨((x : N) : H), x.2⟩ : Γ)) ?_
    intro a b h
    have h' : ((a : N) : H) = ((b : N) : H) := congrArg (fun y : Γ => (y : H)) h
    exact Subtype.ext (Subtype.ext h')
  haveI : (κ.map (· * n₀)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right κ n₀
  have hc := Measure.isMulLeftInvariant_eq_smul (κ.map (· * n₀)) κ
  set c := Measure.haarScalarFactor (κ.map (· * n₀)) κ
  have h𝓝' : IsFundamentalDomain (Γ.subgroupOf N) ((· * n₀) ⁻¹' 𝓝) κ := by
    refine h𝓝.preimage_of_equiv (quasiMeasurePreserving_mul_right κ n₀) (e := id) bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : κ ((· * n₀) ⁻¹' 𝓝) = κ 𝓝 := h𝓝'.measure_eq h𝓝
  have h0 : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hmap : (κ.map (· * n₀)) 𝓝 = κ ((· * n₀) ⁻¹' 𝓝) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight n₀) 𝓝
  have h1 : (c : ENNReal) * κ 𝓝 = 1 * κ 𝓝 := by
    calc (c : ENNReal) * κ 𝓝 = (c • κ) 𝓝 := by simp [Measure.smul_apply]
      _ = (κ.map (· * n₀)) 𝓝 := by rw [hc]
      _ = 1 * κ 𝓝 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

end GlobalTheory
end

end

section

@[expose] public section

open MeasureTheory Function
open scoped Pointwise

theorem _root_.GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → ∀ n₀ : N, κ.map (· * n₀) = κ := by
  first | exact @GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain | exact GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain | (intros; apply GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain <;> assumption)

end
end

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.integral_continuousMultilinearMap_pi_measure : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (E : ι → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i), (∀ i, Integrable (g i) (μ i)) → Integrable (fun x : ∀ i, X i => Φ fun i => g i (x i)) (Measure.pi μ) ∧ ∫ x, Φ (fun i => g i (x i)) ∂Measure.pi μ = Φ fun i => ∫ y, g i y ∂μ i := by
  first | exact @GlobalTheory.MultilinFubini.integral_multilinear_pi | exact GlobalTheory.MultilinFubini.integral_multilinear_pi | (intros; apply GlobalTheory.MultilinFubini.integral_multilinear_pi <;> assumption)

end
end
