module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.Continuity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open MvPolynomial

theorem hasFDerivAt_eval {I : Type} [Fintype I] [DecidableEq I] (p : MvPolynomial I ℂ) (x : I → ℂ) :
    HasFDerivAt (fun x => eval x p) (∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i) x := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const a x
  | add p q hp hq =>
    refine ((hp.add hq).congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => map_add _ _ _)
    simp [add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    refine ((hp.mul (hasFDerivAt_apply (𝕜 := ℂ) j x)).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
    simp [pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm, apply_ite, add_comm]

theorem anChart_alg {k A : Type} [Field k] [CommRing A] [Algebra k A] (D : ℕ) [h : Algebra.IsStandardSmoothOfRelativeDimension D k A]
    (σ : k →+* ℂ) (ψ₀ : A →+* ℂ) (h₀ : ψ₀.comp (algebraMap k A) = σ) :
    ∃ (N : ℕ) (g : Fin N → A) (f : Fin D → A) (B : Set (Fin D → ℂ)) (ε : ℝ) (Ψ : (Fin D → ℂ) → (A →+* ℂ)),
      0 < ε ∧ IsOpen B ∧ (∀ b ∈ B, (Ψ b).comp (algebraMap k A) = σ ∧ ∀ i, Ψ b (f i) = b i) ∧
      (∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B) ∧
      ∀ ψ : A →+* ℂ, ψ.comp (algebraMap k A) = σ → (∀ j, ‖ψ (g j) - ψ₀ (g j)‖ < ε) →
        (fun i => ψ (f i)) ∈ B ∧ Ψ (fun i => ψ (f i)) = ψ := by
  classical
  obtain ⟨I, J, _, _, P, hd⟩ := h.out
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  have e : Fin D ≃ {i : I // i ∉ Set.range P.map} := (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl, ← hd, Algebra.Presentation.dimension, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Set.card_range_of_injective P.map_inj])).symm
  let ev := fun (x : I → ℂ) => eval₂Hom σ x
  have pt : ∀ ψ : A →+* ℂ, ψ.comp (algebraMap k A) = σ → ∀ p, ψ (algebraMap P.Ring A p) = ev (fun i => ψ (P.val i)) p := fun ψ hψ p => by
    rw [P.algebraMap_apply, aeval_def, ← coe_eval₂Hom, map_eval₂Hom, hψ]
  let q : I → MvPolynomial I k := fun i => if h : i ∈ Set.range P.map then P.relation h.choose else X i
  have q₁ : ∀ j, q (P.map j) = P.relation j := fun j => (dif_pos ⟨j, rfl⟩).trans
    (congrArg _ (P.map_inj (⟨j, rfl⟩ : P.map j ∈ Set.range P.map).choose_spec))
  have q₂ : ∀ i : {i : I // i ∉ Set.range P.map}, q i = X i.1 := fun i => dif_neg i.2
  let Φ : (I → ℂ) → I → ℂ := fun x i => eval x (map σ (q i))
  have Φe : ∀ x i, Φ x i = ev x (q i) := fun x i => eval_map _ _ _
  let x₀ : I → ℂ := fun i => ψ₀ (P.val i)
  let F : (I → ℂ) →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i =>
    ∑ i', eval x₀ (pderiv i' (map σ (q i))) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i'
  have hF : HasFDerivAt Φ F x₀ := hasFDerivAt_pi.2 fun i => hasFDerivAt_eval _ _
  have Fv : ∀ v i, F v i = ∑ i', ev x₀ (pderiv i' (q i)) * v i' := fun v i => by
    simp [F, ev, pderiv_map, eval_map]
  have inj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun v hv => by
    have z₁ : ∀ i, i ∉ Set.range P.map → v i = 0 := fun i hi => by
      have := congrFun hv i
      rw [Fv, q₂ ⟨i, hi⟩] at this
      simpa [pderiv_X, Pi.single_apply, apply_ite] using this
    have dt : ((ev x₀).mapMatrix P.jacobiMatrix).det ≠ 0 := by
      rw [← RingHom.map_det, ← pt ψ₀ h₀, ← P.jacobian_eq_jacobiMatrix_det]
      exact (P.jacobian_isUnit.map ψ₀).ne_zero
    have z₂ : (fun j => v (P.map j)) = 0 := Matrix.eq_zero_of_vecMul_eq_zero dt (funext fun j => by
      have := congrFun hv (P.map j)
      rw [Fv, q₁, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image P.map)) (fun i _ hi => by
        rw [z₁ i (by simpa using hi), mul_zero]), Finset.sum_image fun a _ b _ h => P.map_inj h] at this
      simpa [Matrix.vecMul, dotProduct, P.jacobiMatrix_apply, mul_comm] using this)
    funext i
    by_cases hi : i ∈ Set.range P.map
    · obtain ⟨j, rfl⟩ := hi; exact congrFun z₂ j
    · exact z₁ i hi
  let F' : (I → ℂ) ≃L[ℂ] (I → ℂ) := (LinearEquiv.ofInjectiveEndo F.toLinearMap inj).toContinuousLinearEquiv
  have cd : ContDiffAt ℂ 1 Φ x₀ := contDiffAt_pi.2 fun i =>
    (AnalyticOnNhd.eval_mvPolynomial (map σ (q i)) x₀ trivial).contDiffAt
  let T := cd.toOpenPartialHomeomorph Φ (f' := F') hF one_ne_zero
  let O := T.target ∩ interior {w | ContDiffAt ℂ 1 T.symm w}
  have oO : IsOpen O := T.open_target.inter isOpen_interior
  have mO : Φ x₀ ∈ O := ⟨cd.image_mem_toOpenPartialHomeomorph_target (f' := F') hF one_ne_zero,
    mem_interior_iff_mem_nhds.2 ((cd.to_localInverse (f' := F') hF one_ne_zero).eventually (by simp))⟩
  let em : (Fin D → ℂ) →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i =>
    if h : i ∈ Set.range P.map then 0 else ContinuousLinearMap.proj (e.symm ⟨i, h⟩)
  have m₁ : ∀ b j, em b (P.map j) = 0 := fun b j => by simp [em]
  have m₂ : ∀ b i, em b (e i) = b i := fun b i => by simp only [em, ContinuousLinearMap.pi_apply, dif_neg (e i).2]; simp
  have lf : ∀ x : I → ℂ, (∀ j, ev x (P.relation j) = 0) → ∃ ψ : A →+* ℂ, ∀ p, ψ (algebraMap P.Ring A p) = ev x p := fun x hx =>
    ⟨(algebraMap P.Ring A).liftOfSurjective P.algebraMap_surjective ⟨ev x, by
      show P.ker ≤ _
      rw [← P.span_range_relation_eq_ker, Ideal.span_le]
      rintro _ ⟨j, rfl⟩; exact hx j⟩, fun p => RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩
  choose Ψ hΨ using lf
  have rel : ∀ b, em b ∈ O → ∀ j, ev (T.symm (em b)) (P.relation j) = 0 := fun b hb j => by
    rw [← q₁, ← Φe, show Φ (T.symm (em b)) = em b from T.right_inv hb.1, m₁]
  obtain ⟨ε, ε0, hε⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (T.open_source.mem_nhds
    (cd.mem_toOpenPartialHomeomorph_source (f' := F') hF one_ne_zero)) (hF.continuousAt.preimage_mem_nhds (oO.mem_nhds mO)))
  let n := Fintype.equivFin I
  refine ⟨_, fun j => P.val (n.symm j), fun i => P.val (e i), em ⁻¹' O, ε, fun b => if h : em b ∈ O then Ψ _ (rel b h) else ψ₀, ε0,
    oO.preimage em.continuous, fun b hb => ?_, fun a => ?_, fun ψ hψ hg => ?_⟩
  · simp only [dif_pos (show em b ∈ O from hb)]
    refine ⟨RingHom.ext fun r => ?_, fun i => ?_⟩
    · rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k P.Ring A, hΨ]; exact eval₂Hom_C _ _ _
    · rw [show P.val (e i) = algebraMap P.Ring A (X (e i).1) by simp, hΨ, ← q₂, ← Φe,
        show Φ (T.symm (em b)) = em b from T.right_inv hb.1, m₂]
  · obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    refine DifferentiableOn.congr (f := fun b => eval (T.symm (em b)) (map σ p)) (fun b hb => ?_) fun b hb => ?_
    · have c₁ : ContDiffAt ℂ 1 T.symm (em b) := interior_subset hb.2
      have c₂ : DifferentiableAt ℂ (fun x : I → ℂ => eval x (map σ p)) (T.symm (em b)) := (hasFDerivAt_eval _ _).differentiableAt
      exact (c₂.comp b ((c₁.differentiableAt one_ne_zero).comp b em.differentiableAt)).differentiableWithinAt
    · simp only [dif_pos (show em b ∈ O from hb)]; rw [hΨ, eval_map]; rfl
  · have hx := hε (show (fun i => ψ (P.val i)) ∈ Metric.ball x₀ ε from (dist_pi_lt_iff ε0).2 fun i => by
      simpa [dist_eq_norm] using hg (n i))
    have e₁ : em (fun i => ψ (P.val (e i))) = Φ fun i => ψ (P.val i) := funext fun i => by
      by_cases hi : i ∈ Set.range P.map
      · obtain ⟨j, rfl⟩ := hi
        rw [m₁, Φe, q₁, ← pt ψ hψ, P.algebraMap_apply, P.aeval_val_relation, map_zero]
      · obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
        obtain rfl : (e j).1 = i := congrArg Subtype.val hj
        rw [m₂, Φe, q₂]
        simp only [ev, eval₂Hom_X']
    have mB : em (fun i => ψ (P.val (e i))) ∈ O := by rw [e₁]; exact hx.2
    refine ⟨mB, (dif_pos mB).trans (RingHom.ext fun a => ?_)⟩
    obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    rw [hΨ, pt ψ hψ, e₁, show T.symm (Φ fun i => ψ (P.val i)) = _ from T.left_inv hx.1]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open Module

variable {V k : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field k] [Algebra V k] [FaithfulSMul V k]

theorem exists_finset_iInf_le {M : Type} [AddCommGroup M] [Module k M] [FiniteDimensional k M] {O : Type}
    (K : O → Submodule k M) : ∃ F : Finset O, ∀ b, (⨅ a ∈ F, K a) ≤ K b := by
  classical
  obtain ⟨N, ⟨F, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule k M)).has_min
    {N | ∃ F : Finset O, N = ⨅ a ∈ F, K a} ⟨⊤, ∅, by simp⟩
  refine ⟨F, fun b => ?_⟩
  have hle : (⨅ a ∈ insert b F, K a) ≤ ⨅ a ∈ F, K a := by
    rw [Finset.iInf_insert]
    exact inf_le_right
  have heq : (⨅ a ∈ insert b F, K a) = ⨅ a ∈ F, K a := by
    by_contra hne
    exact hmin _ ⟨insert b F, rfl⟩ (lt_of_le_of_ne hle hne)
  rw [← heq, Finset.iInf_insert]
  exact inf_le_left

theorem card_le_finrank_of_li {ι' ι : Type} [Fintype ι'] [Fintype ι] (v : ι → ι' → V) (hv : LinearIndependent V v)
    (W : Submodule k (ι' → k)) (hW : ∀ i, (algebraMap V k ∘ v i) ∈ W) : Fintype.card ι ≤ finrank k W := by
  have hk : LinearIndependent k (fun i => algebraMap V k ∘ v i) :=
    linearIndependent_algebraMap_comp_iff.mpr hv
  have hw : LinearIndependent k (fun i => (⟨algebraMap V k ∘ v i, hW i⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hk
  exact hw.fintype_card_le_finrank

theorem exists_li_of_submodule {ι' : Type} [Fintype ι'] [DecidableEq ι'] (N : Submodule V (ι' → V)) :
    ∃ v : Fin (finrank V N) → ι' → V, LinearIndependent V v ∧ ∀ i, v i ∈ N := by
  let b := Module.finBasis V N
  exact ⟨fun i => b i, b.linearIndependent.map' N.subtype (Submodule.ker_subtype N), fun i => (b i).2⟩

private theorem sub_algebraMap_smul_id_apply_algebraMap_comp {n : ℕ} {O : Type} (L : O → (Fin n → V) →ₗ[V] (Fin n → V))
    (Lk : O → (Fin n → k) →ₗ[k] (Fin n → k)) (hL : ∀ a c, Lk a (algebraMap V k ∘ c) = algebraMap V k ∘ L a c)
    (χ : O → V) (a : O) (c : Fin n → V) :
    (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))) (algebraMap V k ∘ c) =
      algebraMap V k ∘ ((L a - χ a • (LinearMap.id : (Fin n → V) →ₗ[V] (Fin n → V))) c) := by
  ext i
  have := congrFun (hL a c) i
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Function.comp_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul] at this ⊢
  rw [this]

private theorem finrank_range_le_finrank_range_of_reduction {m : ℕ} {ι' : Type} [Fintype ι'] [DecidableEq ι']
    (B : (Fin m → V) →ₗ[V] (ι' → V)) (Bk : (Fin m → k) →ₗ[k] (ι' → k))
    (h : ∀ c, Bk (algebraMap V k ∘ c) = algebraMap V k ∘ B c) :
    finrank V (LinearMap.range B) ≤ finrank k (LinearMap.range Bk) := by
  obtain ⟨v, hv, hvN⟩ := exists_li_of_submodule (LinearMap.range B)
  have := card_le_finrank_of_li (k := k) v hv (LinearMap.range Bk) (fun i => by
    obtain ⟨c, hc⟩ := hvN i
    exact ⟨algebraMap V k ∘ c, by rw [h, hc]⟩)
  simpa using this

theorem finrank_eig_bc {n : ℕ} {O : Type} (L : O → (Fin n → V) →ₗ[V] (Fin n → V))
    (Lk : O → (Fin n → k) →ₗ[k] (Fin n → k)) (hL : ∀ a c, Lk a (algebraMap V k ∘ c) = algebraMap V k ∘ L a c)
    (χ : O → V) :
    finrank V (⨅ a, LinearMap.ker (L a - χ a • LinearMap.id) : Submodule V (Fin n → V)) =
      finrank k (⨅ a, LinearMap.ker (Lk a - algebraMap V k (χ a) • LinearMap.id) : Submodule k (Fin n → k)) := by
  classical

  have hle : finrank V (⨅ a, LinearMap.ker (L a - χ a • LinearMap.id) : Submodule V (Fin n → V)) ≤
      finrank k (⨅ a, LinearMap.ker (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))) :
        Submodule k (Fin n → k)) := by
    obtain ⟨v, hv, hvN⟩ := exists_li_of_submodule
      (⨅ a, LinearMap.ker (L a - χ a • LinearMap.id) : Submodule V (Fin n → V))
    have := card_le_finrank_of_li (k := k) v hv
      (⨅ a, LinearMap.ker (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k)))) (fun i => by
        have hi := hvN i
        simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hi ⊢
        intro a
        rw [sub_algebraMap_smul_id_apply_algebraMap_comp L Lk hL χ a, hi a]
        ext j
        simp)
    simpa using this

  obtain ⟨F, hF⟩ := exists_finset_iInf_le (k := k)
    (fun a => LinearMap.ker (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))))
  let B : (Fin n → V) →ₗ[V] (F × Fin n → V) :=
    LinearMap.pi fun p => (LinearMap.proj p.2).comp (L p.1 - χ p.1 • LinearMap.id)
  let Bk : (Fin n → k) →ₗ[k] (F × Fin n → k) :=
    LinearMap.pi fun p => (LinearMap.proj p.2).comp (Lk p.1 - algebraMap V k (χ p.1) • LinearMap.id)
  have hB : ∀ c, Bk (algebraMap V k ∘ c) = algebraMap V k ∘ B c := by
    intro c
    ext p
    have := congrFun (sub_algebraMap_smul_id_apply_algebraMap_comp L Lk hL χ p.1 c) p.2
    simpa [B, Bk] using this
  have hmemk : ∀ c : Fin n → k, Bk c = 0 ↔ ∀ a ∈ F, (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))) c = 0 := by
    intro c
    constructor
    · intro h a ha
      ext j
      exact congrFun h (⟨a, ha⟩, j)
    · intro h
      ext p
      exact congrFun (h p.1 p.1.2) p.2
  have hkerk : LinearMap.ker Bk =
      (⨅ a, LinearMap.ker (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))) : Submodule k (Fin n → k)) := by
    ext c
    rw [LinearMap.mem_ker, hmemk]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro h b
      have hc : c ∈ ⨅ a ∈ F, LinearMap.ker (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))) := by
        simp only [Submodule.mem_iInf, LinearMap.mem_ker]
        exact h
      exact hF b hc
    · intro h a _
      exact h a
  have hker : LinearMap.ker B =
      (⨅ a, LinearMap.ker (L a - χ a • LinearMap.id) : Submodule V (Fin n → V)) := by
    ext c
    simp only [LinearMap.mem_ker, Submodule.mem_iInf]
    constructor
    · intro h b
      have h1 : Bk (algebraMap V k ∘ c) = 0 := by
        rw [hB, h]
        ext p
        simp
      have h2 := (LinearMap.mem_ker.2 h1 : _ ∈ LinearMap.ker Bk)
      rw [hkerk] at h2
      simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2
      have h3 := h2 b
      rw [sub_algebraMap_smul_id_apply_algebraMap_comp L Lk hL χ b] at h3
      ext j
      have := congrFun h3 j
      simp only [Function.comp_apply, Pi.zero_apply] at this
      exact (FaithfulSMul.algebraMap_injective V k) (by rw [this, Pi.zero_apply, map_zero])
    · intro h
      ext p
      simp [B, h p.1]
  have hrn : finrank V (LinearMap.range B) + finrank V (LinearMap.ker B) = n := by
    have h := LinearMap.rank_range_add_rank_ker B
    rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, rank_fin_fun] at h
    exact_mod_cast h
  have hrnk := LinearMap.finrank_range_add_finrank_ker Bk
  have hr := finrank_range_le_finrank_range_of_reduction B Bk hB
  rw [hker] at hrn
  rw [hkerk, Module.finrank_fin_fun] at hrnk
  omega

end ReciprocityTheory.ChartRestriction.G.Chart
end
end
