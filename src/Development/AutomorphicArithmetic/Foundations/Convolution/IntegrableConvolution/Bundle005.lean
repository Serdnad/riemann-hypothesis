module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.UnitsTrace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField GroundTheory.Global.InfinitePlace
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.L1.infSplit :
    UpperTheory.ConvolutionTheory.L1.InfSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm
  refine ⟨fun hF => ?_, fun p => ?_⟩
  · have h : ∀ v : InfinitePlace F, Nonempty (E →ₐ[F] v.Completion) := fun v => by
      haveI : IsAlgClosed v.Completion :=
        IsAlgClosed.of_ringEquiv ℂ _
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex (hF.isComplex v)).symm
      exact ⟨IsAlgClosed.lift⟩
    exact ⟨Pi.algHom F (fun v : InfinitePlace F => v.Completion) fun v => (h v).some⟩
  · obtain ⟨e, he, hs⟩ := UpperTheory.ConvolutionTheory.L1.galSplit F E σ hσ m hm (InfiniteAdeleRing F) (InfiniteAdeleRing E)
      (tensorInfiniteAdeleRingEquiv (K := F) (L := E)) p
    have hd : ∀ r i, e (infiniteAdeleRingMap (K := F) (L := E) r) i = r := fun r i => by
      have := he 1 r i
      rwa [tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul, map_one, map_one, one_mul] at this
    have hx : ∀ (x : E) i, e (algebraMap E (InfiniteAdeleRing E) x) i = p ((σ ^ (i : ℕ)) x) := fun x i => by
      have := he x 1 i
      rwa [tensorInfiniteAdeleRingEquiv_tmul', map_one, mul_one, mul_one] at this
    refine ⟨⟨e, ?_, ?_, hd, hs⟩, hx⟩
    · let b := Module.finBasis F E
      have h : ∀ y i, e y i = ∑ j, p ((σ ^ (i : ℕ)) (b j)) * adeleCoord b j y := fun y i => by
        conv_lhs => rw [← tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y]

        rw [map_sum, map_sum, Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => he _ _ _
      refine continuous_pi fun i => ?_
      simp_rw [h]
      exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_adeleCoord b j)
    · have h : ∀ a, e.symm a =
          ∑ i, infiniteAdeleRingMap (K := F) (L := E) (a i) * e.symm (Pi.single i 1) := fun a => by
        apply e.injective
        funext k

        rw [map_sum, Finset.sum_apply, RingEquiv.apply_symm_apply]
        simp_rw [map_mul, RingEquiv.apply_symm_apply, Pi.mul_apply, hd]
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hj
          rw [Pi.single_eq_of_ne hj.symm, mul_zero]
        · simp
      have h' : (e.symm : _ → _) = fun a => ∑ i, infiniteAdeleRingMap (K := F) (L := E) (a i) * e.symm (Pi.single i 1) :=
        funext h
      rw [h']
      exact continuous_finsetSum _ fun i _ =>
        (continuous_infiniteAdeleRingMap.comp (continuous_apply i)).mul continuous_const
end

section

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

private lemma proj_comm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Z : Submodule ℂ H) [Z.HasOrthogonalProjection] (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hZ : ∀ z ∈ Z, T z ∈ Z) (x : H) : Z.starProjection (T x) = T (Z.starProjection x) := by
  have hp : Z.starProjection x ∈ Z := Submodule.starProjection_apply_mem Z x
  apply Submodule.eq_starProjection_of_mem_orthogonal (hZ _ hp)
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hxo : x - Z.starProjection x ∈ Zᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hsym : ⟪z, T (x - Z.starProjection x)⟫_ℂ = ⟪T z, x - Z.starProjection x⟫_ℂ := by
    have := ContinuousLinearMap.adjoint_inner_left T (x - Z.starProjection x) z
    rw [← this, ← ContinuousLinearMap.star_eq_adjoint, hT.star_eq]
  rw [← map_sub, hsym]
  exact (Submodule.mem_orthogonal _ _).1 hxo _ (hZ z hz)

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.jointNe :
    UpperTheory.ConvolutionTheory.L1.JointNe := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U h i y hy
  obtain ⟨hcl, hinv, hirr⟩ := UpperTheory.ConvolutionTheory.L1.cutIrr Γ G H π V m ι E A U h
  have hmemVE : ∀ w, w ∈ eigIn V E 1 ↔ w ∈ V ∧ E w = w := by
    intro w
    simp [eigIn, Module.End.mem_eigenspace_iff, Submodule.mem_inf]
  have hmemZ : ∀ (k : Fin (m + 1)) w, w ∈ eigIn (eigIn V E 1) (A k) y ↔
      w ∈ eigIn V E 1 ∧ A k w = (y : ℂ) • w := by
    intro k w
    simp only [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    rfl
  have hsa : ∀ k, IsSelfAdjoint (A k) := fun k =>
    (ContinuousLinearMap.nonneg_iff_isPositive.1 (h.A_pos k)).isSelfAdjoint
  have hAVE : ∀ j, ∀ w ∈ eigIn V E 1, A j w ∈ eigIn V E 1 := by
    intro j w hw
    obtain ⟨hwV, hwE⟩ := (hmemVE w).1 hw
    refine (hmemVE _).2 ⟨h.A_mem j w hwV, ?_⟩
    rw [← h.A_E, hwE]

  have hstep : ∀ j, eigIn (eigIn V E 1) (A j) y ≠ ⊥ → eigIn (eigIn V E 1) (A (j + 1)) y ≠ ⊥ := by
    intro j hj
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hj
    obtain ⟨hvE, hvA⟩ := (hmemZ j v).1 hv
    obtain ⟨hvV, hvE'⟩ := (hmemVE v).1 hvE
    have hvm : v ∈ V.map (U : H →ₗ[ℂ] H) := by rw [h.U_mem]; exact hvV
    obtain ⟨u, hu, rfl⟩ := hvm
    have hU : ∀ a b : H, U a = U b → a = b := fun a b hab => U.injective hab
    refine (Submodule.ne_bot_iff _).2 ⟨u, (hmemZ _ u).2 ⟨(hmemVE u).2 ⟨hu, ?_⟩, ?_⟩, ?_⟩
    · apply hU
      rw [h.U_E]
      exact hvE'
    · apply hU
      rw [h.U_A, map_smul]
      exact hvA
    · rintro rfl
      exact hv0 (by simp)
  have hall : ∀ j, eigIn (eigIn V E 1) (A j) y ≠ ⊥ := by
    have ht : ∀ t : Fin (m + 1), eigIn (eigIn V E 1) (A (i + t)) y ≠ ⊥ := by
      intro t
      induction t using Fin.induction with
      | zero => simpa using hy
      | succ t ih =>
        rw [← Fin.coeSucc_eq_succ, ← add_assoc]
        exact hstep _ ih
    intro j
    have := ht (j - i)
    rwa [add_sub_cancel] at this

  have hS : ∀ S : Finset (Fin (m + 1)), ∃ w ∈ eigIn V E 1, w ≠ 0 ∧ ∀ j ∈ S, A j w = (y : ℂ) • w := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have hne : eigIn V E 1 ≠ ⊥ := by
        intro hb
        obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 (hall i)
        have := ((hmemZ i v).1 hv).1
        rw [hb] at this
        exact hv0 (by simpa using this)
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact ⟨v, hv, hv0, by simp⟩
    | insert k S hk ih =>
      obtain ⟨w₀, hw₀, hw₀0, hw₀A⟩ := ih
      by_contra hno
      have hno' : ∀ w ∈ eigIn V E 1, (∀ j ∈ S, A j w = (y : ℂ) • w) → A k w = (y : ℂ) • w → w = 0 := by
        intro w hw hwS hwk
        by_contra hw0
        exact hno ⟨w, hw, hw0, fun j hj => by
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact hwk
          · exact hwS j hj⟩
      set Z := eigIn (eigIn V E 1) (A k) y with hZdef
      have hZcl : IsClosed (Z : Set H) := by
        have h2 : IsClosed {w : H | A k w = (y : ℂ) • w} :=
          isClosed_eq (A k).continuous (continuous_const_smul _)
        have : (Z : Set H) = (eigIn V E 1 : Set H) ∩ {w : H | A k w = (y : ℂ) • w} := by
          ext w
          exact hmemZ k w
        rw [this]
        exact hcl.inter h2
      haveI : CompleteSpace Z := hZcl.completeSpace_coe
      have hZA : ∀ j, ∀ z ∈ Z, A j z ∈ Z := by
        intro j z hz
        obtain ⟨hzVE, hzA⟩ := (hmemZ k z).1 hz
        refine (hmemZ k _).2 ⟨hAVE j z hzVE, ?_⟩
        rw [h.A_A, hzA, map_smul]
      have hZπ : ∀ j, j ≠ k → ∀ g, ∀ z ∈ Z, π (ι j g) z ∈ Z := by
        intro j hj g z hz
        obtain ⟨hzVE, hzA⟩ := (hmemZ k z).1 hz
        refine (hmemZ k _).2 ⟨hinv j g z hzVE, ?_⟩
        rw [h.A_ι k j (Ne.symm hj), hzA, map_smul]

      have hNo : ∀ w ∈ eigIn V E 1, (∀ j ∈ S, A j w = (y : ℂ) • w) → w ∈ Zᗮ := by
        intro w hw hwS
        rw [← Submodule.starProjection_apply_eq_zero_iff]
        have hp : Z.starProjection w ∈ Z := Submodule.starProjection_apply_mem Z w
        obtain ⟨hpVE, hpA⟩ := (hmemZ k _).1 hp
        refine hno' _ hpVE (fun j hj => ?_) hpA
        rw [← proj_comm Z (A j) (hsa j) (hZA j), hwS j hj, map_smul]
      let M : Submodule ℂ H :=
        { carrier := {w | w ∈ eigIn V E 1 ∧ ∀ g, π (ι k g) w ∈ Zᗮ}
          add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun g => by
            rw [map_add (f := _)]; exact Submodule.add_mem _ (ha.2 g) (hb.2 g)⟩
          zero_mem' := ⟨Submodule.zero_mem _, fun g => by
            rw [map_zero]; exact Submodule.zero_mem _⟩
          smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun g => by
            rw [map_smul]; exact Submodule.smul_mem _ c (ha.2 g)⟩ }
      have hMmem : ∀ w, w ∈ M ↔ w ∈ eigIn V E 1 ∧ ∀ g, π (ι k g) w ∈ Zᗮ := fun w => Iff.rfl
      have hMle : M ≤ eigIn V E 1 := fun w hw => hw.1
      have hMcl : IsClosed (M : Set H) := by
        have : (M : Set H) = (eigIn V E 1 : Set H) ∩ ⋂ g, (π (ι k g)) ⁻¹' (Zᗮ : Set H) := by
          ext w
          simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
          exact hMmem w
        rw [this]
        exact hcl.inter (isClosed_iInter fun g =>
          (Submodule.isClosed_orthogonal Z).preimage (π (ι k g)).continuous)
      have hMinv : ∀ j g, ∀ v ∈ M, π (ι j g) v ∈ M := by
        intro j g v hv
        refine (hMmem _).2 ⟨hinv j g v hv.1, fun g' => ?_⟩
        by_cases hjk : j = k
        · subst hjk
          rw [← π.map_mul_apply, ← map_mul]
          exact hv.2 _
        · rw [← π.map_mul_apply, ((h.ι_comm k j (Ne.symm hjk)) g' g).eq, π.map_mul_apply]
          rw [Submodule.mem_orthogonal]
          intro z hz
          rw [π.inner_map_right, ← map_inv]
          exact (Submodule.mem_orthogonal _ _).1 (hv.2 g') _ (hZπ j hjk _ z hz)
      have hw₀M : w₀ ∈ M := by
        refine (hMmem _).2 ⟨hw₀, fun g => hNo _ (hinv k g w₀ hw₀) fun j hj => ?_⟩
        have hjk : j ≠ k := fun e => hk (e ▸ hj)
        rw [h.A_ι j k hjk, hw₀A j hj, map_smul]
      have hMtop : M = eigIn V E 1 := by
        rcases hirr M hMle hMcl hMinv with hb | he
        · exfalso
          rw [hb] at hw₀M
          exact hw₀0 (by simpa using hw₀M)
        · exact he
      obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 (hall k)
      have hzM : z ∈ M := by
        rw [hMtop]
        exact ((hmemZ k z).1 hz).1
      have hzo := hzM.2 1
      rw [map_one, π.map_one_apply] at hzo
      have := (Submodule.mem_orthogonal _ _).1 hzo z hz
      exact hz0 (inner_self_eq_zero.1 this)
  obtain ⟨w, hw, hw0, hwA⟩ := hS Finset.univ
  refine (Submodule.ne_bot_iff _).2 ⟨w, ?_, hw0⟩
  simp only [jointEig, Submodule.mem_iInf]
  exact fun j => (hmemZ j w).2 ⟨hw, hwA j (Finset.mem_univ j)⟩
end

section

private theorem factor_alg {A B C : Type} [Ring A] [Ring B] [Ring C] [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
    (p : A →ₐ[ℂ] B) (hp : Function.Surjective p) (g : A →ₐ[ℂ] C) (h : ∀ a, p a = 0 → g a = 0) :
    ∃ r : B →ₐ[ℂ] C, ∀ a, r (p a) = g a := by
  have key : ∀ a, g (Function.surjInv hp (p a)) = g a := by
    intro a
    rw [← sub_eq_zero, ← map_sub]
    apply h
    rw [map_sub, Function.surjInv_eq hp, sub_self]
  refine ⟨{ toFun := fun b => g (Function.surjInv hp b)
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_, commutes' := ?_ }, key⟩
  · rw [← map_one p, key, map_one]
  · intro x y
    obtain ⟨x, rfl⟩ := hp x
    obtain ⟨y, rfl⟩ := hp y
    simp only [← map_mul p, key, map_mul g]
  · rw [← map_zero p, key, map_zero]
  · intro x y
    obtain ⟨x, rfl⟩ := hp x
    obtain ⟨y, rfl⟩ := hp y
    simp only [← map_add p, key, map_add g]
  · intro c
    simp only [← p.commutes c, key, g.commutes]

private theorem comm_lift {X E : Type} [Ring E] [Algebra ℂ E] (T : X → E) (S : E) (h : ∀ x, Commute S (T x))
    (a : FreeAlgebra ℂ X) : Commute S (FreeAlgebra.lift ℂ T a) := by
  induction a using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact (Algebra.commutes r S).symm
  | grade1 x => rw [FreeAlgebra.lift_ι_apply]; exact h x
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add (f := _)]; exact ha.add_right hb

theorem UpperTheory.ConvolutionTheory.L1.algTrace :
    UpperTheory.ConvolutionTheory.L1.AlgTrace := by
  intro W X _ _ _ m T hcomm hirr U hU
  rcases subsingleton_or_nontrivial W with hW | hW
  · refine ⟨1, one_ne_zero, fun i₀ S _ => ?_⟩
    rw [one_mul]
    congr 1
    ext w
    exact Subsingleton.elim _ _
  let ρ : Fin (m + 1) → (FreeAlgebra ℂ X →ₐ[ℂ] Module.End ℂ W) := fun i => FreeAlgebra.lift ℂ (T i)
  have hρι : ∀ i x, ρ i (FreeAlgebra.ι ℂ x) = T i x := fun i x => FreeAlgebra.lift_ι_apply _ _
  have hρT : ∀ i j, i ≠ j → ∀ a y, Commute (ρ i a) (T j y) := fun i j hij a y =>
    (comm_lift (T i) (T j y) (fun x => (hcomm i j hij x y).symm) a).symm
  have hρρ : ∀ i j, i ≠ j → ∀ a b, Commute (ρ i a) (ρ j b) := fun i j hij a b =>
    comm_lift (T j) (ρ i a) (hρT i j hij a) b
  have hρU : ∀ i a w, U (ρ (i + 1) a w) = ρ i a (U w) := by
    intro i a
    induction a using FreeAlgebra.induction with
    | grade0 r => intro w; simp [Algebra.algebraMap_eq_smul_one]
    | grade1 x => intro w; rw [hρι, hρι, hU]
    | mul a b ha hb => intro w; simp only [map_mul, Module.End.mul_apply, ha, hb]
    | add a b ha hb => intro w; simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
  have hker : ∀ a, ρ 0 a = 0 → ∀ i, ρ i a = 0 := by
    intro a ha i
    induction i using Fin.induction with
    | zero => exact ha
    | succ i ih =>
      rw [← Fin.coeSucc_eq_succ]
      ext w
      apply U.injective
      rw [hρU, ih]
      simp
  obtain ⟨d, -, ⟨e⟩⟩ := UpperTheory.ConvolutionTheory.L1.matImage (FreeAlgebra ℂ X) W (ρ 0) {b | ∃ j, j ≠ 0 ∧ ∃ x, b = T j x}
    (by
      rintro a b ⟨j, hj, x, rfl⟩
      exact hρT 0 j hj.symm a x)
    (by
      intro P h1 h2
      apply hirr P
      intro i x w hw
      by_cases hi : i = 0
      · subst hi
        rw [← hρι]
        exact h1 _ w hw
      · exact h2 _ ⟨i, hi, x, rfl⟩ w hw)
  let p : FreeAlgebra ℂ X →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ := (e : (ρ 0).range →ₐ[ℂ] _).comp (ρ 0).rangeRestrict
  have hp : Function.Surjective p := e.surjective.comp (ρ 0).rangeRestrict_surjective
  have hp0 : ∀ a, p a = 0 → ρ 0 a = 0 := by
    intro a ha
    have h1 : e ((ρ 0).rangeRestrict a) = 0 := ha
    have h2 : (ρ 0).rangeRestrict a = 0 := (map_eq_zero_iff e e.injective).1 h1
    exact congrArg Subtype.val h2
  choose r hr using fun i => factor_alg p hp (ρ i) (fun a ha => hker a (hp0 a ha) i)
  obtain ⟨c, hc, H⟩ := UpperTheory.ConvolutionTheory.L1.unitsTrace W m d r
    (by
      intro i j hij a b
      obtain ⟨a, rfl⟩ := hp a
      obtain ⟨b, rfl⟩ := hp b
      rw [hr, hr]
      exact hρρ i j hij a b)
    (by
      intro P h
      apply hirr P
      intro i x w hw
      rw [← hρι, ← hr]
      exact h _ _ w hw)
    U
    (by
      intro i a w
      obtain ⟨a, rfl⟩ := hp a
      rw [hr, hr, hρU])
  refine ⟨c, hc, fun i₀ S hS => H i₀ S ?_⟩
  intro j hj a
  obtain ⟨a, rfl⟩ := hp a
  rw [hr]
  exact comm_lift (T j) S (hS j hj) a
end
