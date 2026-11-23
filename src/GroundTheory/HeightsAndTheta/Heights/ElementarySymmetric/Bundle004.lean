module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

theorem FramePlaneGraph.zeroSetEuc_sup_span {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (q : MvPolynomial (Fin n) ℂ) :
    zeroSetEuc (J ⊔ Ideal.span {q}) = zeroSetEuc J ∩ {z | eval (fun i => z i) q = 0} := by
  ext z
  simp only [zeroSetEuc, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun p hp => h p (Ideal.mem_sup_left hp),
      h q (Ideal.mem_sup_right (Ideal.mem_span_singleton_self q))⟩
  · rintro ⟨h1, h2⟩ p hp
    have hle : J ⊔ Ideal.span {q} ≤ RingHom.ker (eval fun i => z i) :=
      sup_le (fun p hp => RingHom.mem_ker.mpr (h1 p hp))
        ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr h2))
    exact RingHom.mem_ker.mp (hle hp)

theorem FramePlaneGraph.lt_of_add_one_le_nat {x : WithBot ℕ∞} {d : ℕ} (h : x + 1 ≤ (d : WithBot ℕ∞)) :
    x < d := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe y =>
    have h' : y + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
    have hy : y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h')
    have : y < d := (ENat.add_one_le_iff hy).mp h'
    exact_mod_cast this

theorem FramePlaneGraph.dim_sup_span_lt {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) {q : MvPolynomial (Fin n) ℂ} (hq : q ∉ J) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {q})) < d := by
  have hr : Ideal.Quotient.mk J q ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hle : J ≤ J ⊔ Ideal.span {q} := le_sup_left
  have h1 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) hr (by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self q))
  exact FramePlaneGraph.lt_of_add_one_le_nat (hd ▸ h1)

theorem FramePlaneGraph.proof (hG : FrameGraphGeneric.Statement) : FramePlaneGraph.Statement := by
  intro n d J hJ hd b
  obtain ⟨I₀, q, hcard, hq, hloc⟩ := hG n d J hJ hd b
  refine ⟨I₀, J ⊔ Ideal.span {q}, hcard, FramePlaneGraph.dim_sup_span_lt hJ hd hq, ?_⟩
  set W : Set (EuclideanSpace ℂ (Fin n)) := {z | eval (fun i => z i) q ≠ 0} with hWdef
  have hS : zeroSetEuc J \ zeroSetEuc (J ⊔ Ideal.span {q}) = zeroSetEuc J ∩ W := by
    rw [FramePlaneGraph.zeroSetEuc_sup_span]
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, hWdef]
    tauto
  have hW : IsOpen W := isOpen_ne_fun ((MvPolynomial.continuous_eval q).comp
    (by fun_prop : Continuous fun z : EuclideanSpace ℂ (Fin n) => fun i => z i)) continuous_const
  rw [hS]
  intro z hz
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hπ, hgraph⟩ := hloc z hz.1 hz.2
  refine ⟨Ω ∩ g ⁻¹' W, V ∩ W, g, hg.continuousOn.isOpen_inter_preimage hΩ hW, hV.inter hW,
    ⟨hzV, hz.2⟩, hg.mono Set.inter_subset_left, fun w hw => hπ w hw.1, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hxJ, hxW⟩, hxV, -⟩
    have hx : x ∈ g '' Ω := hgraph ▸ ⟨hxJ, hxV⟩
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨w, ⟨hw, hxW⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hwW⟩, rfl⟩
    have hx : g w ∈ zeroSetEuc J ∩ V := hgraph.symm ▸ ⟨w, hw, rfl⟩
    exact ⟨⟨hx.1, hwW⟩, hx.2, hwW⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

theorem FrameGraphGeneric.proof (hA : FrameJacobianGeneric.Statement) (hB : FrameImplicitGraph.Statement) :
    FrameGraphGeneric.Statement := by
  intro n d J hJ hd b
  obtain ⟨I₀, f, s, hcard, hfJ, hs, hM, hgen⟩ := hA n d J hJ hd b
  refine ⟨I₀, frameJacobianDet b I₀ f * s, hcard, fun h => (hJ.mem_or_mem h).elim hM hs, ?_⟩
  intro z hz hq
  rw [map_mul] at hq
  set W : Set (EuclideanSpace ℂ (Fin n)) := {x | eval (fun i => x i) s ≠ 0} with hWdef
  have hW : IsOpen W := isOpen_ne_fun ((MvPolynomial.continuous_eval s).comp
    (by fun_prop : Continuous fun x : EuclideanSpace ℂ (Fin n) => fun i => x i)) continuous_const
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hVW, hg, hproj, hgraph⟩ :=
    hB n b I₀ f z (fun k => hz _ (hfJ k)) (left_ne_zero_of_mul hq) W hW (right_ne_zero_of_mul hq)
  refine ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, ?_⟩
  rw [← hgraph]
  ext x
  simp only [zeroSetEuc, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hxV⟩
    exact ⟨fun k => hx _ (hfJ k), hxV⟩
  · rintro ⟨hx, hxV⟩
    refine ⟨fun p hp => ?_, hxV⟩
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker (eval fun i => x i) :=
      Ideal.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact RingHom.mem_ker.mpr (hx k))
    have h0 := RingHom.mem_ker.mp (hle (hgen p hp))
    rw [map_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hVW hxV)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

namespace FrameImplicitGraph

variable {n : ℕ}

def polyDeriv (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
  ∑ l, eval (fun i => x i) (pderiv l p) • EuclideanSpace.proj l

theorem polyDeriv_apply (p : MvPolynomial (Fin n) ℂ) (x v : EuclideanSpace ℂ (Fin n)) :
    polyDeriv p x v = ∑ l, eval (fun i => x i) (pderiv l p) * v l := by
  simp [polyDeriv]

theorem hasStrictFDerivAt_eval (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    HasStrictFDerivAt (fun y : EuclideanSpace ℂ (Fin n) => eval (fun i => y i) p) (polyDeriv p x) x :=
  _root_.UpperTheory.Reformulated.B.Qi29.hasStrictFDerivAt_eval p x

def projCLM (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) :=
  ContinuousLinearMap.pi fun i : I => innerSL ℂ (b i)

def phi (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    (I → ℂ) × ({j // j ∉ I} → ℂ) :=
  (frameProj b I x, fun k => eval (fun i => x i) (f k))

def phiDeriv (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ) :=
  (projCLM b I).prod (ContinuousLinearMap.pi fun k => polyDeriv (f k) x)

theorem hasStrictFDerivAt_phi (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    HasStrictFDerivAt (phi b I f) (phiDeriv b I f x) x :=
  (projCLM b I).hasStrictFDerivAt.prodMk (hasStrictFDerivAt_pi.2 fun k => hasStrictFDerivAt_eval (f k) x)

theorem phiDeriv_injective (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n))
    (hx : eval (fun i => x i) (frameJacobianDet b I f) ≠ 0) :
    Function.Injective (phiDeriv b I f x) := by
  refine (injective_iff_map_eq_zero (phiDeriv b I f x)).2 fun v hv => ?_
  set c : Fin n → ℂ := fun j => inner ℂ (b j) v with hc
  have h1 : ∀ i ∈ I, c i = 0 := fun i hi => by
    have := congrFun (congrArg Prod.fst hv) ⟨i, hi⟩
    simpa [phiDeriv, projCLM, c] using this
  have hvl : ∀ l, v l = ∑ j, c j * b j l := fun l => by
    have := congrArg (fun y : EuclideanSpace ℂ (Fin n) => y l) (b.sum_repr' v)
    simpa [c, smul_eq_mul] using this.symm
  have h2 : ∀ k, ∑ j, c j * eval (fun i => x i) (frameDeriv b j (f k)) = 0 := fun k => by
    have := congrFun (congrArg Prod.snd hv) k
    simp only [phiDeriv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply, polyDeriv_apply,
      Prod.snd_zero, Pi.zero_apply] at this
    rw [← this]

    simp only [frameDeriv, map_sum, map_mul, eval_C, hvl, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  let M : Matrix {j // j ∉ I} {j // j ∉ I} ℂ := Matrix.of fun k j => eval (fun i => x i) (frameDeriv b j (f k))
  have hM : M.det ≠ 0 := by
    have : eval (fun i => x i) (frameJacobianDet b I f) = M.det := by
      rw [frameJacobianDet, RingHom.map_det]
      rfl
    rwa [← this]
  have hMc : M.mulVec (fun j => c j) = 0 := by
    funext k
    rw [Pi.zero_apply, ← h2 k, ← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ I)]
    simp [M, Matrix.mulVec, dotProduct, h1, mul_comm]
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hM hMc
  have hc0 : ∀ j, c j = 0 := fun j => by
    by_cases hj : j ∈ I
    · exact h1 j hj
    · exact congrFun h3 ⟨j, hj⟩
  have hv' : v = ∑ j, c j • b j := (b.sum_repr' v).symm
  rw [hv']
  simp [hc0]

theorem finrank_eq (I : Finset (Fin n)) :
    Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Module.finrank ℂ ((I → ℂ) × ({j // j ∉ I} → ℂ)) := by
  have h1 : Fintype.card {j // j ∉ I} = n - I.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    simp
  have h2 : I.card ≤ n := by simpa using I.card_le_univ
  simp only [finrank_euclideanSpace, Fintype.card_fin, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    h1, Fintype.card_coe]
  omega

theorem phiDeriv_equiv (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n))
    (hx : eval (fun i => x i) (frameJacobianDet b I f) ≠ 0) :
    ∃ e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ),
      (e : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ)) = phiDeriv b I f x := by
  refine ⟨(LinearMap.linearEquivOfInjective (phiDeriv b I f x : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] _)
    (phiDeriv_injective b I f x hx) (finrank_eq I)).toContinuousLinearEquiv, ?_⟩
  ext v
  all_goals simp [LinearMap.linearEquivOfInjective_apply]

theorem continuous_eval (p : MvPolynomial (Fin n) ℂ) :
    Continuous fun y : EuclideanSpace ℂ (Fin n) => eval (fun i => y i) p :=
  continuous_iff_continuousAt.2 fun x => (hasStrictFDerivAt_eval p x).continuousAt

theorem proof : FrameImplicitGraph.Statement := by
  intro n b I f z hz hdet U hU hzU
  obtain ⟨e0, he0⟩ := phiDeriv_equiv b I f z hdet
  have hs : HasStrictFDerivAt (phi b I f)
      (e0 : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ)) z :=
    he0 ▸ hasStrictFDerivAt_phi b I f z
  let e := hs.toOpenPartialHomeomorph (phi b I f)
  have hecoe : (e : EuclideanSpace ℂ (Fin n) → (I → ℂ) × ({j // j ∉ I} → ℂ)) = phi b I f := rfl
  let W := {x : EuclideanSpace ℂ (Fin n) | eval (fun i => x i) (frameJacobianDet b I f) ≠ 0}
  have hW : IsOpen W := isOpen_ne_fun (continuous_eval _) continuous_const
  let V := e.source ∩ U ∩ W
  have hV : IsOpen V := (e.open_source.inter hU).inter hW
  let ι : (I → ℂ) → (I → ℂ) × ({j // j ∉ I} → ℂ) := fun w => (w, 0)
  have hι : Continuous ι := continuous_id.prodMk continuous_const
  refine ⟨ι ⁻¹' (e.target ∩ e.symm ⁻¹' V), V, fun w => e.symm (ι w),
    (e.continuousOn_symm.isOpen_inter_preimage e.open_target hV).preimage hι, hV,
    ⟨⟨hs.mem_toOpenPartialHomeomorph_source, hzU⟩, hdet⟩, fun x hx => hx.1.2, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨ex, hex⟩ := phiDeriv_equiv b I f _ hw.2.2
    have hd : HasFDerivAt e (ex : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ))
        (e.symm (ι w)) := by
      rw [hecoe, hex]
      exact (hasStrictFDerivAt_phi b I f _).hasFDerivAt
    have hιd : HasFDerivAt ι ((ContinuousLinearMap.id ℂ (I → ℂ)).prod 0) w :=
      (hasFDerivAt_id w).prodMk (hasFDerivAt_const 0 w)
    exact ((e.hasFDerivAt_symm hw.1 hd).comp w hιd).differentiableAt.differentiableWithinAt
  · intro w hw
    have := congrArg Prod.fst (e.right_inv hw.1)
    rw [hecoe] at this
    exact this
  · ext x
    constructor
    · rintro ⟨hx0, hxV⟩
      have hex : e x = ι (frameProj b I x) := by
        rw [hecoe]
        exact Prod.ext rfl (funext hx0)
      refine ⟨frameProj b I x, ⟨?_, ?_⟩, ?_⟩
      · rw [← hex]; exact e.map_source hxV.1.1
      · show e.symm (ι (frameProj b I x)) ∈ V
        rw [← hex, e.left_inv hxV.1.1]; exact hxV
      · show e.symm (ι (frameProj b I x)) = x
        rw [← hex, e.left_inv hxV.1.1]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨fun k => ?_, hw.2⟩
      have := congrArg (fun p => p.2 k) (e.right_inv hw.1)
      rw [hecoe] at this
      exact this

end FrameImplicitGraph

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def InterNumPointDeg.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), IsSubvar x pp 0 →
      interNum pp (![] : Fin 0 → SubSystem k x Ω) =
        (FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CutRestrLenExact.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (Lc : LineBundle k x) (s : Ω),
      IsSubvar x pp e → s ∈ Lc.secs → (∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) →
      ∀ Q : LineBundle k x, ∀ᶠ c : ℕ in atTop,
        restrLen pp ((Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ))) -
            restrLen pp (Q.toSubSystem.twist (twistSys k x (c : ℤ))) =
          restrLen (pp ⊔ zeroIdeal Lc.toSubSystem s)
            ((Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def InterNumAdditive.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (i : Fin n)
      (L' L'' : LineBundle k x), IsSubvar x pp n →
      interNum pp (Function.update (fun j => (L j).toSubSystem) i (L'.twist L''.toSubSystem)) =
        interNum pp (Function.update (fun j => (L j).toSubSystem) i L'.toSubSystem) +
          interNum pp (Function.update (fun j => (L j).toSubSystem) i L''.toSubSystem)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w


open Classical in
def InterNumCut.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (Lc : LineBundle k x) (s : Ω),
      IsSubvar x pp (n + 1) → s ∈ Lc.secs → (∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) →
      interNum pp (Fin.snoc (α := fun _ => SubSystem k x Ω) (fun i => (L i).toSubSystem)
          Lc.toSubSystem) =
        ∑ᶠ qq : Ideal (Poly k N),
          if h : qq ∈ (pp ⊔ zeroIdeal Lc.toSubSystem s).minimalPrimes ∧ IsSubvar x qq n then
            haveI : qq.IsPrime := h.1.1.1
            ((cutMult (pp ⊔ zeroIdeal Lc.toSubSystem s) qq).toNat : ℤ) *
              interNum qq (fun i => (L i).toSubSystem)
          else 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def InterNumEventual.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x), IsSubvar x pp n →
      ∃ m : ℤ, ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L i).toSubSystem) c = m

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def InterSumTopVanish.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin (n + 1) → LineBundle k x), IsSubvar x pp n →
      ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L i).toSubSystem) c = 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end
