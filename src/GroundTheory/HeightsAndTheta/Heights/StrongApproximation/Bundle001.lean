module

public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem AETopologicalRing.aut_mul_self (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) :
    c * c = 1 := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  by_contra h
  have hc2 : c * c ≠ c := fun h' => hc (by simpa using congrArg (c⁻¹ * ·) h')
  have hcard : ({1, c, c * c} : Finset (E ≃ₐ[F] E)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hc2)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hc, Ne.symm h⟩
  have hle := Finset.card_le_univ ({1, c, c * c} : Finset (E ≃ₐ[F] E))
  have := AlgEquiv.card_le (F := F) (K := E)
  omega

theorem AETopologicalRing.exists_anti (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) :
    ∃ δ : E, c δ = -δ ∧ δ ≠ 0 := by
  have hcc := AETopologicalRing.aut_mul_self c h2 hc
  obtain ⟨x, hx⟩ : ∃ x, c x ≠ x := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  refine ⟨x - c x, ?_, sub_ne_zero.2 (Ne.symm hx)⟩
  have hx2 : c (c x) = x := by rw [← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply]
  rw [map_sub, hx2]
  ring


omit [NumberField F] in
theorem AETopologicalRing.linearIndependent_one_anti (c : E ≃ₐ[F] E) {δ : E} (hδ : c δ = -δ)
    (h0 : δ ≠ 0) : LinearIndependent F ![(1 : E), δ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
  have h' := congrArg c hst
  simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hδ, map_zero] at h'
  have ht : algebraMap F E t = 0 := by
    have : (2 * δ) * algebraMap F E t = 0 := by linear_combination hst - h'
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero h0)
  have ht' : t = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).1 ht
  subst ht'
  simp only [map_zero, zero_mul, add_zero] at hst
  exact ⟨(map_eq_zero_iff _ (algebraMap F E).injective).1 hst, rfl⟩

def AETopologicalRing.sigALinear (c : E ≃ₐ[F] E) :
    AE F E →ₗ[FiniteAdeleRing (𝓞 F) F] AE F E :=
  LinearMap.baseChange (FiniteAdeleRing (𝓞 F) F) c.toLinearMap

omit [NumberField E] in
theorem AETopologicalRing.sigALinear_apply (c : E ≃ₐ[F] E) (a : AE F E) :
    AETopologicalRing.sigALinear c a = sigA c a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end


open scoped RestrictedProduct in
theorem AETopologicalRing.t2Space_finiteAdeleRing (F : Type) [Field F] [NumberField F] :
    T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem AETopologicalRing.proof : AETopologicalRing.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have : IsTopologicalRing (AE F E) :=
    IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) (AE F E)
  have hσ : Continuous (sigA c) := by
    have := IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F)
      (AETopologicalRing.sigALinear c)
    convert this using 1
    funext a
    exact (AETopologicalRing.sigALinear_apply c a).symm
  obtain ⟨δ, hδ, h0⟩ := AETopologicalRing.exists_anti c h2 hc
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank (AETopologicalRing.linearIndependent_one_anti c hδ h0)
      (by simp [h2])
  let B := Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b
  have hB0 : B 0 = (1 : AE F E) := by
    simp [B, b, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.one_def]
  have hB1 : B 1 = inclA F E δ := by
    simp [B, b, Algebra.TensorProduct.basis_apply]
    rfl
  have := AETopologicalRing.t2Space_finiteAdeleRing F
  have : T2Space (AE F E) := T2Space.of_injective_continuous B.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F) B.equivFun.toLinearMap)
  refine ⟨inferInstance, hσ, ⟨δ, hδ, fun a => ⟨(B.repr a 0, B.repr a 1), ?_, ?_⟩⟩, fun N J => ?_⟩
  · have := B.sum_repr a
    rw [Fin.sum_univ_two, hB0, hB1] at this
    exact this.symm
  · rintro ⟨p₁, p₂⟩ hp
    rw [hp, ← hB0, ← hB1]
    simp
  · have hmul : Continuous (fun p : Matrix (Fin N) (Fin N) (AE F E) × Matrix (Fin N) (Fin N) (AE F E) =>
        p.1 * p.2) := continuous_fst.matrix_mul continuous_snd
    have hform : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => gᵀ * J * g.map (sigA c)) :=
      (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul (continuous_id.matrix_map hσ)
    have hdet : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => g.det) := continuous_id.matrix_det
    exact ⟨hmul, hform, hdet, (isClosed_eq hdet continuous_const).inter (isClosed_eq hform continuous_const)⟩

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix ReciprocityTheory.ChartRestriction.G.SA

theorem HypPairExists.proof : HypPairExists.Statement := by
  intro E _ σ hσ h2 N J hJ hdet e he0 hee

  have hw : ∃ j, ∑ i, e i * J i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : e ᵥ* J = 0 := by
      ext j
      simpa [vecMul, dotProduct] using h j
    apply he0
    calc e = e ᵥ* (J * J⁻¹) := by rw [mul_nonsing_inv J hdet, vecMul_one]
      _ = (e ᵥ* J) ᵥ* J⁻¹ := by rw [vecMul_vecMul]
      _ = 0 := by rw [h0, zero_vecMul]
  obtain ⟨j, hj⟩ := hw
  have hsingle : hf σ J e (Pi.single j 1) = ∑ i, e i * J i j := by
    simp only [hf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · simp

  obtain ⟨a, hea⟩ : ∃ a : Fin N → E, hf σ J e a = 1 :=
    ⟨σ (∑ i, e i * J i j)⁻¹ • Pi.single j 1, by
      rw [hf_smul_right, hsingle, hσ, inv_mul_cancel₀ hj]⟩
  have hae : hf σ J a e = 1 := by
    rw [← hf_symm hσ hJ, hea, map_one]
  have haa : σ (hf σ J a a) = hf σ J a a := hf_symm hσ hJ a a
  set t : E := -(hf σ J a a) / 2 with ht_def
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  have ht : t + σ t = -(hf σ J a a) := by
    rw [ht_def, map_div₀, map_neg, haa, hσ2]
    field_simp
    ring
  refine ⟨a + t • e, ?_, ?_⟩
  · rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right,
      hf_smul_right, hea, hae, hee]
    linear_combination ht
  · rw [hf_add_right, hf_smul_right, hea, hee, mul_zero, add_zero]

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

section Places

open Classical

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

theorem evalAt_singleF_same (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    evalAt F v (singleF F v x) = x := by
  change Pi.single v x v = x
  simp

theorem evalAt_singleF_ne {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (x : v.adicCompletion F) :
    evalAt F u (singleF F v x) = 0 := by
  change Pi.single v x u = 0
  simp [h]

theorem singleF_mul_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : v.adicCompletion F)
    (y : w.adicCompletion F) : singleF F v x * singleF F w y = 0 := by
  apply FiniteAdeleRing.ext; intro u
  change Pi.single v x u * Pi.single w y u = 0
  by_cases hu : u = v
  · subst hu; simp [h]
  · simp [hu]

theorem singleV_mul_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : Kv E v) (y : Kv E w) :
    singleV E v x * singleV E w y = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp [singleV, Algebra.TensorProduct.tmul_mul_tmul, singleF_mul_of_ne h]
    | add y y' hy hy' => rw [map_add (f := _), mul_add, hy, hy', add_zero]
  | add x x' hx hx' => rw [map_add (f := _), add_mul, hx, hx', add_zero]

theorem compAt_singleV_same (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) :
    compAt E v (singleV E v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [compAt, singleV, evalAt_singleF_same]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx']

theorem compAt_singleV_ne {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (x : Kv E v) :
    compAt E u (singleV E v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [compAt, singleV, evalAt_singleF_ne h]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', add_zero]

theorem compAt_restrictTo (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F))
    (a : AE F E) : compAt E v (restrictTo E S a) = if v ∈ S then compAt E v a else 0 := by

  rw [restrictTo, map_sum]
  split_ifs with hv
  · rw [Finset.sum_eq_single_of_mem v hv (fun w _ hw => compAt_singleV_ne hw.symm _),
      compAt_singleV_same]
  · exact Finset.sum_eq_zero fun w hw => compAt_singleV_ne (by rintro rfl; exact hv hw) _

theorem compAt_inclA (v : HeightOneSpectrum (𝓞 F)) (y : E) :
    compAt E v (inclA F E y) = inclV E v y := by
  simp [compAt, inclA, inclV]

theorem compAt_sigA (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : AE F E) :
    compAt E v (sigA c a) = sigV c v (compAt E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [compAt, sigA, sigV]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), map_add (f := _)]

theorem map_compAt_mem_SU (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) {x : Matrix (Fin N) (Fin N) (AE F E)}
    (hx : x ∈ SU (sigA c) (J.map (inclA F E))) :
    x.map (compAt E v) ∈ SU (sigV c v).toRingHom (J.map (inclV E v)) := by
  obtain ⟨hdet, hu⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · have h := congrArg (compAt E v).mapMatrix hu
    simp only [map_mul, RingHom.mapMatrix_apply] at h
    have hJ : (J.map (inclA F E)).map (compAt E v) = J.map (inclV E v) := by
      ext i j; simp [compAt_inclA]
    have hs : (x.map (sigA c)).map (compAt E v) = (x.map (compAt E v)).map (sigV c v).toRingHom := by
      ext i j; simp [compAt_sigA]
    rw [hJ, hs, Matrix.transpose_map] at h
    exact h

end Places

theorem list_prod_one_add {ι R : Type*} [Ring R] (B : ι → R) (hB : ∀ v w, v ≠ w → B v * B w = 0)
    (l : List ι) (hl : l.Nodup) : (l.map fun v => 1 + B v).prod = 1 + (l.map B).sum := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [ih hl.2]
    have h0 : ∀ l' : List ι, v ∉ l' → B v * (l'.map B).sum = 0 := by
      intro l' hv'
      induction l' with
      | nil => simp
      | cons w l' ih' =>
        rw [List.mem_cons, not_or] at hv'
        rw [List.map_cons, List.sum_cons, mul_add, hB v w hv'.1, ih' hv'.2, add_zero]
    rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, h0 l hl.1]
    abel

theorem Truncation.proof (hLoc : LocalInClosure.Statement) : Truncation.Statement := by
  classical
  intro F E _ _ _ _ _ c hE hc N J hJ hdet hiso _ _ S x
  have part3 : ∀ l : List (HeightOneSpectrum (𝓞 F)), l.Nodup → (∀ v, v ∈ l ↔ v ∈ S) →
      trunc E S x = (l.map fun v => embed E v (x.map (compAt E v))).prod := by
    intro l hl hlS
    have hB : ∀ v w : HeightOneSpectrum (𝓞 F), v ≠ w →
        (x.map (compAt E v) - 1).map (singleV E v) * (x.map (compAt E w) - 1).map (singleV E w) = 0 := by
      intro v w h
      ext i j
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun k _ => singleV_mul_of_ne h _ _
    rw [show (fun v => embed E v (x.map (compAt E v))) =
      fun v => 1 + (x.map (compAt E v) - 1).map (singleV E v) from rfl, list_prod_one_add _ hB l hl]
    have hS : l.toFinset = S := by ext v; rw [List.mem_toFinset, hlS]
    rw [← List.sum_toFinset _ hl, hS, trunc]
    congr 1
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.map_apply, restrictTo, Matrix.sub_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_sub, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨?_, ?_, part3, ?_⟩
  · intro v hv
    ext i j
    simp only [trunc, Matrix.map_apply, Matrix.add_apply, map_add (f := _), compAt_restrictTo, if_pos hv,
      Matrix.sub_apply, map_sub]
    abel
  · intro v hv
    ext i j
    simp only [trunc, Matrix.map_apply, Matrix.add_apply, map_add (f := _), compAt_restrictTo, if_neg hv,
      add_zero]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro hx
    have : Module.Finite F E := Module.finite_of_finrank_eq_succ hE
    have : IsTopologicalRing (AE F E) :=
      IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) (AE F E)
    rw [part3 S.toList (Finset.nodup_toList S) (fun v => Finset.mem_toList)]
    have hmem : ∀ l : List (HeightOneSpectrum (𝓞 F)),
        (l.map fun v => embed E v (x.map (compAt E v))).prod ∈ Cl c J := by
      intro l
      induction l with
      | nil =>
        exact subset_closure ⟨1, one_mem_SU, Matrix.map_one _ (map_zero _) (map_one _)⟩
      | cons v l ih =>
        rw [List.map_cons, List.prod_cons]
        refine map_mem_closure₂ continuous_mul
          (hLoc F E c hE hc N J hJ hdet hiso v _ (map_compAt_mem_SU c v J hx)) ih ?_
        rintro _ ⟨γ, hγ, rfl⟩ _ ⟨γ', hγ', rfl⟩
        exact ⟨γ * γ', mul_mem_SU hγ hγ', Matrix.map_mul⟩
    exact hmem _

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem SAHolds.of_neighbourhoods_truncation (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement := by
  classical
  intro F E _ _ _ _ _ c hrk hc N J hJ hdet hiso _ _ x hx
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  obtain ⟨hN1, hN2⟩ := hNb F E c hrk hc
  change x ∈ Cl c J
  rw [Cl, ← closure_closure, mem_closure_iff_nhds]
  intro U hU
  have hU' : (fun M => x + M) ⁻¹' U ∈ 𝓝 (0 : Matrix (Fin N) (Fin N) (AE F E)) := by
    have hcont : Continuous (fun M : Matrix (Fin N) (Fin N) (AE F E) => x + M) :=
      continuous_const.add continuous_id
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hU
  obtain ⟨S₀, hS₀⟩ := hN1 N _ hU'
  choose T hT using fun p : Fin N × Fin N => hN2 (x p.1 p.2)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ Finset.univ.biUnion T with hSdef
  obtain ⟨t1, t2, -, t4⟩ := hTr F E c hrk hc N J hJ hdet hiso S x
  refine ⟨trunc E S x, ?_, t4 hx⟩
  have hmem : x + (trunc E S x - x) ∈ U := by
    apply hS₀
    intro i j
    have hS : ∀ v ∈ S, compAt E v ((trunc E S x - x) i j) = 0 := by
      intro v hv
      have h := congrFun (congrFun (t1 v hv) i) j
      simp only [Matrix.map_apply] at h
      rw [Matrix.sub_apply, map_sub, h, sub_self]
    refine ⟨fun v hv => hS v (Finset.mem_union_left _ hv), fun v hv => ?_⟩
    by_cases hvS : v ∈ S
    · rw [hS v hvS]; exact zero_mem _
    · have h := congrFun (congrFun (t2 v hvS) i) j
      simp only [Matrix.map_apply] at h
      have hvT : v ∉ T (i, j) := fun h' =>
        hvS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, h'⟩))
      have hx' : compAt E v (x i j) ∈ intAt E v := hT (i, j) v hvT
      rw [Matrix.sub_apply, map_sub, h]
      refine sub_mem ?_ hx'
      rw [Matrix.one_apply]
      split_ifs
      · exact AddSubgroup.subset_closure
          ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩
      · exact zero_mem _
  simpa using hmem

theorem SAHolds.proof (_hHyp : HypPairExists.Statement) (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement :=
  SAHolds.of_neighbourhoods_truncation hNb hTr

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end
