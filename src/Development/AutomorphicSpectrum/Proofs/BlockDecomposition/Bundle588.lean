module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle569
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDense
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle577
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle578
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.NormCongr

theorem aeval_intertwine {K : Type} [Field K] {n : ℕ} {X Y H : Matrix (Fin n) (Fin n) K}
    (h : X * H = H * Y) (p : K[X]) : aeval X p * H = H * aeval Y p := by
  have hpow : ∀ k : ℕ, X ^ k * H = H * Y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Matrix.mul_assoc, hpow, ← Matrix.mul_assoc,
      Algebra.commutes a H, Matrix.mul_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_norms_of_congr (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
    (n : ℕ) (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n)
    (H₀ : Matrix (Fin n) (Fin n) E) (hdet : H₀.det ≠ 0)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E))
    (hc1 : c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) =
      (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hc2 : (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m =
      cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly)
    (ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q)
    (hι1 : ∀ e : E, ι (algebraMap E _ e) = (1 : k) ⊗ₜ algebraMap E (Fld Q) e)
    (hιc : ∀ y, involBase Q k (ι y) = ι (cj w y))
    (x : (k ⊗[maximalRealSubfield E] plus Q)ˣ)
    (hx : inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) = eval₂ ι ((1 : k) ⊗ₜ alpha Q) m) :
    x ∈ norms Q k := by
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := γ₀.val.map (algebraMap E (w.adicCompletion E)) with hA
  set H : Matrix (Fin n) (Fin n) (w.adicCompletion E) := H₀.map (algebraMap E (w.adicCompletion E)) with hH
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ₀.val.charpoly := Matrix.charpoly_map _ _
  obtain ⟨f, hf⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A c.val hAsep hc1.symm
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcA : cT (cj w) A * H * A = H := by
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hinv
    simp only [Matrix.map_mul, cT_map hU w hw] at this
    exact this
  have hHu : IsUnit H.det := by
    rw [hH, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hdet.isUnit).map _
  have hcT : cT (cj w) A * H = H * aeval A (atPl w r₀) := by
    calc cT (cj w) A * H = cT (cj w) A * H * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = H * aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA]
  have hdiv : atPl w γ₀.val.charpoly ∣ (f.map (cj w)).comp (atPl w r₀) * f - m := by
    rw [← hAP]
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ ?_
    have h1 : cT (cj w) (aeval A f) * H = H * aeval A ((f.map (cj w)).comp (atPl w r₀)) := by
      rw [GlobalTheory.NormInert.cT_aeval, aeval_intertwine hcT, aeval_comp]
    have h2 : H * aeval A m = H * (aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f) := by
      rw [hc2, hf, h1, Matrix.mul_assoc]
    have h3 : aeval A m = aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f := by
      have hHi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ hHu
      calc aeval A m = H⁻¹ * H * aeval A m := by rw [hHi, Matrix.one_mul]
        _ = H⁻¹ * H * (aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f) := by
          rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
        _ = _ := by rw [hHi, Matrix.one_mul]
    rw [map_sub, map_mul, ← h3, sub_self]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q := (involBase Q k).toRingHom
  let Φ : (w.adicCompletion E)[X] →+* k ⊗[maximalRealSubfield E] Fld Q := eval₂RingHom ι ((1 : k) ⊗ₜ alpha Q)
  let g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom
  have hΦ : ∀ p : E[X], Φ (atPl w p) = (1 : k) ⊗ₜ AdjoinRoot.mk Q.1 p := by
    intro p
    have e : ι.comp (algebraMap E _) = g.comp (algebraMap E (Fld Q)) := RingHom.ext fun e => hι1 e
    change eval₂ ι ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E (w.adicCompletion E))) = _
    rw [eval₂_map, e]
    refine (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_
    change (1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _
    rw [← aeval_def]
    congr 1
    exact AdjoinRoot.aeval_eq p
  have hR : Φ (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [hΦ]
    congr 1
    have h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hinvΦ : ib (Φ f) = Φ ((f.map (cj w)).comp (atPl w r₀)) := by
    have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
    have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
      change (1 : k) ⊗ₜ invol Q (alpha Q) = _
      rw [invol_alpha]
    change ib (eval₂ ι _ f) = eval₂ ι _ _
    rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
    exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm
  obtain ⟨t, ht⟩ := hdiv
  have hft : f * (f.map (cj w)).comp (atPl w r₀) = m + atPl w γ₀.val.charpoly * t := by
    rw [← ht]; ring
  have h0 : Φ (atPl w γ₀.val.charpoly) = 0 := by
    rw [hΦ]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  have hz : Φ f * ib (Φ f) = inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) := by
    rw [hinvΦ, ← map_mul, hft, map_add (f := _), map_mul, h0, zero_mul, add_zero, hx]
    rfl
  have hu : IsUnit (Φ f) :=
    isUnit_of_mul_isUnit_left (by rw [hz]; exact x.isUnit.map _)
  exact ⟨hu.unit, Units.ext hz⟩

theorem mem_norms_of_congr_equiv (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
    (j : w.adicCompletion E ≃+* k ⊗[maximalRealSubfield E] E)
    (hj1 : ∀ e : E, j (algebraMap E _ e) = 1 ⊗ₜ e)
    (hj2 : ∀ x, j (cj w x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k)
      ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x))
    (n : ℕ) (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n)
    (H₀ : Matrix (Fin n) (Fin n) E) (hdet : H₀.det ≠ 0)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E))
    (hc1 : c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) =
      (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hc2 : (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m =
      cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly)
    (x : (k ⊗[maximalRealSubfield E] plus Q)ˣ)
    (hx : inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) =
      eval₂ (((inclBase Q k).toRingHom).comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) m) :
    x ∈ norms Q k := by
  refine mem_norms_of_congr hU w hw k n γ₀ hell H₀ hdet hinv m c hc1 hc2 r Q hQ _ (fun e => ?_) (fun y => ?_) x hx
  · change inclBase Q k (j (algebraMap E _ e)) = _
    rw [hj1]
    simp [inclBase]
  · change involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cj w y))
    rw [hj2]
    generalize j y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.CompanionTheory.NormCongr
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.FinPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  have ht := ThBasic.continuous_thL hU n w
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = id := funext fun y => by simp [nrmL, hs]
    rw [e]
    exact continuous_id
  · have e : nrmL n w = fun y => y * thL n w y := funext fun y => by simp [nrmL, thL, hs]
    rw [e]
    exact continuous_id.mul ht

theorem isClosed_KGL (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsClosed (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) :=
  (ThBasic.twist_basic E hU n w).2.2.2.2.2.1.isClosed

theorem nrmL_mem_KGL (hU : Unr E) (n : ℕ) (w : Pl E) {y : GLw n w} (hy : y ∈ GlobalTheory.LFun.KGL w (n := n)) :
    nrmL n w y ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have ht := ThBasic.thL_mem_KGL hU n w y hy
  unfold nrmL
  unfold thL at ht
  split_ifs at ht ⊢ with hs
  · exact hy
  · exact mul_mem hy ht

theorem mem_prod_of_mem_tsupport (hU : Unr E) (a b : ℕ) (w : Pl E) {y : GLw a w × GLw b w}
    (hy : y ∈ tsupport ((((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) : Set (GLw a w × GLw b w)).indicator
      (1 : GLw a w × GLw b w → ℂ))) :
    y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) := by
  have hcl : IsClosed (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (isClosed_KGL hU a w).prod (isClosed_KGL hU b w)
  have h := closure_minimal Set.support_indicator_subset hcl hy
  exact Subgroup.mem_prod.1 h

theorem finite_pairs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S → ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ, (∀ w, HasCompactSupport (φ w)) → (∀ᶠ w in cofinite, φ w = (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) : Set (GLw a w × GLw b w)).indicator 1) → {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ ∀ w ∈ S, ∃ y : GLw a w × GLw b w, φ w y ≠ 0 ∧ (nrmL a w y.1).val.charpoly = atPl w p.1 ∧ (nrmL b w y.2).val.charpoly = atPl w p.2}.Finite := by
  intro E _ _ _ hU a b S hS φ hc hφ
  let C₁ : ∀ w : Pl E, Set (GLw a w) := fun w => nrmL a w '' (Prod.fst '' tsupport (φ w))
  let C₂ : ∀ w : Pl E, Set (GLw b w) := fun w => nrmL b w '' (Prod.snd '' tsupport (φ w))
  have hC₁ : ∀ w, IsCompact (C₁ w) := fun w =>
    ((hc w).isCompact.image continuous_fst).image (continuous_nrmL hU a w)
  have hC₂ : ∀ w, IsCompact (C₂ w) := fun w =>
    ((hc w).isCompact.image continuous_snd).image (continuous_nrmL hU b w)
  have hK₁ : ∀ᶠ w in cofinite, C₁ w ⊆ GlobalTheory.LFun.KGL w (n := a) := by
    filter_upwards [hφ] with w hw
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [hw] at hy
    exact nrmL_mem_KGL hU a w (mem_prod_of_mem_tsupport hU a b w hy).1
  have hK₂ : ∀ᶠ w in cofinite, C₂ w ⊆ GlobalTheory.LFun.KGL w (n := b) := by
    filter_upwards [hφ] with w hw
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [hw] at hy
    exact nrmL_mem_KGL hU b w (mem_prod_of_mem_tsupport hU a b w hy).2
  refine ((GlobalTheory.T.finite_ellipticCharpoly_compact_section E a S hS C₁ hC₁ hK₁).prod (GlobalTheory.T.finite_ellipticCharpoly_compact_section E b S hS C₂ hC₂ hK₂)).subset ?_
  rintro p ⟨h₁, h₂, h⟩
  refine ⟨⟨h₁, fun w hw => ?_⟩, ⟨h₂, fun w hw => ?_⟩⟩
  · obtain ⟨y, hy, e₁, -⟩ := h w hw
    exact ⟨_, ⟨y.1, ⟨y, subset_tsupport _ hy, rfl⟩, rfl⟩, e₁⟩
  · obtain ⟨y, hy, -, e₂⟩ := h w hw
    exact ⟨_, ⟨y.2, ⟨y, subset_tsupport _ hy, rfl⟩, rfl⟩, e₂⟩

end GlobalTheory.CompanionTheory.FinPol
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.RatCentComm

theorem commute_norm {G : Type} [Group G] (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (D g : G)
    (hg : g ∈ twCent θ D) : g * (D * θ D) = (D * θ D) * g := by
  have h1 : g * D = D * θ g := hg
  have h2 : θ g = D⁻¹ * g * D := by rw [mul_assoc, h1]; group
  have h3 := congrArg θ h2
  rw [hθ, map_mul, map_mul, map_inv, h2] at h3
  calc g * (D * θ D)
      = (D * θ D) * ((θ D)⁻¹ * (D⁻¹ * g * D) * θ D) := by group
    _ = _ := by rw [← h3]

theorem twCent_ratF_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E),
    (δ * thE E n δ).val.charpoly.Separable →
    ∀ a ∈ twCent (thF E n) (ratF E n δ), ∀ b ∈ twCent (thF E n) (ratF E n δ), a * b = b * a := by
  intro E _ _ _ n δ hs a ha b hb
  have hθ : ∀ g, thF E n (thF E n g) = g :=
    GlobalTheory.LocTwist.thetaGL_thetaGL n _ (fun y => GlobalTheory.ThetaPull.cFin_cFin y)
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E n δ * thF E n (ratF E n δ)).val
      (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [GlobalTheory.MassNorm.thF_ratF, ← map_mul]
    exact h1
  have hc : ∀ g ∈ twCent (thF E n) (ratF E n δ),
      Commute g.val (ratF E n δ * thF E n (ratF E n δ)).val := fun g hg => by
    change g.val * _ = _ * g.val
    rw [← Units.val_mul, ← Units.val_mul, commute_norm _ hθ _ _ hg]
  obtain ⟨p, hp⟩ := GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc a ha)
  obtain ⟨q, hq⟩ := GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc b hb)
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]

end GlobalTheory.CompanionTheory.RatCentComm
end
end

section

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MuLocal

open Formalism.L2.Host GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUnitAt_of_valuation (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ)
    (h : ValuativeRel.valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1) : IsUnitAt w x := by
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have h1 := GlobalTheory.SmGL.ord_eq_zero_iff.2 h
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at h1
  rw [IsUnitAt, ← WithZero.exp_log h0, h1, WithZero.exp_zero]

theorem loc_eq_unrChar {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) :
    χ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (χ.val w) :=
  GlobalTheory.PrinSat.eq_unrChar_of_ord (fun x hx => h x (isUnitAt_of_valuation w x hx)) (GlobalTheory.PrinSat.ord_unif w)

theorem loc_pow (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) (x : (w.adicCompletion E)ˣ) :
    (χ ^ k).loc w x = χ.loc w x ^ k := by
  simp [HChar.loc]

theorem loc_mul_loc_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : GlobalTheory.BCT.IsMu μ e) (w : HeightOneSpectrum (𝓞 E))
    (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ) :
    μ.loc (GlobalTheory.ThetaSatake.cw w) x * μ.loc w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) = 1 := by
  have h1 := GlobalTheory.BCT.MuProps.mu_mul_conj h (Neutral.B1.localIdele E _ x)
  rw [GlobalTheory.PolChar.ideleConj_eq, GlobalTheory.ThetaPull.conjAd_localIdele] at h1
  exact h1

theorem isUnitAt_conj (w : HeightOneSpectrum (𝓞 E)) (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ)
    (hx : IsUnitAt (GlobalTheory.ThetaSatake.cw w) x) :
    IsUnitAt w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) :=
  ((conjLoc_spec _ w).2.2 x.val).trans hx

theorem isUnifAt_conj (w : HeightOneSpectrum (𝓞 E)) (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ)
    (hx : IsUnifAt (GlobalTheory.ThetaSatake.cw w) x) :
    IsUnifAt w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) :=
  ((conjLoc_spec _ w).2.2 x.val).trans hx

end GlobalTheory.CompanionTheory.MuLocal


open GlobalTheory.CompanionTheory.MuLocal Formalism.L2.Host GlobalTheory.CuspRep in
theorem GlobalTheory.CompanionTheory.MuLocal.muLoc_holds : PositivityTheory.Rg.BcB.F.RS.MuLoc := by
  intro E _ _ _ _ μ e w hμ hun
  refine ⟨loc_eq_unrChar hun, fun k => ⟨fun x hx => ?_, ?_⟩, fun u _ hu => ?_⟩
  · rw [loc_pow, hun x hx, one_pow]
  · rw [HChar.val, HChar.locK, MonoidHom.comp_apply, loc_pow]
    rfl
  · obtain rfl := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hu
    have hc := loc_mul_loc_conj hμ w
    refine ⟨fun x hx => ?_, ?_⟩
    · have h2 := hc x
      rw [hun _ (isUnitAt_conj w x hx), mul_one] at h2
      exact h2
    · have h2 := hc (atFin (GlobalTheory.ThetaSatake.cw w) (unif (GlobalTheory.ThetaSatake.cw w)))
      rw [μ.val_eq hun _ (isUnifAt_conj w _ (unif_spec _))] at h2
      exact eq_inv_of_mul_eq_one_left h2

end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.K_finite_vectors_dense : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), IsSubrep (R (latticeGL E a) μ) H → H ≤ (Submodule.span ℂ {F | F ∈ H ∧ IsKFinL2 μ F}).topologicalClosure := by
  first | exact @GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite | exact GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite | (intros; apply GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenberg_character_orthogonality : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ a b : Matrix (Fin ρ) (Fin p) D.host.E → ℂ, Summable (fun η => ‖a η‖) → Summable (fun η => ‖b η‖) → ∫ x in m.𝓕, (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt η) * a η) * conj (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ) * b ξ) ∂m.μ = ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, a η * conj (b η) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.parseval | exact GlobalTheory.CompanionTheory.FJE.parseval | (intros; apply GlobalTheory.CompanionTheory.FJE.parseval <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical


theorem _root_.GlobalTheory.T.pair_involution_continuous : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
  Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧ ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := by
  first | exact @GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts | exact GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts | (intros; apply GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts <;> assumption)
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.convergence_strip : GlobalTheory.CompanionTheory.EGlue.ConvStrip := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | exact GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | (intros; apply GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip <;> assumption)
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.factor_induction : GlobalTheory.CompanionTheory.EGlue.FactorStep := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.factorStep_holds | exact GlobalTheory.CompanionTheory.EGlue.factorStep_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.factorStep_holds <;> assumption)
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.hull_generation : GlobalTheory.CompanionTheory.EGlue.HullGen := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.hullGen | exact GlobalTheory.CompanionTheory.EGlue.hullGen | (intros; apply GlobalTheory.CompanionTheory.EGlue.hullGen <;> assumption)
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.topological_infimum : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.Gl0.topInf | exact GlobalTheory.CompanionTheory.EGlue.Gl0.topInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.Gl0.topInf <;> assumption)
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.capacity_equivalence : GlobalTheory.CompanionTheory.EGlue.CapEquiv := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.capEquiv | exact GlobalTheory.CompanionTheory.EGlue.capEquiv | (intros; apply GlobalTheory.CompanionTheory.EGlue.capEquiv <;> assumption)
end
