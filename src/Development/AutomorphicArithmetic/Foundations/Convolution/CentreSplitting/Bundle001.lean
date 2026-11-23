module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Bundle004
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import GroundTheory.AutomorphicForms.TensorProductTheorem.Irreducible
import GroundTheory.AutomorphicForms.TensorProductTheorem.Places
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem le_or_iso {M I : Type} [AddCommGroup M] [Module ℂ M] (A : I → M →ₗ[ℂ] M) (U U' C : Submodule ℂ M)
    (hU : ∀ i, ∀ x ∈ U, A i x ∈ U) (hU' : ∀ i, ∀ x ∈ U', A i x ∈ U') (hC : ∀ i, ∀ x ∈ C, A i x ∈ C)
    (hi : ∀ W ≤ U, (∀ i, ∀ x ∈ W, A i x ∈ W) → W = ⊥ ∨ W = U) (hi' : ∀ W ≤ U', (∀ i, ∀ x ∈ W, A i x ∈ W) → W = ⊥ ∨ W = U')
    (hd : U' ⊓ C = ⊥) (hle : U ≤ U' ⊔ C) :
    U ≤ C ∨ ∃ T : U ≃ₗ[ℂ] U', ∀ i (φ ψ : U), ψ.1 = A i φ.1 → (T ψ).1 = A i (T φ).1 := by
  have uniq : ∀ (x : M) (a b : U'), x - a ∈ C → x - b ∈ C → a = b := fun x a b ha hb => by
    have h1 : (a : M) - b ∈ U' ⊓ C := ⟨U'.sub_mem a.2 b.2, by simpa using C.sub_mem hb ha⟩
    rw [hd, Submodule.mem_bot, sub_eq_zero] at h1
    exact Subtype.ext h1
  have ex : ∀ x : U, ∃ a : U', (x : M) - a ∈ C := fun x => by
    obtain ⟨a, ha, c, hc, e⟩ := Submodule.mem_sup.1 (hle x.2)
    exact ⟨⟨a, ha⟩, by rw [← e]; simpa using hc⟩
  choose p hp using ex
  let P : U →ₗ[ℂ] U' :=
    { toFun := p
      map_add' := fun x y => uniq _ _ _ (hp _) (by
        have := C.add_mem (hp x) (hp y)
        rwa [sub_add_sub_comm] at this)
      map_smul' := fun c x => uniq _ _ _ (hp _) (by
        have := C.smul_mem c (hp x)
        rwa [smul_sub] at this) }
  have hP : ∀ i (φ ψ : U), ψ.1 = A i φ.1 → (P ψ).1 = A i (P φ).1 := fun i φ ψ e =>
    congrArg Subtype.val (uniq ψ.1 (p ψ) ⟨_, hU' i _ (p φ).2⟩ (hp ψ) (by rw [e, ← map_sub]; exact hC i _ (hp φ)))
  rcases hi (U ⊓ C) inf_le_left fun i x hx => ⟨hU i x hx.1, hC i x hx.2⟩ with h0 | h0
  · have hinj : Function.Injective P := (injective_iff_map_eq_zero P).2 fun x hx => by
      have h1 := hp x
      rw [show p x = 0 from hx] at h1
      have h2 : x.1 ∈ U ⊓ C := ⟨x.2, by simpa using h1⟩
      rw [h0] at h2
      exact Subtype.ext h2
    rcases hi' ((LinearMap.range P).map U'.subtype) (Submodule.map_subtype_le _ _) (by
      rintro i _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨⟨_, hU i _ x.2⟩, rfl⟩, hP i x _ rfl⟩) with h1 | h1
    · refine Or.inl fun x hx => ?_
      have h2 : (P ⟨x, hx⟩).1 ∈ (LinearMap.range P).map U'.subtype := ⟨_, ⟨_, rfl⟩, rfl⟩
      rw [h1, Submodule.mem_bot] at h2
      have h3 := hp ⟨x, hx⟩
      rw [show (p ⟨x, hx⟩).1 = 0 from h2] at h3
      simpa using h3
    · refine Or.inr ⟨LinearEquiv.ofBijective P ⟨hinj, fun y => ?_⟩, hP⟩
      obtain ⟨_, ⟨x, rfl⟩, e⟩ := h1.ge y.2
      exact ⟨x, Subtype.ext e⟩
  · exact Or.inl (inf_eq_left.1 h0)

theorem UpperTheory.ConvolutionTheory.Dp.orthOrIso :
    UpperTheory.ConvolutionTheory.Dp.OrthOrIso := by
  intro K _ _ n μ _ U U' l l' hs hs' hi hi'
  obtain ⟨C, hC, hsup, horth⟩ := UpperTheory.V.Af.StrongMultiplicityOne.compl K n μ U' l' hs'
  have hinf : U' ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha, haC⟩
    have hzero := horth a ha a haC
    rw [inner_self_eq_zero] at hzero
    exact (Submodule.mem_bot ℂ).2 (CuspidalSpectrum.eq_zero_of_cuspVecL_eq_zero (μ := μ) (l' ha) hzero)
  let A : ((isExpLieAlgebra K n).lieSubalgebra ⊕ archCompact K n ⊕ AdelicGLn.FiniteAdelicGL K n) → cuspForms K n →ₗ[ℂ] cuspForms K n :=
    Sum.elim (fun X => (gkModuleCusp K n).ρ X) (Sum.elim (fun k => (gkModuleCusp K n).σ k) fun g => finRepCusp K n g)
  have hA : ∀ W, Fb.Stab W ↔ ∀ i, ∀ x ∈ W, A i x ∈ W := fun W =>
    ⟨fun h i => by
      rcases i with X | k | g
      exacts [h.ρ X, h.σ k, h.τ g], fun h => ⟨fun X => h (.inl X), fun k => h (.inr (.inl k)), fun g => h (.inr (.inr g))⟩⟩
  rcases le_or_iso A U U' C ((hA _).1 hs) ((hA _).1 hs') ((hA _).1 hC) (fun W h1 h2 => hi W h1 ((hA _).2 h2))
    (fun W h1 h2 => hi' W h1 ((hA _).2 h2)) hinf (l.trans hsup.ge) with h | ⟨T, hT⟩
  · refine Or.inl (Submodule.IsOrtho.symm ?_)
    rw [Submodule.isOrtho_iff_inner_eq]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact horth a ha b (h hb)
  · exact Or.inr ⟨T, fun X => hT (.inl X), fun k => hT (.inr (.inl k)), fun g => hT (.inr (.inr g))⟩
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem comap_irreducible {G H L : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (π : UnitaryRep G H) (ρ : UnitaryRep G L) (T : H →L[ℂ] L) (hT : ∀ v, ‖T v‖ = ‖v‖)
    (hTπ : ∀ g v, T (π g v) = ρ g (T v)) (V : Submodule ℂ L)
    (hle : ∀ x ∈ V, ∃ v, T v = x) (hcl : IsClosed (V : Set L)) (hinv : ρ.IsInvariant V)
    (hne : V ≠ ⊥) (hirr : ∀ V' ≤ V, IsClosed (V' : Set L) → ρ.IsInvariant V' → V' = ⊥ ∨ V' = V) :
    ∃ (_ : CompleteSpace (V.comap T.toLinearMap)) (hV : π.IsInvariant (V.comap T.toLinearMap)),
      (π.restrict (V.comap T.toLinearMap) hV).IsIrreducible := by
  have hc : IsClosed ((V.comap T.toLinearMap : Submodule ℂ H) : Set H) :=
    IsClosed.preimage T.continuous hcl
  have hI : π.IsInvariant (V.comap T.toLinearMap) := by
    intro g v hv
    show T (π g v) ∈ V
    rw [hTπ]
    exact hinv g _ hv
  have hcs : CompleteSpace (V.comap T.toLinearMap) := hc.completeSpace_coe
  refine ⟨hcs, hI, ?_, fun U hU hUi => ?_⟩
  · rw [Submodule.nontrivial_iff_ne_bot]
    intro h0
    apply hne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨v, rfl⟩ := hle x hx
    have hv : v ∈ V.comap T.toLinearMap := hx
    rw [h0, Submodule.mem_bot] at hv
    rw [hv, map_zero]
    exact Submodule.zero_mem _
  · let J : (V.comap T.toLinearMap) →ₗᵢ[ℂ] L :=
      { toLinearMap := T.toLinearMap ∘ₗ (V.comap T.toLinearMap).subtype
        norm_map' := fun v => hT v.1 }
    have hinj := Submodule.map_injective_of_injective (f := J.toLinearMap) J.injective
    have htop : (⊤ : Submodule ℂ (V.comap T.toLinearMap)).map J.toLinearMap = V := by
      refine le_antisymm ?_ fun x hx => ?_
      · rintro _ ⟨v, -, rfl⟩
        exact v.2
      · obtain ⟨v, rfl⟩ := hle x hx
        exact ⟨⟨v, hx⟩, trivial, rfl⟩
    have hclU : IsClosed ((U.map J.toLinearMap : Submodule ℂ L) : Set L) :=
      J.isometry.isClosedEmbedding.isClosedMap _ hU
    have hinvU : ρ.IsInvariant (U.map J.toLinearMap) := by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨_, hUi g v hv, hTπ g v.1⟩
    refine (hirr (U.map J.toLinearMap) ((Submodule.map_mono le_top).trans htop.le) hclU hinvU).imp
      (fun h0 => hinj (h0.trans (Submodule.map_bot _).symm)) fun h0 => hinj (h0.trans htop.symm)

theorem UpperTheory.ConvolutionTheory.Dp.sumT :
    UpperTheory.ConvolutionTheory.Dp.SumT := by
  intro K _ _ n μ _ V hV
  exact comap_irreducible (cuspRepT μ) (rightRegularRep (rationalGLOne (K := K) (n := n)) μ) (toLp μ) (norm_toLp μ)
    (toLp_cuspRepT μ) V (fun x hx => ⟨⟨x, hV.le hx⟩, rfl⟩) hV.closed hV.inv hV.ne_bot hV.irred
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.fixedDense :
    UpperTheory.ConvolutionTheory.Dp.FixedDense := by
  intro G H X _ _ _ _ _ _ _ ρ τ J U hU hρ hτ hJ hd v hv
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨x, hx⟩ := hd.exists_dist_lt v hε
  have hfin : ((fun g => τ g x) '' (U : Set G)).Finite := by
    obtain ⟨t, -, ht⟩ := hU.elim_nhds_subcover (fun g => {h | τ h x = τ g x}) fun g _ => by
      have h1 : IsOpen ((fun h => g⁻¹ * h) ⁻¹' {g | τ g x = x}) := (hτ x).preimage (by fun_prop)
      refine Filter.mem_of_superset (h1.mem_nhds (by simp)) fun h hh => ?_
      have h2 : τ (g⁻¹ * h) x = x := hh
      show τ h x = τ g x
      conv_rhs => rw [← h2]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    refine (t.finite_toSet.image fun g => τ g x).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact ⟨i, hi, (h : τ g x = τ i x).symm⟩
  classical
  set S := hfin.toFinset with hS
  have hm : ∀ y, y ∈ S ↔ ∃ g ∈ U, τ g x = y := fun y => by simp [hS]
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨x, (hm x).2 ⟨1, U.one_mem, by simp⟩⟩
  have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  have hc' : (S.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  have hst : ∀ u ∈ U, ∀ y ∈ S, τ u y ∈ S := fun u hu y hy => by
    obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
    exact (hm _).2 ⟨u * g, U.mul_mem hu hg, by rw [map_mul]; rfl⟩
  refine ⟨_, ⟨(S.card : ℂ)⁻¹ • ∑ y ∈ S, y, fun u hu => ?_, rfl⟩, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (τ u) (τ u⁻¹) (hst u hu) (hst _ (U.inv_mem hu)) (fun y _ => ?_) (fun y _ => ?_) fun _ _ => rfl
    · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  · have e : v - J ((S.card : ℂ)⁻¹ • ∑ y ∈ S, y) = (S.card : ℂ)⁻¹ • ∑ y ∈ S, (v - J y) := by

      rw [map_smul, map_sum, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hc', one_smul]
    have h1 : ∀ y ∈ S, ‖v - J y‖ = dist v (J x) := fun y hy => by
      obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
      rw [hJ, dist_eq_norm, ← hρ g (v - J x), map_sub, hv g hg]
    rw [dist_eq_norm, e, norm_smul, norm_inv, Complex.norm_natCast]
    refine lt_of_le_of_lt ?_ hx
    rw [inv_mul_le_iff₀ (by exact_mod_cast hpos)]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
end

section

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.BasicNotions GlobalTheory.CuspRep
open Filter Topology Matrix GroundTheory.Automorphic GroundTheory.Automorphic.RestrictedTensor GroundTheory.Automorphic.AdelicGLn
open scoped RestrictedProduct

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

private theorem toRes_apply (g : GL (Fin n) (Af F)) (v : HeightOneSpectrum (𝓞 F)) :
    toRestricted F n g v = GeneralLinearGroup.map (pLoc F v) g := Units.ext (Matrix.ext fun _ _ => rfl)

private theorem toRes_loc [DecidableEq (HeightOneSpectrum (𝓞 F))] (w : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin n) (w.adicCompletion F)) :
    toRestricted F n (locGL F n w g) = singleHom (fun v => GLnLocal.integralGL (v.adicCompletion F) n) w g := by
  refine RestrictedProduct.ext _ _ fun v => ?_
  rw [toRes_apply]
  by_cases h : v = w
  · subst h; rw [pLoc_locGL, singleHom_apply_self]
  · rw [pLoc_locGL_of_ne h, singleHom_apply_of_ne _ h]

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (Af F)) V}

private theorem coe_equiv (D : TensorDecomposition F n ρ) (g : GL (Fin n) (Af F)) (x : V) :
    (D.equiv.toLinearEquiv (ρ g x)).1 = tensorRep _ D.π (toRestricted F n g) (D.equiv.toLinearEquiv x).1 :=
  congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ D.equiv.toIntertwiningMap g x)

private theorem exists_vec (D : TensorDecomposition F n ρ) : ∃ η : ∀ v, D.W v, IsRestricted D.ξ η ∧ ∀ v, η v ≠ 0 := by
  classical
  choose u hu using fun v => @exists_ne _ (nontrivial_of_isIrreducible (D.isIrreducible v)) 0
  refine ⟨fun v => if D.ξ v = 0 then u v else D.ξ v, D.ne_zero.mono fun v hv => if_neg hv, fun v => ?_⟩
  beta_reduce
  split_ifs with h
  exacts [hu v, h]

private theorem exists_emb (D : TensorDecomposition F n ρ) (w : HeightOneSpectrum (𝓞 F)) :
    ∃ f : D.W w →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (D.π w g x) = ρ (locGL F n w g) (f x) := by
  classical
  obtain ⟨η, hη, h0⟩ := exists_vec D
  let j : D.W w →ₗ[ℂ] restrictedTensor D.ξ :=
    ((PiTensorProduct.tprod ℂ).toLinearMap η w).codRestrict _ fun u => tprod_mem_restrictedTensor (hη.update w u)
  have hj : ∀ u, (j u).1 = PiTensorProduct.tprod ℂ (Function.update η w u) := fun _ => rfl
  refine ⟨D.equiv.toLinearEquiv.symm.toLinearMap ∘ₗ j, fun e => ?_, fun g x => ?_⟩
  · have h1 : D.equiv.toLinearEquiv.symm (j (η w)) = 0 := LinearMap.congr_fun e (η w)
    have h2 := congrArg Subtype.val (D.equiv.toLinearEquiv.symm.map_eq_zero_iff.1 h1)
    rw [hj, Function.update_eq_self] at h2
    exact tprod_ne_zero hη h0 h2
  · refine D.equiv.toLinearEquiv.injective (Subtype.ext ?_)
    rw [coe_equiv, toRes_loc]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hj]
    have h3 := tensorRep_mulSingle_tprod (K := fun v => GLnLocal.integralGL (v.adicCompletion F) n) (π := D.π) w g
      (Function.update η w x)
    rw [Function.update_idem, Function.update_self] at h3
    exact h3.symm

end SlopeTestRemainingChoices

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem dec_tau {K : Type} [Field K] [NumberField K] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {Mx : AdelicGKModule K n V} (D : Mx.Decomposition) (u : D.W₁) (g : AdelicGLn.FiniteAdelicGL K n) (y : D.W₂) :
    Mx.τ g (D.equiv.toLinearEquiv.symm (u ⊗ₜ y)) = D.equiv.toLinearEquiv.symm (u ⊗ₜ D.π₂ g y) := by
  have h2 := Representation.IntertwiningMap.isIntertwining _ _ D.equiv.symm.toIntertwiningMap (1, g) (u ⊗ₜ y)
  rw [RestrictedTensor.outerTensor_tmul] at h2
  simp only [map_one, Module.End.one_apply] at h2
  refine Eq.trans ?_ h2.symm
  show _ = Mx.gk.rep 1 _
  rw [map_one]; rfl

theorem UpperTheory.ConvolutionTheory.Dp.locFlath :
    UpperTheory.ConvolutionTheory.Dp.LocFlath := by
  intro E _ _ _ n π D w σ
  obtain ⟨f, h0, hf⟩ := exists_emb (F := E) D.finite w
  have hnt : Nontrivial (Cm.carrier π) := Submodule.nontrivial_iff_ne_bot.2 fun e =>
    π.ne_bot (by rw [← Cm.map_carrier, e, Submodule.map_bot])
  let e := D.toDecomposition.equiv
  have h1 : Nontrivial D.toDecomposition.W₁ := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact not_subsingleton (Cm.carrier π) e.toLinearEquiv.injective.subsingleton
  obtain ⟨u, hu⟩ := exists_ne (0 : D.toDecomposition.W₁)
  let J : D.finite.W w →ₗ[ℂ] π.V := (Cm.carrierEq π).toLinearMap ∘ₗ e.toLinearEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.mk ℂ _ _ u ∘ₗ f
  have hJ0 : ∀ x, J x = 0 → f x = 0 := fun x hx => by
    have h2 : e.toLinearEquiv.symm (u ⊗ₜ f x) = 0 := (Cm.carrierEq π).map_eq_zero_iff.1 hx
    have h3 := e.toLinearEquiv.symm.map_eq_zero_iff.1 h2
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hu
    simpa [hl] using congrArg (fun z => TensorProduct.lid ℂ _ (LinearMap.rTensor _ l z)) h3
  have hJ : ∀ g x, J (D.finite.π w g x) = π.locRep w g (J x) := fun g x => by
    refine Eq.trans ?_ (Cm.carrierEq_τ π (locGL E n w g) _)
    refine congrArg (Cm.carrierEq π) ?_
    have h2 := dec_tau D.toDecomposition u (locGL E n w g) (f x)
    rw [← hf] at h2
    exact h2.symm
  constructor
  · intro h
    exact GlobalTheory.CuspRep.LocUniq.isLocComp_unique π w σ
      { V := D.finite.W w, ρ := D.finite.π w, smooth := (D.finite.isAdmissible w).1, irred := D.finite.isIrreducible w } h
      ⟨J, fun h2 => h0 (LinearMap.ext fun x => hJ0 x (LinearMap.congr_fun h2 x)), hJ⟩
  · rintro ⟨t⟩
    refine ⟨J ∘ₗ t.toLinearEquiv.toLinearMap, fun h2 => h0 (LinearMap.ext fun x => hJ0 x ?_), fun g x => ?_⟩
    · obtain ⟨y, rfl⟩ := t.toLinearEquiv.surjective x
      exact LinearMap.congr_fun h2 y
    · exact (congrArg J (Representation.IntertwiningMap.isIntertwining _ _ t.toIntertwiningMap g x)).trans (hJ g _)
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.normIff :
    UpperTheory.ConvolutionTheory.Dp.NormIff := by
  intro E _ _ _ n π
  constructor
  · intro h ψ hψ
    refine mem_centralCuspForms.2 fun s x => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact congrArg ψ.1 (Subsingleton.elim _ _)
    · have hc : ((n : ℝ) * Module.finrank ℚ E) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 hn.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
      have hs : (⟨Real.exp (n * Module.finrank ℚ E * (Real.log s.1 / (n * Module.finrank ℚ E))), Real.exp_pos _⟩ :
          {r : ℝ // 0 < r}) = s := Subtype.ext (by
        change Real.exp _ = s.1
        rw [mul_div_cancel₀ _ hc, Real.exp_log s.2])
      have e := UpperTheory.V.KernelIndexFullLattice.splitEq_holds E n (Real.log s.1 / (n * Module.finrank ℚ E))
      rw [hs] at e
      have key := h (Cm.ofCusp E n ψ) hψ (Real.log s.1 / (n * Module.finrank ℚ E)) x
      rw [e] at key
      exact key
  · intro h φ hφ t g
    have hφ' : φ ∈ (Cm.carrier π).map (Cm.ofCusp E n) := by
      rw [Cm.map_carrier]; exact hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ'
    rw [UpperTheory.V.KernelIndexFullLattice.splitEq_holds E n t]
    exact h hψ _ g
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.V
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.Dp

def RhoLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) g v,
    rhoL μ w g v = localRepresentationL2 μ w g v

def TsphVec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K)
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (B : Multiset ℂˣ),
    GlobalTheory.LFun.HasSatGL w (locOn hV w) B ↔ SSat μ V w (B.map fun b : ℂˣ => (b : ℂ))

def SSatUnit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K)
    (V : Submodule ℂ (LL μ)) (B : Multiset ℂ), SSat μ V w B →
    (∃ B' : Multiset ℂˣ, B = B'.map fun b : ℂˣ => (b : ℂ)) ∧ ∀ B₁, SSat μ V w B₁ → B₁ = B

def SSatIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
    (π : CuspSub E n) (V : Submodule ℂ (LL μ)), Carries μ π V → ∀ (w : Pl E) (B : Multiset ℂ),
    SSat μ V w B ↔ ∃ B' : Multiset ℂˣ, B = B'.map (fun b : ℂˣ => (b : ℂ)) ∧ (UpperTheory.CBC.Cusp.cx π).sat w B'

def SSatEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ w : Pl E,
    V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion E) n) ≠ ⊥ → ∃ B, SSat μ V w B

def JGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (τ : E →+* ℂ),
    (∃ j, IsJ (n := n) τ j) ∧ ∀ j, IsJ (n := n) τ j ↔ ∀ a b, j (HarishChandra.e (a, b)) = Cm.genC τ a b

def CapHC : Prop :=
  ∀ (n : ℕ) (u : ℂ), ∃ z : Subalgebra.center ℂ (HarishChandra.U n),
    (z : HarishChandra.U n) = Formalism.REAL.qdet (fun a b => HarishChandra.e (a, b)) (u + ((n : ℂ) - 1) / 2) ∧
      HarishChandra.harishChandraHom z = ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k)

def CapZc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (τ : E →+* ℂ),
    (∀ i : Fin n, zc τ i ∈ Subalgebra.center ℂ (UC E n)) ∧
    ∀ u : ℂ, Cm.capC τ u = u ^ n • (1 : UC E n) + ∑ i : Fin n, u ^ (n - (i + 1)) • zc τ i

def InfZc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (π : CuspSub E n) (τ : E →+* ℂ) (m : Multiset ℂ),
    (UpperTheory.CBC.Cusp.cx π).inf τ m ↔ m.card = n ∧ ∀ (i : Fin n), ∀ φ ∈ π.V, Cm.uC E n (zc τ i) φ = m.esymm (i + 1) • φ

def LactSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (u : UC K n) (β : TI K n), SmoothT β →
    ∃ h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ),
      ∀ g, lact u β g = (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹

def DiracSep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (v : LL μ), (∀ β : TI K n, SmoothT β → Oinf μ ν β v = 0) → v = 0

def SInfIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
    (π : CuspSub E n) (V : Submodule ℂ (LL μ)), Carries μ π V → ∀ (τ : E →+* ℂ) (m : Multiset ℂ),
    SInf μ V τ m ↔ (UpperTheory.CBC.Cusp.cx π).inf τ m

def SInfEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ τ : E →+* ℂ, ∃! m, SInf μ V τ m

def AtInj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
    (V V' : Submodule ℂ (LL μ)), IsSummand μ V → IsSummand μ V' → ∀ (S : Set (Pl E)), S.Finite → ∀ t : Pl E → Multiset ℂ,
    (∀ w ∉ S, SSat μ V w (t w)) → (∀ w ∉ S, SSat μ V' w (t w)) → V = V'

end UpperTheory.ConvolutionTheory.Dp
end
end
