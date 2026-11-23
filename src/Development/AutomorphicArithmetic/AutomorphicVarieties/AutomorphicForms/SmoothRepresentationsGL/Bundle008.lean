module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
public import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle001
public import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance
public import GroundTheory.AutomorphicForms.SatakeNormalized
public import GroundTheory.AutomorphicForms.WhittakerGroups
public import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsIsOpenForallCuspRepTFinOneEq
public import GroundTheory.AutomorphicForms.L2LocalComponents.CuspSmooth
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.levelS :
    UpperTheory.V.Af.Smo.LevelS := by
  intro E _ _ n V
  let e := AdelicGLn.finiteRestrictedEquiv E n
  let f : (∀ v : HeightOneSpectrum (𝓞 E), (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E)))) →
      GL (Fin n) (Af E) := fun x => e.symm (RestrictedProduct.structureMap _ _ Filter.cofinite x)
  have hf : Continuous f := e.symm.continuous.comp RestrictedProduct.isEmbedding_structureMap.continuous
  let o : ∀ v : HeightOneSpectrum (𝓞 E), (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E))) :=
    fun v => ⟨1, one_mem _⟩
  have ho : f o = 1 := by
    refine e.symm_apply_eq.2 ?_
    rw [map_one]
    rfl
  have hV : f ⁻¹' (V : Set (GL (Fin n) (Af E))) ∈ 𝓝 o := hf.continuousAt.preimage_mem_nhds (ho ▸ V.mem_nhds_one)
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨S, t, ht, hS⟩ := hV
  refine ⟨S, fun k hk => ?_⟩
  have hek : ∀ v, e k v = cmp v k := fun v => Units.ext (Matrix.ext fun _ _ => rfl)
  have hi : ∀ v : HeightOneSpectrum (𝓞 E), cmp v k ∈ GLnLocal.integralGL (v.adicCompletion E) n := fun v => by
    have h := GlobalTheory.AdelicU.mem_GLint_iff.1 (hk.2 v)
    rw [GLnLocal.mem_integralGL_iff]
    simp only [GroundTheory.Global.mem_valuationInteger_iff]
    exact h
  have hx : f (fun v => ⟨cmp v k, hi v⟩) = k := by
    refine e.symm_apply_eq.2 (DFunLike.ext _ _ fun v => ?_)
    exact (hek v).symm
  rw [← hx]
  refine hS fun v hv => ?_
  have : (⟨cmp v k, hi v⟩ : (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E)))) = o v :=
    Subtype.ext (hk.1 v hv)
  exact this ▸ mem_of_mem_nhds (ht v)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_equiv_mod {M : Type} [AddCommGroup M] [Module ℂ M] (U U' D : Submodule ℂ M)
    (h : U ⊓ D = ⊥) (h' : U' ⊓ D = ⊥) (e : U ⊔ D = U' ⊔ D) :
    ∃ T : U ≃ₗ[ℂ] U', ∀ u, (T u).1 - u.1 ∈ D := by
  have inj : ∀ W : Submodule ℂ M, W ⊓ D = ⊥ → Function.Injective (D.mkQ ∘ₗ W.subtype) := fun W hW => by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have hx' : x.1 ∈ W ⊓ D := ⟨x.2, (Submodule.Quotient.mk_eq_zero D).1 hx⟩
    rw [hW] at hx'
    exact Subtype.ext hx'
  have rg : ∀ W : Submodule ℂ M, LinearMap.range (D.mkQ ∘ₗ W.subtype) = (W ⊔ D).map D.mkQ := fun W => by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  have er : LinearMap.range (D.mkQ ∘ₗ U.subtype) = LinearMap.range (D.mkQ ∘ₗ U'.subtype) := by
    rw [rg, rg, e]
  refine ⟨(LinearEquiv.ofInjective _ (inj U h)).trans
    ((LinearEquiv.ofEq _ _ er).trans (LinearEquiv.ofInjective _ (inj U' h')).symm), fun u => ?_⟩
  refine (Submodule.Quotient.eq D).1 ?_
  exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (inj U' h')).apply_symm_apply
    (LinearEquiv.ofEq _ _ er (LinearEquiv.ofInjective _ (inj U h) u)))

private theorem iso_of_compl {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (π π' : CuspSub E n)
    (D : Submodule ℂ (TR.Sm E n)) (hD : TR.IsStable D) (h : π.V ⊓ D = ⊥) (h' : π'.V ⊓ D = ⊥)
    (hle : π'.V ≤ π.V ⊔ D) : π.Iso π' := by
  have hst : TR.IsStable (π.V ⊓ (π'.V ⊔ D)) := by
    rintro o φ ⟨h1, h2⟩
    refine ⟨π.stable o φ h1, ?_⟩
    obtain ⟨x, hx, d, hd, rfl⟩ := Submodule.mem_sup.1 h2
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (π'.stable o x hx) (hD o d hd)
  have hge : π.V ≤ π'.V ⊔ D := by
    rcases π.irred _ inf_le_left hst with h0 | h0
    · refine absurd (eq_bot_iff.2 fun x hx => ?_) π'.ne_bot
      obtain ⟨u, hu, d, hd, rfl⟩ := Submodule.mem_sup.1 (hle hx)
      have hu' : u ∈ π.V ⊓ (π'.V ⊔ D) := ⟨hu, by
        have := Submodule.add_mem_sup hx (D.neg_mem hd)
        rwa [add_neg_cancel_right] at this⟩
      rw [h0, Submodule.mem_bot] at hu'
      rw [← h']
      refine ⟨hx, ?_⟩
      rw [hu', zero_add]
      exact hd
    · exact inf_eq_left.1 h0
  obtain ⟨T, hT⟩ := exists_equiv_mod π.V π'.V D h h'
    (le_antisymm (sup_le hge le_sup_right) (sup_le hle le_sup_right))
  refine ⟨T, fun o φ => Subtype.ext (sub_eq_zero.1 ?_)⟩
  rw [← Submodule.mem_bot ℂ, ← h']
  refine ⟨π'.V.sub_mem (T _).2 (π'.op o _).2, ?_⟩
  have h1 := D.sub_mem (hT (π.op o φ)) (hD o _ (hT φ))
  rw [map_sub, TR.CuspSub.op_val, sub_sub_sub_cancel_right] at h1
  exact h1

private theorem stab_orthRel {E : Type} [Field E] [NumberField E] {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : cuspForms E n →ₗ[ℂ] H)
    (hρ : ∀ X, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι ((gkModuleCusp E n).ρ X a)) (ι c) + inner ℂ (ι a) (ι ((gkModuleCusp E n).ρ X c)) = 0)
    (hσ : ∀ k, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι ((gkModuleCusp E n).σ k a)) (ι ((gkModuleCusp E n).σ k c)) = inner ℂ (ι a) (ι c))
    (hτ : ∀ g, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι (finRepCusp E n g a)) (ι (finRepCusp E n g c)) = inner ℂ (ι a) (ι c))
    {U : Submodule ℂ (cuspForms E n)} (hU : U ≤ centralCuspForms E n) (hs : Fb.Stab U) :
    Fb.Stab (orthRel ι (centralCuspForms E n) U) := by
  refine ⟨fun X φ hφ => ?_, fun k φ hφ => ?_, fun g φ hφ => ?_⟩
  · refine map_mem_orthRel (A' := fun y => -(gkModuleCusp E n).ρ X y) (Fb.stab_central.ρ X)
      (fun x hx y hy => ?_) (fun u hu => U.neg_mem (hs.ρ X u hu)) hφ
    rw [map_neg, inner_neg_left, neg_eq_iff_add_eq_zero]
    exact hρ X x (hU hx) y hy
  · refine map_mem_orthRel (A' := (gkModuleCusp E n).σ k⁻¹) (Fb.stab_central.σ k)
      (fun x hx y hy => ?_) (hs.σ k⁻¹) hφ
    rw [← hσ k _ (hU (hs.σ k⁻¹ x hx)) y hy, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  · refine map_mem_orthRel (A' := finRepCusp E n g⁻¹) (Fb.stab_central.τ g)
      (fun x hx y hy => ?_) (hs.τ g⁻¹) hφ
    rw [← hτ g _ (hU (hs.τ g⁻¹ x hx)) y hy, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]

private theorem carrier_le_of_not_iso {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ}
    (π π' : CuspSub E n) (hi : ¬ π.Iso π') (C : Submodule ℂ (cuspForms E n)) (hC : Fb.Stab C)
    (hinf : Fb.carrier π ⊓ C = ⊥) (hle : Fb.carrier π' ≤ Fb.carrier π ⊔ C) : Fb.carrier π' ≤ C := by
  have hst : TR.IsStable (π'.V ⊓ C.map (Fb.ofCusp E n)) := fun o x hx =>
    ⟨π'.stable o x hx.1, hC.map o x hx.2⟩
  rcases π'.irred _ inf_le_left hst with h0 | h0
  · refine absurd (iso_of_compl π π' _ hC.map ?_ h0 ?_) hi
    · rw [← Fb.map_carrier, ← Submodule.map_inf _ Fb.ofCusp_injective, hinf, Submodule.map_bot]
    · rw [← Fb.map_carrier, ← Fb.map_carrier, ← Submodule.map_sup]
      exact Submodule.map_mono hle
  · intro φ' hφ'
    obtain ⟨ψ, hψ, e⟩ := inf_eq_left.1 h0 (Fb.mem_carrier.1 hφ')
    obtain rfl := Fb.ofCusp_injective e
    exact hψ

theorem UpperTheory.V.Af.Smo.innerZero :
    UpperTheory.V.Af.Smo.InnerZero := by
  intro E _ _ _ n μ _ π π' hc hc' hi φ hφ φ' hφ'
  have l := Fb.carrier_le_central π hc
  have l' := Fb.carrier_le_central π' hc'
  have hs := Fb.stab_carrier π
  have hC := stab_orthRel (CuspidalSpectrum.cuspToL2 μ) (fun X a ha c hc => petersson_inner_lieAlgebra_skewAdjoint μ X ha hc)
    (fun k a ha c hc => petersson_inner_maximalCompact_invariant μ k ha hc) (fun g a ha c hc => petersson_inner_finiteAdelic_invariant μ g ha hc) l hs
  have hsup := CuspidalSpectrum.sup_orthRel_centralCuspForms μ _ l hs.ρ hs.τ
  have hinf := inf_orthRel_eq_bot (ι := CuspidalSpectrum.cuspToL2 μ) l fun a ha h0 =>
    CuspidalSpectrum.eq_zero_of_cuspVecL_eq_zero (μ := μ) ha h0
  exact (carrier_le_of_not_iso π π' hi _ hC hinf (l'.trans hsup.ge) hφ').2 φ hφ
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

open CuspidalSpectrum RightCosetSpace in
private theorem UpperTheory.V.Af.Smo.coeFn_tr {E : Type} [Field E] [NumberField E] {n : ℕ}
    (μ : Measure (Reduction.normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] {φ : cuspForms E n} (hφ : φ ∈ centralCuspForms E n)
    (g : AdelicGLn.AdelicGL E n) :
    (toLp μ (cuspRepT μ (toOne g) (cuspVecL μ φ)) : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) → ℂ)
      =ᵐ[quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ] quotTr φ g := by
  rw [toLp_cuspRepT, rightRegularRep_apply, toLp_cuspVecL, quotTr_eq_comp hφ, quotTr_one]
  refine (coeFn_rightTranslate _ μ _ _).trans ?_
  exact (measurePreserving_rightMul μ (toOne g)).quasiMeasurePreserving.ae_eq (coeFn_cuspToL2 μ φ)

private theorem UpperTheory.V.Af.Smo.inner_closure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {S T : Submodule ℂ H} (h : ∀ x ∈ S, ∀ y ∈ T, inner ℂ x y = 0) {x y : H}
    (hx : x ∈ S.topologicalClosure) (hy : y ∈ T.topologicalClosure) : inner ℂ x y = 0 := by
  have h1 : T ≤ S.topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure]
    exact fun b hb => (Submodule.mem_orthogonal _ _).2 fun a ha => h a ha b hb
  exact (Submodule.mem_orthogonal _ _).1
    (Submodule.topologicalClosure_minimal T h1 (Submodule.isClosed_orthogonal _) hy) x hx

open CuspidalSpectrum RightCosetSpace in
theorem UpperTheory.V.Af.Smo.orthTr :
    UpperTheory.V.Af.Smo.OrthTr := by
  intro E _ _ n μ _ U U' hU hU' sU sU' h φ hφ φ' hφ' g g'
  have i1 := isInvariant_topologicalClosure_map μ hU sU.ρ sU.σ sU.τ
  have i2 := isInvariant_topologicalClosure_map μ hU' sU'.ρ sU'.σ sU'.τ
  have m1 := i1 (toOne g) _ (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (f := cuspVecL μ) hφ))
  have m2 := i2 (toOne g') _ (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (f := cuspVecL μ) hφ'))
  have h0 := UpperTheory.V.Af.Smo.inner_closure (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact h a ha b hb) m1 m2
  have h1 : inner ℂ (toLp μ (cuspRepT μ (toOne g) (cuspVecL μ φ)))
      (toLp μ (cuspRepT μ (toOne g') (cuspVecL μ φ'))) = 0 := h0
  rw [MeasureTheory.L2.inner_def] at h1
  rw [← h1]
  refine integral_congr_ae ?_
  filter_upwards [UpperTheory.V.Af.Smo.coeFn_tr μ (hU hφ) g, UpperTheory.V.Af.Smo.coeFn_tr μ (hU' hφ') g'] with q e1 e2
  rw [e1, e2, RCLike.inner_apply']
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.seed :
    UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.SeedConv → UpperTheory.V.Af.Smo.Seed := by
  intro hW hS E _ _ _ n π hc
  have nice : ∀ φ ∈ π.V, Nice φ.1 := by
    intro φ hφ
    have hl := (π.cusp φ hφ).1.level
    rw [← Fb.map_carrier] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    refine ⟨ψ.2.1.continuous, exists_norm_le_of_mem_centralCuspForms (Fb.carrier_le_central π hc hψ),
      ψ.2.1.isLeftInvariant, ψ.2.2, ?_⟩
    let V : Subgroup (GL (Fin n) (Af E)) :=
      { carrier := {k | TR.finRep E n k (Fb.ofCusp E n ψ) = Fb.ofCusp E n ψ}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    exact ⟨⟨V, hl⟩, fun g v hv => congrFun (congrArg Subtype.val hv) g⟩
  refine ⟨nice, ?_⟩
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have N := nice φ hφ
  have hg : ∃ g, whittaker φ.1 g ≠ 0 := by
    by_contra h
    refine h0 (Subtype.ext (MultiplicityOne.eq_zero_of_whittaker_eq_zero N.cont N.left N.cusp ?_
      fun g => not_not.1 fun h' => h ⟨g, h'⟩))
    rw [Fb.finEmb_eq]
    exact N.level
  obtain ⟨g, hg⟩ := hg
  rw [← TR.infGL_mul_finGL g] at hg
  generalize GeneralLinearGroup.map (pInf E) g = y at hg
  generalize GeneralLinearGroup.map (pFin E) g = k at hg
  have hφ' := π.stable (.fin k) φ hφ
  refine ⟨_, hφ', hS E n _ (hW E n _ (nice _ hφ')).1 y ?_⟩
  have e : (TR.act (.fin k) φ).1 = fun x => φ.1 (x * finGL E n k) := rfl
  rw [e]
  simpa only [whittaker, mul_assoc] using hg
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

open GroundTheory.Automorphic.FourierWhittaker in
private theorem exists_uGL {E : Type} [Field E] [NumberField E] {n : ℕ} (ν : GA E n) (hν : IsY 0 ν.val) :
    ∃ X : Pos n → Ad E, ν = uGL X ∧ supN ν.val = supSum 0 X := by
  classical
  refine ⟨fun p => ν.val p.1.1 p.1.2, Units.ext (Matrix.ext fun a b => ?_), ?_⟩
  · rw [coe_uGL, uMat_apply]
    split_ifs with h1 h2
    · subst h1; exact (hν a (Nat.zero_le _)).1
    · rfl
    · exact (hν a (Nat.zero_le _)).2 b (lt_of_le_of_ne (not_lt.1 h2) (Ne.symm h1))
  · unfold supN supSum
    rw [← Finset.sum_product', ← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢
      omega
    · intro p _ q _ h
      exact Subtype.ext h
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hq
      refine ⟨⟨q, by rw [Fin.lt_def]; omega⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro p _
      rfl

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.Smo.whBasic :
    UpperTheory.V.Af.Smo.WhBasic := by
  intro E _ _ n f hf
  refine ⟨?_, ?_, ?_⟩
  · have : whittaker f = partialCoeff f 0 := funext fun g => whittaker_eq_partialCoeff_zero hf.cont g
    rw [this]
    exact continuous_partialCoeff hf.cont 0
  · obtain ⟨C, hC⟩ := hf.bdd
    refine ⟨C, fun g => ?_⟩
    have h := norm_setIntegral_le_of_norm_le_const (μ := vecMeasure E (Pos n)) (s := vecDomain E (Pos n))
      (f := fun X => f (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) (C := C)
      (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top) fun X _ => by
        rw [norm_mul, Circle.norm_coe, mul_one]
        exact hC _
    rwa [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one] at h
  · intro ν hν g
    obtain ⟨X, h1, h2⟩ := exists_uGL ν hν
    rw [h2, h1]
    exact GroundTheory.Automorphic.MultiplicityOne.whittaker_uGL_mul hf.cont hf.left X g
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic
open scoped ValuativeRel

namespace UpperTheory.V.Af.Smo

def SphDict : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)),
    GLnLocal.integralGL (w.adicCompletion E) n = GlobalTheory.LFun.KGL w (n := n) ∧
    Formalism.UG.IsUnifV E w (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ∧
    (∀ r ≤ n, Spherical.sqrtQ (w.adicCompletion E) ^ (r * (n - r)) =
      (Formalism.UG.qV E w : ℂ) ^ (((r : ℂ) * ((n : ℂ) - r)) / 2)) ∧
    ∀ u ∈ Iwasawa.unipotent (w.adicCompletion E) n, IsY 0 u.val ∧
      ∀ ψ : AddChar (w.adicCompletion E) ℂ, Whittaker.psiN ψ u = ψ (supN u.val)

def TjSet : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)), ∀ r ≤ n,
    Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) r =
      (Spherical.minusculeSet (w.adicCompletion E) n r).indicator fun _ => (1 : ℂ)

end UpperTheory.V.Af.Smo
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem psiL_eq_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) : psiL w x = 1 ↔ GroundTheory.Global.localAdelicChar E w x = 1 := by
  have h : psiL w x = (GroundTheory.Global.localAdelicChar E w x : ℂ) := rfl
  rw [h]
  exact Circle.coe_eq_one

private theorem exists_psiL_ne_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (z : w.adicCompletion E) (hz : z ∉ GroundTheory.Global.localInvDifferent w) :
    ∃ a ∈ w.adicCompletionIntegers E, psiL w (a * z) ≠ 1 := by
  by_contra hc
  refine hz ((GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff w z).1 fun a ha => ?_)
  rw [← psiL_eq_one_iff]
  by_contra h
  exact hc ⟨a, ha, h⟩

theorem UpperTheory.V.Af.Smo.psiLoc :
    UpperTheory.V.Af.Smo.PsiLoc := by
  intro E _ _
  refine ⟨fun w => ⟨?_, fun h => ?_⟩, ?_⟩
  · filter_upwards [(GroundTheory.Global.isOpen_localInvDifferent w).mem_nhds (zero_mem _)] with x hx
    exact (psiL_eq_one_iff w x).2 (GroundTheory.Global.localAdelicChar_eq_one_of_mem hx)
  · obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w
      (WithZero.exp (FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E) + 1))
    obtain ⟨a, -, ha⟩ := exists_psiL_ne_one w z (by
      rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, hz, WithZero.exp_le_exp]
      omega)
    exact ha (by rw [h]; rfl)
  · filter_upwards [FractionalIdeal.finite_factors (K := E) ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E)] with w hw
    refine ⟨fun x hx => (psiL_eq_one_iff w x).2 (GroundTheory.Global.localAdelicChar_eq_one_of_mem
      (GroundTheory.Global.mem_localInvDifferent_of_mem hx)), fun ϖ hϖ => ?_⟩
    have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h0 : ϖ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    obtain ⟨a, haO, ha⟩ := exists_psiL_ne_one w ϖ⁻¹ (by
      rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, hw, map_inv₀, hv, ← WithZero.exp_neg,
        WithZero.exp_le_exp]
      omega)
    refine ⟨a * ϖ⁻¹, ?_, ha⟩
    rw [mul_left_comm, mul_inv_cancel₀ h0, mul_one]
    exact haO
end
