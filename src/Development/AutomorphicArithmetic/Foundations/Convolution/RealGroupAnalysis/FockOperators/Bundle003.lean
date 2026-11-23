module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import GroundTheory.GlobalFields.TateThesis.Bundle001
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.perpCpt :
    ∀ (F : Type) [Field F] [NumberField F] (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)), ∃ K : Set (FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
    ∀ x : A F, (∀ a : A F, a.1 = 0 → a.2 ∈ Λ → ψ (a * x) = 1) → x.2 ∈ K := by
  intro F _ _ Λ
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset (K := F) (W := (Λ : Set (FiniteAdeleRing (𝓞 F) F)))
    (Λ.isOpen.mem_nhds Λ.zero_mem)
  refine ⟨(idealFiniteAdeles (traceDualIdeal F J) : Set (FiniteAdeleRing (𝓞 F) F)),
    isCompact_idealFiniteAdeles _, fun x hx => ?_⟩
  refine (forall_finiteAdelicChar_mul_eq_one_iff J x.2).1 fun y hy => ?_
  have h := hx (finiteAdeleInr y) rfl (hJ hy)
  have e : finiteAdeleInr y * x = finiteAdeleInr (y * x.2) := by
    refine Prod.ext ?_ rfl
    change (0 : _) * x.1 = 0
    exact zero_mul _
  rw [e] at h
  rw [finiteAdelicChar_apply]
  exact Circle.ext h
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem wW_val : (wW F).1 = !![0, 1; -1, 0] := rfl

private theorem wInv_val : ((wW F)⁻¹).1 = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, _root_.wW_val]
  simp

private theorem orth_w : InfOrth (wW F) := by
  intro i j
  rw [_root_.wW_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem orth_wInv : InfOrth (wW F)⁻¹ := by
  intro i j
  rw [wInv_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem orth_unitary (h : G1 F) (ho : InfOrth h) :
    (GeneralLinearGroup.map (TR.pInf F) (gl h)).val ∈ Matrix.unitaryGroup (Fin 2) (TR.Rinf F) := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext1 i j
  have e : TR.pInf F ((h.1 * h.1ᵀ) i j) = TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) :=
    congrArg (TR.infEq F).symm (ho i j)
  have e1 : ((GeneralLinearGroup.map (TR.pInf F) (gl h)).val * star (GeneralLinearGroup.map (TR.pInf F) (gl h)).val) i j =
      TR.pInf F ((h.1 * h.1ᵀ) i j) := by

    simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial,
    Matrix.transpose_apply]
    rfl
  have e2 : TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [e1, e, e2]

private theorem rt_split (g : GL (Fin 2) (A F)) :
    TR.rt F 2 g = TR.rt F 2 (TR.infGL F 2 (GeneralLinearGroup.map (TR.pInf F) g)) *
      TR.rt F 2 (finGL F 2 (GeneralLinearGroup.map (pFin F) g)) := by
  rw [← map_mul, TR.infGL_mul_finGL]

private theorem stable_of_orth (π : TR.CuspSub F 2) {h : G1 F} (ho : InfOrth h) {f : TR.Sm F 2} (hf : f ∈ π.V) :
    TR.rt F 2 (gl h) f ∈ π.V := by
  rw [rt_split, Module.End.mul_apply]
  have h1 := π.stable (.fin (GeneralLinearGroup.map (pFin F) (gl h))) f hf
  have h2 := π.stable (.cpt ⟨_, orth_unitary h ho⟩) _ h1
  have e : Unitary.toUnits (⟨_, orth_unitary h ho⟩ : TR.Kinf F 2) = GeneralLinearGroup.map (TR.pInf F) (gl h) :=
    Units.ext rfl
  change TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits (⟨_, orth_unitary h ho⟩ : TR.Kinf F 2)))
    (TR.rt F 2 (finGL F 2 (GeneralLinearGroup.map (pFin F) (gl h))) f) ∈ π.V at h2
  rwa [e] at h2

private theorem ad_eop (v : InfinitePlace F) :
    TR.rt F 2 (gl (wW F)) * TR.Eop v 0 1 = -(TR.Eop v 1 0 * TR.rt F 2 (gl (wW F))) := by
  have hy : (GeneralLinearGroup.map (TR.pInf F) (gl (wW F))).val = !![0, 1; -1, 0] := by
    ext1 i j
    fin_cases i <;> fin_cases j <;> simp [_root_.wW_val]
  have hyi : ((GeneralLinearGroup.map (TR.pInf F) (gl (wW F)))⁻¹).val = !![0, -1; 1, 0] := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  have hfin : ∀ k : GL (Fin 2) (Af F), TR.rt F 2 (finGL F 2 k) * TR.Eop v 0 1 = TR.Eop v 0 1 * TR.rt F 2 (finGL F 2 k) :=
    fun k => (TR.lie_rt_fin _ k).symm
  rw [rt_split (gl (wW F)), mul_assoc, hfin, ← mul_assoc, TR.Cen.rt_Eop, hy, hyi]
  simp [Fin.sum_univ_two, mul_assoc]

end

theorem UpperTheory.ConvolutionTheory.R2.Fo.adW :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∀ π : TR.CuspSub F 2, ∀ f ∈ π.V, TR.rt F 2 (gl (wW F)) f ∈ π.V ∧ TR.rt F 2 (gl (wW F)⁻¹) f ∈ π.V) ∧
    (∀ v, TR.rt F 2 (gl (wW F)) * TR.Eop v 0 1 = -(TR.Eop v 1 0 * TR.rt F 2 (gl (wW F)))) ∧ InfOrth (wW F)⁻¹ := by
  intro F _ _ _
  exact ⟨fun π f hf => ⟨stable_of_orth π orth_w hf, stable_of_orth π orth_wInv hf⟩, ad_eop, orth_wInv⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private lemma countable_gam (K : Type) [Field K] [NumberField K] : Countable (Gam K) := by
  haveI : Countable K := by
    have : Module.Finite ℚ K := inferInstance
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℚ K
    exact hf.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Function.Injective.countable (f := fun g => (g.1 : Matrix (Fin 2) (Fin 2) K)) Subtype.val_injective
  unfold Gam
  exact (Set.countable_range (ratS K)).to_subtype

private lemma setIntegral_mul_right (K : Type) [Field K] [NumberField K] (M : Meas K) (u : G1 K → ℂ)
    (hu : ∀ γ g, u (ratS K γ * g) = u g) (k : G1 K) :
    ∫ g in M.D, u (g * k) ∂M.μ = ∫ g in M.D, u g ∂M.μ := by
  haveI := M.haar
  haveI := M.right
  haveI := countable_gam K
  have hmp : MeasurePreserving (· * k) M.μ M.μ := measurePreserving_mul_right M.μ k
  have hemb : MeasurableEmbedding (· * k : G1 K → G1 K) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd : IsFundamentalDomain (Gam K) ((Equiv.mulRight k) '' M.D) M.μ := by
    refine M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_
    · exact (measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving
    · intro g x
      simp [Subgroup.smul_def, mul_assoc]
  have hinv : ∀ (g : Gam K) x, u (g • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    simpa [Subgroup.smul_def] using hu γ x
  have hpre : (· * k : G1 K → G1 K) ⁻¹' ((Equiv.mulRight k) '' M.D) = M.D := by
    ext x; simp
  have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)
  rw [hpre] at h3
  rw [h3]
  exact hfd.setIntegral_eq M.fund hinv

theorem UpperTheory.ConvolutionTheory.R2.Fo.moveG :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ), (∀ γ g, f (ratGL F 2 γ * g) = f g) → ∀ (φ : S4 F) (g₀ : G1 F),
    lift W M f (W.Om g₀ φ) = lift W M (fun x => f (x * gl g₀⁻¹)) φ := by
  intro F E _ _ _ _ _ _ _ D W M f hf φ g₀
  funext h
  have hu : ∀ γ g, (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) (ratS F γ * g) =
      (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) g := by
    intro γ g
    have h1 : gl (ratS F γ * g) * dM (nu F h) * gl g₀⁻¹ =
        ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) * (gl g * dM (nu F h) * gl g₀⁻¹) := by
      rw [gl_mul, gl_ratS]; group
    have h2 : W.Om (ratS F γ * g) (W.L h φ) = W.Om (ratS F γ) (W.Om g (W.L h φ)) := by
      rw [map_mul, Module.End.mul_apply]
    show f (gl (ratS F γ * g) * dM (nu F h) * gl g₀⁻¹) * Th (W.Om (ratS F γ * g) (W.L h φ)).1 = _
    rw [h1, hf, h2, W.th_Om]
  have key := setIntegral_mul_right F M (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) hu (cD (nu F h) g₀)
  refine Eq.trans (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)) key
  have h1 : gl (g * cD (nu F h) g₀) * dM (nu F h) * gl g₀⁻¹ = gl g * dM (nu F h) := by
    have hi : gl g₀⁻¹ = (gl g₀)⁻¹ := map_inv Matrix.SpecialLinearGroup.toGL g₀
    rw [gl_mul, gl_cD, hi]; group
  have h2 : W.L h (W.Om g₀ φ) = W.Om (cD (nu F h) g₀) (W.L h φ) := by
    have := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (W.comm h g₀)
    simpa only [Module.End.mul_apply] using this
  have h3 : W.Om (g * cD (nu F h) g₀) (W.L h φ) = W.Om g (W.L h (W.Om g₀ φ)) := by
    rw [h2, map_mul, Module.End.mul_apply]
  show f (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om g₀ φ))).1 =
    f (gl (g * cD (nu F h) g₀) * dM (nu F h) * gl g₀⁻¹) * Th (W.Om (g * cD (nu F h) g₀) (W.L h φ)).1
  rw [h1, h3]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)

private noncomputable def st (X : Matrix (Fin 2) (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E) := (X.map D.bar)ᵀ

private theorem st_mul (X Y : Matrix (Fin 2) (Fin 2) (A E)) : st D (X * Y) = st D Y * st D X := by
  simp only [st, Matrix.map_mul, Matrix.transpose_mul]

private theorem st_st (X : Matrix (Fin 2) (Fin 2) (A E)) : st D (st D X) = X := by
  ext i j
  simp [st]

private theorem st_herm (v : V4 F) : st D (D.herm v) = D.herm v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [st, Dat.herm, Dat.bar_mkE]

private theorem mkE_of_fixed {z : A E} (h : D.bar z = z) : D.mkE (D.co z 0) 0 = z := by
  rw [D.mkE_base]
  exact (D.eq_am_of_bar_eq h).symm

private theorem herm_unherm {X : Matrix (Fin 2) (Fin 2) (A E)} (h : st D X = X) :
    D.herm (D.unherm X) = X := by
  have e : ∀ i j, D.bar (X j i) = X i j := fun i j => congrFun (congrFun h i) j
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Dat.herm, Dat.unherm] using mkE_of_fixed D (e 0 0)
  · simpa [Dat.herm, Dat.unherm] using D.mkE_co (X 0 1)
  · have := D.bar_mkE (D.co (X 0 1) 0) (D.co (X 0 1) 1)
    rw [D.mkE_co, e] at this
    simpa [Dat.herm, Dat.unherm] using this.symm
  · simpa [Dat.herm, Dat.unherm] using mkE_of_fixed D (e 1 1)

private noncomputable def eps (K : Type) [Field K] [NumberField K] : A K := (0, 1)

private theorem eps_mul_snd (a : A F) : (eps F * a).2 = a.2 := one_mul _

private theorem am_eps : am E (eps F) = eps E := by
  refine Prod.ext ?_ ?_
  · exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))
  · exact map_one (AdeleBaseChange.finiteAdeleMap F E)

end UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed

open UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed in
theorem UpperTheory.ConvolutionTheory.R2.Fo.hermAct :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E), (∀ h v, D.herm (D.act h v) = h.val * D.herm v * (h.val.map D.bar)ᵀ) ∧ (∀ u t, D.bar (D.mkE u t) = D.mkE u (-t)) ∧
    (∀ z, D.mkE (D.co z 0) (D.co z 1) = z) ∧ ∀ u t : A F, (D.mkE u t).2 = 0 → u.2 = 0 ∧ t.2 = 0 := by
  intro F E _ _ _ _ _ _ _ D
  refine ⟨fun h v => ?_, D.bar_mkE, D.mkE_co, fun u t h0 => ?_⟩
  · change D.herm (D.unherm (h.val * D.herm v * st D h.val)) = h.val * D.herm v * st D h.val
    apply herm_unherm
    rw [st_mul, st_mul, st_st, st_herm, mul_assoc]
  · have h1 : D.mkE (eps F * u) (eps F * t) = D.mkE 0 0 := by
      rw [← D.am_mul_mkE, am_eps, D.mkE_zero]
      refine Prod.ext (zero_mul _) ?_
      rw [eps_mul_snd, h0]
      rfl
    obtain ⟨hu, ht⟩ := D.mkE_inj h1
    exact ⟨(eps_mul_snd u).symm.trans (congrArg Prod.snd hu), (eps_mul_snd t).symm.trans (congrArg Prod.snd ht)⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical SchwartzMap

private theorem mixed_coord {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : V4 F) (i : Fin 4)
    (w : InfinitePlace F) :
    (infPartPi v i).1 ⟨w, IsTotallyReal.isReal w⟩ = TR.pInf F (v i) w := by
  rfl

private theorem pInf_rt_neg {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ φ : F →+* ℝ, φ δ < 0) (w : InfinitePlace F) : TR.pInf F (rt δ) w < 0 := by
  have h : TR.pInf F (rt δ) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ :=
    by
      change InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (algebraMap F w.Completion δ) = _
      rw [AbsoluteValue.Completion.algebraMap_def]
      exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal w) (WithAbs.toAbs _ δ)
  rw [h]
  exact hδ _

private noncomputable def coordLin {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (c : Fin 4 × InfinitePlace F → ℝ) :
    (Fin 4 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4 × InfinitePlace F) where
  toFun u := WithLp.toLp 2 fun p => c p * (u p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩
  map_add' u u' := by
    ext p
    simp [mul_add]
  map_smul' a u := by
    ext p
    simp [mul_left_comm]

private theorem coordLin_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (c : Fin 4 × InfinitePlace F → ℝ) (u : Fin 4 → mixedEmbedding.mixedSpace F) (p : Fin 4 × InfinitePlace F) :
    coordLin c u p = c p * (u p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩ := by
  rfl

private theorem coordLin_inj {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (c : Fin 4 × InfinitePlace F → ℝ) (hc : ∀ p, c p ≠ 0) : LinearMap.ker (coordLin c) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro u hu
  funext i
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have h := congrArg (fun y : EuclideanSpace ℝ (Fin 4 × InfinitePlace F) => y (i, w.1)) hu
    simp only [coordLin_apply] at h
    exact (mul_eq_zero.1 h).resolve_left (hc _)
  · exact (InfinitePlace.not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1) w.2).elim

private theorem exists_sch {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ φ : F →+* ℝ, φ δ < 0) :
    ∃ f : 𝓢(Fin 4 → mixedEmbedding.mixedSpace F, ℂ), ∀ v : V4 F, f (infPartPi v) = gauss δ v := by
  let k : Fin 4 × InfinitePlace F → ℝ := fun p => ![1, 1, 2, -2 * TR.pInf F (rt δ) p.2] p.1
  have hk : ∀ p, 0 < k p := by
    rintro ⟨i, w⟩
    have hd := pInf_rt_neg δ hδ w
    fin_cases i <;> simp [k] <;> linarith
  let c : Fin 4 × InfinitePlace F → ℝ := fun p => Real.sqrt (k p)
  have hc : ∀ p, c p ≠ 0 := fun p => (Real.sqrt_pos.2 (hk p)).ne'
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith (coordLin c) (coordLin_inj c hc)
  let T := LinearMap.toContinuousLinearMap (coordLin c)
  have hT : ∀ u, T u = coordLin c u := fun _ => rfl
  have hg : Function.HasTemperateGrowth T := T.hasTemperateGrowth
  have hK' : AntilipschitzWith K T := hK
  refine ⟨SchwartzMap.compCLMOfAntilipschitz ℂ hg hK' (gaussianSchwartz _), fun v => ?_⟩
  have hn : ‖T (infPartPi v)‖ ^ 2 = ∑ w, TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hs : ∀ i, (T (infPartPi v) (i, w)) ^ 2 = k (i, w) * TR.pInf F (v i) w ^ 2 := fun i => by
      rw [hT, coordLin_apply, mixed_coord, mul_pow, Real.sq_sqrt (hk _).le]
    simp only [hs, Fin.sum_univ_four, k, map_add (f := _), map_mul, map_sub, map_pow, map_ofNat, Pi.add_apply,
      Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.ofNat_apply]
    simp
    ring
  rw [SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply, gaussianSchwartz_apply, hn, gauss]
  push_cast
  rfl

theorem UpperTheory.ConvolutionTheory.R2.Fo.gaussMem :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), (fun v => gauss D.δ v * g (finPartPi v)) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  intro F E _ _ _ _ _ _ _ D g hg
  obtain ⟨f, hf⟩ := exists_sch D.δ D.neg
  have h : (fun v => gauss D.δ v * g (finPartPi v)) = schwartzBruhatTensorPi f g := by
    funext v
    simp only [schwartzBruhatTensorPi, hf]
  rw [h]
  exact schwartzBruhatTensorPi_mem f hg
end
