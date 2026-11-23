module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle539
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle004
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle036
import GroundTheory.AutomorphicForms.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle003
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.dLFock :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (Y : Lie E 2), ∀ φ ∈ Fock D.δ, O.dL D Y φ ∈ Fock D.δ := by
  intro F E _ _ _ _ _ _ _ D O Y φ hφ
  let S : Subalgebra ℂ (Module.End ℂ (S4 F)) :=
    { carrier := {z | ∀ φ ∈ Fock D.δ, z φ ∈ Fock D.δ}
      mul_mem' := fun hx hy φ h => hx _ (hy φ h)
      add_mem' := fun hx hy φ h => add_mem (hx φ h) (hy φ h)
      algebraMap_mem' := fun c φ h => Submodule.smul_mem _ c h }
  have hx : ∀ w i, O.x w i ∈ S := fun w i ψ hψ => (opsFock F E D O w i ψ hψ).1
  have hd : ∀ w i, O.d w i ∈ S := fun w i ψ hψ => (opsFock F E D O w i ψ hψ).2
  have hX : ∀ τ a b, O.X D τ a b ∈ S := fun τ a b => by
    fin_cases a <;> fin_cases b
    · exact hx _ _
    · exact add_mem (hx _ _) (S.smul_mem (hx _ _) _)
    · exact sub_mem (hx _ _) (S.smul_mem (hx _ _) _)
    · exact hx _ _
  have hD : ∀ τ a b, O.DX D τ a b ∈ S := fun τ a b => by
    fin_cases a <;> fin_cases b
    · exact hd _ _
    · exact S.smul_mem (add_mem (hd _ _) (S.smul_mem (hd _ _) _)) _
    · exact S.smul_mem (sub_mem (hd _ _) (S.smul_mem (hd _ _) _)) _
    · exact hd _ _
  refine (?_ : O.dL D Y ∈ S) φ hφ
  refine sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ => S.smul_mem (sub_mem (neg_mem ?_) ?_) _
  · split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact sum_mem fun b _ => mul_mem (hX _ _ _) (hD _ _ _)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Ff.TubeLevelLattice

private theorem tube {G X : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X]
    (T : G → X → X) (hT : Continuous fun p : G × X => T p.1 p.2) (h1 : ∀ w, T 1 w = w)
    (hinv : ∀ k w, T k⁻¹ (T k w) = w) {g : X → ℂ} (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∀ᶠ k in 𝓝 (1 : G), ∀ w, g (T k w) = g w :=
  _root_.UpperTheory.Reformulated.B.Qi19.tube T hT h1 hinv hg hc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private def eI (K : Type) [Field K] [NumberField K] : A K := (1, 0)

private theorem am_eI : am E (eI F) = eI E :=
  Prod.ext (map_one (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)))
    (map_zero (AdeleBaseChange.finiteAdeleMap F E))

private theorem eI_fst (K : Type) [Field K] [NumberField K] (x : A K) : (eI K * x).1 = x.1 :=
  one_mul x.1

private theorem eI_snd (K : Type) [Field K] [NumberField K] (x : A K) : (eI K * x).2 = 0 :=
  zero_mul x.2

private theorem fin_fst (k : GL (Fin 2) (Af E)) (a b : Fin 2) :
    ((finGL E 2 k).val a b).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) a b).1 := by
  have := GlobalTheory.HenQ.finGL_apply k a b
  rw [this]
  change ((1 : Matrix (Fin 2) (Fin 2) (A E)) a b).1 -
    (GlobalTheory.CuspRep.sFin E ((1 : Matrix (Fin 2) (Fin 2) (Af E)) a b)).1 +
    (GlobalTheory.CuspRep.sFin E (k.val a b)).1 = _
  rw [GlobalTheory.HenQ.sFin_fst, GlobalTheory.HenQ.sFin_fst, sub_zero, add_zero]

private theorem eI_mul (x y : A E) (h : x.1 = y.1) : eI E * x = eI E * y :=
  Prod.ext (by rw [eI_fst, eI_fst, h]) (by rw [eI_snd, eI_snd])

private theorem eI_fin (k : GL (Fin 2) (Af E)) :
    eI E • (finGL E 2 k).val = eI E • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
  ext a b
  exact eI_mul _ _ (fin_fst k a b)

private theorem eI_star (D : Dat F E) (k : GL (Fin 2) (Af E)) :
    eI E • D.star2 (finGL E 2 k).val = eI E • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
  have hb : D.bar (eI E) = eI E := by rw [← am_eI (F := F), D.bar_am]
  have h1 := eI_fin k
  ext a b
  have h2 := congrFun (congrFun h1 b) a
  simp only [Matrix.smul_apply, smul_eq_mul] at h2 ⊢
  rw [D.conjTransposeGal_apply]
  have h3 := congrArg D.bar h2
  rw [map_mul, map_mul, hb] at h3
  rw [h3]
  have : D.bar ((1 : Matrix (Fin 2) (Fin 2) (A E)) b a) = (1 : Matrix (Fin 2) (Fin 2) (A E)) a b := by
    by_cases hab : a = b
    · subst hab; simp
    · have hba : b ≠ a := fun h => hab h.symm
      simp [Matrix.one_apply, hab, hba]
  rw [this]

private theorem act_eI (D : Dat F E) (k : GL (Fin 2) (Af E)) (v : V4 F) :
    D.act (finGL E 2 k) (eI F • v) = eI F • v := by
  apply D.herm_injective
  rw [D.herm_act, D.herm_smul, am_eI]
  rw [Matrix.mul_smul, ← Matrix.smul_mul, eI_fin, Matrix.smul_mul, one_mul, Matrix.smul_mul,
    ← Matrix.mul_smul, eI_star, Matrix.mul_smul, mul_one]

private theorem act_fst (D : Dat F E) (k : GL (Fin 2) (Af E)) (v : V4 F) (i : Fin 4) :
    (D.act (finGL E 2 k) v i).1 = (v i).1 := by
  have h := congrFun (act_eI D k v) i
  rw [D.act_smul] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have := congrArg Prod.fst h
  rwa [eI_fst, eI_fst] at this

private def io (w : Fin 4 → Af F) : V4 F := fun i => (0, w i)

private theorem continuous_io : Continuous (io (F := F)) :=
  continuous_pi fun i => continuous_const.prodMk (continuous_apply i)

private theorem finPart_io (w : Fin 4 → Af F) : finPartPi (io w) = w := rfl

private theorem split (v : V4 F) : v = eI F • v + io (finPartPi v) := by
  funext i
  refine Prod.ext ?_ ?_
  · show (v i).1 = (eI F * v i).1 + 0
    rw [eI_fst, add_zero]
  · show (v i).2 = (eI F * v i).2 + (v i).2
    rw [eI_snd, zero_add]

private def TT (D : Dat F E) (k : GL (Fin 2) (Af E)) (w : Fin 4 → Af F) : Fin 4 → Af F :=
  finPartPi (D.act (finGL E 2 k) (io w))

private theorem finPart_act (D : Dat F E) (k : GL (Fin 2) (Af E)) (v : V4 F) :
    finPartPi (D.act (finGL E 2 k) v) = TT D k (finPartPi v) := by
  conv_lhs => rw [split v]
  rw [D.act_add, act_eI]
  funext i
  show (eI F * v i).2 + _ = _
  rw [eI_snd, zero_add]
  rfl

end UpperTheory.ConvolutionTheory.R2.Ff.TubeLevelLattice

end

open UpperTheory.ConvolutionTheory.R2.Ff.TubeLevelLattice in
theorem UpperTheory.ConvolutionTheory.R2.Ff.lLevel :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), LLevel W := by
  intro F E _ _ _ _ _ _ _ D W φ
  obtain ⟨ρ, -, -, -, -, hfin⟩ := actCont F E D
  have hT : Continuous fun p : GL (Fin 2) (Af E) × (Fin 4 → Af F) => TT D p.1 p.2 :=
    continuous_finPartPi.comp (D.continuous_act' (hfin.comp continuous_fst) (continuous_io.comp continuous_snd))
  have h1 : ∀ w, TT D 1 w = w := fun w => by
    simp only [TT, map_one, D.act_one, finPart_io]
  have hinv : ∀ k w, TT D k⁻¹ (TT D k w) = w := fun k w => by
    have e := finPart_act D k⁻¹ (D.act (finGL E 2 k) (io w))
    rw [map_inv, D.act_inv_act, finPart_io] at e
    exact e.symm
  have key : ∀ f ∈ schwartzBruhatPi (K := F) (ι := Fin 4), ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)),
      ∀ v, f (D.act (finGL E 2 k)⁻¹ v) = f v := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ₀, g, hg, rfl⟩ := hG
      obtain ⟨hlc, hcs⟩ := (mem_finiteSchwartzBruhatPi F).1 hg
      have ht : Tendsto (fun k : GL (Fin 2) (Af E) => k⁻¹) (𝓝 1) (𝓝 1) := by
        simpa only [inv_one] using (continuous_inv (G := GL (Fin 2) (Af E))).tendsto 1
      filter_upwards [ht.eventually (tube (TT D) hT h1 hinv hlc hcs)] with k hk v
      have e1 : infPartPi (D.act (finGL E 2 k)⁻¹ v) = infPartPi v := by
        funext i
        simp only [infPartPi, ← map_inv, act_fst]
      have e2 : finPartPi (D.act (finGL E 2 k)⁻¹ v) = TT D k⁻¹ (finPartPi v) := by
        rw [← map_inv, finPart_act]
      simp only [schwartzBruhatTensorPi, e1, e2, hk]
    | zero => exact Eventually.of_forall fun _ _ => rfl
    | add G H _ _ hG hH =>
      filter_upwards [hG, hH] with k h h' v
      simp only [Pi.add_apply, h, h']
    | smul c G _ hG =>
      filter_upwards [hG] with k h v
      simp only [Pi.smul_apply, h]
  have hab : ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)), ab (nu F (finGL E 2 k)) = 1 := by
    have hU : (KLev E 2 1 : Set (GL (Fin 2) (Af E))) ∈ 𝓝 (1 : GL (Fin 2) (Af E)) :=
      (isOpen_KLev le_rfl).mem_nhds (one_mem _)
    filter_upwards [hU] with k hk
    let f : GL (Fin 2) (Af E) →* {r : ℝ // 0 < r} :=
      (IdeleGroup.ideleModule F).comp ((ideleNorm F E).comp
        ((Matrix.GeneralLinearGroup.det).comp (finGL E 2)))
    have := GroundTheory.Automorphic.Reduction.eq_one_of_isCompact (isCompact_KLev le_rfl) f
      (continuous_ab.comp (continuous_nu.comp hfin)) hk
    exact congrArg Subtype.val this
  filter_upwards [key φ.1 φ.2, hab] with k h₁ h₂
  refine Subtype.ext (funext fun v => ?_)
  rw [W.L_apply, h₁, h₂]
  simp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem fre_of_rays {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : V → ℂ) (G : V → V →L[ℝ] ℂ) (hG : Continuous G)
    (h : ∀ (X : V) (s : ℝ), HasDerivAt (fun s : ℝ => u (s • X)) (G (s • X) X) s) :
    HasFDerivAt u (G 0) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.1 hG.continuousAt c hc
  filter_upwards [Metric.ball_mem_nhds (0 : V) hδ] with X hX
  have hX' : ‖X‖ < δ := by simpa using hX
  have hv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => u (s • X) - (s : ℂ) * G 0 X)
      (G (s • X) X - G 0 X) (Set.Icc (0 : ℝ) 1) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * G 0 X) (G 0 X) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (G 0 X)
    exact ((h X s).sub h1).hasDerivWithinAt
  have hbd : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖G (s • X) X - G 0 X‖ ≤ c * ‖X‖ := by
    intro s hs
    have hs' : ‖s • X‖ < δ := by
      rw [norm_smul, Real.norm_of_nonneg hs.1]
      calc s * ‖X‖ ≤ 1 * ‖X‖ := by gcongr; exact hs.2
        _ < δ := by simpa using hX'
    have h2 : ‖G (s • X) - G 0‖ < c := by
      simpa [dist_eq_norm] using hb (x := s • X) (by simpa [dist_eq_norm] using hs')
    calc ‖G (s • X) X - G 0 X‖ = ‖(G (s • X) - G 0) X‖ := by simp
      _ ≤ ‖G (s • X) - G 0‖ * ‖X‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖X‖ := by gcongr
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hv hbd (convex_Icc 0 1)
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  simp only [zero_smul, one_smul, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, sub_zero,
    norm_one, mul_one] at key
  have e : u (0 + X) - u 0 - G 0 X = u X - G 0 X - u 0 := by rw [zero_add]; ring
  rw [e]
  exact key

private theorem fderiv_of_exp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : V → ℂ) (ε : V → V) (L : V →L[ℝ] ℂ)
    (hε : HasStrictFDerivAt ε ((ContinuousLinearEquiv.refl ℝ V : V ≃L[ℝ] V) : V →L[ℝ] V) 0)
    (h : HasFDerivAt (f ∘ ε) L 0) : HasFDerivAt f L (ε 0) := by
  have hi := hε.to_localInverse
  have h0 := hε.localInverse_apply_image
  set l := HasStrictFDerivAt.localInverse ε _ 0 hε
  have h' : HasFDerivAt (f ∘ ε) L (l (ε 0)) := by rw [h0]; exact h
  have hc := h'.comp (ε 0) hi.hasFDerivAt
  have e : L.comp (((ContinuousLinearEquiv.refl ℝ V).symm : V ≃L[ℝ] V) : V →L[ℝ] V) = L := by
    ext x; simp
  rw [e] at hc
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hε.eventually_right_inverse] with y hy
  simp only [Function.comp_apply]
  rw [hy]

section
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem exp_eq (Y : Lie E 2) : toL (NormedSpace.exp (Matrix.of Y)) =
    (Cm.archEq E 2).symm (NormedSpace.exp (Cm.archEq E 2 Y)) := by
  letI : NormedRing (Matrix (Fin 2) (Fin 2) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin 2) (Fin 2) (Cinf E)) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (ArchMatrix E 2) := NormedAlgebra.restrictScalars ℚ ℝ _
  refine (Cm.archEq E 2).injective ?_
  rw [ContinuousLinearEquiv.apply_symm_apply, Cm.archEq_toL]
  have hc : Continuous (Cm.matEq E 2) := (Cm.archEq E 2).continuous
  exact NormedSpace.map_exp (Cm.matEq E 2) hc (Matrix.of Y)

private noncomputable def expL (Y : Lie E 2) : Lie E 2 := (Cm.archEq E 2).symm (NormedSpace.exp (Cm.archEq E 2 Y))

private theorem expL_strict : HasStrictFDerivAt (expL (E := E))
    ((ContinuousLinearEquiv.refl ℝ (Lie E 2) : Lie E 2 ≃L[ℝ] Lie E 2) : Lie E 2 →L[ℝ] Lie E 2) 0 := by
  have h1 : HasStrictFDerivAt (fun x : ArchMatrix E 2 => NormedSpace.exp x) (1 : ArchMatrix E 2 →L[ℝ] ArchMatrix E 2)
      (Cm.archEq E 2 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero
  have h2 := ((Cm.archEq E 2).symm.hasStrictFDerivAt.comp _ (h1.comp (0 : Lie E 2) (Cm.archEq E 2).hasStrictFDerivAt))
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  exact (Cm.archEq E 2).symm_apply_apply x

private theorem expL_cont : Continuous (expL (E := E)) := by
  letI : NormedAlgebra ℚ (ArchMatrix E 2) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact (Cm.archEq E 2).symm.continuous.comp (NormedSpace.exp_continuous.comp (Cm.archEq E 2).continuous)

private theorem toL_ex (Y : Lie E 2) : toL (ex Y 1).val = expL Y := by
  have : (ex Y 1).val = NormedSpace.exp (Matrix.of Y) := by
    rw [ex, IsUnit.unit_spec, one_smul]
  rw [this]
  exact exp_eq Y

private theorem ex_smul (X : Lie E 2) (s : ℝ) : ex (s • X) 1 = ex X s := by
  refine Units.ext ?_
  change NormedSpace.exp ((1 : ℝ) • Matrix.of (s • X)) = NormedSpace.exp (s • Matrix.of X)
  rw [one_smul]
  rfl

private theorem ex_zero (X : Lie E 2) : ex X 0 = 1 := by
  refine Units.ext ?_
  change NormedSpace.exp ((0 : ℝ) • Matrix.of X) = 1
  rw [zero_smul, NormedSpace.exp_zero]

private theorem ex_inv (X : Lie E 2) : (ex X 1)⁻¹ = ex (-X) 1 := by
  have h := (exPar E X).1 1 (-1)
  rw [add_neg_cancel, ex_zero] at h
  have e : ex (-X) 1 = ex X (-1) := by
    rw [← ex_smul X (-1), neg_one_smul]
  rw [e]
  exact inv_eq_of_mul_eq_one_right h.symm

private theorem ex_cont : Continuous fun Y : Lie E 2 => ex Y 1 := by
  have hv : Continuous fun Y : Lie E 2 => (ex Y 1).val := by
    have : (fun Y : Lie E 2 => (ex Y 1).val) = fun Y => Matrix.of (expL Y) := by
      funext Y; rw [← toL_ex]; rfl
    rw [this]
    exact expL_cont
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  have : (fun Y : Lie E 2 => ((ex Y 1)⁻¹).val) = fun Y => (ex (-Y) 1).val := by
    funext Y; rw [ex_inv]
  change Continuous (fun Y : Lie E 2 => ((ex Y 1)⁻¹).val)
  rw [this]
  exact hv.comp continuous_neg

end

theorem UpperTheory.ConvolutionTheory.R2.Ff.smFre :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], SmFre E := by
  intro E _ _ _ Φ T hc hd g
  let G : Lie E 2 → Lie E 2 →L[ℝ] ℂ := fun Y =>
    LinearMap.toContinuousLinearMap ((LinearMap.proj (g * infGL E 2 (ex Y 1))) ∘ₗ T)
  have hGa : ∀ Y X, G Y X = T X (g * infGL E 2 (ex Y 1)) := fun _ _ => rfl
  have hG : Continuous G := continuous_clm_apply.2 fun X => by
    simp only [hGa]
    exact (hc X g).comp ex_cont
  have hray : ∀ (X : Lie E 2) (s : ℝ), HasDerivAt (fun s : ℝ => Φ (g * infGL E 2 (ex (s • X) 1))) (G (s • X) X) s := by
    intro X s
    have h1 := hd X (g * infGL E 2 (ex X s))
    have h2 : HasDerivAt (fun r : ℝ => Φ (g * infGL E 2 (ex X s) * infGL E 2 (ex X (r - s))))
        (T X (g * infGL E 2 (ex X s))) s :=
      HasDerivAt.comp_sub_const s s (by simpa using h1)
    rw [hGa, ex_smul]
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    simp only [ex_smul]
    rw [mul_assoc, ← map_mul, ← (exPar E X).1, add_sub_cancel]
  have h1 := fre_of_rays (fun Y => Φ (g * infGL E 2 (ex Y 1))) G hG hray
  have h2 : HasFDerivAt (chart Φ g ∘ expL) (G 0) 0 := by
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun Y => ?_)
    simp only [Function.comp_apply]
    rw [← toL_ex, chart_val]
  have h3 := fderiv_of_exp (chart Φ g) expL (G 0) expL_strict h2
  have h0 : expL (0 : Lie E 2) = oneL E 2 := by
    rw [← toL_ex, ← zero_smul ℝ (0 : Lie E 2), ex_smul, ex_zero]
    rfl
  rw [h0] at h3
  refine ⟨h3.differentiableAt, fun X => ?_⟩
  rw [h3.fderiv, hGa, ← zero_smul ℝ (0 : Lie E 2), ex_smul, ex_zero, map_one, mul_one]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg' {K : Type} [Field K] [NumberField K]
    (S : Set (Fin 4 → FiniteAdeleRing (𝓞 K) K)) (N : ℕ) (v : V4 K) : 0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem continuous_ab {K : Type} [Field K] [NumberField K] :
    Continuous (ab : (A K)ˣ → ℝ) :=
  continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule (K := K))

private theorem ab_pos {K : Type} [Field K] [NumberField K] (a : (A K)ˣ) : 0 < ab a :=
  (IdeleGroup.ideleModule K a).2

theorem UpperTheory.ConvolutionTheory.R2.Ff.lDom :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), LDom W := by
  intro F E _ _ _ _ _ _ _ D W ι s Φ hΦ C hC
  obtain ⟨K, hK, hΦ⟩ := hΦ
  obtain ⟨ρ, hρ, hact, hnu, -, -⟩ := actCont F E D

  let r : GL (Fin 2) (A E) → GL (Fin 4) (A F) := fun h => ρ h⁻¹
  have hr : Continuous r := hρ.comp continuous_inv
  obtain ⟨K', hK', hlin⟩ := wtLin F (r '' C) (hC.image hr) K hK

  let β : GL (Fin 2) (A E) → ℝ := fun h => (ab (nu F h))⁻¹
  have hβ : Continuous β :=
    (continuous_ab.comp hnu).inv₀ fun h => (ab_pos _).ne'
  obtain ⟨A₀, hA₀⟩ := (hC.image hβ).bddAbove
  refine ⟨K', hK', fun N => ?_⟩
  obtain ⟨B, hB⟩ := hΦ N
  obtain ⟨B', hB'⟩ := hlin N
  refine ⟨|A₀| * (|B| * B'), ?_⟩
  rintro ⟨h, i⟩ ⟨hh, hi⟩ v
  have hβ0 : 0 ≤ β h := (inv_pos.2 (ab_pos _)).le
  have hβA : β h ≤ |A₀| := (hA₀ ⟨h, hh, rfl⟩).trans (le_abs_self _)
  have hnorm : ‖(W.L h (Φ i)).1 v‖ = β h * ‖(Φ i).1 (D.act h⁻¹ v)‖ := by
    rw [W.L_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]
  have h1 : ‖(Φ i).1 (D.act h⁻¹ v)‖ ≤ |B| * (B' * wt K' N v) := by
    have h2 : wt K N ((r h).val *ᵥ v) ≤ B' * wt K' N v := hB' (r h) ⟨h, hh, rfl⟩ v
    have h3 := hB i hi (D.act h⁻¹ v)
    rw [hact h⁻¹ v] at h3 ⊢
    calc _ ≤ B * wt K N ((r h).val *ᵥ v) := h3
      _ ≤ |B| * wt K N ((r h).val *ᵥ v) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg' _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  calc ‖(W.L h (Φ i)).1 v‖ = β h * ‖(Φ i).1 (D.act h⁻¹ v)‖ := hnorm
    _ ≤ |A₀| * (|B| * (B' * wt K' N v)) :=
      mul_le_mul hβA h1 (norm_nonneg _) (abs_nonneg _)
    _ = |A₀| * (|B| * B') * wt K' N v := by ring
end
