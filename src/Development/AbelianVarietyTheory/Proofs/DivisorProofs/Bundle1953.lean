module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LeviOp

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem map_inv_mul {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A⁻¹.map g * A.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem map_mul_inv {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A.map g * A⁻¹.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem hom_mulVec {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (g : F →+* S) (g' : F →+* T)
    (hg : f.comp g = g') (M : Matrix κ κ F) (x : κ → S) (i : κ) :
    f ((M.map g *ᵥ x) i) = (M.map g' *ᵥ (fun j => f (x j))) i := by
  subst hg

  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem spAct_levi {R : Type} [CommRing R] [Algebra F R] (A : Matrix κ κ F) (w : (κ → R) × (κ → R)) :
    GlobalTheory.SympChange.spAct (GlobalTheory.SympChange.leviM A) w =
      (A.map (algebraMap F R) *ᵥ w.1, (A⁻¹.map (algebraMap F R))ᵀ *ᵥ w.2) := by
  unfold GlobalTheory.SympChange.spAct GlobalTheory.SympChange.leviM
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec]
  ext k <;> simp [Matrix.transpose_map]

theorem schr_levi {R : Type} [CommRing R] [Algebra F R] [Invertible (2 : R)] (ψ : AddChar R ℂ)
    (A : Matrix κ κ F) (hA : IsUnit A.det) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    (fun x => schr ψ w φ (A⁻¹.map (algebraMap F R) *ᵥ x)) =
      schr ψ (GlobalTheory.SympChange.spAct (GlobalTheory.SympChange.leviM A) w) (fun x => φ (A⁻¹.map (algebraMap F R) *ᵥ x)) := by
  rw [spAct_levi]
  funext x
  simp only [GlobalTheory.WeilM.schr]
  have h1 := map_inv_mul (algebraMap F R) A hA
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
    Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

def homeo {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S) (A : Matrix κ κ F)
    (hA : IsUnit A.det) : (κ → S) ≃ₜ (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem homeo_apply {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) (x : κ → S) : homeo g A hA x = A⁻¹.map g *ᵥ x := rfl

def linEquiv {S : Type} [CommRing S] [Algebra ℝ S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) : (κ → S) ≃L[ℝ] (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  map_add' x y := Matrix.mulVec_add _ x y
  map_smul' c x := Matrix.mulVec_smul _ c x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem sb_comp {X : Type} [TopologicalSpace X] (h : X ≃ₜ X) {φ : X → ℂ} (hφ : φ ∈ SB X) : φ ∘ h ∈ SB X :=
  ⟨hφ.1.comp_continuous h.continuous, hφ.2.comp_homeomorph h⟩

variable [NumberField F]

def evIr : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem mulVec_mem {v : Pl (F := F)} (M : Matrix κ κ F)
    (hM : ∀ i j, algebraMap F (Fv F v) (M i j) ∈ v.adicCompletionIntegers F) (x : κ → Fv F v)
    (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) (i : κ) :
    (M.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact sum_mem fun j _ => mul_mem (hM i j) (hx j)

theorem eventually_int (M : Matrix κ κ F) :
    ∀ᶠ v : Pl F in cofinite, ∀ i j, algebraMap F (Fv F v) (M i j) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  exact fun i j => (algebraMap F (Af F) (M i j)).2


open scoped Classical in
theorem hasOp_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.leviM A) := by
  intro F _ _ ψ _ _ _ κ _ _ A hA
  let gI : F →+* mixedEmbedding.mixedSpace F := (evIr (F := F)).comp (algebraMap F (AF F))
  let gF : F →+* FiniteAdeleRing (𝓞 F) F := (RingHom.snd _ _).comp (algebraMap F (AF F))
  let L := linEquiv (κ := κ) gI A hA
  refine ⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x),
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L,
    fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f, ?_⟩
    refine SchwartzMap.ext fun x => ?_
    simp
  · have key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
        LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) (pureA F f g) =
          pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f) (g ∘ homeo gF A hA) := by
      intro f g
      funext x
      simp only [LinearMap.funLeft_apply, pureA, Function.comp_apply, homeo_apply,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      congr 1
      · congr 1
        funext i
        exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
      · congr 1
        funext i
        exact hom_mulVec (RingHom.snd _ _) (algebraMap F (AF F)) gF rfl A⁻¹ x i
    have hle : schA F κ ≤ (schA F κ).comap
        (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, g, hg, rfl⟩
      show _ ∈ schA F κ
      rw [key]
      exact Submodule.subset_span ⟨_, _, sb_comp (homeo gF A hA) hg, rfl⟩
    exact fun Φ hΦ => hle hΦ
  · intro w Φ _
    exact schr_levi ψ A hA w Φ
  · intro v
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun φ hφ => sb_comp (homeo _ A hA) hφ) ?_
    intro φ hφ
    refine ⟨φ ∘ (homeo (algebraMap F (Fv F v)) A hA).symm, sb_comp _ hφ, ?_⟩
    funext x
    simp only [LinearMap.funLeft_apply, Function.comp_apply]
    exact congrArg φ ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x)
  · intro v φ _ h
    funext x
    have := congrFun h ((homeo (algebraMap F (Fv F v)) A hA).symm x)
    simp only [LinearMap.funLeft_apply, Pi.zero_apply] at this
    have hx : A⁻¹.map (algebraMap F (Fv F v)) *ᵥ (homeo (algebraMap F (Fv F v)) A hA).symm x = x :=
      (homeo (algebraMap F (Fv F v)) A hA).apply_symm_apply x
    rw [hx] at this
    exact this
  · intro v w φ _
    exact schr_levi (GlobalTheory.LatVac.psiAt ψ v) A hA w φ
  · filter_upwards [eventually_int A, eventually_int A⁻¹] with v hA1 hA2
    funext x
    have hiff : (∀ i, (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, x i ∈ v.adicCompletionIntegers F := by
      constructor
      · intro h i
        have e : x = A.map (algebraMap F (Fv F v)) *ᵥ (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) :=
          ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x).symm
        rw [e]
        exact mulVec_mem A hA1 _ h i
      · intro h i
        exact mulVec_mem A⁻¹ hA2 x h i
    show Set.indicator _ _ _ = Set.indicator _ _ _
    by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
    · rw [Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hiff.2 hx),
        Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
      rfl
    · rw [Set.indicator_of_notMem (show _ ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from mt hiff.1 hx),
        Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
  · intro f φ _ _
    funext x
    simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply]
    congr 1
    · congr 1
      funext i
      exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
    · refine finprod_congr fun v => congrArg (φ v) ?_
      funext i
      exact hom_mulVec (evFin F v).toRingHom (algebraMap F (AF F)) (algebraMap F (Fv F v))
        (RingHom.ext fun c => (evFin F v).commutes c) A⁻¹ x i

end GlobalTheory.LeviOp
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.SplitUnitLiftCont

open GlobalTheory.SplitGLLift GlobalTheory.SplitUnitLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)}

theorem continuous_liftPair (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    Continuous (liftPair h τ) := by
  have hj : Continuous (LinearMap.inr F (Ainf F) (Af F) ∘ₗ GlobalTheory.AdelicU.singleFin v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  have h1 : Continuous (GlobalTheory.AdelicU.Supp.singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ hj
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have h2 : Continuous ((splitAlgEquiv h τ).symm : Fv F v × Fv F v → Fv F v ⊗[F] E) :=
    IsModuleTopology.continuous_of_linearMap (splitAlgEquiv h τ).symm.toLinearMap
  exact h1.comp h2

theorem continuous_liftMat (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} :
    Continuous (liftMat (n := Fin n) h τ) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun p : Matrix (Fin n) (Fin n) (Fv F v) × Matrix (Fin n) (Fin n) (Fv F v) =>
    liftPair h τ (p.1 i j, p.2 i j)
  exact (continuous_liftPair h τ).comp
    (((continuous_fst.matrix_elem i j)).prodMk (continuous_snd.matrix_elem i j))

theorem continuous_liftN (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map τ).det) : Continuous (liftN h τ J hJ) := by
  have : IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := IsModuleTopology.isTopologicalRing (AF F) _
  have hp : Continuous (pairHom (J.map τ) hJ) := by
    show Continuous fun g : GL (Fin n) (Fv F v) => ((g : Matrix (Fin n) (Fin n) (Fv F v)),
      (J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ)
    refine Units.continuous_val.prodMk ?_
    exact (continuous_const.matrix_mul (Units.continuous_coe_inv.matrix_transpose)).matrix_mul continuous_const
  show Continuous fun g => 1 + liftMat h τ (pairHom (J.map τ) hJ g - 1)
  exact continuous_const.add ((continuous_liftMat h τ).comp (hp.sub continuous_const))

theorem continuous_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    Continuous (liftU h τ J ε herm hJ) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.2 ⟨continuous_liftN h τ J hJ, ?_⟩
  exact (continuous_liftN h τ J hJ).comp continuous_inv

theorem tendsto_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    Tendsto (liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := by
  have := (continuous_liftU h τ J ε herm hJ).tendsto 1
  rwa [map_one] at this

theorem tendsto_liftU_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)} {n : ℕ} (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F) (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det), Tendsto (GlobalTheory.SplitUnitLift.liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := fun h τ J ε herm hJ => tendsto_liftU h τ J ε herm hJ

end GlobalTheory.SplitUnitLiftCont

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

namespace GlobalTheory.BlockForms


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem isBlockEmb_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      Continuous ι := by
  intro F E _ _ _ _ _ _ σ hσ n J _ r Xf Yf _ l d h ι hι
  obtain ⟨Φ, j, _, hΦs, -, -, hform⟩ := hι
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ hσ.2.2.1
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsig : Continuous (sigR (AF F) σ) := by
    have hc := IsModuleTopology.continuous_of_linearMap (R := AF F) (LinearMap.baseChange (AF F) σ.toLinearMap)
    refine hc.congr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 : Continuous fun g : GlobalTheory.CuspRep.GA E d => g.1.map Φ.symm :=
    Units.continuous_val.matrix_map hΦs
  have h2 : Continuous fun g : GlobalTheory.CuspRep.GA E d => (g⁻¹).1.map Φ.symm :=
    Units.continuous_coe_inv.matrix_map hΦs
  have h3 : Continuous fun g : GlobalTheory.CuspRep.GA E d => Matrix.transpose (((g⁻¹).1.map Φ.symm).map (sigR (AF F) σ)) :=
    (h2.matrix_map hsig).matrix_transpose
  have hM : Continuous fun g : GlobalTheory.CuspRep.GA E d => (matHom _ σ J (ι g)).1 := by
    refine Continuous.congr ?_ fun g => (hform g).symm
    exact (continuous_const.add ((continuous_const.matrix_mul (h1.sub continuous_const)).matrix_mul continuous_const)).add
      ((continuous_const.matrix_mul (h3.sub continuous_const)).matrix_mul continuous_const)
  have hMi : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((matHom _ σ J (ι g))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 := by
    refine (hM.comp continuous_inv).congr fun g => ?_
    simp only [Function.comp_apply, map_inv]
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨hM, hMi⟩)

end GlobalTheory.BlockForms
end

section

set_option autoImplicit false

open Matrix
open GlobalTheory.FlagFibre (Low)

namespace GlobalTheory.FlagCell

theorem exists_elim_row {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (i : Fin m)
    (h : IsUnit (A.submatrix (Fin.castLE i.2.le) (Fin.castLE i.2.le)).det) :
    ∃ r : Fin m → R, r i = 1 ∧ (∀ k, i < k → r k = 0) ∧ ∀ j, j < i → ∑ k, r k * A k j = 0 := by
  classical
  set c : Fin i → Fin m := Fin.castLE i.2.le with hc
  set B := A.submatrix c c with hB
  set x : Fin i → R := (fun j => A i (c j)) ᵥ* B⁻¹ with hx
  have hxB : x ᵥ* B = fun j => A i (c j) := by
    rw [hx, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ h, Matrix.vecMul_one]
  have hlt : ∀ l, c l < i := fun l => l.2
  refine ⟨Pi.single i 1 - ∑ l, Pi.single (c l) (x l), ?_, ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.single_eq_same, Finset.sum_apply]
    rw [Finset.sum_eq_zero fun l _ => Pi.single_eq_of_ne (hlt l).ne' _, sub_zero]
  · intro k hk
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [Finset.sum_eq_zero fun l _ => Pi.single_eq_of_ne ((hlt l).trans hk).ne' _,
      Pi.single_eq_of_ne hk.ne', sub_zero]
  · intro j hj
    have hj' : c ⟨j, hj⟩ = j := rfl
    have h1 := congrFun hxB ⟨j, hj⟩
    simp only [Matrix.vecMul, dotProduct, hB, Matrix.submatrix_apply, hj'] at h1
    simp only [Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul]
    rw [h1, sub_self]

theorem exists_lu (R : Type) [CommRing R] (m : ℕ) (A : Matrix (Fin m) (Fin m) R)
    (h : ∀ l : Fin (m + 1), IsUnit (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det) :
    ∃ (n : Low m → R) (M : Matrix (Fin m) (Fin m) R),
      M.BlockTriangular id ∧ IsUnit M.det ∧ A = uniR n * M := by
  classical
  choose r h1 h0 hA using fun i : Fin m => exists_elim_row A i (h i.castSucc)
  let L : Matrix (Fin m) (Fin m) R := Matrix.of r
  have hL : L.BlockTriangular OrderDual.toDual := fun i k hk => h0 i k hk
  have hdet : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hL]
    exact Finset.prod_eq_one fun i _ => h1 i
  have hu : IsUnit L.det := hdet ▸ isUnit_one
  have hAu : IsUnit A.det := by simpa using h (Fin.last m)
  letI := L.invertibleOfIsUnitDet hu
  have hLi : L⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular hL
  have hd : ∀ i, L⁻¹ i i = 1 := by
    intro i
    have := congrFun (congrFun (Matrix.mul_nonsing_inv L hu) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.one_apply_eq] at this
    · have h2 : L i i = 1 := h1 i
      rwa [h2, one_mul] at this
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [hLi (i := k) (j := i) hk, mul_zero]
      · rw [hL (i := i) (j := k) hk, zero_mul]
    · simp
  refine ⟨fun s => L⁻¹ s.1.1 s.1.2, L * A, fun i j hj => hA i j hj, ?_, ?_⟩
  · rw [Matrix.det_mul]; exact hu.mul hAu
  · have : (uniR fun s : Low m => L⁻¹ s.1.1 s.1.2) = L⁻¹ := by
      ext a b
      rw [uniR_apply]
      split_ifs with hab hab'
      · rfl
      · rw [hab', hd]
      · exact (hLi (i := a) (j := b) (show a < b from lt_of_le_of_ne (not_lt.1 hab) hab')).symm
    rw [this, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hu, Matrix.one_mul]

end GlobalTheory.FlagCell
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPic

namespace GlobalTheory.TranslFst

theorem iso_transl_fst : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB (G2 A).left), L.IsLB → (∃ t : (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ h : 𝟙_ (Over S) ⟶ A, (∃ t : (L.pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, t.IsGen) → LBIso L (L.pull (GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A)).left) := by
  intro S A _ _ hA L hL h1 h2 h hh
  have hG : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have z : ∀ (f : A ⟶ G2 A), (∃ t : (L.pull f.left).Gen, t.IsGen) → pull f.left (cls L hL) = 0 := by
    intro f hf
    rw [← cls_pull hL _ (pull_isLB hL _)]
    exact (cls_eq_zero_iff _).2 hf
  have fac : ∀ (g : G2 A ⟶ A) (e : A ⟶ G2 A), pull e.left (cls L hL) = 0 → pull (g ≫ e).left (cls L hL) = 0 := by
    intro g e he
    rw [Over.comp_left, pull_comp, he, map_zero]
  have cube := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hG L hL (G2 A) (lift (fst A A) 1) (toUnit _ ≫ lift h 1)
    (lift 1 (snd A A))
  have e := (cls_linComb hL _ _ (LB.isLB_linComb hL _ _)).symm.trans ((cls_eq_zero_iff _).2 cube)
  have habc : (lift (fst A A) 1 : G2 A ⟶ G2 A) * (toUnit _ ≫ lift h 1) * lift 1 (snd A A) =
      GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A) := by
    ext <;> simp [GlobalTheory.UPel.HT.Hecke.transl, MonObj.mul_comp, MonObj.comp_mul]
  have hac : (lift (fst A A) 1 : G2 A ⟶ G2 A) * lift 1 (snd A A) = 𝟙 _ := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hbc : (toUnit _ ≫ lift h 1 : G2 A ⟶ G2 A) * lift 1 (snd A A) = snd A A ≫ lift (toUnit A ≫ h) (𝟙 A) := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hab : (lift (fst A A) 1 : G2 A ⟶ G2 A) * (toUnit _ ≫ lift h 1) = (fst A A * (toUnit _ ≫ h)) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have ha : (lift (fst A A) 1 : G2 A ⟶ G2 A) = fst A A ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hb : (toUnit _ ≫ lift h 1 : G2 A ⟶ G2 A) = (toUnit _ ≫ h) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hc : (lift 1 (snd A A) : G2 A ⟶ G2 A) = snd A A ≫ lift 1 (𝟙 A) := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have h1' : (1 : G2 A ⟶ G2 A) = (1 : G2 A ⟶ A) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  simp only [Fin.sum_univ_eight, Matrix.cons_val] at e
  rw [habc, hac, hbc, hab, ha, hb, hc, h1', Over.id_left, pull_id] at e
  simp only [fun g => fac g _ (z _ h1), fun g => fac g _ (z _ h2), fun g => fac g _ (z _ hh)] at e
  have key : pull (GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A)).left (cls L hL) = cls L hL := by
    simp only [one_smul, neg_smul, smul_zero, neg_zero, add_zero, zero_add] at e
    exact eq_of_sub_eq_zero ((sub_eq_add_neg _ _).trans e)
  refine (cls_eq_iff hL (pull_isLB hL _)).1 ?_
  rw [cls_pull hL, key]

end GlobalTheory.TranslFst
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryToTransposeGramGroupMap_surjective : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • Matrix.reindex e e X.gramᵀ), Function.Surjective (GlobalTheory.SquareAgree.kapX X e hJ) := by
  first | exact @GlobalTheory.SquareAgree.kapX_surjective | exact GlobalTheory.SquareAgree.kapX_surjective | (intros; apply GlobalTheory.SquareAgree.kapX_surjective <;> assumption)
end
