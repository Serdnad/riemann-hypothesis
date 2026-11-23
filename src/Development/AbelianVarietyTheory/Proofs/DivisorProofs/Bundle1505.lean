module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle962
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_comap_injective_intertwiner : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (f : M →ₗ[ℂ] M'), Function.Injective f → (∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) → (∀ U' : Submodule ℂ M', UnitOn s F' U' → UnitOn s F (U'.comap f)) ∧ (LocU s F' → LocU s F) := by
  first | exact @GlobalTheory.HoweR.unitOn_comap_locU | exact GlobalTheory.HoweR.unitOn_comap_locU | (intros; apply GlobalTheory.HoweR.unitOn_comap_locU <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_of_le_stable : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ U U' : Submodule ℂ M, UnitOn s F U → U' ≤ U → (∀ a b, s a = s b → ∀ u ∈ U', F a b u ∈ U') → UnitOn s F U' := by
  first | exact @GlobalTheory.HoweR.unitOn_of_le | exact GlobalTheory.HoweR.unitOn_of_le | (intros; apply GlobalTheory.HoweR.unitOn_of_le <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.isLocallyBlockUnitary_pi_fin : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), LocU s F → ∀ n : ℕ, LocU s (fun a b => (LinearMap.pi fun i : Fin n => F a b ∘ₗ LinearMap.proj i : Module.End ℂ (Fin n → M))) := by
  first | exact @GlobalTheory.HoweR.locU_pi_fin | exact GlobalTheory.HoweR.locU_pi_fin | (intros; apply GlobalTheory.HoweR.locU_pi_fin <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.quadraticOperator_eigenvector_diagonalBlock_identity : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x : ℂ) (y : ι → M), (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ j, s j = false → ∑ b, F j b (y b) = 0) → ∀ a, (x ^ 2 - α * x - β) • y a = 0 := by
  first | exact @GlobalTheory.HoweR.qop_quadratic_on_eigenvector | exact GlobalTheory.HoweR.qop_quadratic_on_eigenvector | (intros; apply GlobalTheory.HoweR.qop_quadratic_on_eigenvector <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.fockHarmonics_sup_coinvariants_eq_top : ∀ (P Q R S : ℕ) (x : ℂ), Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := by
  first | exact @GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ | exact GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ | (intros; apply GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.fockSecondAction_quadraticIdentity_mod_coinvariants : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f, qop (units (fockAct2 P Q R S)) α β a b f ∈ coinv P Q R S x := by
  first | exact @GlobalTheory.HoweR.SecondQuad.qop_mem_coinv | exact GlobalTheory.HoweR.SecondQuad.qop_mem_coinv | (intros; apply GlobalTheory.HoweR.SecondQuad.qop_mem_coinv <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → mixArch L M hr = mixArch L' M hr) ∧ (∀ τ : Equiv.Perm (Fin e), mixArch (fun a => L (τ a)) M hr = mixArch L M hr) ∧ ∀ (M' : HermLB q) (r' : M'.B.ι → Y.functionFieldˣ) (hr' : IsRatSec M'.B r'), M'.div hr' = M.div hr → (∀ σ, Set.EqOn (logNorm (M'.φ σ) r') (logNorm (M.φ σ) r) (offSupp q σ (M.div hr))) → mixArch L M' hr' = mixArch L M hr := by
  first | exact @GlobalTheory.MixHt.mixArch_iso_symm_congr | exact GlobalTheory.MixHt.mixArch_iso_symm_congr | (intros; apply GlobalTheory.MixHt.mixArch_iso_symm_congr <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.highestWeight_le_span_sup_fockCoinvariants : ∀ (P Q R S : ℕ) (x : ℚ) (μ' : Ix R S → ℚ), JointShape P Q R S (fun _ => x) μ' → ∃ f₀ : Formalism.BasicNotions.TH.Pol P Q R S, hwSub (fockAct2 P Q R S) μ' ≤ Submodule.span ℂ {f₀} ⊔ coinv P Q R S (x : ℂ) := by
  first | exact @GlobalTheory.HoweR.hw_le_span_sup_coinv | exact GlobalTheory.HoweR.hw_le_span_sup_coinv | (intros; apply GlobalTheory.HoweR.hw_le_span_sup_coinv <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.mem_piTensorSpanAllFactors_of_jointKernel : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (L : ∀ w, Set (Module.End ℂ (V w))) (H : ∀ w, Submodule ℂ (V w)), (∀ w v, (∀ l ∈ L w, l v = 0) → v ∈ H w) → ∀ y : PiTensorProduct ℂ V, (∀ w, ∀ l ∈ L w, atPl w l y = 0) → y ∈ tensAll H := by
  first | exact @GlobalTheory.HoweR.mem_tensAll_of_killed | exact GlobalTheory.HoweR.mem_tensAll_of_killed | (intros; apply GlobalTheory.HoweR.mem_tensAll_of_killed <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.negTranspose_fockSecondAction_quadratic_mod_coinvariants : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f, qop (negT (units (fockAct2 P Q R S))) α β a b f ∈ coinv P Q R S x := by
  first | exact @GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | exact GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | (intros; apply GlobalTheory.HoweR.QuadT.negT_fockAct2_quad <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem clo_restrict_dominant : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) (y : Y), ∃ g : clo y ⟶ clo (π y), g ≫ cloι (π y) = cloι y ≫ π ∧ g (genericPoint _) = genericPoint _ ∧ ∀ w : clo y, g.residueDegree w = π.residueDegree (cloι y w) := by
  intro X Y π y
  set i := cloι (π y)
  set j := cloι y
  have hi : i (genericPoint (clo (π y))) = π y := cloι_genericPoint _
  have hj : j (genericPoint (clo y)) = y := cloι_genericPoint _
  have hr : Set.range i = closure {π y} := by
    have h₁ := (genericPoint_spec (clo (π y))).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  have : Surjective (Limits.pullback.snd i (j ≫ π)) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]
    refine Set.eq_univ_of_forall fun w => ?_
    have := ((genericPoint_specializes w).map (j ≫ π).continuous)
    rw [Set.mem_preimage]
    have e : (j ≫ π) (genericPoint (clo y)) = π y := by
      rw [Scheme.Hom.comp_apply, hj]
    rw [e] at this
    exact this.mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i (j ≫ π))
  refine ⟨inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π), ?_, ?_, ?_⟩
  · rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]
  · apply i.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      Scheme.Hom.comp_apply, hj, hi]
  · intro w
    have e₁ := GlobalTheory.CurveDegreesCompare.residueDegree_comp (inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π)) i w
    have e₂ := GlobalTheory.CurveDegreesCompare.residueDegree_comp j π w
    rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      GlobalTheory.Published.residueDegree_of_isClosedImmersion i, one_mul] at e₁
    rw [GlobalTheory.Published.residueDegree_of_isClosedImmersion j, mul_one] at e₂
    rw [← e₁, e₂]

end GlobalTheory.MixHt
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD
open GlobalTheory.RealLift.OneParam

theorem exists_line_of_upqD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ Y : ∀ w : InfinitePlace F, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∃ γ ∈ RLines (σ := σ) J, IsGenD τ C γ Y := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hCM hC Y hY
  have := hCM.1
  obtain ⟨ξ, hξ⟩ := exists_moved hCM
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hCM hξ (τ w).1
  choose C' hC' using fun w => (hC w).2
  have hL : ∀ w, C' w * C w = 1 := fun w => frame_inv (hC w).1 (hC' w)
  set G : InfinitePlace F → ℝ → Matrix β β ℂ := fun w t => C w * NormedSpace.exp (t • Y w) * C' w with hG
  set f : ℝ → Matrix β β (AE F E) := fun t => 1 + liftM τ ξ (fun w => G w t - 1) with hf
  have hfπ : ∀ t w, (f t).map (piInf (τ w)) = G w t := fun t w => by
    rw [hf, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ', add_sub_cancel]
  have hfat : ∀ t, At (evI F) (f t - 1) := fun t => by
    rw [hf, add_sub_cancel_left]
    exact at_liftM τ ξ _
  have hfadd : ∀ s t, f (s + t) = f s * f t := fun s t => by
    refine (eq_of_at hCM τ ?_ fun w => ?_).symm
    · have e : f s * f t - f (s + t) = (f s - 1) * f t + (f t - 1) - (f (s + t) - 1) := by noncomm_ring
      rw [e]
      exact at_sub (at_add (at_mul_right (hfat s) _) (hfat t)) (hfat _)
    · rw [Matrix.map_mul, hfπ, hfπ, hfπ]
      exact (conj_add (hL w) (Y w) s t).symm
  have hf0 : f 0 = 1 := by
    refine eq_of_at hCM τ (hfat 0) fun w => ?_
    rw [hfπ, Matrix.map_one _ (map_zero _) (map_one _)]
    exact conj_zero (hC' w) (Y w)
  have hfU : ∀ t, (f t)ᵀ * J * (f t).map (cA σ) = J := fun t => by
    refine eq_of_at hCM τ ?_ fun w => ?_
    · have e : (f t)ᵀ * J * (f t).map (cA σ) - J =
          (f t - 1)ᵀ * J * (f t).map (cA σ) + J * (f t - 1).map (cA σ) := by
        have e1 : (f t - 1).map (cA σ) = (f t).map (cA σ) - 1 := by
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      exact at_add (at_mul_right (at_mul_right (at_transpose (hfat t)) _) _)
        (at_mul_left (at_map_cA σ (hfat t)) _)
    · have hc : ((f t).map (cA σ)).map (piInf (τ w)) = (G w t).map star := by
        rw [← hfπ t w, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, hfπ]
      by_cases hb : b = 0
      · haveI := isEmpty_of_zero (hb ▸ (hC w).1) (hC' w)
        ext i
        exact isEmptyElim i
      · have h1 := conj_unitary (hC w).1 (hC' w) (hY w) t
        rw [Matrix.mul_smul, Matrix.smul_mul] at h1
        exact smul_right_injective _ hb h1
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  have hfc : Continuous f :=
    continuous_const.add ((continuous_liftM τ ξ).comp (continuous_pi fun w =>
      (((continuous_const.matrix_mul (continuous_exp_smul (Y w))).matrix_mul continuous_const).sub continuous_const)))
  let g : ℝ → UG (cA σ) J := fun t => ⟨⟨f t, f (-t), by rw [← hfadd, add_neg_cancel, hf0],
    by rw [← hfadd, neg_add_cancel, hf0]⟩, hfU t⟩
  let γ : Multiplicative ℝ →* UG (cA σ) J :=
    { toFun := fun t => g (Multiplicative.toAdd t)
      map_one' := Subtype.ext (Units.ext hf0)
      map_mul' := fun x y => Subtype.ext (Units.ext (hfadd _ _)) }
  refine ⟨γ, ⟨?_, fun t => hfat _⟩, fun t w => ?_⟩
  · have hu : Continuous fun t : Multiplicative ℝ => ((g (Multiplicative.toAdd t)).1 : GL β (AE F E)) :=
      Units.continuous_iff.2 ⟨hfc.comp continuous_toAdd, (hfc.comp continuous_neg).comp continuous_toAdd⟩
    exact hu.subtype_mk _
  · change (f t).map (piInf (τ w)) * C w = C w * NormedSpace.exp (t • Y w)
    rw [hfπ, hG]
    simp only [Matrix.mul_assoc]
    rw [hL, Matrix.mul_one]

end GlobalTheory.HoweD
end
end
