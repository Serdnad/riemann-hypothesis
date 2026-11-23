module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Mathlib.Algebra.Module.Lattice.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle622
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

theorem _root_.GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity : ∀ (F : Type) [Field F] [NumberField F] (lam : (AF F)ˣ →* Circle), Continuous lam →
    (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) → ∃ M : ℕ, 0 < M ∧ ∀ b : (AF F)ˣ,
      (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1 := by
  first | exact @GlobalTheory.HeckeExtend.exists_cong_ker | exact GlobalTheory.HeckeExtend.exists_cong_ker | (intros; apply GlobalTheory.HeckeExtend.exists_cong_ker <;> assumption)
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

theorem _root_.GlobalTheory.T.exists_rescale_primitive_in_lattice_at_split_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E → ∀ x y : Fin n → E, x ≠ 0 → y ≠ 0 →
    ∀ (P : Finset (HeightOneSpectrum (𝓞 F))) (τ : ∀ v : P, E →ₐ[F] Fv F v.1), ∃ c : E, c ≠ 0 ∧
      ∀ v : P, PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L (c • x) ∧ PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L ((σ c)⁻¹ • y) := by
  first | exact @GlobalTheory.PlaneSkewScale.exists_rescale_primAt | exact GlobalTheory.PlaneSkewScale.exists_rescale_primAt | (intros; apply GlobalTheory.PlaneSkewScale.exists_rescale_primAt <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

theorem _root_.GlobalTheory.T.isLattice_sublatticePullbackAlongEmbedding : ∀ (E : Type) [Field E] [NumberField E] (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (ι : Matrix (Fin n) (Fin n₁) E), L.IsLattice E → Function.Injective ι.mulVec → (lowLat ι L).IsLattice E := by
  first | exact @GlobalTheory.PlaneSkew.isLattice_lowLat | exact GlobalTheory.PlaneSkew.isLattice_lowLat | (intros; apply GlobalTheory.PlaneSkew.isLattice_lowLat <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

open scoped Classical

namespace GlobalTheory.DoublingEv.ConjTame

def conjSch {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] :
    SchwartzMap D ℂ →SL[starRingEnd ℂ] SchwartzMap D ℂ :=
  SchwartzMap.mkCLM (𝕜 := ℂ) (𝕜' := ℂ) (σ := starRingEnd ℂ) (fun f x => star (f x))
    (fun f g x => by simp [star_add])
    (fun a f x => by simp [smul_eq_mul, mul_comm])
    (fun f => Complex.conjCLE.contDiff.comp (f.smooth ⊤))
    (fun n => ⟨{n}, 1, zero_le_one, fun f x => by
      have h : (fun x => star (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := rfl
      rw [h, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Finset.sup_singleton, one_mul]
      exact SchwartzMap.le_seminorm ℂ n.1 n.2 f x⟩)

theorem conjSch_apply {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] (f : SchwartzMap D ℂ) (x : D) :
    conjSch f x = star (f x) := rfl

theorem star_mem_SB {X : Type} [TopologicalSpace X] {g : X → ℂ} (hg : g ∈ SB X) : star g ∈ SB X :=
  ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩

variable {F : Type} [Field F] [NumberField F]

theorem star_pureA {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    star (pureA F (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) g) = pureA F (conjSch f : _ → ℂ) (star g) := by
  funext x
  simp [pureA, conjSch_apply, star_mul', Pi.star_apply]

end GlobalTheory.DoublingEv.ConjTame


open GlobalTheory.DoublingEv.ConjTame in
theorem GlobalTheory.DoublingEv.isTame_conjMap : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsTame F T → IsTame F (conjMap T) := by
  intro F _ _ κ κ' _ _ T hT g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT (star g) (star_mem_SB hg)
  let Q : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ :=
    fun j => (conjSch.comp (P j)).comp conjSch
  refine ⟨ι, inferInstance, Q, fun j => star (g' j), fun j => star_mem_SB (hg' j), fun f => ?_⟩
  have hs : star (pureA F (f : _ → ℂ) g) = pureA F (conjSch f : _ → ℂ) (star g) := by
    rw [star_pureA]
  rw [conjMap_apply, hs, hP, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_pureA]
  rfl

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
open GlobalTheory.SliceSchwartz
open scoped RestrictedProduct

open scoped Classical

noncomputable section

namespace GlobalTheory.TamePartR

theorem td_of_inj {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [TotallyDisconnectedSpace Y]
    (f : X → Y) (hf : Continuous f) (hi : Function.Injective f) : TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs => ?_⟩
  have h := (hs.image f hf.continuousOn).subsingleton
  exact fun x hx y hy => hi (h (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))

theorem td_adic {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

theorem totallyDisconnected_finiteAdele : ∀ (F : Type) [Field F] [NumberField F], TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (v.adicCompletion F) := fun v => td_adic v
  haveI : TotallyDisconnectedSpace (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]) :=
    td_of_inj (fun x v => x v) (continuous_pi fun v => RestrictedProduct.continuous_eval v)
      fun x y h => Subtype.ext (funext fun v => congrFun h v)
  exact inferInstanceAs (TotallyDisconnectedSpace (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem pureA_sum (F : Type) [Field F] [NumberField F] {κ ι : Type} [Fintype ι] (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : pureA F f (∑ i, g i) = ∑ i, pureA F f (g i) := by
  funext x
  simp [pureA, Finset.sum_apply, Finset.mul_sum]

theorem isTame_partR : ∀ (F : Type) [Field F] [NumberField F] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ₁' → AF F) → ℂ)), IsTame F T → IsTame F (partR (κ := κ) T) := by
  intro F _ _ κ κ' κ₁' _ _ _ T hT g hg
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele (F := F)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField (F := F)
  haveI := totallyDisconnected_finiteAdele F
  obtain ⟨ι₀, _, g₁, g₂, hg₁, hg₂, rfl⟩ := GlobalTheory.T.schwartz_product_decomposition _ κ κ' g hg
  choose ι inst P g' hg' hP using fun i => hT (g₂ i) (hg₂ i)
  choose Q hQ using fun (p : Σ i, ι i) => GlobalTheory.T.schwartz_tensor_right_operator (mixedEmbedding.mixedSpace F) κ κ' κ₁' (P p.1 p.2)
  refine ⟨Σ i, ι i, inferInstance, Q, fun p z => g₁ p.1 (z ∘ Sum.inl) * g' p.1 p.2 (z ∘ Sum.inr),
    fun p => GlobalTheory.SchwartzBox.sb_box (hg₁ p.1) (hg' p.1 p.2), fun f => ?_⟩

  rw [pureA_sum, map_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  funext s
  rw [partR_apply, Finset.sum_apply]
  set xa : κ → mixedEmbedding.mixedSpace F := fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (s (Sum.inl k)).1
  have hfun : (fun x₂ => pureA F f (fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr)) (Sum.elim (s ∘ Sum.inl) x₂)) =
      g₁ i (fun k => (s (Sum.inl k)).2) • pureA F (sliceR f xa) (g₂ i) := by
    funext x₂
    simp only [pureA, Pi.smul_apply, smul_eq_mul, sliceR_apply]
    have e : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F ((Sum.elim (s ∘ Sum.inl) x₂ : κ ⊕ κ' → AF F) k).1) =
        Sum.elim xa (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₂ k).1) := by
      funext k; cases k <;> rfl
    rw [e]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    ring
  rw [hfun, map_smul, hP i (sliceR f xa)]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pureA, hQ]
  simp only [Function.comp_def]
  ring

end GlobalTheory.TamePartR
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.ConjLoc

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def conjSchR (κ : Type) [Fintype κ] : SInf F κ →L[ℝ] SInf F κ :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem conjSchR_apply {κ : Type} [Fintype κ] (f : SInf F κ) (x : κ → mixedEmbedding.mixedSpace F) :
    conjSchR κ f x = starRingEnd ℂ (f x) := rfl

def conjSchCLM {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (T : SInf F κ →L[ℂ] SInf F κ₁) : SInf F κ →L[ℂ] SInf F κ₁ where
  toFun f := conjSchR κ₁ (T (conjSchR κ f))
  map_add' f g := by simp only [map_add (f := _)]
  map_smul' c f := by
    have h : conjSchR κ (c • f) = starRingEnd ℂ c • conjSchR κ f := by
      refine SchwartzMap.ext fun y => ?_; simp only [conjSchR_apply, SchwartzMap.smul_apply, smul_eq_mul, map_mul]
    refine SchwartzMap.ext fun x => ?_
    rw [h, map_smul, conjSchR_apply, RingHom.id_apply, SchwartzMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul,
      smul_eq_mul, map_mul, Complex.conj_conj, conjSchR_apply]
  cont := (conjSchR κ₁).continuous.comp (T.continuous.comp (conjSchR κ).continuous)

theorem conj_mem_SB {X : Type} [TopologicalSpace X] {φ : X → ℂ} (h : φ ∈ SB X) :
    (fun x => starRingEnd ℂ (φ x)) ∈ SB X :=
  ⟨h.1.comp (starRingEnd ℂ), h.2.comp_left (g := starRingEnd ℂ) (map_zero _)⟩

theorem conj_stdInd_apply (κ : Type) (v : Pl (F := F)) (y : κ → Fv F v) :
    starRingEnd ℂ (stdInd F κ v y) = stdInd F κ v y := by
  unfold stdInd
  by_cases hy : y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
  · rw [Set.indicator_of_mem hy, Pi.one_apply, map_one]
  · rw [Set.indicator_of_notMem hy, map_zero]

theorem conj_stdInd (κ : Type) (v : Pl (F := F)) :
    (fun y => starRingEnd ℂ (stdInd F κ v y)) = stdInd F κ v :=
  funext (conj_stdInd_apply κ v)

theorem conj_pure {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (x : κ → AF F) :
    starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (conjSchR κ f) (fun v y => starRingEnd ℂ (φ v y)) x := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, conjSchR_apply, map_mul]
  congr 1
  exact MulEquiv.map_finprod (starRingAut : ℂ ≃+* ℂ).toMulEquiv _

theorem isLocOp_conjLin {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ)
    (he : IsLocOp e) : IsLocOp (conjLin e) := by
  obtain ⟨ei, ev, hSB, hstd, hloc⟩ := he
  refine ⟨conjSchCLM ei, fun v => conjLin (ev v), fun v φ hφ => conj_mem_SB (hSB v _ (conj_mem_SB hφ)), ?_, ?_⟩
  · filter_upwards [hstd] with v hv
    funext y
    rw [conjLin_apply, conj_stdInd, hv, conj_stdInd_apply]
  · intro f φ hφ hfin
    funext y
    rw [conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x)) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (conjSchR κ f) (fun v y => starRingEnd ℂ (φ v y)) :=
      funext (conj_pure f φ)
    have hfin' : ∀ᶠ v in cofinite, (fun y => starRingEnd ℂ (φ v y)) = stdInd F κ v := by
      filter_upwards [hfin] with v hv
      rw [hv, conj_stdInd]
    rw [h1, hloc _ _ (fun v => conj_mem_SB (hφ v)) hfin', conj_pure]
    rfl

end GlobalTheory.DblEval.ConjLoc
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.BlockSwap

section Generic

variable {A : Type} {κ κ' κ₁' : Type}

def swapV (z : κ' ⊕ κ → A) : κ ⊕ κ' → A := z ∘ Sum.swap

theorem partR_eq_partL_swap (T : ((κ' → A) → ℂ) → (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) (y : κ ⊕ κ₁' → A) :
    partR T Φ y = partL T (fun z : κ' ⊕ κ → A => Φ (swapV z)) (swapV y) := by
  simp only [partR, partL, swapV]
  congr 1
  funext x
  congr 1
  funext i
  cases i <;> rfl

end Generic

section Adelic

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def swapCLE (M : Type) [NormedAddCommGroup M] [NormedSpace ℝ M] (κ κ' : Type) : (κ' ⊕ κ → M) ≃L[ℝ] (κ ⊕ κ' → M) :=
  { LinearEquiv.funCongrLeft ℝ M (Equiv.sumComm κ κ') with
    continuous_toFun := continuous_pi fun _ => continuous_apply _
    continuous_invFun := continuous_pi fun _ => continuous_apply _ }

def swapH (X : Type) [TopologicalSpace X] (κ κ' : Type) : (κ' ⊕ κ → X) ≃ₜ (κ ⊕ κ' → X) where
  toFun := swapV
  invFun := swapV
  left_inv z := by funext i; cases i <;> rfl
  right_inv z := by funext i; cases i <;> rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

theorem sb_swap {X : Type} [TopologicalSpace X] {κ κ' : Type} {g : (κ ⊕ κ' → X) → ℂ} (hg : g ∈ SB (κ ⊕ κ' → X)) :
    (fun z : κ' ⊕ κ → X => g (swapV z)) ∈ SB (κ' ⊕ κ → X) :=
  ⟨hg.1.comp_continuous (swapH X κ κ').continuous, hg.2.comp_homeomorph (swapH X κ κ')⟩

theorem partR_of_partL {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ)
    (hL : ∃ P : SInf F (κ' ⊕ κ) →L[ℂ] SInf F (κ₁' ⊕ κ), ∀ g ∈ SB (κ' ⊕ κ → Af F), ∃ g₁ ∈ SB (κ₁' ⊕ κ → Af F),
      ∀ f : SInf F (κ' ⊕ κ), partL e (pureA F f g) = pureA F (P f) g₁) :
    ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ ⊕ κ₁'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ ⊕ κ₁' → Af F),
      ∀ f : SInf F (κ ⊕ κ'), partR e (pureA F f g) = pureA F (P f) g₁ := by
  obtain ⟨PL, hPL⟩ := hL
  refine ⟨(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ₁' κ)).comp
    (PL.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ κ'))), fun g hg => ?_⟩
  obtain ⟨g₁, hg₁, h⟩ := hPL _ (sb_swap hg)
  refine ⟨fun w => g₁ (swapV w), sb_swap hg₁, fun f => ?_⟩
  funext y
  rw [partR_eq_partL_swap]
  have hpure : (fun z : κ' ⊕ κ → AF F => pureA F (⇑f) g (swapV z)) =
      pureA F (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ κ') f)) (fun w => g (swapV w)) := rfl
  rw [hpure, h]
  rfl

end Adelic

end GlobalTheory.DblEval.BlockSwap

end
end

section

noncomputable section

namespace GlobalTheory.IndLine

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def IsKFix (B : Base F E) (om : Rep σ Y W) (f : SInf F (Fin n × Fin d)) : Prop :=
  ∀ k ∈ KInf σ Y B.emb, Acts (evI F) (om (k, 1)) f f

def fixPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (m : ℕ) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Submodule.span ℂ {f | f ∈ fockDeg M B.ψ B.emb m ∧ IsKFix B om f}

def fixDeg (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) : ℕ :=
  sInf {m | ∃ f ∈ fockDeg M B.ψ B.emb m, f ≠ 0 ∧ IsKFix B om f}

def KStabUp (B : Base F E) (om : Rep σ Y W) (H : Submodule ℂ (SInf F (Fin n × Fin d))) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ f ∈ H, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ H

theorem fixPart_le_pol (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (m : ℕ) :
    fixPart B M om m ≤ M.Pol B.ψ B.emb :=
  Submodule.span_le.2 fun _ hf => fockDeg_le_pol M B.ψ B.emb m hf.1

theorem fixPart_eq_bot_of_lt (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {m : ℕ} (hm : m < fixDeg B M om) :
    fixPart B M om m = ⊥ := by
  rw [fixPart, Submodule.span_eq_bot]
  intro f hf
  by_contra h
  exact Nat.notMem_of_lt_sInf hm ⟨f, hf.1, h, hf.2⟩

end GlobalTheory.IndLine
end
end

section

open GlobalTheory.LKCount

namespace GlobalTheory.LKCount

variable {Γ G : Type} [Group Γ] [Group G]

noncomputable def doubleCosetToOrbit (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) :
    DoubleCoset.Quotient ((H.map ι : Subgroup G) : Set G) (K : Set G) →
      MulAction.orbitRel.Quotient H (LeftCosets ι K) :=
  Quotient.lift (fun x => (Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K x))) (by
    intro a b hab
    obtain ⟨_, ⟨h, hh, rfl⟩, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hab
    refine (Quotient.sound ?_).symm
    refine ⟨⟨h, hh⟩, ?_⟩
    show LeftCosets.mk ι K (ι h * a) = LeftCosets.mk ι K (ι h * a * k)
    rw [LeftCosets.mk_eq_mk]
    convert hk using 1
    group)

theorem doubleCosetToOrbit_mk (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) (x : G) :
    doubleCosetToOrbit ι H K (DoubleCoset.mk _ _ x) =
      Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K x) := rfl

theorem doubleCosetToOrbit_bijective (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) :
    Function.Bijective (doubleCosetToOrbit ι H K) := by
  constructor
  · intro p q hpq
    rw [← DoubleCoset.out_eq' p, ← DoubleCoset.out_eq' q] at hpq ⊢
    rw [doubleCosetToOrbit_mk, doubleCosetToOrbit_mk] at hpq
    obtain ⟨h, hh⟩ := Quotient.exact hpq
    have hh' : LeftCosets.mk ι K (ι (h : Γ) * q.out) = LeftCosets.mk ι K p.out := hh
    rw [LeftCosets.mk_eq_mk] at hh'
    refine ((@DoubleCoset.eq _ _ _ _ _ _).2 ⟨ι h, Subgroup.mem_map_of_mem ι h.2, _, hh', ?_⟩).symm
    group
  · intro o
    induction o using Quotient.inductionOn with
    | h y =>
      refine ⟨DoubleCoset.mk _ _ (LeftCosets.rep ι K y), ?_⟩
      rw [doubleCosetToOrbit_mk, LeftCosets.mk_rep]

theorem finsum_doubleCoset_eq_finsum_orbit {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (H : Subgroup Γ)
    (K : Subgroup G) (g : LeftCosets ι K → ℂ) (hg : ∀ h ∈ H, ∀ y : LeftCosets ι K, g (h • y) = g y) :
    ∑ᶠ q : DoubleCoset.Quotient ((H.map ι : Subgroup G) : Set G) (K : Set G), g (LeftCosets.mk ι K (Quotient.out q)) =
      ∑ᶠ o : MulAction.orbitRel.Quotient H (LeftCosets ι K), g (Quotient.out o) := by
  let e := Equiv.ofBijective _ (doubleCosetToOrbit_bijective ι H K)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  have hq : e q = Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K q.out) := by
    show doubleCosetToOrbit ι H K q = _
    conv_lhs => rw [← DoubleCoset.out_eq' q]
    rfl
  rw [hq]
  obtain ⟨h, hh⟩ := Quotient.exact (Quotient.out_eq
    (Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K q.out)))
  rw [← hh]
  exact (hg h h.2 _).symm

end GlobalTheory.LKCount
end
