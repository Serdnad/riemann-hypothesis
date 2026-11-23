module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.SliceExt

noncomputable def splitPts (F : Type) [Field F] [NumberField F] (κ : Type) :
    (κ → AF F) ≃ (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  left_inv x := by
    funext i
    show (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1), (x i).2) : AF F) = x i
    rw [RingEquiv.symm_apply_apply]; rfl
  right_inv p := by
    refine Prod.ext ?_ rfl
    funext i
    exact RingEquiv.apply_symm_apply _ _


open scoped TensorProduct in
open NumberField MeasureTheory in
theorem _root_.GlobalTheory.SliceExt.exists_rep_pure (F : Type) [Field F] [NumberField F]
    (κ : Type) [Fintype κ]
    (G : Type) [Group G] (ρ : G →* (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →L[ℂ] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)) :
    ∃ ω₀ : G →* Module.End ℂ ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ), ∀ (g : G) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
      (h : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ),
      ω₀ g (_root_.GlobalTheory.WeilM.pureA F f h) = _root_.GlobalTheory.WeilM.pureA F (ρ g f) h := by
  classical
  let ι : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hι : Function.Injective ι := DFunLike.coe_injective
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range ι)
  let j := LinearEquiv.ofInjective ι hι
  let e := Submodule.prodEquivOfIsCompl _ C hC
  let A : G → Module.End ℂ ((κ → mixedEmbedding.mixedSpace F) → ℂ) := fun g =>
    e.toLinearMap ∘ₗ ((j.toLinearMap ∘ₗ (ρ g).toLinearMap ∘ₗ j.symm.toLinearMap).prodMap
      LinearMap.id) ∘ₗ e.symm.toLinearMap
  have hA1 : A 1 = 1 := by
    ext v
    simp [A]
  have hAmul : ∀ g h, A (g * h) = A g * A h := by
    intro g h
    ext v
    simp [A]
  have hAι : ∀ g f, A g (ι f) = ι (ρ g f) := by
    intro g f
    have : e.symm (ι f) = (j f, 0) := by
      rw [show ι f = ((j f : LinearMap.range ι) : _) from rfl]
      exact Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC _
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearMap.prodMap_apply,
      LinearEquiv.symm_apply_apply, map_zero, LinearMap.id_apply]
    rw [Submodule.coe_prodEquivOfIsCompl']
    simp [j]
  let s := _root_.GlobalTheory.SliceExt.splitPts F κ
  let slice : ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → (κ → mixedEmbedding.mixedSpace F) → ℂ :=
    fun Φ y a => Φ (s.symm (a, y))
  let W : G → Module.End ℂ ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) := fun g =>
    { toFun := fun Φ x => A g (slice Φ (s x).2) (s x).1
      map_add' := by
        intro Φ Ψ
        funext x
        have : slice (Φ + Ψ) (s x).2 = slice Φ (s x).2 + slice Ψ (s x).2 := rfl
        simp only [this, map_add (f := _), Pi.add_apply]
      map_smul' := by
        intro c Φ
        funext x
        have : slice (c • Φ) (s x).2 = c • slice Φ (s x).2 := rfl
        simp only [this, map_smul, Pi.smul_apply, RingHom.id_apply] }
  refine ⟨{ toFun := W, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext Φ x
    simp only [W, hA1, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply, slice,
      Prod.mk.eta, Equiv.symm_apply_apply]
  · intro g h
    ext Φ x
    simp only [W, hAmul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    have hsl : slice (fun x => A h (slice Φ (s x).2) (s x).1) (s x).2 = A h (slice Φ (s x).2) := by
      funext a
      simp only [slice, Equiv.apply_symm_apply]
    rw [hsl]
  · intro g f h
    funext x
    have hsl : ∀ (f' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ),
        slice (_root_.GlobalTheory.WeilM.pureA F f' h) (s x).2 = h (s x).2 • ι f' := by
      intro f'
      funext a
      have h1 := s.apply_symm_apply (a, (s x).2)
      simp only [slice, _root_.GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul]
      have ha : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (s.symm (a, (s x).2) i).1) = a :=
        congrArg Prod.fst h1
      have hy : (fun i => (s.symm (a, (s x).2) i).2) = (s x).2 := congrArg Prod.snd h1
      rw [ha, hy, mul_comm]
      rfl
    show A g (slice (_root_.GlobalTheory.WeilM.pureA F f h) (s x).2) (s x).1 = _
    rw [hsl, map_smul, hAι]
    simp only [Pi.smul_apply, smul_eq_mul, _root_.GlobalTheory.WeilM.pureA]
    rw [mul_comm]
    rfl

end GlobalTheory.SliceExt
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.DblEval

section Blocks

variable {A : Type} {κ κ₁ κ' κ₁' : Type}

def partL (T : ((κ → A) → ℂ) → (κ₁ → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) : (κ₁ ⊕ κ' → A) → ℂ :=
  fun y => T (fun x => Φ (Sum.elim x (y ∘ Sum.inr))) (y ∘ Sum.inl)

def partR (T : ((κ' → A) → ℂ) → (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) : (κ ⊕ κ₁' → A) → ℂ :=
  fun y => T (fun x => Φ (Sum.elim (y ∘ Sum.inl) x)) (y ∘ Sum.inr)

def partLₗ (e : ((κ → A) → ℂ) →ₗ[ℂ] (κ₁ → A) → ℂ) : ((κ ⊕ κ' → A) → ℂ) →ₗ[ℂ] (κ₁ ⊕ κ' → A) → ℂ where
  toFun := partL e
  map_add' Φ Ψ := funext fun y => by
    show e ((fun x => Φ _) + fun x => Ψ _) _ = _
    rw [map_add (f := _)]; rfl
  map_smul' c Φ := funext fun y => by
    show e (c • fun x => Φ _) _ = _
    rw [map_smul]; rfl

def partRₗ (e : ((κ' → A) → ℂ) →ₗ[ℂ] (κ₁' → A) → ℂ) : ((κ ⊕ κ' → A) → ℂ) →ₗ[ℂ] (κ ⊕ κ₁' → A) → ℂ where
  toFun := partR e
  map_add' Φ Ψ := funext fun y => by
    show e ((fun x => Φ _) + fun x => Ψ _) _ = _
    rw [map_add (f := _)]; rfl
  map_smul' c Φ := funext fun y => by
    show e (c • fun x => Φ _) _ = _
    rw [map_smul]; rfl

@[simp] theorem partLₗ_apply (e : ((κ → A) → ℂ) →ₗ[ℂ] (κ₁ → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) :
    partLₗ e Φ = partL e Φ := rfl

@[simp] theorem partRₗ_apply (e : ((κ' → A) → ℂ) →ₗ[ℂ] (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) :
    partRₗ e Φ = partR e Φ := rfl

end Blocks

def conjLin {X Y : Type} (e : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) : (X → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ y := starRingEnd ℂ (e (fun x => starRingEnd ℂ (φ x)) y)
  map_add' φ ψ := funext fun y => by
    have h : (fun x => starRingEnd ℂ (φ x + ψ x)) = (fun x => starRingEnd ℂ (φ x)) + fun x => starRingEnd ℂ (ψ x) :=
      funext fun x => map_add _ _ _
    simp only [Pi.add_apply]
    rw [h, map_add (f := _), Pi.add_apply, map_add (f := _)]
  map_smul' c φ := funext fun y => by
    have h : (fun x => starRingEnd ℂ (c * φ x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (φ x) :=
      funext fun x => by simp
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [h, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]

theorem conjLin_apply {X Y : Type} (e : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) (y : Y) :
    conjLin e φ y = starRingEnd ℂ (e (fun x => starRingEnd ℂ (φ x)) y) := rfl

section Loc

variable (F : Type) [Field F] [NumberField F]

def stdInd (κ : Type) (v : Pl (F := F)) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

variable {F}

def IsLocOp {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ) : Prop :=
  ∃ (ei : SInf F κ →L[ℂ] SInf F κ₁) (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ₁ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ₁ → Fv F v)) ∧
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ₁ v) ∧
    ∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

end Loc

end GlobalTheory.DblEval

end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


theorem realAd_mul (a b : ℝ) : realAd F a * realAd F b = realAd F (a * b) := by
  unfold realAd
  simp only [LinearMap.inl_apply, map_mul]
  refine Prod.ext ?_ ?_
  · show _ * _ = _
    rw [← map_mul]
  · exact mul_zero _

end GlobalTheory.ThetaDecay

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.EvZeroInf

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def finPart (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (x : κ → AF F) : ℂ :=
  ∏ᶠ v, φ v fun i => evFin F v (x i)

theorem pure_eq_tens (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    pure f φ = tens (evI F) (⇑f) (finPart φ) := rfl

theorem snd_eq_zero_of_at (z : κ → AF F) (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h0 : evI F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F 0 1) = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0
    exact map_zero _
  have h := congrArg Prod.snd (congrFun (hz _ h0) i)
  change (1 : Af F) * (z i).2 = 0 at h
  rwa [one_mul] at h

theorem finPart_add (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : At (evI F) z) :
    finPart φ (x + z) = finPart φ x := by
  unfold finPart
  refine finprod_congr fun v => ?_
  congr 1
  funext i
  have h : evFin F v (z i) = 0 := by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i).2 = 0
    rw [snd_eq_zero_of_at z hz i, map_zero]
  rw [Pi.add_apply, map_add (f := _), h, add_zero]

theorem exists_finPart_ne_zero (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ x₀ : κ → Af F, ∀ x : κ → AF F, (∀ i, (x i).2 = x₀ i) → finPart φ x ≠ 0 := by
  classical
  have hfin := Filter.eventually_cofinite.1 hstd
  set S := hfin.toFinset with hS
  have hy : ∀ v, ∃ y, φ v y ≠ 0 := fun v => by
    by_contra h
    push_neg at h
    exact h0 v (funext h)
  choose y hy using hy
  refine ⟨fun i => ∑ v ∈ S, singleFin v (y v i), fun x hx => ?_⟩
  have hev : ∀ w, (fun i => evFin F w (x i)) = if w ∈ S then y w else 0 := by
    intro w
    funext i
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (x i).2 = _

    rw [hx i, map_sum]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hw h),
        evalV_singleFin_self, if_pos hw]
    · rw [Finset.sum_eq_zero (fun v hv => evalV_singleFin_ne (fun h => hw (by rw [h]; exact hv)) _), if_neg hw]
      rfl
  have hne : ∀ w, φ w (fun i => evFin F w (x i)) ≠ 0 := by
    intro w
    by_cases hw : w ∈ S
    · rw [hev w, if_pos hw]; exact hy w
    · rw [hev w, if_neg hw]
      have hw' : φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
        by_contra h
        exact hw (by rw [hS, Set.Finite.mem_toFinset]; exact h)
      rw [hw', Set.indicator_of_mem (show (0 : κ → Fv F w) ∈ {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from
        fun i => zero_mem _)]
      exact one_ne_zero
  unfold finPart
  rw [finprod_def]
  split_ifs
  · exact Finset.prod_ne_zero_iff.2 fun w _ => hne w
  · exact one_ne_zero

theorem eq_of_pure_eq (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (g g' : SInf F κ) (h : pure g φ = pure g' φ) : g = g' := by
  obtain ⟨x₀, hx₀⟩ := exists_finPart_ne_zero φ h0 hstd
  refine DFunLike.ext g g' fun y => ?_
  let x : κ → AF F := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (x₀ i)
  have hI : (fun i => evI F (x i)) = y :=
    funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (y i)
  have e := congrFun h x
  change g (fun i => evI F (x i)) * finPart φ x = g' (fun i => evI F (x i)) * finPart φ x at e
  rw [hI] at e
  exact mul_right_cancel₀ (hx₀ x fun i => rfl) e

end GlobalTheory.EvZeroInf
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem piW_smul_incl (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : AF F) (e : E) :
    piW t (a • inclR (F := F) (AF F) e) = evFin F v a * t e := by
  simp [piW, inclR, compFin, TensorProduct.smul_tmul', splitProj_tmul]

theorem comp_mem_splitLat (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (hx : x ∈ L) : (fun i => t (x i)) ∈ splitLat t L := by
  refine ⟨_, tmul_mem_latLoc (one_mem _) hx, funext fun i => ?_⟩
  simp [splitVec, splitProj_tmul]

end GlobalTheory.LatInt

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem map_piW_gen (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : AF F) (x : Fin n → E) (y : Fin d → E) :
    (a • incM F (Matrix.vecMulVec x y)).map (piW t) =
      evFin F v a • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (y j)) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.smul_apply, incM, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [piW_smul_incl, map_mul]

theorem latAtV_comp_integral {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)) (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) :
    ∀ γ ∈ latAtV X W v, ∀ i j,
      ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) i j ∈ v.adicCompletionIntegers F := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, x, hx, y, hy, rfl⟩ := hz
    have hx' := (hb.mem_iff).1 (comp_mem_splitLat v t hx)
    have hy' := (hc.mem_iff).1 (comp_mem_splitLat v t hy)
    intro i j
    rw [map_piW_gen, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    exact mul_mem ha (mul_mem (hx' i) (hy' j))
  | zero => intro i j; simp
  | add γ δ _ _ hγ hδ =>
    intro i j
    rw [Matrix.map_add (piW t) (map_add _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    exact add_mem (hγ i j) (hδ i j)
  | neg γ _ hγ =>
    intro i j
    rw [Matrix.map_neg (piW t) (map_neg _), Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
    exact neg_mem (hγ i j)

end GlobalTheory.LatInt
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.GramDet

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  set A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm with hA'
  have key : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]
    ext i j
    simp [hA', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
  intro h0
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁] at hd
  simp [Matrix.det_neg] at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

theorem det_ne_zero_of_map {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) {J : Matrix (Fin n) (Fin n) K}
    (h : (J.map φ).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem gram_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    G.V'.J.det ≠ 0 ∧ G.W.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨det_ne_zero_of_map (B.emb w).1 (det_ne_zero_of_hasSig (hT.geo.hV'.sig w)), ?_⟩
  refine det_ne_zero_of_map (B.emb w).1 ?_
  have h := det_ne_zero_of_hasSig (hT.geo.hW.sig w)
  rw [Matrix.det_smul] at h
  intro h0
  exact h (by rw [h0, mul_zero])

end GlobalTheory.GramDet
end

section

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.VacLine

variable {F : Type} [Field F] [NumberField F]

theorem at_latAtV {E : Type} [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {v : Pl (F := F)} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    At (evFin F v) γ := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
    intro u hu
    rw [← smul_assoc, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add z z' _ _ hz hz' => intro u hu; rw [smul_add, hz u hu, hz' u hu, add_zero]
  | neg z _ hz => intro u hu; rw [smul_neg, hz u hu, neg_zero]

end GlobalTheory.VacLine
end
end

section

open NumberField IsDedekindDomain
open scoped Matrix

theorem _root_.GlobalTheory.T.selfDualLattice_inverseGram_localBasis_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (w : HeightOneSpectrum (𝓞 E)), (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J y x))) → ∀ (X : Matrix (Fin n) (Fin n) E), IsUnit X.det → IsUnit (Xᵀ * J * X.map σ).det → (∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) → ∀ (s : 𝓞 E), s ∉ w.asIdeal → (∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r) → ∀ (e : E), (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) → ∀ i k, w.valuation E (e * (Xᵀ * J * X.map σ)⁻¹ i k) ≤ 1 := by
  first | exact @GlobalTheory.selfDual_inv_gram_integral | exact GlobalTheory.selfDual_inv_gram_integral | (intros; apply GlobalTheory.selfDual_inv_gram_integral <;> assumption)
end
