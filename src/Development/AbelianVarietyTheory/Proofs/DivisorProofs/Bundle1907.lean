module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealAlgSep
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

namespace GlobalTheory.RatWeilOp

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def act {R κ : Type} [CommRing R] [Fintype κ] (a : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (w : (κ → R) × (κ → R)) : (κ → R) × (κ → R) :=
  ((a *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (a *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)

theorem act_mul {R κ : Type} [CommRing R] [Fintype κ] (a b : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (w : (κ → R) × (κ → R)) :
    act (a * b) w = act a (act b w) := by
  simp only [act, Matrix.mulVec_mulVec, Sum.elim_comp_inl_inr]

theorem act_fromBlocks {R κ : Type} [CommRing R] [Fintype κ] (A B C D : Matrix κ κ R) (w : (κ → R) × (κ → R)) :
    act (Matrix.fromBlocks A B C D) w = (A *ᵥ w.1 + B *ᵥ w.2, C *ᵥ w.1 + D *ᵥ w.2) := by
  simp only [act, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]

variable {F : Type} [Field F] [NumberField F]

def ind (κ : Type) (v : Pl F) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def IsFam {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (κ → Fv F v)) ∧ ∀ᶠ v in cofinite, φ v = ind κ v

def IsOp {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (c : ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ) : Prop :=
  c ≠ 0 ∧ Function.Surjective ei ∧
  (∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _)) ∧
  (∀ v (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) =
    schr (GlobalTheory.LatVac.psiAt ψ v) (act (a.map (algebraMap F (Fv F v))) w) (ev v φ)) ∧
  (∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v) ∧
  ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ →
    e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) (fun v => ev v (φ v)) ∧
    (∀ w : (κ → AF F) × (κ → AF F), e (schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
      schr ψ (act (a.map (algebraMap F (AF F))) w) (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))) ∧
    thetaSum F (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) = c * thetaSum F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)

def HasOp {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ e c ei ev, IsOp ψ a e c ei ev

theorem IsOp.isFam {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F} {e c ei ev}
    (h : IsOp ψ a e c ei ev) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) : IsFam fun v => ev v (φ v) := by
  obtain ⟨-, -, hbij, -, hind, -⟩ := h
  refine ⟨fun v => (hbij v).mapsTo (hφ.1 v), ?_⟩
  filter_upwards [hφ.2, hind] with v h1 h2
  rw [h1, h2]

theorem HasOp.mul {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a b : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (ha : HasOp ψ a) (hb : HasOp ψ b) : HasOp ψ (a * b) := by
  obtain ⟨e₁, c₁, ei₁, ev₁, h₁⟩ := ha
  obtain ⟨e₂, c₂, ei₂, ev₂, h₂⟩ := hb
  have h₂' := h₂
  obtain ⟨hc₁, hs₁, hb₁, hw₁, hi₁, hp₁⟩ := h₁
  obtain ⟨hc₂, hs₂, hb₂, hw₂, hi₂, hp₂⟩ := h₂
  refine ⟨e₁ ∘ₗ e₂, c₁ * c₂, ei₁.comp ei₂, fun v => ev₁ v ∘ₗ ev₂ v, mul_ne_zero hc₁ hc₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs₁.comp hs₂
  · intro v
    exact (hb₁ v).comp (hb₂ v)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hw₂ v w φ hφ, hw₁ v _ _ ((hb₂ v).mapsTo hφ), Matrix.map_mul, act_mul]
  · filter_upwards [hi₁, hi₂] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ
    have hφ' : IsFam fun v => ev₂ v (φ v) := IsOp.isFam h₂' hφ
    obtain ⟨hq₂, hw₂', ht₂⟩ := hp₂ f φ hφ
    obtain ⟨hq₁, hw₁', ht₁⟩ := hp₁ (ei₂ f) (fun v => ev₂ v (φ v)) hφ'
    refine ⟨?_, ?_, ?_⟩
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, hq₂, hq₁]
    · intro w
      simp only [LinearMap.comp_apply]
      rw [hw₂' w, hq₂, hw₁' _, Matrix.map_mul, act_mul]
    · simp only [LinearMap.comp_apply]
      rw [hq₂, ht₁, ← hq₂, ht₂, mul_assoc]

end GlobalTheory.RatWeilOp

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

def spAct {R : Type} [CommRing R] [Algebra F R] (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    (κ → R) × (κ → R) :=
  (fun k => (G.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) (Sum.inl k),
    fun k => (G.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) (Sum.inr k))

def weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 0 1 (-1) 0

def leviM (A : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks A 0 0 A⁻¹ᵀ

def unipM (S : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 1 0 S 1

def IsSymp (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop := G.transpose * weylM * G = weylM

def gens : Set (Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  {G | ∃ A : Matrix κ κ F, IsUnit A.det ∧ G = leviM A} ∪ {G | ∃ S : Matrix κ κ F, S.transpose = S ∧ G = unipM S} ∪ {weylM}

variable [NumberField F]

def indO (v : Pl (F := F)) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def HasOp (ψ : AddChar (AF F) ℂ) (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    Function.Surjective ei ∧ (∀ Φ ∈ schA F κ, e Φ ∈ schA F κ) ∧
    (∀ w, ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (spAct G w) (e Φ)) ∧
    (∀ v, (SB _).map (ev v) = SB _) ∧ (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0) ∧
    (∀ v w, ∀ φ ∈ SB (κ → Fv F v),
      ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (spAct G w) (ev v φ)) ∧
    (∀ᶠ v in cofinite, ev v (indO v) = indO v) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = indO v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)

end GlobalTheory.SympChange
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
namespace GlobalTheory.CptCoeff
open MeasureTheory Matrix ComplexConjugate

theorem mul_conj_polar (z w : ℂ) : z * conj w = (1 / 4 : ℂ) * ((((‖z + w‖ ^ 2 : ℝ) : ℂ) - ((‖z - w‖ ^ 2 : ℝ) : ℂ)) +
    Complex.I * (((‖z + Complex.I * w‖ ^ 2 : ℝ) : ℂ) - ((‖z - Complex.I * w‖ ^ 2 : ℝ) : ℂ))) := by
  have e : ∀ y : ℂ, (((‖y‖ ^ 2 : ℝ)) : ℂ) = y * conj y := fun y => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, e, e, e]
  simp only [map_add (f := _), map_sub, map_mul, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * (z * conj w - w * conj z) * Complex.I_sq

theorem integral_sq_norm {X : Type} [MeasurableSpace X] {μ : Measure X} {h : X → ℂ} (hh : MemLp h 2 μ) :
    ∫ x, (((‖h x‖ ^ 2 : ℝ)) : ℂ) ∂μ = (((∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  have hi : Integrable (fun x => ‖h x‖ ^ 2) μ := hh.integrable_norm_pow two_ne_zero
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    hi.aestronglyMeasurable]
  congr 3
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem integrable_sq_norm {X : Type} [MeasurableSpace X] {μ : Measure X} {h : X → ℂ} (hh : MemLp h 2 μ) :
    Integrable (fun x => (((‖h x‖ ^ 2 : ℝ)) : ℂ)) μ :=
  (hh.integrable_norm_pow two_ne_zero).ofReal

theorem integral_mul_conj {X : Type} [MeasurableSpace X] {μ : Measure X} {f g : X → ℂ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : ∫ x, f x * conj (g x) ∂μ = (1 / 4 : ℂ) *
      (((((∫⁻ x, ‖(f + g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) - (((∫⁻ x, ‖(f - g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ)) +
      Complex.I * ((((∫⁻ x, ‖(f + Complex.I • g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) -
        (((∫⁻ x, ‖(f - Complex.I • g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ))) := by
  have h1 := hf.add hg
  have h2 := hf.sub hg
  have h3 := hf.add (hg.const_smul Complex.I)
  have h4 := hf.sub (hg.const_smul Complex.I)
  rw [← integral_sq_norm h1, ← integral_sq_norm h2, ← integral_sq_norm h3, ← integral_sq_norm h4,
    ← integral_sub (integrable_sq_norm h1) (integrable_sq_norm h2),
    ← integral_sub (integrable_sq_norm h3) (integrable_sq_norm h4), ← integral_const_mul,
    ← integral_add, ← integral_const_mul]
  · congr 1
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_conj_polar (f x) (g x)
  · exact (integrable_sq_norm h1).sub (integrable_sq_norm h2)
  · exact ((integrable_sq_norm h3).sub (integrable_sq_norm h4)).const_mul _

theorem integral_mul_conj_map {X : Type} [MeasurableSpace X] {μ : Measure X} (P : Submodule ℂ (X → ℂ))
    (hP : ∀ f ∈ P, MemLp f 2 μ) (T : Module.End ℂ (X → ℂ)) (hT : ∀ f ∈ P, T f ∈ P)
    (hU : ∀ f ∈ P, ∫⁻ x, ‖T f x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) {f g : X → ℂ} (hf : f ∈ P) (hg : g ∈ P) :
    ∫ x, T f x * conj (T g x) ∂μ = ∫ x, f x * conj (g x) ∂μ := by
  rw [integral_mul_conj (hP _ (hT f hf)) (hP _ (hT g hg)), integral_mul_conj (hP f hf) (hP g hg),
    ← map_add, ← map_sub, ← map_smul, ← map_add, ← map_sub, hU _ (P.add_mem hf hg), hU _ (P.sub_mem hf hg),
    hU _ (P.add_mem hf (P.smul_mem _ hg)), hU _ (P.sub_mem hf (P.smul_mem _ hg))]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def infOne : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

theorem at_infOne : At (evI F) (infOne (F := F)) := by
  intro t ht
  have h1 : t.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact ht)
  refine Prod.ext ?_ ?_
  · change t.1 * 1 = 0
    rw [h1, zero_mul]
  · change t.2 * 0 = 0
    exact mul_zero _

theorem evFin_liftV_ne {v w : Pl (F := F)} (h : w ≠ v) (a : Fv F v) : evFin F w (GlobalTheory.LatVac.liftV v a) = 0 :=
  evalV_singleFin_ne h a

theorem mul_eq_zero_of_supp (S : Finset (Pl (F := F))) {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hI : ∀ t : AF F, At (evI F) t → t • A = 0) (hS : ∀ w ∈ S, ∀ t : AF F, At (evFin F w) t → t • A = 0)
    (u : Matrix (Fin n) (Fin k) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hu : ∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) : A * u = 0 := by
  classical
  set e : AF F := infOne + ∑ w ∈ S, GlobalTheory.LatVac.liftV w 1 with he
  have h1 : evI F (1 - e) = 0 := by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F (1 - e)) = 0
    have h0 : fstA F (infOne (F := F)) = 1 := rfl
    have hl : ∀ w : Pl (F := F), fstA F (GlobalTheory.LatVac.liftV w 1) = 0 := fun w => rfl
    have : fstA F (1 - e) = 0 := by

      rw [he, map_sub, map_one, map_add (f := _), map_sum, h0, Finset.sum_eq_zero fun w _ => hl w, add_zero, sub_self]
    rw [this, map_zero]
  have h2 : ∀ w ∈ S, evFin F w (1 - e) = 0 := by
    intro w hw

    rw [he, map_sub, map_one, map_add (f := _), map_sum]
    have h0 : evFin F w (infOne (F := F)) = 0 := by
      change evalV F w (sndA F infOne) = 0
      have : sndA F (infOne (F := F)) = 0 := rfl
      rw [this, map_zero]
    have hs : ∑ x ∈ S, evFin F w (GlobalTheory.LatVac.liftV x 1) = ∑ x ∈ S, if w = x then (1 : Fv F w) else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : w = x
      · subst hx; rw [if_pos rfl, GlobalTheory.LatVac.evFin_liftV]
      · rw [if_neg hx, evFin_liftV_ne hx]
    rw [h0, hs, Finset.sum_ite_eq S w (fun _ => (1 : Fv F w)), if_pos hw, zero_add, sub_self]
  have hue : u = e • u := by
    have := hu (1 - e) h1 h2
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have hA : e • A = 0 := by
    rw [he, add_smul, Finset.sum_smul, hI _ at_infOne, zero_add]
    exact Finset.sum_eq_zero fun w hw => hS w hw _ (GlobalTheory.LatVac.at_liftV w 1)
  rw [hue, Matrix.mul_smul, ← Matrix.smul_mul, hA, Matrix.zero_mul]

theorem matrix_coeff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) → (∀ u : AF F, At (evI F) u → u • (mat h - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat g - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat h - 1) = 0) →
    ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), ∀ u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    (∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) →
    ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (@MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x =>
          om' (g, h) Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u (om' (g, h) Φ) x)) =
        @MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x => Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u Φ x) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT S g h hgI hhI hgS hhS Φ hΦ u hu μ hμ
  letI : MeasurableSpace (Fin a' × Fin (a + a') → AF F) := borel _
  have hW := IsUWeilPair.isUSplitting hT.weil'
  have hg : mat g * u = u := by
    have := mul_eq_zero_of_supp S (mat g - 1) hgI hgS u hu
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have hh : u * (mat h)ᵀ = u := by
    have := mul_eq_zero_of_supp S (mat h - 1) hhI hhS uᵀ
      (fun t h1 h2 => by rw [← Matrix.transpose_smul, hu t h1 h2, Matrix.transpose_zero])
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    have := congrArg Matrix.transpose this
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at this
  have hact : actAB (cA σ) (g, h) u = u := by
    change mat g * u * (mat h)ᵀ = u
    rw [hg, hh]
  have hcomm : om' (g, h) (G.M'.co.rho B.ψ u Φ) = G.M'.co.rho B.ψ u (om' (g, h) Φ) := by
    rw [hW.impl (g, h) u Φ hΦ, hact]
  rw [← hcomm]
  exact integral_mul_conj_map (μ := μ) (schA F _) (fun f hf => GlobalTheory.T.adelic_schwartz_mem_L2 F _ μ hμ f hf) (om' (g, h))
    (fun f hf => hW.pres (g, h) f hf) (fun f hf => hW.unit μ hμ (g, h) f hf) hΦ
    (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std u Φ hΦ)

end GlobalTheory.CptCoeff

end
end

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchTrigBump

theorem exists_bounded_trig {X : Type} [PseudoMetricSpace X] [ProperSpace X] (x₀ : X) {B : Type} [AddCommGroup B]
    (χ : B → X → ℂ) (hc : ∀ b, Continuous (χ b)) (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (hzero : ∀ x, χ 0 x = 1) (hnorm : ∀ a x, ‖χ a x‖ = 1) (hsep : ∀ x y, x ≠ y → ∃ b, χ b x ≠ χ b y)
    (β : X → ℝ) (hβ : Continuous β) (h01 : ∀ u, 0 ≤ β u ∧ β u ≤ 1) :
    ∃ (s : ℕ → Finset B) (c : ℕ → B → ℂ), (∀ n x, ‖∑ b ∈ s n, c n b * χ b x‖ ≤ 2) ∧
      ∀ x, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * χ b x) Filter.atTop (nhds (β x : ℂ)) := by
  first
  | exact @_root_.GlobalTheory.RealAlgebraCharacters.main
  | exact _root_.GlobalTheory.RealAlgebraCharacters.main
  | (apply _root_.GlobalTheory.RealAlgebraCharacters.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RealAlgebraCharacters.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RealAlgebraCharacters.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RealAlgebraCharacters.main ..)

variable {F : Type} [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm


open scoped Classical in
theorem exists_trace_mul_ne_zero (u : mixedEmbedding.mixedSpace F) (hu : u ≠ 0) :
    ∃ w, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u * w) ≠ 0 := by
  let w : mixedEmbedding.mixedSpace F := (fun v => (u.1 v)⁻¹, fun v => (u.2 v)⁻¹)
  have h1 : u * w * u = u := by
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · change u.1 v * (u.1 v)⁻¹ * u.1 v = u.1 v
      exact mul_inv_mul_cancel _
    · change u.2 v * (u.2 v)⁻¹ * u.2 v = u.2 v
      exact mul_inv_mul_cancel _
  have h2 : IsIdempotentElem (u * w) := by
    change u * w * (u * w) = u * w
    rw [← mul_assoc, h1]
  refine ⟨w, fun h => hu ?_⟩
  rw [Algebra.trace_apply] at h
  have h3 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff
    (h2.map (Algebra.lmul ℝ (mixedEmbedding.mixedSpace F)))).1 h
  have h4 := LinearMap.congr_fun h3 u
  simp only [LinearMap.zero_apply] at h4
  rw [← h1]
  exact h4


open scoped Classical in
theorem exists_char_ne {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) (hxy : x ≠ y) :
    ∃ w : κ → mixedEmbedding.mixedSpace F,
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ w) : ℝ)) ≠
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ w) : ℝ)) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
  obtain ⟨w, hw⟩ := exists_trace_mul_ne_zero (x i - y i) (sub_ne_zero.2 hi)
  set t := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((x i - y i) * w) with ht
  refine ⟨Pi.single i ((2 * t)⁻¹ • w), fun h => ?_⟩
  rw [dotProduct_single, dotProduct_single] at h
  have h1 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y i * ((2 * t)⁻¹ • w)) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x i * ((2 * t)⁻¹ • w)) - 1 / 2 := by
    have : (2 * t)⁻¹ * t = 1 / 2 := by field_simp
    rw [← this, mul_smul_comm, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub]
    congr 1
    rw [ht, sub_mul, map_sub]
    ring
  rw [h1] at h
  generalize Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x i * ((2 * t)⁻¹ • w)) = a at h
  have h2 : -(2 * Real.pi * Complex.I) * ((a - 1 / 2 : ℝ) : ℂ) =
      -(2 * Real.pi * Complex.I) * (a : ℂ) + Real.pi * Complex.I := by
    push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_pi_mul_I] at h
  have h3 := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (a : ℂ))
  apply h3
  linear_combination h / 2

theorem arch_bump_trig : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (U : Set (κ → Ainf F)) (y : κ → AF F), IsOpen U → (fun i => (y i).1) ∈ U →
    ∃ β : (κ → Ainf F) → ℝ, Continuous β ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧ β (fun i => (y i).1) = 1 ∧
      (∀ u, β u ≠ 0 → u ∈ U) ∧
      ∃ (s : ℕ → Finset (κ → AF F)) (c : ℕ → (κ → AF F) → ℂ) (C : ℝ),
        (∀ n, ∀ b ∈ s n, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
        (∀ n (x : κ → AF F), ‖∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)‖ ≤ C) ∧
        ∀ x : κ → AF F, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) Filter.atTop
          (nhds ((β (fun i => (x i).1) : ℝ) : ℂ)) := by
  intro F _ _ κ _ ψ hψ U y hU hy
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let P : (κ → Ainf F) → κ → mixedEmbedding.mixedSpace F := fun u i => e (u i)
  let Q : (κ → mixedEmbedding.mixedSpace F) → κ → Ainf F := fun u i => e.symm (u i)
  have hP : Continuous P := continuous_pi fun i => continuous_toMixed.comp (continuous_apply i)
  have hQ : Continuous Q := continuous_pi fun i => continuous_ofMixed.comp (continuous_apply i)
  have hQP : ∀ u, Q (P u) = u := fun u => funext fun i => e.symm_apply_apply _
  have hU' : IsClosed (Q ⁻¹' U)ᶜ := (hU.preimage hQ).isClosed_compl
  obtain ⟨f, hf0, hf1, hf⟩ := exists_continuous_zero_one_of_isClosed hU'
    (isClosed_singleton (x := P fun i => (y i).1))
    (Set.disjoint_singleton_right.2 fun h => h (by rw [Set.mem_preimage, hQP]; exact hy))
  let χ : (κ → mixedEmbedding.mixedSpace F) → (κ → mixedEmbedding.mixedSpace F) → ℂ := fun w u =>
    Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u ⬝ᵥ w) : ℝ))
  have hT : Continuous (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) :=
    LinearMap.continuous_of_finiteDimensional _
  obtain ⟨s, c, hb, hl⟩ := exists_bounded_trig 0 χ
    (fun w => Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (hT.comp (continuous_id.dotProduct continuous_const)))))
    (fun a b x => by simp only [χ, dotProduct_add, map_add (f := _), Complex.ofReal_add, mul_add, Complex.exp_add])
    (fun x => by simp [χ])
    (fun a x => by simp [χ, Complex.norm_exp])
    exists_char_ne f f.continuous (fun u => hf u)
  let ι : (κ → mixedEmbedding.mixedSpace F) → κ → AF F := fun w i => ((e.symm (w i), 0) : Ainf F × Af F)
  let ρ : (κ → AF F) → κ → mixedEmbedding.mixedSpace F := fun b i => e (b i).1
  have hρ : ∀ w, ρ (ι w) = w := fun w => funext fun i => e.apply_symm_apply _
  have hι : Function.Injective ι := Function.LeftInverse.injective hρ
  have hchar : ∀ (x : κ → AF F) w, ψ (x ⬝ᵥ ι w) = χ w (P fun i => (x i).1) := by
    intro x w
    have h2 : (x ⬝ᵥ ι w).2 = 0 := by
      have := map_sum (RingHom.snd (Ainf F) (Af F)) (fun i => x i * ι w i) Finset.univ
      refine this.trans (Finset.sum_eq_zero fun i _ => ?_)
      exact mul_zero (x i).2
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x ⬝ᵥ ι w) = (P fun i => (x i).1) ⬝ᵥ w := by
      have := map_sum (e.toRingHom.comp (RingHom.fst (Ainf F) (Af F))) (fun i => x i * ι w i) Finset.univ
      refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
      change e ((x i).1 * e.symm (w i)) = _
      rw [map_mul, e.apply_symm_apply]
    rw [hψ.2.2, h1]
    intro u hu
    have hu1 : u.1 = 0 := e.injective (hu.trans (map_zero e).symm)
    refine Prod.ext ?_ ?_
    · change u.1 * (x ⬝ᵥ ι w).1 = 0
      rw [hu1, zero_mul]
    · change u.2 * (x ⬝ᵥ ι w).2 = 0
      rw [h2, mul_zero]
  have hsum : ∀ n (x : κ → AF F), ∑ b ∈ (s n).map ⟨ι, hι⟩, c n (ρ b) * ψ (x ⬝ᵥ b) =
      ∑ w ∈ s n, c n w * χ w (P fun i => (x i).1) := by
    intro n x
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Function.Embedding.coeFn_mk, hρ, hchar]
  refine ⟨fun u => f (P u), f.continuous.comp hP, fun u => hf _, hf1 rfl, fun u hu => ?_,
    fun n => (s n).map ⟨ι, hι⟩, fun n b => c n (ρ b), 2, ?_, fun n x => ?_, fun x => ?_⟩
  · by_contra h
    exact hu (hf0 (fun h' => h (by rwa [Set.mem_preimage, hQP] at h')))
  · intro n b hb v
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hb
    funext i
    refine Prod.ext ?_ ?_
    · exact zero_mul (e.symm (w i))
    · exact mul_zero (GlobalTheory.LatVac.liftV v 1).2
  · rw [hsum]; exact hb _ _
  · simp only [hsum]; exact hl _

end GlobalTheory.ArchTrigBump
end
