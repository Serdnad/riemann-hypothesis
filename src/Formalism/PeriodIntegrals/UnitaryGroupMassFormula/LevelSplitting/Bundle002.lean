module

public import Formalism.PeriodIntegrals.Bundle018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.LevelKSplit.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def SplitK : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ∀ ΛX ΛW ΛY : Set (Fin M → E), Adapted F E σ M J P ΛX ΛW ΛY →
    ∀ m h : HA (Af F) σ J, m ∈ Nsub (Af F) σ J P → h ∈ Hsub (Af F) σ J P →
      m * h ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY) → h ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)

end Ext

section ExtN

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def ExistS : Prop :=
  ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ∀ μN : Measure (Nsub (Af F) σ J P), μN.IsHaarMeasure →
    ∀ μH : Measure (Hsub (Af F) σ J P), μH.IsHaarMeasure →
    ∃ μS : Measure (Ssub (Af F) σ J P), μS.IsHaarMeasure ∧
      IsProdNH F E σ M J (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P) μS μN μH

def MeasKf : Prop :=
  ∀ Λ : Set (Fin M → E), MeasurableSet (Kf σ J Λ : Set (HA (Af F) σ J))

variable {F E σ M J}

theorem levelS_of (hinv : ∀ x, σ (σ x) = x) (hEx : ExistS F E σ M J) (hMe : MeasKf F E σ M J) (hSp : SplitK F E σ M J) :
    LevelS F E σ M J := by
  intro hJ r P T hP ΛX ΛW ΛY hA μN hμN μH hμH
  refine ⟨hEx r P T hP μN hμN μH hμH, ?_⟩
  rintro μS ⟨-, hprod⟩
  have hKm : MeasurableSet (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := hMe _
  have key := hprod ((Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1)
    (measurable_one.indicator hKm)
  have hS : {s : Ssub (Af F) σ J P | (s : HA (Af F) σ J) ∈ KS σ J P (ΛX ∪ ΛW ∪ ΛY)} =
      Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := by
    ext s
    show (s : HA (Af F) σ J) ∈ Ssub (Af F) σ J P ⊓ Kf σ J (ΛX ∪ ΛW ∪ ΛY) ↔
      (s : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    rw [Subgroup.mem_inf]
    exact ⟨And.right, fun h => ⟨s.2, h⟩⟩
  have hN : {m : Nsub (Af F) σ J P | (m : HA (Af F) σ J) ∈ NO σ J P (ΛX ∪ ΛW ∪ ΛY)} =
      Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := by
    ext s
    show (s : HA (Af F) σ J) ∈ Nsub (Af F) σ J P ⊓ Kf σ J (ΛX ∪ ΛW ∪ ΛY) ↔
      (s : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    rw [Subgroup.mem_inf]
    exact ⟨And.right, fun h => ⟨s.2, h⟩⟩
  have hH : {m : Hsub (Af F) σ J P | (m : HA (Af F) σ J) ∈ KH σ J P (ΛX ∪ ΛW ∪ ΛY)} =
      Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := by
    ext s
    show (s : HA (Af F) σ J) ∈ Hsub (Af F) σ J P ⊓ Kf σ J (ΛX ∪ ΛW ∪ ΛY) ↔
      (s : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    rw [Subgroup.mem_inf]
    exact ⟨And.right, fun h => ⟨s.2, h⟩⟩
  rw [hS, hN, hH]
  have hL : ∫⁻ k, (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1
      (k : HA (Af F) σ J) ∂μS = μS (Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J))) := by
    rw [← lintegral_indicator_one (measurable_subtype_coe hKm)]
    congr 1
  have inner : ∀ m : Nsub (Af F) σ J P,
      ∫⁻ h, (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1
        ((m : HA (Af F) σ J) * (h : HA (Af F) σ J)) ∂μH =
      (Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J))).indicator
        (fun _ => μH (Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)))) m := by
    intro m
    by_cases hm : (m : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    · rw [Set.indicator_of_mem (show m ∈ Subtype.val ⁻¹'
          (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hm),
        ← lintegral_indicator_one (measurable_subtype_coe hKm)]
      congr 1
      funext h
      by_cases hh : (h : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
      · simp only [Set.indicator_of_mem (show (m : HA (Af F) σ J) * (h : HA (Af F) σ J) ∈
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from (Kf σ J _).mul_mem hm hh),
          Set.indicator_of_mem (show h ∈ Subtype.val ⁻¹'
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hh), Pi.one_apply]
      · rw [Set.indicator_of_notMem (show (m : HA (Af F) σ J) * (h : HA (Af F) σ J) ∉
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from
              fun hmh => hh (hSp hJ hinv r P T hP ΛX ΛW ΛY hA m h m.2 h.2 hmh)),
          Set.indicator_of_notMem (show h ∉ Subtype.val ⁻¹'
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hh)]
    · rw [Set.indicator_of_notMem (show m ∉ Subtype.val ⁻¹'
          (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hm)]
      have hz : ∀ h : Hsub (Af F) σ J P, (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1
          ((m : HA (Af F) σ J) * (h : HA (Af F) σ J)) = (0 : ENNReal) := by
        intro h
        refine Set.indicator_of_notMem (fun hmh => hm ?_) _
        have hh := hSp hJ hinv r P T hP ΛX ΛW ΛY hA m h m.2 h.2 hmh
        have h2 := (Kf σ J (ΛX ∪ ΛW ∪ ΛY)).mul_mem hmh ((Kf σ J (ΛX ∪ ΛW ∪ ΛY)).inv_mem hh)
        rwa [mul_inv_cancel_right] at h2
      simp only [hz, lintegral_zero]
  rw [hL, lintegral_congr inner, lintegral_indicator_const (measurable_subtype_coe hKm)] at key
  rw [key, mul_comm]

end ExtN

def ExistSAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ExistS F E σ M J

def MeasKfAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      MeasKf F E σ M J

def SplitKAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => SplitK F E σ M J

theorem sig_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]

theorem levelSAll_of (h1 : ExistSAll) (h2 : MeasKfAll) (h3 : SplitKAll) : LevelSAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact levelS_of (sig_invol hσ) (h1 F E σ hσ M J hJ) (h2 F E σ hσ M J hJ) (h3 F E σ hσ M J hJ)

end PI.LevelKSplit.W
end
end

section

noncomputable section

namespace PI.LevelKSplit.W.CD

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def ModV : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ g : HA (Af F) σ J,
    ∀ μ : Measure (Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
      μ.map (lin (Af F) σ J g) = μ

end Ext

def ModVAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => ModV F E σ M J

end PI.LevelKSplit.W.CD
end
end

section

noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem cancel_prod {X Y : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (ν : Measure X) [ν.IsAddHaarMeasure] [SFinite ν] (a b : Measure Y) [SFinite a] [SFinite b]
    (h : ν.prod a = ν.prod b) : a = b := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : X)
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have hinf : ν K ≠ ⊤ := hK.measure_lt_top.ne
  ext s hs
  have h1 := congrArg (fun m => m (K ×ˢ s)) h
  simp only [Measure.prod_prod] at h1
  exact (ENNReal.mul_right_inj h0 hinf).1 h1

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem continuous_crd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (crd (F := F) (E := E) R) := by
  first
  | exact continuous_induced_dom
  | exact IsModuleTopology.continuous_of_linearMap (crd (F := F) (E := E) R).toLinearMap
  | fun_prop
  | (delta crd; exact LinearMap.continuous_of_finiteDimensional _)

theorem continuous_crd_symm (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (crd (F := F) (E := E) R).symm := by
  first
  | exact continuous_induced_rng.2 (by simpa [Function.comp_def] using continuous_id)
  | exact IsModuleTopology.continuous_of_linearMap (crd (F := F) (E := E) R).symm.toLinearMap
  | fun_prop

variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [TopologicalSpace R2] [IsTopologicalRing R2]

theorem continuous_first_orbit_map : Continuous (p1 (F := F) (E := E) R1 R2) := by
  have key : ∀ x, p1 (F := F) (E := E) R1 R2 x =
      (crd (F := F) (E := E) R1).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).1) := by
    intro x
    apply (crd (F := F) (E := E) R1).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp [crd, p1, Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, Prod.fst_add, hx, hy]
  rw [show p1 (F := F) (E := E) R1 R2 = fun x =>
      (crd (F := F) (E := E) R1).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).1) from funext key]
  exact (continuous_crd_symm R1).comp
    (continuous_pi fun i => continuous_fst.comp ((continuous_apply i).comp (continuous_crd (R1 × R2))))

theorem continuous_p2 : Continuous (p2 (F := F) (E := E) R1 R2) := by
  have key : ∀ x, p2 (F := F) (E := E) R1 R2 x =
      (crd (F := F) (E := E) R2).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).2) := by
    intro x
    apply (crd (F := F) (E := E) R2).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp [crd, p2, Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, Prod.snd_add, hx, hy]
  rw [show p2 (F := F) (E := E) R1 R2 = fun x =>
      (crd (F := F) (E := E) R2).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).2) from funext key]
  exact (continuous_crd_symm R2).comp
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_crd (R1 × R2))))

theorem continuous_qq :
    Continuous (fun y : (R1 ⊗[F] E) × (R2 ⊗[F] E) => qq R1 R2 y.1 y.2) := by
  delta qq
  exact (continuous_crd_symm (R1 × R2)).comp (continuous_pi fun k =>
    (((continuous_apply k).comp (continuous_crd R1)).comp continuous_fst).prodMk
      (((continuous_apply k).comp (continuous_crd R2)).comp continuous_snd))

variable {M : ℕ}

theorem continuous_psiE : Continuous (psiE (F := F) (E := E) (M := M) R1 R2) := by
  show Continuous (fun x : Fin M → (R1 × R2) ⊗[F] E =>
    (fun i => p1 (F := F) (E := E) R1 R2 (x i), fun i => p2 (F := F) (E := E) R1 R2 (x i)))
  exact (continuous_pi fun i => (continuous_first_orbit_map R1 R2).comp (continuous_apply i)).prodMk
    (continuous_pi fun i => (continuous_p2 R1 R2).comp (continuous_apply i))



theorem continuous_qqv :
    Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) => fun i => qq R1 R2 (y.1 i) (y.2 i)) := by
  refine continuous_pi fun i => ?_
  have h1 : Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) => (y.1 i, y.2 i)) :=
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
  have h2 := (continuous_qq R1 R2).comp h1
  simpa only [Function.comp_def] using h2


theorem continuous_psiE_symm : Continuous (psiE (F := F) (E := E) (M := M) R1 R2).symm := by
  show Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) =>
    fun i => qq R1 R2 (y.1 i) (y.2 i))
  exact continuous_qqv R1 R2

theorem continuous_lin (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) :
    Continuous (lin R σ J g) := by
  first
  | exact IsModuleTopology.continuous_of_linearMap ((lin R σ J g).restrictScalars R)
  | exact Continuous.matrix_mulVec continuous_const continuous_id
  | (delta lin; fun_prop)

end Top

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [LocallyCompactSpace R1] [T2Space R1]
  [SecondCountableTopology R1]
  [TopologicalSpace R2] [IsTopologicalRing R2] [LocallyCompactSpace R2] [T2Space R2]
  [SecondCountableTopology R2]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem pres_snd
    (hV : ∀ (g : HA (R1 × R2) σ J) (ν : Measure (Fin M → (R1 × R2) ⊗[F] E)),
      ν.IsAddHaarMeasure → ν.map (lin (R1 × R2) σ J g) = ν)
    (g : HA R2 σ J) (μ : Measure (Fin M → R2 ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (lin R2 σ J g) = μ := by
  let ν1 : Measure (Fin M → R1 ⊗[F] E) := Measure.addHaar
  let e := psiE (F := F) (E := E) (M := M) R1 R2
  have hc : Continuous e := continuous_psiE R1 R2
  have hcs : Continuous e.symm := continuous_psiE_symm R1 R2
  let P0 : Measure ((Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E)) := ν1.prod μ
  have : P0.IsAddHaarMeasure := inferInstance
  let P : Measure (Fin M → (R1 × R2) ⊗[F] E) := P0.map e.symm
  have : P.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map P0 hcs hc
  have hP := hV (lift R1 R2 σ J g) P inferInstance
  have hl1 := continuous_lin (R1 × R2) σ J (lift R1 R2 σ J g)
  have hl2 := continuous_lin R2 σ J g
  have hPe : P.map e = P0 := by
    rw [Measure.map_map hc.measurable hcs.measurable]
    have : (e ∘ e.symm) = id := funext e.apply_symm_apply
    rw [this, Measure.map_id]
  have key : P0.map (Prod.map id (lin R2 σ J g)) = P0 := by
    have h1 : (Prod.map id (lin R2 σ J g)) ∘ e = e ∘ (lin (R1 × R2) σ J (lift R1 R2 σ J g)) := by
      funext x
      exact (psi_lin R1 R2 σ J g x).symm
    calc P0.map (Prod.map id (lin R2 σ J g))
        = (P.map e).map (Prod.map id (lin R2 σ J g)) := by rw [hPe]
      _ = P.map ((Prod.map id (lin R2 σ J g)) ∘ e) :=
          Measure.map_map (measurable_id.prodMap hl2.measurable) hc.measurable
      _ = P.map (e ∘ (lin (R1 × R2) σ J (lift R1 R2 σ J g))) := by rw [h1]
      _ = (P.map (lin (R1 × R2) σ J (lift R1 R2 σ J g))).map e :=
          (Measure.map_map hc.measurable hl1.measurable).symm
      _ = P0 := by rw [hP, hPe]
  rw [← Measure.map_prod_map ν1 μ measurable_id hl2.measurable, Measure.map_id] at key
  exact (cancel_prod ν1 _ _ key).symm ▸ rfl

end Meas

end PI.LevelKSplit.W.MVA
end
end

section

noncomputable section

namespace PI.LevelKSplit.W.Cont

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

def phiV (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)

theorem phiV_smul (v : HeightOneSpectrum (𝓞 F)) (a : Af F) (x : Af F ⊗[F] E) :
    phiV (E := E) v (a • x) = evalV F v a • phiV v x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1

def phiSL (v : HeightOneSpectrum (𝓞 F)) :
    Af F ⊗[F] E →ₛₗ[(evalV F v).toRingHom] Fv F v ⊗[F] E where
  toFun := phiV v
  map_add' := map_add _
  map_smul' := fun a x => phiV_smul v a x

theorem continuous_phiV (v : HeightOneSpectrum (𝓞 F)) : Continuous (phiV (E := E) v) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  have : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
  exact IsModuleTopology.continuous_of_linearMapₛₗ (continuous_evalV v) (phiSL v)

end

theorem continuous_at_place : PI.LevelKSplit.W.Meas.ContPlace := by
  intro F E _ _ _ _ _ σ n J v
  have h1 : Continuous (fun g : HA (Af F) σ J => (incAf σ J g : GL (Fin n) (Af F ⊗[F] E))) :=
    continuous_subtype_val
  have h2 : Continuous (fun g : HA (Af F) σ J =>
      ((incAf σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) :=
    Units.continuous_val.comp h1
  refine (h2.matrix_map (continuous_phiV (E := E) v)).congr ?_
  intro g
  rfl

end PI.LevelKSplit.W.Cont
end
end
