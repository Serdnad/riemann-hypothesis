module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle005
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LeviEmbeddingBlock32

@[expose] public section

section

noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem latImage (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hfg : L.FG) :
    ∃ (m : ℕ) (b : Fin m → (Fin n → Fv F v ⊗[F] E)),
      (∀ i, b i ∈ latLoc (E := E) v (L : Set (Fin n → E))) ∧
      Submodule.span (Fv F v) (Set.range b) = ⊤ ∧
      (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
        (fun c : Fin m → Fv F v => ∑ i, c i • b i) ''
          Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hfg.restrictScalars (R := ℤ))
  have hsL : ∀ i, s i ∈ L := fun i => by
    have : s i ∈ Submodule.span ℤ (Set.range s) := Submodule.subset_span ⟨i, rfl⟩
    rw [hs] at this; exact this
  set b : Fin m → (Fin n → Fv F v ⊗[F] E) := fun i => ratV (F := F) (Fv F v) (s i) with hb
  have hlat : latLoc (E := E) v (L : Set (Fin n → E)) =
      Submodule.span (v.adicCompletionIntegers F) (Set.range b) := by
    apply le_antisymm
    · unfold latLoc
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => rw [ratV_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [ratV_add]; exact add_mem hx hy
      | smul k x _ hx => rw [ratV_zsmul]; exact zsmul_mem hx k
    · unfold latLoc
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨s i, hsL i, rfl⟩
  have hbΛ : ∀ i, b i ∈ latLoc (E := E) v (L : Set (Fin n → E)) := fun i => by
    rw [hlat]; exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨m, b, hbΛ, ?_, ?_⟩
  · rw [eq_top_iff, ← spanTop v L hL, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have : ratV (F := F) (Fv F v) x ∈ latLoc (E := E) v (L : Set (Fin n → E)) :=
      Submodule.subset_span ⟨x, hx, rfl⟩
    rw [hlat] at this
    exact Submodule.span_le_restrictScalars (v.adicCompletionIntegers F) (Fv F v) _ this
  · ext x
    rw [SetLike.mem_coe, hlat, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨fun i => ⟨d i, hd i (Set.mem_univ _)⟩, rfl⟩

theorem latOpenCompact (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsOpen (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) ∧
      IsCompact (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  obtain ⟨m, b, -, hsp, heq⟩ := latImage v L hL hfg
  let Φ : (Fin m → Fv F v) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun c => ∑ i, c i • b i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [Φ, Pi.single_apply]
  have himg : (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
      Φ '' Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := heq
  rw [himg]
  refine ⟨IsModuleTopology.isOpenMap_of_surjective hsurj _
    (isOpen_set_pi Set.finite_univ fun i _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v), ?_⟩
  exact (isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image
    (IsModuleTopology.continuous_of_linearMap Φ)

end MassDataIdxK
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

theorem imA_vecV_add' (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a + b) = PI.FinKW.vecV X.B.I v a + PI.FinKW.vecV X.B.I v b := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_vecV_zero' (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    PI.FinKW.vecV X.B.I v (0 : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) = 0 := by
  funext i; simp [PI.FinKW.vecV]

theorem scalarAt_one_mem_integralAdeles (p : TypX X) : scP X p 1 ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  have h := scalarAt_mem_integralAdeles X p 1
  simpa using h

theorem imA_lift_sp (p : TypX X) (S : Set (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
    {a : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (ha : a ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F)
      {w | ∃ t ∈ OEp X p, ∃ s ∈ PI.FinKW.vecV X.B.I p.1 '' S, w = t • s}) :
    ∃ A ∈ Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S, PI.FinKW.vecV X.B.I p.1 A = a ∧
      ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v A = 0 := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ⟨τ, hτ, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩ := hx
    refine ⟨(scP X p 1 * τ) • s, ?_, ?_, ?_⟩
    · exact Submodule.smul_mem _
        (⟨scP X p 1 * τ, Subring.mul_mem _ (scalarAt_one_mem_integralAdeles X p) hτ⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
        (Submodule.subset_span hs)
    · rw [imA_vecV_smul', map_mul, component_scalarAt_same, map_one, one_mul]
    · intro v hv
      rw [imA_vecV_smul', map_mul, component_scalarAt_of_ne X p v hv, zero_mul, zero_smul]
  | zero => exact ⟨0, zero_mem _, imA_vecV_zero' X p.1, fun v _ => imA_vecV_zero' X v⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    obtain ⟨B, hB, h3, h4⟩ := hy
    exact ⟨A + B, add_mem hA hB, by rw [imA_vecV_add', h1, h3],
      fun v hv => by rw [imA_vecV_add', h2 v hv, h4 v hv, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    refine ⟨scP X p c • A, Submodule.smul_mem _
      (⟨_, scalarAt_mem_integralAdeles X p c⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hA, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, h1, imA_smul_alg]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]

theorem imA_lift_lat (p : TypX X) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ∃ A ∈ X.B.I.Lf, PI.FinKW.vecV X.B.I p.1 A = u ∧ ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v A = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hin : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) ∈ X.B.I.Lf :=
      Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
    refine ⟨scP X p 1 • (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)),
      Submodule.smul_mem _ (⟨_, scalarAt_one_mem_integralAdeles X p⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hin, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, map_one, one_smul]
      funext i
      simp [PI.FinKW.vecV, PI.FinKW.psiV, Formalism.UG.inclE, ratV, inclR]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]
  | zero => exact ⟨0, zero_mem _, imA_vecV_zero' X p.1, fun v _ => imA_vecV_zero' X v⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    obtain ⟨B, hB, h3, h4⟩ := hy
    exact ⟨A + B, add_mem hA hB, by rw [imA_vecV_add', h1, h3],
      fun v hv => by rw [imA_vecV_add', h2 v hv, h4 v hv, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    refine ⟨scP X p c • A, Submodule.smul_mem _
      (⟨_, scalarAt_mem_integralAdeles X p c⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hA, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, h1, imA_smul_alg]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped ENNReal

theorem massDataIndices_of (hA : MeasAAll) (hB : MeasBAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hX p
  obtain ⟨i, hi, hi0, hμi⟩ := hA X hb hK FdN FdN' u u' hX p
  obtain ⟨j, hj, hj0, hμj, hB0, hBt⟩ := hB X hb hK FdN FdN' u u' hX p
  refine ⟨?_, ?_⟩
  · show (X.measG.μGv p.1 (KvX X p)).toReal =
      (ggC D.R.rS D.R.k (gOf p) : ℝ) / ((nnC D.R.rS D.R.k (gOf p) : ℝ) * (ukC D.R.k (gOf p) : ℝ)) *
        (X.measG.μGv p.1 (KppX X hb p)).toReal
    have h1 : (muP X p (KvX X p)).toReal = (i : ℝ) * (muP X p (KppX X hb p)).toReal := by
      rw [hμi, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    rw [← hi, mul_div_assoc, div_self hi0, mul_one]
    exact h1
  · show (X.measG.μGv p.1 (KnatX X u p)).toReal / (X.measG.μGv p.1 (KvX X p)).toReal =
      (glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ) / (ggC D.R.rS D.R.k (gOf p) : ℝ)
    have h1 : (muP X p (KvX X p)).toReal = (j : ℝ) * (muP X p (KnatX X u p)).toReal := by
      rw [hμj, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    have hpos : (muP X p (KnatX X u p)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hB0, hBt⟩
    show (muP X p (KnatX X u p)).toReal / (muP X p (KvX X p)).toReal = _
    rw [h1, ← hj]
    rcases eq_or_ne (j : ℝ) 0 with h0 | h0
    · simp [h0]
    · rw [mul_comm (j : ℝ) (muP X p (KnatX X u p)).toReal, mul_comm (j : ℝ), div_mul_eq_div_div,
        div_self hpos, div_mul_eq_div_div, div_self hj0]

def LocAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X,
      StTop X p ∧ StK X p ∧ StRed X p ∧ StImA X hb p ∧ StImB X u p

theorem massDataIndices_of_haarIdx_redIdx_locAll (hH : HaarIdx) (hR : RedIdx) (hL : LocAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A :=
  massDataIndices_of
    (fun X hb hK FdN FdN' u u' hX p =>
      let h := hL X hb hK FdN FdN' u u' hX p
      measA_of X hb hH hR p h.1 h.2.1 h.2.2.1 h.2.2.2.1)
    (fun X hb hK FdN FdN' u u' hX p =>
      let h := hL X hb hK FdN FdN' u u' hX p
      measB_of X hH hR u p h.1 h.2.1 h.2.2.1 h.2.2.2.2)

theorem massDataIndices_of_locAll (hL : LocAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  have hH : HaarIdx := by
    exact haarIdx
  have hR : RedIdx := by
    exact redIdx
  intro D X
  exact massDataIndices_of_haarIdx_redIdx_locAll hH hR hL X

def LocOpen : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X,
      StK X p ∧ StRed X p ∧ StImA X hb p ∧ StImB X u p

theorem massDataIndices_of_locOpen (hL : LocOpen) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  exact massDataIndices_of_locAll (fun X hb hK FdN FdN' u u' hX p => ⟨stTop X p, hL X hb hK FdN FdN' u u' hX p⟩)

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni)

section Span

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_span_single (s : Set ι) (v : ι → K) :
    v ∈ Submodule.span K ((fun j => Pi.single j (1 : K)) '' s) ↔ ∀ i, i ∉ s → v i = 0 := by
  classical
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro i hi
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      simp [Pi.single_apply, hij]
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul a x _ hx => intro i hi; simp [hx i hi]
  · intro h
    have hv : v = ∑ i, v i • Pi.single i (1 : K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases hi : i ∈ s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · simp [h i hi]

end Span

variable {K : Type} [Field K] {r k : ℕ}

def pe (b : Fin (r + 1)) : Idx r k := if h : (b : ℕ) < r then Sum.inl ⟨b, h⟩ else zI

def ColFlag (m : Matrix (Idx r k) (Idx r k) K) : Prop :=
  ∀ b : Fin (r + 1), m *ᵥ Pi.single (pe b) 1 - Pi.single (pe b) 1 ∈
    Submodule.span K ((fun a => Pi.single (pe (k := k) a) (1 : K)) '' {a | a < b})

theorem colFlag_iff' (m : Matrix (Idx r k) (Idx r k) K) :
    ColFlag m ↔ ∀ b : Fin (r + 1), ∀ i, (∀ a, a < b → i ≠ pe a) →
      m i (pe b) = if i = pe b then 1 else 0 := by
  classical
  unfold ColFlag
  refine forall_congr' fun b => ?_
  have himg : (fun a => Pi.single (pe (k := k) a) (1 : K)) '' {a | a < b} =
      (fun j => Pi.single j (1 : K)) '' (pe '' {a | a < b}) := by
    rw [Set.image_image]
  rw [himg, mem_span_single]
  refine forall_congr' fun i => ?_
  have h1 : i ∉ pe '' {a | a < b} ↔ ∀ a, a < b → i ≠ pe a := by
    simp only [Set.mem_image, Set.mem_setOf_eq, not_exists, not_and]
    exact forall_congr' fun a => imp_congr_right fun _ => ne_comm
  rw [h1]
  refine imp_congr_right fun _ => ?_
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, sub_eq_zero]

theorem pe_castSucc (i : Fin r) : pe (k := k) (Fin.castSucc i) = Sum.inl i := by
  have h : ((Fin.castSucc i : Fin (r + 1)) : ℕ) < r := i.isLt
  unfold pe
  rw [dite_eq_left h]
  rfl

theorem pe_last : pe (r := r) (k := k) (Fin.last r) = zI := by
  unfold pe
  rw [dite_eq_right (by simp)]

theorem pe_inl_of_lt {a b : Fin (r + 1)} (h : a < b) : pe (k := k) a = Sum.inl ⟨a, by omega⟩ := by
  unfold pe
  rw [dite_eq_left (by omega)]

theorem colFlag_iff (m : Matrix (Idx r k) (Idx r k) K) : ColFlag m ↔ ColC m := by
  classical
  rw [colFlag_iff']
  constructor
  · intro H
    have Hc : ∀ (j : Fin r) (i : Idx r k), (∀ a : Fin r, a < j → i ≠ Sum.inl a) →
        m i (Sum.inl j) = if i = Sum.inl j then 1 else 0 := by
      intro j i hi
      have := H (Fin.castSucc j) i (fun a ha => by
        rw [pe_inl_of_lt ha]
        exact hi _ (by rw [Fin.lt_def] at ha ⊢; simpa using ha))
      rwa [pe_castSucc] at this
    have Hz : ∀ i : Idx r k, (∀ a : Fin r, i ≠ Sum.inl a) → m i zI = if i = zI then 1 else 0 := by
      intro i hi
      have := H (Fin.last r) i (fun a ha => by
        rw [pe_inl_of_lt ha]
        exact hi _)
      rwa [pe_last] at this
    have Hinr : ∀ (j : Fin r) (x : Mid k ⊕ Fin r), m (Sum.inr x) (Sum.inl j) = 0 := by
      intro j x
      have := Hc j (Sum.inr x) (fun a _ h => Sum.inr_ne_inl h)
      simpa using this
    unfold ColC IsUpUni
    refine ⟨⟨?_, fun a => ?_⟩, ?_, ?_, fun w => ?_, ?_, fun j => ?_⟩
    · intro i j hij
      have hij' : j < i := hij
      have := Hc j (Sum.inl i) (fun a ha h => by
        cases h
        exact lt_irrefl _ (ha.trans hij'))
      simpa [b11, hij'.ne'] using this
    · have := Hc a (Sum.inl a) (fun a' ha' h => by
        cases h
        exact lt_irrefl _ ha')
      simpa [b11] using this
    · ext a b
      simp [b21, Hinr]
    · ext a b
      simp [b31, Hinr]
    · simpa [wI, zI] using Hz (wI w) (fun a h => Sum.inr_ne_inl h)
    · simpa using Hz zI (fun a h => Sum.inr_ne_inl h)
    · simpa [zI] using Hz (Sum.inr (Sum.inr j)) (fun a h => Sum.inr_ne_inl h)
  · intro hC
    unfold ColC IsUpUni at hC
    obtain ⟨⟨hup, hdiag⟩, h21, h31, hw, hzz, hf⟩ := hC
    intro b i hi
    induction b using Fin.lastCases with
    | last =>
      rw [pe_last]
      rcases i with i' | ((w | u) | j)
      · exact absurd (pe_castSucc i').symm (hi _ (Fin.castSucc_lt_last i'))
      · simpa [wI, zI] using hw w
      · cases u
        simpa [zI] using hzz
      · simpa [zI] using hf j
    | cast j =>
      rw [pe_castSucc]
      rcases i with i' | (x | j')
      · rcases lt_trichotomy i' j with h | rfl | h
        · exact absurd (pe_castSucc i').symm (hi _ (Fin.castSucc_lt_castSucc_iff.mpr h))
        · simpa [b11] using hdiag i'
        · have := hup h
          simpa [b11, h.ne'] using this
      · simpa [b21] using congrFun (congrFun h21 x) j
      · simpa [b31] using congrFun (congrFun h31 j') j

end MassDataIdxStIm
end
end
