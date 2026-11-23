module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle177
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle257
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle281
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle276
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle277
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetInFamilyMovedOfNotLeak
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovesTotalMeasureEstimates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle026
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MoveLatticeIsTermSameDatumWithWitnesses
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle275
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviConjHaarModulus
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepAverage

theorem exists_smooth_average_of_isKTypeOf : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  intro B d hD hK P u hu
  have hσ : IsURep B.σs := (tensorRep B d hD).1
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => by
    obtain ⟨_, hds, _, _⟩ := hD v
    obtain ⟨_, _, h, _⟩ := hds
    exact h
  have hw : ∀ v, B.w v ∈ Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v) ∧ B.w v ≠ 0 := fun v => by
    obtain ⟨_, _, ⟨h1, h2⟩, _⟩ := hD v
    refine ⟨h2, fun h0 => ?_⟩
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1

  let A : Set B.Hs := {y | ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧
    HasCompactSupport F ∧ y = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I)}
  have hint : ∀ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
      Integrable (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w)) (muInf B.I) :=
    fun F hF hc => integrable_inf B hσ (B.tens B.w) hF.continuous hc
  have hzero : (0 : B.Hs) ∈ A := ⟨0, contDiff_const, HasCompactSupport.zero, by simp⟩
  have hadd : ∀ x y, x ∈ A → y ∈ A → x + y ∈ A := by
    rintro x y ⟨F, hF, hFc, rfl⟩ ⟨G, hG, hGc, rfl⟩
    refine ⟨F + G, hF.add hG, hFc.add hGc, ?_⟩
    rw [← integral_add (hint F hF hFc) (hint G hG hGc)]
    congr 1
    funext g
    simp [add_smul]
  have hsmul : ∀ (c : ℂ) x, x ∈ A → c • x ∈ A := by
    rintro c x ⟨F, hF, hFc, rfl⟩
    refine ⟨fun z => c * F z, contDiff_const.mul hF, hFc.mul_left (f := fun _ => c), ?_⟩
    rw [← integral_smul]
    congr 1
    funext g
    rw [mul_smul]

  have htens : ∀ u' : ∀ v, B.H v, (∀ v, u' v ∈ Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → B.tens u' ∈ A := by
    intro u' hu'
    have hloc := fun v => GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v)
      (B.w v) (hU v) (hK v) (hw v).1 (hw v).2 (u' v) (hu' v)
    choose F hF hFc hFe using hloc
    obtain ⟨G, hG, hGc, hGe⟩ := tens_average B hU hσ B.w F hF hFc
    refine ⟨G, hG, hGc, ?_⟩
    rw [← hGe]
    congr 1
    funext v
    exact hFe v

  have hword : ∀ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (y : B.Hs), y ∈ A → wordAct B l y ∈ A := by
    intro l
    induction l with
    | nil => intro y hy; exact hy
    | cons X l ih =>
      intro y hy
      obtain ⟨F, hF, hFc, hFe⟩ := ih y hy
      obtain ⟨F', hF', hF'c, hd⟩ := GlobalTheory.AverageDeriv.hasDerivAt_orbit_average B F (atPlace B X.1 X.2) (B.tens B.w)
        hσ hF hFc
      refine ⟨F', hF', hF'c, ?_⟩
      show dAct B (atPlace B X.1 X.2) (wordAct B l y) = _
      rw [hFe]
      exact hd.deriv

  let S : Submodule ℂ B.Hs :=
    { carrier := A
      add_mem' := fun hx hy => hadd _ _ hx hy
      zero_mem' := hzero
      smul_mem' := fun c x hx => hsmul c x hx }
  have hle : VP B P ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨l, u', -, hu', rfl⟩
    exact hword l _ (htens u' hu')
  exact hle hu

end GlobalTheory.StepAverage
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_selfDualLattice_completion_maxOrder : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), IsHermND σ J → Submodule.IsLattice E L → (∀ y : Fin n → E, y ∈ L ↔ ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ Lv : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin n → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v Lv ∧ ∀ y, y ∈ Lv ↔ y ∈ GlobalTheory.AdelicU.latLoc F L v := by
  first | exact @GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice | exact GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice | (intros; apply GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.indicator_completedLattice_eq_finprod_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ X : Fin 1 → Fin n → Af F ⊗[F] E, {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}.indicator (1 : (Fin 1 → Fin n → Af F ⊗[F] E) → ℂ) X = ∏ᶠ v : HeightOneSpectrum (𝓞 F), {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) := by
  first | exact @GlobalTheory.AdelicU.indicator_latHat_eq_finprod | exact GlobalTheory.AdelicU.indicator_latHat_eq_finprod | (intros; apply GlobalTheory.AdelicU.indicator_latHat_eq_finprod <;> first | assumption | exact Submodule.IsFullLattice.toIsLattice)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.eventually_localLatticeCompletion_eq_coordinateLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (b : Module.Basis (Fin d) F E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} = latV b v := by
  first
  | exact @GlobalTheory.AdelicU.Cofinite.eventually_latLoc_eq_latV
  | intro F E _ _ _ _ _ n d b L hL
    exact GlobalTheory.AdelicU.Cofinite.eventually_latLoc_eq_latV F E n d b L hL.toIsLattice
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraSeriesCentralIdempotent_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), Green → ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → eSerC L n f ≠ 0 := by
  exact @GlobalTheory.GLm.eSerC_ne_zero
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermDoubleCosetMoveKernel_symm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → S.kern β (j + 1) βJ d Λ Λ' = S.kern β (j + 1) βJ d Λ' Λ := by
  first | exact @GlobalTheory.HL.KernSym.kern_symm | exact GlobalTheory.HL.KernSym.kern_symm | (intros; apply GlobalTheory.HL.KernSym.kern_symm <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → {Λ₁ : Submodule L.O S.V | ∃ w, S.MvTo (j + 1) d Λ Λ₁ w}.Finite ∧ (∀ Λ₁, Nice (S.refA (j + 1) Λ) (ind (S.MvTo (j + 1) d Λ Λ₁))) ∧ {Λ₁ | S.kern β (j + 1) βJ d Λ Λ₁ ≠ 0}.Finite ∧ (∀ Λ₁, 0 ≤ S.kern β (j + 1) βJ d Λ Λ₁) ∧ ∀ (P : Submodule L.O S.V → Prop) (g : Submodule L.O S.V → ℂ) (G : S.MW → ℂ), (∀ w Λ₁, S.MvTo (j + 1) d Λ Λ₁ w → G w = if P Λ₁ then g Λ₁ else 0) → (∀ w, ¬ S.Mv (j + 1) d Λ w → G w = 0) → Nice (S.refA (j + 1) Λ) G ∧ ∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * g y = (S.cK β βJ : ℂ) * cint (S.refA (j + 1) Λ) G := by
  first | exact @GlobalTheory.HL.moves_split_by_target | exact GlobalTheory.HL.moves_split_by_target | (intros; apply GlobalTheory.HL.moves_split_by_target <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem cK_nonneg' (β βJ : ℕ) :
    0 ≤ S.cK β βJ := by
  unfold _root_.GlobalTheory.HL.Frames.cK
  positivity

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem ind_eq_one_of_pos {W : Type} {P : W → Prop} {w : W} (h : P w) :
    _root_.GlobalTheory.IdxInt.ind P w = 1 := by
  unfold _root_.GlobalTheory.IdxInt.ind
  exact if_pos h

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem ind_eq_zero_of_not {W : Type} {P : W → Prop} {w : W} (h : ¬ P w) :
    _root_.GlobalTheory.IdxInt.ind P w = 0 := by
  unfold _root_.GlobalTheory.IdxInt.ind
  exact if_neg h

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem eq_of_MvTo_of_MvTo {a : ℕ} {d : S.Datum}
    {Λ Λ₁ Λ₂ : Submodule L.O S.V} {w : S.MW}
    (h₁ : S.MvTo a d Λ Λ₁ w) (h₂ : S.MvTo a d Λ Λ₂ w) : Λ₁ = Λ₂ := by
  unfold _root_.GlobalTheory.HL.Frames.MvTo at h₁ h₂
  exact SetLike.coe_injective (h₁.2.trans h₂.2.symm)

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem Mv_of_MvTo {a : ℕ} {d : S.Datum}
    {Λ Λ₁ : Submodule L.O S.V} {w : S.MW}
    (h : S.MvTo a d Λ Λ₁ w) : S.Mv a d Λ w := by
  unfold _root_.GlobalTheory.HL.Frames.MvTo at h
  exact h.1

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem exists_MvTo_isTerm_of_Mv_of_InFF [IsNonarchimedeanLocalField F] [CharZero F]
    (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hF : S.InFF β (j + 1) βJ d Λ)
    (w : S.MW) (hw : S.Mv (j + 1) d Λ w) :
    ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ S.IsTerm d Λ₁ := by
  have hw' := hw
  unfold _root_.GlobalTheory.HL.Frames.Mv at hw'
  obtain ⟨n₀, -, n₀', -, n'', -, -, -, -, -, hmov, hW⟩ :=
    _root_.GlobalTheory.HL.MoveWit.main L r k S j β βJ d Λ hT hF _ _ _ _ hw'
  refine ⟨n₀⁻¹ • Λ, ?_, ?_⟩
  · unfold _root_.GlobalTheory.HL.Frames.MvTo
    exact ⟨hw, hmov⟩
  · unfold _root_.GlobalTheory.HL.Frames.IsTerm
    exact ⟨⟨_, _⟩, hW⟩


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.kern_row_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → |(∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, S.kern β (j + 1) βJ d Λ y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d Λ hT hF
  obtain ⟨-, -, hfinK, -, hsplit⟩ :=
    _root_.GlobalTheory.HL.moves_split_by_target L r k S j β βJ d Λ hT hF
  obtain ⟨hNMv, hNLeak, -, hI, hIleak, -⟩ :=
    _root_.GlobalTheory.HL.MoveTotal.total_moves L r k S hk j β βJ d Λ hT hF
  have hlin := _root_.GlobalTheory.IdxInt.Lin.main (S.refA (↑j + 1) Λ)
  have hc := cK_nonneg' S β βJ
  set Good : S.MW → Prop := fun w => ∃ Λ₁, S.MvTo (↑j + 1) d Λ Λ₁ w ∧
    (S.IsTerm d Λ₁ ∧ S.InFF β (↑j + 1) βJ d Λ₁) with hGood
  obtain ⟨hNG, hsum⟩ := hsplit
    (fun y => S.IsTerm d y ∧ S.InFF β (↑j + 1) βJ d y)
    (fun _ => 1) (_root_.GlobalTheory.IdxInt.ind Good)
    (fun w Λ₁ h => by
      by_cases hP : S.IsTerm d Λ₁ ∧ S.InFF β (↑j + 1) βJ d Λ₁
      · rw [if_pos hP, ind_eq_one_of_pos ⟨Λ₁, h, hP⟩]
      · rw [if_neg hP, ind_eq_zero_of_not]
        rintro ⟨Λ₂, h₂, hP₂⟩
        exact hP (eq_of_MvTo_of_MvTo S h₂ h ▸ hP₂))
    (fun w hw => ind_eq_zero_of_not fun ⟨Λ₁, h, _⟩ =>
      hw (Mv_of_MvTo S h))
  have hsupp : (Function.support fun y : {y // S.IsTerm d y ∧
      S.InFF β (↑j + 1) βJ d y} =>
        S.kern β (↑j + 1) βJ d Λ ↑y).Finite :=
    (hfinK.preimage Subtype.val_injective.injOn).subset fun y hy => hy
  have hK : (((∑ᶠ y : {y // S.IsTerm d y ∧
      S.InFF β (↑j + 1) βJ d y},
        S.kern β (↑j + 1) βJ d Λ ↑y : ℝ)) : ℂ) =
      (S.cK β βJ : ℂ) *
        _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind Good) := by
    have hmap := map_finsum Complex.ofRealHom hsupp
    simp only [Complex.ofRealHom_eq_coe] at hmap
    rw [hmap, ← hsum]
    simp
  set H : S.MW → ℂ := fun w =>
    _root_.GlobalTheory.IdxInt.ind (S.Mv (↑j + 1) d Λ) w +
      (-1) * _root_.GlobalTheory.IdxInt.ind Good w with hH
  have hNH : _root_.GlobalTheory.IdxInt.Nice (S.refA (↑j + 1) Λ) H :=
    (hlin.1 _ _ hNMv (hlin.2.1 (-1) _ hNG).1).1
  have hIH : _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ) H =
      _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind (S.Mv (↑j + 1) d Λ)) +
        (-1) * _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind Good) := by
    rw [← (hlin.2.1 (-1) _ hNG).2]
    exact (hlin.1 _ _ hNMv (hlin.2.1 (-1) _ hNG).1).2.1
  have hbound : ∀ w, ‖H w‖ ≤ (_root_.GlobalTheory.IdxInt.ind
      (fun w => S.Mv (↑j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1) w).re := by
    intro w
    by_cases hw : S.Mv (↑j + 1) d Λ w
    · by_cases hg : Good w
      · rw [hH]
        simp only
        rw [ind_eq_one_of_pos hw, ind_eq_one_of_pos hg]
        unfold _root_.GlobalTheory.IdxInt.ind
        split_ifs <;> simp
      · have hleak : ¬ S.NoLeak Λ w.2.1 := by
          intro hno
          apply hg
          obtain ⟨Λ₁, h₁, hT₁⟩ := exists_MvTo_isTerm_of_Mv_of_InFF S j β βJ d Λ hT hF w hw
          refine ⟨Λ₁, h₁, hT₁, ?_⟩
          have hw' := hw
          unfold _root_.GlobalTheory.HL.Frames.Mv at hw'
          have h₁' := h₁
          unfold _root_.GlobalTheory.HL.Frames.MvTo at h₁'
          unfold _root_.GlobalTheory.HL.Frames.NoLeak at hno
          exact _root_.GlobalTheory.HL.OffLeak.inFF_moved_of_not_leak L r k S j β βJ d Λ hT hF _ _ _ _
            hw' hno Λ₁ h₁'.2
        rw [hH]
        simp only
        rw [ind_eq_one_of_pos hw, ind_eq_zero_of_not hg, ind_eq_one_of_pos ⟨hw, hleak⟩]
        simp
    · have hg : ¬ Good w := fun ⟨Λ₁, h, _⟩ => hw (Mv_of_MvTo S h)
      rw [hH]
      simp only
      rw [ind_eq_zero_of_not hw, ind_eq_zero_of_not hg]
      unfold _root_.GlobalTheory.IdxInt.ind
      split_ifs <;> simp
  have hnorm := (hlin.1 _ _ hNH hNLeak).2.2 hbound
  have hKre := congrArg Complex.re hK
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hKre
  have hsplitre := congrArg Complex.re hIH
  simp only [Complex.add_re, neg_one_mul, Complex.neg_re] at hsplitre
  have hHre : |S.cK β βJ *
      (_root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ) H).re| ≤
      16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
    rw [abs_mul, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hc).trans
      ((mul_le_mul_of_nonneg_left hnorm hc).trans hIleak)
  rw [hKre]
  rw [hsplitre] at hHre
  rw [abs_le] at hI hHre ⊢
  constructor <;> nlinarith [hI.1, hI.2, hHre.1, hHre.2]

end GlobalTheory.HL
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.local_hermitian_dual_quotient_cyclic_split_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) → (loc v L).toAddSubgroup.relIndex (loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L)).toAddSubgroup = T ^ 2 → ∃ d ∈ loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L), ∀ x ∈ loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L :=
  @_root_.GlobalTheory.St.G.CyclicQuot.local_dual_cyclic
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.leftQuotientCovolume_withDensity_unfold_subgroup : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (Γ : Subgroup H) [DiscreteTopology Γ] (Φ b : G → ENNReal), Measurable Φ → Measurable b → (∀ h g, Φ (j h * g) = Φ g) → (∀ g, ∫⁻ h, b (j h * g) ∂ν = 1) → covol ((Γ.map j : Subgroup G) : Set G) (μ.withDensity Φ) Set.univ = covol (Γ : Set H) ν Set.univ * ∫⁻ g, Φ g * b g ∂μ := by
  first | exact @GlobalTheory.GenUnfold.covol_withDensity_eq | exact GlobalTheory.GenUnfold.covol_withDensity_eq | (intros; apply GlobalTheory.GenUnfold.covol_withDensity_eq <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.isotropicFlag_levi_conj_haar_modulus : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, 1 ≤ j i) → IsIsoFlag ε j W → ∀ μ, IsGaugeSub (flagN ε W) (dimN n j) μ → ∀ m ∈ flagM ε W, μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) • μ := by
  first | exact @GlobalTheory.FlagModulus.modulus | exact GlobalTheory.FlagModulus.modulus | (intros; apply GlobalTheory.FlagModulus.modulus <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.fibreVolume_normalFormStabiliser : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ j → j + 2 ≤ k → DeOK k r z z' γ De → 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yj k r hj z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset0 k r hj z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y / s) := by
  first | exact @GlobalTheory.Amp.FibreVolume.fibre_volume | exact GlobalTheory.Amp.FibreVolume.fibre_volume | (intros; apply GlobalTheory.Amp.FibreVolume.fibre_volume <;> assumption)
end
