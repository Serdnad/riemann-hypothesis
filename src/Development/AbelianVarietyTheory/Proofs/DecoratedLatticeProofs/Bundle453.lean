module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle417
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle082
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SameOrbEquivalence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle376
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsExtGeometryTupleOfRepresentatives
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle435
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam

theorem conv_single_one_of_forall {G : Type} [Monoid G] (l : List (G →₀ ℂ))
    (h : ∀ x ∈ l, x = Finsupp.single 1 1) : GlobalTheory.QPl.conv l = Finsupp.single 1 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : x = Finsupp.single 1 1 := h x (by simp)
    have hl := ih (fun y hy => h y (by simp [hy]))
    show List.foldr _ _ (x :: l) = _
    simp only [List.foldr_cons]
    change (x.sum fun g a => (GlobalTheory.QPl.conv l).sum fun h b => Finsupp.single (g * h) (a * b)) = _
    rw [hx, hl, Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
    simp

end GlobalTheory.Fam
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PosOne
open scoped ENNReal

attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

section Scale
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k]

theorem isQuotInt_smul_measure {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {ν : Measure k} {μX : Measure (GL n k)}
    {μG : Measure (GL (n ⊕ Fin c) k)} {p : ℕ} {f : GL (n ⊕ Fin c) k → ℂ} {z : ℂ} (a : ℝ≥0∞)
    (h : IsQuotInt ν μX μG p f z) : IsQuotInt ν μX (a • μG) p f ((a.toReal : ℂ) * z) := by
  obtain ⟨F, hF, hf, hz⟩ := h
  refine ⟨F, hF, hf, ?_⟩
  rw [integral_smul_measure, hz, Complex.real_smul]

theorem isQuotInt_const_mul {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {ν : Measure k} {μX : Measure (GL n k)}
    {μG : Measure (GL (n ⊕ Fin c) k)} {p : ℕ} {f : GL (n ⊕ Fin c) k → ℂ} {z : ℂ} (b : ℂ)
    (h : IsQuotInt ν μX μG p f z) : IsQuotInt ν μX μG p (fun x => b * f x) (b * z) := by
  obtain ⟨F, hF, hf, hz⟩ := h
  refine ⟨fun x => b * F x, (SB _).smul_mem b hF, fun x => ?_, ?_⟩
  · dsimp only
    rw [hf x, ← integral_const_mul]
    congr 1
    funext g
    exact (integral_const_mul _ _).symm
  · rw [hz, integral_const_mul]

theorem app_smul {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V] (b : ℂ) (l : SB X →ₗ[ℂ] V)
    (f : X → ℂ) : app (b • l) f = b • app l f := by
  unfold app
  split_ifs <;> simp

theorem oneDbl_smul {n₀ n₁ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] {c : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] {ψ : AddChar k Circle} {ν : Measure k}
    {m₁ : Measure (GL n₁ k)} {G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)} {m₂ : Measure (GL n₂ k)}
    {G₂ : Measure (GL (n₂ ⊕ Fin c) k)} {μ₁ μ₂ : kˣ →* ℂˣ} {ρ : ℕ} {σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A}
    {T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} {F : A}
    {Φ₁ : Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ}
    {Φ₂ : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ} {z : ℂ} (a b : ℝ≥0∞)
    (h : OneDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F Φ₁ Φ₂ z) :
    OneDbl ψ ν m₁ (a • G₁) m₂ (b • G₂) μ₁ μ₂ ρ σ T F Φ₁ Φ₂ ((a.toReal : ℂ) * ((b.toReal : ℂ) * z)) := by
  obtain ⟨w, hw, hz⟩ := h
  refine ⟨fun x => (b.toReal : ℂ) • w x, fun x Ψ => ?_, ?_⟩
  · exact isQuotInt_smul_measure b (hw x Ψ)
  · have := isQuotInt_smul_measure a (isQuotInt_const_mul (b.toReal : ℂ) hz)
    convert this using 2 with x
    rw [app_smul, smul_eq_mul]

theorem relIndex_mul_measure_KO {Y : Type} [Fintype Y] [DecidableEq Y] (G : Measure (GL Y k)) [G.IsHaarMeasure]
    (hK : G (KO k Y) = 1) (J : Subgroup (GL Y k)) (hJ : IsCO J) (hle : J ≤ KO k Y) :
    (J.relIndex (KO k Y) : ℝ≥0∞) * G J = 1 ∧ J.relIndex (KO k Y) ≠ 0 := by
  haveI : BorelSpace (GL Y k) := GlobalTheory.SplitFlip.borel_GL
  have hc : IsCompact (KO k Y : Set (GL Y k)) := GlobalTheory.SplitFlip.isCompact_KO
  haveI : CompactSpace (KO k Y) := isCompact_iff_compactSpace.1 hc
  have ho : IsOpen ((J.subgroupOf (KO k Y) : Subgroup (KO k Y)) : Set (KO k Y)) :=
    hJ.1.preimage continuous_subtype_val
  haveI : Finite (KO k Y ⧸ J.subgroupOf (KO k Y)) := Subgroup.quotient_finite_of_isOpen _ ho
  haveI : (J.subgroupOf (KO k Y)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨?_, Subgroup.FiniteIndex.index_ne_zero⟩
  rw [GlobalTheory.IndexVolume.relIndex_mul_measure_subgroup J (KO k Y) hle hJ.1.measurableSet G, hK]

theorem rescale_one_eq {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (hc : 1 ≤ c) {ν : Measure k} (hν : IsUnitVol ν)
    (m : Measure (GL n k)) : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν (1 : GL (n ⊕ Fin c) k) m = m := by
  have h := GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one k n c 1 le_rfl hc ν hν
  have e : (((stabLat (1 : GL (n ⊕ Fin c) k)).subgroupOf (N k n c 1) : Subgroup (N k n c 1)) : Set (N k n c 1)) =
      {u : N k n c 1 | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} := by
    ext u
    simp [Subgroup.mem_subgroupOf, mem_stabLat]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale
  rw [e, h, inv_one, one_smul]

end Scale



theorem comb_eq_sum_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → HasConductor ψ 1 → ∀ (ν : Measure k), IsUnitVol ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ), IsOpen (μ₁.ker : Set kˣ) → IsOpen (μ₂.ker : Set kˣ) →
  ∀ (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
    G₁ (KO k (n₁ ⊕ Fin (c + 1))) = 1 → G₂ (KO k (n₂ ⊕ Fin c)) = 1 →
  ∀ (L₀ : Level (GL (n₀ ⊕ Fin (c + 1 + 1)) k)) (L₁ : Level (GL (n₁ ⊕ Fin (c + 1)) k)) (L₂ : Level (GL (n₂ ⊕ Fin c) k)),
    IsCO L₁.J → IsCO L₂.J → L₁.J ≤ KO k _ → L₂.J ≤ KO k _ →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A), (∀ j : L₂.J, τ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) →
  ∀ (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)),
    HasTypes μ₁ L₀ L₁ P₁.1 → HasTypes μ₂ L₁ L₂ P₂.1 →
  ∀ (α : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (A₁ : Finset (GL (n₁ ⊕ Fin (c + 1)) k)) (A₂ : Finset (GL (n₂ ⊕ Fin c) k)),
    Covers 1 L₁.J A₁ (fun h => GlobalTheory.StepData.flat ψ ν μ₁ P₁.1 α h) → (∀ γ ∈ A₁, Covers 1 L₂.J A₂ fun h => GlobalTheory.StepData.flat ψ ν μ₂ P₂.1 γ h) →
  ∀ (e₀ : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ), IsOneComb ψ ν (ρ + 1) L₀ α e₀ →
  ∀ (e₂ : GL (n₂ ⊕ Fin c) k → (GL (n₂ ⊕ Fin c) k →₀ ℂ)), (∀ β ∈ A₂, IsOneComb ψ ν ρ L₂ β (e₂ β)) →
  ∀ (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ),
    (∀ a ∈ e₀.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    comb e₀ z = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ))⁻¹ *
      ∑ γ ∈ A₁, ∑ β ∈ A₂, ((((m₁ (prX (Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (prX (Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) *
        comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F)) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ ho₁ ho₂ m₁ G₁ m₂ G₂ hm₁ hG₁ hm₂ hG₂ hK₁ hK₂
    L₀ L₁ L₂ hco₁ hco₂ hle₁ hle₂ A _ _ τ hτ T hT F hF P₁ P₂ hty₁ hty₂ α A₁ A₂ hcov₁ hcov₂ e₀ he₀ e₂ he₂ z hz
  haveI := hm₁
  haveI := hG₁
  haveI := hm₂
  haveI := hG₂
  have hne : ψ ≠ 1 := hcond.ne_one
  have hsd : IsSelfDual ψ ν := ((GlobalTheory.SplitWeil.selfDual_measure k ψ hψ hne).2.1 hcond ν).1 hν
  obtain ⟨⟨ρ₀, hρ₀⟩, hsm⟩ := GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₀ ⊕ Fin (c + 1 + 1)) (n₁ ⊕ Fin (c + 1)) μ₁ ho₁
  have hsm₀ := hsm ρ₀ hρ₀

  have hcomb : ∀ f : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ,
      comb (e₀.mapDomain (· * α⁻¹)) (fun g => f (g * α)) = comb e₀ f := by
    intro f
    unfold comb
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    simp only [inv_mul_cancel_right]
  have hsrc : SrcComb ψ ν (ρ + 1) ρ₀ (ρ₀ α P₁) (e₀.mapDomain (· * α⁻¹)) := by
    intro L hL
    have hP : ∀ j : L₀.J, ρ₀ (j : GL (n₀ ⊕ Fin (c + 1 + 1)) k) P₁ = (L₀.lam j : ℂ) • P₁ := fun j =>
      Subtype.ext ((hρ₀ _ _).trans (hty₁.1 j))
    rw [he₀ _ ρ₀ hsm₀ L hL P₁ hP, ← hcomb]
    congr 1
    funext g
    rw [map_mul, Module.End.mul_apply]
  have hsym : ∀ g ∈ (e₀.mapDomain (· * α⁻¹)).support,
      SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ g 1 (ρ₀ α P₁).1) P₂.1 (z (g * α)) := by
    intro g hg
    classical
    rw [Finsupp.mapDomain_support_of_injective (mul_left_injective α⁻¹)] at hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hg
    have e : om μ₁ (a * α⁻¹) 1 (ρ₀ α P₁).1 = om μ₁ (a * α⁻¹ * α) 1 P₁.1 := by
      rw [← hρ₀, ← hρ₀, map_mul ρ₀ (a * α⁻¹) α, Module.End.mul_apply]
    rw [e]
    simpa only [inv_mul_cancel_right] using hz a ha
  have h1 := @GlobalTheory.T.positionOne_of_symmetricDoubleIntegral_finite k _ _ _ _ _ _
    n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hne ν hsd μ₁ μ₂ ho₁ ho₂ m₁ hm₁ G₁ hG₁ m₂ hm₂ G₂ hG₂ A _ _ τ hτ T hT F ρ₀ hρ₀ (ρ₀ α P₁) P₂
    (e₀.mapDomain (· * α⁻¹)) hsrc (fun g => z (g * α)) hsym
  rw [hcomb, hρ₀] at h1

  obtain ⟨hi₁, hn₁⟩ := relIndex_mul_measure_KO G₁ hK₁ L₁.J hco₁ hle₁
  obtain ⟨hi₂, hn₂⟩ := relIndex_mul_measure_KO G₂ hK₂ L₂.J hco₂ hle₂
  set r₁ : ℝ≥0∞ := (L₁.J.relIndex (KO k (n₁ ⊕ Fin (c + 1))) : ℝ≥0∞) with hr₁
  set r₂ : ℝ≥0∞ := (L₂.J.relIndex (KO k (n₂ ⊕ Fin c)) : ℝ≥0∞) with hr₂
  haveI : (r₁ • G₁).IsHaarMeasure := Measure.IsHaarMeasure.smul G₁ (by simpa [hr₁] using hn₁) (by simp [hr₁])
  haveI : (r₂ • G₂).IsHaarMeasure := Measure.IsHaarMeasure.smul G₂ (by simpa [hr₂] using hn₂) (by simp [hr₂])
  have h2 := oneDbl_smul r₁ r₂ h1
  have hc : 1 ≤ c := by omega
  rw [← rescale_one_eq (n := n₁) (c := c + 1) (by omega) hν m₁, ← rescale_one_eq (n := n₂) hc hν m₂] at h2
  have h3 := (@GlobalTheory.PosOne.oneDbl_iff_sum k _ _ _ _ _ _
    n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ ho₁ ho₂
    m₁ hm₁ (r₁ • G₁) ‹(r₁ • G₁).IsHaarMeasure› m₂ hm₂ (r₂ • G₂) ‹(r₂ • G₂).IsHaarMeasure›
    L₁ L₂ hco₁ hco₂ (by exact hi₁) (by exact hi₂) 1 1 A _ _ τ hτ T hT F hF
    P₁ P₂ hty₁.2 hty₂ α A₁ A₂ hcov₁ hcov₂ _).1 h2

  have hex : ∀ γ ∈ A₁, ∀ β ∈ A₂, toOne ν τ ρ (fun v => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) v)
      (τ β F) = comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F) := by
    intro γ _ β hβ
    refine he₂ β hβ A τ hτ _ ?_ F hF
    intro g hg v
    unfold app
    split_ifs with h₁ h₂
    · exact (hT.1 _).1 _ g hg v
    · simp
    · simp
  have hr : ((r₁.toReal : ℂ) * (r₂.toReal : ℂ)) = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ)) := by
    simp [hr₁, hr₂]
  have hr0 : ((L₁.J.relIndex (KO k (n₁ ⊕ Fin (c + 1))) : ℂ) * (L₂.J.relIndex (KO k (n₂ ⊕ Fin c)) : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn₁) (Nat.cast_ne_zero.2 hn₂)
  rw [← mul_assoc, hr] at h3
  rw [eq_inv_mul_iff_mul_eq₀ hr0, h3]
  refine Finset.sum_congr rfl fun γ hγ => Finset.sum_congr rfl fun β hβ => ?_
  rw [hex γ hγ β hβ]
  rfl

end GlobalTheory.PosOne
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw.CosExt



theorem exists_qExt_cos : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle), c.Is → ∀ (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → (∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ)) → ∀ A, (G.T δ hδ η).IsRepSystem A G.ψk G.ν → ∀ M : ℕ, (G.T δ hδ η).Adapted A (box _ (G.ϖ ^ M)⁻¹) (box _ (G.ϖ ^ M)) → ∀ (C : Type) [Fintype C] (cs : C → XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k), (∀ y y', SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk (cs y')) → y = y') → (∀ z ∈ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ M)⁻¹, ∃ y, SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk z)) → ∃ E : QExt G χ, E.δ = δ ∧ E.η = η ∧ E.A = A ∧ E.M = M ∧ (∃ e : C ≃ E.Ch (G.s + 1), ∀ y, E.cos (e y) = Submodule.Quotient.mk (cs y)) ∧ ∀ j, G.s + 1 + 1 < j → Nonempty (Unique (E.Ch j)) := by
  intro D c v B PP G χ hc δ hδ η hη hμ A hA M hM C _ cs hinj hall
  obtain ⟨E, rfl, rfl, rfl, rfl, -⟩ := GlobalTheory.QTw.Inh.exists_ext_of_reps D c v B PP G χ hc δ hδ η hη hμ A hA M hM
  classical
  let Ch' : ℕ → Type := fun j => if j = G.s + 1 then C else if G.s + 1 + 1 < j then Unit else E.Ch j
  have eC : Ch' (G.s + 1) = C := if_pos rfl
  have eE : ∀ j, j ≤ G.s + 1 + 1 → j ≠ G.s + 1 → Ch' j = E.Ch j := fun j h1 h2 => by
    simp only [Ch', if_neg h2, if_neg (not_lt.2 h1)]
  have eU : ∀ j, G.s + 1 + 1 < j → Ch' j = Unit := fun j h1 => by
    simp only [Ch', if_neg (show j ≠ G.s + 1 by omega), if_pos h1]
  let fC : ∀ j, Fintype (Ch' j) := fun j => by
    simp only [Ch']; split_ifs <;> infer_instance
  let rep' : ∀ j d, j + d = G.s → Ch' j → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (d + 1)) G.k :=
    fun j d h x => E.rep j d h (cast (eE j (by omega) (by omega)) x)
  let cos' : Ch' (G.s + 1) → (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k) ⧸ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ E.M) :=
    fun y => Submodule.Quotient.mk (cs (cast eC y))
  have hpen : ∀ (α : Ch' G.s) (y : Ch' (G.s + 1)), ∃ e, (ofSplit G.q).IsCombAt c.ψ (G.FX G.s (by omega)) (G.FX (G.s + 1) le_rfl) e
      ((G.T E.δ E.tame E.η).xiPen (box _ (G.ϖ ^ E.M)) (rep' G.s 0 rfl α) (cos' y)) :=
    fun α y => GlobalTheory.LocMod.CombAt.exists_isCombAt _ hc.std _ _ _
  have htop : ∀ (y : Ch' (G.s + 1)), ∃ e, (ofSplit G.q).IsCombAt c.ψ (G.FX (G.s + 1) le_rfl) G.FM e
      ((G.T E.δ E.tame E.η).xiTop (box _ (G.ϖ ^ E.M)) G.ψk G.ν (-1) (cos' y)) :=
    fun y => GlobalTheory.LocMod.CombAt.exists_isCombAt _ hc.std _ _ _
  choose dPen hdPen using hpen
  choose dTop hdTop using htop
  let dL' : ∀ j, Ch' j → Ch' (j + 1) → WO (c.X j) (c.X (j + 1)) →₀ ℂ := fun j =>
    if h : j + 1 ≤ G.s then fun α γ => E.dL j (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ)
    else if h' : j = G.s then (by subst h'; exact dPen)
    else if h'' : j = G.s + 1 then (by subst h''; exact fun y _ => dTop y)
    else fun _ _ => 0
  let wt' : ∀ j, Ch' j → ℂ := fun j =>
    if h : j = G.s + 1 then (by subst h; exact fun y => (E.idx (G.s + 1) : ℂ) *
      (Nat.card {yb | SameOrb ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ E.M)) (cos' y) yb} : ℂ))
    else if h' : j ≤ G.s then fun α => E.wt j (cast (eE j (by omega) (by omega)) α)
    else fun _ => (E.idx (G.s + 1 + 1) : ℂ)
  let εL' : ∀ j, Ch' j → GA D (c.V j) →₀ ℂ := fun j =>
    if h : j ≤ G.s then fun α => E.εL j (cast (eE j (by omega) (by omega)) α) else fun _ => 0
  let E' : QExt G χ :=
    { δ := E.δ, tame := E.tame, η := E.η, unr := E.unr, mu_comp := E.mu_comp, A := E.A, reps := E.reps, Ch := Ch', fC := fC, rep := rep'
      rep_bij := fun j d h => (E.rep_bij j d h).comp
        ((Equiv.cast (eE j (by omega) (by omega))).bijective.bijOn_univ)
      M := E.M, adapt := E.adapt, cos := cos'
      cos_inj := fun y y' h => (Equiv.cast eC).injective (hinj _ _ h)
      cos_all := fun z hz => by
        obtain ⟨y, hy⟩ := hall z hz
        exact ⟨cast eC.symm y, by simpa [cos'] using hy⟩
      one := (Fintype.card_congr (Equiv.cast (eE (G.s + 1 + 1) le_rfl (by omega)))).trans E.one
      eL := E.eL, eLT := E.eLT, eL_at := E.eL_at, eLT_at := E.eLT_at, dL := dL'
      dL_mid := fun j d H α γ => by
        have := E.dL_mid j d H (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ)
        have e : dL' j α γ = E.dL j (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ) := by
          simp only [dL']; rw [dite_eq_left (show j + 1 ≤ G.s by omega)]
        rw [e]; exact this
      dL_pen := fun α y => by
        have e : dL' G.s α y = dPen α y := by
          simp only [dL']; rw [dite_eq_right (by omega), dite_eq_left trivial]
        rw [e]; exact hdPen α y
      dL_top := fun y u => by
        have e : dL' (G.s + 1) y u = dTop y := by
          simp only [dL']; rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left trivial]
        rw [e]; exact hdTop y
      εL := εL'
      εL_at := fun j ρ hρ d h α => by
        obtain ⟨e, h1, h2⟩ := E.εL_at j ρ hρ d h (cast (eE j (by omega) (by omega)) α)
        refine ⟨e, h1, ?_⟩
        rw [← h2]; simp only [εL']; rw [dite_eq_left (show j ≤ G.s by omega)]
      εL_zero := fun α => by
        simp only [εL']; rw [dite_eq_left (Nat.zero_le _)]; exact E.εL_zero _
      idx := E.idx, idx_mid := E.idx_mid, idx_top := E.idx_top, m := E.m, haar := E.haar, wt := wt'
      wt_mid := fun j d h α => by
        rw [← E.wt_mid j d h (cast (eE j (by omega) (by omega)) α)]
        simp only [wt']; rw [dite_eq_right (show j ≠ G.s + 1 by omega), dite_eq_left (show j ≤ G.s by omega)]
      wt_pen := fun y => by simp only [wt']; rw [dite_eq_left trivial]
      wt_top := fun u => by simp only [wt']; rw [dite_eq_right (by omega), dite_eq_right (by omega)] }
  refine ⟨E', rfl, rfl, rfl, rfl, ⟨Equiv.cast eC.symm, fun y => ?_⟩, fun j hj => ⟨(Equiv.cast (eU j hj)).unique⟩⟩
  simp [E', cos']

end GlobalTheory.QTw.CosExt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bottom_spherical_card_weight_index : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : QExt G χ), Fintype.card (E.Ch 0) = 1 ∧ (∀ α, E.wt 0 α = 1) ∧ E.idx 0 = 1 ∧ ∀ j, j ≤ G.s + 1 + 1 → E.idx j ≠ 0 := by
  exact @GlobalTheory.QTw.QExt.bottom_one
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.inv_haarVolume_toReal_eq_relIndex_integral : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : GlobalTheory.QTw.QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : GlobalTheory.QTw.QExt G χ) (j : ℕ) (H : Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)), H ≤ KO G.k _ → MeasurableSet (H : Set (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)) → H.relIndex (KO G.k _) ≠ 0 → ((((E.m j H).toReal)⁻¹ : ℝ) : ℂ) = (H.relIndex (KO G.k _) : ℂ) := by
  first | exact @GlobalTheory.QTw.QExt.m_inv_toReal_eq_relIndex | exact GlobalTheory.QTw.QExt.m_inv_toReal_eq_relIndex | (intros; apply GlobalTheory.QTw.QExt.m_inv_toReal_eq_relIndex <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_extGeometry_tuple_of_representatives : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle), c.Is → ∀ (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → (∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ)) → ∀ A, (G.T δ hδ η).IsRepSystem A G.ψk G.ν → ∀ M : ℕ, (G.T δ hδ η).Adapted A (box _ (G.ϖ ^ M)⁻¹) (box _ (G.ϖ ^ M)) → ∃ E : QExt G χ, E.δ = δ ∧ E.η = η ∧ E.A = A ∧ E.M = M := by
  first | exact @GlobalTheory.QExtEx.exists_qExt | exact GlobalTheory.QExtEx.exists_qExt | (intros; apply GlobalTheory.QExtEx.exists_qExt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.isFrame_finitePart_mul_of_carries_lattice : ∀ (D : D7) (V : HSp D) (t : GA D V) (Λ M : Lat V) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)), Moves V t Λ M (fun _ => True) → Formalism.L2.DIV.IsFrame β Λ → Formalism.L2.DIV.IsFrame (finE V t * β) M := by
  first | exact @GlobalTheory.Core.Mi.FrameMove.isFrame_of_moves | exact GlobalTheory.Core.Mi.FrameMove.isFrame_of_moves | (intros; apply GlobalTheory.Core.Mi.FrameMove.isFrame_of_moves <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped ENNReal NNReal

namespace GlobalTheory.MixedAbsGrowth

theorem map_infPart_nsmul {D : D7} {m r : ℕ} (n : ℕ) (u : Mx D m r) (hu : u.map (infPart D) = 0) :
    (n • u).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hu i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at h ⊢
  rw [Matrix.smul_apply, nsmul_eq_mul, (infPart D).map_mul, h, mul_zero]

theorem map_infPart_actO {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T)
    (hu : u.map (infPart D) = 0) : (actO S T g h u).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

theorem actO_actO_inv {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  have := GlobalTheory.WeilVacMove.actO_inv_actO g⁻¹ h⁻¹ x
  rwa [inv_inv, inv_inv] at this

theorem mixed_abs_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h (w : WO S₀ T), (∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 (om (g, h) f) x w‖ₑ) ≤ ENNReal.ofReal (C * (height S g * height T h) ^ A) := by
  intro D ψ S T χS χT om hW S₀ ρ d v f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨K₀, hK₀, -, m, hm⟩ := GlobalTheory.KernelSeminorm.exists_level_multiple hUo
  obtain ⟨k, hk⟩ := GlobalTheory.T.mixedCoordinate_tsum_le_of_theta_level_multiple D ψ hW.std θ hθ S S₀ T ρ d v
  obtain ⟨C, hC⟩ := hk K₀ hK₀
  obtain ⟨A, hA⟩ := GlobalTheory.WeilWordGrowth.sup_words_growth D ψ S T χS χT om hW θ hθ k
  obtain ⟨c, hc⟩ := hA f hf
  refine ⟨(C : ℝ) * (m : ℝ) ^ k * max c 0, A + k, fun g h w => ?_⟩
  obtain ⟨n, hn0, hnm, hnU⟩ := hm g h
  have hF := hW.om_pres (g, h) f hf
  have hlev : ∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) (om (g, h) f) = om (g, h) f := by
    intro u hu hinf
    have h1 := hU _ (hnU u hu hinf) (map_infPart_actO _ _ _ (map_infPart_nsmul n u hinf))
    have h2 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ (n • u)) f hf
    rw [h1, actO_actO_inv] at h2
    exact h2.symm
  have h1 := hC n hn0 (om (g, h) f) hF hlev w
  have h2 : supSob ψ θ k (om (g, h) f) ≤ ENNReal.ofReal (c * (height S g * height T h) ^ A) := hc g h
  set H : ℝ := height S g * height T h with hH
  have H0 : 0 ≤ H := mul_nonneg (height_pos S g).le (height_pos T h).le
  refine h1.trans ?_
  have e1 : ((C : ℝ≥0∞) * (n : ℝ≥0∞) ^ k) = ENNReal.ofReal ((C : ℝ) * (n : ℝ) ^ k) := by
    rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow (Nat.cast_nonneg n),
      ENNReal.ofReal_natCast]
  rw [e1]
  refine (mul_le_mul' le_rfl (h2.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left c 0) (pow_nonneg H0 A))))).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hn : (n : ℝ) ^ k ≤ ((m : ℝ) * H) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg n) hnm k
  have hc0 : 0 ≤ max c 0 := le_max_right c 0
  calc (C : ℝ) * (n : ℝ) ^ k * (max c 0 * H ^ A) ≤ (C : ℝ) * ((m : ℝ) * H) ^ k * (max c 0 * H ^ A) := by
        gcongr
    _ = (C : ℝ) * (m : ℝ) ^ k * max c 0 * H ^ (A + k) := by rw [mul_pow, pow_add]; ring

end GlobalTheory.MixedAbsGrowth
end
