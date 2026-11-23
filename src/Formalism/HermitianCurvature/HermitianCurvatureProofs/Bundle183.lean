module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle175
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle176
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle171
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle063
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABStar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle165
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle066
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle140
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle163
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def GEqs (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : B.Mat k r → E) : Prop :=
  Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') J ∧
  (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Formalism.REAL.RdV X J g = c • J g) ∧
  (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.LdV X J g = c • J g) ∧
  (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs → ∀ w : ℂ, ∃ c : ℂ,
    ∀ g ∈ JF.Om k r z z', Q.capLft k r Bs w J g = c • J g) ∧
  (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z'] Bs → ∀ w : ℂ, ∃ c : ℂ,
    ∀ g ∈ JF.Om k r z z', Q.capR k r Bs w J g = c • J g) ∧
  (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.CV k r (Y : ℂ) J g = c • J g)

def NDiff : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (m : ℕ∞) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    J ∈ Gr.FFlM m k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Formalism.REAL.RdV X J g = c • J g) ∧
    (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Q.LdV X J g = c • J g)

def UCap : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (u u' : ℕ → ℝ) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' →
    J ∈ Gr.FFlM ((2 * r + k + 1 : ℕ) : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [D.z] Bs → ∀ w : ℂ, ∃ c : ℂ,
      ∀ g ∈ JF.Om k r D.z D.z', Q.capLft k r Bs w J g = c • J g) ∧
    (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [D.z'] Bs → ∀ w : ℂ, ∃ c : ℂ,
      ∀ g ∈ JF.Om k r D.z D.z', Q.capR k r Bs w J g = c • J g)

def GEqsPost : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : B.Mat k r → E) (ℓ : E →L[ℂ] ℂ), GEqs k r z z' J → GEqs k r z z' (fun g => ℓ (J g))

def SmoothOfCoeffs : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (Dm : Set (B.Mat k r))
    (J : B.Mat k r → E), (∀ ℓ : E →L[ℂ] ℂ, Q.SmoothLev k r 0 Dm (fun g => ℓ (J g))) → Q.SmoothLev k r 0 Dm J

def GChart : Prop :=
  ∀ (k r : ℕ), ∃ d : ℕ, ∀ g₀ ∈ B.GV k r, ∃ (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)),
    IsOpen O ∧ IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ κ O ∧ ContDiffOn ℝ ∞ Φ U ∧
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) ∧ (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g)

def ChartEqs : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsOpen O → IsOpen U → ContDiffOn ℝ ∞ κ O → ContDiffOn ℝ ∞ Φ U →
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) → (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g) →
    (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') → GEqs k r z z' u →
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → SOp d),
      (∀ j i w, ContDiffOn ℝ ∞ ((P j).a i w) O) ∧ (∀ j, (P j).ord ≤ 2 * r + k + 1) ∧
      ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
      (∀ j, ∀ x ∈ O, (P j).app (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → (∀ j, (P j).symb x ξ = 0) →
        ∃ Ξ : B.Mat k r, B.inLie k r Ξ ∧ Ξ ≠ 0 ∧ IsNilpotent Ξ ∧
          (∀ X ∈ JfS.lieOf (UWset k r z) ∪ JfS.lieOf (Nset k r), (Matrix.trace (Ξ * X)).re = 0) ∧
          (∀ X ∈ JfS.lieOf (UWset k r z') ∪ JfS.lieOf (Nset k r),
            (Matrix.trace (Ξ * (κ x * X * (κ x)⁻¹))).re = 0)

def ClassToWeak : Prop :=
  ∀ (d N : ℕ) (P : SOp d) (U : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ),
    IsOpen U → (∀ i w, ContDiffOn ℝ ∞ (P.a i w) U) → P.ord ≤ N → ContDiffOn ℝ (N : WithTop ℕ∞) u U →
    (∀ x ∈ U, P.app u x = 0) →
    ∀ φ : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x, u x * P.tr φ x = 0

def LieSsetSplit : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∀ X ∈ JfS.lieOf (Sset k r z), ∃ A ∈ JfS.lieOf (UWset k r z), ∃ Bn ∈ JfS.lieOf (Nset k r), X = A + Bn

def GRegScalar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → GEqs k r z z' u →
    Q.SmoothLev k r 0 (Q.OmPlus k r z z') u

theorem gRegJ_of (hN : NDiff) (hU : UCap) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hS : GRegScalar) : GRegJ := by
  intro k r Wp Wq _ _ _ _ _ _ D u u' J hT hT' hF hCV
  have hG : GEqs k r D.z D.z' J := by
    obtain ⟨hn1, hn2⟩ := hN k r Wp Wq D _ J hF
    obtain ⟨hu1, hu2⟩ := hU k r Wp Wq D u u' J hT hT' hF
    refine ⟨?_, hn1, hn2, hu1, hu2, hCV⟩
    intro g₀ hg₀
    obtain ⟨U, F, hUo, hgU, hFc, hJF⟩ := hF.1 g₀ hg₀
    exact ⟨U, F, hUo, hgU, by simpa [Gr.smM] using hFc, hJF⟩
  exact hC k r (Wq →L[ℂ] Wp) _ J (fun ℓ =>
    hS k r D.z D.z' _ D.k_pos D.z_mem D.z'_mem D.T_pos D.T'_pos (hP k r D.z D.z' _ J ℓ hG))

theorem gRegScalar_of (hK : GChart) (hE : ChartEqs) (hW : ClassToWeak) (hR : EllRegW) (hSym : JfS.SymbolNil)
    (hL : LieSsetSplit) : GRegScalar := by
  intro k r z z' u hk hz hz' hT hT' hG g₀ hg₀
  obtain ⟨d, hd⟩ := hK k r
  have hg₀G : g₀ ∈ B.GV k r := hg₀.1.1
  obtain ⟨O, U, κ, Φ, hO, hU, hg₀U, hκ, hΦ, hκO, hΦU⟩ := hd g₀ hg₀G
  have hO' : IsOpen (O ∩ κ ⁻¹' Q.OmPlus k r z z') :=
    hκ.continuousOn.isOpen_inter_preimage hO (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z')
  have hU' : IsOpen (U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z')) :=
    hΦ.continuousOn.isOpen_inter_preimage hU hO'
  have hΦg₀ : Φ g₀ ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z' := by
    obtain ⟨h1, h2⟩ := hΦU g₀ hg₀U hg₀G
    refine ⟨h1, ?_⟩
    show κ (Φ g₀) ∈ Q.OmPlus k r z z'
    rw [h2]; exact hg₀.2
  have hκO' : ∀ x ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z',
      κ x ∈ B.GV k r ∧ κ x ∈ U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z') ∧ Φ (κ x) = x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hκO x hx.1
    refine ⟨h1, ⟨h2, ?_⟩, h3⟩
    show Φ (κ x) ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z'
    rw [h3]; exact hx
  have hΦU' : ∀ g ∈ U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z'), g ∈ B.GV k r →
      Φ g ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z' ∧ κ (Φ g) = g :=
    fun g hg hgG => ⟨hg.2, (hΦU g hg.1 hgG).2⟩
  obtain ⟨ι, hι, P, hPc, hPo, huc, hPu, hsym⟩ := hE k r z z' d _ _ κ Φ u hk hz hz' hT hT' hO' hU'
    (hκ.mono Set.inter_subset_left) (hΦ.mono Set.inter_subset_left) hκO' hΦU' (fun x hx => hx.2) hG
  have := hι
  have hsm : ContDiffOn ℝ ∞ (fun x => u (κ x)) (O ∩ κ ⁻¹' Q.OmPlus k r z z') := by
    refine hR d ι P _ _ hO' hPc huc.continuousOn
      (fun j φ hφ hφc hφs => hW d _ (P j) _ _ hO' (hPc j) (hPo j) huc (hPu j) φ hφ hφc hφs) ?_
    intro x hx ξ hξ
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨Ξ, hΞ, hΞ0, hnil, hl, hr⟩ := hsym x hx ξ hξ hall
    apply hΞ0
    have hxG := (hκO' x hx).1
    have hxOm : κ x ∈ Q.OmPlus k r z z' := hx.2
    refine hSym k r z z' hk hz hz' hT hT' (κ x) hxG ⟨hxOm.2, fun a => hxOm.1 ⟨(a : ℕ) + 1, by omega⟩ a.isLt⟩
      Ξ hΞ hnil ?_ ?_
    · intro X hX
      obtain ⟨A, hA, Bn, hB, rfl⟩ := hL k r z hz hT X hX
      simp only [mul_add, Matrix.trace_add, Complex.add_re]
      rw [hl A (Or.inl hA), hl Bn (Or.inr hB), add_zero]
    · intro X hX
      obtain ⟨A, hA, Bn, hB, rfl⟩ := hL k r z' hz' hT' X hX
      simp only [mul_add, add_mul, Matrix.trace_add, Complex.add_re]
      rw [hr A (Or.inl hA), hr Bn (Or.inr hB), add_zero]
  refine ⟨U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z'), fun g => u (κ (Φ g)), hU', ⟨hg₀U, hΦg₀⟩, ?_, ?_⟩
  · exact hsm.comp (hΦ.mono Set.inter_subset_left) (fun g hg => hg.2)
  · intro g hg hgG
    show u g = u (κ (Φ g))
    rw [(hΦU g hg.1 hgG.1).2]

theorem jfSmoothBuilt_of_leaves (hN : NDiff) (hU : UCap) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hK : GChart)
    (hE : ChartEqs) (hW : ClassToWeak) (hR : EllRegW) (hSym : JfS.SymbolNil) (hL : LieSsetSplit) :
    JfSmoothBuilt :=
  transfer_smooth_of_regularity (gRegJ_of hN hU hP hC (gRegScalar_of hK hE hW hR hSym hL))

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Matrix MeasureTheory Topology
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem averaging_properness_holds : ACProper := by
  intro k r Wp Wq _ _ _ _ D C C' hC hC' hC'O
  have hW : IsCompact (UWset k r D.z) := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z D.z_mem D.T_pos
  have hW' : IsCompact (UWset k r D.z') := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z' D.z'_mem D.T'_pos
  have hgc : Continuous (B.gN : B.Mat k r → ℝ) := Formalism.FourierDecayAlt.P.B6.gN_continuous
  obtain ⟨MW, hMW⟩ := hW.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨MW', hMW'⟩ := hW'.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨MC, hMC⟩ := hC.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨Co, hCo0, hCo⟩ := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.orbit D.z D.z' C' hC' hC'O
  have gN_nn : ∀ M : B.Mat k r, 0 ≤ B.gN M := fun M => Real.sqrt_nonneg _
  have bnd : ∀ {s : Set (B.Mat k r)} {M : ℝ}, (∀ x ∈ s, ‖B.gN x‖ ≤ M) → ∀ x ∈ s, B.gN x ≤ M :=
    fun h x hx => (le_abs_self _).trans (h x hx)
  set Bd : ℝ := max MW 0 * max MC 0 * max MW' 0 with hBd
  set R : ℝ := max (max MW MW') (Co * Bd ^ (2 * r + 1)) with hR
  refine ⟨Metric.closedBall 0 (max R 0), isCompact_closedBall _ _, ?_⟩
  intro p hp g hg hsg
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  set h : B.Mat k r := Matrix.of p.1.1
  set n : B.Mat k r := Matrix.of p.1.2
  set h' : B.Mat k r := Matrix.of p.2.1
  set n' : B.Mat k r := Matrix.of p.2.2
  have hdet : IsUnit h.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have hdet' : IsUnit h'.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh'.1
  have hx : n⁻¹ * g * n' = h * B.sgs p g * h'⁻¹ := by
    have e1 : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have e2 : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet'
    calc n⁻¹ * g * n' = (h * h⁻¹) * (n⁻¹ * g * n') * (h' * h'⁻¹) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = h * (h⁻¹ * n⁻¹ * g * n' * h') * h'⁻¹ := by simp only [Matrix.mul_assoc]
  have hb : B.gN (n⁻¹ * g * n') ≤ Bd := by
    rw [hx]
    have h1 := bnd hMW h hh
    have h2 := bnd hMC _ hsg
    have h3 := bnd hMW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh')
    calc B.gN (h * B.sgs p g * h'⁻¹) ≤ B.gN (h * B.sgs p g) * B.gN h'⁻¹ := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ B.gN h * B.gN (B.sgs p g) * B.gN h'⁻¹ :=
        mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) (gN_nn _)
      _ ≤ max MW 0 * max MC 0 * max MW' 0 :=
        mul_le_mul (mul_le_mul (h1.trans (le_max_left _ _)) (h2.trans (le_max_left _ _)) (gN_nn _) (le_max_right _ _))
          (h3.trans (le_max_left _ _)) (gN_nn _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
  have hBd0 : 0 ≤ Bd := by positivity
  have hpow : B.gN (n⁻¹ * g * n') ^ (2 * r + 1) ≤ Bd ^ (2 * r + 1) := pow_le_pow_left₀ (gN_nn _) hb _
  obtain ⟨hon, hon'⟩ := hCo g hg n hn n' hn'
  have hnR : B.gN n ≤ max R 0 :=
    (hon.trans (mul_le_mul_of_nonneg_left hpow hCo0)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hn'R : B.gN n' ≤ max R 0 :=
    (hon'.trans (mul_le_mul_of_nonneg_left hpow hCo0)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hhR : B.gN h ≤ max R 0 :=
    (bnd hMW h hh).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hh'R : B.gN h' ≤ max R 0 :=
    (bnd hMW' h' hh').trans ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have sup : ∀ x : Mt k r, ‖x‖ ≤ B.gN (Matrix.of x) := fun x => Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.sup_le_gN (Matrix.of x)
  rw [mem_closedBall_zero_iff]
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · exact (sup _).trans hhR
  · exact (sup _).trans hnR
  · exact (sup _).trans hh'R
  · exact (sup _).trans hn'R

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem normC_one (w : List C.Letter) : TBB.normC (fun _ => (1 : ℝ)) w = 1 := by
  unfold TBB.normC
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]


end place

theorem nfHyp_mono {Cb c c' : ℝ} {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A₀ : ℝ} {p₀ : ℕ} {χ χ' : ℝ → ℝ} {N : ℕ}
    (h : NFHyp Cb c p f A₀ p₀ χ N) (hc : c' ≤ c) (hχ' : C6.IsCut0 χ') : NFHyp Cb c' p f A₀ p₀ χ' N := by
  obtain ⟨-, a2, a3, a4, a5, a6⟩ := h
  refine ⟨hχ', a2, a3, a4, le_trans ?_ a5, a6⟩
  have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
    positivity
  have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) =
      x * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) :=
    fun x => by ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_right hc hX


end

end Formalism.FourierDecayAlt.P.CutBP
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def NFOpOK (C : ℝ) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (N : ℕ) (Th : B.DiffOp P.k P.r Wp Wq) : Prop :=
  B.SmoothCoef (B.GPos p.T.base) Th ∧ B.Commutes p.T.base (B.GPos p.T.base) Th ∧
    CutMP.GlobCoef Th (C * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1)) ∧
    (B.opOrder Th : ℝ) ≤ C * CutMP.nDim P.k P.r * ((N : ℝ) + 1)

def NFDomZero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ),
    ¬ (D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) → topD p H w c = 0

def NFDomMeas : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
      AEStronglyMeasurable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w)
        volume

theorem domination_at_zero_holds : NFDomZero := by
  intro Wp Wq _ _ _ _ _ _ P p H w c hc
  unfold topD TBB.Ew TBB.NP KB.Pl.RR
  generalize TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) = a
  generalize TBB.normC (fun x => 1) w = b
  generalize TBB.bigPt P.r c = x at hc ⊢
  unfold D.RRplace
  by_cases hl : D.IsLocPt x (P.r + 1)
  · have hG : ¬ 0 < TBB.Gp p x := fun h => hc ⟨hl, h⟩
    rw [dite_eq_left ⟨hl, hl⟩, dite_eq_right (by omega)]
    have hv : ∀ H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp), D.vecV p.T.base p.ν' p.m₀ H' x = 0 := by
      intro H'
      unfold D.vecV
      rw [dite_eq_right]
      rintro ⟨-, h⟩
      apply hG
      unfold TBB.Gp
      exact h
    have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      ext i
      simp
    have hi0 : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
      simp [B.hsInner, h0]
    simp [hv]
    split_ifs with hw
    · simp [hi0]
    · unfold Top.topOf
      simp [hv, hi0]
  · simp [hl]

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

theorem jDHatOpQQ_of_opA_opR_residue_splitting (hA : JDOpA) (hR : JDOpR) (h1 : ResidueSplittingModelAlgebra) (h2 : MirrorResidueSplittingModelAlgebra)
    (h3 : JDHatLagrange) (h4 : JDHatNodes) : JDHatOpQQ := by
  obtain ⟨KA, hKA, hA⟩ := hA
  obtain ⟨KR, hKR, hR⟩ := hR
  refine ⟨max KA KR, le_max_of_le_left hKA, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr _ hGQ hML X hX
  have hAat := hA (max KA KR) (le_max_left _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hML
  have hRat := hR (max KA KR) (le_max_right _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGQ hML
  have hAh : ∀ y, HReal (max KA KR) S T v e L (L.Ahat y) := fun y => by
    obtain ⟨Θ, _, hΘ, _, hJ⟩ := hAat y
    exact hReal_op Θ hΘ fun J hJ' => (hJ J hJ').1
  have hAhv : ∀ y, HReal (max KA KR) S T v e L (L.Ahatv y) := fun y => by
    obtain ⟨_, Θv, _, hΘv, hJ⟩ := hAat y
    exact hReal_op Θv hΘv fun J hJ' => (hJ J hJ').2
  have hRh : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhM (D.parOf S v) L y) := fun y => by
    obtain ⟨Θ, _, hΘ, _, hJ⟩ := hRat y
    exact hReal_op Θ hΘ fun J hJ' => (hJ J hJ').1
  have hRhv : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhvM (D.parOf S v) L y) := fun y => by
    obtain ⟨_, Θv, _, hΘv, hJ⟩ := hRat y
    exact hReal_op Θv hΘv fun J hJ' => (hJ J hJ').2
  have hx : ∀ y, xInvM (D.parOf S v) y ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) :=
    fun y => jdh_kap_mem _ L _
  obtain ⟨ν, hνi, hνr⟩ := h4 (D.parOf S v)
  have hR0n : ∀ j, HReal (max KA KR) S T v e L (L.R0 (ν j)) := fun j => by
    rw [h1 _ L hML _ (hνr j)]
    refine hReal_sub (hReal_mul (hx _) (hRh _)) (hReal_sum _ _ fun l hl => ?_)
    exact hReal_mul (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hx _) (jdh_SSn_mem _ L l hl))
      (jdh_kap_mem _ L _)) (hAh _)
  have hR0vn : ∀ j, HReal (max KA KR) S T v e L (L.R0v (ν j)) := fun j => by
    rw [h2 _ L hML _ (hνr j)]
    refine hReal_sub (hReal_mul (hx _) (hRhv _)) (hReal_sum _ _ fun l hl => ?_)
    exact hReal_mul (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hx _) (jdh_kap_mem _ L _))
      (jdh_SSns_mem _ L l hl)) (hAhv _)
  have key : HReal (max KA KR) S T v e L X := by
    simp only [MA.hatSet, Set.mem_union, Set.mem_range] at hX
    rcases hX with ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩
    · exact hAh y
    · rw [(h3 _ L ν hνi y).1]
      exact hReal_sum _ _ fun j _ => hReal_smul _ (hR0n j)
    · exact hAhv y
    · rw [(h3 _ L ν hνi y).2]
      exact hReal_sum _ _ fun j _ => hReal_smul _ (hR0vn j)
  exact key

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

def JAAssembleQQ : Prop :=
  JDHatOpQQ → JDHatBdd → JDJComm → JDCCLower → TransferSquareIntegrable → BoundedOperatorsSquareIntegrable → JABddOpQQ → JABddStar → JAIsAdj → JAPhiOp →
    JAStarOp → JAGroupAdj → JALocCC → JAFFStable → JAdjTrQQ

theorem jAdjTrQQ_of_leaves (hA : JAAssembleQQ) (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp)
    (h12 : JAGroupAdj) (h13 : JALocCC) (h14 : JAFFStable) : JAdjTrQQ :=
  hA h1 hat_bounded_decay_holds transfer_commutation_holds class_lower_decay_holds transfer_square_integrable_holds bounded_operators_square_integrable h7 transfer_star_bound_holds transfer_is_adjoint_holds phi_operator_transfer_holds h11
    h12 h13 h14

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end
