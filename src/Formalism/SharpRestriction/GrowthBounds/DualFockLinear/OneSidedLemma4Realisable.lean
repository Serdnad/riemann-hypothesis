module

public import Formalism.SharpRestriction.GrowthBounds.TableLineDegreeFive
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeneratorImageIsSymbol
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.CoeUntopDLeAlt
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.DvDegOtherMono
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.FixedSymbolFactorIntegral
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeOldest
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.LeadingDepthOneMemClosure
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.Lemma4OfRemainingStatements
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.LetterWeightPos
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.MdWeightMapDomain
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.SymbolGeneratorData
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideExplicitIdentification
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableIffGeneralRank
import Formalism.PolynomialDimension.DetMulEqSumAdjugate
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

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4OfAdmittedTheoremII, Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4Realisable

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4OfAdmittedTheoremII =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4OfAdmittedTheoremII", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.TableLineDegreeFive\npublic import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeneratorImageIsSymbol\nimport Formalism.PolynomialDimension.DetMulEqSumAdjugate\npublic import Formalism.SharpRestriction.GrowthBounds.PathWeight.CoeUntopDLeAlt\npublic import Formalism.SharpRestriction.GrowthBounds.PathWeight.DvDegOtherMono\npublic import Formalism.SharpRestriction.GrowthBounds.PathWeight.FixedSymbolFactorIntegral\npublic import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeOldest\npublic import Formalism.SharpRestriction.GrowthBounds.PathWeight.LeadingDepthOneMemClosure\npublic import Formalism.SharpRestriction.GrowthBounds.PathWeight.Lemma4OfRemainingStatements\npublic import Formalism.SharpRestriction.GrowthBounds.PathWeight.LetterWeightPos\npublic import Formalism.SharpRestriction.GrowthBounds.PathWeight.MdWeightMapDomain\npublic import Formalism.SharpRestriction.GrowthBounds.PathWeight.SymbolGeneratorData\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

def OneSidedLemma4 (_D : Formalism.BasicNotions.D7) (CLa CD Csz : ℝ) : Prop :=
  Conclusion6With (fun d l => d ≤ l + l / 100) _D CLa CD Csz

def RestGeomU : Prop :=
  RestGeomWith (fun d l => d ≤ l + l / 100)

def RestDivMU (CLa CD Csz : ℝ) : Prop :=
  RestDivMWith (fun d l => d ≤ l + l / 100) CLa CD Csz

theorem restGeomU : RestGeomU := by
  exact _root_.Formalism.MainNotions.G.symbolGeneratorData.restGeom_of_upper_bound

theorem restDivMU (hE : FieldMultidegreeDivisibility) : ∃ C : ℝ, 1 ≤ C ∧ (RestGeomU → RestDivMU C (C + 1) C) := by
  exact restDivM_of_degree_bound (fun d l => d ≤ l + l / 100) hE

theorem one_sided_lemma4_of_interfaces (D : Formalism.BasicNotions.D7) (CLa CD Csz : ℝ) (hModel : RestModel) (hDiv : RestDivMU CLa CD Csz)
    (hW1 : GeneratorSpanInclusion) (hW2 : GeneratorImageIsSymbol) (hMon : RestMon) (hPh : RestPh) : OneSidedLemma4 D CLa CD Csz := by
  exact lemma4_of_remaining_statements_with (fun d l => d ≤ l + l / 100) D CLa CD Csz hModel hDiv hW1 hW2 hMon hPh

theorem one_sided_lemma4_of_admitted_lemmas : ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, StandardMonomialSpanBis D → PathPairCorrespondence D → admB2 D → admB3 D → CoefficientValuationLemma D → LargePrimeLengthVanishing D →
    OneSidedLemma4 D C (C + 1) C := by
  by_cases hE : FieldMultidegreeDivisibility
  · obtain ⟨C, hC, hD⟩ := restDivMU hE
    exact ⟨C, hC, fun D hA3 hB1 hB2 hB3 hC1 _ => one_sided_lemma4_of_interfaces D C (C + 1) C restModel (hD restGeomU)
      (generator_pair_conditions_of_admitted D hA3 hB1) (generator_path_homogeneous_holds D hB2 hB3 hC1) (restMon D) restPh⟩
  · exact ⟨1, le_rfl, fun D _ _ _ _ _ h => absurd h hE⟩

theorem one_sided_lemma4_of_admitted_theorem_II : ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ), tableLineDegreeFive.admitted D CLa Ck Crk Cdeg →
    OneSidedLemma4 D C (C + 1) C := by
  obtain ⟨C, hC, H⟩ := one_sided_lemma4_of_admitted_lemmas
  refine ⟨C, hC, fun D CLa Ck Crk Cdeg hA => ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h15, h16, h17, h18, _, h20, h21, _⟩ := hA
  exact H D h15 h16 h17 h18 h20 h21

end Formalism.MainNotions.TestSideCounting
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4OfAdmittedTheoremII =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4Realisable =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4Realisable", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideExplicitIdentification\npublic import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4OfAdmittedTheoremII\npublic import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableIffGeneralRank\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (kapR)

def kapFl (p k : ℕ) {n' : ℕ} (d : Fin n' → ℕ) : ℕ := ∑ s, k * Nat.log p (d s)

def MultDiv (O : Type) [CommRing O] (p κ : ℕ) {n' k : ℕ} (d : Fin n' → ℕ) : Prop :=
  ∀ α : Fin n' × Fin k →₀ ℕ, (∀ s, multideg α s = d s) →
    (((∏ s, (d s).factorial : ℕ) : ℕ) : O) ∣ (p : O) ^ κ * ((expFact α : ℕ) : O)

def OneSidedLemma4Element (p : ℕ) {n' r : ℕ} [NeZero n'] (K : ℕ) [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    (Fr : Frames n' r) (N₁ G' cP : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) {k : ℕ} (hk : k = r + K) (o : ℕ)
    (sig : MvPolynomial (TV n' k) (KK O)) : Prop :=
  ∃ (n : ℕ) (obd : ℤ → ℤ → ℝ) (xi : Fin n → ℤ → SegRing O r K) (dd : ℤ → ℤ → ℕ) (mon : Fin n' × Fin (r + K) →₀ ℕ),
    (∀ (i : Fin n) (j : ℕ), j < Fr.J →
      xi i j ∈ XX' O r K Fr j (fun _ => (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ))
        (fun x => Bo p Fr deg j x / 2 - sl p Fr deg Y (r + K) j x) (obd j) ∧
      xi i j ∈ restrictSupport O {mm | ∀ x ∈ Fr.letters j, ∑ c : Fin (r + K), mm (x, c) = dd j x}) ∧
    (∀ j : ℕ, j < Fr.J → ∀ x ∈ Fr.letters j, (Fr.IsW j x ∨ x ∈ Fr.LLset j) →
        (dd j x : ℝ) ≤ levDeg p Fr deg j x + levDeg p Fr deg j x / 100) ∧
    IsLabel p Fr mon ∧ (∀ v ∈ mon.support, v.1 ∈ Fr.TT) ∧
    (∀ mm ∈ (monPh O K p Fr mon xi).support, normDeg r mm = o) ∧
    sig = MvPolynomial.map (algebraMap O (KK O)) (rename (castVK hk) (monPh O K p Fr mon xi))

theorem one_sided_lemma4_realisable (D : Formalism.BasicNotions.D7) (CLa CD Csz : ℝ) (h6 : OneSidedLemma4 D CLa CD Csz) {p n' r K : ℕ} [Fact p.Prime] [NeZero n']
    [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF p n') O]
    (S : UniformizedDVR p O) (hO : OHyp p n' O S) {k : ℕ} (hk : k = r + K) (hH : CommonHypotheses p n' r k) (Fr : Frames n' r)
    (L₁ N₁ G' : ℕ) (hV : Fr.Valid L₁ N₁) (hT : TwistBound p Fr (p ^ G')) (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ)
    (c0 c'' cStar : ℕ) (Dd : ℝ) (hII : HypII CLa CD Csz p Fr k L₁ N₁ G' deg a Y c0 c'' cStar Dd)
    (g : Matrix (Fin k) (Fin k) (WF p n')) (hg : IsGLW g) (o : ℕ) (sig : MvPolynomial (TV n' k) (KK O))
    (hs : OneSidedLemma4Element p K O Fr N₁ G' (cPrime n' r Fr.TT.card c0 c'' cStar) deg Y hk o sig) :
    Realisable p n' S.w n' r g (cPrime n' r Fr.TT.card c0 c'' cStar) o sig := by
  subst hk
  obtain ⟨n, obd, xi, dd, mon, h1, h2, h3, h4, h5, rfl⟩ := hs
  have hren : rename (castVK (n' := n') (rfl : r + K = r + K)) (monPh O K p Fr mon xi) = monPh O K p Fr mon xi := by
    have : (castVK (n' := n') (rfl : r + K = r + K)) = id := by
      funext v
      rfl
    rw [this, rename_id_apply]
  rw [hren]
  exact h6 p n' r K O S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII g hg n obd xi dd h1 h2 mon h3 h4 o h5

section At

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
  [Algebra O Kf] [Algebra (WF p n') O] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) {j : W →+* O} (w : O) {m : ℕ} (r : ℕ)
  (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ)

def XiAt (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (Fr : Frames n' r) (N₁ G' : ℕ) (Y : ℝ)
    (c0 cP κ : ℕ) (bT bD : ℝ) (e : Edge W Qq (m + 1)) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ tF DX : ℕ, (tF : ℝ) ≤ bT ∧ (DX : ℝ) ≤ bD ∧
    ∀ F1 : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (F1 : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB →
      Θ F1 ∈ Re p ι σ w r (flW (dT TT lam0)) e →
      Θ F1 ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e) →
      ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
        (∀ q, o q ≤ tF ∧ HasMultideg (sig q) (dT TT lam0) ∧
          OneSidedLemma4Element p K O Fr N₁ G' cP (flatDeg lam0) Y hk (o q) (sig q)) ∧
        ValLe (Kf := KK O) (p : O) DX
          ((p : KK O) ^ κ * fock (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O))) (∑ q, sig q) /
            (((∏ s, (dT TT lam0 s).factorial : ℕ) : ℕ) : KK O))

def RealAt (hS : HidaSetting p n' W Qq O Kf ι σ j w) (cP κ : ℕ) (e : Edge W Qq (m + 1))
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ gv : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW gv ∧
    ∀ (o : ℕ) (sig : MvPolynomial (TV n' (m + 1)) (KK O)), HasMultideg sig (dT TT lam0) → InWj w sig 0 →
      Realisable p n' w n' r gv cP o sig →
      ∃ T : Module.Dual Kf (Vsp Kf (flW (m := m) (dT TT lam0))),
        T ∈ scale (algebraMap O Kf w ^ (-(o : ℤ))) (dualLat O Kf (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)) ∧
        T ∈ Re' p ι σ w r (flW (dT TT lam0)) e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          T ∈ scale (algebraMap O Kf w ^ (cP : ℤ)) (Re' p ι σ w r (flW (dT TT lam0)) e')) ∧
        ∀ F : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
          Θ F ∈ Re p ι σ w r (flW (dT TT lam0)) e →
          ∃ z : O, be p r (flW (dT TT lam0)) (Θ F) T =
            kapR hS ((p : KK O) ^ κ * fock (subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O))) sig /
              (((∏ s, (dT TT lam0 s).factorial : ℕ) : ℕ) : KK O)) + algebraMap O Kf (w ^ cP * z)

end At

def XiStep (C Ct0 CD CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        XiAt p n' ι σ w r TT lam0 K hk F (orbitWindowCount r de h x) (goodG' r de h x) Y c0 (cPrime n' r TT.card c0 cpp cStar)
          (kapFl p (m + 1) (dT TT lam0))
          (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0)
          (CD * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e g FsB Θ

def RealStep (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        RealAt p n' ι σ w r TT lam0 hSet.1 (cPrime n' r TT.card c0 cpp cStar) (kapFl p (m + 1) (dT TT lam0)) e g Θ

def RestXi (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CDf C₁ : ℝ, 0 < Ct0 ∧ 0 < CDf ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → XiStep C Ct0 CDf CLa

def RestReal (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → RealStep C CLa

end Formalism.MainNotions.TestSideCounting
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4Realisable =====
