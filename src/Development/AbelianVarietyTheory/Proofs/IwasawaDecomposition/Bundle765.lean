module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle035
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle686
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle733
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle764
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle756
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle744
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle725
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle724
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem datExt_of_hypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → DatExt :=
  fun h1 h2 h3 h4 h5 h6 h7 => datExt_of_datExt0 (GlobalTheory.T.adelicData_extend_largerFields_of_hypotheses h1 h2 h3 h4 h5 h6 h7)

end GlobalTheory.Mem.R3.Rw

end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.LieBase

theorem hasChernIntegral_covol_flagDeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult → HasChernIntegral Eb (openPart j) (lieGram e U hj f₀ A₀) R (GlobalTheory.TrueCx.covol (U.X k) * Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL la R hR
  have h3 := GlobalTheory.LieBase.hasChernIntegral_pointPoly_covol E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  have h := GlobalTheory.GoodMetric.hasChernIntegral_of_eq_mul Eb (openPart j) (lieGram e U hj f₀ A₀) R (pointPoly H Dw) _
    (GlobalTheory.TrueCx.covol (U.X k))
    (fun y hy c' hc A hA => GlobalTheory.PointHodge.pointwise_hodge E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
      la R hR y hy c' hc A hA) h3
  rw [mul_comm] at h
  convert h using 3

end GlobalTheory.LieBase
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.hodgeMetric_lieGram_isGood_mumford : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsGood Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  exact @GlobalTheory.LieBaseGood.lieGram_isGood
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_simpLab_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ φ lab : InvFun (𝓞 E), IsPolyFan H.bar q φ ∧ IsTwInv H φ ∧ IsTwInv H lab ∧ SimpLab H.bar q φ lab ∧ Subordinate H.bar q φ ψ := by
  intro E _ _ _ H q ψ hD hψ hT
  obtain ⟨lab, hlT, hlab⟩ := GlobalTheory.T.exists_invariant_carrierDim_polyFan E H q ψ hD hψ hT
  obtain ⟨N, hN⟩ := GlobalTheory.T.polFanCarrierDimension_bounded E H q ψ lab hlab
  have key : ∀ d : ℕ, ∃ φ : InvFun (𝓞 E), IsTwInv H φ ∧ IsBaryStage H.bar q ψ lab φ (N - d) := by
    intro d
    induction d with
    | zero => exact ⟨ψ, hT, isBaryStage_start hψ hN⟩
    | succ d ih =>
      obtain ⟨φ, hφT, hφ⟩ := ih
      rcases Nat.eq_zero_or_pos (N - d) with h | h
      · exact ⟨φ, hφT, by rw [show N - (d + 1) = N - d by omega]; exact hφ⟩
      · have e : N - d = (N - (d + 1)) + 1 := by omega
        rw [e] at hφ
        exact GlobalTheory.T.barycentricSubdivision_star_step_cells E H q ψ lab φ _ hD hψ hT hlT hlab hφT hφ
  obtain ⟨φ, hφT, hφ⟩ := key N
  rw [Nat.sub_self] at hφ
  exact ⟨φ, lab, hφ.1, hφT, hlT, GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero _ H.bar q ψ lab φ hlab hφ, hφ.2.1⟩

end GlobalTheory.PolFan
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Main

variable {O : Type} [CommRing O] {bar : O → O}

theorem maxMult_lt_of_among_zero {q M : ℕ} {φ : InvFun O} (hM : 1 ≤ M) (h : maxMult bar q φ ≤ M)
    (h0 : MultCellsAmong bar q φ M 0) : maxMult bar q φ < M := by
  obtain ⟨R, hR⟩ := h0
  have key : maxMult bar q φ ≤ ((M - 1 : ℕ) : ℕ∞) := by
    unfold maxMult
    refine iSup_le fun X => iSup_le fun i1 => iSup_le fun i2 => iSup_le fun i3 => iSup_le fun i4 => iSup_le fun hX =>
      iSup_le fun m => iSup_le fun δ => iSup_le fun hc => iSup_le fun hli => iSup_le fun hp => ?_
    have hle : ((cellMult bar fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) : ℕ∞) ≤ M := by
      refine le_trans ?_ h
      unfold maxMult
      exact le_iSup_of_le X <| le_iSup_of_le i1 <| le_iSup_of_le i2 <| le_iSup_of_le i3 <| le_iSup_of_le i4 <|
        le_iSup_of_le hX <| le_iSup_of_le m <| le_iSup_of_le δ <| le_iSup_of_le hc <| le_iSup_of_le hli <|
        le_iSup_of_le hp le_rfl
    have hne : cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≠ M := fun he =>
      (hR X hX m δ ⟨hc, hli, hp, he⟩).elim fun k _ => k.elim0
    have hle' : cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≤ M := by exact_mod_cast hle
    exact_mod_cast (show cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≤ M - 1 by omega)
  exact key.trans_lt (by exact_mod_cast (show M - 1 < M by omega))

end Main

theorem exists_round_lt_maxMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → maxMult H.bar q φ < ⊤ →
    2 ≤ maxMult H.bar q φ → ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧
      SimpLab H.bar q φ' lab' ∧ Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' < maxMult H.bar q φ := by
  intro E _ _ _ H q φ lab hD hP hT hL hS hfin h2
  set M := (maxMult H.bar q φ).toNat with hMdef
  have hMe : maxMult H.bar q φ = M := (ENat.coe_toNat hfin.ne).symm
  have hM2 : 2 ≤ M := by rw [hMe] at h2; exact_mod_cast h2
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_multCellsAmong_of_isPolyFan E H q φ hP M
  have key : ∀ (n : ℕ) (φ lab : InvFun (𝓞 E)), IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab →
      SimpLab H.bar q φ lab → maxMult H.bar q φ ≤ M → MultCellsAmong H.bar q φ M n →
      ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧ SimpLab H.bar q φ' lab' ∧
        Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' < M := by
    intro n
    induction n with
    | zero =>
      intro φ lab hP hT hL hS hle h0
      exact ⟨φ, lab, hP, hT, hL, hS, Subordinate.refl φ, maxMult_lt_of_among_zero (by omega) hle h0⟩
    | succ n ih =>
      intro φ lab hP hT hL hS hle h0
      obtain ⟨φ₁, lab₁, hP₁, hT₁, hL₁, hS₁, hs₁, hle₁, h₁⟩ := GlobalTheory.T.exists_starSubdivision_removes_maxMultiplicity_cells E H q φ lab hD hP hT hL hS M n hM2 hle h0
      obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := ih φ₁ lab₁ hP₁ hT₁ hL₁ hS₁ hle₁ h₁
      exact ⟨φ', lab', hP', hT', hL', hS', hs'.trans hs₁, hlt⟩
  obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := key n φ lab hP hT hL hS hMe.le hn
  exact ⟨φ', lab', hP', hT', hL', hS', hs', hMe ▸ hlt⟩

end GlobalTheory.PolFan
end
end
