module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle344
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle373
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle550
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle552
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle259
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle260
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle658
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle688
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle450
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselFlatMapEquivariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle574
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.exists_cmSplitPoint_at_place_over_split : ∀ (D : D7) (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → D.host.F = maximalRealSubfield D.host.E → ∃ p : GlobalTheory.FinPl.SplitPt D (Kw w), p.e = e ∧ p.v = w.under (𝓞 D.host.F) ∧ ∀ a : AE D, p.pr a = cpt w (Lev.swapAE D (finPart D a)) := by
  first | exact @GlobalTheory.SplitPtAtPlace.exists_splitPt_cpt | exact GlobalTheory.SplitPtAtPlace.exists_splitPt_cpt | (intros; apply GlobalTheory.SplitPtAtPlace.exists_splitPt_cpt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlace.CombAll

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_form (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {y : WO S T}
    (hy : IsHalf (cA D p.e) y) : ∃ b : Matrix Y Y' k, ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  set N : Matrix (Fin S.rank) (Fin T.rank) k := (y.map fun a => p.π (cA D a)).transpose with hN
  have hyN : y = N.transpose.map fun a => cA D (p.ι a) := by
    ext i j
    simp only [hN, Matrix.transpose_transpose, Matrix.map_apply, p.ι_π, map_mul, Formalism.L2.Theta.cA_cA]
    exact (hy i j).symm
  refine ⟨(FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D))) * FT.β).transpose, fun t => ?_⟩
  rw [hyN, GlobalTheory.LocSympl.pi_hO_up]
  rw [show (S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * (FT.β * t * FS.γ) =
      ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * FT.β * t) * FS.γ by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  rw [show FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * FT.β * t) =
      (FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D))) * FT.β) * t by
    simp only [Matrix.mul_assoc]]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem exists_heis (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (O : SB (Matrix Y Y' k)) {u : WO S T}
    (hu : IsHalf (p.e + cA D p.e) u) :
    ∃ Φ : SB (Matrix Y Y' k), ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = heisO ψ S T u (Tm O) := by
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψk hcont hne
  have h1 := p.split.1
  have h1' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, h1]
  set x := p.down FS FT u with hx
  set y : WO S T := cA D p.e • u with hyd
  have hy : IsHalf (cA D p.e) y := fun i j => by
    simp only [hyd, Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc, h1']
  have hux : p.up FS FT x = p.e • u := by
    rw [hx]
    unfold Place.down Place.up
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    exact p.ι_π _
  have hsum : y + p.up FS FT x = u := by
    rw [hux]
    ext i j
    simp only [hyd, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← add_mul, add_comm]
    exact hu i j
  obtain ⟨b, hb⟩ := exists_form p FS FT hy
  let Φx : SB (Matrix Y Y' k) := ⟨fun t => O.1 (t + x), GlobalTheory.LocComb.trans_mem_SB O.2 x⟩
  let Φm : SB (Matrix Y Y' k) := ⟨fun t => GlobalTheory.LocMod.Inhab.pairing ψk t b * Φx.1 t, GlobalTheory.LocComb.modul_mem_SB hd Φx.2 b⟩
  refine ⟨ψ (-symplOH S T y (p.up FS FT x)) • Φm, fun Tm h => ?_⟩
  have e1 : Tm Φx = heisO ψ S T (p.up FS FT x) (Tm O) := h.trans x O Φx fun _ => rfl
  have e2 : Tm Φm = heisO ψ S T y (Tm Φx) := h.modul y hy Φx Φm fun t => by
    show GlobalTheory.LocMod.Inhab.pairing ψk t b * Φx.1 t = _
    rw [GlobalTheory.LocSympl.psi_sympl_up p FS FT ψ ψk hψk t y, hb t]
    rfl
  have e3 := GlobalTheory.PlaceModel.heisL_heisL S T ψ y (p.up FS FT x) (Tm O)
  change heisO ψ S T y (heisO ψ S T (p.up FS FT x) (Tm O)) =
    ψ (symplOH S T y (p.up FS FT x)) • heisO ψ S T (y + p.up FS FT x) (Tm O) at e3
  rw [map_smul, e2, e1, e3, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul, hsum]

end GlobalTheory.FlatPlace.CombAll

namespace GlobalTheory.FlatPlace

theorem isCombAt_of_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (c : WO S T →₀ ℂ), (∀ u ∈ c.support, IsHalf (p.e + cA D p.e) u) → ∀ T₀, p.IsModel ψ FS FT T₀ → ∀ O Ξ : SB (Matrix Y Y' k), IsOne O → T₀ O ≠ 0 → T₀ Ξ = comb ψ S T c (T₀ O) → p.IsCombAt ψ FS FT c Ξ.1 := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT c hc T₀ hT₀ O Ξ hO hT₀O hΞ
  classical
  have hA : ∀ u : c.support, ∃ Φ : SB (Matrix Y Y' k), ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = heisO ψ S T u (Tm O) :=
    fun u => CombAll.exists_heis p ψ hψ FS FT O (hc u u.2)
  choose Φ hΦ using hA
  let Ξ' : SB (Matrix Y Y' k) := ∑ u : c.support, c u • Φ u
  have hΞ' : ∀ Tm, p.IsModel ψ FS FT Tm → Tm Ξ' = comb ψ S T c (Tm O) := fun Tm h => by

    simp only [Ξ', map_sum, map_smul, fun u => hΦ u Tm h]
    rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum]
    exact Finset.sum_coe_sort c.support (fun u => c u • heisO ψ S T u (Tm O))
  have hinj : Ξ = Ξ' := by
    by_contra hne
    have h0 : Ξ - Ξ' ≠ 0 := sub_ne_zero.2 hne
    have e1 : T₀ (Ξ - Ξ') = ((0 : ℂ) • T₀) (Ξ - Ξ') := by
      rw [map_sub, hΞ, hΞ' T₀ hT₀, sub_self, LinearMap.smul_apply, zero_smul]
    have e2 := (GlobalTheory.LocModU.localModel_uniq_transport_exist D k p Y Y' S T FS FT ψ hψ).1 T₀ ((0 : ℂ) • T₀) hT₀
      (GlobalTheory.LocMod.Witness.isModel_smul p hT₀ 0) _ h0 e1
    apply hT₀O
    rw [e2, zero_smul, LinearMap.zero_apply]
  refine ⟨hc, fun Tm h Φ₀ Φ' h1 h2 => ?_⟩
  have e2 : Φ' = Ξ' := by rw [← hinj]; exact Subtype.ext h2
  have e3 : Φ₀ = O := Subtype.ext (h1.trans hO.symm)
  rw [e2, e3, hΞ' Tm h]

end GlobalTheory.FlatPlace
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.LocMod.Witness

theorem exists_isModel_of_isThetaAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), (∀ x, p.up FS FT x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔ ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation k)) → ∀ f₀ φ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ φ f → ∃ Tm, p.IsModel ψ FS FT Tm ∧ (∀ O, IsOne O → Tm O = f₀) ∧ ∃ Φ : SB (Matrix Y Y' k), (∀ x, Φ.1 x = φ (p.up FS FT x)) ∧ Tm Φ = f := by
  classical
  intro D k _ _ _ _ p ψ hψ S T ΛS ΛT hS hT Y Y' _ _ _ _ FS FT hlat f₀ φ f hf₀ hφ hθ
  obtain ⟨⟨T₀, h₀⟩, hall⟩ := hθ
  have hf : f = T₀ φ := hall T₀ h₀

  have hNk : ∀ N : ℕ, 0 < N → (N : k) ≠ 0 := fun N hN h => by
    have h1 : prH p (N : D.host.E) = 0 := by rw [map_natCast]; exact h
    have h2 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    exact h2 ((map_eq_zero (prH p)).1 h1)
  obtain ⟨N, hN, hinv, hsupp⟩ := hφ.2
  have hN0 := hNk N hN
  have hA := lat_compact p FS FT hS hT
  have hAo := lat_open p FS FT hS hT
  generalize hAd : ((latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True).comap (upH p FS FT) : AddSubgroup _) = A at hA hAo
  have memA : ∀ x, x ∈ A ↔ p.up FS FT x ∈ (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) := fun x => by
    rw [← hAd]; rfl
  have hup_smul : ∀ x : Matrix Y Y' k, p.up FS FT (N • x) = N • p.up FS FT x := fun x => map_nsmul (upH p FS FT) N x
  have hNx : ∀ x : Matrix Y Y' k, (N : k) • x = N • x := fun x => Nat.cast_smul_eq_nsmul k N x

  let g : Matrix Y Y' k → ℂ := fun x => φ (p.up FS FT x)
  have hlc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : IsOpen ((fun y : Matrix Y Y' k => (N : k)⁻¹ • (y - x)) ⁻¹' (A : Set (Matrix Y Y' k))) :=
      hAo.preimage ((continuous_const_smul ((N : k)⁻¹)).comp (continuous_id.sub continuous_const))
    have hx : x ∈ ((fun y : Matrix Y Y' k => (N : k)⁻¹ • (y - x)) ⁻¹' (A : Set (Matrix Y Y' k))) := by
      simp only [Set.mem_preimage, sub_self, smul_zero]; exact A.zero_mem
    filter_upwards [hU.mem_nhds hx] with y hy
    have hy' : (N : k)⁻¹ • (y - x) ∈ A := hy
    have e1 : y = x + N • ((N : k)⁻¹ • (y - x)) := by
      rw [← hNx, smul_smul, mul_inv_cancel₀ hN0, one_smul, add_sub_cancel]
    change φ (p.up FS FT y) = φ (p.up FS FT x)
    rw [e1, up_add, hup_smul]
    exact hinv _ ((memA _).1 hy') (up_half p FS FT _) _
  have hcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (hA.image (continuous_const_smul (N : k)⁻¹)) fun x hx => ?_
    by_contra h
    apply hx
    have h1 := hsupp _ h
    rw [← hup_smul, ← memA] at h1
    refine ⟨N • x, h1, ?_⟩
    change (N : k)⁻¹ • (N • x) = x
    rw [← hNx, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  let Φ : SB (Matrix Y Y' k) := ⟨g, hlc, hcs⟩

  have hext : ∀ Ψ : SB (Matrix Y Y' k), IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) (ext p FS FT Ψ) :=
    ext_sb p FS FT hS hT
  refine ⟨T₀.comp (ext p FS FT), ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩, fun O hO => ?_, Φ, fun x => rfl, ?_⟩
  · exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T _ _ hS hT p.e p.split.1 (GlobalTheory.PlaceCoord.infPart_split p.split)
      _ hf₀ T₀ h₀ _ (hext Ψ)
  · refine Eq.trans (congrArg T₀ ?_) (h₀.trans _ (hext Ψ) _ (up_half p FS FT x))
    funext t
    rw [ext_apply, ext_apply, down_add, down_up, h]
    exact if_congr (half_add (up_half p FS FT x)).symm rfl rfl
  · refine Eq.trans (congrArg T₀ ?_) (h₀.modul _ (hext Ψ) _ hy)
    funext t
    rw [ext_apply, ext_apply, h]
    split_ifs with ht
    · rw [up_down p FS FT ht]
    · rw [mul_zero]
  · have e1 : ext p FS FT O = (1 : ℂ) • halfInd p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) := by
      funext t
      rw [one_smul, ext_apply, halfInd]
      by_cases ht : IsHalf p.e t
      · rw [if_pos ht, hO, Set.indicator_apply]
        refine if_congr ?_ rfl rfl
        rw [and_iff_left ht, ← up_down p FS FT ht, down_up, hlat]
        rfl
      · rw [if_neg ht, if_neg fun h => ht h.2]
    change T₀ (ext p FS FT O) = f₀
    rw [e1]
    exact h₀.vac
  · change T₀ (ext p FS FT Φ) = f
    rw [hf]
    congr 1
    funext t
    rw [ext_apply]
    split_ifs with ht
    · change φ (p.up FS FT (p.down FS FT t)) = φ t
      rw [up_down p FS FT ht]
    · by_contra h
      exact ht (hφ.1 t (Ne.symm h))

end GlobalTheory.LocMod.Witness
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.Chain (ptOf)
open GlobalTheory.Chain.RealIt (glue)

namespace GlobalTheory.EvenOntoRealZeta


open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction in
theorem realZeta : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, RealZeta D := by
  intro hDS hHC D c hc k hk s s' hs hs' p hp m X hmX
  have hvac := hp.pre.vac
  have hW := hp.pre.weil
  have hArch := fun τ =>
    (GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions hDS hHC D c.t (s.par τ) (s'.par τ) (c.a k τ) (c.a k τ) (hp.pre.par τ)).1 τ s.V s'.V
  have hfock : ∀ τ, IsFockAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f :=
    fun τ => ⟨hc.inf, isAdapted_model s.M τ, isAdapted_model s'.M τ, hvac.theta, hvac.ne, hvac.vac τ⟩
  have hLL := fun τ => (hArch τ).1 c.ψ c.θ (c.χ k) (c.χ k) p.ω hW (hc.exp k hk τ) (hc.exp k hk τ)
    s.par s'.par s.M s'.M rfl rfl _ _ p.f (hfock τ)
  have hZL := fun τ => (hArch τ).2 c.ψ c.θ (c.χ k) (c.χ k) p.ω hW (hc.exp k hk τ) (hc.exp k hk τ)
    s.par s'.par s.M s'.M rfl rfl _ _ p.f (hfock τ) m X hmX.1 hmX.2.1
  choose Φ hΦ using fun τ => (hLL τ).joint_ex
  choose w hwsm hwk hwhi using fun τ => GlobalTheory.T.exists_smooth_kFinite_unit_highestWeight_vector hHC D s.V s.par s.M τ
  refine ⟨glue Φ, fun τ => ⟨w τ, hwsm τ⟩, fun τ => hwk τ, ?_⟩
  intro mR hmR z
  have hfac := GlobalTheory.T.thetaInner_fockProduct_eq_prod_realPlaces D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ (c.χ k) (c.χ k) p.ω hc.inf hW m X hmX p.f hvac
  obtain ⟨cst, hcst, hhaar⟩ := GlobalTheory.T.integral_realUnitary_haar_eq_prod_Upq_haar D s.V s.par s.M c.θ hc.inf mR (fun τ => Formalism.REAL.muG (s.M.ε τ)) hmR
    (fun τ => inferInstance)
  have hZ := fun τ => hZL τ (Φ τ) (hΦ τ) ⟨w τ, hwk τ⟩ (hwhi τ) (Formalism.REAL.muG (s.M.ε τ)) inferInstance
  set i0 := ipTh m X p.f p.f with hi0
  set F : D.what₂.Tau → Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ → ℂ := fun τ h =>
    ipTh m X (p.ω (atTau c.θ s.V τ h, 1) (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
      (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) / i0 *
      conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ with hF
  have hrep : ∀ τ (Y : Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ), s.M.rep τ (ofFr s.M τ Y) = s.M.σ τ Y := by
    intro τ Y
    have h1 : s.M.fr τ * (s.M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (s.M.fr_unit τ))
    have : s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹ = Y := by
      calc s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹
          = (s.M.fr τ * (s.M.fr τ)⁻¹) * Y * (s.M.fr τ * (s.M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
        _ = Y := by rw [h1]; simp
    simp only [DSModel.rep, ofFr, this]
  have hFu : ∀ τ (u : Formalism.REAL.UJ (s.M.ε τ)), F τ (ofFr s.M τ (umat u)) =
      ipTh m X (actSrc c.θ p.ω τ (ofFr s.M τ (umat u))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) *
        star (coefOn (s.M.σ τ) (w τ) (w τ) u) / i0 := by
    intro τ u
    simp only [hF, hrep, actSrc, coefOn, starRingEnd_apply]
    ring
  have hFint : ∀ τ, Integrable (fun u : Formalism.REAL.UJ (s.M.ε τ) => F τ (ofFr s.M τ (umat u))) (Formalism.REAL.muG (s.M.ε τ)) := by
    intro τ; simp_rw [hFu]; exact (hZ τ).2.1.div_const _
  have hFval : ∀ τ, ∃ r : ℝ, 0 < r ∧ ∫ u, F τ (ofFr s.M τ (umat u)) ∂(Formalism.REAL.muG (s.M.ε τ)) = (r : ℂ) / i0 := by
    intro τ
    obtain ⟨r, hr, hrI⟩ := (hZ τ).2.2.1
    refine ⟨r, hr, ?_⟩
    simp_rw [hFu]; rw [integral_div, hrI]
  choose r hr hrI using hFval
  have hi0 : i0 ≠ 0 := hfac.1
  have hz : ∀ g : GinfC s.V, z g = i0 * ∏ τ, F τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) := by
    intro g
    have h := hfac.2 Φ g g.2
    change ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
      conj (∏ τ, ⟪(w τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) = _
    rw [h, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
  obtain ⟨hIint, hIval⟩ := hhaar F hFint
  have hintz : ∫ g, z g ∂mR = i0 * ((cst : ℂ) * ∏ τ, ((r τ : ℂ) / i0)) := by
    simp_rw [hz]; rw [integral_const_mul, hIval]; simp_rw [hrI]
  refine ⟨?_, ?_⟩
  · rw [hintz]
    exact mul_ne_zero hi0 (mul_ne_zero (by exact_mod_cast hcst.ne')
      (Finset.prod_ne_zero_iff.2 fun τ _ => div_ne_zero (by exact_mod_cast (hr τ).ne') hi0))
  · intro a ha hfr
    have htpos : 0 < c.t := by have := hc.step; omega
    refine ⟨0, div_pos (by exact_mod_cast htpos) two_pos, ?_⟩
    obtain ⟨C, hC⟩ := GlobalTheory.T.realMatrixCoeff_fockVectors_le_doublingHeight_pow D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ (c.χ k) (c.χ k) p.ω hc.inf hW m X hmX p.f hvac
      a ha hfr (glue Φ) (glue Φ)
    set mf : GinfC s.V → ℂ := fun g => conj (∏ τ, ⟪(w τ : s.M.H τ),
      s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) with hmf
    have hmint : Integrable mf mR := by
      obtain ⟨hI2, -⟩ := hhaar (fun τ h => conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ) (fun τ => by
        simp only [hrep]
        exact (hZ τ).1.norm.mono' (hZ τ).1.1.star (Filter.Eventually.of_forall fun x => (RCLike.norm_conj _).le))
      simpa [hmf, map_prod] using hI2
    set Hf : GinfC s.V → ℝ := fun g => ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w
      (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (g : GA D s.V)) with hHf
    have hHc : Continuous Hf := continuous_finsetProd _ fun w _ =>
      (GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).1.comp ((GlobalTheory.AdelicU.continuous_projArch _ _ w).comp continuous_subtype_val)
    have hHpos : ∀ g, 0 < Hf g ∧ Hf g ≤ 1 := fun g =>
      ⟨Finset.prod_pos fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).1,
        Finset.prod_le_one₀ (fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).1.le)
          fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).2⟩
    have hzint : Integrable z mR :=
      (hIint.const_mul i0).congr (Filter.Eventually.of_forall fun g => (hz g).symm)
    have htb : c.t ≤ s'.V.rank := by
      rw [hs'.rank]; nlinarith
    have hbd : ∀ g, ‖z g‖ ≤ C * Hf g ^ ((s'.V.rank : ℝ) / 2) * ‖mf g‖ := by
      intro g
      change ‖ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
        mf g‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC g g.2) (norm_nonneg _)
    exact GlobalTheory.T.integrable_mul_heightPow_of_bounded_factor mR z mf Hf C s'.V.rank c.t hzint hmint hHc hHpos htb hbd

end GlobalTheory.EvenOntoRealZeta
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.OneCosetBFPlace

theorem one_coset_place : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), (∃ u : UX D ρ, ∃ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (Formalism.L2.Theta.mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a)) → ∃ r ∈ Rgrp (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h)), r ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ g = r * k := by
  intro D hq T L μ hL sc G W M hM F hF ρ h v hv g hg hc
  obtain ⟨u, a, ha, hc⟩ := hc
  obtain ⟨k, hk, hkv, hm⟩ := GlobalTheory.T.besselStep_orbit_at_badPlace_eq_congruenceTranslate D hq T L μ hL sc G W M hM F hF ρ h v hv g hg u a ha hc
  obtain ⟨r, hr, hrv, rfl⟩ := GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move _ _ _ g k u hg hkv hm
  exact ⟨r, hr, hrv, k⁻¹, inv_mem hk, inv_mem hkv, rfl⟩

end GlobalTheory.OneCosetBFPlace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.jacobiToBesselFlatMap_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ Ψ, IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀), ∀ n ∈ flagN B.d, ∀ h : GA D B.A, flFB s (s.om (J.d.emb0 g, n * embA B.d B.o h) Ψ) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • s.om₀ (g, B.o.emb (h, 1)) (flFB s Ψ) := by
  first | exact @GlobalTheory.AscFlatEquiFB.flFB_equivariant | exact GlobalTheory.AscFlatEquiFB.flFB_equivariant | (intros; apply GlobalTheory.AscFlatEquiFB.flFB_equivariant <;> assumption)
end
