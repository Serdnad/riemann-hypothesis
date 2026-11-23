module

public import Formalism.SharpRestriction.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ExportFamilies
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle020
public import Formalism.SharpRestriction.LevelLetterCocycles.PullbackLevelTwoToOne
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.RealExtOfExact
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ThmEFinal
public import Formalism.SharpRestriction.LevelLetterCocycles.FinrankEqOneOfBijective
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle021
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefJumpProof
import Formalism.SharpRestriction.LevelLetterCocycles.PhiItSmul
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle023
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle022
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle019

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions Filter Topology

theorem export_link_of_family {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.TwistedPlaces.OrbitValuationBound Fm) : LinkN Fm := by
  obtain ⟨C, x0, hx⟩ := h
  refine ⟨C, x0, fun x hx0 i hsha j hj hS => ?_⟩
  have hp := hx x hx0 i
  unfold TwistedPlaces.aux₃ at hp
  exact hp hsha hS j hj

theorem linkN_of {eps : ℝ} (Fm : FamP eps) (hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm) (hS : Formalism.MainNotions.TwistedPlaces.KudlaFamilyStatement Fm) :
    LinkN Fm := export_link_of_family Fm (hS hA)

def ThetaScalarNonzero (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ D.what₂.isot j σ,
    D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = lam • f

theorem thetaT_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) (hI : DirectSum.IsInternal (D.what₂.isot j))
    (h : ThetaScalarNonzero D μ j) : Function.Injective (D.what₂.thetaT μ j) := by
  classical
  choose lam hlam0 hlam using h
  set T : Module.End ℂ (D.what₂.Mj j) := (D.what₂.thetaP μ j).comp (D.what₂.thetaT μ j) with hTdef
  have hsub : ∀ σ, D.what₂.isot j σ ≤ Module.End.eigenspace T (lam σ) := by
    intro σ f hf
    rw [Module.End.mem_eigenspace_iff]
    exact hlam σ f hf
  have htop : (⊤ : Submodule ℂ (D.what₂.Mj j)) ≤ ⨆ (c : ℂ) (_ : c ≠ 0), Module.End.eigenspace T c := by
    rw [← hI.submodule_iSup_eq_top]
    refine iSup_le fun σ => le_trans (hsub σ) ?_
    exact le_iSup₂_of_le (lam σ) (hlam0 σ) le_rfl
  have hind : iSupIndep (Module.End.eigenspace T) := by
    first
      | exact Module.End.eigenspaces_iSupIndep T
      | exact Module.End.eigenspaces_independent T
  have hdis : Disjoint (Module.End.eigenspace T 0) ⊤ := (hind 0).mono_right htop
  have hker : LinearMap.ker T = ⊥ := by
    rw [← Module.End.eigenspace_zero]
    exact disjoint_top.mp hdis
  have hTinj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
  exact Function.Injective.of_comp (f := D.what₂.thetaP μ j) hTinj

def LamPos (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT,
    (∀ f ∈ D.what₂.isot j σ, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = ((D.what₂.lamP μ j σ : ℝ) : ℂ) • f) ∧
    (D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP μ j σ)

end Formalism.MainNotions.N

end
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

section JumpsT2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem jumps_in_letter_of_crystalline [NeZero n] (W : LocWach PD LL O v n) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) :
    ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
      SetCS W d T₁ T₂ F b S η m → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ (MiW d b S η) (hiW d b S η) :=
  fun _ _ _ _ _ _ _ _ hS => Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumpsLet₂ W hE hC hQ hS

theorem liftRing_of_uniformizer_clause (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) :
    Formalism.MainNotions.LiftingTheory.lifta_Ring W :=
  Formalism.MainNotions.LiftingTheory.lifta_ring_of W (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W h9 hA T hT).1

theorem lemGA_la_of_adm [NeZero n] (W : LocWach PD LL O v n) (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : LemGA_la W := by
  intro d T₁ T₂ F b S η m hS
  exact lemGA_la_of W hT2 h9 h5
    (liftRing_of_uniformizer_clause W h9 hS.1 T₂ hS.2.2.2.2.2.1.2.1) (jumps_in_letter_of_crystalline W hE hC hQ)
    d T₁ T₂ F b S η m hS

end JumpsT2

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.BasicNotions

theorem base_change_statement (D : D7) : H1fBaseChangeTheorem D := BCF.base_change_statement_of_jump Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general D

theorem base_change_every_theory (Th : LocTheory) : Formalism.MainNotions.WachCoordinates.admBC Th := BCF.base_change_of_coefficient_jump Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general Th

end Formalism.MainNotions.UnusedSlot80
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem evaluation_add (hz : PowerSeries.constantCoeff W.π₀₁ = 0) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f + g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f + Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  funext i
  exact PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero' hz) f g

theorem evalZero_mul (hz : PowerSeries.constantCoeff W.π₀₁ = 0) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f * g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  funext i
  exact PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hz) f g

theorem evalZero_X_eq_pi0 (hz : PowerSeries.constantCoeff W.π₀₁ = 0) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W PowerSeries.X = W.π₀ := by
  funext i
  show PowerSeries.subst W.π₀₁ PowerSeries.X = W.π₀ i
  rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hz)]
  rfl

theorem evalZero_C (c : O) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C c) = algebraMap O (LetA O n) c := by
  funext i
  show PowerSeries.subst W.π₀₁ (PowerSeries.C c) = _
  rw [PowerSeries.subst_C]
  rfl

def AdaptData (T : LocLat G Qp LL O) (i : ZMod n) (h η m : ℕ) (e' : Fin (finrank LL T.V) → W.DD T)
    (m' : ℕ) (u : Fin m' → ℤ) : Prop :=
  Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T (i - 1) e' ∧ m' ≤ m ∧ ∃ hmr : m' ≤ finrank LL T.V,
    (∀ j, -(η : ℤ) ≤ u j ∧ u j ≤ η) ∧
    (∀ j (hj : e' (Fin.castLE hmr j) ∈ W.N T),
      ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (W.cmp T ⟨_, hj⟩)) ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (u j)) ∧
    ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i →
      Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut.lowSum (PD := PD) T τ h η ≤ ∑ j, ((h : ℤ) + u j)

def AdaptBas : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (e' : Fin (finrank LL T₂.V) → W.DD T₂) (m' : ℕ) (u : Fin m' → ℤ),
        AdaptData W T₂ i (b i + S) η m e' m' u

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB
end
end

section

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

structure BrData2 (hR : Ring9 W) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) where
  C₁ : Coord W (baseIdOf hR) T₁
  C₂ : Coord W (baseIdOf hR) T₂
  C₀ : Coord W (baseIdOf hR) W.one
  h : CoordHom C₁ C₂ F
  e₀ : C₀.V
  Ks : ℕ → Type
  [ksRing : ∀ s, CommRing (Ks s)]
  [ksAlg : ∀ s, Algebra LL (Ks s)]
  Δ : Type

attribute [instance] BrData2.ksRing BrData2.ksAlg

structure BrProps2 {hR : Ring9 W} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L}
    (D : BrData2 hR T₁ T₂ F) (e : W.DD W.one) (Cu : Formalism.ExponentWindows.E.Cuts n) (kd : ZMod n → Formalism.ExponentWindows.Kind)
    (bb : ZMod n → ℕ) (j g G₀ Sz η hh : ℕ) : Prop where

  he₀ : ∀ i, D.C₀.t i D.e₀ = (letE i : LetA O n) • e

  arcs : ∀ ϖ : O, Irreducible ϖ → ∀ c ∈ Cu.cuts, Formalism.ExponentWindows.E.FinalArc (latHomOf D.h) c (Cu.ell c)
    (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb c) LL D.Ks D.Δ ϖ (W.χΓ W.gam) j
    (Formalism.ExponentWindows.E.parM (baseIdOf hR).Bs.ℓ hh g) g G₀ Sz η (Formalism.ExponentWindows.E.kindAt kd c)
    (Formalism.ExponentWindows.E.sizeAt bb c)

variable [Fintype (K →ₐ[Qp] LL)]

def Realised2 (hR : Ring9 W) (e : W.DD W.one) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := T₁.V) →
    CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (j Gp S η h : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ)
      (hC : CutsOK n j ty cuts arcLen),
      KindJumps PD T₁ W.emb Gp S η ty →
      (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) →
      gPar Gp S η ≤ h → SizesOK (gPar Gp S η) S h ty → ThickLe2 ty cuts arcLen →
      ∃ D : BrData2 hR T₁ T₂ F,
        BrProps2 D e (cutsOf hC) (kdOf ty) (bbOf ty) j (gPar Gp S η) Gp S η h


variable (W) in
structure BrHyp2 (Cc : ℝ) : Prop where

  s_one : W.s = 1

  unram : Function.Bijective (algebraMap K₀ K)

  five_le : 5 ≤ PD.p

  P5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W

  P6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W

  P9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W

  herr : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFirstProperty W

  wx : Formalism.MainNotions.LiftingTheory.coreWX W

  wr : Formalism.MainNotions.LiftingTheory.coreWR W Cc

  tools : ToolsAlg W

  f1 : F1 W

  f2 : F2 W

  hodge : HodgeExact PD LL O

  valRing : ValRing O v

  complete : IsAdicComplete (Ideal.span {(((PD.p : ℕ) : O))}) O

  real : ∃ e : W.DD W.one, UnitGen W e ∧ BKExt W e ∧ ∀ hR : Ring9 W, Realised2 hR e

theorem realised_of {Cc : ℝ} (H : BrHyp2 W Cc) : Realised W := by
    intro T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hC hK hJ hg hS hT hb1 hb2 _
    obtain ⟨e, he, hbk, hreal⟩ := H.real
    have h5 := H.five_le
    have hp2 : PD.p ≠ 2 := by omega
    have hR : Ring9 W := ring_condition_of_delta_invariants (H.P9 T₁ hc₁.2.2.2) H.s_one hp2 (unram_of H.unram)
    obtain ⟨D, P⟩ := hreal hR T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen hC hK hJ hg hS hT
    obtain ⟨-, -, hO, hD, -⟩ := hG
    have := hO
    have := hD
    obtain ⟨ϖ, eO, x, hϖ, hprim, hu⟩ :=
      ground_of hR H.s_one (by omega) H.valRing H.complete
    have hcard : IsUnit ((W.DelF.card : ℕ) : O) :=
      cardΔ_of (not_isUnit_p W H.valRing)
        (card_DelF H.s_one hp2 (unram_of H.unram) (H.P9 T₁ hc₁.2.2.2))
    have Q : LocalWachInputs W (baseIdOf hR) :=
      { s_one := H.s_one
        p_ne_two := hp2
        unram := unram_of H.unram
        P9 := H.P9
        P5 := H.P5
        P6 := H.P6
        tools := H.tools
        p_ne_zero := p_ne_zero_of W
        cardΔ := hcard
        inj := baseIdOf_inj hR
        full := baseIdOf_full hR }
    have hK₂ : ∀ i, JumpsAtE PD T₂ W.emb i ((ty i).win Gp S η) := fun i =>
      kind_quot H.hodge F hc₁ hc₂ hon (hK i)
    have hl₁ := finalLat_of Q hc₁.2.2.2 hC hg hS
      (fun i => jumpsAtE_mono (hK i) Set.subset_union_left) D.C₁
    have hl₂ := finalLat_of Q hc₂.2.2.2 hC hg hS
      (fun i => jumpsAtE_mono (hK₂ i) Set.subset_union_left) D.C₂
    have hunit := primUnit_of (baseIdOf_inj hR) (baseIdOf_full hR) he D.C₀ D.e₀ P.he₀
    refine ⟨{ I := baseIdOf hR, C₁ := D.C₁, C₂ := D.C₂, C₀ := D.C₀, h := D.h, e₀ := D.e₀, ϖ := ϖ,
              eO := eO, u := W.χΓ W.gam, x := x, Ks := D.Ks, Δ := D.Δ }, ?_⟩
    exact
      { irr := hϖ
        prim := hprim
        u_eq := hu
        lat₁ := hl₁
        lat₂ := hl₂
        unit := hunit
        rho := rho_field H.f1 H.f2 hc₁.2.2.2 h hJ (by omega) D.C₁ hl₁.prim.p5M (cutsOf hC) _ j _ _
        ext := fun κ hκ => by
          obtain ⟨R, hE, hses, hY, hrep⟩ :=
            ext_of' he H.hodge hbk hc₂.2.2.2 D.C₂ D.C₀ D.e₀ P.he₀ κ hκ
          exact ⟨R.ext hE, hrep, primExt_of Q H.hodge hC hS hK₂ R hE hses hY D.e₀
            (lift_of' H.unram H.s_one hp2 H.wr H.wx H.hodge R hE hcard hses hY (Mb₁ + hb₁) Mb₂ hb₂ hb2
              D.e₀ (fun i => by rw [hunit.N_eq i]; exact Submodule.mem_span_singleton_self _) hC)⟩
        wprime := wprimeCuts_of' H.unram H.s_one hp2 H.wr H.wx D.h hcard hc₁ hc₂ hon Mb₁ hb₁
          (Mb₂ + hb₂) hb1 hC
        arcs := P.arcs ϖ hϖ }

theorem crystalline_lifting_second_form {Cc : ℝ} (H : BrHyp2 W Cc) : ThmELiftAt PD (O := O) n W.emb v := by
  intro _ h5 T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hK hJ hg hS hC hT hb1 hb2
    hW
  obtain ⟨D, P⟩ := realised_of H T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hC hK
    hJ hg hS hT hb1 hb2 hW
  obtain ⟨-, -, hO, hD, hF⟩ := hG
  have := hO
  have := hD
  have hnum := finalNum_of PD.p (by omega) n j Gp S η h ty cuts arcLen (Mb₁ + hb₁) (Mb₂ + hb₂) hC hg hS
    hT hW
  have hnum' : Formalism.ExponentWindows.E.FinalNum D.I.Bs.ℓ (cutsOf hC) (kdOf ty) (bbOf ty) j (gPar Gp S η) Gp S η h
      (sigPar PD.p (gPar Gp S η) h j) (rrPar PD.p n (Mb₁ + hb₁) (Mb₂ + hb₂) cuts)
      (kapPar PD.p (gPar Gp S η) h (ellMax cuts arcLen)) (ellMax cuts arcLen) := by
    rw [D.I.ℓ_eq]
    exact hnum
  have hJ₂ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₂.ρ τ (Set.Icc (-(h : ℤ)) h) := fun τ a ha =>
    hJ τ a (H.hodge.1 T₁ T₂ F hc₁ hc₂ hon τ a ha)
  have key := Formalism.ExponentWindows.E.theorem_E_final_form O D.ϖ P.irr D.I.Bs D.eO n (cutsOf hC) (kdOf ty) (bbOf ty) j
    (gPar Gp S η) Gp S η h _ _ _ _ D.u D.x LL D.Ks D.Δ D.C₁.V D.C₂.V D.C₀.V (latOf D.C₁) (latOf D.C₂)
    (latOf D.C₀) D.e₀ (latHomOf D.h) (ZfN D.C₁ F) (Zf D.C₂) ⟨P.prim, P.u_eq, hF⟩ hnum'
    P.lat₁ P.lat₂ P.unit
    ⟨fun m κ hκ => ZfN_smul D.C₁ F m κ hκ,
      rho_fieldN H.f1 H.f2 F hc₁.2.2.2 hc₂.2.2.2 h hJ hJ₂ (by omega) D.C₁ P.lat₁.prim.p5M (cutsOf hC) _ j
        _ _, P.ext⟩ P.wprime P.arcs
  rw [parE_eq_ePar] at key
  exact liftF_ofN D.h H.s_one (by omega) (H.herr T₂ hc₂.2.2.2).2 _ key

end Formalism.MainNotions.WachCoordinates.Br
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def SecondRankCount (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Prop :=
  ∀ S : Submodule O (LcQ W T π' c),
    finrank O (IIrest W T Pt π' Eπ h' c S) ≤ (finrank K₀ K + 1) * finrank O S

end Local

def SecondRankCountAll (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
      (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, SecondRankCount ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def SecondRankHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelLR D HW → SecondRankCountAll D HW

def SecondPropositionOfRank : Prop := ∀ (D : D7) (HW : HWOf D.loc), modelQR D HW → SecondRankCountAll D HW → u2R D HW

theorem second_proposition_of_models (hL : SecondPropositionOfRank) (hQ : ModelQStep) (hR : SecondRankHypothesis) (hML : ModelLStep) : SecondPropositionHypothesis :=
  fun D HW F Cm CA CB CK hA =>
    hL D HW (hQ D HW F Cm CA CB CK hA) (hR D HW F Cm CA CB CK hA (hML D HW F Cm CA CB CK hA))

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def FirstFrameOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    adm1 D HW F Cm → DdRFull D → DiRank D HW F Cm → modelLR D HW → modelFR D HW → u1R D HW

theorem first_frame_of_models (hL : FirstFrameOfModels) (hML : ModelLStep) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
      DdRFull D → DiRank D HW F Cm → Adm1 D HW F Cm CA CB CK → modelFR D HW → u1R D HW :=
  fun D HW F Cm CA CB CK hd hr hA hMF => hL D HW F Cm hA.1 hd hr (hML D HW F Cm CA CB CK hA) hMF

end Formalism.MainNotions.N.Ln34

end
end

section

namespace Formalism.MainNotions.UnusedSlot80.InvCut

open Formalism.MainNotions.N.Ln03

def PrecompConst : Prop :=
  ∀ (LL : Type) [Field LL] (l : ℕ) [Fact l.Prime] (s : ℕ) (S : Set (ZMod (l ^ (s + 1)))ˣ),
    Subgroup.closure S = ⊤ → ∀ f : Rs LL l s → LL, (∀ a ∈ S, precomp LL l s a f = f) →
      ∃ c : LL, ∀ ζ : Rs LL l s, f ζ = c

def GenUnits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (s : ℕ) (u : ℤ_[l]ˣ),
    ((u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])}) → ((u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) →
      Subgroup.closure (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) = ⊤

end Formalism.MainNotions.UnusedSlot80.InvCut
end
