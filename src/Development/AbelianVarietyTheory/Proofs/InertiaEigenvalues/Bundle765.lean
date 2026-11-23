module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle751
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle154
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesFinal
public import Formalism.SharpRestriction.LevelLetterCocycles.RingHypothesesOfCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle753
import Formalism.SharpRestriction.LevelLetterCocycles.SemisimpleLetterIffForallMem
import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle754
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.RawLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cmp.RallisRange

variable {D : D7} {V W : HSp D}

theorem vol_lt_top (V : HSp D) {ν : Measure (GA D V)} {𝓗 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h : IsFundamentalDomain (GQ V) 𝓗 ν) : ν 𝓗 < ⊤ :=
  GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓗 hν h

end GlobalTheory.Cmp.RallisRange

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.complexHecke_conjugatePlace_petersson_adjoint : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3),
    Rl.Char3 F → ∀ (i : Fin D.R.m) (k : ℕ) (P P' : PlE D.host), IsSplitPl D.host P → IsConjPl D.host P P' →
    Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    Formalism.IndefR.Bridge.SplitOff P' (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal → 1 ≤ k → k ≤ D.R.r →
    ∃ (α α' : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i)) (R R' : Finset (Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i))),
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P k α ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R ∧
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P' k α' ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α' R' ∧
      (∀ x, ∃ x', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x)) ∧
      (∀ y, ∃ y', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y)) ∧
      ∀ x y x' y' : (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).H,
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x) →
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y) →
        ⟪x', y⟫_ℂ = ⟪x, y'⟫_ℂ := by
  first | exact @GlobalTheory.CxHeckeAdj.hecke_adjoint | exact GlobalTheory.CxHeckeAdj.hecke_adjoint | (intros; apply GlobalTheory.CxHeckeAdj.hecke_adjoint <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

section LetterAux

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem γD_letE_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n)
    (x : W.DD T) : W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [← algebraMap_smul W.EE (letE i : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul]
  congr 1
  funext j
  show W.γ₀ g ((letE i : LetA O n) j) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem sum_letE_eq_one [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem le_Mmax_of [NeZero n] (Mi : ZMod n → ℕ) (i : ZMod n) : Mi i ≤ Formalism.MainNotions.LiftingTheory.Mmax n Mi := by
  have h := Finset.le_sup (f := fun k : ℕ => Mi (k : ZMod n)) (Finset.mem_range.2 (ZMod.val_lt i))
  simp only [ZMod.natCast_zmod_val] at h
  exact h

theorem smul_letE_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (a : LetA O n)
    (x : W.DD T) (hx : a • x ∈ W.N T) : a • ((letE i : LetA O n) • x) ∈ W.N T := by
  rw [smul_smul, mul_comm, ← smul_smul]
  exact (W.N T).smul_mem _ hx

theorem letE_rec (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (c : O)
    (y z : W.DD T) (h : W.π₀ • (y + c • z) = W.γD T W.gam z - z) :
    W.π₀ • ((letE i : LetA O n) • y + c • ((letE i : LetA O n) • z)) =
      W.γD T W.gam ((letE i : LetA O n) • z) - (letE i : LetA O n) • z := by
  rw [smul_comm c (letE i : LetA O n) z, ← smul_add, smul_smul, mul_comm W.π₀, ← smul_smul, h,
    smul_sub, γD_letE_smul]

theorem mem_N_of_letE [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T)
    (h : ∀ i : ZMod n, (letE i : LetA O n) • x ∈ W.N T) : x ∈ W.N T := by
  have e : x = ∑ i : ZMod n, (letE i : LetA O n) • x := by
    rw [← Finset.sum_smul, sum_letE_eq_one, one_smul]
  rw [e]
  exact Submodule.sum_mem _ (fun i _ => h i)

theorem mem_of_qp_pow_zero (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T)
    (h : Formalism.MainNotions.LiftingTheory.qp W ^ 0 • x ∈ W.N T) : x ∈ W.N T := by
  rwa [pow_zero, one_smul] at h

end LetterAux

theorem dss_semisimple_of_used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.LiftingTheory.adm19 D HW F := by
  intro D HW F Cm hN l _ K s LL h
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL h) := hN.2.2.2.2.2.2.2.2.1 l K s LL h
  rw [Formalism.MainNotions.UnusedSlot35.DssRec.coreDss_iff_mem _ h9]
  intro hA T Mi hi hT hJ ug hug hv cO hc Y y₀ hy hΔ seq h0 hrec
  subst h0
  have hs : s = 1 := ((HW l).W_s K s LL h).symm.trans hA.2.1
  subst hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := by
    refine ⟨fun x hx => ?_, by rw [← hpl]; exact hA.2.2, h⟩
    obtain ⟨y, hy⟩ := hA.1.2 ⟨x, hx⟩
    have h2 := y.2.2
    have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
    rw [this] at h2
    exact h2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hw1 : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL h).gam_gen
    rw [hA.2.1, Nat.cast_one] at this
    exact this
  have hug1 : ug ^ (l - 1) = (((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam) ^ (l - 1) := by
    have := hug
    rw [hpl] at this
    exact this
  have hug' : ug = ((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam :=
    GlobalTheory.units_eq_of_pow_pred_eq_of_val_one l (D.loc l) LL ug _ hug1 hv hw1
  have hc' : ∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - ((((((HW l).W K 1 LL h).χΓ
      ((HW l).W K 1 LL h).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) := by
    intro x
    have := hc x
    rw [hpl, hug'] at this
    exact this
  have hjx : ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ),
      Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL h) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → 0 < j → j ≤ Y →
      a + (j : ℤ) ∈ Formalism.MainNotions.LiftingTheory.xList ((HW l).W K 1 LL h) T (Formalism.MainNotions.LiftingTheory.Mmax _ Mi)
        (Formalism.MainNotions.LiftingTheory.Mmax _ hi) Y := by
    intro i τ a j hO hjump hj0 hjY
    have ha := hJ i τ hO a hjump
    have hM := le_Mmax_of Mi i
    have hH := le_Mmax_of hi i
    rw [Formalism.MainNotions.LiftingTheory.xList, Finset.mem_sort, Finset.mem_image]
    refine ⟨(a, (j : ℤ)), Finset.mem_product.2 ⟨?_, ?_⟩, rfl⟩
    · simp only [Formalism.MainNotions.LiftingTheory.jumpSet, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, τ, hjump⟩
      · have := ha.1; omega
      · have := ha.2; omega
    · rw [Finset.mem_Icc]; omega
  have hmem : ∀ i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)),
      (letE i : LetA ↥(OL LL) _) • seq (Formalism.MainNotions.LiftingTheory.xList ((HW l).W K 1 LL h) T (Formalism.MainNotions.LiftingTheory.Mmax _ Mi)
        (Formalism.MainNotions.LiftingTheory.Mmax _ hi) Y).length ∈ ((HW l).W K 1 LL h).N T := by
    intro i
    have hDL : Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL h) T i ((letE i : LetA ↥(OL LL) _) • seq 0) := by
      refine ⟨by rw [smul_smul, letE_mul_self], fun δ hδ => ?_⟩
      rw [γD_letE_smul ((HW l).W K 1 LL h) T δ i (seq 0)]
      have e2 := hΔ δ hδ
      exact congrArg (fun z => (letE i : LetA ↥(OL LL) _) • z) e2
    have hYi : Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL h) ^ Y • ((letE i : LetA ↥(OL LL) _) • seq 0) ∈
        ((HW l).W K 1 LL h).N T := by
      exact smul_letE_mem ((HW l).W K 1 LL h) T i _ (seq 0) hy
    have key := GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl T hT i 0 Y cO hc' _
      (fun τ a j hO hjump hj hjY => hjx i τ a j hO hjump hj hjY)
      (fun k => (letE i : LetA ↥(OL LL) _) • seq k) hDL hYi
      (fun k hk => letE_rec ((HW l).W K 1 LL h) T i _ _ _ (hrec k hk))
    exact mem_of_qp_pow_zero ((HW l).W K 1 LL h) T _ key.2
  exact mem_N_of_letE ((HW l).W K 1 LL h) T _ hmem

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.crystallineUniversalPart_caseA : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → TruncatedSeriesCountingBounds.adm15 D → UnusedSlot80.UniversalComponentCaseA D HW F Cm := by
  first | exact @GlobalTheory.universalPart_caseA | exact GlobalTheory.universalPart_caseA | (intros; apply GlobalTheory.universalPart_caseA <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem admissibleArcDatum_gives_arcProperty : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → RamifiedCoefficientChains.adm11 D → UnusedSlot80.ArcLiftingCoordinates D HW F Cm :=
  fun D HW F Cm hA h1f h11 => UnusedSlot80.arc_coordinates_final D HW F Cm hA h1f h11

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem classSplitAlongArcs : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmSplitA D HW F Cm → UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → DeltaInvariantLattices.P6 D HW F → LiftingTheory.WachKillsQuotients D HW F → InvariantsGenerators.LitFont D HW F → LiftingTheory.adm23 D HW F → TruncatedSeriesCountingBounds.adm9 D → RamifiedCoefficientChains.adm11 D → UnusedSlot80.SplittingArcLifting D HW F Cm :=
  UnusedSlot80.split_case_A_final

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

noncomputable section

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem qp_isUnit (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
  obtain ⟨wq, hwq⟩ := hR9.qq
  have h1 : IsUnit (algebraMap (LetA O n) W.EE (W.φA letπ)) := by
    have := W.EE_π.map W.φE
    rw [W.φE_ext] at this
    exact this
  rw [W.φA_π, map_mul] at h1
  have h2 := (IsUnit.mul_iff.1 h1).2
  rw [hwq, map_mul] at h2
  exact (IsUnit.mul_iff.1 h2).2

theorem qp_pow_inj (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) (k : ℕ) {x : W.DD T}
    (h : Formalism.MainNotions.LiftingTheory.qp W ^ k • x = 0) : x = 0 := by
  have hu := (qp_isUnit W hR9).pow k
  rw [← map_pow] at hu
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) x] at h
  exact hu.smul_left_cancel.1 (h.trans (smul_zero _).symm)

theorem dl_of_qp (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) {i : ZMod n} {y : ℕ} {z : W.DD T}
    (h : Formalism.MainNotions.LiftingTheory.InNΔi W T i (Formalism.MainNotions.LiftingTheory.qp W ^ y • z)) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧ Formalism.MainNotions.LiftingTheory.qp W ^ y • z ∈ W.N T := by
  obtain ⟨hNΔ, hl⟩ := h
  have hN : Formalism.MainNotions.LiftingTheory.qp W ^ y • z ∈ W.N T := hNΔ.1
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ y • z) = Formalism.MainNotions.LiftingTheory.qp W ^ y • z := hNΔ.2
  obtain ⟨m, -, hme⟩ := Submodule.mem_map.1 hl
  refine ⟨⟨?_, fun δ hδ => ?_⟩, hN⟩
  · refine sub_eq_zero.1 (qp_pow_inj W hR9 y ?_)
    rw [smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ y) (letE i : LetA O n) z, ← hme]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Formalism.MainNotions.WachCoordinates.Br.letE_mul_self, sub_self]
  · refine sub_eq_zero.1 (qp_pow_inj W hR9 y ?_)
    have hq : W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ y) = Formalism.MainNotions.LiftingTheory.qp W ^ y :=
      (W.AΔ.pow_mem (Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.qp_mem hR9) y) δ hδ
    have e : Formalism.MainNotions.LiftingTheory.qp W ^ y • W.γD T δ z = W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ y • z) := by
      rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA, hq]
    rw [smul_sub, e, hΔ δ hδ, sub_self]

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

def pseq (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) (k : ℕ) : W.DD T :=
  Polynomial.aeval dop (((xs.take k).map fun x => Polynomial.X - Polynomial.C (cc x)).prod) z

theorem pseq_zero (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) :
    pseq W dop cc xs z 0 = z := by
  simp [pseq]

theorem pseq_succ (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) (k : ℕ)
    (hk : k < xs.length) :
    pseq W dop cc xs z (k + 1) = dop (pseq W dop cc xs z k) - cc (xs.getD k 0) • pseq W dop cc xs z k := by
  have ht : xs.take (k + 1) = xs.take k ++ [xs.getD k 0] := by
    rw [List.take_succ, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
    rfl
  unfold pseq
  rw [ht, List.map_append, List.prod_append, mul_comm, map_mul, Module.End.mul_apply]
  simp [Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]

theorem pseq_length (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (X : Finset ℤ) (z : W.DD T) :
    pseq W dop cc X.toList z X.toList.length =
      Polynomial.aeval dop (∏ x ∈ X, (Polynomial.X - Polynomial.C (cc x))) z := by
  unfold pseq
  rw [List.take_length, Finset.prod_map_toList]

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem eigenvalue_product_maps_letter_lattice_local (l : ℕ) (hpl : PD.p = l)
    (hR9 : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T)
    (hdss : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (y' Y : ℕ)
      (cO : ℤ → O), (∀ x : ℤ, ((l : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) →
      ∀ xs : List ℤ, (∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i →
        IsJumpV PD T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) →
      ∀ seq : ℕ → W.DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp W ^ Y • seq 0 ∈ W.N T →
      (∀ k < xs.length, W.π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) =
        W.γD T W.gam (seq k) - seq k) →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp W ^ y' • seq xs.length ∈ W.N T) :
    Formalism.MainNotions.N.LetterConditionLocal W := by
  intro hCA T hT i y _ dop hdop cc hcc X hX z hz
  obtain ⟨hDL, hzN⟩ := dl_of_qp W (hR9 hCA T hT) hz
  have hcc' : ∀ x : ℤ, ((l : ℕ) : O) * cc x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) := by
    intro x
    have e := hcc x
    rw [hpl] at e
    linear_combination -e
  have hj : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i →
      IsJumpV PD T.ρ τ a → 0 < j → j ≤ y → a + (j : ℤ) ∈ X.toList :=
    fun τ a j ho hja h1 h2 => Finset.mem_toList.2 (hX τ a j ho hja h1 h2)
  have hrec : ∀ k < X.toList.length, W.π₀ • (pseq W dop cc X.toList z (k + 1) +
      cc (X.toList.getD k 0) • pseq W dop cc X.toList z k) =
      W.γD T W.gam (pseq W dop cc X.toList z k) - pseq W dop cc X.toList z k := by
    intro k hk
    rw [pseq_succ W dop cc X.toList z k hk, sub_add_cancel]
    exact hdop _
  have key := hdss hCA T hT i 0 y cc hcc' X.toList hj (pseq W dop cc X.toList z)
    (by rw [pseq_zero]; exact hDL) (by rw [pseq_zero]; exact hzN) hrec
  rw [pseq_length] at key
  obtain ⟨hD, hNl⟩ := key
  rw [pow_zero, one_smul] at hNl
  refine ⟨⟨hNl, hD.2⟩, Submodule.mem_map.2 ⟨_, hNl, ?_⟩⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  exact hD.1

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

open Formalism.BasicNotions.Loc

theorem eigenvalue_product_maps_letter_lattice_of_conclusions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.N.LetterConditionGlobal D HW F := by
  intro D HW F Cm hN l _ K s LL h hCA
  have hs : s = 1 := by rw [← (HW l).W_s K s LL h]; exact hCA.2.1
  subst hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := by
    refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, h⟩
    obtain ⟨w, hw⟩ := hCA.1.2 ⟨x, hx⟩
    have h2 := w.2.2
    have : ((w : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hw
    rw [this] at h2
    exact h2
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL h) := hN.2.2.2.2.2.2.2.2.1 l K 1 LL h
  exact eigenvalue_product_maps_letter_lattice_local _ l hpl (fun hA T hT => Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.ring_hypotheses_of_crystalline _ hA h9 T hT)
    (fun _ => GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl) hCA

end GlobalTheory.PrimeSequence
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.fontaineAtPlacesOverL : ∀ (D : D7) (i : D.nd.Loc), Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i := by
  first | exact @GlobalTheory.FontaineAdm.fontaineProperties_all_places | exact GlobalTheory.FontaineAdm.fontaineProperties_all_places | (intros; apply GlobalTheory.FontaineAdm.fontaineProperties_all_places <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.adm7_elementDenominator : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm7 D := by
  first | exact @GlobalTheory.elementDenominator_adm7 | exact GlobalTheory.elementDenominator_adm7 | (intros; apply GlobalTheory.elementDenominator_adm7 <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.ramifiedCoefficientChains_adm13 : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm13 D := by
  first | exact @GlobalTheory.h1f_generators_of_record | exact GlobalTheory.h1f_generators_of_record | (intros; apply GlobalTheory.h1f_generators_of_record <;> assumption)
end
