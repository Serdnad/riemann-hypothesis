module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle274
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle396
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle323
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle291
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle243
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle345
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricCharResidueConjEqWeightedUnipotentSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle391
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle390
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LiftSpan



theorem span_liftForm_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → A.fam.Ok 1 → (∀ i t, Function.Injective (R.extV i t)) → ∀ (i : Fin D.R.m) (t : T), Submodule.span ℂ (Set.range fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) = LinearMap.range (R.extV i t) ⊓ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB _ _ i t
  classical
  have hHV := hB.models.HV i t
  have hjV := hB.models.jV
  have hExt : (R.B.L i t).pres.ExtBij :=
    (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.1
  have key : (fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) =
      fun x => (R.cV i).ext ((R.B.L i t).pres.extL (GlobalTheory.OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x)) := by
    funext x
    exact congrArg (R.cV i).ext (hjV i t _)
  have hR : Set.range (fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) =
      (R.cV i).ext '' ((R.B.L i t).pres.extL ''
        {f | ∀ u : F.P0, A.leftGroupActionLift i t (u : G) f = ((F.ψ0⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • f}) := by
    rw [key]
    ext Y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨_, (GlobalTheory.TraceIncl.mem_range_srcForm i t F.P0 F.ψ0⁻¹ _).1 ⟨x, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      obtain ⟨x, rfl⟩ := (GlobalTheory.TraceIncl.mem_range_srcForm i t F.P0 F.ψ0⁻¹ f).2 hf
      exact ⟨x, rfl⟩
  rw [hR, Submodule.span_image]
  ext Y
  simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_range]
  have hs1 := GlobalTheory.T.span_eigenforms_adelic_forms_iff_class_presentation (W := (R.cV i).W) (Bridge.ratF (Vc D i)) (A.MtCSD i t) D.what₂.embLL (R.cV i).coef.ρ
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch (A.leftGroupActionLift i t)
    (R.B.L i t).pres (R.B.L i t).act_tie hExt F.P0 F.ψ0⁻¹
  have hs2a := GlobalTheory.T.base_level_adelic_type_implies_lift_law D G Pl0 T A Ks R F hB.models.cV hB.grp.red_L i t
  have hs2b := GlobalTheory.T.lift_law_implies_adelic_extension_base_level D G Pl0 T A Ks R F hB.models.cV hB.grp.red_L i t
  constructor
  · rintro ⟨Φ, hΦ, rfl⟩
    obtain ⟨hAd, hq⟩ := (hs1 Φ).1 hΦ
    refine ⟨?_, hs2b Φ hq⟩
    have h1 : Φ ∈ LinearMap.range (R.HV i t).e := by rw [hHV.2.1]; exact hAd
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, by rw [← hy]; rfl⟩
  · rintro ⟨⟨y, rfl⟩, hlev⟩
    have h1 : (R.HV i t).e y ∈ LinearMap.range (R.HV i t).e := LinearMap.mem_range_self _ y
    rw [hHV.2.1] at h1
    exact ⟨(R.HV i t).e y, (hs1 _).2 ⟨h1, hs2a _ hlev⟩, rfl⟩

end GlobalTheory.LiftSpan
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem span_range_map_mem {M N ι : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N)
    (g : ι → M) {y : M} (hy : y ∈ Submodule.span ℂ (Set.range g)) : f y ∈ Submodule.span ℂ (Set.range fun i => f (g i)) := by
  have h := Submodule.mem_map_of_mem (f := f) hy
  rwa [Submodule.map_span, ← Set.range_comp] at h



theorem topSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → TopMultH R → ∀ (b : Bool) (t : T), Submodule.span ℂ (Set.range fun x => R.cX.toMap R.prX ((R.HX t).e (R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)))) = Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hPr hOk hTop b t
  have hjX : ∀ x, (R.HX t).e (R.jX t x) = R.B.jR t x := hB.models.jX t
  simp only [hjX]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hmem : R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x) ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ
        (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ :=
      Bridge.ClassPres.extMem_holds (R.B.R t).pres _
    have hlv := (GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char _ _ _ (A.fam.R t).r (F.lvl b).P (F.lvl b).ψ (rowForm A (F.lvl b).P (F.lvl b).ψ t x)).1 ⟨x, rfl⟩
    exact GlobalTheory.T.principalLevelForm_mem_faceLevelMultiplicity D G Pl0 T A Ks R F hB b t _ hmem (GlobalTheory.TopSpan.jR_level D G Pl0 T A Ks R F b t _ hlv)
  · intro Tm hT
    obtain ⟨Fn, hF, hQ, rfl⟩ := GlobalTheory.T.exists_principalLevelForm_of_faceLevelMultiplicity D G Pl0 T A Ks R F hB b t Tm hT
    exact span_range_map_mem (R.cX.toMap R.prX) (fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x))
      (GlobalTheory.T.principalLevelForm_mem_span_adelicRationalForms D G Pl0 T A Ks R F b t Fn hF hQ)

end GlobalTheory.TopSpan
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.LabCarry

theorem inner_eq_zero_of_normal {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T : H →ₗ[ℂ] H) (hT : Commute T (LinearMap.adjoint T)) {a b : ℂ} (hab : a ≠ b) {x y : H}
    (hx : T x = a • x) (hy : T y = b • y) : ⟪x, y⟫_ℂ = 0 := by
  set S : H →ₗ[ℂ] H := T - b • LinearMap.id with hS
  have hSy : S y = 0 := by simp [hS, hy]
  have hSadj : LinearMap.adjoint S = LinearMap.adjoint T - (starRingEnd ℂ b) • LinearMap.id := by
    rw [hS, map_sub, LinearEquiv.map_smulₛₗ, LinearMap.adjoint_id]
  have hSc : Commute S (LinearMap.adjoint S) := by
    rw [hSadj, hS]
    have h1 : Commute T (starRingEnd ℂ b • (LinearMap.id : H →ₗ[ℂ] H)) := (Commute.one_right T).smul_right _
    have h2 : Commute (b • (LinearMap.id : H →ₗ[ℂ] H)) (LinearMap.adjoint T) := (Commute.one_left _).smul_left _
    have h3 : Commute (b • (LinearMap.id : H →ₗ[ℂ] H)) (starRingEnd ℂ b • (LinearMap.id : H →ₗ[ℂ] H)) :=
      ((Commute.one_left _).smul_left _).smul_right _
    exact (hT.sub_right h1).sub_left (h2.sub_right h3)
  have hSa : LinearMap.adjoint S y = 0 := by
    have h0 : ⟪LinearMap.adjoint S y, LinearMap.adjoint S y⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left]
      have : S (LinearMap.adjoint S y) = LinearMap.adjoint S (S y) := by
        have := congrArg (fun f : H →ₗ[ℂ] H => f y) hSc.eq
        simpa [Module.End.mul_apply] using this
      rw [this, hSy, map_zero, inner_zero_right]
    exact inner_self_eq_zero.1 h0
  have hTa : LinearMap.adjoint T y = (starRingEnd ℂ b) • y := by
    have := hSa
    rw [hSadj, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  have key : ⟪T x, y⟫_ℂ = ⟪x, LinearMap.adjoint T y⟫_ℂ := (LinearMap.adjoint_inner_right T x y).symm
  rw [hx, hTa, inner_smul_left, inner_smul_right] at key
  have hne : starRingEnd ℂ a ≠ starRingEnd ℂ b := fun h => hab ((starRingEnd ℂ).injective h)
  have : (starRingEnd ℂ a - starRingEnd ℂ b) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.Mem.R3.LabCarry

namespace GlobalTheory.Mem.R3.LabCarry

theorem twSub_iSup {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) (V : I → Submodule ℂ E) :
    Tw.sub s (⨆ p, V p) = ⨆ p, Tw.sub s (V p) := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun p x hx => Submodule.mem_iSup_of_mem (p := V) p hx)
  exact Submodule.iSup_induction V (motive := fun y => Tw.mk s y ∈ ⨆ p, Tw.sub s (V p)) hx
    (fun p y hy => Submodule.mem_iSup_of_mem p hy) (zero_mem _) fun y z hy hz => add_mem hy hz

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem carries_of_eq (R : RealDat3 D A3 Ks) (p : A3.fam3.base3.Ix) {c c' : Pl D.host.E → List ℤ → ℂ}
    (heq : R.EEc c' = R.EEc c) (h : R.Carries p c') : R.Carries p c := by
  have key : ∀ V W : Submodule ℂ R.HE.H, V = W →
      (V ≠ ⊥ ∧ V.map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
        Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms))) →
      (W ≠ ⊥ ∧ W.map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
        Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms))) := by
    rintro V W rfl hV; exact hV
  exact key _ _ heq h

end GlobalTheory.Mem.R3.LabCarry

namespace GlobalTheory.Mem.R3.LabCarry



theorem carried : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (c : Pl D.host.E → List ℤ → ℂ) (b : Bool) (x : R.HE.H), x ≠ 0 → x ∈ R.EEc c → R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b) → ∃ p, R.Carries p c := by
  intro hWe hDs hHC hCu D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hHo hHost c b x hx0 hxc hxb
  by_contra hno
  push_neg at hno
  obtain ⟨hcore, hSF, -, -, hEEc, -, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hP.char
  obtain ⟨h, -, hN, -, hev, hchar⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 (hcore hHo.aux.ex)
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCu R.toRealDat) R.SF hSF

  have heig : ∀ c' (y : R.HE.H), y ∈ R.EEc c' → ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P →
      GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) y = c' P (dualLab d) • y := by
    intro c' y hy P d hG hL
    rw [hEEc c'] at hy
    rw [hev c' P hG (Finsupp.single d 1) y hy]
    congr 1
    simp [GlobalTheory.Hk3.evC, Finsupp.sum_single_index, hL]

  have horth : ∀ c', R.EEc c' ≠ R.EEc c → R.EEc c' ≤ (ℂ ∙ x)ᗮ := by
    intro c' hne y hy
    have hex : ∃ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧ GlobalTheory.Hk3.IsLab (Yc D 0) P d ∧
        c' P (dualLab d) ≠ c P (dualLab d) := by
      by_contra hall
      push_neg at hall
      apply hne
      ext z
      constructor
      · intro hz
        rw [hEEc c]
        exact hchar c z fun P d hG hL => by rw [heig c' z hz P d hG hL, hall P d hG hL]
      · intro hz
        rw [hEEc c']
        exact hchar c' z fun P d hG hL => by rw [heig c z hz P d hG hL, hall P d hG hL]
    obtain ⟨P, d, hG, hL, hcc⟩ := hex
    have hT : Commute (h P (Finsupp.single d 1)) (LinearMap.adjoint (h P (Finsupp.single d 1))) := by
      rw [hN.2 P hG]
      exact hN.1 P P hG hG _ _
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have := inner_eq_zero_of_normal _ hT hcc (heig c' y hy P d hG hL) (heig c x hxc P d hG hL)
    rw [← inner_conj_symm, this, map_zero]

  have hpart : ∀ p, R.EEp3 p ≤ (ℂ ∙ x)ᗮ := by
    intro p
    unfold RealDat3.EEp3
    refine iSup₂_le fun c' hc' => horth c' fun heq => hno p ?_
    exact carries_of_eq R p heq hc'

  have hxT : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈ (R.toCx3 F).EEl b := hxb
  rw [← (hHo.prim.sumE b).2] at hxT
  have hxS : x ∈ ⨆ p, R.EEp3 p := by
    have h1 : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈
        Tw.sub (twAt D.what₂.embLL A3.A.v0) (⨆ p, R.EEp3 p) := by
      rw [twSub_iSup]
      have hle : (⨆ p, (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl b) ≤
          ⨆ p, Tw.sub (twAt D.what₂.embLL A3.A.v0) (R.EEp3 p) := iSup_mono fun p => inf_le_left
      exact hle hxT
    exact h1
  have hself : x ∈ (ℂ ∙ x)ᗮ := (iSup_le hpart) hxS
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hself
  exact hx0 (inner_self_eq_zero.1 hself)

end GlobalTheory.Mem.R3.LabCarry
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.Mirror

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc hD_swap_zero)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem suppAt_of_isK {ε a : AE D} {v y : Fin B.rank → AE D} {k : GA D B} (hk : IsK B v y k) (hy : a • y = y)
    (h1 : (ε + cA D ε) * a = a) (h2 : (ε + cA D ε) * cA D a = cA D a) : SuppAt ε B k := by
  rw [suppAt_iff_vec]
  intro x
  have e1 : (ε + cA D ε) * hA B x y = hA B x y := by
    rw [← hy, hA_smul_right, ← mul_assoc, h2]
  have e2 : (ε + cA D ε) • y = y := by
    conv_lhs => rw [← hy]
    rw [smul_smul, h1, hy]
  have e : (mt B k).mulVec x - x = hA B x y • v - hA B x v • y := by rw [hk x]; abel
  rw [e, smul_sub, smul_smul, e1, smul_comm, e2]

def fixGrp (B : HSp D) (x : Fin B.rank → AE D) : Subgroup (GA D B) where
  carrier := {g | (mt B g).mulVec x = x}
  one_mem' := by show _ = _; rw [mt_one, Matrix.one_mulVec]
  mul_mem' := fun {g h} hg hh => by
    show _ = _
    rw [mulVec_mul, show (mt B h).mulVec x = x from hh, show (mt B g).mulVec x = x from hg]
  inv_mem' := fun {g} hg => by
    show _ = _
    conv_lhs => rw [← show (mt B g).mulVec x = x from hg]
    rw [mulVec_inv_cancel]

theorem fix_of_isK (d : BesselDatum A B ι) {i l : Fin (d.ρ + 1)} (h : l ≠ i) {t} {g : GA D B}
    (hg : IsK B (vecA B (dual d i)) (iA ι t) g) : g ∈ fixGrp B (vecA B (d.aux l)) := by
  show _ = _
  rw [hg, hA_vec_iA (besselDatum_auxiliaryVector_orthogonal_image d l), hA_vec, (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).1, if_neg h]
  simp

theorem fix_of_ExGe (d : BesselDatum A B ι) {ε : AE D} (he : IsSplitIdem D ε) {p : ℕ} {l : Fin (d.ρ + 1)} (h : l.1 < p)
    {g : GA D B} (hg : g ∈ ExGe d ε p) : g ∈ fixGrp B (vecA B (d.aux l)) := by
  refine (Subgroup.closure_le _).2 (Set.iUnion_subset fun i => Set.iUnion_subset fun hi u hu => ?_) hg
  obtain ⟨t, -, ht⟩ := (GlobalTheory.T.mem_besselExchangeGroup_iff_rootExchange D A B ι d ε he i u).1 (Subgroup.subset_closure hu)
  exact fix_of_isK d (fun e => by rw [e] at h; omega) ht

theorem basis_castSucc (d : BesselDatum A B ι) (l : Fin d.ρ) : d.aux l.castSucc = d.e l := by
  unfold BesselDatum.aux; rw [Fin.snoc_castSucc]

theorem hD_basis_e (d : BesselDatum A B ι) (m) (j : Fin d.ρ) : B.hD (d.aux m) (d.e j) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun l => ?_) m
  · rw [Fin.snoc_last]; exact hD_swap_zero (d.ez j)
  · rw [Fin.snoc_castSucc]; exact d.ee l j

theorem hD_basis_succ_f (d : BesselDatum A B ι) (i : Fin d.ρ) : B.hD (d.aux i.succ) (d.f i) = 0 := by
  have key : ∀ m : Fin (d.ρ + 1), m.1 = i.1 + 1 → B.hD (d.aux m) (d.f i) = 0 := by
    intro m
    unfold BesselDatum.aux
    refine Fin.lastCases (fun _ => ?_) (fun l hl => ?_) m
    · rw [Fin.snoc_last]; exact hD_swap_zero (d.fz i)
    · rw [Fin.snoc_castSucc, d.ef, if_neg]
      rintro rfl
      simp at hl
  exact key _ rfl

theorem conj_apply {v y : Fin B.rank → AE D} {k c : GA D B} (hk : IsK B v y k) (hc : c ∈ fixGrp B v)
    {x : Fin B.rank → AE D} (hx : hA B x v = 0) :
    (mt B (c * k * c⁻¹)).mulVec x = x + hA B ((mt B c⁻¹).mulVec x) y • v := by
  have hc' : (mt B c).mulVec v = v := hc
  have h0 : hA B ((mt B c⁻¹).mulVec x) v = 0 := by rw [hA_mt_left, inv_inv, hc', hx]
  rw [mulVec_mul, mulVec_mul, hk, h0, zero_smul, sub_zero, Matrix.mulVec_add, Matrix.mulVec_smul, hc', mulVec_cancel_inv]

theorem sum_single (d : BesselDatum A B ι) (j : Fin d.ρ) (a : AE D) :
    ∑ l, (if l = j then a else 0) • vecA B (d.e l) = a • vecA B (d.e j) := by
  simp [ite_smul]

theorem mirror : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (ε : AE D), IsSplitIdem D ε → ∀ (j : Fin d.ρ) (t₀ t : Fin A.rank → AE D) (b₀ k : GA D B), ε • t₀ = t₀ → cA D ε • t = t → IsK B (vecA B (dual d j.succ)) (iA ι t₀) b₀ → IsK B (vecA B (d.e j)) (iA ι t) k → SuppAt ε B k ∧ ∀ b ∈ ExGe d ε (j.1 + 2), b * (b₀ * k * b₀⁻¹) * b⁻¹ ∈ d.N ∧ SuppAt ε B (b * (b₀ * k * b₀⁻¹) * b⁻¹) ∧ d.psiN ψ (b * (b₀ * k * b₀⁻¹) * b⁻¹) = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D d.θ * hA A t₀ t)) := by
  intro D A B ι d ψ ε he j t₀ t b₀ k ht₀ ht hb₀ hk
  have h1 : ε * ε = ε := he.1
  have h2 : ε * cA D ε = 0 := he.2.1
  have h3 : cA D ε * cA D ε = cA D ε := by rw [← RingHom.map_mul, h1]
  have a1 : (ε + cA D ε) * ε = ε := by rw [add_mul, h1, mul_comm, h2, add_zero]
  have a2 : (ε + cA D ε) * cA D ε = cA D ε := by rw [add_mul, h2, h3, zero_add]
  have sk : SuppAt ε B k := suppAt_of_isK (a := cA D ε) hk (by rw [← iA_smul, ht]) a2 (by rw [cA_cA, a1])
  have sb : SuppAt ε B b₀ := suppAt_of_isK (a := ε) hb₀ (by rw [← iA_smul, ht₀]) a1 a2
  refine ⟨sk, fun b hb => ?_⟩
  have sb' := suppAt_of_mem_ExGe hb
  have hn : b * (b₀ * k * b₀⁻¹) * b⁻¹ = (b * b₀) * k * (b * b₀)⁻¹ := by group
  have hfix : ∀ l : Fin d.ρ, l ≤ j → b * b₀ ∈ fixGrp B (vecA B (d.e l)) := by
    intro l hl
    have hl' : l.1 ≤ j.1 := hl
    rw [← basis_castSucc]
    refine mul_mem (fix_of_ExGe d he (by simp; omega) hb) (fix_of_isK d (fun e => ?_) hb₀)
    have := congrArg Fin.val e
    simp at this; omega
  have hact : ∀ x : B.V, B.hD x (d.e j) = 0 → actV B (b * (b₀ * k * b₀⁻¹) * b⁻¹) x =
      vecA B x + hA B ((mt B (b * b₀)⁻¹).mulVec (vecA B x)) (iA ι t) • vecA B (d.e j) := by
    intro x hx
    rw [hn]
    exact conj_apply hk (hfix j le_rfl) (by rw [hA_vec, hx, map_zero])
  refine ⟨Subgroup.subset_closure ⟨fun i => ?_, fun x hx => ?_⟩,
    suppAt_mul (suppAt_mul sb' (suppAt_mul (suppAt_mul sb sk) (suppAt_inv sb))) (suppAt_inv sb'), ?_⟩
  · refine ⟨_, fun l hl => ?_, by rw [hact _ (d.ee i j), ← sum_single]⟩
    split_ifs with h
    · subst h
      rw [show (mt B (b * b₀)⁻¹).mulVec (vecA B (d.e i)) = _ from inv_mem (hfix i hl), hA_vec_iA (d.eA i)]
    · rfl
  · exact ⟨_, by rw [hact _ (hx j), ← sum_single]⟩
  · unfold BesselDatum.psiN BesselDatum.simpleSum
    congr 3
    have e : ∀ i : Fin d.ρ, hA B (actV B (b * (b₀ * k * b₀⁻¹) * b⁻¹) (d.aux i.succ)) (vecA B (d.f i)) =
        if j = i then hA B ((mt B (b * b₀)⁻¹).mulVec (vecA B (d.aux i.succ))) (iA ι t) else 0 := by
      intro i
      rw [hact _ (hD_basis_e d _ j), hA_add, hA_smul, hA_vec, hA_vec, hD_basis_succ_f, d.ef]
      split_ifs <;> simp
    simp only [e, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hb' : (mt B b⁻¹).mulVec (vecA B (d.aux j.succ)) = vecA B (d.aux j.succ) :=
      inv_mem (fix_of_ExGe d he (by simp) hb)
    have p1 : hA B (iA ι t) (vecA B (dual d j.succ)) = 0 := by
      rw [← hA_herm, hA_vec_iA (dual_perp d _), map_zero]
    rw [_root_.mul_inv_rev, mulVec_mul, hb', hA_mt_left, inv_inv, hb₀, p1, zero_smul, sub_zero, hA_add_right,
      hA_vec_iA (besselDatum_auxiliaryVector_orthogonal_image d _), zero_add, hA_smul_right, hA_herm, hA_vec, (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).1, if_pos rfl,
      map_one, mul_one, hA_iA d.isom]

end GlobalTheory.RootExch.Mirror

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteAddChar_conj_eq_prod_placeResidueChars : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ ψ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ, (∀ kv, ψ' kv ≠ 1) ∧ ∀ (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (t u : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1)), (∀ kv, GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) s (t kv)) → (∀ kv, GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I s) (u kv)) → star (X.psiEf (divN X.B.I X.B.g s)) = ∏ kv, ψ' kv (t kv + u kv) := by
  first | exact @GlobalTheory.Mem.SymChar.CharProd.psiEf_conj_eq_prod | exact GlobalTheory.Mem.SymChar.CharProd.psiEf_conj_eq_prod | (intros; apply GlobalTheory.Mem.SymChar.CharProd.psiEf_conj_eq_prod <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symmetricCharResidue_conj_eq_weightedUnipotentSum : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I (GlobalTheory.Mem.SymChar.argS X k)) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtB D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j else 0) := by
  first | exact @GlobalTheory.Mem.SymChar.ResBar.resBar | exact GlobalTheory.Mem.SymChar.ResBar.resBar | (intros; apply GlobalTheory.Mem.SymChar.ResBar.resBar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integration_by_parts_rightDerivative_adelicQuotient : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ F, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ ∧ ∫ g in 𝓕, Rder θ V τ X φ g * F g ∂μ = -∫ g in 𝓕, φ g * Rder θ V τ X F g ∂μ := by
  first | exact @GlobalTheory.Mem.IntByParts.integral_Rder_mul | exact GlobalTheory.Mem.IntByParts.integral_Rder_mul | (intros; apply GlobalTheory.Mem.IntByParts.integral_Rder_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.smoothCuspForm_mem_unitaryRapidDecayForms : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ F, IsCuspForm θ V F → F ∈ Decay θ V := by
  first | exact @GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay | exact GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay | (intros; apply GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelFrameCharacter_mul_movedPoint : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ → χ x = Units.map (σ : K →* ℂ) (Λ.chr h)) → ∀ (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp), IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) → χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.chi_mul_topChi_moved | exact GlobalTheory.Mem.Col2.TopCh.chi_mul_topChi_moved | (intros; apply GlobalTheory.Mem.Col2.TopCh.chi_mul_topChi_moved <;> assumption)
end
