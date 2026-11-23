module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle375
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle594
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle643
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle487
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle642
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle373
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle629
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle627
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle407
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle644
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
namespace GlobalTheory.DepHalf

open scoped Pointwise

theorem smul_mem_latBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D →
    ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latRow G i, e • u ∈ latBig G i := by
  intro D T L sc μ₀ hL hQ G i hi e he u hu
  have h1 : e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu.2 e he
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    unfold Places.modulBar
    intro h
    apply G.pl.modul_ne_bot sc
    have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
    simpa [smul_smul] using this
  have hone : (1 : D.host.E) ∈ ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by
    have hle : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by
      have := FractionalIdeal.inv_anti_mono hmB FractionalIdeal.coeIdeal_le_one
      rwa [inv_one] at this
    exact hle (FractionalIdeal.one_mem_one _)
  have hsub : G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)) ≤
      homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    refine Submodule.smul_le.2 fun r hr x hx y hy => ?_
    rw [smul_mulVec]
    refine Submodule.subset_span ⟨algebraMap (𝓞 D.host.E) D.host.E r, ?_, x *ᵥ y, hx y hy, ?_⟩
    · unfold shiftId
      rw [show algebraMap (𝓞 D.host.E) D.host.E r = algebraMap (𝓞 D.host.E) D.host.E r * 1 by rw [mul_one]]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hone
    · exact (algebraMap_smul D.host.E r (x *ᵥ y)).symm
  have h2 : e • u ∈ hatMx (homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))) := by
    refine AddSubgroup.closure_mono ?_ h1
    rintro w ⟨α, hα, x, hx, rfl⟩
    exact ⟨α, hα, x, hsub hx, rfl⟩
  have hhalf : IsHalf e (e • u) := fun a b => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have h0 : ∀ j, (Node.grid (i + 1) 0 : Node) ≠ .grid 0 j := fun j h => by
    injection h with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) := (G.isV (show (Node.grid (i + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  exact GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hQ hL G) hhalf h2

end GlobalTheory.DepHalf
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

namespace GlobalTheory.Chain.SourceLaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isLift_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsLevelLift V β L 1 1 := by
  unfold IsLevelLift
  refine ⟨Subgroup.one_mem _, ?_, ?_⟩
  · rw [map_one]
    exact Subgroup.one_mem _
  · rw [map_one]
    exact rTup_one

theorem levChi_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    levChi V β L 1 = 1 := by
  have h := (levChar D.sp.cm V.gram β L).map_one
  rw [levChar_apply] at h
  have h' : levFn β L 1 = 1 := h
  unfold levChi
  rw [map_one, h', Units.val_one]

theorem isLift_of_mem (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {κ : GA D V} (h : κ ∈ levG V β (flag1L L)) : IsLevelLift V β L 1 κ := by
  have hm := h
  unfold levG levA at hm
  rw [Subgroup.mem_inf, Subgroup.mem_comap, mem_lev] at hm
  obtain ⟨h1, h2, h3⟩ := hm
  exact ⟨h1, h2, Subgroup.mem_bot.mp h3⟩

private lemma levChi_flag1L_eq_levChi_flagL (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (κ : GA D V) :
    levChi V β (flag1L L) κ = levChi V β (flagL L) κ := by
  have e1 : ext1 (flag1L L).P.H (flag1L L).P.chi (rTup β (flag1L L) (finE V κ)) = 1 := by
    unfold ext1
    split_ifs <;> rfl
  have e2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := by
    unfold ext1
    split_ifs <;> rfl
  unfold levChi levFn
  rw [e1, e2]
  rfl

theorem law_of_pair {V W : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (β' : GL (Fin W.rank) (Lev.EAf D)) (L' : LevDat D.host.E ℂ W.rank) {X : Type} [AddCommGroup X] [Module ℂ X]
    {κ : GA D V} {u v : X}
    (h : (levChi V β (flagL L) κ)⁻¹ • u = (levChi W β' (flagL L') 1)⁻¹ • v) :
    u = levChi V β (flag1L L) κ • v := by
  have hne : levChi V β (flagL L) κ ≠ 0 := by
    unfold levChi
    exact Units.ne_zero _
  rw [levChi_one W β' (flagL L'), inv_one, one_smul] at h
  rw [levChi_flag1L_eq_levChi_flagL, ← h, smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem lawsOK : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → LawsOK R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hIs hθ hωY hωX hvY hvX
  have hInf : R.models_inf := hθ
  refine ⟨?_, ?_⟩
  · intro t k hk κ hκ
    have hl : IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) 1 κ := isLift_of_mem _ _ _ hκ
    have hl' := isLift_one (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv)
    have key := GlobalTheory.T.stepVector_lift_pair_flagLevel_realized_chain R hIs hInf hωY hvY t k hk 1 κ 1 hl hl'
    have e : flag1L (R.datYt t k R.triv) = R.datYt t k R.triv := rfl
    have hlaw := law_of_pair (R.βY k) (R.datYt t k R.triv) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) key
    rw [e] at hlaw
    exact ⟨hl.1, hlaw⟩
  · intro t κ hκ
    have hl : IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) 1 κ :=
      isLift_of_mem _ _ _ hκ
    have hl' := isLift_one D.sp.X' R.βX (R.datXt t)
    have key := GlobalTheory.T.lastVector_lift_pair_flagLevel_characters R hIs hInf hωX hvX t 1 κ 1 hl hl'
    have e : flag1L (R.datYt t (D.R.m - 1) R.triv) = R.datYt t (D.R.m - 1) R.triv := rfl
    have hlaw := law_of_pair (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) R.βX (R.datXt t) key
    rw [e] at hlaw
    exact ⟨hl.1, hlaw⟩

end GlobalTheory.Chain.SourceLaw

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftCuspObj

variable {D : D7}

theorem multT_induction {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S)
    (J : Set (GA D W)) (χ : GA D W → ℂ) (P : (GA D W → ℂ) → Prop) (h0 : P 0)
    (hadd : ∀ φ φ', P φ → P φ' → P (φ + φ')) (hsmul : ∀ (c : ℂ) φ, P φ → P (c • φ))
    (hcusp : ∀ φ, IsAutFunSm θ W φ → IsCuspFun W φ → P φ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) : P (F v) := by
  obtain ⟨T, hT, rfl⟩ := Submodule.mem_map.1 hF
  have key : ∀ m, P (T m) := by
    intro m
    have hT' : T ∈ Submodule.span ℂ {T | IsMultMap θ M J χ T} := hT
    clear hF hT
    induction hT' using Submodule.span_induction with
    | mem x hx => exact hcusp _ ((show IsMultMap θ M J χ x from hx).aut m) ((show IsMultMap θ M J χ x from hx).cusp m)
    | zero => simpa using h0
    | add x y _ _ hx hy => simpa using hadd _ _ hx hy
    | smul a x _ hx => simpa using hsmul a _ hx
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a m => simpa using hsmul a _ (key m)
  | add x y hx hy => simpa using hadd _ _ hx hy

theorem liftInt_add {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    {φ φ' : H → ℂ} {g : G} (h : IntegrableOn (fun x => th g x s * φ x) 𝓕 ν)
    (h' : IntegrableOn (fun x => th g x s * φ' x) 𝓕 ν) :
    Lift.liftInt ν 𝓕 th s (φ + φ') g = Lift.liftInt ν 𝓕 th s φ g + Lift.liftInt ν 𝓕 th s φ' g := by
  simp only [Lift.liftInt, Pi.add_apply, mul_add]
  exact integral_add h h'

theorem liftInt_smul {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (c : ℂ) (φ : H → ℂ) (g : G) :
    Lift.liftInt ν 𝓕 th s (c • φ) g = c * Lift.liftInt ν 𝓕 th s φ g := by
  simp only [Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  ext x
  ring

theorem liftInt_zero {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (g : G) : Lift.liftInt ν 𝓕 th s (0 : H → ℂ) g = 0 := by
  simp [Lift.liftInt]

structure Good {V V' W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ))
    (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (κ : Measure (NI V C)) (𝓝 : Set (NI V C))
    (f : WO V W → ℂ) (f' : WO V' W → ℂ) (g : GA D V) (c : ℂ) (φ : GA D W → ℂ) : Prop where
  integ : ∀ g₁, IntegrableOn (fun h => thetaKO ω g₁ h f * φ h) 𝓕 ν
  integ' : IntegrableOn (fun h => thetaKO ω' 1 h f' * φ h) 𝓕 ν
  mean : IntegrableOn (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g)) 𝓝 κ
  eq : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) ∂κ =
    c * Lift.liftInt ν 𝓕 (thetaKO ω') f' φ 1

section Good

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
  {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {κ : Measure (NI V C)} {𝓝 : Set (NI V C)}
  {f : WO V W → ℂ} {f' : WO V' W → ℂ} {g : GA D V} {c : ℂ}

theorem Good.zero : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c 0 := by
  refine ⟨fun _ => ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  ·
    simp only [liftInt_zero]
    exact integrableOn_zero
  · simp [liftInt_zero]

theorem Good.add {φ φ' : GA D W → ℂ} (h : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c φ)
    (h' : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c φ') : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c (φ + φ') := by
  have e : ∀ x : GA D V, Lift.liftInt ν 𝓕 (thetaKO ω) f (φ + φ') x =
      Lift.liftInt ν 𝓕 (thetaKO ω) f φ x + Lift.liftInt ν 𝓕 (thetaKO ω) f φ' x :=
    fun x => liftInt_add (h.integ x) (h'.integ x)
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, mul_add]
    exact Integrable.add (h.integ g₁) (h'.integ g₁)
  · simp only [Pi.add_apply, mul_add]
    exact Integrable.add h.integ' h'.integ'
  · simp only [e]
    exact Integrable.add h.mean h'.mean
  · simp only [e]
    rw [integral_add h.mean h'.mean, h.eq, h'.eq, liftInt_add h.integ' h'.integ', mul_add]

theorem Good.smul {φ : GA D W → ℂ} (a : ℂ) (h : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c φ) :
    Good C ω ω' ν 𝓕 κ 𝓝 f f' g c (a • φ) := by
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · have e : (fun x => thetaKO ω g₁ x f * (a • φ) x) = fun x => a * (thetaKO ω g₁ x f * φ x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Integrable.const_mul (h.integ g₁) a
  · have e : (fun x => thetaKO ω' 1 x f' * (a • φ) x) = fun x => a * (thetaKO ω' 1 x f' * φ x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Integrable.const_mul h.integ' a
  · simp only [liftInt_smul]
    exact Integrable.const_mul h.mean a
  · simp only [liftInt_smul]
    rw [integral_const_mul, h.eq]
    ring

end Good

theorem constTerm_multT (hct : TowerConstTerm D) (hP : GlobalTheory.Published.CuspRapidDecay)
    {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {χS χT χT' : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hω' : IsWeilDatumO ψ V' W χS χT' ω')
    {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν)
    {S : D.what₂.Tau → SPar} (M : DSModel W S) (J : Set (GA D W)) (χ : GA D W → ℂ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hlow : ∀ f', IsThetaFunO ψ V' W f' → Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) 1 = 0)
    (κ : Measure (NI V C)) (𝓝 : Set (NI V C)) (hκ : κ.IsHaarMeasure) (h𝓝 : IsFundamentalDomain (NIQ V C) 𝓝 κ)
    (g : GA D V) : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f (F v) ((n : GA D V) * g) ∂κ = 0 := by
  obtain ⟨μ, 𝓨, h𝓨⟩ : ∃ μ 𝓨, IsCovolOne (ratMx D W.rank r) μ 𝓨 := GlobalTheory.MixModel.exists_isCovolOne D W.rank r
  have hfor := hct V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 h𝓨 ν 𝓕 hν h𝓕 κ 𝓝 hκ h𝓝
  have hgood : Good C ω ω' ν 𝓕 κ 𝓝 f (res V V' W C B μ 𝓨 (ω (g, 1) f)) g ((κ 𝓝).toReal : ℂ) (F v) :=
    multT_induction θ M J χ
      (fun φ => Good C ω ω' ν 𝓕 κ 𝓝 f (res V V' W C B μ 𝓨 (ω (g, 1) f)) g ((κ 𝓝).toReal : ℂ) φ)
      Good.zero (fun _ _ h h' => Good.add h h') (fun a _ h => Good.smul a h)
      (fun φ hφ hc => by
        obtain ⟨-, -, -, h1, h2, h3, h4⟩ := hfor φ (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc) hc f hf g
        exact ⟨h1, h2, h3, h4⟩) F hF v
  obtain ⟨-, -, hres, -⟩ := hfor 0 GlobalTheory.Grow.RapidDec.zero (by intro _ _ _ _ _ _ _ _; simp) f hf g
  rw [hgood.eq, hlow _ hres, mul_zero]

theorem liftCusp : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    ∀ D : D7, GlobalTheory.Chain.LiftCusp D := by
  intro hDS hHC hP D k V W M M' θ ψ hθ hch ω hω ν 𝓕 hν h𝓕 J χ F hF v f hf r C hC κ 𝓝 hκ h𝓝 g
  obtain ⟨V', B, hs, hsig⟩ := GlobalTheory.T.exists_lowerWittTower_isotropicSplitEmbedding D V _ M r C hC
  have hr : 1 ≤ r := by
    obtain ⟨h0, -⟩ := hC
    exact h0
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  obtain ⟨ω', hW'⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hW.std V' W χS χT (Exists.intro η (And.intro h1 (And.intro h4 (And.intro h3 h2))))
    hW.hecS hW.hecT (resEta_parity hW.resS (by have := hs.rank; omega)) hW.resT
  have hst : GlobalTheory.Chain.IsStepWeil k ψ V' W ω' := Exists.intro χS (Exists.intro χT (And.intro hW' hexp))
  exact constTerm_multT (GlobalTheory.T.constantTermLift_isotropicSubspace D) hP hs hθ hW hW' hν h𝓕 M' J χ F hF v hf
    (fun f' hf' => congrFun (GlobalTheory.T.thetaLift_lowerTower_vanishing hDS hHC hP D k r V' W M' θ ψ hθ hch hr hsig ω' hst ν 𝓕 hν h𝓕 J χ F hF v f'
      hf') 1) κ 𝓝 hκ h𝓝 g

end GlobalTheory.LiftCuspObj

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.tameFunctional_kills_fockVacuum_realTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (ℓ : (WO S T → ℂ) → ℂ), Tame ψ S T ℓ → ∀ f, GlobalTheory.ChainFr.IsVacF ψ θ A B f → (∀ P, ℓ (GlobalTheory.ChainFr.ptF ψ θ A B f P) = 0) → ∀ w : WO S T, w.map (finPart D) = 0 → ℓ (heisO ψ S T w f) = 0 := by
  first | exact @GlobalTheory.FockTransl.tame_kills_real_translates | exact GlobalTheory.FockTransl.tame_kills_real_translates | (intros; apply GlobalTheory.FockTransl.tame_kills_real_translates <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.HandProd

theorem handP_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χA χz : (AE D)ˣ →* Circle) (omb : Om J.W₀ B.A) (omz : Om J.W₀ B.L), s.χW = χA * χz → IsWeilDatumO ψ J.W₀ B.A s.χV χA omb → IsWeilDatumO ψ J.W₀ B.L s.χV χz omz → ∀ (φ : GA D J.W₀ → ℂ) Ξ₁ Φ' Φ₀, IsThetaFunO ψ J.W₀ B.A Ξ₁ → IsThetaFunO ψ J.W₀ B.L Φ' → IsThetaFunO ψ J.W₀ B.L Φ₀ → handP s vL omz φ Φ₀ (B.o.boxT J.W₀ Ξ₁ Φ') = thPair vL.μ vL.𝓕 Φ' Φ₀ • liftT omb J.v0.μ J.v0.𝓕 φ Ξ₁ := by
  intro D ψ σ J B s vL χA χz omb omz hχ hb hz φ Ξ₁ Φ' Φ₀ h1 h' h0
  have hW₀ : IsWeilDatumO ψ J.W₀ B.V₀ s.χV (χA * χz) s.om₀ := hχ ▸ s.weil₀
  have tt := GlobalTheory.TensorTargetRule.tensorTarget D ψ hb.std B.V₀ B.A B.L B.o J.W₀
  funext h₁
  have hpt : ∀ h₀, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (B.o.boxT J.W₀ Ξ₁ Φ')) (omz (h₀, 1) Φ₀) 0 =
      omb (h₀, h₁) Ξ₁ 0 * thPair vL.μ vL.𝓕 Φ' Φ₀ := by
    intro h₀
    rw [tt.om_box s.χV χA χz s.om₀ omb omz hW₀ hb hz h₀ h₁ 1 Ξ₁ Φ' h1 h',
      ← GlobalTheory.WeilPairing.thPair_om_eq D ψ J.W₀ B.L s.χV χz omz hz vL (h₀, 1) Φ' Φ₀ h' h0]
    have e : (fun v => B.o.boxT J.W₀ (omb (h₀, h₁) Ξ₁) (omz (h₀, 1) Φ') ((B.o.resT J.W₀).symm (0, v))) =
        fun v => omb (h₀, h₁) Ξ₁ 0 * omz (h₀, 1) Φ' v := by
      funext v
      simp only [OrthDec.boxT, AddEquiv.apply_symm_apply]
    simp only [contractT, e, thPair]
    rw [← integral_const_mul]
    congr 1; funext w
    have ew := congrFun e w
    rw [ew]; ring
  simp only [handP, hpt, Pi.smul_apply, smul_eq_mul, liftT_apply]
  rw [← integral_const_mul]
  congr 1; funext h₀; ring

end GlobalTheory.HandProd

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.flatKernelPairing_rationalPoints_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∀ h, (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ ((γ * h₀), B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz ((γ * h₀), 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb ((γ * h₁), 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 := by
  first | exact @GlobalTheory.KerRat.flat_kernel_rat | exact GlobalTheory.KerRat.flat_kernel_rat | (intros; apply GlobalTheory.KerRat.flat_kernel_rat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


open GlobalTheory.RowLatChi in
theorem GlobalTheory.ColLatDict.mem_latO_iff_intM : ∀ {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)} {βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)}, IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ {e₁ : AE D} {P₁ : Finset (Pl D.host.E)}, IsIdemSum e₁ P₁ → (∀ w ∈ P₁, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ z : WO S T, IsHalf e₁ z → (z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ ∀ w ∈ P₁, GlobalTheory.StepData.IntM ((GlobalTheory.FunObj.Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w))) := by
  intro D S T ΛS ΛT βS βT hS hT hβS hβT e₁ P₁ hI hAA z hz
  have key : ∀ w, GlobalTheory.StepData.IntM ((GlobalTheory.FunObj.Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w)) ↔
      ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (z.map (toEAf D)) a b)) ≤ 1 := fun w => by
    rw [intM_iff]; rfl
  simp only [key]
  constructor
  · intro h w hw a b
    exact int_of_mem_latO hS hβS hβT w (hAA w hw).1 h a b
  · intro h
    exact mem_latO_of_mem_hatMx hS hI (fun w hw => (hAA w hw).2) hz (mem_hatMx_of_int hβS hβT hI hz h)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gridRowArrow_exists_common_realIntertwiner : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∀ (ω : T → GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V) (f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ), (∀ t, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) (ω t)) → GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f → ∃ It : GlobalTheory.Grid.Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M, ∀ t, IsItW R.θ (G.nV i j).M (G.nV i (j + 1)).M (ω t) (GlobalTheory.Grid.fock R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f) It := by
  first | exact @GlobalTheory.RowThetaIt.rowTheta_it | exact GlobalTheory.RowThetaIt.rowTheta_it | (intros; apply GlobalTheory.RowThetaIt.rowTheta_it <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.firstRowArgument_conjugateMove_left_mul_inv_component : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ w ∈ locPl G t, ∀ (k : FinPt G (.grid 0 D.R.m))
      (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      S.rowAt t w (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T))
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ (ys (GlobalTheory.FirstRowVertex.firstIx D)))) =
      Function.update (S.rowAt t w ys) 0 (((GlobalTheory.FirstRowTermLaw.kapAt S t w k)⁻¹ : GL (Fin ((locGrid G t w).rank (0, (locGrid G t w).m))) (Kw w)).val * S.rowAt t w ys 0) := by
  first | exact @GlobalTheory.FirstRowCoord.rowAt_first_move | exact GlobalTheory.FirstRowCoord.rowAt_first_move | (intros; apply GlobalTheory.FirstRowCoord.rowAt_first_move <;> assumption)
end
