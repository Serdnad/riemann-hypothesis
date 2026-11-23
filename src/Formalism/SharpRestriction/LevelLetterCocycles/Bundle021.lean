module

public import Formalism.DistinguishedUnitIdeals.FrobeniusCoboundedArc
public import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle017
public import Formalism.SharpRestriction.LevelLetterCocycles.PhiItSmul
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle002
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeMapMemLattice
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPosConstLagrangeCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle019
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
public import Mathlib.RingTheory.AdicCompletion.Topology
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

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
    {I : BaseId W} {T₁ T₂ : LocLat G Qp LL O}

def mapZ (F : LatHom T₁.L T₂.L) : ↥(W.wachCocyclesDelta T₁) →ₗ[O] ↥(W.wachCocyclesDelta T₂) :=
  (((W.map F).restrictScalars O).prodMap ((W.map F).restrictScalars O)).restrict
    (fun w hw => map_mem_Z1DΔ F ⟨w, hw⟩)

theorem mapZ_coe (F : LatHom T₁.L T₂.L) (w : ↥(W.wachCocyclesDelta T₁)) :
    (mapZ F w : W.DD T₂ × W.DD T₂) =
      (W.map F (w : W.DD T₁ × W.DD T₁).1, W.map F (w : W.DD T₁ × W.DD T₁).2) := rfl

def ZfDN (F : LatHom T₁.L T₂.L) : Submodule O (W.DD T₁ × W.DD T₁) :=
  ((latticeFiniteCohomology PD T₁.L).comap (W.clK T₁) ⊓
    LinearMap.eqLocus (F.H1map.comp (W.clK T₁)) ((W.clK T₂).comp (mapZ F))).map (W.wachCocyclesDelta T₁).subtype

def ZfN (C₁ : Coord W I T₁) (F : LatHom T₁.L T₂.L) :
    AddSubgroup ((ZMod n → C₁.V) × (ZMod n → C₁.V)) :=
  (ZfDN F).toAddSubgroup.comap (totP C₁)

theorem mem_ZfN (C₁ : Coord W I T₁) (F : LatHom T₁.L T₂.L)
    (κ : (ZMod n → C₁.V) × (ZMod n → C₁.V)) :
    κ ∈ ZfN C₁ F ↔ ∃ w : ↥(W.wachCocyclesDelta T₁), (W.clK T₁ w ∈ latticeFiniteCohomology PD T₁.L ∧
      F.H1map (W.clK T₁ w) = W.clK T₂ (mapZ F w)) ∧
      (w : W.DD T₁ × W.DD T₁) = (tot C₁ κ.1, tot C₁ κ.2) := by
  exact Iff.rfl

theorem ZfN_smul (C₁ : Coord W I T₁) (F : LatHom T₁.L T₂.L) (m : O)
    (κ : (ZMod n → C₁.V) × (ZMod n → C₁.V)) (h : κ ∈ ZfN C₁ F) :
    (PowerSeries.C m • κ.1, PowerSeries.C m • κ.2) ∈ ZfN C₁ F := by
  show totP C₁ (PowerSeries.C m • κ.1, PowerSeries.C m • κ.2) ∈ ZfDN F
  have e : totP C₁ (PowerSeries.C m • κ.1, PowerSeries.C m • κ.2) = m • totP C₁ κ := by
    show (tot C₁ (PowerSeries.C m • κ.1), tot C₁ (PowerSeries.C m • κ.2)) =
      m • (tot C₁ κ.1, tot C₁ κ.2)
    rw [tot_smulC, tot_smulC]
    rfl
  rw [e]
  exact (ZfDN F).smul_mem m h

theorem liftF_ofN {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂}
    (h : CoordHom C₁ C₂ F) (hs : W.s = 1) (hp : PD.p ≠ 2) (herr : Formalism.MainNotions.DeltaInvariantLattices.p2aK W T₂) (e : ℕ)
    (key : ∀ κ ∈ Zf C₂, ∃ κ₁ ∈ ZfN C₁ F,
      (latOf C₂).IsCobound (I.Bs.lc ^ e • κ.1 - fun i => (latHomOf h).f (κ₁.1 i))
        (I.Bs.lc ^ e • κ.2 - fun i => (latHomOf h).f (κ₁.2 i))) :
    F.LiftF PD e := by
  intro c hc
  have hcZ : c ∈ latticeCocycles T₂.L := hc.1
  have hcls : (Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) : LatticeCohomology T₂.L) ∈ latticeFiniteCohomology PD T₂.L :=
    ⟨⟨c, hcZ⟩, hc, rfl⟩
  obtain ⟨hsurj, hker⟩ := herr hs hp
  obtain ⟨w, hw⟩ : ∃ w : ↥(W.wachCocyclesDelta T₂), W.clK T₂ w =
      Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) := hsurj _
  obtain ⟨-, hwa, hwb⟩ := (mem_Z1DΔ (w : W.DD T₂ × W.DD T₂).1 (w : W.DD T₂ × W.DD T₂).2).1 w.2
  obtain ⟨y, hy⟩ := tot_surj C₂ _ hwa
  obtain ⟨z, hz⟩ := tot_surj C₂ _ hwb
  have hκ : (y, z) ∈ Zf C₂ := (mem_Zf C₂ _).2 ⟨w, hw ▸ hcls, Prod.ext hy.symm hz.symm⟩
  obtain ⟨κ₁, hκ₁, m, hm1, hm2⟩ := key _ hκ
  obtain ⟨w₁, ⟨hw₁f, hnat⟩, hw₁⟩ := (mem_ZfN C₁ F _).1 hκ₁
  have hzero : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w - mapZ F w₁) = 0 := by
    refine (hker _).2 ⟨tot C₂ m, fun δ hδ => tot_Δ C₂ m δ hδ, ?_⟩
    have e1 := congrArg (tot C₂) hm1
    have e2 := congrArg (tot C₂) hm2
    rw [tot_sub, lc_pow, tot_smulC, tot_map, tot_dφ] at e1
    rw [tot_sub, lc_pow, tot_smulC, tot_map, tot_dγ] at e2
    have a1 : tot C₁ κ₁.1 = (w₁ : W.DD T₁ × W.DD T₁).1 := by rw [hw₁]
    have a2 : tot C₁ κ₁.2 = (w₁ : W.DD T₁ × W.DD T₁).2 := by rw [hw₁]
    rw [a1] at e1
    rw [a2] at e2
    simp only at e1 e2
    rw [hy] at e1
    rw [hz] at e2
    exact Prod.ext e1 e2
  have e3 : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w - mapZ F w₁) =
      (((PD.p : ℕ) : O) ^ e) • W.clK T₂ w - W.clK T₂ (mapZ F w₁) :=
    ((W.clK T₂).map_sub ((((PD.p : ℕ) : O) ^ e) • w) (mapZ F w₁)).trans
      (congrArg (· - W.clK T₂ (mapZ F w₁)) ((W.clK T₂).map_smul _ w))
  have hz2 : (((PD.p : ℕ) : O) ^ e) • (Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) : LatticeCohomology T₂.L) =
      F.H1map (W.clK T₁ w₁) := by
    rw [hnat, ← hw]
    exact sub_eq_zero.1 (e3.symm.trans hzero)
  obtain ⟨c₁, hc₁, hc₁e⟩ := hw₁f
  rw [← hc₁e] at hz2
  have hq : (Submodule.Quotient.mk ((((PD.p : ℕ) : O) ^ e) • (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L))) : LatticeCohomology T₂.L) =
      Submodule.Quotient.mk (⟨F.post c₁, F.post_Z1T _ c₁.2⟩ : ↥(latticeCocycles T₂.L)) := hz2
  have hB := (Submodule.Quotient.eq _).1 hq
  have hB' : (((PD.p : ℕ) : O) ^ e) • c - F.post c₁ ∈ latticeCoboundaries T₂.L := hB
  have : (((PD.p : ℕ) : O) ^ e) • c = F.post c₁ + ((((PD.p : ℕ) : O) ^ e) • c - F.post c₁) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hc₁) hB'

theorem map_NΔ (F : LatHom T₁.L T₂.L) (h₁ : IsCrys PD T₁.ρ) (h₂ : IsCrys PD T₂.ρ) {x : W.DD T₁}
    (hx : x ∈ W.NΔ T₁) : W.map F x ∈ W.NΔ T₂ := by
  unfold Formalism.BasicNotions.LocWach.NΔ at hx ⊢
  obtain ⟨hN, hΔ⟩ := hx
  refine ⟨W.map_N F h₁ h₂ _ hN, fun δ hδ => ?_⟩
  rw [← W.map_γ, hΔ δ hδ]

theorem map_mulSet (F : LatHom T₁.L T₂.L) (h₁ : IsCrys PD T₁.ρ) (h₂ : IsCrys PD T₂.ρ) (a : LetA O n) {x : W.DD T₁}
    (hx : x ∈ mulSet W T₁ a (W.NΔ T₁)) : W.map F x ∈ mulSet W T₂ a (W.NΔ T₂) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨W.map F y, map_NΔ F h₁ h₂ hy, map_smulA W F a y⟩

theorem frobenius_cocycle_map (F : LatHom T₁.L T₂.L) (h₁ : IsCrys PD T₁.ρ) (h₂ : IsCrys PD T₂.ρ) (M : ℕ) (c : ZMod n) (x : ↥(W.wachCocyclesDelta T₁))
    (hx : HerrCocycleAtLetter W T₁ M c x) : HerrCocycleAtLetter W T₂ M c (mapZ F x) := by
  obtain ⟨h1, h2, h3⟩ := hx
  unfold HerrCocycleAtLetter
  simp only [mapZ_coe]
  refine ⟨?_, ?_, ?_⟩
  · unfold InLetter at h1 ⊢
    rw [← map_smulA W F, h1]
  · rw [← W.map_γ, ← map_sub]
    exact map_mulSet F h₁ h₂ _ h2
  · exact map_mulSet F h₁ h₂ _ h3

theorem frobenius_cocycle_of_rho_data {T : LocLat G Qp LL O} (hF1 : F1 W) (hcr : IsCrys PD T.ρ) (hh M : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(hh : ℤ)) hh))
    (hM : hh < (PD.p - 1) * M) (C : Coord W I T) (c : ZMod n) (w : C.V) (j g sig : ℕ)
    (y z : ZMod n → C.V) (hρ : (latOf C).IsRho c j M g sig w y z)
    (hZ : (tot C y, tot C z) ∈ W.wachCocyclesDelta T) : HerrCocycleAtLetter W T M (c + (j : ZMod n)) ⟨_, hZ⟩ := by
  obtain ⟨τ, -, hy, -, hz⟩ := hρ
  have hzM := tot_sm C M z hz
  refine ⟨?_, ?_, hzM⟩
  · change (letE (c + (j : ZMod n)) : LetA O n) • tot C y = tot C y
    rw [hy, tot_single]
    exact C.t_letter _ _
  · change W.γD T W.gamK (tot C y) - tot C y ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T)
    rw [((mem_Z1DΔ _ _).1 hZ).1]
    obtain ⟨x, hx, hxz⟩ := hzM
    obtain ⟨x', hx', hφ⟩ := ((hF1 hh M hM).1 T hcr hJ).1 x hx
    refine ⟨I.d I.Bs.q • x' - x, (W.NΔ T).sub_mem (d_smul_NΔ _ hx') hx, ?_⟩
    rw [hxz, hφ, smul_sub, I.d_q, mul_smul]

theorem rho_fieldN (hF1 : F1 W) (hF2 : F2 W) (F : LatHom T₁.L T₂.L) (hcr₁ : IsCrys PD T₁.ρ)
    (hcr₂ : IsCrys PD T₂.ρ) (hh : ℕ)
    (hJ₁ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(hh : ℤ)) hh))
    (hJ₂ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₂.ρ τ (Set.Icc (-(hh : ℤ)) hh)) (hp : 2 ≤ PD.p)
    (C : Coord W I T₁) (h5 : ∀ i, (latOf C).P5M i hh) (Cu : Formalism.ExponentWindows.E.Cuts n) (H : ZMod n → ℕ → ℕ)
    (j g sig : ℕ) :
    ∀ c ∈ Cu.cuts, ∀ w, (latOf C).Wc Cu (Formalism.ExponentWindows.E.LamOf I.Bs Cu H) c w →
      ∀ y z, (latOf C).IsRho c j (Formalism.ExponentWindows.E.parM I.Bs.ℓ hh g) g sig w y z → (y, z) ∈ ZfN C F := by
  intro c hc w hw y z hρ
  have hM : hh < (PD.p - 1) * Formalism.ExponentWindows.E.parM I.Bs.ℓ hh g := by
    rw [Formalism.ExponentWindows.E.parM, I.ℓ_eq]
    have := Nat.lt_mul_div_succ (hh + 2 * g) (show 0 < PD.p - 1 by omega)
    omega
  obtain ⟨x, hxf, hx⟩ := (mem_Zf C _).1 (rho_field hF1 hF2 hcr₁ hh hJ₁ hp C h5 Cu H j g sig c hc w hw y z hρ)
  have hZ : (tot C y, tot C z) ∈ W.wachCocyclesDelta T₁ := hx ▸ x.2
  have hxe : x = ⟨_, hZ⟩ := Subtype.ext hx
  have hcoc := frobenius_cocycle_of_rho_data hF1 hcr₁ hh _ hJ₁ hM C c w j g sig y z hρ hZ
  rw [← hxe] at hcoc
  refine (mem_ZfN C F _).2 ⟨x, ⟨hxf, ?_⟩, hx⟩
  exact ((hF1 hh _ hM).2 T₁ T₂ F hcr₁ hcr₂ hJ₁ hJ₂ (c + (j : ZMod n)) x (mapZ F x) hcoc
    (frobenius_cocycle_map F hcr₁ hcr₂ _ _ x hcoc) rfl).symm

end Formalism.MainNotions.WachCoordinates.Br
end
end

section

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.OL

open Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

theorem complete_of_pow {R : Type*} [CommRing R] (J : Ideal R) {n : ℕ} (hn : 0 < n)
    (h : IsAdicComplete (J ^ n) R) : IsAdicComplete J R := by
  let : WithIdeal R := ⟨J⟩
  have hJ : IsAdic J := rfl
  have hJn : IsAdic (J ^ n) := is_ideal_adic_pow hJ hn
  rw [hJ.isAdicComplete_iff]
  exact hJn.isAdicComplete_iff.mp h

variable {l : ℕ} [Fact l.Prime]

theorem l_ne_zero (LL : FinExt l) : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
  intro h
  have h2 := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h
  simp only [ZeroMemClass.coe_zero, SubringClass.coe_natCast] at h2
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)

theorem l_not_unit (P : LocPrime l) (LL : FinExt l) : ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro hu
  have h0 := Formalism.MainNotions.LiftingTheory.zl_v_unit P LL hu.unit
  have h1 := Formalism.MainNotions.LiftingTheory.zl_v_pow P LL 1
  rw [IsUnit.unit_spec, map_natCast] at h0
  rw [pow_one, h0] at h1
  exact absurd h1 (by simp)

theorem l_mem_max (P : LocPrime l) (LL : FinExt l) :
    letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
    ((l : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) := by
  let := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 (l_not_unit P LL))

theorem OL_dvr (P : LocPrime l) (LL : FinExt l) : IsDiscreteValuationRing ↥(OL LL) := by
  letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  have hfd : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hded : IsDedekindDomain ↥(OL LL) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have hnf : ¬ IsField ↥(OL LL) := fun hf => by
    have hm := l_mem_max P LL
    rw [isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot] at hm
    exact l_ne_zero LL hm
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 1 3).mpr hded

theorem OL_complete_max (P : LocPrime l) (LL : FinExt l) :
    letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
    IsAdicComplete (maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  have := OL_dvr P LL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hl0 : Ideal.span {((l : ℕ) : ↥(OL LL))} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact l_ne_zero LL
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hl0 hϖ
  have hC := Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  rw [he, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at hC
  refine complete_of_pow _ (n := e) (Nat.pos_of_ne_zero ?_) hC
  rintro rfl
  rw [pow_zero, Ideal.one_eq_top] at hC
  exact not_subsingleton _ hC.subsingleton

end Formalism.MainNotions.CrystallineLiftingInputs.OL
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def DownSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelFR D HW → DownSlotProposition D HW

def UpSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelFR D HW → UpSlotProposition D HW

def MixedSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → DdRFull D → DiRank D HW F Cm → modelFR D HW → MixedSlotProposition D HW

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.UnusedSlot80.BCW

variable {l : ℕ} [Fact l.Prime]



theorem bcAt_fin (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) (Th : LocTheory) (K LL LL' : FinExt l)
    (hLL : LL.1 ≤ LL'.1) :
    Formalism.MainNotions.WachCoordinates.BCAt ((Th l).PD K) (LL := ↥LL.1) (O := ↥(OL LL)) (O' := ↥(OL LL'))
      (IntermediateField.inclusion hLL) := by
  letI iA : Algebra ↥LL.1 ↥LL'.1 := (IntermediateField.inclusion hLL).toRingHom.toAlgebra
  haveI tA : IsScalarTower ℚ_[l] ↥LL.1 ↥LL'.1 :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion hLL).commutes x).symm
  letI iO : Algebra ↥(OL LL) ↥(OL LL') := (jO hLL).toAlgebra
  letI sO : SMul ↥(OL LL) ↥(OL LL') := iO.toSMul
  haveI t1 : IsScalarTower ↥(OL LL) ↥(OL LL') ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := isFrac_OL LL
  have hc : Continuous (algebraMap ↥LL.1 ↥LL'.1) := by
    refine continuous_induced_rng.2 ?_
    exact continuous_subtype_val
  have hO' : Function.Injective (algebraMap ↥(OL LL') ↥LL'.1) := Subtype.val_injective
  have hjO : Function.Injective (algebraMap ↥(OL LL) ↥(OL LL')) := by
    intro a b h
    have h1 := congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) h
    exact Subtype.ext (Subtype.ext h1)

  haveI tZ : IsScalarTower ℤ_[l] ↥(OL LL) ↥(OL LL') := IsScalarTower.of_algebraMap_eq fun z => by
    apply Subtype.ext; apply Subtype.ext
    show ((algebraMap ℤ_[l] ↥(OL LL') z : ↥LL'.1) : Om l) = ((algebraMap ℤ_[l] ↥(OL LL) z : ↥LL.1) : Om l)
    simp only [SubalgebraClass.coe_algebraMap]
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
    rfl
  haveI : Module.Finite ↥(OL LL) ↥(OL LL') := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI : FaithfulSMul ↥(OL LL) ↥(OL LL') := (faithfulSMul_iff_algebraMap_injective _ _).2 hjO
  haveI : Module.IsTorsionFree ↥(OL LL) ↥(OL LL') := ⟨fun r hr a b hab => by
    have hr0 : algebraMap ↥(OL LL) ↥(OL LL') r ≠ 0 := fun h => hr.ne_zero (hjO (h.trans (map_zero _).symm))
    simp only [Algebra.smul_def] at hab
    exact mul_left_cancel₀ hr0 hab⟩
  haveI : Module.Free ↥(OL LL) ↥(OL LL') := Module.free_of_finite_type_torsion_free'
  let bO := Module.Free.chooseBasis ↥(OL LL) ↥(OL LL')

  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : IsIntegralClosure ↥(OL LL') ℤ_[l] ↥LL'.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL'.1
  haveI : IsLocalization (Algebra.algebraMapSubmonoid ↥(OL LL') (nonZeroDivisors ℤ_[l])) ↥LL'.1 :=
    IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] ↥LL'.1 ↥(OL LL')
  let b : Module.Free.ChooseBasisIndex ↥(OL LL) ↥(OL LL') → ↥LL'.1 :=
    fun i => algebraMap ↥(OL LL') ↥LL'.1 (bO i)
  have hliO : LinearIndependent ↥(OL LL) b :=
    bO.linearIndependent.map' (IsScalarTower.toAlgHom ↥(OL LL) ↥(OL LL') ↥LL'.1).toLinearMap
      (LinearMap.ker_eq_bot.2 hO')
  have hli : LinearIndependent ↥LL.1 b := linInd_frac (O := ↥(OL LL)) b hliO
  have hy : ∀ a : ↥(OL LL'), algebraMap ↥(OL LL') ↥LL'.1 a ∈ Submodule.span ↥LL.1 (Set.range b) := by
    intro a

    haveI : AddMonoidHomClass (↥(OL LL') →+* ↥LL'.1) ↥(OL LL') ↥LL'.1 :=
      (RingHom.instRingHomClass (α := ↥(OL LL')) (β := ↥LL'.1)).toAddMonoidHomClass
    rw [← bO.sum_repr a, map_sum (algebraMap ↥(OL LL') ↥LL'.1)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : algebraMap ↥(OL LL') ↥LL'.1 (bO.repr a i • bO i) =
        (algebraMap ↥(OL LL) ↥LL.1 (bO.repr a i)) • b i := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span ↥LL.1 (Set.range b) := by
    intro x _
    obtain ⟨⟨a, s⟩, hx⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid ↥(OL LL') (nonZeroDivisors ℤ_[l])) x
    obtain ⟨z, hz, hzs⟩ := s.2
    have e1 : algebraMap ↥(OL LL') ↥LL'.1 (s : ↥(OL LL')) = algebraMap ℚ_[l] ↥LL'.1 (z : ℚ_[l]) := by
      rw [← hzs, ← IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL') ↥LL'.1,
        IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1]
      rfl
    have hz0 : (z : ℚ_[l]) ≠ 0 := by
      intro h0
      exact nonZeroDivisors.coe_ne_zero ⟨z, hz⟩ (PadicInt.coe_eq_zero.1 h0)
    have hq : algebraMap ℚ_[l] ↥LL'.1 (z : ℚ_[l]) ≠ 0 := (map_ne_zero _).2 hz0
    have hxe : x = algebraMap ↥LL.1 ↥LL'.1 (algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l])⁻¹) *
        algebraMap ↥(OL LL') ↥LL'.1 a := by
      rw [← IsScalarTower.algebraMap_apply, map_inv₀, ← hx, e1]
      field_simp
    rw [hxe, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hy a)
  let bL := Module.Basis.mk hli hsp
  have hb : ∀ i, bL i = algebraMap ↥(OL LL') ↥LL'.1 (bO i) := fun i => Module.Basis.mk_apply hli hsp i
  have hlin : ∀ φ : ↥LL'.1 →ₗ[↥LL.1] ↥LL.1, Continuous φ := fun φ =>
    LinearMap.continuous_of_finiteDimensional (φ.restrictScalars ℚ_[l])
  have hk : lenOl ((Th l).PD K) (O := ↥(OL LL)) ≠ ⊤ := by
    have hp : (((((Th l).PD K).p : ℕ)) : ↥(OL LL)) ≠ 0 := by
      rw [(Th l).PD_p K]
      intro h0
      have h1 := congrArg (algebraMap ↥(OL LL) ↥LL.1) h0
      rw [map_natCast, map_zero] at h1
      exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
    obtain ⟨k, hk⟩ := Formalism.MainNotions.RamifiedCoefficientChains.len_quot_nat _ hp
    unfold lenOl
    rw [hk]
    exact ENat.natCast_ne_top k
  have e : IsScalarTower.toAlgHom ℚ_[l] ↥LL.1 ↥LL'.1 = IntermediateField.inclusion hLL :=
    AlgHom.ext fun _ => rfl
  rw [← e]
  exact bcAt_desc ((Th l).PD K) hc hO' hJ bO bL hb hlin hk

theorem base_change_of_coefficient_jump (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) (Th : LocTheory) : Formalism.MainNotions.WachCoordinates.admBC Th := by
  intro l _ K LL LL' hLL
  exact bcAt_fin hJ Th K LL LL' hLL

theorem base_change_statement_of_jump (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) (D : D7) : Formalism.MainNotions.UnusedSlot80.H1fBaseChangeTheorem D :=
  base_change_of_coefficient_jump hJ D.loc

end Formalism.MainNotions.UnusedSlot80.BCF
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions

open Formalism.MainNotions.N.TwAll

def TwGoodAtAll (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → I.Ok (C.twI w) ∧ TwGoodAll D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

end Formalism.MainNotions
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def InvLiftStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → invLiftR D HW

def ClassMapStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → classMapR D HW

def FrameStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → frameR D HW

end Formalism.MainNotions.N.Ln34

end
end
