module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle016
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle014
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic

@[expose] public section

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section DefsR

variable (D : Formalism.BasicNotions.D7)

def UPair {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule D.host.E (VS D).V :=
  Submodule.span D.host.E (Set.range F0.fvec ∪ Set.range F'.fl.fvec)

def UUS {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule (𝓞 D.host.E) (VS D).V :=
  XS D F0 ⊔ Submodule.span (𝓞 D.host.E) {F0.z} ⊔ XS D F'.fl ⊔ Submodule.span (𝓞 D.host.E) {F'.fl.z}

def MMg {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule (𝓞 D.host.E) (VS D).V :=
  Submodule.span (𝓞 D.host.E)
    (Set.range F0.fvec ∪ Set.range fun b => ((gS D : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b))

def MMof {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule (𝓞 D.host.E) (VS D).V :=
  ⨅ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
    haveI := P.isPrime
    if ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal then Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MMg D F0 F')
    else Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UUS D F0 F')

def cOne (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] : ℝ :=
  if hc : ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c then hc.choose else 1

def cMass (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (j : ℕ) : ℝ :=
  cOne K F * ∏ i ∈ Finset.Icc 2 j, Formalism.HermitianLatticesTheory.massRatioRightSide K i

def IsGlueReps {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V)
    (M : Submodule (𝓞 K) V) (s : Finset (Submodule (𝓞 K) V)) : Prop :=
  (∀ Λ ∈ s, Λ ∈ GlueSet h U M) ∧
  (∀ Λ ∈ GlueSet h U M, ∃! Λ₁, Λ₁ ∈ s ∧ ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g Λ₁ = Λ) ∧
  (∀ Λ ∈ s, (stabFix h U Λ).Finite)

def cExpl {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : ℝ :=
  cMass D.host.E D.host.F (D.R.k - 1) *
    |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ)) *
    (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i) / Formalism.MainNotions.S.Cnt.massRows D F0 what₂

end DefsR

def HostDict : Prop :=
  ∀ D : Formalism.BasicNotions.D7, Formalism.HermitianLatticesTheory.IsCMUnram D.host.E ∧ IsFixF D.host.E D.host.F ∧ Nondeg (VS D).hT

def RatPair : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ Z : MatZ D, Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        ∃ F' : LFlag (D.sp.Y 0) D.R.rS (Tn u'), F'.zt = F'.fl.z ∧ ZhatL (lf D F0) F' = Z

def PerpDef : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        IsCompl (UPair D F0 F') (orthK (VS D).hT (UPair D F0 F')) ∧
        PosDefOn (VS D).hT (orthK (VS D).hT (UPair D F0 F')) ∧
        finrank D.host.E (UPair D F0 F') = D.R.m ∧
        finrank D.host.E (orthK (VS D).hT (UPair D F0 F')) = D.R.k - 1

def MMChar : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        IsLatIn (UPair D F0 F') (MMof D F0 F') ∧
        ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V,
          (IsRowLat D F0 Λ ∧ F' ∈ EZ (Tn u') F0 Λ Z) ↔ Λ ∈ GlueSet (VS D).hT (UPair D F0 F') (MMof D F0 F')

def RowsGroupoid : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        ∀ s : Finset (Submodule (𝓞 D.host.E) (VS D).V),
          IsGlueReps (VS D).hT (UPair D F0 F') (MMof D F0 F') s →
          nu (Tn u') F0 what₂ Z * Formalism.MainNotions.S.Cnt.massRows D F0 what₂ =
            ∑ Λ ∈ s, ((Nat.card (stabFix (VS D).hT (UPair D F0 F') Λ) : ℕ) : ℝ)⁻¹

def NormMM : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') →
        nM D.host.F (VS D).hT (UPair D F0 F') (MMof D F0 F') =
          |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) * sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z

def RowsMass : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
        Formalism.MainNotions.S.Cnt.massRows D F0 what₂ =
          cMass D.host.E D.host.F D.R.k * ((D.mem u).A.T : ℝ) ^ (D.R.k * finrank ℚ D.host.F) *
            ∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
              (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
                1 - etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1)

end Formalism.L2.SG.Pf.Cnt
end
end

section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem div_mul_mul' {x y z : K} (hz : z ≠ 0) : x / z * (z * y) = x * y := by
  rw [div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ hz]

structure JD (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) {m : ℕ}
    (b : Fin m → V) (a : Fin m → 𝓞 F) : Prop where
  orth : ∀ i j, i ≠ j → h (b i) (b j) = 0
  diag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)
  ne : ∀ i, a i ≠ 0
  loc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L
  fix : IsFixF K F
  max : 𝔭.IsMaximal
  lat : IsLatIn ⊤ L

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

namespace JD

variable (J : JD h L 𝔭 b a)
include J

theorem bX : ∀ i, b i ∈ (⊤ : Submodule K V) := fun _ => Submodule.mem_top

theorem memB (x : V) : x ∈ locF 𝔭 L ↔ ∀ i, haveI := J.max.isPrime; crd h b a x i ∈ HU.SP K 𝔭 :=
  mem_B J.orth J.diag J.ne J.bX J.loc J.max.isPrime J.lat x

theorem memA (x : V) : x ∈ locF 𝔭 (dualIn h ⊤ L) ↔
    ∀ i, haveI := J.max.isPrime; jK (ι (a i)) * crd h b a x i ∈ HU.SP K 𝔭 :=
  mem_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat x

theorem crdG (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x : V) (k : Fin m) :
    crd h b a (gmap h b a Y x) k = ∑ j, jK (Y k j) * crd h b a x j :=
  crd_gmap J.orth J.diag J.ne Y x k

theorem h_sub_mem (x y x' y' : V) (hx : x ∈ locF 𝔭 (dualIn h ⊤ L)) (hy : y ∈ locF 𝔭 (dualIn h ⊤ L))
    (hx' : x' - x ∈ locF 𝔭 L) (hy' : y' - y ∈ locF 𝔭 L) :
    haveI := J.max.isPrime; h x' y' - h x y ∈ HU.SP K 𝔭 := by
  have := J.max.isPrime
  have hAB := h_AB J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat
  have e : h x' y' - h x y = h x (y' - y) + h (x' - x) y + h (x' - x) (y' - y) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  rw [e]
  refine add_mem (add_mem (hAB x _ hx hy').1 (hAB y _ hy hx').2) (hAB _ _ ?_ hy').1
  exact B_le_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat _ hx'

def E (Y : Matrix (Fin m) (Fin m) (𝓞 K))
    (hY : ∀ i j, haveI := J.max.isPrime; jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭) :
    Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) :=
  endoOf h L 𝔭 (gmap h b a Y) (gmap_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y hY)
    (gmap_B J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y)

theorem E_mk (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (hY) (x : ↥(locF 𝔭 (dualIn h ⊤ L))) :
    J.E Y hY (Submodule.Quotient.mk x) = Submodule.Quotient.mk
      ⟨gmap h b a Y x, gmap_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y hY x x.2⟩ := rfl

theorem E_isom (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (hY)
    (hW : ∀ i j, haveI := J.max.isPrime;
      jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) ∈ HU.SP K 𝔭) :
    ∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
      Submodule.Quotient.mk x' = J.E Y hY (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = J.E Y hY (Submodule.Quotient.mk y) →
      h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have := J.max.isPrime
  intro x y x' y' hx hy
  rw [E_mk, Submodule.Quotient.eq, Submodule.mem_comap] at hx hy
  simp only [Submodule.subtype_apply, Submodule.coe_sub] at hx hy
  have gA := gmap_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y hY
  rw [← HU.mem_SP_iff_locF]
  have e : h (x' : V) (y' : V) - h (x : V) (y : V) =
      (h (x' : V) (y' : V) - h (gmap h b a Y x) (gmap h b a Y y)) +
        (h (gmap h b a Y x) (gmap h b a Y y) - h (x : V) (y : V)) := by ring
  rw [e]
  refine add_mem (J.h_sub_mem _ _ _ _ (gA _ x.2) (gA _ y.2) hx hy) ?_
  rw [form_identity J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  have hxA := (J.memA x).1 x.2 i
  have hyA := (J.memA y).1 y.2 j
  have hne : jK (ι (a i)) * jK (ι (a j)) ≠ 0 := mul_ne_zero (jK_ι_ne_zero (J.ne i)) (jK_ι_ne_zero (J.ne j))
  have e2 : star (jK (ι (a i)) * crd h b a x i) * (jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j)))) *
      (jK (ι (a j)) * crd h b a y j) = star (crd h b a x i) * jK (gramO a Y i j) * crd h b a y j := by
    rw [star_mul', star_jK_ι J.fix,
      show jK (ι (a i)) * star (crd h b a x i) * (jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j)))) *
        (jK (ι (a j)) * crd h b a y j) = star (crd h b a x i) * jK (gramO a Y i j) * crd h b a y j *
          ((jK (ι (a i)) * jK (ι (a j))) / (jK (ι (a i)) * jK (ι (a j)))) by ring,
      div_self hne, mul_one]
  rw [← e2]
  exact mul_mem (mul_mem (star_mem_SP J.fix hxA) (hW i j)) hyA

theorem E_eq_of (Y Y' : Matrix (Fin m) (Fin m) (𝓞 K)) (hY hY')
    (hd : ∀ i j, haveI := J.max.isPrime; jK (Y i j - Y' i j) / jK (ι (a j)) ∈ HU.SP K 𝔭) :
    J.E Y hY = J.E Y' hY' := by
  have := J.max.isPrime
  refine Submodule.quot_hom_ext _ _ _ fun x => ?_
  simp only [E_mk]
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]
  rw [J.memB]
  intro k
  rw [crd_sub, J.crdG, J.crdG, ← Finset.sum_sub_distrib]
  refine sum_mem fun j _ => ?_
  rw [← sub_mul, ← map_sub, ← div_mul_mul' (jK_ι_ne_zero (J.ne j))]
  exact mul_mem (hd k j) ((J.memA x).1 x.2 j)

theorem crd_u (j l : Fin m) :
    crd h b a (phi (K := K) b a (Pi.single j 1)) l = if l = j then 1 / jK (ι (a j)) else 0 := by
  rw [crd, h_phi J.orth J.diag J.ne]
  by_cases hl : l = j
  · subst hl; simp
  · simp [Pi.single_apply, hl]

theorem u_mem (j : Fin m) : phi (K := K) b a (Pi.single j 1) ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := J.max.isPrime
  rw [J.memA]
  intro i
  rw [← h_b J.orth J.diag J.ne, h_phi J.orth J.diag J.ne]
  exact HU.jK_mem_SP _

theorem sum_crd_u (f : Fin m → K) (j : Fin m) :
    ∑ l, f l * crd h b a (phi (K := K) b a (Pi.single j 1)) l = f j / jK (ι (a j)) := by
  rw [Finset.sum_eq_single j]
  · rw [J.crd_u, ite_eq_left rfl, mul_one_div]
  · intro l _ hl; rw [J.crd_u, ite_eq_right hl, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem entry_of_E_eq (Y Y' : Matrix (Fin m) (Fin m) (𝓞 K)) (hY hY') (he : J.E Y hY = J.E Y' hY')
    (i j : Fin m) : haveI := J.max.isPrime; jK (Y i j - Y' i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
  have := J.max.isPrime
  have h1 := congrArg (fun f => f (Submodule.Quotient.mk ⟨_, J.u_mem j⟩)) he
  simp only [E_mk] at h1
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
    J.memB] at h1
  have h2 := h1 i
  rw [crd_sub, J.crdG, J.crdG, J.sum_crd_u, J.sum_crd_u, ← sub_div, ← map_sub] at h2
  exact h2

end JD

end Formalism.L2.SG.Pf.fibreCountingData
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.BoxVolSk

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def GramMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ) (T : Matrix (Fin a) (Fin a) E),
    MeasurableSet {x : Fin a → Fin n → Af F ⊗[F] E | gramR (Af F) σ J x ≠ T.map (inclR (Af F))} ∧
    (∀ y : Fin a → Fin n → AF F ⊗[F] E, gramR (AF F) σ J y = T.map (inclR (AF F)) →
      gramR (Af F) σ J (projFin y) = T.map (inclR (Af F))) ∧
    (∀ x : Fin a → Fin n → Af F ⊗[F] E, gramR (Af F) σ J x = T.map (inclR (Af F)) →
      ∀ v, gramR (Fv F v) σ J (projV v x) = T.map (inclR (Fv F v)))

def PosTest : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ)
    (μ : Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
    (fib : HermR (Ainf F) σ a → Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (t : HermR (Ainf F) σ a),
    IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib →
    fib t ≠ 0 →
    ∃ Φ : (Fin a → Fin n → Ainf F ⊗[F] E) → ℝ, Continuous Φ ∧ HasCompactSupport Φ ∧ (∀ x, 0 ≤ Φ x) ∧
      Integrable Φ (fib t) ∧ 0 < ∫ x, Φ x ∂(fib t)

def FinInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n a d : ℕ) (b : Module.Basis (Fin d) F E) (x : Fin a → Fin n → Af F ⊗[F] E),
    ∀ᶠ v in Filter.cofinite, projV v x ∈ latV b v

def BoxMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n a : ℕ) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E)),
    (∀ v, MeasurableSet (C v)) → MeasurableSet {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v}

theorem BoxVolSk_tprod_ofReal {ι : Type} (r : ι → ℝ) (hm : Multipliable (fun i => (r i : ℂ))) :
    ∏' i, (r i : ℂ) = ((∏' i, r i : ℝ) : ℂ) := by
  obtain ⟨L, hL⟩ := hm
  have hclosed : IsClosed (Set.range ((↑) : ℝ → ℂ)) := Complex.isometry_ofReal.isClosedEmbedding.isClosed_range
  have hmem : L ∈ Set.range ((↑) : ℝ → ℂ) :=
    hclosed.mem_of_tendsto hL (Filter.Eventually.of_forall fun s => ⟨∏ i ∈ s, r i, by rw [Complex.ofReal_prod]⟩)
  obtain ⟨l, rfl⟩ := hmem
  have hr : HasProd r l :=
    (Complex.isometry_ofReal.isEmbedding.isInducing.hasProd_iff (g := Complex.ofRealHom) (f := r) (a := l)).mp hL
  rw [hL.tprod_eq, hr.tprod_eq]

end Formalism.L2.SG.Pf.NcS.BoxVolSk
end
end
