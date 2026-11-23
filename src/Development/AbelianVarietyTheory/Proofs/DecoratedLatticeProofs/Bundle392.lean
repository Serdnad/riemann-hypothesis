module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecSingleAt
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.Bundle008
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

theorem GlobalTheory.MiTop.levFn_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    {LL : Type} [CommRing LL] (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : Formalism.L2.DIV.LevDat E LL n) {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ Formalism.L2.DIV.lev hc J β L) (hy : y ∈ Formalism.L2.DIV.lev hc J β L) :
    Formalism.L2.DIV.levFn β L (x * y * x⁻¹) = Formalism.L2.DIV.levFn β L y := by
  have e := congrArg (Formalism.L2.DIV.levChar hc J β L)
    (show (⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : Formalism.L2.DIV.lev hc J β L)⁻¹ : Formalism.L2.DIV.lev hc J β L) =
      ⟨x * y * x⁻¹, _⟩ from rfl)
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at e
  exact e.symm

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiTop
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineSelfDual

theorem hT_frame (D : D7) (S : HSp D) (u v : S.V) :
    S.hT u v = ∑ i, ∑ j, star (S.frame.equivFun u i) * S.gram i j * S.frame.equivFun v j := by
  conv_lhs => rw [← S.frame.sum_repr u, ← S.frame.sum_repr v]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  Module.Basis.equivFun_apply, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

noncomputable def selfDualLatticeCoordsInHermitianFrame (D : D7) (S : HSp D) : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
  S.L0.map (S.frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap

theorem frameCoords_mem_selfDualLatticeCoords_iff (D : D7) (S : HSp D) (u : S.V) : S.frame.equivFun u ∈ selfDualLatticeCoordsInHermitianFrame D S ↔ u ∈ S.L0 :=
  ⟨fun ⟨z, hz, e⟩ => S.frame.equivFun.injective e ▸ hz, fun hu => ⟨u, hu, rfl⟩⟩

theorem isSelfDualC_selfDualLatticeCoordsInFrame (D : D7) (S : HSp D) : IsSelfDualC S (selfDualLatticeCoordsInHermitianFrame D S) := by
  refine ⟨⟨S.standardTuple_isLattice.fg.map _, ?_⟩, ?_⟩
  · exact fun _ _ => (LinearIndependent.iff_fractionRing (𝓞 D.host.E) D.host.E).mp
  · intro y
    obtain ⟨v, rfl⟩ := S.frame.equivFun.surjective y
    have h2 : v ∈ S.L0 ↔ ∀ u ∈ S.L0, S.hT u v ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual S.hT S.L0 = S.L0 from S.baseLattice_isUnimodular]
      simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
    have h3 : ∀ z : D.host.E, z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ ∃ b : 𝓞 D.host.E, (b : D.host.E) = z :=
      fun z => Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
    rw [frameCoords_mem_selfDualLatticeCoords_iff, h2]
    constructor
    · rintro H _ ⟨u, hu, rfl⟩
      have := (h3 _).1 (H u hu)
      rwa [hT_frame] at this
    · intro H u hu
      rw [h3, hT_frame]
      exact H _ ⟨u, hu, rfl⟩

end GlobalTheory.LineSelfDual
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BaseChain.thetaKO_sum_smul_act {D : D7} {S T : HSp D} {ι : Type} (s : Finset ι) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S) (h : GA D T) (c : ι → ℂ) (κ : ι → GA D S) (f : WO S T → ℂ) :
    thetaKO om g h (∑ p ∈ s, c p • om (κ p, 1) f) = ∑ p ∈ s, c p * thetaKO om (g * κ p) h f := by

  simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]


end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LiftVol

theorem thetaKO_sum_translates {D : D7} {S T : HSp D} {ι : Type} (s : Finset ι) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S) (h : GA D T) (c : ι → ℂ) (κ : ι → GA D S) (f : WO S T → ℂ) :
    thetaKO om g h (∑ p ∈ s, c p • om (κ p, 1) f) = ∑ p ∈ s, c p * thetaKO om (g * κ p) h f := by

  simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]



end GlobalTheory.Fam.LiftVol
end

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem GlobalTheory.MiTop.levChi_mul_lev {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ Lev.levG V β L) (hk' : k' ∈ Lev.levG V β L) :
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  unfold Lev.levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg _ ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

theorem GlobalTheory.MiTop.conj_in_level {G : Type} [Group G] (J : Subgroup G) (χ : G → ℂ)
    (hm : ∀ a ∈ J, ∀ b ∈ J, χ (a * b) = χ a * χ b) (h0 : ∀ a, χ a ≠ 0) {k : G} (hk : k ∈ J) (j : G) :
    (j ∈ J ↔ k * j * k⁻¹ ∈ J) ∧ (j ∈ J → χ (k * j * k⁻¹) = χ j) := by
  refine ⟨⟨fun hj => J.mul_mem (J.mul_mem hk hj) (J.inv_mem hk), fun hj => ?_⟩, fun hj => ?_⟩
  · have := J.mul_mem (J.mul_mem (J.inv_mem hk) hj) hk
    rwa [show k⁻¹ * (k * j * k⁻¹) * k = j by group] at this
  · have e := hm _ (J.mul_mem (J.mul_mem hk hj) (J.inv_mem hk)) _ hk
    rw [show k * j * k⁻¹ * k = k * j by group, hm _ hk _ hj, mul_comm (χ k)] at e
    exact (mul_right_cancel₀ (h0 k) e).symm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

theorem levFn_datY_noQ {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {r : ℕ} (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ)
    (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm) (x : GL (Fin V.rank) (Lev.EAf D)) :
    levFn β (Lev.datY V.rank r t j hr Pg Q P χ ξ fr) x = levFn β (Lev.datY V.rank r t j hr Pg ∅ P χ ξ' fr) x := by
  unfold levFn
  have hq : ∀ PP ∈ (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).Q,
      (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).xq PP
        (dBlk (blk2 (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).r) 1 (redFn β PP x)) = 1 := by
    intro PP _
    show _ = 1
    rw [show (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).r = r from rfl, Formalism.IndefR.Eqv.Act.block_determinant_empty_eq_one hn, map_one]
  rw [Finset.prod_eq_one hq]
  rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.BaseChain

end
end
