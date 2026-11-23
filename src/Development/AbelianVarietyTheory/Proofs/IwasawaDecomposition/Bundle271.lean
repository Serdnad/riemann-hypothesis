module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
public import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle190
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.StdUnique

theorem closed_eq_univ {D : D7} (V : HSp D) (C : Set (GA D V)) (hC : IsClosed C) (hQ : ∀ γ ∈ GQ V, γ ∈ C)
    (hf : ∀ h, ∀ k ∈ GfC V, h ∈ C → h * k ∈ C) (h : GA D V) : h ∈ C := by
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hfin : ∀ h : GA D V, (e h).2 = 1 → h ∈ GinfC V := fun h H =>
    MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))
  have hinf : ∀ h : GA D V, (e h).1 = 1 → h ∈ GfC V := fun h H =>
    MonoidHom.mem_ker.2 (Units.ext ((he h).2.symm.trans (by rw [H]; rfl)))
  have hu : e.symm ((e h).1, 1) ∈ C := by
    by_contra hn
    obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V _ (hfin _ (by rw [e.apply_symm_apply])) Cᶜ
      hC.isOpen_compl hn
    exact hU (hf γ k hk (hQ γ hγ))
  have hk : e.symm (1, (e h).2) ∈ GfC V := hinf _ (by rw [e.apply_symm_apply])
  have := hf _ _ hk hu
  rwa [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta, e.symm_apply_apply] at this

variable {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is)
include hc

theorem bot_or_top (U : Submodule ℂ c.W) (hU : ∀ γ ∈ GQ V, ∀ w ∈ U, c.ρ γ w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  refine hc.2.2.2.2 U fun h => ?_
  rintro _ ⟨w, hw, rfl⟩
  refine closed_eq_univ V {h | c.ρ h w ∈ U} (U.closed_of_finiteDimensional.preimage (hc.2.2.1 w))
    (fun γ hγ => hU γ hγ w hw) (fun h k hk H => ?_) h
  show c.ρ (h * k) w ∈ U
  rw [map_mul, hc.1 k hk, mul_one]
  exact H


omit hc in
theorem exists_ratMat (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨γ, ⟨g, -, hg⟩⟩ := γ
  exact ⟨g, hg.symm⟩

omit hc

end GlobalTheory.Mem.StdUnique

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

section Cut

variable {G Γ : Type} [Group G] [Group Γ] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def cutSp (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (Q : Subgroup G) (ch : Q →* ℂˣ)
    {G₀ : Type} [Group G₀] (red : Q →* G₀) (P : Subgroup G₀) (ψ : P →* ℂˣ) : Submodule ℂ (G → W) :=
  Bridge.AdForms ι ρ J χ ⊓
    { carrier := {F | ∀ (κ : Q) (hκ : red κ ∈ P) (h : G), F (h * κ) = ((ch κ * ψ ⟨red κ, hκ⟩ : ℂˣ) : ℂ) • F h}
      add_mem' := fun {F F'} hF hF' κ hκ h => by simp only [Pi.add_apply, hF κ hκ h, hF' κ hκ h, smul_add]
      zero_mem' := fun κ hκ h => by simp
      smul_mem' := fun c F hF κ hκ h => by simp only [Pi.smul_apply, hF κ hκ h]; rw [smul_comm] }

def lvlForm {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G₀ : Type} [Group G₀] [Fintype G₀]
    (r : Representation K G₀ S.Forms) (P : Subgroup G₀) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) : S.Forms :=
  S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x)

end Cut

variable {D : D7}


variable (D) in
def km (n : ℕ) : Formalism.AUTREP.GAf D.host.E n →* GL (Fin n) (EAf D) := (ReciprocityTheory.Aut.GA D.host.E n).subtype

def stdJ {n : ℕ} (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n) : Subgroup (Formalism.AUTREP.GAf D.host.E n) :=
  (Formalism.L2.DIV.lev D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld).comap (km D n)

def stdX {n : ℕ} (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n) : stdJ Ld →* ℂˣ :=
  (Formalism.L2.DIV.levChar D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld).comp ((km D n).subgroupComap _)


variable (D) in
def datV (n : ℕ) (hr : D.R.r ≤ n) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ)
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ n :=
  datY n D.R.r D.R.t 1 hr Pg Q P (fun _ => chi) xi Frm.A

def UnitFr {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) : Prop := ∀ κ, finE V (P.ψ κ) = km D V.rank κ

def toGf {V : HSp D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) : Formalism.AUTREP.GAf D.host.E n →* Bridge.Gf V :=
  (finHom V).rangeRestrict.comp P.ψ

def RatIso {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V) : Prop :=
  ∀ γ : ReciprocityTheory.Aut.GQ D.host.E V.rank, Bridge.ratF V (e γ) = toGf P γ.1 ∧
    ∀ γ₀ : GL (Fin V.rank) D.host.E,
      (γ.1.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) =
        (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom →
      Bridge.IsRatMat V (e γ) γ₀

def wtRep {V : HSp D} {n : ℕ} (c : CoefA V) (e : ReciprocityTheory.Aut.GQ D.host.E n ≃* Formalism.L2.Theta.GQ V) :
    Representation ℂ (ReciprocityTheory.Aut.GQ D.host.E n) c.W :=
  c.coef.ρ.comp e.toMonoidHom

end GlobalTheory.MtIn

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.selfDual_vector_pairs_integral_frame_columns : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ v : Fin W.rank → D.host.E, finVec W v ∈ gLat W 1 → ∀ a : Fin W.rank, ∑ k, eToEAf D (∑ l, D.sp.cm.sig (v l) * W.gram l k) * β.val k a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.PairIntegral.pair_mem_intAf | exact GlobalTheory.PairIntegral.pair_mem_intAf | (intros; apply GlobalTheory.PairIntegral.pair_mem_intAf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.TopBridge

variable {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

theorem rangeRestrict_mem_Q_iff (κ : GA D V) :
    (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q ↔ Lev.finE V κ ∈ parLev D.sp.cm V.gram β L := by
  have e1 : Lev.finE V κ = Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 := Lev.finE_eq V κ
  constructor
  · intro h
    have h1 : Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 ∈ lev D.sp.cm V.gram β (Lev.flagL L) := h
    rw [e1]
    exact h1.1
  · intro h
    have h1 : Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 ∈ lev D.sp.cm V.gram β (Lev.flagL L) := by
      rw [mem_lev]
      exact ⟨e1 ▸ h, Subgroup.mem_top _⟩
    exact h1

theorem mem_levelSubgroup_withP_iff (P : LevelP L.Pg L.r ℂ) {κ : GA D V} (hκ : κ ∈ GfC V) :
    κ ∈ levS V β (Lev.withP L P) ↔ Lev.finE V κ ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (Lev.finE V κ) ∈ P.H :=
  ⟨fun h => h.2, fun h => ⟨hκ, h⟩⟩

theorem levelCharacter_withLevel_of_mem {P : LevelP L.Pg L.r ℂ} {κ : GA D V} (hp : rTup β L (Lev.finE V κ) ∈ P.H) :
    Lev.levChi V β (Lev.withP L P) κ = ((P.chi ⟨_, hp⟩ : ℂˣ) : ℂ) * Lev.levChi V β (Lev.flagL L) κ := by
  unfold Lev.levChi
  rw [Lev.levFn_withP, extendOne_of_mem _ hp, Units.val_mul]

theorem levChi_flagL_eq_ch {κ : GA D V} (hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q) :
    Lev.levChi V β (Lev.flagL L) κ = (((levEnv V β L).ch ⟨_, hq⟩ : ℂˣ) : ℂ) := by
  have e2 : (levEnv V β L).ch ⟨_, hq⟩ = levFn β (Lev.flagL L) (Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1) := rfl
  unfold Lev.levChi
  rw [e2, Lev.finE_eq]
  rfl

end GlobalTheory.TopBridge


open GlobalTheory.TopBridge in
theorem GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_red_R → ∀ (b : Bool) (t : T) (κ : GA D D.sp.X'), κ ∈ GfC D.sp.X' → ((κ ∈ levS _ R.βX (datXP R t (R.levR F b)) ↔ ∃ hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q, (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P) ∧ ∀ (hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hp : (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P), levChi _ R.βX (datXP R t (R.levR F b)) κ = ((levEnv D.sp.X' R.βX (R.datXt t)).ch ⟨_, hq⟩ : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hp⟩ : D.what₂.LLˣ) : D.what₂.LL)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hr b t κ hκ
  have hQ : ∀ hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q,
      (R.B.R t).act_tie.red ⟨_, hq⟩ = R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)) := fun hq =>
    R.eG.eq_symm_apply.2 ((hr t ⟨_, hq⟩).trans (congrArg (rTup R.βX (R.datXt t)) (Lev.finE_eq D.sp.X' κ).symm))
  have hH : ∀ x, x ∈ (R.levR F b).H ↔ R.eG.symm x ∈ (F.lvl b).P := fun x => Iff.rfl
  have hS := mem_levelSubgroup_withP_iff D.sp.X' R.βX (R.datXt t) (R.levR F b) hκ
  refine ⟨hS.trans ?_, ?_⟩
  · constructor
    · rintro ⟨h1, h2⟩
      have hq := (rangeRestrict_mem_Q_iff D.sp.X' R.βX (R.datXt t) κ).2 h1
      exact ⟨hq, (hQ hq).symm ▸ (hH _).1 h2⟩
    · rintro ⟨hq, hp⟩
      exact ⟨(rangeRestrict_mem_Q_iff D.sp.X' R.βX (R.datXt t) κ).1 hq, (hH _).2 (hQ hq ▸ hp)⟩
  · intro hq hp
    have hP : rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ) ∈ (R.levR F b).H := (hH _).2 (hQ hq ▸ hp)
    refine (levelCharacter_withLevel_of_mem D.sp.X' R.βX (R.datXt t) hP).trans ?_
    refine (mul_comm _ _).trans (congrArg₂ (· * ·) (levChi_flagL_eq_ch _ _ _ hq) ?_)
    have e : (⟨_, hp⟩ : (F.lvl b).P) = ⟨R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)), (hH _).1 hP⟩ :=
      Subtype.ext (hQ hq)
    have key : (((R.levR F b).chi ⟨_, hP⟩ : ℂˣ) : ℂ) =
        D.what₂.embLL (((F.lvl b).ψ ⟨R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)), (hH _).1 hP⟩ : D.what₂.LLˣ) : D.what₂.LL) :=
      rfl
    exact key.trans (congrArg (fun p => D.what₂.embLL (((F.lvl b).ψ p : D.what₂.LLˣ) : D.what₂.LL)) e.symm)
end
end

section

namespace MultiplicativeInnerProducts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace CompanionTheory.Member.InnerProductScaling

theorem isMultiplicityInner_smul_measure {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T T' : MMap M) (c : ℝ) (hc : 0 ≤ c) (a : ℂ) (h : IsMultIP M μ 𝓕 T T' a) :
    IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' ((c : ℂ) * a) := by
  intro v v'
  obtain ⟨h1, h2⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at h1 ⊢
    rw [Measure.restrict_smul]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, h2, ENNReal.toReal_ofReal hc, Complex.real_smul, mul_assoc]

theorem ipM_smul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T T' : MMap M) (c : ℝ) (hc : 0 ≤ c) (a : ℂ) (h : IsMultIP M μ 𝓕 T T' a) :
    ipM M (ENNReal.ofReal c • μ) 𝓕 T T' = (c : ℂ) * a := by
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  have h' := isMultiplicityInner_smul_measure M μ 𝓕 T T' c hc a h
  exact hasPeterssonInner_unique M _ 𝓕 T T' v hv (ipM_spec M _ 𝓕 T T' ⟨_, h'⟩) h'

theorem main {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (H : HMod (MMap M)) (W W0 : Submodule ℂ (MMap M)) (hW : W ≤ W0)
    (hH : H.Is W0 (ipM M μ 𝓕)) (n : ℝ) (hn : 0 < n)
    {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    (j : EE ≃ₗ[ℂ] (W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap))
    (hj : HilbTie (W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap)
      (ipMT M (ENNReal.ofReal n⁻¹ • μ) 𝓕) j) :
    ∃ eE : EE →ₗ[ℂ] H.H, LinearMap.range eE = W.comap H.e ∧ (∀ x, ‖eE x‖ ^ 2 = n * ‖x‖ ^ 2) ∧
      ∀ x, ((j x : W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap) : AmbT M) =
        PiTensorProduct.lift (H.e (eE x)) := by
  let L : MMap M ≃ₗ[ℂ] AmbT M := PiTensorProduct.lift
  let f : EE →ₗ[ℂ] MMap M := L.symm.toLinearMap ∘ₗ (W.map L.toLinearMap).subtype ∘ₗ j.toLinearMap
  have hf : ∀ x, f x = L.symm (j x : AmbT M) := fun _ => rfl
  have hfW : ∀ x, f x ∈ W := fun x => by
    obtain ⟨y, hy, e⟩ := (j x).2
    have e' : L y = (j x : AmbT M) := e
    rw [hf, ← e', L.symm_apply_apply]
    exact hy
  obtain ⟨g, hg⟩ := GlobalTheory.Mem.Th.exists_factor H.e hH.1 f fun x => by
    rw [hH.2.1]; exact hW (hfW x)
  refine ⟨g, ?_, fun x => ?_, fun x => ?_⟩
  · ext u
    constructor
    · rintro ⟨x, rfl⟩
      show H.e (g x) ∈ W
      rw [hg]; exact hfW x
    · intro hu
      refine ⟨j.symm ⟨L (H.e u), Submodule.mem_map_of_mem hu⟩, hH.1 ?_⟩
      rw [hg, hf, j.apply_symm_apply]
      exact L.symm_apply_apply _
  · have h1 : IsMultIP M μ 𝓕 (H.e (g x)) (H.e (g x)) (1 * ⟪g x, g x⟫_ℂ) :=
      GlobalTheory.Mem.Th.isMultiplicityInner_mul_inner H.e one_ne_zero (fun a b => by rw [one_mul]; exact (hH.2.2 a b).symm) _ _
    have h2 := ipM_smul M μ 𝓕 _ _ n⁻¹ (inv_pos.2 hn).le _ h1
    have h3 : ⟪x, x⟫_ℂ = ipM M (ENNReal.ofReal n⁻¹ • μ) 𝓕 (f x) (f x) := hj x x
    rw [← hg, h2, one_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    have h4 : ‖x‖ ^ 2 = n⁻¹ * ‖g x‖ ^ 2 := by
      have h5 : ((‖x‖ ^ 2 : ℝ) : ℂ) = ((n⁻¹ * ‖g x‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
        exact h3
      exact Complex.ofReal_injective h5
    rw [h4, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  · rw [hg, hf]
    exact (L.apply_symm_apply _).symm

end CompanionTheory.Member.InnerProductScaling

theorem CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (b : Bool) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (I : RowIds X (toChainReal R F tupT hm hTop) b), R.models_HE → HilbTie ((toChainReal R F tupT hm hTop).EEc b) ((toChainReal R F tupT hm hTop).ipE b) I.jE → ∃ eE : EE →ₗ[ℂ] R.HE.H, LinearMap.range eE = (R.EEat (R.levR F b)).comap R.HE.e ∧ (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) ∧ ∀ x, ((I.jE x : (toChainReal R F tupT hm hTop).EEc b) : (toChainReal R F tupT hm hTop).Amb 0) = PiTensorProduct.lift (R.HE.e (eE x)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop b EE _ _ _ X I hE hj
  exact CompanionTheory.Member.InnerProductScaling.main (R.MY 0) R.ν0 R.fd0 R.HE (R.EEat (R.levR F b)) (R.EEat R.triv)
    (GlobalTheory.Mem.Th.EEat_le_triv R _) hE (RealDat.nP F b) (RealDat.nP_pos b) I.jE hj

end

end MultiplicativeInnerProducts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
theorem _root_.GlobalTheory.Adopt.levelRowsReading_embedding_goodRowsModel_with_norm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (b : Bool) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (I : RowIds X (toChainReal R F tupT hm hTop) b), R.models_HE → HilbTie ((toChainReal R F tupT hm hTop).EEc b) ((toChainReal R F tupT hm hTop).ipE b) I.jE → ∃ eE : EE →ₗ[ℂ] R.HE.H, LinearMap.range eE = (R.EEat (R.levR F b)).comap R.HE.e ∧ (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) ∧ ∀ x, ((I.jE x : (toChainReal R F tupT hm hTop).EEc b) : (toChainReal R F tupT hm hTop).Amb 0) = PiTensorProduct.lift (R.HE.e (eE x)) := by
  first | exact @MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows | exact MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows | (intros; apply MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows <;> assumption)

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LiftSpan

theorem end_smul_smul {W : Type} [AddCommGroup W] [Module ℂ W] (L : Module.End ℂ W) (a b : ℂ) (x : W) :
    L (a • b • x) = (a * b) • L x := by
  rw [map_smul, map_smul, smul_smul]



theorem ext_mem_levSubV_of_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h) → (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hcV hred i t Φ hΦ
  intro k hk g
  have hkG : k ∈ GfC (Vc D i) := hk.1
  have hpar : finE (Vc D i) k ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hk.2.1
  have hH : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).H := hk.2.2
  have hq : (finHom (Vc D i)).rangeRestrict k ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    show Formalism.UG.bc (swapAE D) (finHom (Vc D i) k) ∈
      Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))
    rw [← finE_eq]
    exact ⟨hpar, Subgroup.mem_top _⟩
  set κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := ⟨_, hq⟩ with hκdef
  have hred' : R.eG ((R.B.L i t).act_tie.red κ) = Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) :=
    hred i t κ
  have hu : (R.B.L i t).act_tie.red κ ∈ F.P0 := by
    have h2 : R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)) ∈ F.P0 := hH
    rw [← hred', MulEquiv.symm_apply_apply] at h2
    exact h2
  have hlaw := hΦ κ hu ((finHom (Vc D i)).rangeRestrict g)
  have hchi : levChi _ (R.βV i) (datVP R i t (R.levR F false)) k =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) •
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    have hH' : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).conj.H := hH
    have hP : (⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hH⟩ : F.P0) =
        ⟨(R.B.L i t).act_tie.red κ, hu⟩ := Subtype.ext (by
          show R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)) = (R.B.L i t).act_tie.red κ
          rw [← hred', MulEquiv.symm_apply_apply])
    have hw := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.levR F false).conj (finE (Vc D i) k)
    have he := Formalism.L2.DIV.extendOne_of_mem (R.levR F false).conj.chi hH'
    have hw2 : Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) =
        (R.levR F false).conj.chi ⟨_, hH'⟩ * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k) :=
      hw.trans (congrArg (fun u => u * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k)) he)
    show ((Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) : ℂˣ) : ℂ) = _
    rw [hw2, Units.val_mul, mul_comm, smul_eq_mul]
    congr 1
    · show (((Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨R.eG.symm _, hH⟩))⁻¹ : ℂˣ) : ℂ) = _
      rw [hP]
      rfl
  have e1 := Formalism.IndefR.Eqv.Act.coefExt_mul (R.cV i) (hcV i) Φ g k hkG
  have e3 : (R.cV i).ext Φ g = (R.cV i).ρ g⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict g)) := rfl
  rewrite [e1, hchi, hlaw, e3, smul_eq_mul]
  exact @end_smul_smul _ _ _ _ _ _ _

end GlobalTheory.LiftSpan
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowAct

section Gen

variable {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

theorem parLev_of_Q (q : (levEnv V β L).Q) :
    Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _) ∈ parLev D.sp.cm V.gram β L := q.2.1

def rTupQ : (levEnv V β L).Q →* G0 L.Pg L.r where
  toFun q := rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    exact rTup_one
  map_mul' x y := by
    simp only [Subgroup.coe_mul, map_mul]
    exact rTup_mul (parLev_of_Q V β L x) (parLev_of_Q V β L y)

theorem rTupQ_eq_one_iff (q : (levEnv V β L).Q) :
    rTupQ V β L q = 1 ↔ ((q : Bridge.Gf V)) ∈ (levEnv V β L).J := by
  constructor
  · intro h
    exact ⟨parLev_of_Q V β L q, Subgroup.mem_bot.2 h⟩
  · intro h
    exact Subgroup.mem_bot.1 h.2

end Gen

end GlobalTheory.Mem.R3.RowAct
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_selfDual_adelic_frame_level_one : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (Λ : Set (Fin V.rank → D.host.E)) = L0c D V → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∃ β, IsSDFrame V β Λ 1 := by
  first | exact @GlobalTheory.AdelicFrame.exists_isSDFrame | exact GlobalTheory.AdelicFrame.exists_isSDFrame | (intros; apply GlobalTheory.AdelicFrame.exists_isSDFrame <;> assumption)
end
