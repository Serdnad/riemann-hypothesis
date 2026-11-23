module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle100
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle092
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle098
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRowAnti

variable {D : D7}

theorem lam_step (τ : D.what₂.Tau) (n : ℕ) (hn : n + 1 < D.R.r) :
    Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1) + 1 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n := by
  have h := Formalism.L2.NTheta.lamAt_lt (D.hc τ) n hn
  obtain ⟨a, ha⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) (n + 1)
  obtain ⟨b, hb⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) n
  rw [ha, hb] at h ⊢
  have : a < b := by exact_mod_cast h
  have : a + 1 ≤ b := this
  exact_mod_cast this

theorem pq_eq (i : Fin D.R.m) (ρ : D.what₂.Tau) : pW D i ρ + qW D i ρ = D.R.r := by
  have h := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i ρ
  rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2] at h
  exact h

theorem aPl_anti (i : Fin D.R.m) (p : ℕ) (τ : D.what₂.Tau) (hp : p ≤ D.R.r) : Antitone (aPl D i p τ) := by
  refine antitone_nat_of_succ_le fun n => ?_
  unfold aPl
  by_cases h1 : n + 1 < p
  · rw [if_pos h1, if_pos (by omega : n < p)]
    apply Int.toNat_le_toNat
    apply Int.floor_le_floor
    have := lam_step τ n (by omega)
    push_cast
    linarith
  · rw [if_neg h1]; exact Nat.zero_le _

theorem aMi_anti (i : Fin D.R.m) (p q : ℕ) (τ : D.what₂.Tau) (hpq : p + q = D.R.r) : Antitone (aMi D i p q τ) := by
  refine antitone_nat_of_succ_le fun n => ?_
  unfold aMi
  by_cases h1 : n + 1 < q
  · rw [if_pos h1, if_pos (by omega : n < q)]
    apply Int.toNat_le_toNat
    apply Int.floor_le_floor
    have e1 : p + (q - n) - 1 = (p + (q - (n + 1)) - 1) + 1 := by omega
    have := lam_step τ (p + (q - (n + 1)) - 1) (by omega)
    rw [e1]
    have e2 : ((q - n : ℕ) : ℚ) = ((q - (n + 1) : ℕ) : ℚ) + 1 := by
      rw [show q - n = (q - (n + 1)) + 1 by omega]; push_cast; ring
    rw [e2]
    linarith
  · rw [if_neg h1]; exact Nat.zero_le _

end GlobalTheory.LowRowAnti

open GlobalTheory.LowRowAnti in
theorem GlobalTheory.LowRow.lift_rows_antitone : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau),
    Antitone (aPlAt D i σ ρ) ∧ Antitone (aMiAt D i σ ρ) ∧ pW D i ρ + qW D i ρ = (Wc D i).rank ∧
      (Wc D i).rank ≤ (Vc D i).rank := by
  intro D i σ ρ
  have hpq := pq_eq (D := D) i ρ
  refine ⟨?_, ?_, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i ρ, ?_⟩
  · exact aPl_anti i _ _ (by omega)
  · exact aMi_anti i _ _ _ hpq
  · rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]; exact r_le_V i
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem primeToHost_base : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → PrimeToHost R A.μ0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h PP hP
  rcases hP with hP | hP
  · exact GlobalTheory.LiftScalarCompare.primeToHost h.lev PP hP
  · rw [GlobalTheory.LiftLower.Q_base h.lev] at hP
    simp at hP

end GlobalTheory.LowRow
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow

theorem weightSizes_along : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x →
    ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨x0, fun x hx1 hx i j => ?_⟩
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, hw1, hsum⟩ := h0 x hx hx1 i
  have SZ := Fm.sizes x hx1 i
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := SZ
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hSc := L.Sc_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'.le (by linarith)
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have hwj : ∀ τ, wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    intro τ
    unfold wj
    rw [dite_eq_left (by omega)]
    rfl
  have hwin : ∀ τ, 0 < wj D (j.1 + 1) τ ∧ wj D (j.1 + 1) τ ≤ 2 * L.sc.b := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have := L.win_thick (j.1 + 1) (by omega) (by omega) τ h1
      constructor <;> linarith [this.1, this.2]
    by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have a := L.win_top (j.1 + 1) (by omega) (by omega) τ ⟨t, ht⟩ e.symm
      have a3 := L.bT_ge ⟨t, ht⟩
      have a4 := GlobalTheory.Ggeo.bT_le_five_quarters P ⟨t, ht⟩
      constructor <;> linarith [a.1, a.2]
    · have a := L.win_thin (j.1 + 1) (by omega) (by omega) τ ⟨(D.eTau τ).2, h2, h1⟩
      constructor <;> linarith [a.1, a.2]
  refine ⟨fun τ => ⟨?_, ?_, fun l => ?_, fun l => ?_⟩, fun l => (hG l l).1⟩
  · rw [← hwj]; exact (hwin τ).1
  · rw [← hwj]; exact (hwin τ).2
  · have := L.cloud_v τ l
    exact ⟨this.1, by linarith [this.2]⟩
  · have := L.be_close τ l j
    push_cast at this
    linarith

end GlobalTheory.LowRow
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Facts

theorem infPart_eq_one {D : D7} {v ε} (hε : IsPlaceIdem D v ε) {x : AE D}
    (hx : algebraMap (AF D.host.F) (AE D) ε * (x - 1) = x - 1) : infPart D x = 1 := by
  obtain ⟨α, rfl, -⟩ := hε
  have h3 := congrArg (infPart D) hx
  have h4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    have e2 : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
    have e3 := Algebra.TensorProduct.map_tmul (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α) 1
    rw [e2, TensorProduct.zero_tmul] at e3
    exact e3
  rw [map_mul, h4, zero_mul, map_sub, map_one] at h3
  exact (sub_eq_zero.1 h3.symm)

theorem sigW_add {D : D7} (i : Fin D.R.m) :
    (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
  have := D.R.m_add_three_le_k
  have hi := i.2
  rw [rank_Wc i]
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem signs_of_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) (ρ : D.what₂.Tau) (a : Fin (Wc D i).rank) :
    (R.MW i σ).ε ρ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D ρ)).1) := by
  have hs : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have he := (R.MW i σ).enum ρ
  unfold Links.parAt at he
  rw [if_pos (((labels_overK σ).1 hσ).2 ρ)] at he
  exact (GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs]; exact sigW_add i) he a).2

end GlobalTheory.GalOne.Facts
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.IoExtConj

open GlobalTheory.AdTh.IoExtPf
open scoped Classical

theorem deltaConj_ne {D : D7} (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : deltaConj (D := D) i σ ≠ 0 := by
  refine delta_ne _ _ _ _ (fun τ => ?_) ((rank_Wc i).le.trans (r_le_V i))
  show ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 ≤ _
  rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2, rank_Wc]
  have := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem exists_unit_of_isIoW {D : D7} {V W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S) (hs : LowSm M)
    (hl : ExtLine M) (c : CoefA V) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)) (Δ : PolF D W.rank V.rank) (hΔ : pt Δ ≠ 0)
    (hwt : ∀ (τ : D.what₂.Tau) (a : Fin W.rank → ℝ), ω (1, atTau θ W τ ((M.fr τ)⁻¹ *
      Matrix.diagonal (fun j => Complex.exp ((a j : ℂ) * Complex.I)) * M.fr τ)) (pt Δ) =
        Complex.exp (((∑ j, extWt M τ j * a j : ℝ) : ℂ) * Complex.I) • pt Δ)
    (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank) (h : IsIoW θ M c ω pt Δ io)
    (v' : ∀ ρ, lowT M ρ) (hv' : IsExtVec M (fun ρ => v' ρ)) :
    ∃ w : c.W, ‖w‖ = 1 ∧ io (PiTensorProduct.tprod ℂ v') w = Δ := by
  obtain ⟨-, hK, v, w, hv1, hw1, hio⟩ := h
  let f : LowT M →ₗ[ℂ] (WO V W → ℂ) := pt ∘ₗ io.flip w
  have hf : ∀ x, f x = pt (io x w) := fun x => rfl
  have hv0 : f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [hf, hio]
    exact hΔ
  have hv : IsExtVec M (fun ρ => v ρ) := by
    refine fun τ => ⟨hv1 τ, (v τ).2, fun a ha => ?_⟩
    have hm := GlobalTheory.LowKProj.lowKSub_stable _ _ _ _ ha _ (v τ).2
    let u : lowT M τ := ⟨⟨_, hs τ hm⟩, hm⟩
    have h1 := hK τ _ ha v u rfl w
    rw [hio, hwt τ a, ← hio, ← hf, ← hf] at h1
    have h2 := inj_factor M hs hl τ f (fun k => ω (1, atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)))
      (fun k hk v u hu => hK τ k hk v u hu w) v hv0
      (u - Complex.exp (((∑ j, extWt M τ j * a j : ℝ) : ℂ) * Complex.I) • v τ) (by
        rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, Function.update_eq_self, map_sub, map_smul, ← h1,
          RingHom.id_apply, sub_self])
    exact congrArg (fun y : lowT M τ => ((y : M.sm τ) : M.H τ)) (sub_eq_zero.1 h2)
  choose a ha1 ha using hl _ _ hv hv'
  have e : v' = fun ρ => a ρ • v ρ := funext fun ρ => Subtype.ext (ha ρ)
  have hn : ‖∏ ρ, a ρ‖ = 1 := by simp [norm_prod, ha1]
  have h0 : ∏ ρ, a ρ ≠ 0 := fun h => by simp [h] at hn
  refine ⟨(∏ ρ, a ρ)⁻¹ • w, by rw [norm_smul, norm_inv, hn, hw1]; simp, ?_⟩
  rw [e, MultilinearMap.map_smul_univ, map_smul, map_smul, LinearMap.smul_apply, smul_smul]
  simp only [RingHom.id_apply, inv_mul_cancel₀ h0, one_smul, hio]

end GlobalTheory.GalOne.IoExtConj
end

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.primeBelowComplexEmbeddingLabel_isMaximal_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ τ : E →+* ℂ, (primeBelow io X τ).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h := by
  first | exact @GlobalTheory.PrimePart.primeBelow_isMaximal_card | exact GlobalTheory.PrimePart.primeBelow_isMaximal_card | (intros; apply GlobalTheory.PrimePart.primeBelow_isMaximal_card <;> assumption)
end

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.isIntegralLogHom_diagonal_of_limit : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (G : LogFGL v d) (κ : Type) [Fintype κ] [DecidableEq κ] (U : Matrix (Fin d) κ C) (L : Matrix κ (Fin d) C), (∀ a b, IsIntV v (U a b)) → (∀ a b, IsIntV v (L a b)) → U * L = 1 → ∀ t : κ → C, (∀ r : ℝ, ∃ (t' : κ → C) (A : Matrix (Fin d) (Fin d) C) (φ : Fin d → MvPowerSeries (Fin d) C), IsIntHom G G φ A ∧ (∀ ℓ, A.mulVec (fun e => U e ℓ) = t' ℓ • fun e => U e ℓ) ∧ ∀ ℓ, (r : WithTop ℝ) ≤ v (t' ℓ - t ℓ)) → ∃ φ, IsIntHom G G φ (U * Matrix.diagonal t * L) := by
  first | exact @GlobalTheory.DiagLimit.isIntHom_diagonal_of_limit | exact GlobalTheory.DiagLimit.isIntHom_diagonal_of_limit | (intros; apply GlobalTheory.DiagLimit.isIntHom_diagonal_of_limit <;> assumption)
end

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.frobenius_acts_on_type_at_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), FrobOnType io X := by
  first | exact @GlobalTheory.PrimePart.frobOnType_all | exact GlobalTheory.PrimePart.frobOnType_all | (intros; apply GlobalTheory.PrimePart.frobOnType_all <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.HeckeBridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compInf_eq_infTens (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w z = Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) (infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem coe_infDiag (k : Eˣ) :
    (Formalism.L2.Host.infDiag k : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
  classical
  rw [Formalism.L2.Host.infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]
  let p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd _ _
  refine Prod.ext ?_ ?_
  · change p1 _ = _
    rw [map_prod]
    change ∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E)) = _
    exact Finset.univ_prod_mulSingle _
  · change p2 _ = _
    rw [map_prod]
    exact Finset.prod_eq_one fun _ _ => rfl

theorem exists_tensor_adele_equiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) :
    ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
      Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
      ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z)) := by
  obtain ⟨j, hjc, hjc', hj⟩ := GlobalTheory.HeckeTensorRead.exists_infinite_equiv F E σ hcm
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨s.trans (j.prodCongr (finAdEquiv F E)), j, (hjc.prodMap GlobalTheory.DefU.ClassFin.continuous_finAdEquiv).comp hsc, hsc'.comp (hjc'.prodMap continuous_finAdEquiv_symm), hj,
    fun z => Prod.ext (congrArg j (hs z).1) (congrArg (finAdEquiv F E) (hs z).2)⟩

theorem exists_hchar (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : IsCMExt F E σ → ∀ χ : Chr F E, IsHecke F E χ → ∃ H : Formalism.L2.Host.HChar E,
      (∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x) ∧
      ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : InfinitePlace F → ℤ), HasExp τ χ m →
        H.HasInf (fun w => (τ w).1) m := by
  intro hcm χ hχ
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := exists_tensor_adele_equiv F E σ hcm
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      refine Prod.ext (hj k).symm (hfin k).symm))
  have hloc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ),
      u (Neutral.B1.localIdele E W x) = locIdele F W x := fun W x =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, infTens_locIdele, map_one, finTens_locIdele]
      rfl))
  let H : Formalism.L2.Host.HChar E := ⟨Circle.toUnits.comp (χ.comp u), ht.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  refine ⟨H, fun W x => ?_, fun τ m hm k => ?_⟩
  · change Circle.toUnits (χ (u _)) = Circle.toUnits (χ (locIdele F W x))
    rw [hloc]
  · set z := u (Formalism.L2.Host.infDiag k) with hz
    have hz1 : Φ (z : AF F ⊗[F] E) = (Formalism.L2.Host.infDiag k : AdeleRing (𝓞 E) E) := Φ.apply_symm_apply _
    rw [coe_infDiag, hΦ] at hz1
    have hinf : infTens F E z = (1 : Ainf F) ⊗ₜ[F] (k : E) :=
      j.injective ((congrArg Prod.fst hz1).trans (hj k).symm)
    have hfin1 : finTens F E z = 1 :=
      (finAdEquiv F E).injective ((congrArg Prod.snd hz1).trans (map_one _).symm)
    have hAt : At (evI F) ((z : AF F ⊗[F] E) - 1) := by
      intro a ha
      have ha1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
      refine tens_ext ?_ ?_
      · rw [Algebra.smul_def, map_mul, map_zero]
        change (a.1 ⊗ₜ[F] (1 : E)) * _ = 0
        rw [ha1, TensorProduct.zero_tmul, zero_mul]
      · rw [Algebra.smul_def, map_mul, map_zero, map_sub, map_one, hfin1, sub_self, mul_zero]
    have hpi : ∀ w, piInf (τ w) z = (τ w).1 k := fun w => by
      change infEmb (τ w) (compInf F E w z) = _
      rw [compInf_eq_infTens, hinf, Algebra.TensorProduct.map_tmul, map_one, infEmb_tmul, map_one, one_mul]
      rfl
    change ((χ z : Circle) : ℂ) = _
    rw [hm z hAt]
    exact Finset.prod_congr rfl fun w _ => by rw [hpi w]

end GlobalTheory.HeckeBridge
end
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.capelliKilled_smoothFunction_centreOrbit_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (q : (E →+* ℂ) → ℂ → Polynomial ℂ), (∀ τ u, q τ u ≠ 0) → ∃ (X' : Set (Module.End ℂ (Sm E b) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E b) → ℂ) (u : Sm E b), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b) → u ≠ 0 → (∀ z ∈ Zalg E b, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E b, χ' z = χ z := by
  first | exact @GlobalTheory.KilledFinCentre.centre_orbit_finite | exact GlobalTheory.KilledFinCentre.centre_orbit_finite | (intros; apply GlobalTheory.KilledFinCentre.centre_orbit_finite <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.exists_complex_conjugate_cuspidal_representation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∃ (π' : CuspSub E a) (J : π.V ≃ₗ⋆[ℂ] π'.V), ∀ o φ, J (π.op o φ) = π'.op o (J φ) := by
  first | exact @GlobalTheory.exists_conj_cuspSub | exact GlobalTheory.exists_conj_cuspSub | (intros; apply GlobalTheory.exists_conj_cuspSub <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_global_oneForms_projective_rank : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FP R (GlobForm A.hom) g := by
  first | exact @GlobalTheory.AbCoh.globForm_FP | exact GlobalTheory.AbCoh.globForm_FP | (intros; apply GlobalTheory.AbCoh.globForm_FP <;> assumption)
end
