module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyCV
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPfLocSec
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle020
public import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle001
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.Carrier.EnergyNF

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
  Formalism.L2.SG.Pf.Carrier.EnergyPlace Formalism.L2.SG.Pf.Carrier.EnergyFinal Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lintegral_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)] (F : ι → E → ℝ≥0∞) (hF : ∀ i, Measurable (F i)) :
    ∫⁻ x, ∏ i, F i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, F i y ∂(μ i) := by
  have hm : Measurable (fun x : ι → E => ∏ i, F i (x i)) :=
    Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i)
  have key : ∀ s : Finset ι, ∀ x : ι → E,
      (∫⋯∫⁻_s, (fun x : ι → E => ∏ i, F i (x i)) ∂μ) x = (∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * ∏ i ∈ sᶜ, F i (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | insert i s hi ih =>
      intro x
      rw [lmarginal_insert _ hm hi]
      simp_rw [ih]
      have hsplit : ∀ y, ∏ j ∈ sᶜ, F j (Function.update x i y j) = F i y * ∏ j ∈ (insert i s)ᶜ, F j (x j) := by
        intro y
        have hic : i ∈ sᶜ := Finset.mem_compl.2 hi
        rw [← Finset.mul_prod_erase _ _ hic, Function.update_self, Finset.compl_insert]
        congr 1
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      simp_rw [hsplit]
      have h2 : ∀ y, (∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * (F i y * ∏ j ∈ (insert i s)ᶜ, F j (x j)) =
          ((∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * ∏ j ∈ (insert i s)ᶜ, F j (x j)) * F i y := fun y => by ring
      simp_rw [h2]
      rw [lintegral_const_mul _ (hF i), Finset.prod_insert hi]
      ring
  rw [lintegral_eq_lmarginal_univ (fun _ => Classical.arbitrary E), key, Finset.compl_univ, Finset.prod_empty,
    mul_one]

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

theorem intCe_eq_prodE (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (hL : LocRep X u u' L) :
    intCe X u u' 1 = ∏ v, ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) := by
  obtain ⟨hpos, hLc⟩ := hL
  have hG : MeasurableSet (Good X u u') := by
    rw [good_eq_pi]; exact MeasurableSet.univ_pi fun _ => goodV_meas u u'
  have hpt : ∀ c ∈ Good X u u', ENNReal.ofReal (Formalism.L2.SG.RealObj.wt X u u' c * hilbertSchmidtSqGram X u u' 1 c) =
      ∏ v, ENNReal.ofReal (wtV u u' (c v) * L v (c v)) := by
    intro c hc
    have hcv : ∀ v, c v ∈ GoodV u u' := fun v => hc v
    rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ =>
      mul_nonneg (wtV_nonneg u u' (hcv v)) ((hpos v).2 _))]
    congr 1
    have hO : hilbertSchmidtSqGram X u u' 1 c = ∏ v, L v (c v) := by
      unfold hilbertSchmidtSqGram
      rw [hilbert_schmidt_tensor_product_factor]
      exact Finset.prod_congr rfl fun v _ => hLc c hc v
    rw [hO, Finset.prod_mul_distrib]
    rfl
  unfold intCe
  rw [setLIntegral_congr_fun hG hpt, good_eq_pi]
  have h2s : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
    have h : ((2 : ℝ≥0∞) • (volume : Measure ℂ)) = ((2 : NNReal) • (volume : Measure ℂ)) := by
      rw [ENNReal.smul_def]; simp
    rw [h]; infer_instance
  unfold dcInf
  rw [Measure.restrict_pi_pi]
  have hdc : SigmaFinite ((dcV (D := D)).restrict (GoodV u u')) := by unfold dcV; infer_instance
  rw [show (Measure.pi fun _ : Fin (D.R.rS + 1) => (2 : ℝ≥0∞) • (volume : Measure ℂ)) = dcV (D := D) from rfl]
  exact lintegral_pi_prod _ (fun v cv => ENNReal.ofReal (wtV u u' cv * L v cv))
    (fun v => ENNReal.measurable_ofReal.comp ((wtV_cont u u').measurable.mul (hpos v).1))

def PlaceEnergyE (P : Parts X u u') (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  ∀ v, ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) =
    ENNReal.ofReal (K v) * Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))

theorem energyNorm_of_stepsE (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (K : InfinitePlace X.B.I.F → ℝ)
    (h1 : LocRep X u u' L) (h2 : PlaceEnergyE P L K) (h3 : ConstPin P ψ K) :
    P.EnergyNorm (IntNX X u u' ψ) := by
  set n : InfinitePlace X.B.I.F → ℝ :=
    fun v => (Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))).toReal with hn
  have hC : IntC X u u' 1 = (∏ v, K v) * ∏ v, n v := by
    unfold IntC
    rw [intCe_eq_prodE L h1]
    rw [Finset.prod_congr rfl (fun v _ => h2 v)]
    rw [ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h3.1 v)]
  unfold Parts.EnergyNorm IntNX
  rw [hC]
  have hre : (∏ j, (Formalism.FourierDecayAlt.B.normSq (P.T j).base (P.f j)).toReal / P.Gam0) =
      (∏ v, n v) * (P.Gam0 ^ P.S.f)⁻¹ := by
    rw [← Equiv.prod_comp P.τ.symm, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      ← Fintype.card_congr P.τ, Fintype.card_fin, div_eq_mul_inv]
  rw [hre, ← h3.2]
  ring

theorem placeEnergyE_of_steps (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (hPN : PlaceNorm P hr L) (hCV : ChangeVar P hr) :
    PlaceEnergyE P L (fun _ => EnergyConst.Kexp P) := by
  intro v
  rw [setLIntegral_congr_fun (goodV_meas u u') (fun cv hcv => by rw [hPN v cv hcv])]
  rw [hCV hk hT v (fun q => ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
      (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base q))‖ ^ 2) (fun q => by positivity)]
  rw [← Formalism.L2.SG.Pf.Carrier.EnergyKM.kMatch_holds P hg hrd hr hk hg0 hk1]
  rfl

theorem energyNorm_bookY_of_placeNormG_of_changeVar (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst.LemmaMS X u u' ψ)
    (hPN : PlaceNormG P hr) (hCV : ChangeVar P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN := by
  obtain ⟨L, hL⟩ := Formalism.L2.SG.Pf.Carrier.EnergyPfLoc.locRep_holds X u u'
  rw [intN_massDataY]
  exact energyNorm_of_stepsE P ψ L (fun _ => EnergyConst.Kexp P) hL
    (placeEnergyE_of_steps P hr hk hT hg hrd hg0 hk1 L (placeNorm_of_G P hr hPN L hL) hCV)
    (EnergyConst.constPin_of P ψ hC hMS hf)

theorem energy_norm_bound_second_form (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst.LemmaMS X u u' ψ)
    (hPN : PlaceNormG P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN :=
  energyNorm_bookY_of_placeNormG_of_changeVar hb Y X0 ψ sd C Th vR Q i0 i0' νq P hr hk hT hg hrd hg0 hk1 hf hC hMS hPN
    (Formalism.L2.SG.Pf.Carrier.EnergyCV.changeVar_of_pos P hr hg0)

theorem energy_norm_bound_third_form (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hstd : Formalism.L2.SG.LocVol.IsStdChar ψ)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst2.LemmaMSStd X u u' ψ)
    (hPN : PlaceNormG P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN :=
  energy_norm_bound_second_form hb Y X0 ψ sd C Th vR Q i0 i0' νq P hr hk hT hg hrd hg0 hk1 hf hC (hMS hψ hstd hC) hPN

end Formalism.L2.SG.Pf.Carrier.EnergyNF
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain Function

namespace Formalism.L2.SG.Pf.Carrier.EnergyMS

open Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StepGSplit : Prop := ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), GSplitX X

def TypCount : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (i : Fin 2),
    (Finset.univ.filter (fun p : TypX X => gAt X p.1 = D.host.g i)).card = D.R.f

theorem typNorm_of (hG : StepGSplit) (hC : TypCount) : TypNorm := by
  intro D X
  have hgA : ∀ p : TypX X, ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ) = ((gAt X p.1 : ℕ) : ℝ) := fun p => by
    rw [(hG D X p).1]
  simp only [hgA]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun p : TypX X => gAt X p.1 = D.host.g 0)]
  have h0 : ∀ p ∈ Finset.univ.filter (fun p : TypX X => gAt X p.1 = D.host.g 0),
      ((gAt X p.1 : ℕ) : ℝ) = ((D.host.g 0 : ℕ) : ℝ) := fun p hp => by
    rw [(Finset.mem_filter.1 hp).2]
  have h1 : ∀ p ∈ Finset.univ.filter (fun p : TypX X => ¬ gAt X p.1 = D.host.g 0),
      ((gAt X p.1 : ℕ) : ℝ) = ((D.host.g 1 : ℕ) : ℝ) := fun p hp => by
    have h := (Finset.mem_filter.1 hp).2
    unfold gAt at h ⊢
    split_ifs at h ⊢ with hg
    · exact absurd rfl h
    · rfl
  rw [Finset.prod_congr rfl h0, Finset.prod_congr rfl h1, Finset.prod_const, Finset.prod_const]
  have hc1 : Finset.univ.filter (fun p : TypX X => ¬ gAt X p.1 = D.host.g 0) =
      Finset.univ.filter (fun p : TypX X => gAt X p.1 = D.host.g 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold gAt
    have hne := D.host.g_ne
    split_ifs <;> simp [hne, Ne.symm hne]
  rw [hc1, hC D X 0, hC D X 1, Formalism.MainNotions.S.Lat.gS, Nat.cast_mul, mul_pow]

theorem dN_eq {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : PlX X) :
    dN X v = ((Nat.castRingHom ℝ : ℕ →* ℝ).comp (Ideal.absNorm : Ideal (𝓞 X.B.I.F) →*₀ ℕ).toMonoidHom)
      (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) := rfl

theorem diffProd_holds : DiffProd := by
  intro D X
  have hne : differentIdeal ℤ (𝓞 X.B.I.F) ≠ ⊥ := by
    intro h
    have h2 := NumberField.absNorm_differentIdeal (K := X.B.I.F) (𝓞 X.B.I.F)
    rw [h, Ideal.absNorm_bot] at h2
    exact NumberField.discr_ne_zero X.B.I.F (Int.natAbs_eq_zero.mp h2.symm)
  have hfin := Ideal.hasFiniteMulSupport hne
  have hdN : dN X = fun v => ((Nat.castRingHom ℝ : ℕ →* ℝ).comp
      (Ideal.absNorm : Ideal (𝓞 X.B.I.F) →*₀ ℕ).toMonoidHom) (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) :=
    funext (fun v => dN_eq X v)
  refine ⟨?_, ?_⟩
  · rw [hdN]
    exact hfin.subset (Function.mulSupport_comp_subset (map_one _) _)
  · rw [hdN, ← MonoidHom.map_finprod _ hfin, Ideal.finprod_heightOneSpectrum_factorization hne]
    show ((Ideal.absNorm (differentIdeal ℤ (𝓞 X.B.I.F)) : ℕ) : ℝ) = _
    rw [NumberField.absNorm_differentIdeal (K := X.B.I.F) (𝓞 X.B.I.F), Nat.cast_natAbs, Int.cast_abs]

def DiscEF : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    |((NumberField.discr X.B.I.E : ℤ) : ℝ)| = |((NumberField.discr X.B.I.F : ℤ) : ℝ)| ^ 2

def DegE : Prop := ∀ (D : D7), Module.finrank ℚ D.host.E = 2 * D.R.f

theorem discRd_of (hE : DiscEF) (hd : DegE) : DiscRd := by
  intro D X
  have hdisc : NumberField.discr X.B.I.E = NumberField.discr D.host.E :=
    NumberField.discr_eq_discr_of_algEquiv (K := X.B.I.E) X.ιE.toRatAlgEquiv
  have h1 := hE D X
  rw [hdisc] at h1
  have h2 := hd D
  have ha : 0 ≤ |((NumberField.discr X.B.I.F : ℤ) : ℝ)| := abs_nonneg _
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  have hf : (D.R.f : ℝ) ≠ 0 := by
    have : D.R.f ≠ 0 := by omega
    exact_mod_cast this
  unfold Formalism.BasicNotions.Host.rdE
  rw [h1, h2, ← Real.rpow_natCast (|((NumberField.discr X.B.I.F : ℤ) : ℝ)|) 2, ← Real.rpow_mul ha,
    ← Real.rpow_natCast _ D.R.f, ← Real.rpow_mul ha]
  have hex : ((2 : ℕ) : ℝ) * (1 / ((2 * D.R.f : ℕ) : ℝ)) * (D.R.f : ℝ) = 1 := by
    push_cast
    field_simp
  rw [hex, Real.rpow_one]

theorem lemmaMSStd_of_leaves (hO : MSOrd) (hT : MSTyp) (hG : StepGSplit) (hC : TypCount) (hE : DiscEF) (hd : DegE)
    {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Formalism.L2.SG.Pf.Carrier.EnergyConst2.LemmaMSStd X u u' ψ := by
  exact lemmaMSStd_of hO hT diffProd_holds (discRd_of hE hd) (typNorm_of hG hC) X u u' ψ

end Formalism.L2.SG.Pf.Carrier.EnergyMS
end
end

section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.AllRowsRMul

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

abbrev phi (x y : X.B.I.L2 X.B.μf X.B.fund) (c : X.B.I.Gf) : ℂ := ⟪x, X.B.R (1, c) y⟫_ℂ

theorem R_facts :
    (∀ a b : X.B.I.GA, X.B.R (a * b) = (X.B.R a).comp (X.B.R b)) ∧ (∀ a F, ‖X.B.R a F‖ = ‖F‖) ∧
      (∀ x y : X.B.I.L2 X.B.μf X.B.fund, StronglyMeasurable (phi X x y)) := by
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have hU := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have hFR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  have := hFR.2.1
  have := hFR.2.2.2.1
  have : X.B.μf.IsMulRightInvariant := hU
  have : (X.B.I.muA X.B.μf).IsMulLeftInvariant := rr_muA_left X.B.I X.B.μf
  have : (X.B.I.muA X.B.μf).IsMulRightInvariant := rr_muA_right X.B.I X.B.μf
  have : SigmaFinite (X.B.I.muA X.B.μf) := rr_muA_sigmaFinite X.B.I X.B.μf
  have h1 := rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have h2 := rr_IsReg_of X.B.I X.B.μf X.B.fund X.B.R X.B.R_spec
  refine ⟨fun a b => rr_mul h1 h2 a b, fun a F => rr_norm h1 h2 a F, fun x y => ?_⟩
  exact (rr_weak_meas h1 h2 x y).comp_measurable (measurable_const.prodMk measurable_id)

theorem phi_bound (x y : X.B.I.L2 X.B.μf X.B.fund) (c : X.B.I.Gf) : ‖phi X x y c‖ ≤ ‖x‖ * ‖y‖ := by
  have h := (R_facts X).2.1 (1, c) y
  calc ‖phi X x y c‖ ≤ ‖x‖ * ‖X.B.R (1, c) y‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [h]

theorem isRConvF_conv {f g : X.B.I.Gf → ℂ} {T U : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund}
    (hf : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R f T) (hg : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R g U) :
    X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (X.B.I.convF X.B.μf f g) (T.comp U) := by
  obtain ⟨hmul, -, hmeas⟩ := R_facts X
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have : SecondCountableTopology X.B.I.Gf := rr_secondCountable X.B.I X.B.μf
  have hK : Integrable (fun p : X.B.I.Gf × X.B.I.Gf => f p.1 * g (p.1⁻¹ * p.2)) (X.B.μf.prod X.B.μf) := by
    have h0 : Integrable (fun q : X.B.I.Gf × X.B.I.Gf => f q.1 * g q.2) (X.B.μf.prod X.B.μf) := hf.1.mul_prod hg.1
    exact ((measurePreserving_prod_inv_mul X.B.μf X.B.μf).integrable_comp h0.aestronglyMeasurable).2 h0
  have hF : ∀ x y : X.B.I.L2 X.B.μf X.B.fund, Integrable (fun p : X.B.I.Gf × X.B.I.Gf =>
      f p.1 * g (p.1⁻¹ * p.2) * phi X x y p.2) (X.B.μf.prod X.B.μf) := fun x y =>
    hK.mul_bdd ((hmeas x y).comp_measurable measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => phi_bound X x y p.2)
  refine ⟨hK.integral_prod_right, fun x y => ?_⟩
  have step : ∀ a, ⟪x, X.B.R (1, a) (U y)⟫_ℂ = ∫ c, g (a⁻¹ * c) * phi X x y c ∂X.B.μf := by
    intro a
    rw [← ContinuousLinearMap.adjoint_inner_left, hg.2]
    have e : ∀ b, g b * ⟪ContinuousLinearMap.adjoint (X.B.R (1, a)) x, X.B.R (1, b) y⟫_ℂ =
        g b * phi X x y (a * b) := by
      intro b
      rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← hmul, Prod.mk_mul_mk, one_mul]
    simp_rw [e]
    rw [← integral_mul_left_eq_self (fun c => g (a⁻¹ * c) * phi X x y c) a]
    congr 1
    funext b
    simp only [inv_mul_cancel_left]
  rw [ContinuousLinearMap.comp_apply, hf.2]
  simp_rw [step, ← integral_const_mul]
  have hF' : Integrable (Function.uncurry fun a c => f a * (g (a⁻¹ * c) * phi X x y c)) (X.B.μf.prod X.B.μf) := by
    have := hF x y
    simp only [mul_assoc] at this
    exact this
  rw [integral_integral_swap hF']
  congr 1
  funext c
  unfold AutInst.convF
  rw [← integral_mul_const]
  congr 1
  funext a
  ring

end Formalism.L2.SG.Pf.AllRowsRMul
end
end
