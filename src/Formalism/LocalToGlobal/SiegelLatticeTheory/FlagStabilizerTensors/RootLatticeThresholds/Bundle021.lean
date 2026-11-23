module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdBounds
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PiProd


set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
        = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi fun i => μ (Fin.succ i))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero]
          simp
      _ = (∫⁻ x, f 0 x ∂(μ 0)) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ (Fin.succ i)) := by
          rw [← ih (fun i => f (Fin.succ i)) (fun i => hf _)]
          exact lintegral_prod_mul (hf 0).aemeasurable
            (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

theorem lintegral_fintype_prod {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod (fun i => f (e i)) (fun i => hf _)

theorem pi_withDensity {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hfin : ∀ i x, f i x ≠ ⊤) :
    Measure.pi (fun i => (μ i).withDensity (f i)) = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  haveI : ∀ i, SigmaFinite ((μ i).withDensity (f i)) := fun i =>
    SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall (hfin i))
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_fintype_prod _ hf]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

end PiProd

section WeilGen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem weil_of_bruhat (μG μS : Measure G) [SigmaFinite μG] [SFinite μS] [μG.IsMulLeftInvariant]
    (B : G → ℝ≥0∞) (hBm : Measurable B) (hinv : μS.map (fun s => s⁻¹) = μS)
    (hb1 : ∀ x, ∫⁻ s, B (s * x) ∂μS = 1) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂(μG.withDensity B) := by
  have hF : Measurable fun p : G × G => f (p.1 * p.2) := hf.comp measurable_mul
  have hg : Measurable fun x => ∫⁻ s, f (s * x) ∂μS := hF.lintegral_prod_left'
  have hBinv : ∀ x, ∫⁻ s, B (s⁻¹ * x) ∂μS = 1 := by
    intro x
    have h1 : ∫⁻ s, B (s * x) ∂(μS.map fun s => s⁻¹) = ∫⁻ s, B (s⁻¹ * x) ∂μS :=
      lintegral_map (hBm.comp (measurable_mul_const x)) measurable_inv
    rw [← h1, hinv, hb1]
  rw [lintegral_withDensity_eq_lintegral_mul _ hBm hg]
  symm
  calc _ = ∫⁻ x, ∫⁻ s, B x * f (s * x) ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply]
        exact (lintegral_const_mul _ (hf.comp (measurable_mul_const x))).symm
    _ = ∫⁻ s, ∫⁻ x, B x * f (s * x) ∂μG ∂μS :=
        lintegral_lintegral_swap
          ((hBm.comp measurable_fst).mul (hf.comp (measurable_snd.mul measurable_fst))).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, B (s⁻¹ * x) * f x ∂μG ∂μS := by
        refine lintegral_congr fun s => ?_
        simpa only [inv_mul_cancel_left] using
          lintegral_mul_left_eq_self (μ := μG) (fun x => B (s⁻¹ * x) * f x) s
    _ = ∫⁻ x, ∫⁻ s, B (s⁻¹ * x) * f x ∂μS ∂μG :=
        lintegral_lintegral_swap
          ((hBm.comp (measurable_fst.inv.mul measurable_snd)).mul (hf.comp measurable_snd)).aemeasurable
    _ = ∫⁻ x, f x ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [show ∫⁻ s, B (s⁻¹ * x) * f x ∂μS = (∫⁻ s, B (s⁻¹ * x) ∂μS) * f x from
          lintegral_mul_const _ (hBm.comp (measurable_inv.mul_const x)), hBinv, one_mul]

end WeilGen

variable {D : D7}

def NV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {g | Formalism.L2.SG.HidaSetting.InN (X.B.I.ε v) (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a))
    (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) (uMat g)}

def StV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  StSet (NV X u v) (NV X u' v) (γ v)

def stCoordV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) (y : Formalism.REAL.UJ (X.B.I.ε v)) : FreeE w → ℂ :=
  fun p => ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1)) *
    Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v)
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR ⟨p.1.1.1, by have := p.2.1; omega⟩))
      (uMat ((γ v)⁻¹ * y * γ v) *ᵥ frm X u' D.host.rdE v p.1.2)

def muStabV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : Point D.host.E (D.R.rS + 1)) : Measure (FreeE w → ℂ) :=
  Measure.pi fun _ => ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) • (volume : Measure ℂ)

def LocPinAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ v, ∃ μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)), IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv ∧
    IsQuotLoc μRv (ν v) ∧ μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w

def LocPin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  LocPinAt X u u' w (νl w)

def LocUni (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w → ∀ v, ∃ μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
    IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv ∧ μRv.map (fun s => s⁻¹) = μRv ∧
    μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w ∧
    ∃ b : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable b ∧ (∀ x, b x ≠ ⊤) ∧ ∀ x, ∫⁻ s, b (s * x) ∂μRv = 1

def GlobProd (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w →
    ∀ μRv : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      (∀ v, IsHaarLoc (StV X u u' (gamW X u u' w) v) (μRv v) ∧
        (μRv v).map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w) →
      μR = Measure.pi μRv

theorem ooQuot_pin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) (hR : StRel X u u')
    (hLU : LocUni X u u') (hGP : GlobProd X u u') :
    ∃ νl, (∀ w, OkPt X u u' w → LocPin X u u' w νl) ∧ Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' νq νl := by
  have hI := stInv_of_rel X u u' hR
  have key : ∀ w : Point D.host.E (D.R.rS + 1),
      ∃ ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)), OkPt X u u' w →
        LocPinAt X u u' w ν ∧ ∀ y : ∀ v, X.Vloc u' v,
          (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
            Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
              (X.tensU u' y) =
          X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
            Jv (ν v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) (y v)) := by
    intro w
    by_cases hw : OkPt X u u' w
    · obtain ⟨μR, hH, hQ, hM⟩ := hN.2 w hw.1
      haveI : SigmaFinite μR := hH.1
      choose μRv hHv hIv hMv b hbm hbt hb1 using hLU w hw μR hH hM
      have hprod : μR = Measure.pi μRv := hGP w hw μR hH hM μRv fun v => ⟨hHv v, hMv v⟩
      haveI : ∀ v, SigmaFinite (μRv v) := fun v => (hHv v).1
      have hσ : ∀ v, SigmaFinite ((Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v)) :=
        fun v => SigmaFinite.withDensity_of_ne_top' (hbt v)
      have hBm : Measurable fun x : X.B.I.Ginf => ∏ v, b v (x v) :=
        Finset.measurable_prod _ fun v _ => (hbm v).comp (measurable_pi_apply v)
      have hb1G : ∀ x : X.B.I.Ginf, ∫⁻ s, (∏ v, b v ((s * x) v)) ∂μR = 1 := by
        intro x
        rw [hprod]
        have := lintegral_fintype_prod (μ := μRv) (fun v t => b v (t * x v))
          (fun v => (hbm v).comp (measurable_mul_const _))
        refine this.trans ?_
        exact Finset.prod_eq_one fun v _ => hb1 v (x v)
      have hinvG : μR.map (fun s => s⁻¹) = μR := by
        haveI : ∀ v, SigmaFinite ((μRv v).map (fun s => s⁻¹)) := fun v => by rw [hIv v]; infer_instance
        rw [hprod]
        have := Measure.pi_map_pi (μ := μRv) (f := fun _ s => s⁻¹) (fun v => measurable_inv.aemeasurable)
        refine this.trans ?_
        congr 1
        funext v
        exact hIv v
      have hp : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR
          (Measure.pi fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v)) := by
        intro f hf
        rw [pi_withDensity _ b hbm hbt]
        exact weil_of_bruhat (Formalism.L2.SG.ProjRows.muInf X.B.I) μR _ hBm hinvG hb1G f hf
      refine ⟨fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v), fun _ => ⟨fun v => ?_, fun y => ?_⟩⟩
      · refine ⟨μRv v, hHv v, fun f hf => ?_, hMv v⟩
        exact weil_of_bruhat (Formalism.REAL.muG (X.B.I.ε v)) (μRv v) (b v) (hbm v) (hIv v) (hb1 v) f hf
      · exact oo_eq_tens X u u' _ μR _ _ hH.2.2.1 _ hBm hb1G _ hσ hQ hp (hI w hw) y
    · exact ⟨fun v => Formalism.REAL.muG (X.B.I.ε v), fun h => absurd h hw⟩
  choose νl hνl using key
  exact ⟨νl, fun w hw => (hνl w hw).1, fun w hw hG y => (hνl w ⟨hw, hG⟩).2 y⟩

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

section

noncomputable section

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt

namespace Formalism.L2.SG.Pf.ThresholdAtPlaceBounds

theorem thrSet_pos {ι : Type} [Fintype ι] (G : Sz.Glob ι) {C : ℝ} (hC : 1 ≤ C) {de de' : ℕ → ℝ} {T T' : ℝ} {l : ℕ}
    (hB : ∀ w, 0 < G.supI de de' T T' l w) (hB1 : ∀ w, 0 < G.cutSupLong de de' T T' l w)
    (hka : 0 < G.ka) (hN : 0 < G.N) (hg : 0 < G.g) (hI : 0 < G.lenI) (hTT : 0 < T * T') :
    ∀ x ∈ G.thrSet C de de' T T' l, 0 < x := by
  intro x hx
  obtain ⟨i, -, -, hx⟩ := hx
  have hC0 : 0 < C := by linarith
  rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨s, -, -, rfl⟩ | rfl
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB1 w
    unfold Formalism.FourierDecayAlt.Sz.xHat
    positivity
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB w
    unfold Formalism.FourierDecayAlt.Sz.xHat
    positivity
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB w
    unfold Formalism.FourierDecayAlt.Sz.lamHat
    positivity
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB w
    have hs : 0 < Real.sqrt (T * T') := Real.sqrt_pos.mpr hTT
    unfold Formalism.FourierDecayAlt.Sz.lamPrimeHat
    apply Real.sqrt_pos.mpr
    positivity

variable {D : D7}

theorem gOf_place' (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (w : InfinitePlace D.host.E) :
    (Formalism.L2.SG.SpectralTiesReal.gOf D e).place w = Formalism.MainNotions.BridgeLemma.cfgOf D (e w) := by
  simp only [Formalism.FourierDecayAlt.Sz.Glob.place, Formalism.MainNotions.BridgeLemma.cfgOf, Formalism.L2.SG.SpectralTiesReal.gOf]
  congr 1
  exact Formalism.MainNotions.BridgeLemma.sza_m_eq D

theorem lOf_succ_le (de de' : ℕ → ℝ) : Formalism.L2.SG.SpectralTiesReal.lOf D de de' + 1 ≤ D.R.k := by
  unfold Formalism.L2.SG.SpectralTiesReal.lOf
  split_ifs with h
  · have := (Nat.find_spec h).2.1
    omega
  · have := D.R.m_add_three_le_k
    omega

theorem del_big {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h5 : 5 ≤ Cl) :
    16000 * (D.R.k : ℝ) ^ 3 ≤ D.s.Del := by
  have hHc := hH
  obtain ⟨-, -, a3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a20, -, -, -, -, -⟩ := hHc
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hf16 : (16 : ℝ) ≤ D.R.f := by
    have h2 := D.R.two_le_m
    have : 16 ≤ D.R.m ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left h2 4
    exact_mod_cast le_trans this a3
  set x : ℝ := (D.R.k : ℝ) * D.R.f * large₂.sc.L with hx
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) * 1 * 1 ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := by gcongr <;> linarith
    linarith
  have hp : x ^ (5 : ℝ) ≤ x ^ Cl := Real.rpow_le_rpow_of_exponent_le hx1 h5
  have e5 : x ^ (5 : ℝ) = x ^ (5 : ℕ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e5] at hp
  have hx5 : x ^ 5 = (D.R.k : ℝ) ^ 3 * ((D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5) := by rw [hx]; ring
  have hf5 : (16 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hf16 5
  have hL5 : 1 ≤ large₂.sc.L ^ 5 := one_le_pow₀ hL
  have hk2 : (25 : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by nlinarith
  have hprod : (16000 : ℝ) ≤ (D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5 := by
    have a : (25 : ℝ) * 16 ^ 5 * 1 ≤ (D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5 := by gcongr
    linarith
  have hk3 : 0 ≤ (D.R.k : ℝ) ^ 3 := by positivity
  have : 16000 * (D.R.k : ℝ) ^ 3 ≤ x ^ 5 := by rw [hx5]; nlinarith
  linarith

theorem first_size_lower_bound {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hD : StandingNumericalData D C0) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (h40 : 40 ≤ Cl) (τ : D.what₂.Tau) :
    40 * ((Formalism.MainNotions.BridgeLemma.cfgOf D τ).m : ℝ) * (Formalism.MainNotions.BridgeLemma.cfgOf D τ).k * (Formalism.MainNotions.BridgeLemma.cfgOf D τ).Del ≤
      (Formalism.MainNotions.BridgeLemma.cfgOf D τ).b 1 := by
  obtain ⟨-, -, -, -, -, -, -, h8, -, -, -, -, -, -, -, h16, -⟩ := hH
  have hm := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have h1m : (1 : ℕ) ≤ D.R.m := by omega
  have hb := h8 τ 1 le_rfl h1m
  have hkpos : (0 : ℝ) < (D.R.k : ℝ) := by exact_mod_cast (by omega : 0 < D.R.k)
  have hk : (0 : ℝ) < (D.R.k : ℝ) ^ Cl := Real.rpow_pos_of_pos hkpos _
  have hkb : (D.R.k : ℝ) ^ Cl ≤ bOne D τ 1 := le_trans (le_max_left _ _) (h16 τ 1 le_rfl h1m).1
  dsimp only [Formalism.MainNotions.BridgeLemma.cfgOf]
  rcases le_or_gt 0 ((D.R.m : ℝ) * D.R.k * D.s.Del) with h0 | h0
  · nlinarith
  · nlinarith

theorem thrSet_pos_at {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hD : StandingNumericalData D C0)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h40 : 40 ≤ Cl) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) {CA : ℝ}
    (hCA : 1 ≤ CA) (u u' : D.what₂.Word) :
    ∀ x ∈ (Formalism.L2.SG.SpectralTiesReal.gOf D e).thrSet CA (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')
      (D.mem u).A.T (D.mem u').A.T
      (Formalism.L2.SG.SpectralTiesReal.lOf D (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')), 0 < x := by
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hDel := del_big hH (by linarith)
  have hHc := hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a19, -, -, -, -, -, -⟩ := hHc
  have hT : ((D.mem u).A.T : ℝ) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hT' : ((D.mem u').A.T : ℝ) ≠ 0 := by exact_mod_cast (D.mem u').A.T_prime.ne_zero
  have hTp : (0 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hTp' : (0 : ℝ) < (D.mem u').A.T := by exact_mod_cast (D.mem u').A.T_prime.pos
  have hka : 0 < (Formalism.L2.SG.SpectralTiesReal.gOf D e).ka := by
    show 0 < Real.pi / D.host.v
    exact div_pos Real.pi_pos (by linarith)
  have hg : 0 < (Formalism.L2.SG.SpectralTiesReal.gOf D e).g := by
    show 0 < ((D.host.g 0 : ℕ) : ℝ) * ((D.host.g 1 : ℕ) : ℝ)
    have a : (0 : ℝ) < ((D.host.g 0 : ℕ) : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
    have b : (0 : ℝ) < ((D.host.g 1 : ℕ) : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
    exact mul_pos a b
  have hrk : (D.R.rS : ℝ) + 1 ≤ D.R.k := by
    have h1 := Formalism.MainNotions.BridgeLemma.m_eq D
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.rS + 1 ≤ D.R.k)
  have hN : (Formalism.L2.SG.SpectralTiesReal.gOf D e).N = 4 * 5 * ((D.R.rS : ℝ) + 1) := rfl
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hN3 : (Formalism.L2.SG.SpectralTiesReal.gOf D e).N ^ 3 ≤ D.s.Del / 2 := by
    rw [hN]
    have : ((D.R.rS : ℝ) + 1) ^ 3 ≤ (D.R.k : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hrk 3
    nlinarith
  have hN1 : (11 / 4 : ℝ) ≤ (Formalism.L2.SG.SpectralTiesReal.gOf D e).N ^ 3 := by
    rw [hN]
    have h20 : (20 : ℝ) ≤ 4 * 5 * ((D.R.rS : ℝ) + 1) := by nlinarith
    have := pow_le_pow_left₀ (by norm_num) h20 3
    norm_num at this
    linarith
  have hl := lOf_succ_le (D := D) (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')
  have hk3 : (125 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hk5 3
    norm_num at this
    linarith
  have hD11 : (11 / 2 : ℝ) ≤ D.s.Del := by nlinarith
  refine thrSet_pos _ hCA (fun w => ?_) (fun w => ?_) hka (by rw [hN]; positivity) hg ?_ (mul_pos hTp hTp')
  · unfold Sz.Glob.supI
    rw [gOf_place']
    exact ThresholdBounds.supI_pos _ (Formalism.MainNotions.BridgeLemma.cfg_ok hD hH (e w)) (first_size_lower_bound hD hH h40 (e w)) hD11
      (Formalism.MainNotions.BridgeLemma.isWord_deOf D u) (Formalism.MainNotions.BridgeLemma.isWord_deOf D u') hl hT hT' hka (pow_pos hg _)
  · unfold Sz.Glob.cutSupLong
    rw [gOf_place']
    exact ThresholdBounds.sSup_be_image_cutIntervalLong_pos _ (Formalism.MainNotions.BridgeLemma.cfg_ok hD hH (e w)) (first_size_lower_bound hD hH h40 (e w)) hN1 hN3
      (Formalism.MainNotions.BridgeLemma.isWord_deOf D u) (Formalism.MainNotions.BridgeLemma.isWord_deOf D u') hl hT hT' hka (pow_pos hg _)
  · show 0 < (D.s.Del : ℝ) / 2 - 5 / 2
    linarith

end Formalism.L2.SG.Pf.ThresholdAtPlaceBounds
end
end
