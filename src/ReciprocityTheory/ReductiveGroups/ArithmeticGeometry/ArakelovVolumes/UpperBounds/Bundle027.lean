module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfP

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem vanish_other (hV : VanishAtSStatement (E := E)) (hM : MeasInvStatement (E := E))
    (hO : OrthoStatement (E := E)) (hLU : LUStatement (E := E)) (hR : NfacRmulStatement (E := E))
    (Xa : ArchInM X) (Fl : FlatM X Xa) (ψ : Frame X.Ψ r → ℝ) (C0 : ℝ) (hψb : ∀ x ∈ X.dom, ψ x ≤ C0)
    (bb : ℝ) (hbb : 0 ≤ bb) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (b0 : Frame X.Ψ r)
    (hb0 : b0 ∈ Bor X.Ψ r) (j : Fin Fl.δ) (hx : Fl.xs j = rmul x0 b0) (ε : ℝ) (hε : 0 < ε)
    (hball : closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0)
    (hiso : ∀ y ∈ closedBall (0 : V (nd X)) (2 * ε), (∀ k, Fl.s k (cpt X x0 y) = 0) → y = 0)
    (hnull : volume {y | y ∈ OmF X x0 ∧ HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y = 0} = 0)
    (F : V (nd X) → ℂ)
    (hI : ∫⁻ y in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤)
    (P : Frame X.Ψ r → ℂ) (hBE : IsBEq X Xa.Fp P) (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (j' : Fin Fl.δ) (hne : γ ≠ 1 ∨ j' ≠ j) :
    P (lact γ (Fl.xs j')) = 0 := by
  have hw0sec : X.IsSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1.1
  have hssec : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hy : lact γ (Fl.xs j') ∈ X.dom := OntoS.dom_lact X hγ (Fl.xs_mem j')
  obtain ⟨x1, ho1, b1, hb1, hyeq⟩ := hO r X _ hy
  have hx1dom : x1 ∈ X.dom := orth_mem_dom X x1 ho1

  have hs1 : ∀ k, Fl.s k x1 = 0 := by
    intro k
    have h0 : Fl.s k (lact γ (Fl.xs j')) = 0 :=
      (Fl.S_eq _ hy).2 ⟨j', γ, hγ, idF X, idF_mem X, by rw [rmul_idF]⟩ k
    rw [hyeq, (hssec k).2.1 x1 hx1dom b1 hb1] at h0
    exact (mul_eq_zero.1 h0).resolve_left (bchar_ne_zero X hb1 _)
  have hw1 : Fl.w0 x1 ≠ 0 := by
    intro h
    have h1 : Fl.w0 (lact γ (Fl.xs j')) = X.χ Xa.L γ * Fl.w0 (Fl.xs j') :=
      hw0sec.2.2 γ hγ _ (Fl.xs_mem j')
    rw [hyeq, hw0sec.2.1 x1 hx1dom b1 hb1, h, mul_zero] at h1
    exact mul_ne_zero (chi_ne X hγ) (Fl.w0_ne j') h1.symm
  have hx0dom : x0 ∈ X.dom := orth_mem_dom X x0 ho
  have hx0d : ∀ τ, (mat x0 τ).det ≠ 0 := fun τ => (hx0dom τ).1
  have hx1d : ∀ τ, (mat x1 τ).det ≠ 0 := fun τ => (hx1dom τ).1
  have hx1av := avoid_base X Xa Fl j j' hγ hne x0 b0 hb0 hx x1 b1 hb1 hyeq ε hball hiso hs1
  obtain ⟨Nb, hNb, hNbav⟩ :=
    nbhd_avoid X x0 hx0d (isCompact_closedBall (0 : V (nd X)) (2 * ε)) hx1av hx1d
  have hOm : IsOpen (OmF X x1) := (isOpen_dom X).preimage (cpt_diff X x1).continuous
  have hS : OmF X x1 ∩ cpt X x1 ⁻¹' Nb ∈ 𝓝 (0 : V (nd X)) := by
    refine Filter.inter_mem (hOm.mem_nhds (zero_mem_OmF X x1 ho1)) ?_
    apply (cpt_diff X x1).continuous.continuousAt.preimage_mem_nhds
    rw [cpt_zero X x1]
    exact hNb
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hS
  have hρ : 0 < δ / 2 := half_pos hδ
  have hcbδ : closedBall (0 : V (nd X)) (δ / 2) ⊆ ball 0 δ :=
    Metric.closedBall_subset_ball (half_lt_self hδ)
  have hcb : closedBall (0 : V (nd X)) (δ / 2) ⊆ OmF X x1 := fun w hw => (hδsub (hcbδ hw)).1
  have hbO : ball (0 : V (nd X)) (δ / 2) ⊆ OmF X x1 :=
    fun w hw => hcb (Metric.ball_subset_closedBall hw)
  have hbN : ∀ w ∈ ball (0 : V (nd X)) (δ / 2), cpt X x1 w ∈ Nb :=
    fun w hw => (hδsub (hcbδ (Metric.ball_subset_closedBall hw))).2

  obtain ⟨Δ, zOf, bOf, hΔ, -, hzOf, -, hdec, hlast⟩ := hLU r X x1 ho1
  have hN1 : ∀ w ∈ ball (0 : V (nd X)) (δ / 2), cpt X x1 w ∈ Nset X Δ zOf (δ / 2) := by
    intro w hw
    obtain ⟨hΔw, hzw, -⟩ := hlast w (hbO hw) (idF X) (idF_mem X)
    rw [rmul_idF] at hΔw hzw
    show (cpt X x1 w ∈ X.dom ∧ Δ (cpt X x1 w) ≠ 0) ∧ zOf (cpt X x1 w) ∈ ball (0 : V (nd X)) (δ / 2)
    exact ⟨⟨hbO hw, hΔw⟩, by rw [hzw]; exact hw⟩
  have hN2 : ∀ z ∈ OmF X x0, cpt X x0 z ∈ Nset X Δ zOf (δ / 2) →
      z ∉ closedBall (0 : V (nd X)) (2 * ε) := by
    intro z _ hzN hzB
    generalize hxz : cpt X x0 z = x at hzN
    have hzN' : (x ∈ X.dom ∧ Δ x ≠ 0) ∧ zOf x ∈ ball (0 : V (nd X)) (δ / 2) := hzN
    obtain ⟨⟨hxd, hxΔ⟩, hxb⟩ := hzN'
    obtain ⟨-, hbB, hxeq⟩ := hdec x hxd hxΔ
    apply hNbav _ (hbN _ hxb) z hzB (binv X (bOf x)) (binv_mem X hbB)
    calc cpt X x1 (zOf x) = rmul (rmul (cpt X x1 (zOf x)) (bOf x)) (binv X (bOf x)) :=
          (rmul_binv X _ hbB).symm
      _ = rmul x (binv X (bOf x)) := by rw [← hxeq]
      _ = rmul (cpt X x0 z) (binv X (bOf x)) := by rw [hxz]
  have hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have hNopen : IsOpen (Nset X Δ zOf (δ / 2)) :=
    hzOf.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hmeas : Measurable ((Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s)) :=
    (gφ_meas X P hBE.1.continuousOn Xa.Fp Xa.L Fl.s fun k => (hssec k).1.continuousOn).indicator
      hNopen.measurableSet
  have hinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      (Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s) (rmul x b) =
        (Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s) x := by
    classical
    intro x hx b hb
    have hiff := Nset_sat X x1 hdec hlast (δ / 2) hx hb
    by_cases hxN : x ∈ Nset X Δ zOf (δ / 2)
    · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hiff.2 hxN), if_pos hxN,
        gφ_rmul X hR hBE hssec hx hb]
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg (fun h => hxN (hiff.1 h)), if_neg hxN]

  obtain ⟨c1, hc1, hc1le⟩ := rhs_bound X x1 Xa Fl P (Nset X Δ zOf (δ / 2)) (δ / 2) hρ hcb hN1
  have hfin := lhs_finite X x0 ho Xa Fl ψ C0 hψb bb hbb ε hε hnull F hI P hPF
    (Nset X Δ zOf (δ / 2)) hN2
  have heq := hM r X x1 x0 ho1 ho _ hmeas hinv
  have hlt := hc1le.trans_lt (heq.trans_lt hfin)
  have hfinI := ENNReal.lt_top_of_mul_ne_top_right hlt.ne (ENNReal.ofReal_pos.2 hc1).ne'
  have hdet := etale_transfer X hLU hw0sec hssec (Fl.xs_mem j') (Fl.coord j') hγ (idF_mem X) ho1
    hb1 (by rw [rmul_idF]; exact hyeq) hw1
  have hnd : 0 < nd X := by have := Xa.n_ge; omega
  have hP1 : P x1 = 0 :=
    hV r X x1 hnd ho1 hx1dom P Fl.w0 Fl.s (δ / 2) hρ ((comp_cpt_diffOn X hBE.1 x1).mono hbO)
      (fun k => (comp_cpt_diffOn X (hssec k).1 x1).mono hbO)
      ((comp_cpt_diffOn X hw0sec.1 x1).mono hbO) hw1 hs1 hdet hfinI
  rw [hyeq, hBE.2 x1 hx1dom b1 hb1, hP1, mul_zero]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI ReciprocityTheory.ChartRestriction.G.AR.Up.OntoJ
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem onto_of (hPoin : PoinStatement (E := E)) (hExtF : ExtFStatement (E := E))
    (hGrad : RhGradFStatement (E := E)) (hExG : ExhaustGStatement (E := E))
    (hKa : KaUnfoldStatement (E := E)) (hPair : PairUnfoldStatement (E := E))
    (hBig : BigCellStatement (E := E)) (hConn : OmFConnStatement (E := E)) :
    OntoStatement (E := E) := by
  intro r X x0 hx0 hPD la W Ps g1 bb m hW hWL hbb4 hm hg1 hg1ne hPs hWPs hLev hSS FF hFF hfin
    f hf hfF
  obtain ⟨K, g, hg⟩ := hfin
  have hWm : Measurable W := hW.1
  have hPo := fun (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ)
      (hD : OntoJ.Dt X x0 W bb la F P) =>
    hPoin r X x0 hx0 hPD la W bb hW hWL hbb4 F P hD.1 hD.2.1 hD.2.2.1 hD.2.2.2
  have hae : ∀ᵐ z ∂(OntoI.nuF X x0 W FF), z ∈ FF := by
    have h1 : ∀ᵐ z ∂((muF X x0).restrict FF), z ∈ FF := ae_restrict_mem hFF.1
    first
      | exact (withDensity_absolutelyContinuous _ _).ae_le h1
      | (unfold OntoI.nuF; exact (withDensity_absolutelyContinuous _ _).ae_le h1)
  have hmemP : ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), OntoJ.Dt X x0 W bb la F P →
      MemLp (fun z => poin X la P (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) := fun F P hD =>
    OntoI.memLp_of (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm
      (hPo F P hD).2.1.1.1.continuousOn ((hPo F P hD).2.2.1 FF hFF)
  have hmemf : MemLp (fun z => f (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
    OntoI.memLp_of (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm
      hf.1.1.1.continuousOn hfF
  have hzero : MemLp (fun z => (0 : Frame X.Ψ r → ℂ) (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) := by
    refine (hmemP _ _ (OntoJ.Dt_zero X x0)).ae_eq (ae_of_all _ fun z => ?_)
    exact OntoI.poin_zero (r := r) (X := X) la _

  obtain ⟨M, hMmem⟩ : ∃ M : Submodule ℂ (Lp ℂ 2 (OntoI.nuF X x0 W FF)), ∀ v, v ∈ M ↔
      ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) (hD : OntoJ.Dt X x0 W bb la F P),
        v = (hmemP F P hD).toLp _ := by
    refine ⟨{ carrier := {v | ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ)
                (hD : OntoJ.Dt X x0 W bb la F P), v = (hmemP F P hD).toLp _}
              add_mem' := by
                rintro _ _ ⟨F1, P1, hD1, rfl⟩ ⟨F2, P2, hD2, rfl⟩
                refine ⟨_, _, OntoJ.Dt_add (r := r) (X := X) (x0 := x0) hWm hD1 hD2, ?_⟩
                rw [← MemLp.toLp_add (hmemP F1 P1 hD1) (hmemP F2 P2 hD2)]
                refine MemLp.toLp_congr _ _ ?_
                filter_upwards [hae] with z hz
                have hx : cpt X x0 z ∈ X.dom := hFF.2.1 hz
                show poin X la P1 (cpt X x0 z) + poin X la P2 (cpt X x0 z) =
                  poin X la (fun y => P1 y + P2 y) (cpt X x0 z)
                exact (OntoI.poin_add (r := r) (X := X) la ((hPo F1 P1 hD1).1 _ hx)
                  ((hPo F2 P2 hD2).1 _ hx)).symm
              zero_mem' := ⟨fun _ => 0, fun _ => 0, OntoJ.Dt_zero X x0, by
                rw [← MemLp.toLp_zero hzero]
                exact MemLp.toLp_congr _ _
                  (ae_of_all _ fun z => (OntoI.poin_zero (r := r) (X := X) la (cpt X x0 z)).symm)⟩
              smul_mem' := by
                rintro a _ ⟨F, P, hD, rfl⟩
                refine ⟨_, _, OntoJ.Dt_smul (r := r) (X := X) (x0 := x0) a hD, ?_⟩
                rw [← MemLp.toLp_const_smul a (hmemP F P hD)]
                exact MemLp.toLp_congr _ _
                  (ae_of_all _ fun z => (OntoI.poin_smul (r := r) (X := X) la a P (cpt X x0 z)).symm) },
      fun v => Iff.rfl⟩

  obtain ⟨D2, hD2i⟩ : ∃ D2 : Submodule ℂ (Frame X.Ψ r → ℂ), ∀ h, h ∈ D2 ↔
      h ∈ Submodule.span ℂ (Set.range g) ∧
        MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
    ⟨{ carrier := {h | h ∈ Submodule.span ℂ (Set.range g) ∧
          MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF)}
       add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, ha.2.add hb.2⟩
       zero_mem' := ⟨Submodule.zero_mem _, hzero⟩
       smul_mem' := fun c {h} hh => ⟨Submodule.smul_mem _ c hh.1, hh.2.const_smul c⟩ },
      fun h => Iff.rfl⟩
  have hD2m : ∀ h : D2, MemLp (fun z => (h : Frame X.Ψ r → ℂ) (cpt X x0 z)) 2
      (OntoI.nuF X x0 W FF) := fun h => ((hD2i h).1 h.2).2
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : D2 →ₗ[ℂ] Lp ℂ 2 (OntoI.nuF X x0 W FF), ∀ h : D2,
      Φ h = (hD2m h).toLp _ :=
    ⟨{ toFun := fun h => (hD2m h).toLp _
       map_add' := fun a b => MemLp.toLp_add (hD2m a) (hD2m b)
       map_smul' := fun c a => MemLp.toLp_const_smul c (hD2m a) }, fun h => rfl⟩
  have hMle : M ≤ LinearMap.range Φ := by
    intro v hv
    obtain ⟨F, P, hD, rfl⟩ := (hMmem v).1 hv
    obtain ⟨c, hc⟩ := hg _ (hSS _ (hPo F P hD).2.1) ((hPo F P hD).2.2.1 FF hFF)
    obtain ⟨h, hhD, hhx⟩ : ∃ h : Frame X.Ψ r → ℂ, h ∈ Submodule.span ℂ (Set.range g) ∧
        ∀ x, h x = ∑ i, c i * g i x :=
      ⟨∑ i, c i • g i, Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)),
        fun x => by simp [Finset.sum_apply]⟩
    have hae2 : (fun z => h (cpt X x0 z)) =ᵐ[OntoI.nuF X x0 W FF]
        fun z => poin X la P (cpt X x0 z) := by
      filter_upwards [hae] with z hz
      rw [hhx, hc _ (hFF.2.1 hz)]
    have hmh : MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
      (hmemP F P hD).ae_eq hae2.symm
    refine LinearMap.mem_range.2 ⟨⟨h, (hD2i h).2 ⟨hhD, hmh⟩⟩, ?_⟩
    rw [hΦ]
    exact MemLp.toLp_congr _ _ hae2
  haveI hfS : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) := by
    first
      | exact FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  have hD2le : D2 ≤ Submodule.span ℂ (Set.range g) := by
    intro h hh
    exact ((hD2i h).1 hh).1
  haveI hfD2 : FiniteDimensional ℂ D2 := by
    first
      | exact Submodule.finiteDimensional_of_le hD2le
      | exact Module.Finite.of_injective (Submodule.inclusion hD2le)
          (Submodule.inclusion_injective hD2le)
  haveI hfR : FiniteDimensional ℂ (LinearMap.range Φ) := by
    first
      | exact LinearMap.finiteDimensional_range Φ
  haveI hfM : FiniteDimensional ℂ M := by
    first
      | exact Submodule.finiteDimensional_of_le hMle
      | exact Module.Finite.of_injective (Submodule.inclusion hMle)
          (Submodule.inclusion_injective hMle)
  haveI : CompleteSpace M := by
    first
      | exact FiniteDimensional.complete ℂ M

  obtain ⟨y, hyM, w, hw, hvyw⟩ : ∃ y ∈ M, ∃ w ∈ M.orthogonal,
      hmemf.toLp _ = y + w := by
    first
      | exact Submodule.exists_add_mem_mem_orthogonal M _
      | exact Submodule.exists_add_mem_mem_orthogonal _
  obtain ⟨F, P, hD, rfl⟩ := (hMmem y).1 hyM
  have hmemf0 : MemLp (fun z => f (cpt X x0 z) - poin X la P (cpt X x0 z)) 2
      (OntoI.nuF X x0 W FF) := hmemf.sub (hmemP F P hD)
  have hwLp : w = hmemf0.toLp _ := by
    change w = (hmemf.sub (hmemP F P hD)).toLp _
    rw [MemLp.toLp_sub hmemf (hmemP F P hD), hvyw]
    abel
  have horth : ∀ (F' : V (nd X) → ℂ) (P' : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F' (OmF X x0) →
      InAt X x0 W bb F' → IsBEq X la P' → (∀ z ∈ OmF X x0, P' (cpt X x0 z) = F' z) →
      ∫ z in FF, poin X la P' (cpt X x0 z) *
          (starRingEnd ℂ) (f (cpt X x0 z) - poin X la P (cpt X x0 z)) *
          ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 = 0 := by
    intro F' P' h1 h2 h3 h4
    have hD' : OntoJ.Dt X x0 W bb la F' P' := ⟨h1, h2, h3, h4⟩
    have hmem' : (hmemP F' P' hD').toLp _ ∈ M :=
      (hMmem _).2 ⟨F', P', hD', rfl⟩
    have h0 : ⟪(hmemP F' P' hD').toLp _, w⟫_ℂ = 0 := by
      first
        | exact Submodule.inner_right_of_mem_orthogonal hmem' hw
    have h0' : ⟪w, (hmemP F' P' hD').toLp _⟫_ℂ = 0 := by
      first
        | exact inner_eq_zero_symm.1 h0
    rw [hwLp,
      OntoI.inner_toLp (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm hmemf0
        (hmemP F' P' hD')] at h0'
    refine (integral_congr_ae ?_).trans h0'
    filter_upwards with z
    ring
  have hf0SS : (fun y => f y - poin X la P y) ∈ X.SS la :=
    hSS _ (OntoI.bdd_sub (r := r) (X := X) hf.1 (hPo F P hD).2.1)
  have hff0 : InFF X x0 W FF (fun y => f y - poin X la P y) := by
    have hcf : ContinuousOn (fun z => f (cpt X x0 z)) (OmF X x0) :=
      hf.1.1.1.continuousOn.comp
        ((OntoB.cd_cpt (r := r) (X := X) (x0 := x0)).continuous.continuousOn)
        (by intro z hz; exact hz)
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2 / (1 : ℝ))) (muF X x0) :=
      OntoH.aem_of (r := r) (X := X) (x0 := x0)
        (ENNReal.continuous_ofReal.comp_continuousOn ((hcf.norm.pow 2).div_const 1))
    have haem : AEMeasurable
        (fun z => ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2 / (1 : ℝ)) * W (cpt X x0 z))
        ((muF X x0).restrict FF) :=
      (h1.mul (OntoH.measW (r := r) (X := X) (x0 := x0) hWm).aemeasurable).restrict
    have key := OntoI.lint_add_le (μ := (muF X x0).restrict FF) (a := fun z => f (cpt X x0 z))
      (b := fun z => -poin X la P (cpt X x0 z)) (k := fun _ => (1 : ℝ))
      (om := fun z => W (cpt X x0 z)) (fun _ => one_pos) haem
    simp only [div_one, norm_neg, ← sub_eq_add_neg] at key
    have hPF := (hPo F P hD).2.2.1 FF hFF
    show ∫⁻ z in FF, ENNReal.ofReal (‖f (cpt X x0 z) - poin X la P (cpt X x0 z)‖ ^ 2) *
      W (cpt X x0 z) ∂muF X x0 < ⊤
    refine lt_of_le_of_lt key (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · first
        | exact ENNReal.mul_lt_top (by simp) hfF
    · first
        | exact ENNReal.mul_lt_top (by simp) hPF
  have hvan := OntoH.vanish (r := r) (X := X) (x0 := x0) hExG hGrad hKa hPair hBig hConn hExtF
    hx0 hPD hW hWL hbb4 hm hg1 hg1ne hPs hWPs hLev hFF hf0SS hff0 horth
  obtain ⟨hD1, hD2, hD3, hD4⟩ := hD
  refine ⟨F, P, hD1, hD2, hD3, hD4, fun x hx => ?_⟩
  have hx0' := hvan x hx
  exact (sub_eq_zero.1 hx0').symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
