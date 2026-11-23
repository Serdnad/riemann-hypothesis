module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle075
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Mathlib.RingTheory.PowerSeries.Exp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle070
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.GradedWeylDivisibility.StatementA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle079
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SatakeDualWeyl.Bundle001
public import Mathlib.RingTheory.Unramified.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle078
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.cyclicWordMarkedClusters_letterwise : ∀ {n : ℕ} (th : ZMod n → Prop) (j : ℕ), Clusters th j → ∀ t, th t → (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨ ∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k) := by
  first | exact @GlobalTheory.HTW.Rec.clusters_letterwise | exact GlobalTheory.HTW.Rec.clusters_letterwise | (intros; apply GlobalTheory.HTW.Rec.clusters_letterwise <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.jT2_hcAt_nodup_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (g : D.R.GG) (s : Bool), Roomy L C → (jT2 (hcAt D g) j s).Nodup := by
  first | exact @GlobalTheory.HTW.Rec.twistedDualJumpsWithoutBlock_nodup_of_roomy | exact GlobalTheory.HTW.Rec.twistedDualJumpsWithoutBlock_nodup_of_roomy | (intros; apply GlobalTheory.HTW.Rec.twistedDualJumpsWithoutBlock_nodup_of_roomy <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem long_clusters : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG) (j : ℕ), 4 * H.Lw < orderOf φ.2 → 1 ≤ j →
    2 * j + 2 ≤ H.Lw →
    Clusters (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) j ∧ j + 1 ≤ orderOf φ := by
  intro R H τ φ j h4 hj hjL
  have hpos : 0 < orderOf φ := orderOf_pos φ
  have hdvd : orderOf φ.2 ∣ orderOf φ := orderOf_snd_dvd_orderOf
  have hle : orderOf φ.2 ≤ orderOf φ := Nat.le_of_dvd hpos hdvd
  have hw := GlobalTheory.T.atMostTwoThick_in_window_long_orbit H τ φ h4
  refine ⟨GlobalTheory.T.cyclicWord_markedClusters_of_atMostTwoInWindow _ H.Lw j hj (by omega) (by omega) hw, by omega⟩

end GlobalTheory
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem roomy_of_large : ∀ eps C A : ℝ, 0 < eps → 100 ≤ C → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → Roomy L C := by
  intro eps C A he hC
  have hC0 : (0 : ℝ) ≤ C := by linarith
  obtain ⟨x1, h1⟩ := GlobalTheory.T.thinSize_dominates_at_large_scale eps he
  obtain ⟨x2, h2⟩ := GlobalTheory.T.scale_log_mul_le_size_ratio eps C (max A 0) he hC0 (le_max_right _ _)
  refine ⟨max (max x1 x2) 4, fun D L P hL hA hx => ?_⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx4 : (4 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  obtain ⟨a1, a2, a3⟩ := h1 D L P hL hx1
  refine ⟨hC, a1, a2, a3, GlobalTheory.T.topSize_add_le_three_halves_scale D L P hx4, ?_⟩
  have hb : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have hw : (D.host.Lw : ℝ) ≤ max A 0 * Real.log L.sc.x :=
    P.Lw_le.trans (mul_le_mul_of_nonneg_right (hA.trans (le_max_left _ _)) hlog)
  refine le_trans ?_ (h2 L.sc hL hx2)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0) hb

end GlobalTheory.HTW
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.BeProps

open MvPowerSeries GlobalTheory.ThStr Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ}

theorem norm_eq_one_of_pow {n : ℕ} (hn : 0 < n) {a : ℂ_[l]} (ha : a ^ n = 1) : ‖a‖ = 1 := by
  have h : ‖a‖ ^ n = 1 := by rw [← norm_pow, ha, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hn.ne').1 h

theorem norm_le_one_of_mem_Wp {w : ℂ_[l]} (hw : w ∈ Wp l) : ‖w‖ ≤ 1 := by
  have hc : IsClosed {x : ℂ_[l] | ‖x‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  refine closure_minimal (t := {x : ℂ_[l] | ‖x‖ ≤ 1}) (fun x hx => ?_) hc hw
  change ‖x‖ ≤ 1
  induction hx using Subring.closure_induction with
  | mem x hx => obtain ⟨n, hn, -, h⟩ := hx; exact (norm_eq_one_of_pow hn h).le
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | neg x _ hx => simpa using hx
  | mul x y _ _ hx hy => rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

variable [NeZero d]

theorem constantCoeff_laS (s : ZMod d) : constantCoeff (laS l d s) = 0 :=
  (GlobalTheory.BiextInhab.laK_idMod2 (K := ℂ_[l]) (d := d) hl.out).1 s

theorem constantCoeff_laAt {κ : Type} [Finite κ] (ι : ZMod d → κ) (s : ZMod d) :
    constantCoeff (laAt (l := l) ι s) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) (constantCoeff_laS s)

theorem coeff_subst_range {K σ : Type*} [CommRing K] {G : MvPowerSeries σ K}
    (hG : MvPowerSeries.constantCoeff G = 0) (f : PowerSeries K) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (f.subst G) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
        PowerSeries.coeff n f * MvPowerSeries.coeff α (G ^ n) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG),
    finsum_eq_sum_of_support_subset (s := Finset.range ((α.sum fun _ k => k) + 1))]
  · rfl
  · intro k hk
    by_contra h
    apply hk
    have hlt : (α.sum fun _ k => k) < k := by simpa using h
    have h0 : MvPowerSeries.coeff α (G ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hG)
      exact_mod_cast hlt
    simp [h0]

theorem expMv_eq_subst {σ : Type*} {G : MvPowerSeries σ ℂ_[l]} (hG : MvPowerSeries.constantCoeff G = 0) :
    expMv G = (PowerSeries.exp ℂ_[l]).subst G := by
  ext α
  rw [coeff_subst_range hG]
  show expMv G α = _
  rw [expMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [div_eq_inv_mul]

theorem subst_psubst {σ τ : Type} [Finite σ] {b : σ → MvPowerSeries τ ℂ_[l]} (hb : HasSubst b)
    {f : MvPowerSeries σ ℂ_[l]} (hf : constantCoeff f = 0) (g : PowerSeries ℂ_[l]) :
    subst b (PowerSeries.subst f g) = PowerSeries.subst (subst b f) g := by
  have ha : HasSubst (fun _ : Unit => f) := hasSubst_of_constantCoeff_zero fun _ => hf
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply ha hb]

end GlobalTheory.BeProps
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem trF_locCoch_eq_finsum_fib : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ (ρ : F →ₗ[k] k), IsRes k x ρ → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), trF k τ ρ (locCoch k K x h Finset.univ) = ∑ᶠ e : fib k K x, e.1 h := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ ρ hρ hac hred h
  have hloc : locCoch k K x (h : K) Finset.univ = (h : K) • vol0 k K x := if_pos rfl
  have h1 : trF k τ ρ (locCoch k K x (h : K) Finset.univ) = ρ (Algebra.trace F K (h : K)) := by
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hloc, map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [h1]
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd 0
  haveI : IsIntegrallyClosed (rA k x {0}) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  haveI : IsFractionRing (rA k x {0}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {0} (Finset.singleton_nonempty _)).1
  haveI := hc.fin
  have hint : IsIntegral (rA k x {0}) (h : K) := h.2
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := rA k x {0}) (K := F)).1 (Algebra.isIntegral_trace (L := F) hint)
  obtain ⟨ev, hev, hker⟩ := GlobalTheory.T.laurentConstantTerm_eq_eval_origin_chart k F d x hc.pd ρ hρ
  have ha' : (a : F) = Algebra.trace F K (h : K) := ha
  rw [← ha', hev, GlobalTheory.T.trace_eval_origin_eq_fibre_trace k F K d x hc ev hker h a ha', GlobalTheory.T.trace_fibreRing_eq_finsum_fibrePoints k F K d x hc hac hred h]

end GlobalTheory.PD
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem setting_of_wordBase : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)), D.nd.l i ≠ 2 → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → RecS.ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd := by
  intro D L HW i r ρ π w hw Cx hG Wd hl hB _ft T₁ T₂ F h1 h2 hF
  obtain ⟨ht1c, ht1w, ht1l⟩ := hB.t1 T₁ h1
  obtain ⟨ht2c, ht2low⟩ := hB.t2 T₂ h2
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨ht1c, ht2c, hF⟩, hB.small.1.2.2.2.2.2, ?_, fun a => ht2low _ft a, ?_, ht1l⟩
  · intro x y hxy
    have hv : ((algebraMap ↥(Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 x : ↥(D.nbr i w hw).Kw.1) : Loc.Om (D.nd.l i)) =
        ((algebraMap ↥(Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 y : ↥(D.nbr i w hw).Kw.1) : Loc.Om (D.nd.l i)) := by rw [hxy]
    exact Subtype.ext hv
  · intro y
    exact ⟨⟨y.1, show y.1 ∈ Loc.K0 (D.nbr i w hw).Kw from ⟨y.2, hB.unram y.2⟩⟩, Subtype.ext rfl⟩
  · exact (HW _).W_s _ 1 _ hG
  · rw [(D.loc _).PD_p]; exact hl
  · intro a
    have hw' := ht1w a
    have e : Wd.win a = (if Wd.up a then
        Set.Icc (Wd.sz a : ℤ) ((Wd.sz a : ℤ) + Wd.S) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η
      else Set.Icc (-(Wd.sz a : ℤ) - Wd.S) (-(Wd.sz a : ℤ)) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η) := by
      unfold NWord.win
      cases h : Wd.up a <;> ext u <;> simp [abs_le]
    rw [← e]; exact hw'
  · intro a ha
    rcases hB.num.thick_or a with h | h
    · exact absurd h ha
    · exact h

end GlobalTheory.HTW.RecS
end

section

noncomputable section

namespace GlobalTheory.HTW.RecS.Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.HTW.Rec GlobalTheory.HTW.RecS

theorem coefExt_dvr {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    ∃ _ : IsDomain ↥(OL Cx.LL), IsDiscreteValuationRing ↥(OL Cx.LL) ∧ IsFractionRing ↥(OL Cx.LL) ↥Cx.LL.1 :=
  (goodO_finExt_integers _ Cx.LL).1

section Std

variable {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {k : ℕ}

theorem mem_stdG_OL (x : Fin k → ↥LL.1) : x ∈ stdG ↥(OL LL) ↥LL.1 k ↔ ∀ j, x j ∈ OL LL := by
  constructor
  · rintro ⟨u, rfl⟩ j
    exact (u j).2
  · intro h
    exact ⟨fun j => ⟨x j, h j⟩, rfl⟩


set_option synthInstance.maxHeartbeats 400000 in
def stdLat (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : Lat K LL where
  V := Fin k → ↥LL.1
  ρ := matRep M
  cont := hc
  L :=
    { T := stdG ↥(OL LL) ↥LL.1 k
      stable := fun g x hx => by
        rw [mem_stdG_OL] at hx ⊢
        intro j
        change ∑ b, M g j b * x b ∈ OL LL
        exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (hO g j b) (hx b)
      fg := by
        rw [stdG, LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      free := Module.Free.of_equiv (LinearEquiv.ofInjective _ (stdG_inj Subtype.val_injective k))
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥LL.1 (Fin k)).span_eq]
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_⟩
        funext j'
        simp [Pi.single_apply] }

theorem stdLat_isMatRep (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : IsMatRep (stdLat M hO hc) M :=
  ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem finrank_stdLat (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : Module.finrank ↥LL.1 (stdLat M hO hc).V = k :=
  Module.finrank_fin_fun _

def latId (T : Lat K LL) : LatHom T.L T.L where
  f := LinearMap.id
  equiv _ _ := rfl
  cont := continuous_id
  T_le _ h := h

theorem latId_onto (T : Lat K LL) : (latId T).Onto := fun y hy => ⟨y, hy, rfl⟩

end Std

section LocRep

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

theorem locC_mem_OL {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) : TruncatedSeriesCountingIdentities.locC Cx M g a b ∈ OL Cx.LL := by
  have h1 : Br.loc D.nbr i w hw M g a b ∈ OL (D.nbr i w hw).LL :=
    ((D.nbr i w hw).eO (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)).2
  change Cx.inc (Br.loc D.nbr i w hw M g a b) ∈ OL Cx.LL
  exact IsIntegral.map ((IntermediateField.inclusion Cx.le).restrictScalars ℤ_[D.nd.l i]) h1

end LocRep

section Glob

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem continuous_twistedDual_rhoO (hρ : Continuous fun g => rhoO D.nd i ρ π g) : Continuous fun g => T2O D.nd i ρ π g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  have hW : Continuous fun g => WpO D.nd i ρ π g := h1.smul hρ
  have hε : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
    GlobalTheory.LocalInv.eps_cont D.nd i
  exact hε.smul (hW.comp continuous_inv).matrix_transpose

end Glob

section Sub

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

def phiK : KK D.nd i →+* ↥Cx.LL.1 := Cx.inc.comp (Br.toLLK (D.nbr i w hw))

theorem locC_eq_map {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    TruncatedSeriesCountingIdentities.locC Cx M g = (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiK i w hw Cx) := by
  refine Matrix.ext fun a b => ?_
  change Cx.inc ((D.nbr i w hw).toLL (M _ a b)) = Cx.inc (Br.toLLK (D.nbr i w hw) (toK D.nd i (M _ a b)))
  rw [Br.toLLK_alg]
  rfl

theorem mapM_rDuO (h : GE D.nd) :
    mapM (toK D.nd i) (rDuO D.nd i r π) h = toK D.nd i (((chiU D.nd i 1 * epsU D.nd i) h : (D.nd.O i)ˣ) : D.nd.O i) •
      (mapM (toK D.nd i) (rO D.nd i r π) h⁻¹).transpose := by
  ext a b
  simp [mapM, rDuO, twistM, dualM]

theorem mapM_T2O (h : GE D.nd) :
    mapM (toK D.nd i) (T2O D.nd i ρ π) h = toK D.nd i (((chiU D.nd i 1 * epsU D.nd i) h : (D.nd.O i)ˣ) : D.nd.O i) •
      (mapM (toK D.nd i) (rhoO D.nd i ρ π) h⁻¹).transpose := by
  ext a b
  simp [mapM, T2O, WpO, twistM, dualM]
  ring

end Sub

section Sub2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

theorem isSubOfSums_T2O (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    IsSubOfSums (matRep (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π))) fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) := by
  obtain ⟨e, he⟩ := hd
  let A : Matrix (Fin D.R.r) (Fin D.R.nV) (KK D.nd i) :=
    LinearMap.toMatrix' ((LinearMap.fst (KK D.nd i) _ _).comp e.toLinearMap)
  let B : Matrix (Fin D.R.nV) (Fin D.R.r) (KK D.nd i) :=
    LinearMap.toMatrix' (e.symm.toLinearMap.comp (LinearMap.inl (KK D.nd i) _ _))
  have hA : ∀ u, A.mulVec u = (e u).1 := fun u => by simp [A, LinearMap.toMatrix'_mulVec]
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  have hint : ∀ h : GE D.nd, A * mapM (toK D.nd i) (rO D.nd i r π) h = mapM (toK D.nd i) (rhoO D.nd i ρ π) h * A := by
    intro h
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hA, he]
  let φ := phiK i w hw Cx
  let At : Matrix (Fin D.R.nV) (Fin D.R.r) ↥Cx.LL.1 := A.transpose.map φ
  have hinj : Function.Injective At.mulVec := by
    have h1 : B.transpose.map φ * At = 1 := by
      rw [← Matrix.map_mul, ← Matrix.transpose_mul, hAB, Matrix.transpose_one, Matrix.map_one _ (map_zero φ) (map_one φ)]
    intro u v huv
    have := congrArg (B.transpose.map φ).mulVec huv
    simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
  refine ⟨1, fun _ => π, LinearMap.pi fun _ => Matrix.mulVecLin At, ?_, fun g v => ?_⟩
  · intro u v huv
    exact hinj (congrFun huv 0)
  · funext a
    change At.mulVec ((TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π) g).mulVec v) =
      (TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r π) g).mulVec (At.mulVec v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [locC_eq_map, locC_eq_map, mapM_rDuO, mapM_T2O]
    have hK : ∀ (s : KK D.nd i) (h : GE D.nd),
        A.transpose * (s • (mapM (toK D.nd i) (rhoO D.nd i ρ π) h).transpose) =
          (s • (mapM (toK D.nd i) (rO D.nd i r π) h).transpose) * A.transpose := by
      intro s h
      rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hint]
    simp only [At]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hK]

end Sub2

theorem exists_lattices {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (h : PtIn i r ρ π) :
    ∃ (T₁ T₂ : Lat (D.nbr i w hw).Kw Cx.LL) (F : LatHom T₁.L T₂.L),
      IsSubOfTwistedDualSums i r w hw Cx T₁ ∧ IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ ∧ F.Onto ∧ Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
  let T := stdLat (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) (locC_mem_OL i w hw Cx _)
    (fun v => locC_cont D i _ (continuous_twistedDual_rhoO i ρ π h.contρ) w hw Cx v)
  exact ⟨T, T, latId T, isSubOfSums_T2O i r ρ π w hw Cx h.dec, stdLat_isMatRep _ _ _, latId_onto T,
    finrank_stdLat _ _ _⟩

end GlobalTheory.HTW.RecS.Model
end
end

section


theorem _root_.GlobalTheory.T.weylRowAction_mem_weylLattice_square : ∀ (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ (M : Matrix (Fin n) (Fin n) R), ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν, Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν := by
  first | exact @GlobalTheory.WeylRowAll.rowAct_mem_weyl_square | exact GlobalTheory.WeylRowAll.rowAct_mem_weyl_square | (intros; apply GlobalTheory.WeylRowAll.rowAct_mem_weyl_square <;> assumption)
end

section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_complexConj_isometry_inert_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), IsInertAt (maximalRealSubfield E) E v P → ∃ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E), (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)) ∧ (∀ x, σ (σ x) = x) ∧ (∀ x, Valued.v (σ x) = Valued.v x) ∧ (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) ∧ σ ϖ = ϖ ∧ IsUnifV E P ϖ := by
  first | exact @GlobalTheory.InertConj.exists_conj_completion | exact GlobalTheory.InertConj.exists_conj_completion | (intros; apply GlobalTheory.InertConj.exists_conj_completion <;> assumption)
end
