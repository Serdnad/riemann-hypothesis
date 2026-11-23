module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Mathlib.LinearAlgebra.Semisimple
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Schwarz
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped NNReal ComplexConjugate
open Filter Topology Set Metric MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.Mem.Th (InfF CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis

variable {D : D7} (V : HSp D)

def EisRegularAt (Φ : ℂ → GA D (dblSp V) → ℂ) (s₀ : ℂ) (k : ℕ) : Prop :=
  ∃ (r : ℝ) (H : ℂ → GA D (dblSp V) → ℂ), 0 < r ∧
    (∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * eisCont V Φ s g) ∧
    (∀ g, DifferentiableOn ℂ (H · g) (ball s₀ r)) ∧
    ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball s₀ r ×ˢ univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖H s g‖ ≤ C * Grow.height (dblSp V) g ^ N

def petCoef (m : Measure (GA D V)) (f₁ f₂ : GA D V → ℂ) : GA D V → ℂ := fun g => Cusp.petersson V m (rTr V g f₁) f₂

def BasicIdentity (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)) (Φ : GA D (dblSp V) → ℂ) (f₁ f₂ : GA D V → ℂ) : Prop :=
  DblConv V μ m (eis V Φ) f₁ f₂ ∧ ZetaConvH D.sp.cm.sig (gram_hdbl V) m Φ (petCoef V m f₁ f₂) ∧
    dblInt V μ m (eis V Φ) f₁ f₂ = zetaH D.sp.cm.sig (gram_hdbl V) m Φ (petCoef V m f₁ f₂)

end GlobalTheory.Eis

namespace GlobalTheory.Published

open GlobalTheory.Eis

def DoublingMethod : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
    HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
      (EisContinues V (flat V a φ s₁) ∧ ∀ s₀, ∃ k, EisRegularAt V (flat V a φ s₁) s₀ k) ∧
      (V.rank < b → EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1) ∧
      ∀ θ : InfF D, IsInfFam θ → V.SigOK → ∀ A : CptF V, Cusp.IsCartanFrame V A →
        ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ Cusp.A0 θ V A, ∀ f₂ ∈ Cusp.A0 θ V A,
          (∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂) ∧
          ZetaContinues V μ m (flat V a φ s₁) f₁ f₂

end GlobalTheory.Published

namespace GlobalTheory.Eis

theorem dslope_family {X : Type} [TopologicalSpace X] {H : ℂ → X → ℂ} {w : X → ℝ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ∀ x, DifferentiableOn ℂ (H · x) (ball s₀ r))
    (hc : ContinuousOn (fun p : ℂ × X => H p.1 p.2) (ball s₀ r ×ˢ univ))
    (hb : ∀ s ∈ ball s₀ r, ∀ x, ‖H s x‖ ≤ w x) (h0 : ∀ x, H s₀ x = 0) :
    (∀ x, DifferentiableOn ℂ (dslope (H · x) s₀) (ball s₀ (r / 2))) ∧
    ContinuousOn (fun p : ℂ × X => dslope (H · p.2) s₀ p.1) (ball s₀ (r / 2) ×ˢ univ) ∧
    ∀ s ∈ ball s₀ (r / 2), ∀ x, ‖dslope (H · x) s₀ s‖ ≤ w x / r := by
  have hsub : ball s₀ (r / 2) ⊆ ball s₀ r := ball_subset_ball (by linarith)
  have hsub' : closedBall s₀ (r / 2) ⊆ ball s₀ r := closedBall_subset_ball (by linarith)
  have h1 : ∀ x, DifferentiableOn ℂ (dslope (H · x) s₀) (ball s₀ r) := fun x =>
    (Complex.differentiableOn_dslope (ball_mem_nhds _ hr)).2 (hd x)
  refine ⟨fun x => (h1 x).mono hsub, ?_, fun s hs x => Complex.norm_dslope_le_div_of_mapsTo_ball (hd x)
    (fun z hz => by simpa [h0] using hb z hz x) (hsub hs)⟩
  rintro ⟨s₁, x₀⟩ ⟨hs₁, -⟩
  have h2 : ContinuousWithinAt (fun p : ℂ × X => dslope (H · x₀) s₀ p.1) (ball s₀ (r / 2) ×ˢ univ) (s₁, x₀) :=
    (((h1 x₀).continuousOn.continuousAt (isOpen_ball.mem_nhds (hsub hs₁))).comp_of_eq continuousAt_fst rfl).continuousWithinAt
  have h3 : Tendsto (fun p : ℂ × X => dslope (H · p.2) s₀ p.1 - dslope (H · x₀) s₀ p.1)
      (𝓝[ball s₀ (r / 2) ×ˢ univ] (s₁, x₀)) (𝓝 0) := by
    refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
    have h4 : ∀ᶠ x in 𝓝 x₀, ∀ z ∈ closedBall s₀ (r / 2), ‖H z x - H z x₀‖ < ε * (r / 4) := by
      refine (isCompact_closedBall s₀ (r / 2)).eventually_forall_of_forall_eventually fun z hz => ?_
      have h5 : ∀ y, ContinuousAt (fun p : ℂ × X => H p.1 p.2) (z, y) := fun y =>
        hc.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hsub' hz, trivial⟩)
      have h6 : ContinuousAt (fun p : X × ℂ => ‖H p.2 p.1 - H p.2 x₀‖) (x₀, z) :=
        (((h5 x₀).comp_of_eq (f := fun p : X × ℂ => (p.2, p.1)) (by fun_prop) rfl).sub
          ((h5 x₀).comp_of_eq (f := fun p : X × ℂ => (p.2, x₀)) (by fun_prop) rfl)).norm
      exact h6.eventually (gt_mem_nhds (by simpa using by positivity))
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (continuousAt_snd.eventually h4)] with p hp h4
    have h7 := Complex.norm_dslope_le_div_of_mapsTo_ball (f := fun z => H z p.2 - H z x₀) (R₂ := ε * (r / 4))
      (((hd _).sub (hd _)).mono hsub) (fun z hz => by simpa [h0] using (h4 z (ball_subset_closedBall hz)).le) hp.1
    have h8 : dslope (fun z => H z p.2 - H z x₀) s₀ p.1 = dslope (H · p.2) s₀ p.1 - dslope (H · x₀) s₀ p.1 := by
      rcases eq_or_ne p.1 s₀ with e | e
      · rw [e, dslope_same, dslope_same, dslope_same]
        exact deriv_fun_sub ((hd _).differentiableAt (ball_mem_nhds _ hr)) ((hd _).differentiableAt (ball_mem_nhds _ hr))
      · simp only [dslope_of_ne _ e, slope_def_field]; ring
    rw [← h8]
    refine h7.trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hε hr]
  simpa [ContinuousWithinAt] using h3.add h2

variable {D : D7} {V : HSp D} {Φ : ℂ → GA D (dblSp V) → ℂ} {s₀ : ℂ} {j k : ℕ}

theorem EisRegularAt.succ (h : EisRegularAt V Φ s₀ k) : EisRegularAt V Φ s₀ (k + 1) := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h
  refine ⟨r, fun s g => (s - s₀) * H s g, hr, fun s hs h0 g => by simp only [e s hs h0]; ring,
    fun g => (differentiableOn_id.sub_const _).mul (hd g), (by fun_prop : ContinuousOn (fun x : ℂ × _ => x.1 - s₀) _).mul hc,
    r * C, N, fun s hs g => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (mem_ball_iff_norm.1 hs).le (hb s hs g) (norm_nonneg _) hr.le

theorem EisRegularAt.pred (h : EisRegularAt V Φ s₀ (k + 1)) (hp : EisPoleLE V Φ s₀ j) (hj : j ≤ k) :
    EisRegularAt V Φ s₀ k := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h
  have h0 : ∀ g, H s₀ g = 0 := fun g => by
    obtain ⟨E, hE, -⟩ := id (hp.2 g)
    obtain ⟨c, hc⟩ := hE.poleLE_iff.1 (hp.2 g)
    have h1 : Tendsto (fun s => (s - s₀) ^ (k + 1 - j)) (𝓝[≠] s₀) (𝓝 0) :=
      (Continuous.tendsto' (by fun_prop) s₀ 0 (by simp; omega)).mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {s₀}ᶜ))) ((zero_mul c ▸ h1.mul hc).congr' ?_)
    filter_upwards [hE.cont_eventuallyEq, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)]
      with s h2 h3 h4
    rw [e s h4 h3, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega), ← h2]
    rfl
  obtain ⟨h1, h2, h3⟩ := dslope_family hr hd hc hb h0
  refine ⟨r / 2, fun s g => dslope (H · g) s₀ s, half_pos hr, fun s hs hs' g => ?_, h1, h2, C / r, N, fun s hs g => ?_⟩
  · have := sub_ne_zero.2 hs'
    simp only [dslope_of_ne _ hs', slope_def_field, h0, e s (ball_subset_ball (by linarith) hs) hs']
    field_simp
    ring
  · rw [div_mul_eq_mul_div]; exact h3 s hs g

theorem EisRegularAt.of_poleLE (h : EisRegularAt V Φ s₀ k) (hp : EisPoleLE V Φ s₀ j) : EisRegularAt V Φ s₀ j := by
  rcases le_total k j with hk | hk
  · exact Nat.le_induction h (fun _ _ => EisRegularAt.succ) j hk
  · exact Nat.decreasingInduction (motive := fun i _ => j ≤ i → EisRegularAt V Φ s₀ i)
      (fun i _ ih hi => (ih (by omega)).pred hp hi) (fun _ => h) hk le_rfl

theorem EisRegularAt.of_eisValueAt {ψ : GA D (dblSp V) → ℂ} (h : EisRegularAt V Φ s₀ k) (hv : EisValueAt V Φ s₀ ψ) :
    ∃ r : ℝ, 0 < r ∧ (∀ g, DifferentiableOn ℂ (eisCont V Φ · g) (ball s₀ r)) ∧
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => eisCont V Φ x.1 x.2) (ball s₀ r ×ˢ univ) ∧
      ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖eisCont V Φ s g‖ ≤ C * Grow.height (dblSp V) g ^ N := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h.of_poleLE (eisValueAt_iff_eisPoleLE.1 hv).1
  have e' : ∀ s ∈ ball s₀ r, ∀ g, eisCont V Φ s g = H s g := fun s hs g => by
    rcases eq_or_ne s s₀ with rfl | h0
    · refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] s)
        ((hv.2 g).analyticAt_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with z h1 h2
      rw [e z h2 h1, pow_zero, one_mul]; rfl
    · rw [e s hs h0, pow_zero, one_mul]
  exact ⟨r, hr, fun g => (hd g).congr fun s hs => e' s hs g, hc.congr fun x hx => e' _ hx.1 _, C, N,
    fun s hs g => e' s hs g ▸ hb s hs g⟩

section Consequences

variable (hP : Published.DoublingMethod) (h0 : 0 < V.rank) {a : GL (Fin V.rank) (AE D)} (ha : IsMaj V a)
  (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)) {μ : (AE D)ˣ →* Circle} {b : ℕ} (hμ : IsHeckeChar D μ)
  (hb : ResEta D μ b) {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s₁)
include hP h0 ha hI hμ hb hφ

end Consequences

end GlobalTheory.Eis

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)
open scoped TensorProduct NNReal Classical

namespace GlobalTheory.TruncKer

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def subFlag {V : HSpace E} (𝔉 : IsoFlag V) (J : Finset (Fin 𝔉.k)) : IsoFlag V where
  k := J.card
  X i := 𝔉.X (Fin.cases (motive := fun _ => Fin (𝔉.k + 1)) 0 (fun i => (J.orderEmbOfFin rfl i).succ) i)
  zero := 𝔉.zero
  strictMono := 𝔉.strictMono.comp fun a b h => by
    induction b using Fin.cases with
    | zero => exact absurd h (Fin.not_lt_zero _)
    | succ b =>
      induction a using Fin.cases with
      | zero => exact Fin.succ_pos _
      | succ a => exact Fin.succ_lt_succ_iff.2 ((J.orderEmbOfFin rfl).strictMono (Fin.succ_lt_succ_iff.1 h))
  iso := 𝔉.le_perp _ _

structure WittFrame (V : HSpace E) where

  e : Fin (wittIndex V) → V.V

  f : Fin (wittIndex V) → V.V
  ee : ∀ i j, V.hD (e i) (e j) = 0
  ff : ∀ i j, V.hD (f i) (f j) = 0
  ef : ∀ i j, V.hD (e i) (f j) = if i = j then 1 else 0

namespace WittFrame

variable {V : HSpace E} (Φ : WittFrame V)

theorem linearIndependent_e : LinearIndependent E Φ.e :=
  LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun j => V.hT (Φ.f j))
    (fun j i h => (Φ.ef i j).trans (if_neg h.symm)) fun i => (Φ.ef i i).trans (if_pos rfl)

def flag0 : IsoFlag V := .ofVectors Φ.e Φ.linearIndependent_e Φ.ee

def stdFlag (J : Finset (Fin (wittIndex V))) : IsoFlag V := subFlag Φ.flag0 J

def sub (u : SV (wittIndex V)) : Submodule E V.V := Submodule.span E (Φ.e '' {i | u i = 1} ∪ Φ.f '' {i | u i = -1})

variable (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

def levi (P : Finset (SV (wittIndex V))) : Subgroup (HA R hc.sig V.gram) :=
  ⨅ u ∈ P, parab hc V R (Φ.sub u) ⊓ parab hc V R (Φ.sub (-u))

def coef (i : Fin (wittIndex V)) : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hLin hc.sig V.gram R y (coordR V R (Φ.f i))
  map_add' y y' := hLin_add_left _ _ _ y y' _
  map_smul' c y := hLin_smul_left _ _ _ c y _

theorem coef_coordR (i : Fin (wittIndex V)) (x : V.V) : Φ.coef hc R i (coordR V R x) = inclR R (V.hD x (Φ.f i)) := by
  change hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)
  rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hR, Formalism.UG.hform, coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig, TensorProduct.tmul_sum, starRingEnd_apply]

theorem coef_eq_zero (i : Fin (wittIndex V)) {y : Fin V.rank → R ⊗[F] E}
    (hy : y ∈ extSub (F := F) V R (Φ.flag0.X i.castSucc)) : Φ.coef hc R i y = 0 := by
  refine (Submodule.span_le (p := LinearMap.ker (Φ.coef hc R i))).2 ?_ hy
  rintro _ ⟨x, hx, rfl⟩
  have : V.hT (Φ.f i) x = 0 := (Submodule.span_le (p := LinearMap.ker (V.hT (Φ.f i)))).2 (by
    rintro _ ⟨j, hj, rfl⟩
    exact (Φ.ef j i).trans (if_neg (Fin.ne_of_val_ne (ne_of_lt hj)))) hx
  exact (Φ.coef_coordR hc R i x).trans (by rw [HSpace.hD, this, map_zero])

theorem sub_coef_mem (i : Fin (wittIndex V)) {y : Fin V.rank → R ⊗[F] E}
    (hy : y ∈ extSub (F := F) V R (Φ.flag0.X i.succ)) :
    y - Φ.coef hc R i y • coordR V R (Φ.e i) ∈ extSub (F := F) V R (Φ.flag0.X i.castSucc) := by
  have h1 : ∀ x ∈ Φ.flag0.X i.succ, x - V.hT (Φ.f i) x • Φ.e i ∈ Φ.flag0.X i.castSucc := fun x hx => by
    have := (Submodule.span_le (p := (Φ.flag0.X i.castSucc).comap (LinearMap.id - (V.hT (Φ.f i)).smulRight (Φ.e i)))).2 (by
      rintro _ ⟨j, hj, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
      rw [show V.hT (Φ.f i) (Φ.e j) = _ from Φ.ef j i]
      split_ifs with e
      · rw [e, one_smul, sub_self]; exact zero_mem _
      · rw [zero_smul, sub_zero]
        exact Submodule.subset_span ⟨j, lt_of_le_of_ne (Nat.lt_succ_iff.1 hj) (Fin.val_ne_of_ne e), rfl⟩) hx
    simpa using this
  suffices h : extSub (F := F) V R (Φ.flag0.X i.succ) ≤ (extSub (F := F) V R (Φ.flag0.X i.castSucc)).comap
    (LinearMap.id - (Φ.coef hc R i).smulRight (coordR V R (Φ.e i))) by simpa using h hy
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have := h1 x hx
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
  rw [coef_coordR]
  convert coordR_mem (F := F) V R this using 1
  funext a; simp [coordR, HSpace.hD]

def chi (i : Fin (wittIndex V)) : Φ.flag0.par hc R →* R ⊗[F] E where
  toFun p := Φ.coef hc R i (act hc V p.1 (coordR V R (Φ.e i)))
  map_one' := by rw [OneMemClass.coe_one, IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one, coef_coordR, Φ.ef, if_pos rfl, map_one]
  map_mul' p q := by
    have he : coordR (F := F) V R (Φ.e i) ∈ extSub (F := F) V R (Φ.flag0.X i.succ) :=
      coordR_mem V R (Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)
    have h1 := Φ.coef_eq_zero hc R i (mem_parab_iff_maps.1 (IsoFlag.mem_par.1 p.2 i.castSucc) _
      (Φ.sub_coef_mem hc R i (mem_parab_iff_maps.1 (IsoFlag.mem_par.1 q.2 i.succ) _ he)))
    rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_sub, map_sub, sub_eq_zero, act, act, act, Matrix.mulVec_smul, map_smul, smul_eq_mul] at h1
    rw [MulMemClass.coe_mul, IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, mul_comm]
    exact h1

def IsWeylRep (π : Equiv.Perm (Fin (wittIndex V))) (ε : Fin (wittIndex V) → SignTypeˣ) (w : GRat hc.sig V.gram) : Prop :=
  ∀ u, ∀ x ∈ Φ.sub (invSV π ε u), ratAct hc V w x ∈ Φ.sub u

def IsGood (L : Submodule (𝓞 E) (Fin V.rank → E)) (a : GL (Fin V.rank) (AF F ⊗[F] E)) : Prop :=
  Submodule.IsLattice E L ∧ (∀ v, IsSelfDualAt hc.sig V.gram L v) ∧
  (∀ i, V.frame.equivFun (Φ.e i) ∈ L ∧ V.frame.equivFun (Φ.f i) ∈ L) ∧ IsMajorantFrame hc.sig V.gram a ∧
  ∀ (w : InfinitePlace F) (i : Fin (wittIndex V)),
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ hc.sig) (Formalism.UG.bc (compInf F E w) a⁻¹).1 * (Formalism.UG.bc (compInf F E w) a⁻¹).1) *ᵥ
      coordR V w.Completion (Φ.e i) = JR w.Completion V.gram *ᵥ coordR V w.Completion (Φ.f i)

end WittFrame

def IsSSPart {n : ℕ} (γ s : Matrix (Fin n) (Fin n) E) : Prop :=
  Module.End.IsSemisimple (Matrix.toLin' s) ∧ Commute γ s ∧ IsNilpotent (γ - s)

def IsSSClass {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (𝔬 : Set (GRat σ J)) : Prop :=
  ∃ δ : GRat σ J, Module.End.IsSemisimple (Matrix.toLin' δ.1.1) ∧
    𝔬 = {γ | ∃ s : GRat σ J, IsSSPart γ.1.1 s.1.1 ∧ IsConj δ s}

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (K : Subgroup (GA D V))

abbrev GF (V : HSp D) : Type := GRat D.sp.cm.sig V.gram

abbrev rat (V : HSp D) : GF V →* GA D V := ratEmb D.sp.cm.sig V.gram

def absChi (i : Fin (wittIndex V)) : PA Φ.flag0 →* ℝ≥0 :=
  (Doubling.absE D.host.F D.host.E).comp (Φ.chi D.sp.cm (AF D.host.F) i).toHomUnits

def H0 (x : GA D V) : A0 (wittIndex V) := WithLp.toLp 2 fun i => Real.log (Doubling.iwAbs (absChi Φ i) K x)

def unipMeas (𝔉 : IsoFlag V) : Measure (NA 𝔉) := (GlobalTheory.AutomorphicL2Unitary.quotMeasure (NQ 𝔉) Measure.haar Set.univ)⁻¹ • Measure.haar

def kerP (J : Finset (Fin (wittIndex V))) (𝔬 : Set (GF V)) (f : GA D V → ℂ) (x y : GA D V) : ℂ :=
  ∑' δ : {δ : GF V // δ ∈ 𝔬 ∧ rat V δ ∈ Φ.levi D.sp.cm (AF D.host.F) (stdPar J)},
    ∫ n : NA (Φ.stdFlag J), f (x⁻¹ * rat V δ * n * y) ∂unipMeas (Φ.stdFlag J)

def kT (𝔬 : Set (GF V)) (f : GA D V → ℂ) (T : A0 (wittIndex V)) (x : GA D V) : ℂ :=
  ∑ J : Finset (Fin (wittIndex V)), (-1) ^ J.card * ∑' ξ : Quot ((Φ.stdFlag J).parRat D.sp.cm),
    tauHat (stdPar J) ∅ (H0 Φ K (rat V ξ.out * x) - T) * kerP Φ J 𝔬 f (rat V ξ.out * x) (rat V ξ.out * x)

def Ys (π : Equiv.Perm (Fin (wittIndex V))) (ε : Fin (wittIndex V) → SignTypeˣ) (w : GF V) (x : GA D V)
    (T : A0 (wittIndex V)) : A0 (wittIndex V) := inverseChamberMap π ε (T - H0 Φ K (rat V w * x))

def Yfam (x : GA D V) (T : A0 (wittIndex V)) (Q : Finset (SV (wittIndex V))) : A0 (wittIndex V) :=
  if h : ∃ s : Equiv.Perm (Fin (wittIndex V)) × (Fin (wittIndex V) → SignTypeˣ) × GF V,
      Φ.IsWeylRep D.sp.cm s.1 s.2.1 s.2.2 ∧ Q ⊆ weylPar s.1 s.2.1 then
    pr Q (Ys Φ K h.choose.1 h.choose.2.1 h.choose.2.2 x T) else 0

def weight (𝔞 : Submodule ℝ (A0 (wittIndex V))) (T : A0 (wittIndex V)) (x : GA D V) : ℝ :=
  ∫ H : aMQ 𝔞 ∅, gamM 𝔞 ∅ (Yfam Φ K x T) H

def volA (𝔞 : Submodule ℝ (A0 (wittIndex V))) (I : Subgroup (GA D V)) (dt : Measure I) : ℝ :=
  (GlobalTheory.AutomorphicL2Unitary.quotMeasure ((GQ V).subgroupOf I) dt).real {q | ‖𝔞.starProjection (H0 Φ K (q.out : I))‖ < 1} /
    (volume : Measure (aMQ 𝔞 ∅)).real (Metric.ball 0 1)

def IsMinLevi (γ : GF V) (P : Finset (SV (wittIndex V))) : Prop :=
  IsPar P ∧ rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) P ∧
    ∀ (g : GF V) P', IsPar P' → rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P' → P'.card ≤ P.card

end GlobalTheory.TruncKer

end
end
