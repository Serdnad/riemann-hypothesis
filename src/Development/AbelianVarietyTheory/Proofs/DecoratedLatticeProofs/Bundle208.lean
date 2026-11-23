module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle187
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle183
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToFourierJacobiHandedFamilyContinuousAutom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle185
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.CosetSymGL

abbrev Cos {G : Type} [Group G] (K : Subgroup G) (g : G) : Type :=
  {c : G ⧸ K // ∃ k ∈ K, c = ((k * g : G) : G ⧸ K)}

theorem card_cos_eq_of_mem {G : Type} [Group G] {K : Subgroup G} {g h a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (e : h = a * g * b) : Nat.card (Cos K h) = Nat.card (Cos K g) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a, K.mul_mem hk ha, ?_⟩
    rw [e, ← mul_assoc, ← mul_assoc, QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, K.mul_mem hk (K.inv_mem ha), ?_⟩
    rw [e, show k * a⁻¹ * (a * g * b) = k * g * b by group, QuotientGroup.mk_mul_of_mem _ hb]

def quotEquiv {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) : G ⧸ K ≃ G ⧸ K :=
  Quotient.congr θ.toEquiv fun a b => by
    change QuotientGroup.leftRel K a b ↔ QuotientGroup.leftRel K (θ a) (θ b)
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← map_inv, ← map_mul, hθ]

theorem quotEquiv_mk {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) (x : G) :
    quotEquiv K θ hθ (x : G ⧸ K) = ((θ x : G) : G ⧸ K) := rfl

theorem card_cos_aut {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) (g : G) :
    Nat.card (Cos K g) = Nat.card (Cos K (θ g)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (quotEquiv K θ hθ) fun c => ?_)
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨θ k, (hθ k).2 hk, by rw [quotEquiv_mk, map_mul]⟩
  · rintro ⟨k, hk, e⟩
    refine ⟨θ.symm k, (hθ _).1 (by simpa using hk), (quotEquiv K θ hθ).injective ?_⟩
    rw [e, quotEquiv_mk, map_mul, MulEquiv.apply_symm_apply]

theorem cosetSym_of_aut {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K)
    (h : ∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g⁻¹ * b) : CosetSym K := fun g => by
  obtain ⟨a, ha, b, hb, e⟩ := h g
  exact (card_cos_aut K θ hθ g).trans (card_cos_eq_of_mem ha hb e)

end GlobalTheory.ChainOnto.CosetSymGL

namespace GlobalTheory.ChainOnto.CosetSymGL


open GlobalTheory.LFun.ConjPlace in
theorem invT_of_symm {L : Type} [Field L] {n : ℕ} (d : GL (Fin n) L)
    (hd : (d : Matrix (Fin n) (Fin n) L)ᵀ = (d : Matrix (Fin n) (Fin n) L)) : invT (RingEquiv.refl L) n d = d⁻¹ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invT_val, RingEquiv.refl_apply, Matrix.coe_units_inv]
  conv_lhs => rw [← hd]
  rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply]

open GlobalTheory.LFun.ConjPlace in
theorem invT_mem_iff {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L) :
    invT (RingEquiv.refl L) n g ∈ Formalism.UG.GLint (Fin n) O ↔ g ∈ Formalism.UG.GLint (Fin n) O :=
  (mem_iff_invT (RingEquiv.refl L) (O := O) (O' := O) (fun _ => Iff.rfl) g).symm


open GlobalTheory.LFun.ConjPlace in
theorem invT_mem_doset (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) : ∃ a ∈ KGL w (n := n), ∃ b ∈ KGL w (n := n),
      invT (RingEquiv.refl _) n g = a * g⁻¹ * b := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := E) w
  have hϖO : ϖ ∈ Formalism.UG.Ov E w := by
    change Valued.v ϖ ≤ 1
    unfold Formalism.UG.IsUnifV at hϖ
    rw [hϖ]
    exact (WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)
  obtain ⟨ex, -, k₁, hk₁, k₂, hk₂, hg⟩ := Formalism.UG.Final.CartanDecomp E w n ϖ hϖO hϖ g
  set d : GL (Fin n) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hd
  have hdv : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Formalism.UG.diagPow E w ϖ ex := by
    rw [hd, Units.val_mul, Units.val_mul, hg, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc,
      Units.mul_inv, mul_one]
  have hsym : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [hdv, Formalism.UG.diagPow, Matrix.diagonal_transpose]
  have hgd : g = k₁ * d * k₂ := by rw [hd]; group
  set θ := invT (RingEquiv.refl (w.adicCompletion E)) n
  refine ⟨θ k₁ * k₂, (KGL w (n := n)).mul_mem ((invT_mem_iff _ _).2 hk₁) hk₂,
    k₁ * θ k₂, (KGL w (n := n)).mul_mem hk₁ ((invT_mem_iff _ _).2 hk₂), ?_⟩
  have hθd : θ d = d⁻¹ := invT_of_symm d hsym
  rw [hgd, map_mul, map_mul, hθd, hd]
  group

end GlobalTheory.ChainOnto.CosetSymGL


open GlobalTheory.ChainOnto.CosetSymGL GlobalTheory.LFun.ConjPlace in
theorem GlobalTheory.ChainOnto.kGL_commensurated_cosetSym : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), IsCommensurated (KGL w (n := n)) ∧ CosetSym (KGL w (n := n)) := fun E _ _ w n =>
  ⟨Formalism.UG.Final.GLintComm E w n, cosetSym_of_aut _ (invT (RingEquiv.refl _) n) (fun x => invT_mem_iff _ x)
    (invT_mem_doset E w n)⟩
end
end

section

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont.Shift

open Set Metric

theorem holValueAt_of_continuousAt {h : ℂ → ℂ} (a : GlobalTheory.Cont.Continues h) {t : ℂ}
    (b : ContinuousAt (GlobalTheory.Cont.cont h) t) : GlobalTheory.Cont.HolValueAt h t (GlobalTheory.Cont.cont h t) := by
  obtain ⟨H₀, hH⟩ := a
  have ha := hH.isExtAt (mem_univ t)
  exact ha.holValueAt_iff.2 ((b.tendsto.mono_left nhdsWithin_le_nhds).congr' ha.cont_eventuallyEq)

theorem differentiable_npow_sub {c : ℝ≥0} (hc : 0 < c) (s₁ : ℂ) : Differentiable ℂ fun s => npow c (s₁ - s) :=
  (GlobalTheory.Eis.differentiable_npow hc).comp (differentiable_const _ |>.sub differentiable_id)

theorem contMod_shift (D : D7) (T : HSp D) (e e' : ℂ → GA D T → ℂ) (x : GA D T) (c : ℝ≥0) (s₁ s₂ : ℂ) (hc : 0 < c)
    (he : ∀ s g, e' s g = npow c (s₁ - s) * e (s + s₂) (g * x)) (hm : ContMod T e) : ContMod T e' := by
  have hd := differentiable_npow_sub hc s₁
  have hfun : ∀ g, (fun z => e' z g) = fun z => npow c (s₁ - z) * (fun w => e w (g * x)) (z + s₂) :=
    fun g => funext fun z => he z g
  refine ⟨fun g => ?_, fun s₀ => ?_⟩
  · obtain ⟨H₀, hH⟩ := hm.1 (g * x)
    rw [GlobalTheory.Cont.isMerExt_univ] at hH
    obtain ⟨σ, hσ⟩ := hH.2
    refine ⟨fun z => npow c (s₁ - z) * H₀ (z + s₂), GlobalTheory.Cont.isMerExt_univ.2 ⟨fun z => ?_, σ - s₂.re, fun z hz => ?_⟩⟩
    · exact (hd.analyticAt z).meromorphicAt.fun_mul
        ((hH.1 (z + s₂)).comp_analyticAt (g := (· + s₂)) (by fun_prop))
    · simp only [he]
      congr 1
      exact hσ (by simpa [GlobalTheory.Cont.mem_rightOf] using sub_lt_iff_lt_add.1 hz)
  · obtain ⟨k, r, H, hr, h1, h2, h3, C, N, h4⟩ := hm.2 (s₀ + s₂)
    have hball : ∀ s ∈ ball s₀ r, s + s₂ ∈ ball (s₀ + s₂) r := fun s hs => by
      simpa [mem_ball, dist_eq_norm] using hs

    have hval : ∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ g,
        GlobalTheory.Cont.cont (fun z => e' z g) s = npow c (s₁ - s) * GlobalTheory.Cont.cont (fun z => e z (g * x)) (s + s₂) := by
      intro s hs hne g
      have hne' : s + s₂ ≠ s₀ + s₂ := fun h => hne (add_right_cancel h)
      have hopen : ball (s₀ + s₂) r ∩ {s₀ + s₂}ᶜ ∈ 𝓝 (s + s₂) :=
        (isOpen_ball.inter isOpen_compl_singleton).mem_nhds ⟨hball s hs, hne'⟩
      have hcont : ContinuousAt (GlobalTheory.Cont.cont fun z => e z (g * x)) (s + s₂) := by
        have hq : ContinuousAt (fun t => H t (g * x) / (t - (s₀ + s₂)) ^ k) (s + s₂) :=
          (((h2 (g * x)).continuousOn.continuousAt (isOpen_ball.mem_nhds (hball s hs)))).div
            (by fun_prop) (pow_ne_zero _ (sub_ne_zero.2 hne'))
        refine hq.congr (Filter.eventually_of_mem hopen fun t ht => ?_)
        have := h1 t ht.1 ht.2 (g * x)
        show H t (g * x) / _ = _
        rw [this, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 ht.2))]
      have hv := holValueAt_of_continuousAt (hm.1 (g * x)) hcont
      have hn : GlobalTheory.Cont.HolValueAt (fun z => npow c (s₁ - z)) s (npow c (s₁ - s)) :=
        GlobalTheory.Cont.IsHolExt.holValueAt ⟨GlobalTheory.Cont.isRightDomain_univ, fun z _ => hd.analyticAt z, .refl _⟩ (mem_univ s)
      have hp := hn.mul hv.comp_add
      rw [hfun g]
      exact hp.valueAt.cont_eq
    obtain ⟨B, hB⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn hd.continuous.continuousOn
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB s₀ (mem_closedBall_self hr.le))
    refine ⟨k, r, fun s g => npow c (s₁ - s) * H (s + s₂) (g * x), hr, fun s hs hne g => ?_, fun g => ?_, ?_,
      B * |C| * GlobalTheory.Grow.height T x ^ N, N, fun s hs g => ?_⟩
    · show npow c (s₁ - s) * H (s + s₂) (g * x) = _
      rw [hval s hs hne g, h1 _ (hball s hs) (fun h => hne (add_right_cancel h)) (g * x)]
      rw [show s + s₂ - (s₀ + s₂) = s - s₀ by ring]
      ring
    · refine (hd.differentiableOn).mul ((h2 (g * x)).comp (by fun_prop) fun s hs => hball s hs)
    · refine (hd.continuous.comp continuous_fst).continuousOn.mul ?_
      exact h3.comp (f := fun p : ℂ × GA D T => (p.1 + s₂, p.2 * x)) (by fun_prop)
        fun (p : ℂ × GA D T) (hp : p ∈ ball s₀ r ×ˢ univ) => ⟨hball p.1 hp.1, mem_univ _⟩
    · have hH := h4 _ (hball s hs) (g * x)
      have hn := hB s (ball_subset_closedBall hs)
      have hg := GlobalTheory.Grow.height_mul_le T g x
      have hg0 := (GlobalTheory.Grow.height_pos T g).le
      have hx0 := (GlobalTheory.Grow.height_pos T x).le
      have hgx0 := (GlobalTheory.Grow.height_pos T (g * x)).le
      have e1 : ‖H (s + s₂) (g * x)‖ ≤ |C| * (GlobalTheory.Grow.height T g * GlobalTheory.Grow.height T x) ^ N :=
        hH.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hgx0 N)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hgx0 hg N) (abs_nonneg C)))
      rw [norm_mul]
      calc ‖npow c (s₁ - s)‖ * ‖H (s + s₂) (g * x)‖ ≤ B * (|C| * (GlobalTheory.Grow.height T g * GlobalTheory.Grow.height T x) ^ N) :=
            mul_le_mul hn e1 (norm_nonneg _) hB0
        _ = B * |C| * GlobalTheory.Grow.height T x ^ N * GlobalTheory.Grow.height T g ^ N := by rw [mul_pow]; ring

end GlobalTheory.EisCont.Shift

end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.exists_common_level_compact_translates_thetaFunction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ K : Set (GA D S), IsCompact K → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ k ∈ K, ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (om (k, 1) f) = om (k, 1) f := by
  first | exact @GlobalTheory.Core.Rk.Level.exists_common_level | exact GlobalTheory.Core.Rk.Level.exists_common_level | (intros; apply GlobalTheory.Core.Rk.Level.exists_common_level <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.petersson_coefficient_bounded_spherical_unramified : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (L : Lat A), IsInfFam θ → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)), ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u₁ par → SphFun A L Sf u₂ → ∀ v ∉ Sf, ∀ x : GA D A, proj D.sp.cm.sig A.gram v x = 1 → IsSphCoef A L v par fun y => rcoef m u₁ u₂ (x * emb D.sp.cm.sig A.gram v y) := by
  first | exact @GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef | exact GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef | (intros; apply GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B) (omh : WRep (dblSp A) B), IsWeilDatumO ψ A B χA χB om → ThetaClause ψ A B χB om omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → CoefClause ψ A B om omh ν 𝓕 := by
  first | exact @GlobalTheory.Core.Rk.coefClause_of_thetaClause | exact GlobalTheory.Core.Rk.coefClause_of_thetaClause | (intros; apply GlobalTheory.Core.Rk.coefClause_of_thetaClause <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.integral_unramifiedOutsideOpenSubset_insert_place : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)) (v : FinPl D), v ∉ Sf → ∀ μ : Measure (Gv A v), μ.IsHaarMeasure → μ (stabLoc D.sp.cm.sig A.gram L v) = 1 → ∀ (S' : Finset (FinPl D)), (∀ u, u ∈ S' ↔ u = v ∨ u ∈ Sf) → ∀ F : GA D A → ℂ, IntegrableOn F (openOff A L S') m → ∫ g in openOff A L S', F g ∂m = ∫ x in openOff A L Sf, (∫ y, F (x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ * emb D.sp.cm.sig A.gram v y) ∂μ) ∂m := by
  first | exact @GlobalTheory.Core.Rk.HaarStep.integral_openOff_insert | exact GlobalTheory.Core.Rk.HaarStep.integral_openOff_insert | (intros; apply GlobalTheory.Core.Rk.HaarStep.integral_openOff_insert <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.sphericalParameterBound_split_place : ∀ D : D7, ParamBoundOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.Core.Rk.BdSplit.paramBound_split | exact GlobalTheory.Core.Rk.BdSplit.paramBound_split | (intros; apply GlobalTheory.Core.Rk.BdSplit.paramBound_split <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.siegelWeilSection_integrable_and_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IntegrableOn (fun w => φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w)) 𝓕 ν ∧ Continuous (swSec A B omh ν 𝓕 φ) := by
  first | exact @GlobalTheory.Core.Rk.IP.swSec_integrable_continuous | exact GlobalTheory.Core.Rk.IP.swSec_integrable_continuous | (intros; apply GlobalTheory.Core.Rk.IP.swSec_integrable_continuous <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B), IsWeilDatumO ψ A B χA χB om → ∃ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh := by
  first | exact @GlobalTheory.Core.Rk.exists_doubled_weilDatum | exact GlobalTheory.Core.Rk.exists_doubled_weilDatum | (intros; apply GlobalTheory.Core.Rk.exists_doubled_weilDatum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw

theorem upVal_of_span_adj : ∀ D : D7, SoftQ D → UpSpanQ D → UpAdjQ D → UpVal D := by
  intro D hSoft hSpan hAdj
  intro hgap c tw htw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' φ v hv
  have hk' : k + 1 ≤ D.R.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := (hSoft c tw htw (k + 1) hk' s' hs').1
  have hl : ∀ (u : s.CC c) (x : s'.CC c), (∀ y, ip' y x = ip (p.io y) u) → ∀ (y : s'.CC c), ∀ w ∈ s'.KF,
      s'.pet (PiLocalization₂.val y w) (p.up φ (PiLocalization₂.val u v)) = ip' y x * ipD (p.It φ w) v := by
    intro u x hx y w hw
    rw [hx y]
    exact (hAdj hgap c tw htw k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)
  have key : ∀ (u : s.CC c) (x : s'.CC c), (∀ y, ip' y x = ip (p.io y) u) → p.up φ (PiLocalization₂.val u v) ≠ 0 →
      x ≠ 0 ∧ ∃ w₁, IsAdjVec p ipD ipD' φ v w₁ ∧ p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₁ := by
    intro u x hx hF
    obtain ⟨hx0, w₁, hw₁, hFx⟩ := GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span (GA D s'.V) (SmT s'.M) (s'.CC c)
      (s'.CC c).subtype s'.KF ipD' ip' s'.pet hM'.hermD hM'.posD hM'.herm hM'.pos
      (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v)
      (hSpan hgap c tw htw k hk s s' hs hs' p hp u φ v hv) (hl u x hx) hF
    have hFx' : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₁ := hFx
    refine ⟨hx0, w₁, ⟨hw₁, fun w hw => ?_⟩, hFx'⟩
    have h1 := hl u x hx x w hw
    rw [hFx'] at h1
    have h2 := (hM'.schur x x w w₁).symm.trans h1
    have hxx : ip' x x ≠ 0 := fun h => by
      have := hM'.pos x hx0
      rw [h] at this
      simp at this
    exact mul_left_cancel₀ hxx h2
  refine ⟨fun ⟨u, hF⟩ => ?_, fun w₀ hw₀ u x hx => ?_⟩
  · obtain ⟨x, hx, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
    obtain ⟨-, w₁, hw₁, hFx⟩ := key u x hx hF
    refine ⟨w₁, fun h => hF ?_, hw₁⟩
    rw [hFx, h]
    simp
  · by_cases hF : p.up φ (PiLocalization₂.val u v) = 0
    · have h1 := hl u x hx x w₀ hw₀.1
      rw [hF, ← hw₀.2 w₀ hw₀.1] at h1
      have h0 : s'.pet (PiLocalization₂.val x w₀) (0 : GA D s'.V → ℂ) = 0 := by
        simp [PiLocalization₂.pet, Lift.pet]
      rw [h0] at h1
      rw [hF]
      rcases mul_eq_zero.mp h1.symm with h | h
      · have hx0 : x = 0 := by
          by_contra hne
          have := hM'.pos x hne
          rw [h] at this
          simp at this
        subst hx0
        first | rfl | simp [PiLocalization₂.val]
      · have hw0 : w₀ = 0 := by
          by_contra hne
          have := hM'.posD w₀ hne
          rw [h] at this
          simp at this
        subst hw0
        simp
    · obtain ⟨-, w₁, hw₁, hFx⟩ := key u x hx hF
      have hd : w₁ = w₀ := by
        by_contra hne
        have hdK : w₁ - w₀ ∈ s'.KF := s'.KF.sub_mem hw₁.1 hw₀.1
        have hz : ipD' (w₁ - w₀) (w₁ - w₀) = 0 := by
          rw [map_sub, hw₁.2 _ hdK, hw₀.2 _ hdK, sub_self]
        have := hM'.posD _ (sub_ne_zero.mpr hne)
        rw [hz] at this
        simp at this
      rw [hFx, hd]

end GlobalTheory.ChainTw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.besselToFourierJacobi_handedFamily_continuous_automorphic : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ') (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ), IsContAut B.A φ → IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsQuasiFam ψ J.W₀ L' (handBF s l φ Ξ) := by
  first | exact @GlobalTheory.HandFam.handBF_isQuasiFam | exact GlobalTheory.HandFam.handBF_isQuasiFam | (intros; apply GlobalTheory.HandFam.handBF_isQuasiFam <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.besselDoubleStepUnfolding_of_unfoldings_and_link : ∀ D : D7, UnfBF D → UnfFB D → LinkLaw D → HandFBLaw D → FlatLaw D → DoubleStep D := by
  first | exact @GlobalTheory.Unf.doubleStep_of_laws | exact GlobalTheory.Unf.doubleStep_of_laws | (intros; apply GlobalTheory.Unf.doubleStep_of_laws <;> assumption)
end
