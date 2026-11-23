module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle155
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle196
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtSmoothOnProj
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace LevelTowerAlt

theorem exists_join {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'}
    {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
    [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}
    (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)
    (hT' : CoordTie ℤ ξ' fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) (g : X' ⟶ X) (i : Ω →+* Ω')
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ g i) :
    ∃ (K₃ : Type) (_ : Fintype K₃) (J₃ : K₃ → Type) (_ : ∀ k, Fintype (J₃ k)) (y₃ : (Σ k, J₃ k) → Ω') (bk : K → K₃)
      (bx : ∀ k, J k ≃ J₃ (bk k)), Nonempty K₃ ∧ Function.Injective bk ∧ (∀ k x, y₃ ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧
      CoordTie ℤ ξ' fun c' : (k : K₃) → J₃ k => ∏ k, y₃ ⟨k, c' k⟩ := by
  let J₁ : K ⊕ Unit → Type := Sum.elim J fun _ => Unit
  letI : ∀ k, Fintype (J₁ k) := fun k => match k with
    | .inl k => (inferInstance : Fintype (J k))
    | .inr _ => (inferInstance : Fintype Unit)
  let s : (Σ k, J₁ k) → Ω' := fun q => match q with
    | ⟨.inl k, a⟩ => i (y ⟨k, a⟩)
    | ⟨.inr _, _⟩ => 1
  have h1 := GlobalTheory.T.coords_join_blocks X' Ω' ξ' K' J' y' (K ⊕ Unit) J₁ s hT' (by
    rintro (k | k) p
    · obtain ⟨hsp, hreg, -⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' g i hd p
      obtain ⟨c, hc⟩ := hT.cover ⟨g p.1, hsp⟩
      refine ⟨c k, (map_ne_zero i).2 (TiePrimes.ne_of_seg hc.1 k), fun a => ?_⟩
      have := hreg _ (TiePrimes.ratio_mem hc ⟨k, a⟩)
      rw [map_div₀] at this
      exact this
    · refine ⟨(), one_ne_zero, fun a => ?_⟩
      show (1 : Ω') / 1 ∈ _
      rw [div_one]; exact one_mem _)
  let J₃ : K' ⊕ (K ⊕ Unit) → Type := Sum.elim J' J₁
  let y₃ : (Σ k, J₃ k) → Ω' := fun q => match q with
    | ⟨.inl k, a⟩ => y' ⟨k, a⟩
    | ⟨.inr k, a⟩ => s ⟨k, a⟩
  refine ⟨K' ⊕ (K ⊕ Unit), inferInstance, J₃, fun k => match k with
    | .inl k => (inferInstance : Fintype (J' k))
    | .inr k => (inferInstance : Fintype (J₁ k)), y₃, fun k => .inr (.inl k), fun k => Equiv.refl _,
    ⟨.inr (.inr ())⟩, fun a b h => by simpa using h, fun _ _ => rfl, ?_⟩
  have e : (fun c' : (k : K' ⊕ (K ⊕ Unit)) → J₃ k => ∏ k, y₃ ⟨k, c' k⟩) =
      fun c' : (k : K' ⊕ (K ⊕ Unit)) → Sum.elim J' J₁ k =>
        (∏ k, y' ⟨k, c' (Sum.inl k)⟩) * ∏ k, s ⟨k, c' (Sum.inr k)⟩ :=
    funext fun c' => Fintype.prod_sum_type _
  rw [e]; exact h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
  {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω}

@[reducible] def reTie (B : HodgeCpt Y S y) (h : CoordTie ℤ B.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) :
    HodgeCpt Y S y' := { B with tie := h }

theorem flag_zero [∀ k, Fintype (J k)] (B : HodgeCpt Y S y) (d : ℕ) (hc : B.IsCover d) (h0 : D.p + D.q = 0) :
    Nonempty B.Flag := by
  have hrk : ∀ s, labelRk D s = 0 := by
    rintro (τ | τ)
    · show D.p = 0; omega
    · show D.q = 0; omega
  haveI : ∀ s, IsEmpty (Fin (labelRk D s)) := fun s => by rw [hrk s]; infer_instance
  have hV : ∀ s, B.Vgen s = ⊥ := fun s => by
    obtain ⟨U, -, b, hb, -⟩ := B.vb s ⟨_, specializes_rfl⟩ trivial
    refine hb.symm.trans ?_
    rw [Set.range_eq_empty, Submodule.span_empty]
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Y.X Y.t.G B.Ω₀ B.ξ₀
  obtain ⟨j, hj⟩ := GlobalTheory.T.lie_model_pullback_map Y.X B.X B.Ω₀ Ω B.ξ₀ B.ξ B.f B.fn Y.t.G B.t.G B.m.φ Li₀ B.Li M₀ B.M B.fn_over B.m.cart
  obtain ⟨hext, -, -⟩ := GlobalTheory.T.lie_lattice_dominant_compat Y.X B.X B.Ω₀ Ω B.ξ₀ B.ξ B.f B.fn Y.t.G B.t.G B.m.φ Li₀ B.Li M₀ B.M j B.gen₀
    B.tie.gen B.fn_over B.m.cart Y.t.semi.smooth hj
  refine ⟨{ b := fun _ => isEmptyElim, sub := fun s p _ => ?_, Li₀ := Li₀, M₀ := M₀, j := j, j_pt := hj,
            V₀ := fun _ => ⊥, V₀_mem := fun s e => ?_, deg := d, generic := ?_ }⟩
  · obtain ⟨U, hU, b, -, hb⟩ := B.vb s p trivial
    exact ⟨U, hU, b, fun _ => by rw [Subsingleton.elim b isEmptyElim], hb⟩
  · rw [hV, Submodule.mem_bot, Submodule.mem_bot]
    refine ⟨fun h => by rw [h, map_zero], fun h => by_contra fun hne => ?_⟩
    have := hext.2 1 (fun _ => e) (linearIndependent_unique_iff.2 hne)
    exact this.ne_zero 0 h
  · letI := B.fn.toAlgebra
    refine ⟨fun _ => isEmptyElim, fun _ => 0, fun s => ⟨linearIndependent_empty_type, ?_⟩, hext.1,
      fun _ => linearIndependent_empty_type, fun _ => linearIndependent_empty_type, fun _ => isEmptyElim,
      fun _ => isEmptyElim, fun s i => congrArg (fun b => flagStep Ω b i) (Subsingleton.elim _ _), ?_, hc.1, ?_⟩
    · rw [Set.range_eq_empty, Submodule.span_empty]
    · haveI : IsEmpty (Σ σ : CMType H ⊕ CMType H,
          {lk : Fin (labelRk D σ) × Fin (labelRk D σ) // lk.2 < lk.1}) := ⟨fun q => isEmptyElim q.2.1.1⟩
      exact algebraicIndependent_empty_type
    · haveI : IsEmpty (Σ σ : CMType H ⊕ CMType H, Fin (labelRk D σ) × Fin (labelRk D σ)) :=
        ⟨fun q => isEmptyElim q.2.1⟩
      rw [Set.range_eq_empty, IntermediateField.adjoin_empty, IntermediateField.finrank_bot']
      exact hc.2

end LevelTowerAlt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

section

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_conjVec (z : (Σ k, J k) → ℂ) (f : MRing J) :
    MvPolynomial.eval (conjVec z) (MvPolynomial.map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, conjVec]

theorem contDiff_conjVec : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, J k) → ℂ => conjVec z) :=
  contDiff_pi.2 fun i => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) i)

theorem conjVec_ne {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ∀ k, ∃ i, conjVec z ⟨k, i⟩ ≠ 0 :=
  fun k => (hz k).imp fun _ hi => (map_ne_zero _).2 hi

noncomputable def symmLine (Z : HermLine J) : HermLine J where
  a := Z.a
  h z := Real.sqrt (Z.h z * Z.h (conjVec z))
  pos z hz := Real.sqrt_pos.2 (mul_pos (Z.pos z hz) (Z.pos _ (conjVec_ne hz)))
  smul c z hc := by
    have h1 : conjVec (fun p : Σ k, J k => c p.1 * z p) =
        fun p : Σ k, J k => (fun k => starRingEnd ℂ (c k)) p.1 * conjVec z p := by
      funext p
      simp [conjVec]
    have h2 := Z.smul (fun k => starRingEnd ℂ (c k)) (conjVec z) fun k => (map_ne_zero _).2 (hc k)
    have hP := prod_norm_zpow_pos hc Z.a
    rw [h1, h2, Z.smul c z hc]
    simp only [Complex.norm_conj]
    rw [_root_.mul_mul_mul_comm, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hP.le]

theorem symmLine_smooth {Z : HermLine J} (hZ : IsSmoothHerm Z) : IsSmoothHerm (symmLine Z) :=
  ContDiffOn.sqrt (ContDiffOn.mul hZ (ContDiffOn.comp hZ contDiff_conjVec.contDiffOn fun _ hz => conjVec_ne hz))
    fun z hz => (mul_pos (Z.pos z hz) (Z.pos _ (conjVec_ne hz))).ne'

theorem symmLine_conj (Z : HermLine J) : IsConjInvariantH (symmLine Z) := by
  intro z
  show Real.sqrt (Z.h (conjVec z) * Z.h (conjVec (conjVec z))) = Real.sqrt (Z.h z * Z.h (conjVec z))
  rw [SncPiece.conj_conj, mul_comm]

end

theorem vertical_factor_smooth_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∀ p ∈ D.S, (∃ A : HermLine J, A.a = D.vdeg p ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z) ∧ ∀ a, ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ G : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, Real.log (D.vertFactor p ((D.chart a).γ t')) = (G t').re := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D p hp
  have hpos := VertFactorPos.proof II Ψ K J Ω W D p hp
  have hsm := VertFactorSmooth.proof VertFactorPos.proof II Ψ K J Ω W D p hp
  constructor
  · obtain ⟨Z, hZa, hZs, hZ⟩ := HermExtend.proof K J (mCoordIdeal D.y) (D.vdeg p) (D.vertFactor p) D.arith.2.1.2.1
      hpos hsm.1 hsm.2
    refine ⟨symmLine Z, hZa, symmLine_smooth hZs, symmLine_conj Z, fun z hz => ?_⟩
    have hconj : D.vertFactor p (conjVec z) = D.vertFactor p z := by
      obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp hz
      rw [VertFactorSmooth.vertFactor_eq D hp (SncPiece.conj_mem hz) hG hH hdeg hrel
          (by rw [eval_conjVec]; exact (map_ne_zero _).2 hHz),
        VertFactorSmooth.vertFactor_eq D hp hz hG hH hdeg hrel hHz, eval_conjVec, eval_conjVec, ← map_div₀,
        Complex.norm_conj]
    show Real.sqrt (Z.h z * Z.h (conjVec z)) = _
    rw [hZ z hz, hZ _ (SncPiece.conj_mem hz), hconj, Real.sqrt_mul_self (hpos z hz).le]
  · intro a t ht
    have hz := (D.chart a).mem t ht
    obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp hz
    have hγ := (D.chart a).analytic t ht
    have hev : ∀ f : MRing J, AnalyticAt ℂ
        (fun t' => MvPolynomial.eval ((D.chart a).γ t') (MvPolynomial.map (Int.castRingHom ℂ) f)) t := fun f =>
      AnalyticAt.comp (g := fun z => MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f))
        (AnalyticOnNhd.eval_mvPolynomial _ _ (Set.mem_univ _)) hγ
    have h0 := hpos _ hz
    rw [VertFactorSmooth.vertFactor_eq D hp hz hG hH hdeg hrel hHz] at h0
    obtain ⟨L, hL, hLe⟩ := exists_log_re ((hev G).div (hev H) hHz) (norm_pos_iff.1 h0)
    refine ⟨L, hL, ?_⟩
    filter_upwards [hLe, (hev H).continuousAt.eventually_ne hHz, Metric.isOpen_ball.mem_nhds ht] with t' h1 h2 h3
    rw [VertFactorSmooth.vertFactor_eq D hp ((D.chart a).mem t' h3) hG hH hdeg hrel h2]
    exact h1

end LevelTowerAlt
end

section

open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.AnForm.A (coordDiv)

namespace LevelTowerAlt

variable {n : ℕ}

theorem frequently_ne (c y : Fin n → ℂ) : ∃ᶠ y' in 𝓝 y, ∀ k, y' k ≠ c k := by
  have h : Dense (Set.pi Set.univ fun k : Fin n => ({c k}ᶜ : Set ℂ)) :=
    dense_pi Set.univ fun k _ => dense_compl_singleton (c k)
  exact (mem_closure_iff_frequently.1 (h y)).mono fun y' hy' k => hy' k (Set.mem_univ k)

theorem eq_of_eventually_ne {β : Type*} [TopologicalSpace β] [T2Space β] {f g : (Fin n → ℂ) → β} (c : Fin n → ℂ)
    {y : Fin n → ℂ} (hf : ContinuousAt f y) (hg : ContinuousAt g y)
    (h : ∀ᶠ y' in 𝓝 y, (∀ k, y' k ≠ c k) → f y' = g y') : f y = g y :=
  tendsto_nhds_unique_of_frequently_eq hf hg (((frequently_ne c y).and_eventually h).mono fun _ h' => h'.2 h'.1)

theorem exists_div_coord {f : (Fin n → ℂ) → ℂ} {y₀ : Fin n → ℂ} (hf : AnalyticAt ℂ f y₀) (S : Finset (Fin n))
    (hz : ∀ᶠ y in 𝓝 y₀, y ∈ coordDiv S → f y = 0) :
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u y₀ ∧ ∀ᶠ y in 𝓝 y₀, f y = u y * ∏ i ∈ S, y i := by
  classical
  have hne : ∀ᶠ y in 𝓝 y₀, ∀ i, y₀ i ≠ 0 → y i ≠ 0 := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases h : y₀ i = 0
    · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
    · exact ((continuous_apply i).continuousAt.eventually_ne h).mono fun _ h' _ => h'
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hf.eventually_analyticAt.and (hz.and hne))
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  let A : (Fin n → ℂ) → Fin n → ℂ := fun z => y₀ + (r : ℂ) • z
  have hAd : Differentiable ℂ A := (differentiable_const _).add (differentiable_id.const_smul (r : ℂ))
  have hA : ∀ z ∈ ball (0 : Fin n → ℂ) 1, A z ∈ ball y₀ r := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    nlinarith
  have hkey : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i, (y₀ i = 0 → z i ≠ 0) → A z i ≠ 0 := by
    intro z hz i hi
    by_cases h : y₀ i = 0
    · show y₀ i + (r : ℂ) * z i ≠ 0
      rw [h, zero_add]
      exact mul_ne_zero hr' (hi h)
    · exact (hb _ (hA z hz)).2.2 i h
  have hAa : ∀ z, AnalyticAt ℂ A z := fun z => by
    have h1 : AnalyticAt ℂ ((fun _ : Fin n → ℂ => (r : ℂ)) • id) z := analyticAt_const.smul analyticAt_id
    exact analyticAt_const.add h1
  have hpd : ∀ z, AnalyticAt ℂ (fun z => ∏ i ∈ S, A z i) z := fun z =>
    Finset.analyticAt_fun_prod (𝕜 := ℂ) S (f := fun i z => A z i) fun i _ => analyticAt_pi_iff.1 (hAa z) i
  obtain ⟨G, hG, hGe⟩ := GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices.proof n
    (fun z => f (A z) / ∏ i ∈ S, A z i)
    (fun z hz => (AnalyticAt.fun_div (f := fun z => f (A z)) (g := fun z => ∏ i ∈ S, A z i)
      (AnalyticAt.comp (g := f) (f := A) (hb _ (hA z hz.1)).1 (hAa z)) (hpd z)
      (Finset.prod_ne_zero_iff.2 fun i _ => hkey z hz.1 i fun _ => hz.2 i)).differentiableAt.differentiableWithinAt)
    (by
      intro z hz i hi
      have h0 : Function.update z i 0 ∈ ball (0 : Fin n → ℂ) 1 := by
        rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos] at hz ⊢
        intro k
        by_cases hk : k = i
        · subst hk
          simp
        · rw [Function.update_of_ne hk]
          exact hz k
      have hud : DifferentiableAt ℂ (Function.update z i) (0 : ℂ) := (hasFDerivAt_update z (0 : ℂ)).differentiableAt
      have hφ : DifferentiableAt ℂ (fun x : ℂ => f (A (Function.update z i x))) 0 :=
        DifferentiableAt.comp (g := fun w => f (A w)) 0
          ((hb _ (hA _ h0)).1.differentiableAt.comp _ (hAd _)) hud
      by_cases hc : i ∈ S ∧ y₀ i = 0
      · have hφ0 : f (A (Function.update z i 0)) = 0 :=
          (hb _ (hA _ h0)).2.1 ⟨i, hc.1, by simp [A, hc.2]⟩
        refine ⟨_, ((hasDerivAt_iff_tendsto_slope.1 hφ.hasDerivAt).div_const
          ((r : ℂ) * ∏ k ∈ S.erase i, A z k)).congr fun x => ?_⟩
        have h1 : ∏ k ∈ S.erase i, A (Function.update z i x) k = ∏ k ∈ S.erase i, A z k :=
          Finset.prod_congr rfl fun k hk => by
            simp only [A, Pi.add_apply, Pi.smul_apply, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
        have h2 : A (Function.update z i x) i = r * x := by simp [A, hc.2]
        rw [← Finset.mul_prod_erase S _ hc.1, h1, h2, slope_def_field, hφ0, sub_zero, sub_zero, div_div]
        congr 1
        ring
      · refine ⟨_, tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto
          (hφ.continuousAt.div ((hpd _).continuousAt.comp hud.continuousAt) ?_))⟩
        refine Finset.prod_ne_zero_iff.2 fun k hk => hkey _ h0 k fun h => ?_
        have hki : k ≠ i := fun e => hc ⟨e ▸ hk, e ▸ h⟩
        rw [Function.update_of_ne hki]
        exact hi k hki)
  let B : (Fin n → ℂ) → Fin n → ℂ := fun y => (r : ℂ)⁻¹ • (y - y₀)
  have hBa : ∀ y, AnalyticAt ℂ B y := fun y => by
    have h1 : AnalyticAt ℂ ((fun _ : Fin n → ℂ => (r : ℂ)⁻¹) • (id - fun _ : Fin n → ℂ => y₀)) y :=
      analyticAt_const.smul (analyticAt_id.sub analyticAt_const)
    exact h1
  have hAB : ∀ y, A (B y) = y := fun y => by
    simp only [A, B, smul_smul, mul_inv_cancel₀ hr', one_smul, add_sub_cancel]
  have hB : ∀ y ∈ ball y₀ r, B y ∈ ball (0 : Fin n → ℂ) 1 := by
    intro y hy
    rw [mem_ball_iff_norm] at hy
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le, inv_mul_lt_iff₀ hr,
      mul_one]
    exact hy
  have hu : ∀ y ∈ ball y₀ r, AnalyticAt ℂ (fun y => G (B y)) y := fun y hy =>
    AnalyticAt.comp (g := G) (f := B) (hG _ (hB y hy)) (hBa y)
  refine ⟨fun y => G (B y), hu _ (mem_ball_self hr), ?_⟩
  filter_upwards [ball_mem_nhds y₀ hr] with y hy
  refine eq_of_eventually_ne (f := f) (g := fun y => G (B y) * ∏ i ∈ S, y i) y₀ (hb y hy).1.continuousAt
    ((hu y hy).continuousAt.mul (continuous_finsetProd _ fun i _ => continuous_apply i).continuousAt) ?_
  filter_upwards [isOpen_ball.mem_nhds hy] with y' hy' hne'
  have h1 : ∀ i, B y' i ≠ 0 := fun i => mul_ne_zero (inv_ne_zero hr') (sub_ne_zero.2 (hne' i))
  have h2 : ∏ i ∈ S, y' i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => by
    have := hkey _ (hB y' hy') i fun _ => h1 i
    rwa [hAB] at this
  rw [hGe _ (hB y' hy') h1, hAB, div_mul_cancel₀ _ h2]

theorem prod_eq_zero_iff_coordDiv (S : Finset (Fin n)) (y : Fin n → ℂ) : ∏ i ∈ S, y i = 0 ↔ y ∈ coordDiv S :=
  Finset.prod_eq_zero_iff

theorem sum_log_eq (S : Finset (Fin n)) {y : Fin n → ℂ} (hy : y ∉ coordDiv S) :
    ∑ i ∈ S, Real.log (‖y i‖ ^ 2)⁻¹ = -2 * Real.log ‖∏ i ∈ S, y i‖ := by
  rw [norm_prod, Real.log_prod fun i hi => norm_ne_zero_iff.2 fun h => hy ⟨i, hi, h⟩, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_inv, Real.log_pow]
  push_cast
  ring

theorem exists_smooth_log_diff {Φ : (Fin n → ℂ) → Fin n → ℂ} {y₀ : Fin n → ℂ} (hΦ : AnalyticAt ℂ Φ y₀)
    {U : Set (Fin n → ℂ)} (hU : U ∈ 𝓝 y₀) (hinj : Set.InjOn Φ U) {S S' : Finset (Fin n)}
    (h : ∀ᶠ y in 𝓝 y₀, y ∈ coordDiv S ↔ Φ y ∈ coordDiv S') :
    ∃ q : (Fin n → ℂ) → ℝ, ContDiffAt ℝ ∞ q y₀ ∧ ∀ᶠ y in 𝓝 y₀, y ∉ coordDiv S →
      ∑ i ∈ S', Real.log (‖Φ y i‖ ^ 2)⁻¹ = ∑ i ∈ S, Real.log (‖y i‖ ^ 2)⁻¹ + q y := by
  obtain ⟨g, hga, hg0, hgr, hgl, -⟩ := exists_local_inverse hΦ hU hinj
  obtain ⟨u, hu, hue⟩ := exists_div_coord (f := fun y => ∏ i ∈ S', Φ y i)
    (Finset.analyticAt_fun_prod _ fun i _ => analyticAt_pi_iff.1 hΦ i) S
    (h.mono fun y hy hS => (prod_eq_zero_iff_coordDiv _ _).2 (hy.1 hS))
  have hgt : Tendsto g (𝓝 (Φ y₀)) (𝓝 y₀) := by
    have := hga.continuousAt.tendsto
    rwa [hg0] at this
  obtain ⟨v, hv, hve⟩ := exists_div_coord (f := fun x => ∏ i ∈ S, g x i)
    (Finset.analyticAt_fun_prod _ fun i _ => analyticAt_pi_iff.1 hga i) S'
    (by
      filter_upwards [hgt.eventually h, hgr] with x h1 h2 h3
      rw [h2] at h1
      exact (prod_eq_zero_iff_coordDiv _ _).2 (h1.2 h3))
  have h1 : v (Φ y₀) * u y₀ = 1 := by
    refine eq_of_eventually_ne (f := fun y => v (Φ y) * u y) (g := fun _ => 1) 0
      ((hv.continuousAt.comp hΦ.continuousAt).mul hu.continuousAt) continuousAt_const ?_
    filter_upwards [hue, hΦ.continuousAt.tendsto.eventually hve, hgl] with y e1 e2 e3 hy
    rw [e3, e1, ← mul_assoc] at e2
    have hp : ∏ i ∈ S, y i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hy i
    exact mul_right_cancel₀ hp (by rw [← e2, one_mul])
  have hu0 : u y₀ ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have huR : AnalyticAt ℝ u y₀ := hu.restrictScalars
  refine ⟨fun y => -2 * Real.log ‖u y‖, contDiffAt_const.mul
    ((huR.contDiffAt.norm ℝ hu0).log (norm_ne_zero_iff.2 hu0)), ?_⟩
  filter_upwards [h, hue, hu.continuousAt.eventually_ne hu0] with y e1 e2 e3 hy
  have hp : ∏ i ∈ S, y i ≠ 0 := fun h0 => hy ((prod_eq_zero_iff_coordDiv _ _).1 h0)
  rw [sum_log_eq S' fun h' => hy (e1.2 h'), sum_log_eq S hy, e2, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 e3) (norm_ne_zero_iff.2 hp)]
  ring

theorem exists_smooth_glue {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n)) (E : (Fin n → ℂ) → ℝ)
    (h : ∀ y₀ ∈ U, ∃ q : (Fin n → ℂ) → ℝ, ContDiffAt ℝ ∞ q y₀ ∧ ∀ᶠ y in 𝓝 y₀, y ∉ coordDiv S → E y = q y) :
    ∃ f : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ f U ∧ ∀ y ∈ U, y ∉ coordDiv S → E y = f y := by
  choose! q hq hqe using h
  refine ⟨fun y => q y y, fun y₀ hy₀ => ((hq y₀ hy₀).congr_of_eventuallyEq ?_).contDiffWithinAt,
    fun y hy => (hqe y hy).self_of_nhds⟩
  have hc : ∀ᶠ y in 𝓝 y₀, ContinuousAt (q y₀) y :=
    (((hq y₀ hy₀).of_le (m := 1) (by exact_mod_cast le_top)).eventually (by simp)).mono fun _ h => h.continuousAt
  filter_upwards [hU.mem_nhds hy₀, hc, (hqe y₀ hy₀).eventually_nhds] with y hy h1 h2
  refine eq_of_eventually_ne (f := q y) (g := q y₀) 0 (hq y hy).continuousAt h1 ?_
  filter_upwards [h2, hqe y hy] with y' e1 e2 hy'
  have hn : y' ∉ coordDiv S := fun ⟨i, _, hi⟩ => hy' i hi
  rw [← e1 hn, ← e2 hn]

end LevelTowerAlt
end
