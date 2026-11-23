module

public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.UnipUGood
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle005
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle012
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle004
import Development.WeilBound.ThetaLifts.LatticeBasics.FarRight
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle013
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.WeilBound.ThetaLifts.SchwartzMoments.EqZeroOfMoments
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKEnd (unipU IsCusp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem IsRapid.bound {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (h1 : ∀ h : UA σ Y.J, 1 ≤ ht h) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (T : UA σ Y.J → ℂ) (A : ℝ), 0 ≤ A → (∀ γ ∈ ratU σ Y.J, ∀ h, T (γ * h) = T h) →
      (∀ h, ‖T h‖ ≤ A * (ht h : ℝ) ^ N) → ∀ h, ‖T h‖ * ‖φ h‖ ≤ A * M := by
  obtain ⟨C, hC⟩ := hφ.2.2 N
  refine ⟨2 ^ N * max C 0, by positivity, fun T A hA hi hb h => ?_⟩
  have q1 : 1 ≤ qht h := le_ciInf fun γ => h1 _
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (f := fun γ : ratU σ Y.J => ht (γ.1 * h)) (b := 2 * qht h)
    (lt_two_mul_self (zero_lt_one.trans_le q1))
  calc _ ≤ A * (2 * qht h : ℝ) ^ N * ‖φ h‖ := mul_le_mul_of_nonneg_right (hi γ γ.2 h ▸ (hb _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) (by exact_mod_cast hγ.le) N) hA)) (norm_nonneg _)
    _ = A * (2 ^ N * (‖φ h‖ * (qht h : ℝ) ^ N)) := by ring
    _ ≤ _ := by gcongr; exact (hC h).trans (le_max_left _ _)

variable {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} {χ : Chr F E} {s₀ : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}

theorem eis_bound (he : ∀ h h', IsEmb h h' (e (h, h'))) {c : ℝ≥0} (h1 : ∀ h h' x, IsEmb (σ := σ) (Y := Y) h h' x → ht2 x ≤ c * (ht h * ht h'))
    (h2 : ∀ h : UA σ Y.J, 1 ≤ ht h) {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (C : ℝ) (N : ℕ) (b : ℝ≥0) :
    ∃ M : ℝ, ∀ Ê : G2 σ Y → ℂ, (∀ c ∈ rat2 σ Y, ∀ x, Ê (c * x) = Ê x) → (∀ x, ‖Ê x‖ ≤ C * (ht2 x : ℝ) ^ N) →
      ∀ h, ht h ≤ b → ∀ h', ‖Ê (e (h, h'))‖ * ‖φ h'‖ ≤ M := by
  obtain ⟨M, -, hM⟩ := hφ.bound h2 N
  refine ⟨max C 0 * (c * b) ^ N * M, fun Ê hi hb h hh => hM (fun x => Ê (e (h, x))) _ (by positivity) (fun γ hγ x => ?_) fun x => ?_⟩
  · rw [← hi _ ((he 1 γ).rat (one_mem _) hγ) (e (h, x)), ← map_mul, Prod.mk_mul_mk, one_mul]
  · refine (hb _).trans ?_
    rw [mul_assoc, ← mul_pow]
    have : ht2 (e (h, x)) ≤ c * b * ht x := (h1 _ _ _ (he h x)).trans (by rw [mul_assoc]; gcongr)
    gcongr
    exacts [le_max_left _ _, by exact_mod_cast this]

theorem sfin {A : Type} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ] : SFinite μ := inferInstance

theorem sfin' {A : Type} [Group A] [TopologicalSpace A] [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A]
    (μ : Measure A) [μ.IsHaarMeasure] : SFinite μ := inferInstance



theorem ct_zero (hO : OffOpen) (hU : PositivityTheory.ThKEnd.Grp.UnipUGood) (hE1 : EisContinues) (hH : HtEmb) {B : Base F E} {r s : ℕ}
    (hB : B.IsGood σ) (hn : 1 ≤ n) (hY : Y.IsSkew σ B r s) (d0 : Y.J.det ≠ 0) [LocallyCompactSpace (UA σ Y.J)]
    [SecondCountableTopology (UA σ Y.J)] [T2Space (UA σ Y.J)] (hb : ∀ Ω : Set (UA σ Y.J), IsCompact Ω → ∃ C : ℝ≥0, ∀ g ∈ Ω, ht g ≤ C)
    (hχ : IsHecke F E χ) (he : ∀ h h', IsEmb h h' (e (h, h'))) (ce : Continuous e) (hS : IsStab2 B K)
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) (ca : Continuous a) (a0 : ∀ x, 0 < a x) (cf : Continuous f)
    (hf : Law χ (s₀ + n / 2) f) {U Ê} (hE : IsEisCont (flat a f s₀) U Ê) {μ : Measure (UA σ Y.J)} {D : Set (UA σ Y.J)}
    (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ Y.J) D μ) (fin : μ D < ⊤) {t₀ : ℝ}
    (hi : ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ) {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (hc : IsCusp Y φ) :
    ∀ s ∈ U, IsCusp Y fun h => ∫ h' in D, Ê s (e (h, h')) * detInv χ h' * φ h' ∂μ := by
  intro s hs V v1 v2 κ 𝓜 k1 k2 h
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨g, -⟩ := hU F E σ hB.cm n Y (.inr hY.skew) d0 V
  haveI := g.sc
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 fin.ne
  haveI : IsFiniteMeasure (κ.restrict 𝓜) := isFiniteMeasure_restrict.2 (g.fin κ 𝓜 k1 k2).2.ne
  haveI : SFinite (μ.restrict D) := sfin _
  haveI : SFinite (κ.restrict 𝓜) := sfin _
  haveI : SFinite μ := sfin' μ
  obtain ⟨c, c1, -, c3⟩ := hH F E σ n Y
  obtain ⟨t₁, half⟩ := hE.half
  have cE : ∀ s ∈ U, Continuous (Ê s) := fun s hs =>
    hE.cont.comp_continuous (f := fun x => (s, x)) (by fun_prop) fun _ => ⟨hs, trivial⟩
  have iv : ∀ s ∈ U, ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := fun s hs γ hγ x =>
    An.ident hE.isOpen hE.conn (hE.hol _) (hE.hol _) (fun s hs => ⟨(half s hs).1,
      (hf.flat ha a0 s).eis_rat hχ (half s hs).2 hγ _⟩) hs
  obtain ⟨Ω, hΩ, cov⟩ := g.cov
  obtain ⟨b, hb'⟩ := hb _ ((hΩ.image continuous_subtype_val).image (continuous_mul_const h))
  let k : ℂ → unipU σ Y V × UA σ Y.J → ℂ := fun s y => Ê s (e (y.1.1 * h, y.2)) * detInv χ y.2 * φ y.2
  have ck : ∀ s ∈ U, Continuous (k s) := fun s hs =>
    (((cE s hs).comp (ce.comp (by fun_prop))).mul ((continuous_detInv hχ).comp continuous_snd)).mul (hφ.1.comp continuous_snd)
  have bk : ∀ s ∈ U, ∃ ε > 0, ∃ M, ∀ s' ∈ U ∩ Metric.ball s ε, ∀ y, ‖k s' y‖ ≤ M := fun s hs => by
    obtain ⟨ε, C, N, h0, hg⟩ := hE.grow s hs
    obtain ⟨M, hM⟩ := eis_bound he c1 c3 hφ C N b
    refine ⟨ε, h0, M, fun s' hs' y => ?_⟩
    obtain ⟨γ, hγ, h1⟩ := cov y.1
    have := hM (Ê s') (iv s' hs'.1) (hg s' hs'.2) _ (hb' _ ⟨_, ⟨_, h1, rfl⟩, rfl⟩) y.2
    rw [show e ((γ * y.1).1 * h, y.2) = e (γ.1, 1) * e (y.1.1 * h, y.2) by simp [← map_mul, mul_assoc],
      iv s' hs'.1 _ ((he _ _).rat hγ (one_mem _))] at this
    simpa only [k, norm_mul, norm_detInv, mul_one] using this
  have ik : ∀ s ∈ U, Integrable (k s) ((κ.restrict 𝓜).prod (μ.restrict D)) := fun s hs => by
    obtain ⟨ε, h0, M, hM⟩ := bk s hs
    exact .of_bound (ck s hs).aestronglyMeasurable M (.of_forall (hM s ⟨hs, Metric.mem_ball_self h0⟩))
  have hol : DifferentiableOn ℂ (fun s => ∫ y, k s y ∂(κ.restrict 𝓜).prod (μ.restrict D)) U := fun s hs => by
    obtain ⟨ε, h0, M, hM⟩ := bk s hs
    have o := hE.isOpen.inter (Metric.isOpen_ball (x := s) (ε := ε))
    exact ((An.diffOn_integral o (fun s hs => (ck s hs.1).aestronglyMeasurable)
      (fun y => (((hE.hol _).mul_const _).mul_const _).mono Set.inter_subset_left) fun S hS _ =>
        ⟨M, fun s hs => hM s (hS hs)⟩).differentiableAt (o.mem_nhds ⟨hs, Metric.mem_ball_self h0⟩)).differentiableWithinAt
  have l1 : Law (1 : Chr F E) ((0 : ℂ) + n / 2) fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2) := fun p t x hp => by
    beta_reduce
    rw [ha.mul hp, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (absE_pos _).le (a0 x).le]; simp
  have h1 : IsHecke F E (1 : Chr F E) := ⟨continuous_const, fun _ => rfl⟩
  obtain ⟨U₁, Ê₁, hE₁, -⟩ := hE1 F E σ B n Y r _ hB hn (.inr hY) 1 h1 0 (fun x => by simp only [pow_zero, ite_self]; rfl) K a hS ha 0 (fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2))
    ⟨(Complex.continuous_ofReal.comp ca).cpow continuous_const fun x => Complex.ofReal_mem_slitPlane.2 (a0 x), l1, by
      refine FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2)).subset ?_)
      rintro _ ⟨k, rfl⟩
      refine funext fun x => ?_
      obtain ⟨p, t, hp, k', hk', rfl⟩ := ha.iwa x
      show (a _ : ℂ) ^ _ = (a _ : ℂ) ^ _
      simp only [mul_assoc, ha.val p t hp _ (mul_mem hk' k.2), ha.val p t hp _ hk']⟩
  obtain ⟨t₂, half₁⟩ := hE₁.half
  rw [← integral_prod (k s) (ik s hs)]
  refine An.ident hE.isOpen hE.conn hol (differentiableOn_const 0) (t := max (max t₁ t₂) (t₀ - n / 2)) (fun s hs => ?_) hs
  have s1 := (le_max_left _ _).trans_lt hs
  obtain ⟨u, sm⟩ := half s ((le_max_left _ _).trans_lt s1)
  have cs := continuous_flat (s₀ := s₀) cf ca a0 s
  obtain ⟨C, hC⟩ := (hf.flat (s₀ := s₀) ha a0 s).bound cs ha hK
  have ez : (s - s₀ + (s₀ + n / 2)).re = s.re + n / 2 := by simp; ring
  rw [ez] at hC
  have i1 : Integrable (fun g => flat a f s₀ s (e (1, g))) μ :=
    ((hi (s.re + n / 2) (by have := (le_max_right _ _).trans_lt hs; linarith)).const_mul C).mono'
      (cs.comp (ce.comp (Continuous.prodMk_right 1))).aestronglyMeasurable (.of_forall fun g => hC _)
  have i2 := i1.mul_bdd (continuous_detInv hχ).aestronglyMeasurable (.of_forall fun g => (norm_detInv χ g).le)
  obtain ⟨u₁, sm₁⟩ := half₁ (s.re : ℂ) (by simpa using (le_max_right _ _).trans_lt s1)
  obtain ⟨ε, C₁, N, h0, hg⟩ := hE₁.grow _ u₁
  have hfin : ∀ x, ∑' q : Cos σ Y, ∫⁻ y in D, ‖eisTerm (flat a f s₀ s) (e (x, y)) q * detInv χ y * φ y‖ₑ ∂μ ≠ ⊤ := fun x => by
    obtain ⟨M, hM⟩ := eis_bound he c1 c3 hφ C₁ N (ht x)
    have hM' := hM _ (fun c hc => (l1.flat ha a0 _).eis_rat h1 sm₁ hc) (hg _ (Metric.mem_ball_self h0)) x le_rfl
    haveI : Countable (Cos σ Y) := by
      exact Set.countable_univ_iff.1 ((sm₁ 1).summable.countable_support.mono fun q _ => mul_ne_zero
        (Complex.cpow_ne_zero_iff.2 (.inl (Complex.ofReal_ne_zero.2 (a0 _).ne')))
        (Complex.cpow_ne_zero_iff.2 (.inl (Complex.ofReal_ne_zero.2 (a0 _).ne'))))
    rw [← lintegral_tsum (f := fun q y => ‖eisTerm (flat a f s₀ s) (e (x, y)) q * detInv χ y * φ y‖ₑ) fun q => (((cs.comp (continuous_const.mul (ce.comp (Continuous.prodMk_right x)))).mul
      (continuous_detInv hχ)).mul hφ.1).measurable.enorm.aemeasurable]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in D, ENNReal.ofReal (max C 0 * M) ∂μ)
      (by rw [setLIntegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top fin.ne) (lintegral_mono fun y => ?_)
    have t1 : ∀ q : Cos σ Y, eisTerm (flat a (fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2)) 0 (s.re : ℂ)) (e (x, y)) q =
        ((a (q.out.1 * e (x, y)) ^ (s.re + n / 2) : ℝ) : ℂ) := fun q => by
      rw [eisTerm, flat, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (a0 _).ne'), Complex.ofReal_cpow (a0 _).le]
      congr 1; push_cast; ring
    have t2 : HasSum (fun q : Cos σ Y => a (q.out.1 * e (x, y)) ^ (s.re + n / 2)) (Ê₁ s.re (e (x, y))).re := by
      simpa only [t1, Complex.ofReal_re] using Complex.hasSum_re (sm₁ (e (x, y)))
    have p0 : ∀ q : Cos σ Y, 0 ≤ max C 0 * (a (q.out.1 * e (x, y)) ^ (s.re + n / 2) * ‖φ y‖) := fun q => by
      have := Real.rpow_nonneg (a0 (q.out.1 * e (x, y))).le (s.re + n / 2); positivity
    have t3 := (t2.mul_right ‖φ y‖).mul_left (max C 0)
    refine (ENNReal.tsum_le_tsum fun q => ?_).trans ((ENNReal.ofReal_tsum_of_nonneg p0 t3.summable).symm.le.trans
      (ENNReal.ofReal_le_ofReal ?_))
    · rw [← ofReal_norm_eq_enorm, norm_mul, norm_mul, norm_detInv, mul_one, ← mul_assoc]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ((hC _).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (a0 _).le _))) (norm_nonneg _))
    · rw [t3.tsum_eq]
      exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (norm_nonneg _)).trans (hM' y))
        (le_max_right _ _)
  refine ⟨u, ?_⟩
  rw [integral_prod (k s) (ik s u)]
  simp only [k, fun x => unfoldC hO hU hB hY d0 hχ he ce cs (hf.flat ha a0 s) sm hμ hD i1 hφ hc x (hfin x)]
  obtain ⟨b₀, hb₀⟩ := hφ.2.2 0
  rw [integral_integral_swap (f := fun (m : unipU σ Y V) g => flat a f s₀ s (e (1, g)) * detInv χ g * φ (m.1 * h * g))
    ((i2.comp_snd _).mul_bdd (c := b₀) (hφ.1.comp (by fun_prop)).aestronglyMeasurable
      (.of_forall fun y => by simpa using hb₀ (y.1.1 * h * y.2)))]
  simp only [integral_const_mul, mul_assoc _ h, hc V v1 v2 κ 𝓜 k1 k2, mul_zero, integral_zero]

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

theorem coefLine_of (hS : SWFull) (hX : BoxSec) (hW : DblW) (hH : HgtEx) (hT : HgtInt) (hK : Stab2Cpt) (hC : CptAll)
    (hR : PairsStable) (hM : MatchEx) (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hP : PolSch) : CoefLine := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq μ D hμ hD s t lam hl y hy Ψ hΨ
  have T := h.triple
  have l1 := T.geo.lt
  have l2 := T.geo.aBig
  have cW := hC F E σ B _ G.W _ _ T.base (Or.inr T.geo.hW) (by omega)
  have cV := hC F E σ B _ G.V' _ _ T.base (Or.inl T.geo.hV') (by omega)
  obtain ⟨q1, q2⟩ := (hM F E σ B a a' G X om om' R Rf h).2.2 _ _ hy.1 hy.2
  have b1 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1
  have b2 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1
  have s1 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T) _ q1
  have s2 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) _ q2.1
  have s3 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) _ hΨ
  have c1 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1 (Or.inr (by omega))
  have c2 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1 (Or.inr (by omega))
  have rp : ∀ s u, IsRapid (comb G om om' s u y) := fun s u =>
    cW.rapid (((c1 _ s1).const_smul s).add ((c2 _ s2).const_smul u)) fun γ hγ g => by
      simp only [comb, Pi.add_apply, Pi.smul_apply, I_inv G.M (b1 _ s1).2.1 γ hγ, I_inv G.M' (b2 _ s2).2.1 γ hγ]
  have tr : ∀ s u g, (fun h => comb G om om' s u y (h * g)) = comb G om om' s u (om (1, g) y.1, om' (1, g) y.2) := fun s u g =>
    funext fun h => by simp only [comb, Pi.add_apply, Pi.smul_apply, I_right]
  obtain ⟨dd, om₂, S, l, d1, d2, d3, -⟩ := hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)
  obtain ⟨⟨K, ht, k1, k2, k3, k4⟩, e, ce, he⟩ := hH F E σ B _ G.W _ _ T.base (.inr T.geo.hW)
  obtain ⟨t₀, hi⟩ := hT F E σ B _ G.W _ _ T.base (.inr T.geo.hW) K ht e k1 k2 he μ hμ
  have sec := hX F E σ B _ _ _ _ G.M' _ _ _ _ T.base (by omega) (by omega) T.geo.hV' (by omega) T.geo.hW T.geo.hM' X.α
    T.chars.heckeα T.chars.resα dd om₂ S l d3 d1 K ht k1 k2 Ψ hΨ Ψ hΨ
  obtain ⟨U, Ê, hE, u, hv⟩ := hS F E σ B _ _ _ _ G.M' _ _ _ _ T.base (by omega) (by omega) T.geo.hV' (by omega) T.geo.hW T.geo.hM' X.α
    T.chars.heckeα T.chars.resα dd om₂ S l d3 d1 K ht k1 k2 Ψ hΨ Ψ hΨ
  obtain ⟨hol, t₁, far⟩ := kpair_cont T.base (.inr T.geo.hW) (by omega) cW T.chars.heckeα he ce
    (hK F E σ B _ G.W _ _ T.base (.inr T.geo.hW) K k1) k2 k3 k4 sec.cont sec.law hE hμ hD hi
  have key := An.ident hE.isOpen hE.conn (hol _ (rp s t)) ((hol _ (rp 0 1)).const_mul lam) (fun z hz => ⟨(far z hz).1, by
    simp only [(far z hz).2.2 _ (rp s t), (far z hz).2.2 _ (rp 0 1), tr, ← integral_const_mul,
      fun g => hl _ ((hR F E σ B a a' G X om om' R Rf h hp hq).2 y hy g) y hy]
    exact integral_congr_ae (.of_forall fun g => mul_left_comm _ _ _)⟩) u
  haveI := cW.sc; haveI := cV.sc; haveI := cW.lc; haveI := cV.lc
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (G.M'.μ.restrict G.M'.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cV.fin _ _ T.geo.hM'.haar T.geo.hM'.dom⟩
  have val : ∀ φ, IsRapid φ → kpair X.α e μ D (Ê (((a' : ℂ) - (a + a' : ℕ)) / 2)) φ =
      2 * ((G.M'.μ.real G.M'.dom)⁻¹ : ℝ) * pet G.M'.μ G.M'.dom (th om' μ D φ Ψ) (th om' μ D φ Ψ) := fun φ hφ => by
    have := An.at_value (μ.restrict D) (G.M'.μ.restrict G.M'.dom) ⟨(b2 _ s3).1, cV.bdd₂ cW (b2 _ s3).1 (b2 _ s3).2.1⟩
      ⟨hφ.1, cW.bdd hφ.1 hφ.2.1⟩
    refine Eq.trans ?_ (congrArg _ this)
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, if_neg (show ¬ a + a' < a' by omega), setAverage_eq, Complex.real_smul,
      ← fun g => (((d2 Ψ s3 Ψ s3).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring
  rw [val _ (rp s t), val _ (rp 0 1), mul_left_comm lam] at key
  exact mul_left_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 (inv_ne_zero (cV.vol_ne T.geo.hM'.haar T.geo.hM'.dom)))) key

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Dense

open PositivityTheory.ThKOwn (polE eq_zero_PG)

theorem exp_tg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : E → ℝ}
    (hr : r.HasTemperateGrowth) (c : ℂ) (s : ℝ) :
    (fun y => c * Complex.exp ((s : ℂ) * Complex.I * (r y : ℂ))).HasTemperateGrowth := by
  have hlin : (fun y => (s / (2 * Real.pi)) * r y).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul hr
  have hc := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp hlin
  have h : (fun y => c * Complex.exp ((s : ℂ) * Complex.I * (r y : ℂ))) =
      fun y => c * ((GlobalTheory.Published.Metaplectic.eChar : ℝ → ℂ) ∘ fun y => (s / (2 * Real.pi)) * r y) y := by
    funext y
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [Function.comp, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 2
    push_cast
    field_simp
  rw [h]
  exact (Function.HasTemperateGrowth.const c).mul hc

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem quad_tg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E ≃L[ℝ] V)
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : (fun x => Q (L x) (L x)).HasTemperateGrowth := by
  have hL : (fun x => L x).HasTemperateGrowth := (L : E →L[ℝ] V).hasTemperateGrowth
  exact (Q.toContinuousBilinearMap).bilinear_hasTemperateGrowth hL hL

theorem lower_bound {n : ℕ} (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] V) (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hpos : ∀ x, x ≠ 0 → 0 < Q x x) :
    ∃ w : ℝ, 0 < w ∧ ∀ x, w * ‖x‖ ^ 2 ≤ Q (L x) (L x) := by
  set q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Q (L x) (L x) with hqdef
  have hq : Continuous q := (quad_tg L Q).1.continuous
  have hscale : ∀ (t : ℝ) x, q (t • x) = t ^ 2 * q x := by
    intro t x
    simp only [hqdef, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hq0 : q 0 = 0 := by simp [hqdef]
  by_cases hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMinOn hne
      hq.continuousOn
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    have hw : 0 < q u := hpos _ (by simpa using hu0)
    refine ⟨q u, hw, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      show _ ≤ q 0
      simp [hq0]
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hm : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simp [norm_smul, hn]
    have h1 : q u ≤ q (‖x‖⁻¹ • x) := hmin hm
    have h2 : q x = ‖x‖ ^ 2 * q (‖x‖⁻¹ • x) := by
      rw [hscale]
      field_simp
    show _ ≤ q x
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := by
      by_contra hx
      exact hne ⟨‖x‖⁻¹ • x, by simp [norm_smul, norm_ne_zero_iff.2 hx]⟩
    subst hx
    show _ ≤ q 0
    simp [hq0]

theorem poly_mem {n : ℕ} (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] V)
    (N : Submodule ℂ (SchwartzMap V ℂ))
    (hmul : ∀ (l : V →ₗ[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (l x : ℂ) * f x) → f₁ ∈ N)
    (f₀ : SchwartzMap V ℂ) (hf₀ : f₀ ∈ N) (P : MvPolynomial (Fin n) ℂ) :
    ∃ F ∈ N, ∀ y, F y = polE P (L.symm y) * f₀ y := by
  induction P using MvPolynomial.induction_on with
  | C z => exact ⟨z • f₀, N.smul_mem z hf₀, fun y => by simp [polE]⟩
  | add P R hP hR =>
    obtain ⟨F, hF, hFy⟩ := hP
    obtain ⟨G, hG, hGy⟩ := hR
    refine ⟨F + G, N.add_mem hF hG, fun y => ?_⟩
    have h : polE (P + R) (L.symm y) = polE P (L.symm y) + polE R (L.symm y) := by simp [polE]
    rw [h, add_mul, SchwartzMap.add_apply, hFy, hGy]
  | mul_X P p hP =>
    obtain ⟨F, hF, hFy⟩ := hP
    let l : V →L[ℝ] ℝ := (EuclideanSpace.proj (𝕜 := ℝ) p).comp (L.symm : V →L[ℝ] EuclideanSpace ℝ (Fin n))
    have hg : (fun y => ((l y : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp l).hasTemperateGrowth
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun y => ((l y : ℝ) : ℂ)) F,
      hmul (l : V →ₗ[ℝ] ℝ) F _ hF (fun y => ?_), fun y => ?_⟩
    · rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
      rfl
    · rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hFy]
      have h : polE (P * MvPolynomial.X p) (L.symm y) = polE P (L.symm y) * ((l y : ℝ) : ℂ) := by
        simp [polE, l]
      rw [h]
      ring

theorem schwartz_functional_eq_zero_of_dense (Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (c₀ : ℂ)
    (f₀ : SchwartzMap V ℂ) (hc : c₀ ≠ 0) (hpos : ∀ x, x ≠ 0 → 0 < Q x x)
    (hf : ∀ x, f₀ x = c₀ * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ)))
    (N : Submodule ℂ (SchwartzMap V ℂ)) (hN : f₀ ∈ N)
    (hmul : ∀ (l : V →ₗ[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (l x : ℂ) * f x) → f₁ ∈ N)
    (T : SchwartzMap V ℂ →L[ℂ] ℂ) (hT : ∀ f ∈ N, T f = 0) : T = 0 := by
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃L[ℝ] V := (toEuclidean (E := V)).symm
  let q : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℝ := fun x => Q (L x) (L x)
  let r : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℝ := fun x => Q' (L x) (L x)
  have hq : q.HasTemperateGrowth := quad_tg L Q
  have hr : r.HasTemperateGrowth := quad_tg L Q'
  obtain ⟨w, hw, hlow⟩ := lower_bound L Q hpos
  let g : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ :=
    fun y => c₀ * Complex.exp (((-1 : ℝ) : ℂ) * Complex.I * (r y : ℂ))
  let g' : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ :=
    fun y => c₀⁻¹ * Complex.exp (((1 : ℝ) : ℂ) * Complex.I * (r y : ℂ))
  have hg : g.HasTemperateGrowth := exp_tg hr c₀ (-1)
  have hg' : g'.HasTemperateGrowth := exp_tg hr c₀⁻¹ 1
  let A : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ →L[ℂ] SchwartzMap V ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
  let B : SchwartzMap V ℂ →L[ℂ] SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L
  let M := SchwartzMap.smulLeftCLM ℂ g
  let M' := SchwartzMap.smulLeftCLM ℂ g'
  have hS : ∀ f, T (A (M f)) = 0 := by
    have hext := eq_zero_PG q hq w hw hlow (T ∘L A ∘L M)
      (fun f hf' => by
        obtain ⟨P, hP⟩ := hf'
        obtain ⟨F, hFN, hF⟩ := poly_mem L N hmul f₀ hN P
        have hAM : A (M f) = F := by
          ext y
          have hy : (L (L.symm y)) = y := L.apply_symm_apply y
          simp only [A, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp,
            M, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hP, hF, hf]
          simp only [g, q, r, hy]
          push_cast
          rw [show -(Q y y : ℂ) - Complex.I * (Q' y y : ℂ) =
            -1 * Complex.I * (Q' y y : ℂ) + -(Q y y : ℂ) by ring, Complex.exp_add]
          ring
        show T (A (M f)) = 0
        rw [hAM]
        exact hT F hFN)
    exact fun f => DFunLike.congr_fun hext f
  ext h
  have hinv : A (M (M' (B h))) = h := by
    ext y
    simp only [A, B, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp,
      M, M', SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg',
      smul_eq_mul, L.apply_symm_apply]
    simp only [g, g']
    rw [← mul_assoc, mul_mul_mul_comm, ← Complex.exp_add]
    push_cast
    simp [hc]
  rw [← hinv]
  simpa using hS _

end GlobalTheory.ThK.Dbl.Dense

end
end
