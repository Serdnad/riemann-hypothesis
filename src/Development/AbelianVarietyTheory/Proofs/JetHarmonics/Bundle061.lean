module

public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle056
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle004
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001
public import Mathlib.Analysis.Normed.Ring.Units
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002

@[expose] public section

section

set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.ThetaLeast


open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv GlobalTheory.GaugeBaseChange in
theorem nabValN_algebraMap (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] [Algebra S S']
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB S d O) (h : PS S 2 d)
    (hc : MvPowerSeries.constantCoeff h = 0) (w0 : O) (m n : ℕ) (f : PS S n d) (κ : Type) [Fintype κ]
    (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) :
    nabValN B S' (MvPowerSeries.map (algebraMap S S') h) w0 m (MvPowerSeries.map (algebraMap S S') f) cp
      (fun l j => algebraMap S S' (u l j)) (MvPolynomial.map (algebraMap S S') P) =
      algebraMap S S' (nabValN B S h w0 m f cp u P) := by
  set ψ := algebraMap S S' with hψ
  have eF : (fun i => MvPowerSeries.map ψ (B.FK S i)) = B.FK S' := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.G.F i)) =
      MvPowerSeries.map (algebraMap S S') (B.G.F i)
    ext e
    simp [coeff_map, hψ]
  have eA : mapP ψ (B.actK S w0) = B.actK S' w0 := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.A.act w0 i)) =
      MvPowerSeries.map (algebraMap S S') (B.A.act w0 i)
    ext e
    simp [coeff_map, hψ]
  have gC : GP (comp1 (B.actK S w0) (pt S (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL S h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map ψ (B.hL S h w0) = B.hL S' (MvPowerSeries.map ψ h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), eA, baseChange_pt]
  have g1 : ∀ (b : Fin n) (j : Fin 1), GP ((![pt S d b] : Fin 1 → Pt S n d) j) := by
    intro b j
    fin_cases j
    exact gp_pt b
  have cb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt S d b] (B.hL S h w0)) = 0 :=
    fun b => gt_const_ev _ (g1 b) _ cL
  have eb : ∀ b : Fin n, MvPowerSeries.map ψ (ev (n := n) ![pt S d b] (B.hL S h w0)) =
      ev (n := n) ![pt S' d b] (B.hL S' (MvPowerSeries.map ψ h) w0) := by
    intro b
    rw [map_ev ψ _ (g1 b), eL]
    congr 1
    funext j
    fin_cases j
    exact baseChange_pt ψ b
  unfold nabValN

  rw [← MvPowerSeries.constantCoeff_map, ← GlobalTheory.dpolyN_map, eF, map_mul,
  map_expS _ _ (by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero fun b _ => cb b, mul_zero]),
  MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast ψ, map_sum,
  Finset.sum_congr rfl fun b _ => eb b]

theorem smul_mem_HHa {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k] {cc : Ty → Ty} {isX : Ty → Prop}
    {a : Ty → ℕ → ℕ} (s : k) {P : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) :
    s • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ s hP.1, fun σ i i' hi t => by rw [map_smul, hP.2.1 σ i i' hi t],
    fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩

theorem exists_lift_integers (K : Type) [Field K] [NumberField K] (V L : Type) [CommRing V] [IsDomain V]
    [IsIntegrallyClosed V] [Field L] [Algebra V L] [IsFractionRing V L] (io : K →+* L) :
    ∃ φ : 𝓞 K →+* V, ∀ x : 𝓞 K, algebraMap V L (φ x) = io (x : K) := by
  have h : ∀ x : 𝓞 K, ∃ z : V, algebraMap V L z = io (x : K) := fun x =>
    IsIntegrallyClosed.algebraMap_eq_of_integral
      (IsIntegral.tower_top (R := ℤ) (map_isIntegral_int io x.isIntegral_coe))
  choose g hg using h
  have inj := IsFractionRing.injective V L
  refine ⟨⟨⟨⟨g, inj ?_⟩, fun x y => inj ?_⟩, inj ?_, fun x y => inj ?_⟩, hg⟩ <;> simp [hg]

theorem exists_combination_integers (K : Type) [Field K] [NumberField K] (T : CDVR) (io : K →+* T.Fr)
    (Ty : Type) (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (P : MvPolynomial (Letter Ty r n) T.Fr) (hP : P ∈ HaO r n T.Fr (algebraMap T.V T.Fr).range cc isX a) :
    ∃ (s : ℕ) (c : Fin s → T.V) (Q : Fin s → MvPolynomial (Letter Ty r n) K),
      (∀ j, Q j ∈ HaO r n K (integralClosure ℤ K).toSubring cc isX a) ∧
      P = ∑ j, algebraMap T.V T.Fr (c j) • MvPolynomial.map io (Q j) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_lift_integers K T.V T.Fr io
  let p : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal T.V).comap φ
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ _
  have hS : p.primeCompl ≤ nonZeroDivisors (𝓞 K) := p.primeCompl_le_nonZeroDivisors
  let V := Localization.subalgebra.ofField K p.primeCompl hS
  haveI : IsLocalRing V := IsLocalization.AtPrime.isLocalRing V p
  haveI : IsDedekindDomain V := IsLocalization.isDedekindDomain (𝓞 K) hS V
  haveI : IsPrincipalIdealRing V :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain V).out 3 1).1 ‹IsDedekindDomain V›
  have hu : ∀ s : p.primeCompl, IsUnit (φ s) := fun s => by
    by_contra hn
    exact s.2 ((IsLocalRing.mem_maximalIdeal _).2 hn)
  have hV : ∀ x : V, io (algebraMap V K x) ∈ (algebraMap T.V T.Fr).range := by
    rintro ⟨x, a, s, hs, rfl⟩
    obtain ⟨u, hu'⟩ := hu ⟨s, hs⟩
    refine ⟨φ a * (u⁻¹ : T.Vˣ), ?_⟩
    change _ = io (algebraMap _ K a * (algebraMap _ K s)⁻¹)
    rw [map_mul, map_mul, map_inv₀, map_units_inv, hu', hφ, hφ]
  obtain ⟨s, c, Q, hc, hQ, hsum⟩ := GlobalTheory.exists_integral_combination_of_mem_HaO Ty r n V K T.Fr io _ hV cc isX a P hP
  have hden : ∀ j, ∃ b : p.primeCompl, ∀ m, (((b : 𝓞 K) : K) • Q j).coeff m ∈ (integralClosure ℤ K).toSubring := by
    intro j
    choose g hg using (hQ j).2
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Q j).support g
    refine ⟨b, fun m => ?_⟩
    by_cases hm : m ∈ (Q j).support
    · obtain ⟨z, hz⟩ := hb m hm
      have : (((b : 𝓞 K) : K) • Q j).coeff m = (z : K) := by
        rw [MvPolynomial.coeff_smul, ← hg m]
        have := congrArg (algebraMap V K) hz
        rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply] at this
        exact this.symm
      rw [this]
      exact z.isIntegral_coe
    · rw [MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.1 hm, smul_zero]
      exact Subring.zero_mem _
  choose b hb using hden
  choose c' hc' using hc
  choose u hu' using hu
  refine ⟨s, fun j => c' j * ((u (b j))⁻¹ : T.Vˣ), fun j => ((b j : 𝓞 K) : K) • Q j,
    fun j => ⟨smul_mem_HHa _ (hQ j).1, hb j⟩, ?_⟩
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : io ((b j : 𝓞 K) : K) ≠ 0 := by
    rw [← hφ, ← hu']
    exact ((u (b j)).isUnit.map _).ne_zero
  beta_reduce
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map io), MvPolynomial.map_C, ← mul_assoc,
    ← map_mul, map_mul (algebraMap T.V T.Fr), map_units_inv, hu', hφ, hc', mul_assoc, inv_mul_cancel₀ h0, mul_one]

theorem totalDegree_le_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    (T : CDVR) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) T.Fr} (hP : P ∈ FFV (Dw := Dw) T a n) :
    P.totalDegree ≤ DF Dw a := by
  have key : ∀ m ∈ P.support, (m.sum fun _ e => e) = DF Dw a := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, DF]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i
  exact Finset.sup_le fun m' hm' => (key m' hm').le

theorem val_algebraMap_nonneg (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ)) (x : T.V) :
    0 ≤ v (algebraMap T.Fr F (algebraMap T.V T.Fr x)) := by
  by_cases hx : algebraMap T.V T.Fr x = 0
  · rw [hx, map_zero, AddValuation.map_zero]; exact le_top
  · rw [hv _ hx]
    exact_mod_cast GlobalTheory.vV_algebraMap_nonneg_dvr T x

theorem nval_le_of_val (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ))
    {x z : T.Fr} (hx : x ≠ 0) {ε : F} (hε : 0 ≤ v ε) {ρ : ℚ} (hρ : v (ε * algebraMap T.Fr F z) = (ρ : WithTop ℚ))
    {δ : ℝ} (hle : (ρ : ℝ) ≤ ((vV T.V x : ℤ) : ℚ) + δ) (e : ℕ) :
    nval T.V e z ≤ nval T.V e x + ((δ / e : ℝ) : EReal) := by
  have hz : z ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero, AddValuation.map_zero] at hρ
    exact WithTop.top_ne_coe hρ
  rw [AddValuation.map_mul, hv z hz] at hρ
  have h1 : (((vV T.V z : ℤ) : ℚ) : WithTop ℚ) ≤ (ρ : WithTop ℚ) := hρ ▸ le_add_of_nonneg_left hε
  have h2 : ((vV T.V z : ℤ) : ℚ) ≤ ρ := WithTop.coe_le_coe.1 h1
  have h3 : ((vV T.V z : ℤ) : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast h2
  rw [nval_of_ne hz, nval_of_ne hx, ← EReal.coe_add, EReal.coe_le_coe_iff, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg e)
  rw [Rat.cast_intCast] at hle
  linarith

theorem le_iInf_add_coe {ι : Sort*} {X : EReal} {g : ι → EReal} {δ : ℝ} (h : ∀ i, X ≤ g i + (δ : EReal)) :
    X ≤ (⨅ i, g i) + (δ : EReal) := by
  rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))]
  exact le_iInf fun i =>
    (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))).2 (h i)

end GlobalTheory.ThetaLeast
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory
namespace QuotCutoff

def mulM {m : ℕ} (a b : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of a * Matrix.of b) i j

lemma continuous_mulM {m : ℕ} : Continuous (fun p : PI.MtM m × PI.MtM m => mulM p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

lemma mulM_assoc {m : ℕ} (a b c : PI.MtM m) : mulM (mulM a b) c = mulM a (mulM b c) :=
  Matrix.mul_assoc (Matrix.of a) (Matrix.of b) (Matrix.of c)

lemma continuous_mulM_left {m : ℕ} (x : PI.MtM m) : Continuous (fun s => mulM s x) :=
  continuous_mulM.comp (continuous_id.prodMk continuous_const)

def invM {m : ℕ} (a : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of a)⁻¹ i j

lemma continuousAt_invM {m : ℕ} (a : PI.MtM m) (h : Matrix.of a * (Matrix.of a)⁻¹ = 1) :
    ContinuousAt invM a := by
  have hu : IsUnit (Matrix.of a).det := Matrix.isUnit_det_of_right_inverse h
  have h1 : ContinuousAt Ring.inverse (Matrix.of a).det := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact continuousAt_matrix_inv (Matrix.of a) h1

def piece {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) (j : ℕ) : Set (PI.MtM m) :=
  {x | Matrix.of x ∈ G} ∩ Metric.closedBall 0 (j : ℝ)

lemma isClosed_of {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsClosed G) :
    IsClosed {x : PI.MtM m | Matrix.of x ∈ G} := hG

lemma isCompact_piece {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsClosed G) (j : ℕ) :
    IsCompact (piece G j) :=
  (isCompact_closedBall _ _).inter_left (isClosed_of hG)

lemma exists_bound {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hμ : PI.IsHaarOnM S μ)
    (hR : PI.IsRightInvM S μ) (j : ℕ) :
    ∃ c : ℝ≥0∞, c < ⊤ ∧ ∀ x : PI.MtM m, μ ((fun s => mulM s x) ⁻¹' piece G j) ≤ c := by
  have hC := isCompact_piece hG.1 j
  set K : Set (PI.MtM m) :=
    (fun p : PI.MtM m × PI.MtM m => mulM p.1 (invM p.2)) '' (piece G j ×ˢ piece G j) with hK
  have hKc : IsCompact K := by
    refine (hC.prod hC).image_of_continuousOn ?_
    rintro ⟨a, b⟩ ⟨-, hb⟩
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun p : PI.MtM m × PI.MtM m => invM p.2) (a, b) :=
      ContinuousAt.comp (g := invM) (f := fun p : PI.MtM m × PI.MtM m => p.2) (x := (a, b))
        (continuousAt_invM b (hG.2.2.2 (Matrix.of b) hb.1).2) continuousAt_snd
    exact ContinuousAt.comp (g := fun p : PI.MtM m × PI.MtM m => mulM p.1 p.2)
      (f := fun p : PI.MtM m × PI.MtM m => (p.1, invM p.2))
      continuous_mulM.continuousAt (continuousAt_fst.prodMk h1)
  have hKS : IsCompact (K ∩ {x | Matrix.of x ∈ S}) := hKc.inter_right (isClosed_of hS.1)
  refine ⟨μ (K ∩ {x | Matrix.of x ∈ S}),
    (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos m S μ hS hμ).2.1 _ hKS (fun x hx => hx.2), fun x => ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  have hA : MeasurableSet ((fun s => mulM s x) ⁻¹' piece G j) :=
    (hC.isClosed.preimage (continuous_mulM_left x)).measurableSet
  by_cases h : ∃ s₀ : PI.MtM m, Matrix.of s₀ ∈ S ∧ mulM s₀ x ∈ piece G j
  · obtain ⟨s₀, hs₀, hx⟩ := h
    have h1 : μ.map (fun s => mulM s s₀) = μ := hR _ hs₀
    rw [← h1, Measure.map_apply (continuous_mulM_left s₀).measurable hA, h1]
    refine measure_mono_ae ?_
    filter_upwards [hae] with t ht hti
    refine ⟨⟨(mulM t (mulM s₀ x), mulM s₀ x), ⟨?_, hx⟩, ?_⟩, ht⟩
    · rw [← mulM_assoc]; exact hti
    · have h2 := (hG.2.2.2 (Matrix.of (mulM s₀ x)) hx.1).2
      change Matrix.of t * Matrix.of (mulM s₀ x) * (Matrix.of (mulM s₀ x))⁻¹ = Matrix.of t
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  · refine measure_mono_ae ?_
    filter_upwards [hae] with t ht hti
    exact absurd ⟨t, ht, hti⟩ h

lemma exists_pos {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hSG : S ⊆ G) (hμ : PI.IsHaarOnM S μ)
    (x : PI.MtM m) (hx : Matrix.of x ∈ G) :
    ∃ j : ℕ, 0 < μ ((fun s => mulM s x) ⁻¹' piece G j) := by
  obtain ⟨j, hj⟩ := exists_nat_gt ‖x‖
  refine ⟨j, ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  have hU : IsOpen ((fun s => mulM s x) ⁻¹' Metric.ball 0 (j : ℝ)) :=
    Metric.isOpen_ball.preimage (continuous_mulM_left x)
  have h1 : mulM (Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ)) x = x :=
    Matrix.one_mul (Matrix.of x)
  have := (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos m S μ hS hμ).2.2 _ hU
    ⟨Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ), by
      rw [Set.mem_preimage, h1]; simpa using hj, hS.2.1⟩
  refine this.trans_le (measure_mono_ae ?_)
  filter_upwards [hae] with t ht hti
  exact ⟨hG.2.2.1 _ (hSG ht) _ hx, Metric.ball_subset_closedBall hti⟩

lemma exists_precutoff {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hSG : S ⊆ G) (hμ : PI.IsHaarOnM S μ)
    (hR : PI.IsRightInvM S μ) :
    ∃ φ : PI.MtM m → ℝ≥0∞, Measurable φ ∧ ∀ x : PI.MtM m, Matrix.of x ∈ G →
      ∫⁻ s, φ (mulM s x) ∂μ ≠ 0 ∧ ∫⁻ s, φ (mulM s x) ∂μ ≠ ⊤ := by
  choose c hc hb using exists_bound hG hS hμ hR
  have hP : ∀ j, MeasurableSet (piece G j) := fun j => (isCompact_piece hG.1 j).measurableSet
  set w : ℕ → ℝ≥0∞ := fun j => (2⁻¹ : ℝ≥0∞) ^ j * (1 + c j)⁻¹ with hw
  have hmeas : ∀ j, Measurable ((piece G j).indicator (fun _ => w j)) :=
    fun j => measurable_const.indicator (hP j)
  have hI : ∀ x : PI.MtM m, ∫⁻ s, (∑' j, (piece G j).indicator (fun _ => w j) (mulM s x)) ∂μ
      = ∑' j, w j * μ ((fun s => mulM s x) ⁻¹' piece G j) := by
    intro x
    rw [lintegral_tsum (f := fun j s => (piece G j).indicator (fun _ => w j) (mulM s x))
      (fun j => ((hmeas j).comp (continuous_mulM_left x).measurable).aemeasurable)]
    congr 1
    ext j
    rw [← lintegral_indicator_const ((continuous_mulM_left x).measurable (hP j))]
    rfl
  refine ⟨fun y => ∑' j, (piece G j).indicator (fun _ => w j) y,
    Measurable.tsum hmeas, fun x hx => ?_⟩
  rw [hI x]
  constructor
  · obtain ⟨j, hj⟩ := exists_pos hG hS hSG hμ x hx
    intro h
    rw [ENNReal.tsum_eq_zero] at h
    have hwj : w j ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (by simp)) ?_
      rw [ENNReal.inv_ne_zero]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, (hc j).ne⟩
    exact mul_ne_zero hwj hj.ne' (h j)
  · refine ne_top_of_le_ne_top (b := ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j) ?_
      (ENNReal.tsum_le_tsum fun j => ?_)
    · rw [ENNReal.tsum_geometric]
      simp
    · have h1 : (1 + c j)⁻¹ * μ ((fun s => mulM s x) ⁻¹' piece G j) ≤ 1 := by
        calc _ ≤ (1 + c j)⁻¹ * (1 + c j) := by
              gcongr
              exact (hb j x).trans le_add_self
          _ ≤ 1 := ENNReal.inv_mul_le_one _
      calc w j * _ = (2⁻¹ : ℝ≥0∞) ^ j * ((1 + c j)⁻¹ * μ ((fun s => mulM s x) ⁻¹' piece G j)) :=
            mul_assoc _ _ _
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ j * 1 := by gcongr
        _ = _ := mul_one _

end QuotCutoff


open QuotCutoff in
theorem exists_normalised_cutoff : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μS : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM S μS → PI.IsRightInvM S μS → ∃ φ : PI.MtM m → ℝ≥0∞, Measurable φ ∧ ∀ x : PI.MtM m, Matrix.of x ∈ G → ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1 := by
  intro m G S μ hG hS hSG hμ hR
  obtain ⟨φ, hφ, hI⟩ := exists_precutoff hG hS hSG hμ hR
  haveI := hμ.1
  set I : PI.MtM m → ℝ≥0∞ := fun x => ∫⁻ s, φ (mulM s x) ∂μ with hIdef
  have hIm : Measurable I :=
    Measurable.lintegral_prod_left' (f := fun p : PI.MtM m × PI.MtM m => φ (mulM p.1 p.2))
      (hφ.comp continuous_mulM.measurable)
  have hinv : ∀ s₀ x : PI.MtM m, Matrix.of s₀ ∈ S → I (mulM s₀ x) = I x := by
    intro s₀ x hs₀
    have h1 : μ.map (fun s => mulM s s₀) = μ := hR _ hs₀
    have h2 := lintegral_map (μ := μ) (f := fun s => φ (mulM s x))
      (hφ.comp (continuous_mulM_left x).measurable) (continuous_mulM_left s₀).measurable
    rw [h1] at h2
    simp only [hIdef]
    rw [h2]
    simp only [mulM_assoc]
  refine ⟨fun y => φ y * (I y)⁻¹, hφ.mul hIm.inv, fun x hx => ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  calc ∫⁻ s, φ (mulM s x) * (I (mulM s x))⁻¹ ∂μ = ∫⁻ s, φ (mulM s x) * (I x)⁻¹ ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with s hs
        rw [hinv s x hs]
    _ = I x * (I x)⁻¹ := lintegral_mul_const _ (hφ.comp (continuous_mulM_left x).measurable)
    _ = 1 := ENNReal.mul_inv_cancel (hI x hx).1 (hI x hx).2

end GlobalTheory
end
end

section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtGermCompare

theorem surjective_cube {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom := by
  have hG := GlobalTheory.globalFns_holds
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    RigidIsoCube.surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have s₂ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg G) s₁
  rw [Over.w (snd G G)] at s₂
  have s₃ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg (G ⊗ G)) s₂
  rw [Over.w (snd G (G ⊗ G))] at s₃
  exact s₃

theorem cubical_unique {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (sj : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  let e : 𝟙_ (Over S) ⟶ G3 G := lift 1 (lift 1 1)
  have h : c.t.s = c'.t.s := JetSer.gen_ext_val L.isLB (φ := thφ G (x3 G)) (ε := thε) c.isGen c'.isGen fun y J hJ =>
    gen_unique L.isLB (φ := thφ G (x3 G)) (ε := thε) (G3 G).hom e.left (Over.w e) sj c.isGen c'.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV c' hJ).face 1 1).symm) _ _ y J hJ
  obtain ⟨⟨t⟩, _⟩ := c
  obtain ⟨⟨t'⟩, _⟩ := c'
  obtain rfl : t = t' := h
  rfl

section Scale
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}

end Scale

section Bound
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}

end Bound

section Cast
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {L L' : RigLB G}

end Cast

open GlobalTheory.FamGerm

section Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [Algebra (FractionRing V) F]

variable [CharZero F]

end Data

section Statements

end Statements

end GlobalTheory.PtGermCompare
end
end
