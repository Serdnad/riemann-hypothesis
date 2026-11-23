module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Length
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthSumHeightOneDisjointDivisors
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle238
public import Mathlib.RingTheory.WittVector.Basic
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle386
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformTaylorBoundLeviPluriharmonicSplit
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedGaussianIntegralUniformPosSemidef
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle388
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
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
public import Mathlib.RingTheory.WittVector.Complete
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.RingTheory.Bialgebra.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003

@[expose] public section

section


theorem _root_.GlobalTheory.T.length_sum_height_one_disjoint_divisors : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A], ringKrullDim A = 2 → ∀ (a b : A), a ≠ 0 → b ≠ 0 → ∀ (P Q : Finset (PrimeSpectrum A)), (∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal) → (∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) → Disjoint P Q → ∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal b})).toNat = ∑ p ∈ Q, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) b})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal a})).toNat := by
  first | exact @GlobalTheory.IntersectionSymm.intersection_symm | exact GlobalTheory.IntersectionSymm.intersection_symm | (intros; apply GlobalTheory.IntersectionSymm.intersection_symm <;> assumption)
end

section

namespace GlobalTheory.PicReducedTors

theorem pic_isOfFinOrder : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B),
    IsOfFinOrder M := by
  intro B _ _ _ M
  haveI : IsNoetherian ℤ B := inferInstance
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  let φ := Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)
  haveI : Module.Finite ℤ ((P : minimalPrimes B) → B ⧸ (P : Ideal B)) := inferInstance
  obtain ⟨n, hn, hmul⟩ := GlobalTheory.T.exists_nat_mul_mem_range_pi_quotient_minimalPrimes' B
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    have hrad : b ∈ (⊥ : Ideal B).radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      have := congrFun hb ⟨P, hP⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact this
    obtain ⟨k, hk⟩ := hrad
    exact IsReduced.eq_zero b ⟨k, by simpa using hk⟩
  refine GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B _ φ n hinj hn hmul M ?_
  refine GlobalTheory.T.pic_pi_isOfFinOrder' _ _ (fun P N => ?_) _
  haveI : (P : Ideal B).IsPrime := P.2.1.1
  exact GlobalTheory.T.pic_isOfFinOrder_of_finite_int' _ N

end GlobalTheory.PicReducedTors
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem wittDual_reduction : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (M V : Type) [AddCommGroup M] [Module (WittVector p k) M] [Module.Free (WittVector p k) M] [Module.Finite (WittVector p k) M] [AddCommGroup V] [Module k V] (r : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = p • n) → ∃ r' : Module.Dual (WittVector p k) M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] Module.Dual k V, (∀ l m, r' l (r m) = WittVector.constantCoeff (l m)) ∧ Function.Surjective r' ∧ ∀ l, r' l = 0 ↔ ∃ l', l = p • l' := by
  intro p _ k _ _ _ M V _ _ _ _ _ _ r hr hker
  have hσs : Function.Surjective (WittVector.constantCoeff : WittVector p k →+* k) :=
    WittVector.constantCoeff_surjective p
  have hpk : ∀ y : k, (p • y) = 0 := fun y => by
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hσker : ∀ x : WittVector p k, WittVector.constantCoeff x = 0 → ∃ y, x = p • y := by
    intro x hx
    have hx' : x ∈ Ideal.span {(p : WittVector p k)} :=
      (WittVector.mem_span_p_iff_coeff_zero_eq_zero x).2 (by simpa [WittVector.constantCoeff_apply] using hx)
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx'
    exact ⟨y, by rw [nsmul_eq_mul, ← hy, mul_comm]⟩
  have hwd : ∀ (l : Module.Dual (WittVector p k) M) (m m' : M), r m = r m' →
      WittVector.constantCoeff (l m) = WittVector.constantCoeff (l m') := by
    intro l m m' h
    obtain ⟨n, hn⟩ := (hker (m - m')).1 (by rw [map_sub, h, sub_self])
    have h1 : l m - l m' = p • l n := by rw [← map_sub, hn, map_nsmul]
    rw [← sub_eq_zero, ← map_sub, h1, map_nsmul, hpk]
  have hg0 : ∀ (l : Module.Dual (WittVector p k) M) (m : M),
      WittVector.constantCoeff (l (Function.surjInv hr (r m))) = WittVector.constantCoeff (l m) :=
    fun l m => hwd l _ _ (Function.surjInv_eq hr _)
  let g : Module.Dual (WittVector p k) M → Module.Dual k V := fun l =>
    { toFun := fun v => WittVector.constantCoeff (l (Function.surjInv hr v))
      map_add' := fun v w => by
        obtain ⟨m, rfl⟩ := hr v
        obtain ⟨m', rfl⟩ := hr w
        rw [← map_add r, hg0, hg0, hg0, map_add (f := _), map_add (f := _)]
      map_smul' := fun c v => by
        obtain ⟨a, rfl⟩ := hσs c
        obtain ⟨m, rfl⟩ := hr v
        rw [← LinearMap.map_smulₛₗ, hg0, hg0, map_smul, smul_eq_mul, map_mul, RingHom.id_apply,
          smul_eq_mul] }
  have hg : ∀ l m, g l (r m) = WittVector.constantCoeff (l m) := fun l m => hg0 l m
  let r' : Module.Dual (WittVector p k) M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)]
      Module.Dual k V :=
    { toFun := g
      map_add' := fun l l' => by
        ext v
        obtain ⟨m, rfl⟩ := hr v
        rw [LinearMap.add_apply, hg, hg, hg, LinearMap.add_apply, map_add (f := _)]
      map_smul' := fun a l => by
        ext v
        obtain ⟨m, rfl⟩ := hr v
        rw [LinearMap.smul_apply, hg, hg, LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul] }
  have hr' : ∀ l m, r' l (r m) = WittVector.constantCoeff (l m) := hg
  let b := Module.Free.chooseBasis (WittVector p k) M
  refine ⟨r', hr', ?_, ?_⟩
  · intro f
    let a : Module.Free.ChooseBasisIndex (WittVector p k) M → WittVector p k :=
      fun i => Function.surjInv hσs (f (r (b i)))
    let l : Module.Dual (WittVector p k) M := b.constr (WittVector p k) a
    let F1 : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] k :=
      { toFun := fun m => WittVector.constantCoeff (l m)
        map_add' := fun m m' => by rw [map_add (f := _), map_add (f := _)]
        map_smul' := fun c m => by rw [map_smul, smul_eq_mul, map_mul, smul_eq_mul] }
    have hF : F1 = f.comp r := by
      refine b.ext fun i => ?_
      show WittVector.constantCoeff (l (b i)) = f (r (b i))
      rw [show l (b i) = a i from b.constr_basis _ _ _]
      exact Function.surjInv_eq hσs _
    refine ⟨l, ?_⟩
    ext v
    obtain ⟨m, rfl⟩ := hr v
    rw [hr']
    exact LinearMap.congr_fun hF m
  · intro l
    constructor
    · intro h0
      have hz : ∀ m, WittVector.constantCoeff (l m) = 0 := fun m => by
        rw [← hr', h0, LinearMap.zero_apply]
      choose w hw using fun i => hσker _ (hz (b i))
      refine ⟨b.constr (WittVector p k) w, b.ext fun i => ?_⟩
      rw [LinearMap.smul_apply, b.constr_basis, hw]
    · rintro ⟨l', rfl⟩
      rw [map_nsmul]
      ext v
      rw [LinearMap.smul_apply, hpk, LinearMap.zero_apply]

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.effCartier_comap_of_isIso_restrict_open : ∀ {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Y.IdealSheafData) (U : Y.Opens), IsIso (s ∣_ U) → FinalTheorems.EffCartier (I.comap s) → FinalTheorems.EffCartier (I.comap U.ι) := by
  first | exact @GlobalTheory.effCartier_comap_of_isIso_restrict | exact GlobalTheory.effCartier_comap_of_isIso_restrict | (intros; apply GlobalTheory.effCartier_comap_of_isIso_restrict <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_holo_quadratic_add_levi_isLittleO : ∀ (n : ℕ) (φ : V n → ℝ) (p : V n), ContDiffAt ℝ 2 φ p → ∃ q : V n → ℂ, Differentiable ℂ q ∧ (fun v : V n => φ v - 2 * (q v).re - (leviV n (fun w => ((φ w : ℝ) : ℂ)) p (fun j => (v - p) j)).re) =o[𝓝 p] (fun v : V n => ‖v - p‖ ^ 2) := by
  first | exact @GlobalTheory.TaylorLevi.exists_holo_quadratic_add_levi | exact GlobalTheory.TaylorLevi.exists_holo_quadratic_add_levi | (intros; apply GlobalTheory.TaylorLevi.exists_holo_quadratic_add_levi <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.quotient_jets_fderiv_det_ne_zero : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (p : V n) (w0 : V n → ℂ) (w : Fin n → V n → ℂ), DifferentiableAt ℂ w0 p → (∀ j, DifferentiableAt ℂ (w j) p) → ‖w0 p - 1‖ ≤ ε → ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε → (∀ j, ‖w j p‖ ≤ ε) → (∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε) → w0 p ≠ 0 ∧ (fderiv ℂ (fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n)) p).det ≠ 0 := by
  first | exact @GlobalTheory.quot_jets_det_ne_zero | exact GlobalTheory.quot_jets_det_ne_zero | (intros; apply GlobalTheory.quot_jets_det_ne_zero <;> assumption)
end

section

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.uniform_taylor_bound_levi_pluriharmonic_split : ∀ (n : ℕ) (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, closedBall z δ ⊆ U ∧ ∃ h : V n → ℂ, Differentiable ℂ h ∧ h 0 = 0 ∧ ∀ w ∈ closedBall (0 : V n) δ, φ (z + w) ≤ φ z + 2 * (h w).re + (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re + η * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.PluriTaylor.taylor_levi_unif | exact GlobalTheory.PluriTaylor.taylor_levi_unif | (intros; apply GlobalTheory.PluriTaylor.taylor_levi_unif <;> assumption)
end

section

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.truncatedGaussianIntegral_uniform_posSemidef : ∀ (n : ℕ) (C ε : ℝ), 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop, ∀ H : Matrix (Fin n) (Fin n) ℂ, H.PosSemidef → (∀ j l, ‖H j l‖ ≤ C) → 1 ≤ (H.det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ, Real.exp (-(m * ((∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re + η * ‖w‖ ^ 2))) := by
  first | exact @GlobalTheory.TruncGauss.trunc_gauss | exact GlobalTheory.TruncGauss.trunc_gauss | (intros; apply GlobalTheory.TruncGauss.trunc_gauss <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.lintegral_nsq_canonical_add_chart_part : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (i : ι) (W : Set (V n)) (D : ι → Y → ℂ), MeasurableSet W → W ⊆ (A.chart i).target → (∀ y ∈ (A.chart i).source, A.chart i y ∈ W → D (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D i y) → AEMeasurable (D i ∘ (A.chart i).symm) (volume.restrict W) → ∫⁻ y in (A.chart i).source ∩ A.chart i ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu = ∫⁻ v in W, ENNReal.ofReal (‖D i ((A.chart i).symm v)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm v))) := by
  first | exact @GlobalTheory.OTY.lintegral_nsq_chart_part | exact GlobalTheory.OTY.lintegral_nsq_chart_part | (intros; apply GlobalTheory.OTY.lintegral_nsq_chart_part <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_linComb_sections_ne_zero_on_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (N : ℕ) (s : Fin N → ι → Y → ℂ) (T : Finset Y), (∀ k, A.IsSec L (s k)) → (∀ P ∈ T, P ∉ A.zeroSet s) → ∃ s' : ι → Y → ℂ, A.IsSec L s' ∧ (∀ P ∈ T, s' (A.pick P) P ≠ 0) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq L s' y ≤ C * A.sqn L s y := by
  first | exact @GlobalTheory.OTY.exists_linComb_ne_zero_on_finset | exact GlobalTheory.OTY.exists_linComb_ne_zero_on_finset | (intros; apply GlobalTheory.OTY.exists_linComb_ne_zero_on_finset <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_finite_disjoint_meeting_every_component : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ S : Set Y, S.Finite → ∃ T : Set Y, T.Finite ∧ Disjoint T S ∧ ∀ y, ∃ P ∈ T, P ∈ connectedComponent y := by
  first | exact @GlobalTheory.OTY.exists_finite_disjoint_meets_components | exact GlobalTheory.OTY.exists_finite_disjoint_meets_components | (intros; apply GlobalTheory.OTY.exists_finite_disjoint_meets_components <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ChartGraph

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def chartMatrixTopBlock (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  (mat (nmat X z) τ).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le)

def chartBottomLeftBlock (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
  (mat (nmat X z) τ).submatrix (fun m => ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩)
    (Fin.castLE X.p0_le)

def graphCoord (X : Data E r) (z : V (nd X)) : X.Coord := fun τ => chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹

end GlobalTheory.ChartGraph
end
end
