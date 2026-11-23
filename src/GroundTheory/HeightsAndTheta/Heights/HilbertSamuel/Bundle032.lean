module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralClosureFinite
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenerationOfH1GenAmple.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsMultiHomogIdeal V → H1GenAmple S V N →
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → KH.GeneratedV S V (e + c • N)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ κ, Fintype (ι κ)] {Ω : Type} [Field Ω]

noncomputable def expo (d : K → ℕ) : K →₀ ℕ := Finsupp.equivFunOnFinite.symm d

@[simp] theorem coe_expo (d : K → ℕ) : ⇑(expo d) = d := Finsupp.coe_equivFunOnFinite_symm d

theorem mapDomain_fst_apply (μ : (Σ κ, ι κ) →₀ ℕ) (κ : K) :
    μ.mapDomain Sigma.fst κ = ∑ i, μ ⟨κ, i⟩ := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_sigma]
  simp [Finsupp.single_apply]


omit [Fintype K] [∀ κ, Fintype (ι κ)] in
theorem mConeMap_monomial (y : (Σ κ, ι κ) → Ω) (μ : (Σ κ, ι κ) →₀ ℕ) (r : ℤ) :
    mConeMap y (monomial μ r) = monomial (μ.mapDomain Sigma.fst) (aeval y (monomial μ r)) := by
  rw [mConeMap, aeval_monomial, aeval_monomial, monomial_eq,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mConeMap_of_homog (y : (Σ κ, ι κ) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = monomial (expo d) (aeval y g) := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]

  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [mConeMap_monomial]
  have hμd : μ.mapDomain Sigma.fst = expo d := by
    ext κ
    rw [mapDomain_fst_apply, coe_expo, hg μ hμ κ]
  rw [hμd]

def formRing (y : (Σ κ, ι κ) → Ω) : Subalgebra ℤ (MvPolynomial K Ω) where
  carrier := {F | ∀ m : K →₀ ℕ, AddMonoidAlgebra.coeff F m ∈ secM y ⇑m}
  mul_mem' := by
    classical
    intro F G hF hG m
    rw [coeff_mul]
    refine sum_mem fun x hx => ?_
    have hm : ⇑x.1 + ⇑x.2 = ⇑m := by rw [← Finsupp.coe_add, (Finset.HasAntidiagonal.mem_antidiagonal.mp hx)]
    rw [← hm]
    exact secM_mul_mem y (hF x.1) (hG x.2)
  add_mem' := by
    intro F G hF hG m
    rw [MvPolynomial.coeff_add]
    exact add_mem (hF m) (hG m)
  algebraMap_mem' := by
    classical
    intro n m
    rw [MvPolynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      have h1 : (1 : Ω) ∈ secM y ⇑(0 : K →₀ ℕ) :=
        Submodule.subset_span ⟨1, ProjLine.isMultiHomog_one, map_one _⟩
      have := zsmul_mem h1 n
      simpa using this
    · exact zero_mem _

theorem mConeMap_mem_formRing (y : (Σ κ, ι κ) → Ω) (f : MRing ι) : mConeMap y f ∈ formRing y := by
  classical
  induction f using MvPolynomial.induction_on with
  | C n =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ n
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp fun m => ?_
    rw [mConeMap, aeval_X, coeff_C_mul, coeff_X]
    split_ifs with h
    · subst h
      refine Submodule.subset_span ⟨X q, ?_, by simp⟩
      convert ProjLine.isMultiHomog_X (ι := ι) q using 1
      funext κ
      simp [Finsupp.single_apply, eq_comm]
    · simp

theorem monomial_mem_range (y : (Σ κ, ι κ) → Ω) {d : K → ℕ} {v : Ω} (hv : v ∈ secM y d) :
    monomial (expo d) v ∈ (mConeMap y).range := by
  change v ∈ Submodule.span ℤ _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g, mConeMap_of_homog y hg⟩
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul n x _ hx => rw [map_zsmul]; exact zsmul_mem hx n

theorem proof (h : KH.CondStatement) : NmSectionsFinite.Statement := by
  unfold NmSectionsFinite.Statement
  intro K _ ι _ Ω _ y a ha hy hbir τ₂
  classical
  obtain ⟨k, c, -, hc0, hc⟩ := h K ι Ω y a ha hy hbir
  set R := (mConeMap y).range
  have : IsNoetherianRing R :=
    isNoetherianRing_of_surjective (MRing ι) R (mConeMap y).rangeRestrict.toRingHom
      (mConeMap y).rangeRestrict_surjective

  set G : Set (MvPolynomial K Ω) := {F | ∃ τ, τ₂ ≤ τ ∧ ∃ s ∈ chartLatNm y (fun κ => (a κ : ℤ)) τ,
    F = monomial (expo fun κ => τ * a κ) s}
  set u : MvPolynomial K Ω := monomial (expo fun κ => k * a κ) (aeval y c)
  have hinj : Function.Injective (LinearMap.mulLeft R u) := by
    intro F F' hF
    simp only [LinearMap.mulLeft_apply] at hF
    exact mul_left_cancel₀ (by simpa [u] using hc0) hF
  have hmap : (Submodule.span R G).map (LinearMap.mulLeft R u) ≤ Submodule.span R {1} := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨F, ⟨τ, -, s, hs, rfl⟩, rfl⟩
    rw [LinearMap.mulLeft_apply, monomial_mul]
    have hdeg : expo (fun κ => k * a κ) + expo (fun κ => τ * a κ) = expo fun κ => (τ + k) * a κ := by
      ext κ; simp; ring
    rw [hdeg]
    obtain ⟨g, hg⟩ := monomial_mem_range y (hc τ s hs)
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨⟨_, g, rfl⟩, by rw [Subalgebra.smul_def, smul_eq_mul, mul_one]; exact hg⟩
  have hfg : (Submodule.span R G).FG := by
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have := isNoetherian_of_fg_of_noetherian (Submodule.span R {(1 : MvPolynomial K Ω)})
      (Submodule.fg_span_singleton 1)
    exact isNoetherian_submodule.mp inferInstance _ hmap
  obtain ⟨t, htG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
  choose d hd e he hte using fun j : t => htG j.2
  refine ⟨t, inferInstance, d, e, max τ₂ (Finset.univ.sup d), fun j => ⟨hd j,
    le_max_of_le_right (Finset.le_sup (Finset.mem_univ j)), he j⟩, ?_⟩
  intro τ hτ s hs
  have hdτ : ∀ j, d j ≤ τ := fun j =>
    le_trans (le_max_of_le_right (Finset.le_sup (Finset.mem_univ j))) hτ
  have hmem : monomial (expo fun κ => τ * a κ) s ∈ Submodule.span R (t : Set (MvPolynomial K Ω)) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨τ, le_trans (le_max_left _ _) hτ, s, hs, rfl⟩
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hmem
  have hR : ∀ F, ((f F : R) : MvPolynomial K Ω) ∈ formRing y := by
    intro F
    obtain ⟨g, hg⟩ := (f F).2
    rw [← hg]
    exact mConeMap_mem_formRing y g
  refine ⟨fun j => AddMonoidAlgebra.coeff ((f j : R) : MvPolynomial K Ω) (expo fun κ => (τ - d j) * a κ), fun j => ?_, ?_⟩
  · simpa using hR j (expo fun κ => (τ - d j) * a κ)
  · have hc' := congrArg (AddMonoidAlgebra.coeff · (expo fun κ => τ * a κ)) hf
    rw [coeff_monomial, if_pos rfl] at hc'
    rw [← hc', coeff_sum, ← Finset.sum_coe_sort t]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul]
    set p := ((f j : R) : MvPolynomial K Ω)
    rw [hte j]
    rw [coeff_mul_monomial', if_pos]
    · congr 2
      ext κ
      simp [Nat.sub_mul]
    · intro κ
      simpa using Nat.mul_le_mul_right (a κ) (hdτ j)

end NmSectionsFinite

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

noncomputable section

namespace IntegralAgainstPositive

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem finsum_nonpos_of {α : Sort*} {f : α → ℝ} (h : ∀ x, f x ≤ 0) : ∑ᶠ x, f x ≤ 0 := by
  have h0 : 0 ≤ ∑ᶠ x, -f x := finsum_nonneg fun x => neg_nonneg.2 (h x)
  rw [finsum_neg_distrib] at h0
  exact neg_nonneg.1 h0


omit [∀ k, Fintype (ι k)] in
theorem isOpen_blocksNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem isConeTangent_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P) (ξ : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hpts] with w hw
    exact hw.2 f (hP0 hf)
  have hd := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (γ y)).comp y
    hγ.differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun T => T ξ) (hd.unique h0)
  simpa [smul_eq_mul] using this

theorem maDensity_nonneg_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {L : Fin e → HermLine ι} (hsp : ∀ j, IsSemipositiveRel P0 P (L j))
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun j y' => Real.log ((L j).h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun j => ?_
  have hh : ContDiffAt ℝ 2 (L j).h (γ y) :=
    ((hsp j).1.contDiffAt (isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log ((L j).h z)) (γ y) :=
    hh.log ((L j).pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log ((L j).h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log ((L j).h z)) ξ hA hlog
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log ((L j).h z)) ∘ γ) y ξ
  rw [hl]
  exact (hsp j).2 _ hy _ (isConeTangent_of_sheet hP0 hA hpts ξ)

theorem proof : IntegralAgainstPositive.Statement := by
  intro K _ ι _ P P0 e L g hP0 hsp hg
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine integral_nonpos fun y => ?_
    have key : ∀ w, sheetDensity P hΨ.choose (pot L) g y w ≤ 0 := by
      intro w
      unfold sheetDensity
      split_ifs with hγ
      · have hsh := hγ.choose_spec
        have hz : hγ.choose y ∈ mcPts P := hsh.2.self_of_nhds.2.1
        exact mul_nonpos_of_nonpos_of_nonneg (hg _ hz) (maDensity_nonneg_of_sheet hP0 hsp hsh)
      · exact le_rfl
    exact finsum_nonpos_of fun w => finsum_nonpos_of fun _ => key w
  · exact le_rfl

end IntegralAgainstPositive

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

theorem SmallPacking.proof (hR : NmSectionsRankBound.Statement) (hS : SmallSectionsSeparated.Statement) :
    SmallPacking.Statement := by
  classical
  intro K _ ι _ Ω _ y D A La hX hB hA hLa
  obtain ⟨hfin, C₁, hC₁, hrank⟩ := hR K ι Ω y D A.a hX hB
  obtain ⟨C, hC, hsep⟩ := hS K ι Ω y D A hX hB hA
  have key : ∀ (τ : ℕ) (T : Finset (La τ)), (∀ s ∈ T, IsSmallH (mCoordIdeal y) y A τ (s : Ω)) →
      Real.log T.card ≤ C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3) := by
    intro τ T hT
    obtain ⟨Z, ev, hZ, hrep, hsepτ⟩ := hsep τ
    have hpos : ∀ z : Z, 0 < A.h z := fun z => A.pos _ (hZ z z.2).1
    let φ : chartLatNm y A.a τ →+ (Z → ℂ) :=
      { toFun := fun s z => ev s z / ((A.h z : ℂ) ^ τ)
        map_zero' := by funext z; simp
        map_add' := by intro s t; funext z; simp [add_div] }
    have hφ : ∀ s z, ‖φ s z‖ = ‖ev s z‖ / A.h z ^ τ := fun s z => by
      simp [φ, norm_pow, abs_of_pos (hpos z)]
    have hnorm : ∀ s : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → ‖φ s‖ ≤ 1 := by
      intro s hs
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun z => ?_
      obtain ⟨dg, dh, g, h, hg, hh, hdeg, heq, hz0, hev⟩ := hrep s z
      have hle := hs dg dh g h z hg hh hdeg heq (hZ z z.2)
      rw [← hev, norm_mul] at hle
      rw [hφ, div_le_one (pow_pos (hpos z) τ)]
      exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.2 hz0)
    have hdist : ∀ s t : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) →
        IsSmallH (mCoordIdeal y) y A τ (t : Ω) → s ≠ t →
        Real.exp (-(C * ((τ : ℝ) + 1))) ≤ ‖φ s - φ t‖ := by
      intro s t hs ht hst
      obtain ⟨z, hz⟩ := hsepτ s t hs ht hst
      refine le_trans ?_ (norm_le_pi_norm (φ s - φ t) z)
      rw [← map_sub φ, hφ, map_sub ev, Pi.sub_apply, le_div_iff₀ (pow_pos (hpos z) τ)]
      exact hz
    let ι' : La τ →+ chartLatNm y A.a τ := AddSubgroup.inclusion (hLa τ)
    have := hfin τ
    let L : Submodule ℤ (Z → ℂ) := LinearMap.range φ.toIntLinearMap
    have hsmall : ∀ s ∈ T, IsSmallH (mCoordIdeal y) y A τ ((ι' s : chartLatNm y A.a τ) : Ω) := hT
    have hinj : Set.InjOn (fun s => φ (ι' s)) T := by
      intro s hs t ht hst
      by_contra hne
      have hne' : ι' s ≠ ι' t := fun h => hne (Subtype.ext (by simpa [ι'] using congrArg Subtype.val h))
      have := hdist _ _ (hsmall s hs) (hsmall t ht) hne'
      simp only at hst
      rw [hst, sub_self, norm_zero] at this
      exact absurd this (not_le.2 (Real.exp_pos _))
    have hP := Packing.proof (Z → ℂ) L (T.image fun s => φ (ι' s)) (C * ((τ : ℝ) + 1)) (by positivity)
      (by intro v hv; obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hv; exact ⟨ι' s, rfl⟩)
      (by intro v hv; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv; exact hnorm _ (hsmall s hs))
      (by
        intro v hv w hw hvw
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hw
        exact hdist _ _ (hsmall s hs) (hsmall t ht) fun h => hvw (by rw [h]))
    rw [Finset.card_image_of_injOn hinj] at hP
    have hL : (Module.finrank ℤ L : ℝ) ≤ Module.finrank ℤ (chartLatNm y A.a τ) := by
      exact_mod_cast LinearMap.finrank_range_le φ.toIntLinearMap
    refine hP.trans (mul_le_mul_of_nonneg_right (hL.trans (hrank τ)) (by positivity))
  have hfinite : ∀ τ, {s : La τ | IsSmallH (mCoordIdeal y) y A τ (s : Ω)}.Finite := by
    intro τ
    by_contra hinf
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (⌈Real.exp (C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3))⌉₊ + 1)
    have h1 := key τ T (fun s hs => hTsub hs)
    rw [hTcard, Real.log_le_iff_le_exp (by positivity)] at h1
    push_cast at h1
    linarith [Nat.le_ceil (Real.exp (C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3)))]
  refine ⟨hfinite, C₁ * (C + Real.log 3), fun τ => ?_⟩
  unfold smallSectionCount
  rw [show Nat.card {s : La τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} = (hfinite τ).toFinset.card from
    Nat.card_eq_card_finite_toFinset (hfinite τ)]
  refine (key τ _ fun s hs => (hfinite τ).mem_toFinset.1 hs).trans ?_
  have h1 : (1 : ℝ) ≤ (τ : ℝ) + 1 := by linarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)]
  have hl : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  calc C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3)
      ≤ C₁ * ((τ : ℝ) + 1) ^ D * ((C + Real.log 3) * ((τ : ℝ) + 1)) := by gcongr; nlinarith
    _ = C₁ * (C + Real.log 3) * ((τ : ℝ) + 1) ^ (D + 1) := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenerationOfH1Vanishing.proof (hU : ClosedPtGenUniform.Statement) (hC : GenNearCover.Statement) :
    GenerationOfH1Vanishing.Statement := by
  intro S _ K _ _ ι _ _ V N hS hH M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨c₂, hc₂⟩ := hH M 𝓜 hfin hgr hV e
  obtain ⟨c₃, hc₃⟩ := hC S K ι V M 𝓜 (fun c => e + c • N) hS hgr hV
    (fun P hP _ => hU S K ι V N hS hH M 𝓜 hfin hgr hV e P hP)
  exact ⟨max c₂ c₃, fun c hc => ⟨hc₂ c (le_of_max_le_left hc), hc₃ c (le_of_max_le_right hc)⟩⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockChainSum.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    (fun n : ℕ => ∑ j ∈ Finset.range n, twoBlockStep x (matAct B x) (n - j - 1) j -
        (I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m' 1) -
          I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m 0)) *
          (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
