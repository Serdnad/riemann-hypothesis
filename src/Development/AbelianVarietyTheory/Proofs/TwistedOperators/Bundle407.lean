module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Aesop.Main
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle375
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle015
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.TwistHatMx

theorem homLat_conj {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (h : Matrix (Fin m) (Fin n) D.host.E) (hh : h ∈ homLat Λ Λ') : q * h * j ∈ homLat M M' := by
  intro y hy
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hq _ (hh _ (hj _ hy))

theorem smul_homLat_conj {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (x : Matrix (Fin m) (Fin n) D.host.E) (hx : x ∈ 𝔪 • homLat Λ Λ') : q * x * j ∈ 𝔪 • homLat M M' := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro c hc h hh
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact Submodule.smul_mem_smul hc (homLat_conj j q hj hq h hh)
  · intro a b ha hb
    rw [Matrix.mul_add, Matrix.add_mul]
    exact Submodule.add_mem _ ha hb

theorem gen_conj {D : D7} {m n m' n' : ℕ} (a : AF D.host.F) (x : Matrix (Fin m) (Fin n) D.host.E) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) :
    rat q * (Matrix.of fun i k => a ⊗ₜ[D.host.F] x i k) * rat j = Matrix.of fun i k => a ⊗ₜ[D.host.F] (q * x * j) i k := by
  have e : ∀ {r s : ℕ} (y : Matrix (Fin r) (Fin s) D.host.E), (Matrix.of fun i k => a ⊗ₜ[D.host.F] y i k) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) • rat y := by
    intro r s y
    ext i k
    simp [rat, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, e, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [rat, Matrix.map_mul]

theorem rat_conj_mem_hatMx {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (x : Mx D m n) (hx : x ∈ hatMx (𝔪 • homLat Λ Λ')) : rat q * x * rat j ∈ hatMx (𝔪 • homLat M M') := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    rw [gen_conj]
    exact AddSubgroup.subset_closure ⟨α, hα, q * y * j, smul_homLat_conj 𝔪 j q hj hq y hy, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Matrix.mul_add, Matrix.add_mul]
    exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha =>
    rw [Matrix.mul_neg, Matrix.neg_mul]
    exact AddSubgroup.neg_mem _ ha

end GlobalTheory.TwistHatMx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LCIntegralField

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

def stab (f : X → ℂ) : AddSubgroup X where
  carrier := {v | ∀ y, f (y + v) = f y}
  zero_mem' := fun y => by simp
  add_mem' := by
    intro a b (ha : ∀ y, f (y + a) = f y) (hb : ∀ y, f (y + b) = f y) y
    show f (y + (a + b)) = f y
    rw [← add_assoc, hb, ha]
  neg_mem' := by
    intro a (ha : ∀ y, f (y + a) = f y) y
    show f (y + -a) = f y
    have := ha (y + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_stab {f : X → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    IsOpen (stab f : Set X) := by
  classical
  have hT : IsCompact (tsupport f) := hc
  haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hT
  have hfin : (f '' tsupport f).Finite := by
    have := (hf.comp_continuous (continuous_subtype_val : Continuous (Subtype.val : tsupport f → X))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at this
  have key : ∀ c ∈ f '' tsupport f, c ≠ 0 → ∀ᶠ v in nhds (0 : X), ∀ y, f y = c → f (y + v) = c := by
    intro c _ hc0
    have hLT : f ⁻¹' {c} ⊆ tsupport f := fun y hy =>
      subset_tsupport f (by rw [Function.mem_support, show f y = c from hy]; exact hc0)
    have hLc : IsCompact (f ⁻¹' {c}) :=
      hT.of_isClosed_subset (isClosed_singleton.preimage hf.continuous) hLT
    obtain ⟨V, hV, hKV⟩ := compact_open_separated_add_right hLc (hf.isOpen_fiber c) subset_rfl
    filter_upwards [hV] with v hv y hy
    exact hKV (Set.add_mem_add hy hv)
  have h1 : ∀ᶠ v in nhds (0 : X), ∀ c ∈ f '' tsupport f, c ≠ 0 → ∀ y, f y = c → f (y + v) = c :=
    (Filter.eventually_all_finite hfin).2 fun c hc => by
      by_cases h0 : c = 0
      · exact Filter.Eventually.of_forall fun _ h => absurd h0 h
      · exact (key c hc h0).mono fun v hv _ => hv
  have h2 := (continuous_neg.tendsto' (0 : X) 0 neg_zero).eventually h1
  refine AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_
  filter_upwards [h1, h2] with v hv hv'
  show ∀ y, f (y + v) = f y
  intro y
  by_cases hy : f y = 0
  · by_contra hne
    have hne' : f (y + v) ≠ 0 := by rw [hy] at hne; exact hne
    have hmem : f (y + v) ∈ f '' tsupport f := ⟨y + v, subset_tsupport f hne', rfl⟩
    have := hv' _ hmem hne' (y + v) rfl
    rw [add_neg_cancel_right] at this
    exact hne this.symm
  · exact hv (f y) ⟨y, subset_tsupport f hy, rfl⟩ hy y rfl

theorem discrete_quot (U : AddSubgroup X) (hU : IsOpen (U : Set X)) : DiscreteTopology (X ⧸ U) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H g =>
    have hpre : (QuotientAddGroup.mk : X → X ⧸ U) ⁻¹' {(g : X ⧸ U)} = (fun x => -g + x) ⁻¹' (U : Set X) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [eq_comm, QuotientAddGroup.eq]
    rw [← (QuotientAddGroup.isQuotientMap_mk (N := U)).isOpen_preimage, hpre]
    exact hU.preimage (continuous_const.add continuous_id)

theorem integral_eq_sum [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant]
    (U : AddSubgroup X) (hU : IsOpen (U : Set X)) (hUfin : μ U ≠ ⊤) (g : X → ℂ)
    (hg : ∀ u ∈ U, ∀ y, g (y + u) = g y) (hc : HasCompactSupport g) :
    ∃ s : Finset X, ∫ y, g y ∂μ = (∑ γ ∈ s, g γ) * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  classical
  haveI := discrete_quot U hU
  have hfin : ((QuotientAddGroup.mk : X → X ⧸ U) '' tsupport g).Finite :=
    (hc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T := hfin.toFinset with hT
  have hind : ∀ (c : X ⧸ U) y, (Quotient.out c : X) = (Quotient.out c : X) →
      (-(Quotient.out c) + y ∈ U ↔ c = (y : X ⧸ U)) := by
    intro c y _
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  have hdec : g = fun y => ∑ c ∈ T,
      ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator (fun _ => g (Quotient.out c)) y := by
    funext y
    have key : ∀ c : X ⧸ U, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator
        (fun _ => g (Quotient.out c)) y = if c = (y : X ⧸ U) then g y else 0 := by
      intro c
      by_cases h : c = (y : X ⧸ U)
      · rw [if_pos h, Set.indicator_of_mem (show y ∈ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from (hind c y rfl).2 h)]
        have hm : -(Quotient.out c) + y ∈ U := (hind c y rfl).2 h
        have := hg _ hm (Quotient.out c)
        rw [add_neg_cancel_left] at this
        exact this.symm
      · rw [if_neg h, Set.indicator_of_notMem (show y ∉ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from fun hm => h ((hind c y rfl).1 hm))]
    simp only [key]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [hT, Set.Finite.mem_toFinset] at hmem
      exact image_eq_zero_of_notMem_tsupport (fun hs => hmem ⟨y, hs, rfl⟩)
  have hmeas : ∀ c : X ⧸ U, MeasurableSet ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) := fun c =>
    (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hvol : ∀ c : X ⧸ U, μ ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) = μ U := fun c =>
    measure_preimage_add μ _ _
  refine ⟨T.image Quotient.out, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)]
  conv_lhs => rw [hdec]
  rw [integral_finsetSum]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_indicator_const _ (hmeas c)]
    simp only [Measure.real, hvol, Complex.real_smul]
    ring
  · intro c _
    refine (integrable_indicator_iff (hmeas c)).2 (integrableOn_const ?_)
    rw [hvol]; exact hUfin

theorem integral_mem_range [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] [T2Space X]
    (μ : Measure X) [μ.IsAddLeftInvariant] (H : Set X) (hHo : IsOpen H) (hHc : IsCompact H) (hH0 : (0 : X) ∈ H)
    (hμH : μ H = 1) {K : Type} [Field K] (σ : K →+* ℂ) (f : X → ℂ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (hv : ∀ e, f e ∈ Set.range σ) : ∫ e, f e ∂μ ∈ Set.range σ := by
  classical
  set h : X → ℂ := H.indicator (fun _ => 1) with hh
  have hloc : IsLocallyConstant h := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ H
    · exact ⟨H, hHo, hx, fun y hy => by rw [hh, Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨Hᶜ, hHc.isClosed.isOpen_compl, hx, fun y hy => by
        rw [hh, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  have hch : HasCompactSupport h := HasCompactSupport.intro hHc fun x hx => Set.indicator_of_notMem hx _
  set U := stab f ⊓ stab h with hU
  have hUo : IsOpen (U : Set X) := by
    rw [hU, AddSubgroup.coe_inf]; exact (isOpen_stab hf hc).inter (isOpen_stab hloc hch)
  have hUH : (U : Set X) ⊆ H := by
    intro u hu
    have h1 := (AddSubgroup.mem_inf.1 hu).2 0
    rw [zero_add] at h1
    by_contra hn
    rw [hh, Set.indicator_of_notMem hn, Set.indicator_of_mem hH0] at h1
    exact zero_ne_one h1
  have hUfin : μ U ≠ ⊤ := ne_top_of_le_ne_top (by rw [hμH]; exact ENNReal.one_ne_top) (measure_mono hUH)
  obtain ⟨s, hs⟩ := integral_eq_sum μ U hUo hUfin f (fun u hu => (AddSubgroup.mem_inf.1 hu).1) hc
  obtain ⟨s', hs'⟩ := integral_eq_sum μ U hUo hUfin h (fun u hu => (AddSubgroup.mem_inf.1 hu).2) hch
  have hint : ∫ y, h y ∂μ = 1 := by
    rw [hh, integral_indicator_const _ hHo.measurableSet]
    simp [Measure.real, hμH]
  rw [hint] at hs'
  have hr := eq_inv_of_mul_eq_one_right hs'.symm
  rw [hs, hr, ← RingHom.coe_fieldRange]
  have hv' : ∀ e, f e ∈ σ.fieldRange := fun e => by rw [← SetLike.mem_coe, RingHom.coe_fieldRange]; exact hv e
  have hh' : ∀ e, h e ∈ σ.fieldRange := fun e => by
    rw [hh, Set.indicator_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  exact mul_mem (sum_mem fun γ _ => hv' γ) (inv_mem (sum_mem fun γ _ => hh' γ))

end GlobalTheory.LCIntegralField

namespace GlobalTheory.LCIntegralField
open GlobalTheory.FunObj ValuativeRel

theorem integral_vars_mem_range : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {G : GlobalTheory.SplitFlip.Grid k} (ν : MeasureTheory.Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ {K : Type} [Field K] (σ : K →+* ℂ) (f : Vars G → ℂ), IsLocallyConstant f → HasCompactSupport f → (∀ e, f e ∈ Set.range σ) → ∫ e, f e ∂(varsVol G ν) ∈ Set.range σ := by
  intro k _ _ _ _ _ _ G ν hν K _ σ f hf hc hv
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI := hν.1
  haveI : (varsVol G ν).IsAddLeftInvariant := by unfold varsVol; infer_instance
  refine integral_mem_range (varsVol G ν) (Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)) ?_ ?_ ?_ ?_
    σ f hf hc hv
  · exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => Model.isOpen_int
  · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  · exact fun _ _ _ _ => zero_mem _
  · simp [varsVol, Measure.pi_pi, hν.2]

end GlobalTheory.LCIntegralField
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}

theorem mulSingle_ne {m : ℕ} (κ : GL (Fin (Γ.rank (0, m))) k) {X : ℕ × ℕ} (h : X ≠ (0, m)) :
    (Pi.mulSingle (0, m) κ : Γ.VertexGroup) X = 1 := Pi.mulSingle_eq_of_ne h _

theorem moveArgs_fill (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (x : ColArgs Γ) (y : RowArgs Γ)
    (e : Vars Γ) :
    Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (fill hs x y e) = fill hs x (Function.update y 0 ((κ⁻¹).val * y 0)) e := by
  funext b
  cases b with
  | theta i j =>
    by_cases h : i = Γ.m
    · subst h
      rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt, hm]), mulSingle_ne κ (by simp [Edge.src, hm])]
      simp [fill]
    · simp [moveArgs, fill, h]
  | ex i j =>
    by_cases hj : j = Γ.m
    · subst hj
      by_cases hi : i = 0
      · subst hi
        rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt]), fill_ex, fill_ex]
        simp only [Edge.src, Pi.mulSingle_eq_same, Function.update_self, map_one, inv_one, Units.val_one, Matrix.one_mul]
        rw [Matrix.transpose_mul, Assignment.read, invT_val]
      · rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt]), mulSingle_ne κ (by simp [Edge.src, hi])]
        simp [fill, Function.update_of_ne hi]
    · simp [moveArgs, fill, hj]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid MeasureTheory

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}

theorem moveArgs_mul (s : Assignment) (g g' : Γ.VertexGroup) (z : Γ.Args) :
    Γ.moveArgs s (g * g') z = Γ.moveArgs s g' (Γ.moveArgs s g z) := by
  funext b
  simp only [moveArgs, Pi.mul_apply, map_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem mulSingle_comm (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (g : Γ.VertexGroup) (hg : g (0, Γ.m) = 1) :
    Pi.mulSingle (0, Γ.m) κ * g = g * Pi.mulSingle (0, Γ.m) κ := by
  funext X
  by_cases h : X = (0, Γ.m)
  · subst h; simp [hg]
  · simp [Pi.mulSingle_eq_of_ne h]

theorem elt_zero_m (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) {J : Γ.Level} (ρ : Reps hs J) (β : Cosets hs J) : ρ.elt β (0, Γ.m) = 1 := by
  simp [Reps.elt, onColumn, Ne.symm hm]

theorem prod_edgeFactor (hm : Γ.m ≠ 0) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod =
      Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) (.ex 0 Γ.m) := by
  have h1 : ∀ b : Edge, b.src ≠ (0, Γ.m) → b.tgt ≠ (0, Γ.m) → Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) b = 1 := by
    intro b hs ht
    simp [edgeFactor, Pi.mulSingle_eq_of_ne hs, Pi.mulSingle_eq_of_ne ht]
  obtain ⟨n, hn⟩ : ∃ n, Γ.m = n + 1 := ⟨Γ.m - 1, by omega⟩
  rw [oppositePath, List.map_append, List.prod_append]
  have h2 : (((List.range Γ.m).reverse.map (Edge.theta Γ.m)).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact h1 _ (by simp [Edge.src, hm]) (by simp [Edge.tgt, hm])
  rw [h2, mul_one]
  have h3 : List.range Γ.m = 0 :: (List.range n).map Nat.succ := by rw [hn, List.range_succ_eq_map]
  rw [h3, List.map_cons, List.map_cons, List.prod_cons]
  have h4 : ((((List.range n).map Nat.succ).map (Edge.ex · Γ.m)).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact h1 _ (by simp [Edge.src]) (by simp [Edge.tgt])
  rw [h4, mul_one]

variable [MeasurableSpace k] [BorelSpace k]

theorem moved_law (keep : Bool) (g : Γ.VertexGroup) (hg : g (0, Γ.m) = 1) (κ : GL (Fin (Γ.rank (0, Γ.m))) k)
    (T : Γ.Args → ℂ) (c : ℂ) (hlaw : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (0, Γ.m) κ) T = c • T) (z : Γ.Args) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod *
      moved Γ keep g T (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) z) = c * moved Γ keep g T z := by
  have h1 := congrFun hlaw (Γ.moveArgs .one g z)
  simp only [pathAct, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : Γ.moveArgs .one g (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) z) =
      Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (Γ.moveArgs .one g z) := by
    rw [← moveArgs_mul, ← moveArgs_mul, mulSingle_comm κ g hg]
  simp only [moved, pathAct, h2]
  calc _ = (if keep then (1 : ℂ) else (((charFactor Γ g)⁻¹ : ℂˣ) : ℂ)) * ((oppositePath Γ.m).map (Γ.edgeFactor .one g)).prod *
        (((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod *
          T (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (Γ.moveArgs .one g z))) := by ring
    _ = _ := by rw [h1]; ring

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid MeasureTheory

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}
  [MeasurableSpace k] [BorelSpace k]

theorem datum_law (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) (ψ : AddChar k Circle) (ν : Measure k) {J : Γ.Level} (keep : Bool)
    (ρ : Reps hs J) (T : Γ.Args → ℂ) (β : Cosets hs J) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (c : ℂ)
    (hlaw : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (0, Γ.m) κ) T = c • T) (x : ColArgs Γ) (y : RowArgs Γ) :
    Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) (.ex 0 Γ.m) *
        (unfTerm ψ ν keep ρ T β).datum x (Function.update y 0 ((κ⁻¹).val * y 0)) =
      c * (unfTerm ψ ν keep ρ T β).datum x y := by
  simp only [unfTerm, flatTensor, flatIntegrand, ← moveArgs_fill hs hm κ x y]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  have h := moved_law keep (ρ.elt β) (elt_zero_m hs hm ρ β) κ T c hlaw (fill hs x y e)
  rw [prod_edgeFactor hm] at h
  simp only
  rw [← mul_assoc, h, mul_assoc]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def kapAt (S : GridChoice W U) (t : T) (w : Pl D.host.E) (k : FinPt G (.grid 0 D.R.m)) :
    GL (Fin ((locGrid G t w).rank (0, D.R.m))) (Kw w) :=
  inBasis (rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (S.B.β 0 D.R.m) w (finG (G.V (.grid 0 D.R.m)) k)

theorem edgeFactor_ne_zero {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Γ : GlobalTheory.SplitFlip.Grid k) (g : Γ.VertexGroup) (b : GlobalTheory.SplitFlip.Edge) : Γ.edgeFactor .one g b ≠ 0 := by
  simp only [GlobalTheory.SplitFlip.Grid.edgeFactor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (GlobalTheory.SplitFlip.apow_ne_zero _ _))
    (GlobalTheory.SplitFlip.apow_ne_zero _ _)

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

theorem prod_update_comp {m : ℕ} {X : Fin m → Type} (F : ∀ i, X i → ℂ) (i₀ : Fin m) (f : X i₀ → X i₀) (ys : ∀ i, X i) :
    ∏ i, Function.update F i₀ (fun y => F i₀ (f y)) i (ys i) = ∏ i, F i (Function.update ys i₀ (f (ys i₀)) i) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : i = i₀
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem sum_update_comp {κ : Type} {m n : ℕ} {X : Fin n → Type} {Y : Fin m → Type} (τ : κ →₀ ℂ) (A : κ → ∀ j, X j → ℂ)
    (B : κ → ∀ i, Y i → ℂ) (i₀ : Fin m) (f : Y i₀ → Y i₀) (xs : ∀ j, X j) (ys : ∀ i, Y i) :
    (τ.sum fun d a' => a' * (∏ j, A d j (xs j)) * ∏ i, Function.update (B d) i₀ (fun y => B d i₀ (f y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, A d j (xs j)) * ∏ i, B d i (Function.update ys i₀ (f (ys i₀)) i) :=
  Finset.sum_congr rfl fun d _ => by beta_reduce; rw [prod_update_comp]

theorem key_cancel (s PE PL P P' : ℂ) (h1 : PE ≠ 0) (h2 : s * PL = PE) (h3 : PE * P' = PL * P) : s * P' = P :=
  mul_left_cancel₀ h1 (by linear_combination s * h3 + P * h2)

end GlobalTheory.FirstRowTermLaw
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_smoothVector_ne_zero_of_discreteSeriesHom : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ (hU : IsSubrep π ⊤) (Φ : homDS M π ⊤), Φ ≠ 0 → ∃ Ψ ∈ GlobalTheory.PRep.smoothPart (finPartDS M hU), Ψ ≠ 0 := by
  first | exact @GlobalTheory.SmoothAvg.exists_smooth_ne_zero | exact GlobalTheory.SmoothAvg.exists_smooth_ne_zero | (intros; apply GlobalTheory.SmoothAvg.exists_smooth_ne_zero <;> assumption)
end
