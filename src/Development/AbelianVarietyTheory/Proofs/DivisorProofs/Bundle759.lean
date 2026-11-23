module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle543
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle711
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle721
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle722
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle718
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.StrictHensPrime

theorem exists_sh_indEt (A : Type) [CommRing A] (p : Ideal A) [p.IsPrime] :
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra A O) (_ : IsLocalRing O), SH O ∧ IndEt A O ∧
      (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p := by
  classical
  obtain ⟨S, _, _, hH, hloc, hsep, -, -, -, ι, _, _, _, Si, hmono, hcov, hSi⟩ :=
    GlobalTheory.exists_strictHenselisation (Localization.AtPrime p)
      (SeparableClosure (IsLocalRing.ResidueField (Localization.AtPrime p)))
  let _ : Algebra A S := ((algebraMap (Localization.AtPrime p) S).comp
    (algebraMap A (Localization.AtPrime p))).toAlgebra
  have _ : IsScalarTower A (Localization.AtPrime p) S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hI : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Localization.AtPrime p) S) := by
    refine GlobalTheory.StrictHensUnion.indEtale_of_directed_union _ S ι Si hmono hcov fun i => ?_
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi i
    exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
      (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale _ B q.primeCompl)
  refine ⟨S, inferInstance, inferInstance, inferInstance, ⟨hH, hsep⟩, ?_, ?_⟩
  · exact IndEtaleAtPrime.indEt_of_indEt_atPrime A S p hI
  · rw [IsScalarTower.algebraMap_eq A (Localization.AtPrime p) S, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal

end GlobalTheory.StrictHensPrime

end
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_isBundle : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → IsBundle k x fun I => (omB k K (rB k K x I) p).comap (e.restrictScalars k) := by
  intro k _ _ F K _ _ _ _ _ _ d x hx p W _ _ _ _ _ _ _ e he hr
  have hstab : ∀ I, ∀ c ∈ rB k K x I, ∀ w ∈ ((omB k K (rB k K x I) p).comap (e.restrictScalars k) : Set W),
      (c : K) • w ∈ ((omB k K (rB k K x I) p).comap (e.restrictScalars k) : Set W) := by
    intro I c hc w hw
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hw ⊢
    rw [map_smul]
    exact ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K _ p p).2.1 _ hw).2.2.2 c hc
  have key : ∀ i, Module.Finite (rA k x {i}) (Submodule.span (rA k x {i})
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)) ∧
      Module.Projective (rA k x {i}) (Submodule.span (rA k x {i})
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)) := by
    intro i
    obtain ⟨hf1, hf2, hf3⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hx {i} (Finset.singleton_nonempty i)
    haveI := hf2
    haveI := hf3
    obtain ⟨hB1, hB2⟩ := GlobalTheory.T.span_regularForms_finite_projective_smooth k K (rB k K x {i}) p W e he hr
    exact GlobalTheory.T.finite_projective_span_of_integralClosure' k F K (rA k x {i}) (rB k K x {i}) (fun y => Iff.rfl) hf1 (GlobalTheory.T.integralClosure_projective_over_standardOpenRing k F K d x hx i) W _
      (hstab {i}) hB1 hB2
  refine ⟨fun i => ?_, fun i => (key i).2, fun I i hi => GlobalTheory.T.pulledBackForms_intersection_eq_chart_localization k F K d x hx p W e I i hi⟩
  obtain ⟨hfin, -⟩ := key i
  obtain ⟨-, hf2, -⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hx {i} (Finset.singleton_nonempty i)
  haveI := hf2
  haveI : FiniteDimensional F K := hx.fin
  set S : Set W := ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W) with hSdef
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hfin
  have hA : ∀ a : rA k x {i}, ∀ w ∈ S, a • w ∈ S := by
    intro a w hw
    rw [Subalgebra.smul_def, ← algebraMap_smul K (a : F) w]
    exact hstab {i} _ (Subalgebra.algebraMap_mem (integralClosure (rA k x {i}) K) a) w hw
  have hspan : (Submodule.span (rA k x {i}) S).restrictScalars k =
      (omB k K (rB k K x {i}) p).comap (e.restrictScalars k) := by
    apply le_antisymm
    · intro y hy
      change y ∈ Submodule.span (rA k x {i}) S at hy
      change y ∈ S
      induction hy using Submodule.span_induction with
      | mem z hz => exact hz
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul a z _ hz => exact hA a z hz
    · exact fun y hy => Submodule.subset_span hy
  refine ⟨s, by rw [hs, hspan], ?_⟩
  have hK := GlobalTheory.T.kahlerFormsOverSubalgebra_comap_span_eq_top k K (rB k K x {i}) p W e he hr
  have hF := GlobalTheory.T.span_eq_top_of_stable_of_isFractionRing' k F K (rB k K x {i}) W S (hstab {i}) hK
  rw [eq_top_iff, ← hF, Submodule.span_le]
  intro w hw
  have : w ∈ Submodule.span (rA k x {i}) (s : Set W) := by rw [hs]; exact Submodule.subset_span hw
  exact Submodule.span_le_restrictScalars (rA k x {i}) F (s : Set W) this

end GlobalTheory.PD
end
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open Filter Topology

namespace GlobalTheory.KSp.ParNear

variable {E : Type} [Field E] {ν : Type} [Fintype ν] [DecidableEq ν]

theorem toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero (M N : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (h : N.toBlocks₂₁ = 0) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, h, fromBlocks_multiply]
  simp

theorem toBlocks₁₁_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₁ = 1 := by
  ext i j; simp [toBlocks₁₁, Matrix.one_apply]

theorem toBlocks₁₂_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₂ = 0 := by
  ext i j; simp [toBlocks₁₂, one_apply]

variable {F : Type} [Field F] [Algebra F E] (c : E →ₐ[F] E) {α : Type} [Fintype α] [DecidableEq α]

theorem mat_one : mat c (1 : UG c (stdJ ν E)) = 1 := rfl

theorem mat_mul_mat_inv (g : UG c (stdJ ν E)) : mat c g * mat c g⁻¹ = 1 := by
  change (((g * g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
  rw [mul_inv_cancel]; rfl

theorem pr_zero_right (Q : Matrix α α E) (x : Matrix α ν E) : pr c Q x 0 = 0 := by
  simp [pr, form, GlobalTheory.WeilM.hTens]

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E]

theorem continuous_mat : Continuous fun g : UG c (stdJ ν E) => mat c g :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mat_inv : Continuous fun g : UG c (stdJ ν E) => mat c g⁻¹ :=
  Units.continuous_coe_inv.comp continuous_subtype_val

theorem continuous_pr (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E) :
    Continuous fun p : Matrix α ν E × Matrix α ν E => pr c Q p.1 p.2 := by
  simp only [pr, form, GlobalTheory.WeilM.hTens]
  refine continuous_const.mul (htr.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_))
  refine Continuous.mul (Continuous.mul (Continuous.mul ?_ continuous_const) continuous_const) (hc.comp ?_)
  · rcases j with j | j
    · exact continuous_fst.matrix_elem i j
    · exact continuous_const
  · rcases l with l | l
    · exact continuous_const
    · exact continuous_snd.matrix_elem k l

theorem continuous_pr_comp (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E)
    {X : Type} [TopologicalSpace X] {f g : X → Matrix α ν E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => pr c Q (f x) (g x) := by
  have h := (continuous_pr (ν := ν) c hc htr Q).comp (hf.prodMk hg)
  exact h

end GlobalTheory.KSp.ParNear

theorem GlobalTheory.KSp.parFun_fixed_near_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), ∀ φ ∈ SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → parFun c ψ χ Q (mat c g) φ = φ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ hψ _ _ χ hχ _ φ hφ
  obtain ⟨-, htop, -, -, hcc, -, htr, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := htop
  haveI := GlobalTheory.WeilM.nonarch_field F
  have hψl := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ
  have hφl : IsLocallyConstant φ := hφ.1
  have hK : IsCompact (tsupport φ) := hφ.2
  have hA : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _
  have hB : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₂ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _
  have hA' : Continuous fun g : UG c (stdJ ν E) => (mat c g⁻¹).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat_inv c).matrix_elem _ _

  have hi : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), sc F χ (Fintype.card α) (mat c g).toBlocks₁₁.det = 1 := by
    have ht : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁.det) (𝓝 1) (𝓝 1) := by
      have := hA.matrix_det.tendsto 1
      rwa [GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', det_one] at this
    exact ht.eventually (GlobalTheory.T.unitaryCharacterAbsScalar_eventually_eq_one F E c δ hE _ χ hχ)

  have hii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ x ∈ tsupport φ,
      ψ (2⁻¹ * pr c Q (x * (mat c g).toBlocks₁₁) (x * (mat c g).toBlocks₁₂)) * φ (x * (mat c g).toBlocks₁₁) = φ x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have hP : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E =>
        pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      GlobalTheory.KSp.ParNear.continuous_pr_comp c hcc htr Q (continuous_snd.matrix_mul (hA.comp continuous_fst))
        (continuous_snd.matrix_mul (hB.comp continuous_fst))
    have hP2 : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E =>
        (2 : F)⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      continuous_const.mul hP
    have h1 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E =>
        ψ (2⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂)) :=
      hψl.comp_continuous hP2
    have h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h1.eventually_eq (1, x), h2.eventually_eq (1, x), h3.eventually_eq (1, x)] with p e1 e2 e3
    rw [e1, e2, e3, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', GlobalTheory.KSp.ParNear.toBlocks₁₂_one', Matrix.mul_one, Matrix.mul_zero,
      GlobalTheory.KSp.ParNear.pr_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul]

  have hiii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ y ∈ tsupport φ, φ (y * (mat c g⁻¹).toBlocks₁₁) = φ y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1⁻¹).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA'.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h2.eventually_eq (1, y), h3.eventually_eq (1, y)] with p e2 e3
    rw [e2, e3, inv_one, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', Matrix.mul_one]
  filter_upwards [hi, hii, hiii] with g hg1 hg2 hg3 hg
  have hinv : (mat c g).toBlocks₁₁ * (mat c g⁻¹).toBlocks₁₁ = 1 := by
    rw [← GlobalTheory.KSp.ParNear.toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero _ _ ((GlobalTheory.KSp.mem_sieg c).mp ((sieg c ν).inv_mem hg)),
      GlobalTheory.KSp.ParNear.mat_mul_mat_inv, GlobalTheory.KSp.ParNear.toBlocks₁₁_one']
  funext x
  simp only [parFun]
  rw [hg1, one_mul]
  by_cases hx : x ∈ tsupport φ
  · exact hg2 x hx
  · rw [image_eq_zero_of_notMem_tsupport hx]
    by_contra hne
    have hne' : φ (x * (mat c g).toBlocks₁₁) ≠ 0 := right_ne_zero_of_mul hne
    have hy : x * (mat c g).toBlocks₁₁ ∈ tsupport φ := subset_tsupport _ hne'
    have e := hg3 _ hy
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one] at e
    exact hx (subset_tsupport _ (by rw [Function.mem_support, e]; exact hne'))
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem weil_heis_intertwine : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E), Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hη _ _ μ _ κ ω hK
  let U : Subgroup (UG c (stdJ ν E)) :=
    { carrier := {g | ∀ w : Matrix α (ν ⊕ ν) E, Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * mat c g)}
      one_mem' := by
        intro w
        have h1 : mat c (1 : UG c (stdJ ν E)) = 1 := rfl
        rw [map_one, h1, Matrix.mul_one, mul_one, one_mul]
      mul_mem' := by
        intro g h hg hh w
        have hm : mat c (g * h) = mat c g * mat c h := rfl
        rw [map_mul, ← mul_assoc, hg, mul_assoc, hh, ← mul_assoc, hm, Matrix.mul_assoc]
      inv_mem' := by
        intro g hg w
        have h1 : mat c g⁻¹ * mat c g = 1 := by
          change (((g⁻¹ * g : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
          rw [inv_mul_cancel]; rfl
        have h2 := hg (w * mat c g⁻¹)
        rw [Matrix.mul_assoc, h1, Matrix.mul_one] at h2
        have h3 : ω g⁻¹ * ω g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have h4 : ω g * ω g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        show Heisenberg₂ c hψ Q w * ω g⁻¹ = ω g⁻¹ * Heisenberg₂ c hψ Q (w * mat c g⁻¹)
        calc Heisenberg₂ c hψ Q w * ω g⁻¹ = ω g⁻¹ * (ω g * Heisenberg₂ c hψ Q w) * ω g⁻¹ := by
              simp only [← mul_assoc, h3, one_mul]
          _ = ω g⁻¹ * (Heisenberg₂ c hψ Q (w * mat c g⁻¹) * ω g) * ω g⁻¹ := by rw [h2]
          _ = ω g⁻¹ * Heisenberg₂ c hψ Q (w * mat c g⁻¹) := by simp only [mul_assoc, h4, mul_one] }
  have hsieg : sieg c ν ≤ U := by
    intro p hp w
    refine LinearMap.ext fun φ => Subtype.ext ?_
    simp only [Module.End.mul_apply, heis_apply, hK.par p hp]
    exact GlobalTheory.T.siegelParabolic_operators_heisenberg_compat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hη p hp w φ
  have hweyl : weyl c ν ∈ U := by
    intro w
    refine LinearMap.ext fun φ => Subtype.ext ?_
    simp only [Module.End.mul_apply, heis_apply, hK.wey]
    have hs : ∀ f : Matrix α ν E → ℂ, heisFun c ψ Q w (κ • f) = κ • heisFun c ψ Q w f := by
      intro f; funext x; simp only [heisFun, Pi.smul_apply, smul_eq_mul]; ring
    rw [hs, GlobalTheory.T.fourier_intertwines_weyl_heisenberg_schrodinger F E c δ hE α ν Q hQ ψ μ w φ]
    rfl
  have hU := GlobalTheory.T.siegelParabolic_weylElement_generate_unitary F E c δ hE ν U hsieg hweyl
  intro g w
  have hg : g ∈ U := hU ▸ Subgroup.mem_top g
  exact hg w

end GlobalTheory.KSp
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.isCMTypeOfEmbeddings_card_eq_finrank : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2), Fintype.card I = Module.finrank K E := by
  first | exact @GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType | exact GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType | (intros; apply GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType <;> assumption)
end

section

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.level_quotient_module_surjection : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    ∃ g : D.La →+ (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r), Function.Surjective g ∧
      (∀ (c : 𝓞 D.F) (x : D.La), g (algebraMap (𝓞 D.F) D.O c • x) = Ideal.Quotient.mk (w0 ^ r) c • g x) ∧
      ∀ x, g x = 0 ↔ x ∈ GlobalTheory.UPel.HT.EtLev.wSub D w0 r := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.latQuot_free) | (exact GlobalTheory.UPel.HT.EtLev.latQuot_free) | (intros; apply GlobalTheory.UPel.HT.EtLev.latQuot_free <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cocyclePullback_iff_preimage_affineHom : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) [IsAffineHom φ], (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x ↔ ∃ c : Z1 (OPre φ s'), (∀ U V (a : U ⟶ V), c.1 U V a = preα φ s s' V (f U V a)) ∧ GlobalTheory.CatCoh.H1.mk _ c = (preRes φ s').pull1 x) ∧ (∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z ↔ ∃ c : Z2 (OPre φ s'), (∀ U V W (a : U ⟶ V) (b : V ⟶ W), c.1 U V W a b = preα φ s s' W (v U V W a b)) ∧ GlobalTheory.CatCoh.H2.mk _ c = (preRes φ s').pull2 z) ∧ (∀ y, (preRes φ s').pull1 (pullHO1 h y) = (preCoef h).pull1 y) ∧ ∀ y, (preRes φ s').pull2 (pullHO2 h y) = (preCoef h).pull2 y := by
  first | exact @GlobalTheory.AbCoh.red_iff_pre | exact GlobalTheory.AbCoh.red_iff_pre | (intros; apply GlobalTheory.AbCoh.red_iff_pre <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.surjective_deformation_affine_sections : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) [IsAffineHom φ] [IsAffineHom φ₀], SmallExt t σ σ₀ → Flat s → ∀ U : AffOp X, Function.Surjective (preα φ s s' U) ∧ (∀ b, preα φ s s' U b = 0 ↔ ∃ c, b = t • c) ∧ Function.Surjective (preα φ₀ s s₀ U) ∧ ∀ b : (OAff s).obj U, preα φ₀ s s₀ U b = 0 ↔ t • b = 0 := by
  first | exact @GlobalTheory.AbCoh.preα_surjective_and_ker | exact GlobalTheory.AbCoh.preα_surjective_and_ker | (intros; apply GlobalTheory.AbCoh.preα_surjective_and_ker <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonempty_structureSheafCohomologyModel_of_quasiIso : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C), (∀ (S : Type) [CommRing S] [Algebra R S], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R S)).mapHomologicalComplex _).map φ)) → Model s C → Nonempty (Model s K) := by
  first | exact @GlobalTheory.AbCoh.nonempty_model_of_quasiIso | exact GlobalTheory.AbCoh.nonempty_model_of_quasiIso | (intros; apply GlobalTheory.AbCoh.nonempty_model_of_quasiIso <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.connectionCurvatureSumWedge_semilinearPullback : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (x : HO1 s) (n : ℕ) (u v : Fin n → GlobForm s), ObRel (OAff s) x u v → ObRel (OAff s') (pullHO1 h x) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  first | exact @GlobalTheory.AbCoh.obRel_pullHO1 | exact GlobalTheory.AbCoh.obRel_pullHO1 | (intros; apply GlobalTheory.AbCoh.obRel_pullHO1 <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.structureSheafCohomology_basis_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (P : Type) [Preorder P] (G : P → X.affineOpens) (hG : Monotone G), (∀ (U : X.affineOpens) (x : X), x ∈ U.1 → ∃ a, x ∈ (G a).1 ∧ (G a).1 ≤ U.1) → (∀ (a b : P) (x : X), x ∈ (G a).1 → x ∈ (G b).1 → ∃ c, c ≤ a ∧ c ≤ b ∧ x ∈ (G c).1) → Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull2 ∧ (CohomZeroIsConstants (OAff s) → CohomZeroIsConstants (hG.functor.op ⋙ OAff s)) := by
  first | exact @GlobalTheory.AbCoh.cohO_basis_bijective | exact GlobalTheory.AbCoh.cohO_basis_bijective | (intros; apply GlobalTheory.AbCoh.cohO_basis_bijective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank : ∀ (R : Type) [CommRing R] (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ), FP R M n → FP R N n → ∀ (f : M →ₗ[R] N) (r : N →ₗ[R] M), (∀ x, r (f x) = x) → Function.Bijective f := by
  first | exact @GlobalTheory.AbCoh.bijective_of_split_of_FP | exact GlobalTheory.AbCoh.bijective_of_split_of_FP | (intros; apply GlobalTheory.AbCoh.bijective_of_split_of_FP <;> assumption)
end
