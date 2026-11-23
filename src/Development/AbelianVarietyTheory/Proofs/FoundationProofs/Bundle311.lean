module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistCoverDesign
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle003
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Aesop.Main
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle095
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.Divisibility.Bundle002
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelLawsCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

instance finite_levelMod : Finite (LevelMod Dw l) := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ (LevelMod Dw l) := Module.Finite.trans (𝓞 E) _
  have hM : (l.M : ℤ) ≠ 0 := by have := l.three_le; omega
  apply Module.finite_of_fg_torsion
  intro q
  refine ⟨⟨(l.M : ℤ), mem_nonZeroDivisors_of_ne_zero hM⟩, ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
  change (l.M : ℤ) • (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a = 0
  rw [natCast_zsmul, ← map_nsmul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Moduli.LevelAction.mem_of_modN l ⟨a, rfl⟩)

instance finite_levelAut : Finite (LevelAut Dw l) :=
  Finite.of_injective (fun g : LevelAut Dw l => (g : LevelMod Dw l → LevelMod Dw l)) DFunLike.coe_injective

theorem frMap_id_iff {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y' ↔ y = y' := by
  obtain ⟨hu, hr, -⟩ := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y
  exact ⟨fun h => hu _ _ hr h, fun h => h ▸ hr⟩

section Laws

variable {G : Type} [Group G] (R : RelFam Xo c G)

variable {R}

end Laws

end General

section Record

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

end Record

end GlobalTheory.LevelLawsCompare
end
end

section

noncomputable section

namespace GlobalTheory.HalfCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level Coeff Moduli)

variable {D : D7}

abbrev badInt (D : D7) : ℕ := D.host.QS * D.host.q * Ideal.absNorm D.host.ccK

theorem exists_prime_under {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ∀ N : ℕ, (N : 𝓞 K) ∈ P.asIdeal ↔ p ∣ N := by
  haveI := P.isPrime
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨ringChar (𝓞 K ⧸ P.asIdeal), CharP.char_is_prime (𝓞 K ⧸ P.asIdeal) _, fun N => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]

theorem mem_of_dvd {R : Type} [CommRing R] {J : Ideal R} {p N : ℕ} (hp : (p : R) ∈ J) (h : p ∣ N) : (N : R) ∈ J := by
  obtain ⟨c, rfl⟩ := h
  push_cast
  exact J.mul_mem_right _ hp

theorem not_mem_of_coprime {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {a b : ℕ}
    (h : Nat.Coprime a b) (hb : (b : 𝓞 K) ∈ P.asIdeal) : (a : 𝓞 K) ∉ P.asIdeal := by
  intro ha
  obtain ⟨p, hp, hP⟩ := exists_prime_under P
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h ((hP a).1 ha) ((hP b).1 hb))

theorem exists_place_of_dvd_absNorm {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (J : Ideal (𝓞 K))
    (h : p ∣ Ideal.absNorm J) : ∃ P : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ P.asIdeal ∧ P.asIdeal ∣ J := by
  obtain ⟨P, hP, hu, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp J h
  have hm : (p : 𝓞 K) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [hu]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨P, hP.isPrime, ?_⟩, hm, hd⟩
  rintro rfl
  exact hp.ne_zero (by simpa using hm)

theorem prime_dvd_absNorm_halfDifferent (D : D7) {p : ℕ} (hp : p.Prime) :
    p ∣ Ideal.absNorm D.host.𝔟 ↔ p ∣ D.host.QS * D.host.q :=
  D.host.prime_dvd_absNorm_half_iff hp

theorem coprime_ccK (D : D7) : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.host.QS * D.host.q) :=
  Nat.Coprime.mul_right D.host.ccK_coprimeS (D.host.ccK_coprime _ (by simp))

theorem ccE_ne_bot (D : D7) : D.host.ccE ≠ ⊥ := fun h =>
  D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)

theorem absNorm_ccK_mem {P : Place D} (h : P.asIdeal ∣ D.host.ccE) :
    ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
  rw [map_natCast] at this
  exact Ideal.le_of_dvd h this

theorem two_q_mem {P : Place D} (h : P.asIdeal ∣ D.host.𝔟) : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  obtain ⟨p, hp, hP⟩ := exists_prime_under P
  exact (hP _).2 ((prime_dvd_absNorm_halfDifferent D hp).1 ((hP _).1 (Ideal.le_of_dvd h (Ideal.absNorm_mem _))))

theorem primeToAA_iff (P : Place D) : PrimeToAA D P ↔ ¬ P.asIdeal ∣ D.host.ccE ∧ ¬ P.asIdeal ∣ D.host.𝔟 := by
  classical
  have hb := D.host.half_ne_bot
  have hc := ccE_ne_bot D
  have hnot : ¬ (P.asIdeal ∣ D.host.ccE ∧ P.asIdeal ∣ D.host.𝔟) := fun h =>
    not_mem_of_coprime P (coprime_ccK D) (two_q_mem h.2) (absNorm_ccK_mem h.1)
  unfold PrimeToAA Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  rw [FractionalIdeal.count_mul _ _ (FractionalIdeal.coeIdeal_ne_zero.2 hc)
    (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)), FractionalIdeal.count_inv,
    FractionalIdeal.count_coe _ _ hc, FractionalIdeal.count_coe _ _ hb]
  rw [← Associates.count_ne_zero_iff_dvd hc P.irreducible, ← Associates.count_ne_zero_iff_dvd hb P.irreducible] at hnot ⊢
  omega

theorem primeToAA_of_not_mem {P : Place D} (h : ((badInt D : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) : PrimeToAA D P :=
  (primeToAA_iff P).2 ⟨fun hc => h (mem_of_dvd (absNorm_ccK_mem hc) (Dvd.intro_left _ rfl)),
    fun hb => h (mem_of_dvd (two_q_mem hb) (Dvd.intro _ rfl))⟩

section Lev

variable {H : ModHost D}

end Lev

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Rec

end GlobalTheory.HalfCompare
end
end

section

open MeasureTheory Filter Set GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AutomorphicL2Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {f : G → ℂ}

theorem integrableOn_rmul (F : L2 Γ μ) (y : G) {s : Set (Quot Γ)} (hs : _root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ s ≠ ⊤) :
    IntegrableOn (fun q => F (rmul Γ y q)) s (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
  (integrableOn_Lp_of_measure_ne_top (R Γ μ y F) (by norm_num) hs).congr (ae_restrict_of_ae (coeFn_R y F))

theorem setIntegral_norm_rmul_le (F : L2 Γ μ) (y : G) {s : Set (Quot Γ)} (hs : _root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ s ≠ ⊤) :
    ∫ q in s, ‖F (rmul Γ y q)‖ ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ ≤
      (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).real s + ∫ q, ‖F q‖ ^ 2 ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
  have h2 : Integrable (fun q => ‖F q‖ ^ 2) (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).1 (Lp.memLp F)
  have h3 : Integrable (fun q => ‖F (rmul Γ y q)‖ ^ 2) (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
    ((measurePreserving_rmul y).integrable_comp h2.1).2 h2
  have h4 : ∫ q, ‖F (rmul Γ y q)‖ ^ 2 ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ = ∫ q, ‖F q‖ ^ 2 ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
    have h := integral_map (μ := _root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) (measurable_rmul (Γ := Γ) y).aemeasurable
      (f := fun q => ‖F q‖ ^ 2) (by rw [(measurePreserving_rmul y).map_eq]; exact h2.1)
    rw [(measurePreserving_rmul y).map_eq] at h
    exact h.symm
  have h1 : IntegrableOn (fun _ => (1 : ℝ)) s (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := integrableOn_const hs
  calc ∫ q in s, ‖F (rmul Γ y q)‖ ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ
      ≤ ∫ q in s, (1 + ‖F (rmul Γ y q)‖ ^ 2) ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ :=
        integral_mono (integrableOn_rmul F y hs).norm (Integrable.add h1 h3.integrableOn) fun q => by
          beta_reduce
          nlinarith [sq_nonneg (‖F (rmul Γ y q)‖ - 1), norm_nonneg (F (rmul Γ y q))]
    _ = (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).real s + ∫ q in s, ‖F (rmul Γ y q)‖ ^ 2 ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
        rw [integral_add h1 h3.integrableOn]
        simp
    _ ≤ _ := by
        rw [← h4]
        exact add_le_add le_rfl (setIntegral_le_integral h3 (.of_forall fun q => by positivity))

variable [SigmaFinite μ]

theorem integrable_prod (hf : Integrable f μ) (F : L2 Γ μ) {s : Set (Quot Γ)} (hs : _root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ s ≠ ⊤) :
    Integrable (fun p : Quot Γ × G => f p.2 * F (rmul Γ p.2 p.1)) (((_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict s).prod μ) := by
  haveI : IsFiniteMeasure ((_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict s) := isFiniteMeasure_restrict.2 hs
  have hm : AEStronglyMeasurable (fun p : Quot Γ × G => f p.2 * F (rmul Γ p.2 p.1))
      (((_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict s).prod μ) :=
    hf.1.comp_snd.mul ((Lp.stronglyMeasurable F).comp_measurable measurable_rmul_uncurry).aestronglyMeasurable
  refine (integrable_prod_iff' hm).2 ⟨.of_forall fun y => (integrableOn_rmul F y hs).const_mul (f y), ?_⟩
  refine (hf.norm.mul_const ((_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).real s + ∫ q, ‖F q‖ ^ 2 ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)).mono'
    hm.norm.prod_swap.integral_prod_right' (.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simp only [norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (setIntegral_norm_rmul_le F y hs) (norm_nonneg _)

theorem ae_integrable (hf : Integrable f μ) (F : L2 Γ μ) :
    ∀ᵐ q ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ, Integrable (fun y => f y * F (rmul Γ y q)) μ := by
  haveI : SigmaFinite (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
    SigmaFinite.of_map _ (measurePreserving_sec (Γ := Γ) (μ := μ)).measurable.aemeasurable
      (by rw [measurePreserving_sec.map_eq]; infer_instance)
  refine ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hs => ?_
  haveI : IsFiniteMeasure ((_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict s) := isFiniteMeasure_restrict.2 hs.ne
  exact (integrable_prod hf F hs.ne).prod_right_ae

theorem coeFn_Rop [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] (hf : Integrable f μ) (F : L2 Γ μ) :
    Rop Γ μ f F =ᵐ[_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ] fun q => ∫ y, f y * F (rmul Γ y q) ∂μ := by
  haveI : SigmaFinite (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
    SigmaFinite.of_map _ (measurePreserving_sec (Γ := Γ) (μ := μ)).measurable.aemeasurable
      (by rw [measurePreserving_sec.map_eq]; infer_instance)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hs.ne)
    (fun s _ hs => (integrable_prod hf F hs.ne).integral_prod_left) fun s hs hfin => ?_
  have hR := isRepOp_Rop (Γ := Γ) hf F
  rw [integral_integral_swap (f := fun q y => f y * F (rmul Γ y q)) (integrable_prod hf F hfin.ne),
    ← L2.inner_indicatorConstLp_one hs hfin.ne, hR.2]
  refine (integral_inner (𝕜 := ℂ) hR.1 _).symm.trans (integral_congr_ae (.of_forall fun y => ?_))
  beta_reduce
  rw [inner_smul_right, L2.inner_indicatorConstLp_one hs hfin.ne, integral_const_mul,
    integral_congr_ae (ae_restrict_of_ae (coeFn_R y F))]

theorem lift_Rop_eq_convR (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    ∀ f : G → ℂ, Integrable f μ → ∀ F : L2 Γ μ,
      (∀ᵐ x ∂μ, Integrable (fun y => f y * lift Γ F (x * y)) μ) ∧
        lift Γ (Rop Γ μ f F) =ᵐ[μ] convR μ f (lift Γ F) :=
  fun _ hf F => ⟨ae_quotMeasure_iff.1 (ae_integrable hf F), ae_quotMeasure_iff.1 (coeFn_Rop hf F)⟩

end GlobalTheory.AutomorphicL2Pointwise
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary Topology

namespace GlobalTheory.AutomorphicL2KernelContinuous

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  {Γ : Subgroup G} [DiscreteTopology Γ] {f : G → ℂ}

theorem finite_contributing (hc : HasCompactSupport f) {C C' : Set G} (hC : IsCompact C) (hC' : IsCompact C') :
    {γ : Γ | ∃ x ∈ C, ∃ y ∈ C', f (x⁻¹ * γ * y) ≠ 0}.Finite := by
  have hK := (hC.prod (hc.isCompact.prod hC')).image (f := fun p : G × G × G => p.1 * p.2.1 * p.2.2⁻¹) (by fun_prop)
  refine (finite_mem_compact (Γ := Γ) hK).subset ?_
  rintro γ ⟨x, hx, y, hy, h⟩
  exact ⟨(x, x⁻¹ * γ * y, y), ⟨hx, subset_tsupport f h, hy⟩, by simp [mul_assoc]⟩

theorem locallyFinite_support [LocallyCompactSpace G] (hc : HasCompactSupport f) :
    LocallyFinite fun γ : Γ => Function.support fun p : G × G => f (p.1⁻¹ * γ * p.2) := by
  rintro ⟨x, y⟩
  obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨C', hC', hy⟩ := exists_compact_mem_nhds y
  refine ⟨C ×ˢ C', prod_mem_nhds hx hy, (finite_contributing hc hC hC').subset ?_⟩
  rintro γ ⟨p, h, h1, h2⟩
  exact ⟨p.1, h1, p.2, h2, h⟩

theorem continuous_kernel [LocallyCompactSpace G] (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous fun p : G × G => kernel Γ f p.1 p.2 := by
  have h : Continuous fun p : G × G => ∑ᶠ γ : Γ, f (p.1⁻¹ * γ * p.2) :=
    continuous_finsum (fun γ => by fun_prop) (locallyFinite_support hc)
  refine h.congr fun p => ?_
  exact (tsum_eq_finsum (finite_support_kernel hc p.1 p.2)).symm

end GlobalTheory.AutomorphicL2KernelContinuous
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2Cocompact

theorem isOpenMap_mk {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G) :
    IsOpenMap (mk Γ) := by
  intro U hU
  have h : mk Γ ⁻¹' (mk Γ '' U) = ⋃ γ : Γ, (fun x => ((γ : G))⁻¹ * x) ⁻¹' U := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, e⟩
      obtain ⟨γ, rfl⟩ := mk_eq_iff.1 e
      exact ⟨γ, by simpa using hy⟩
    · rintro ⟨γ, hγ⟩
      exact ⟨_, hγ, mk_eq_iff.2 ⟨γ, by simp⟩⟩
  refine isOpen_coinduced.2 ?_
  change IsOpen (mk Γ ⁻¹' (mk Γ '' U))
  rw [h]
  exact isOpen_iUnion fun γ => hU.preimage (by fun_prop)

theorem exists_compact_image_eq_univ {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (Γ : Subgroup G) [CompactSpace (Quot Γ)] :
    ∃ C : Set G, IsCompact C ∧ mk Γ '' C = Set.univ := by
  classical
  choose K hK hK' using fun x : G => exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : G => mk Γ '' interior (K x))
    (fun x => isOpenMap_mk Γ _ isOpen_interior) (fun q _ => by
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      exact Set.mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hK' x), rfl⟩)
  refine ⟨⋃ x ∈ t, K x, t.isCompact_biUnion fun x _ => hK x, Set.eq_univ_of_forall fun q => ?_⟩
  obtain ⟨x, hx, y, hy, e⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
  exact ⟨y, Set.mem_iUnion₂.2 ⟨x, hx, interior_subset hy⟩, e⟩

theorem cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], CompactSpace (Quot Γ) → IsFiniteMeasure (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ∧ (∃ C : Set G, IsCompact C ∧ mk Γ '' C = Set.univ) ∧ ∀ φ : G → ℂ, LeftInv Γ φ → Continuous φ → MemL2Quotient Γ μ φ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ hc
  obtain ⟨C, hC, hCe⟩ := exists_compact_image_eq_univ Γ
  have hfin : IsFiniteMeasure (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
    ⟨(quotMeasure_le MeasurableSet.univ hCe.ge).trans_lt hC.measure_lt_top⟩
  refine ⟨hfin, ⟨C, hC, hCe⟩, fun φ hφ hcont => ⟨hφ, ?_⟩⟩
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  refine MemLp.of_bound ?_ B (Filter.Eventually.of_forall fun q => ?_)
  · rw [aestronglyMeasurable_quotMeasure_iff_lift, hφ.lift_descend]
    exact hcont.aestronglyMeasurable
  · obtain ⟨x, hx, rfl⟩ := hCe.ge (Set.mem_univ q)
    rw [hφ.descend_mk]
    exact hB x hx

end GlobalTheory.AutomorphicL2Cocompact
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_modular_function_tower_algebraic_coefficients : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), ∃ T : Tower Ω ε, IsStd T := by
  first | exact @GlobalTheory.FN.tower_exists | exact GlobalTheory.FN.tower_exists | (intros; apply GlobalTheory.FN.tower_exists <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThBCompat

private theorem cast_eq_of_dvd {N M : ℕ} (h : N ∣ M) (x y : ℤ) (hxy : (x : ZMod M) = (y : ZMod M)) :
    (x : ZMod N) = (y : ZMod N) := by
  have := congrArg (ZMod.castHom h (ZMod N)) hxy
  simpa only [map_intCast] using this

private theorem gamma_le {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h1)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h2)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h3)
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h4)

private theorem gamma1_le {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma1 M ≤ CongruenceSubgroup.Gamma1 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h1)
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h2)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h3)

theorem isThB_succ_coeff_cong : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n : ℕ) (b : X.Fn l) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l (n + 1) b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l hl l2 hN hN1 hlA n b φ φ' h1 h2
  obtain ⟨f, hfI, hfc, hfδ, hfD⟩ := h1
  obtain ⟨f', hf'I, hf'c, hf'δ, hf'D⟩ := h2
  have hfc' : AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f := by
    have h := AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) (b ![1, 0])
    change (b ![1, 0]).val n = _
    rw [← h]
    change AdicCompletion.transitionMap (idl l) (X.Kl l) (Nat.le_succ n)
      (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) (b ![1, 0])) = _
    rw [hfc]
    rfl
  obtain ⟨u, hu⟩ := GlobalTheory.Tower.cls_eq_pow X l n f f' (hfc'.symm.trans hf'c)
  have hf0 : (f : X.K) ≠ 0 := f.ne_zero
  have hu0 : (u : X.K) ≠ 0 := u.ne_zero
  have hle : CongruenceSubgroup.Gamma1 (N * l ^ (n + 1)) ≤ CongruenceSubgroup.Gamma1 (N * l ^ n) :=
    gamma1_le (Nat.mul_dvd_mul_left N (pow_dvd_pow l (Nat.le_succ n)))
  have hL : (u : X.K) ^ (l ^ n) = (f : X.K)⁻¹ * f' := by rw [hu]; field_simp
  have hT := GlobalTheory.TInv.sl_T_eq X N l (n + 1) hl.out l2 hN hN1 (u : X.K) hu0 (by
      intro γ hγ
      rw [pow_succ, pow_mul, hL, map_pow, map_mul, map_inv₀, hfI γ hγ, hf'I γ (hle hγ)]) (by
      intro δ hδ hδ'
      obtain ⟨g, hgI, hg⟩ := hfδ δ hδ hδ'
      obtain ⟨g', hg'I, hg'⟩ := hf'δ δ hδ (gamma_le (pow_dvd_pow l (Nat.le_succ n)) hδ')
      have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := by
        intro h0; exact hf0 ((X.sl (ofSL δ)).injective (h0.trans (map_zero _).symm))
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hg; exact mul_ne_zero hf0 hsf hg
      refine ⟨g' / g ^ l, ?_, ?_⟩
      · intro γ hγ; rw [map_div₀, map_pow, hgI γ hγ, hg'I γ (hle hγ)]
      · have key : ((u : X.K) * X.sl (ofSL δ) u) ^ (l ^ n) = (g' / g ^ l) ^ (l ^ n) := by
          rw [div_pow, ← pow_mul, ← pow_succ', ← hg', ← hg, hu, map_mul, map_pow]; field_simp; ring
        rw [pow_succ, pow_mul, pow_mul, key])
  have hfD' : IsDl X A l n 1 (f : X.K) φ := by
    obtain ⟨hA, a, c, κ, hκ, hac, ha, hc, hcg⟩ := hfD
    refine ⟨hA, a, c, κ, hκ, hac, ha, hc, fun r => ?_⟩
    obtain ⟨z, hz, e⟩ := hcg r
    exact ⟨l * z, A.mul_mem _ _ (natCast_mem A l) hz, by rw [e, pow_succ, mul_assoc]⟩
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, GlobalTheory.Glue.DlPow.isAlgebraic_of_tower X⟩
  exact GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong X A l hlA n (f : X.K) (u : X.K) hf0 hu0 hT φ φ' hfD' (by rw [← hu]; exact hf'D)

end GlobalTheory.ThBCompat
end
