module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Formalism.CharacterColumnKernels.Bundle001
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle111
public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparison
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle117
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalA
public import ReciprocityTheory.GaloisValuations.Global

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem isTest_comp_homeomorph {X : Type} [TopologicalSpace X] (h : X ≃ₜ X) {Φ : X → ℂ} (hΦ : IsTest Φ) :
    IsTest (Φ ∘ h) :=
  ⟨hΦ.1.comp_continuous h.continuous, hΦ.2.comp_homeomorph h⟩

theorem isTest_ops : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (Hyp.rg A g Φ)) ∧ (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun p : A.K × A.K => Φ (p.1, -p.2))) ∧ (∀ (s : A.Kˣ) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (fun p : A.K × A.K => Φ ((s : A.K) * p.1, (s : A.K) * p.2))) ∧ (∀ (h Φ : A.K × A.K → ℂ), IsLocallyConstant h → IsTest Φ → IsTest (fun p => h p * Φ p)) ∧ ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → IsTest (c • Φ + Φ') := by
  intro F E _ _ _ _ _ A
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g Φ hΦ
    set a := (g : Matrix (Fin 2) (Fin 2) A.K) 0 0
    set b := (g : Matrix (Fin 2) (Fin 2) A.K) 0 1
    set c := (g : Matrix (Fin 2) (Fin 2) A.K) 1 0
    set d := (g : Matrix (Fin 2) (Fin 2) A.K) 1 1
    have hdet : a * d - b * c = 1 := by
      have := g.2
      rw [Matrix.det_fin_two] at this
      simpa [a, b, c, d] using this
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => (p.1 * a + p.2 * c, p.1 * b + p.2 * d)
        invFun := fun p => (p.1 * d - p.2 * c, -(p.1 * b) + p.2 * a)
        left_inv := by
          intro p
          ext
          · simp only; linear_combination p.1 * hdet
          · simp only; linear_combination p.2 * hdet
        right_inv := by
          intro p
          ext
          · simp only; linear_combination p.1 * hdet
          · simp only; linear_combination p.2 * hdet
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro Φ hΦ
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => (p.1, -p.2)
        invFun := fun p => (p.1, -p.2)
        left_inv := by intro p; simp
        right_inv := by intro p; simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro s Φ hΦ
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => ((s : A.K) * p.1, (s : A.K) * p.2)
        invFun := fun p => (((s⁻¹ : A.Kˣ) : A.K) * p.1, ((s⁻¹ : A.Kˣ) : A.K) * p.2)
        left_inv := by intro p; ext <;> simp [← mul_assoc]
        right_inv := by intro p; ext <;> simp [← mul_assoc]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro h Φ hh hΦ
    exact ⟨hh.mul hΦ.1, hΦ.2.mul_left⟩
  · intro c Φ Φ' hΦ hΦ'
    refine ⟨?_, ?_⟩
    · exact (hΦ.1.comp (fun z : ℂ => c • z)).add hΦ'.1
    · exact (hΦ.2.smul_left).add hΦ'.2

end GlobalTheory.JR.Hyp
end
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilQuad

theorem gaussInt_stable_of_dual : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → ∀ (t : A.K) (M D : AddSubgroup A.L), IsOpen (M : Set A.L) → IsCompact (M : Set A.L) → IsOpen (D : Set A.L) → IsCompact (D : Set A.L) → (∀ m ∈ M, A.psiK ψ (t * x * A.NL m) = 1) → (D : Set A.L) = {y : A.L | ∀ m ∈ M, A.kerL ψ (t * x) y m = 1} → IsStableGauss A ψ x μ t (gaussInt A ψ x μ t (D : Set A.L)) := by
  intro F E _ _ _ _ hU A ψ x μ hψ hμ t M D hMo hMc hDo hDc hN hD
  obtain ⟨⟨bas⟩, hinj, hNL, hTr, -⟩ := Et.quadratic_structure F E A
  haveI : Module.Finite A.K A.L := Module.Finite.of_basis bas
  haveI : Module.Finite F A.L := Module.Finite.trans A.K A.L
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hpsi : ∀ u v : A.K, A.psiK ψ (u + v) = A.psiK ψ u * A.psiK ψ v := by
    intro u v
    simp only [Et.psiK, map_add (f := _), AddChar.map_add_eq_mul]
  have hNadd : ∀ y m : A.L, A.NL (y + m) = A.NL y + Algebra.trace A.K A.L (star y * m) + A.NL m := by
    intro y m
    apply hinj
    simp only [map_add (f := _), hNL, hTr, star_add, star_mul, star_star]
    ring
  set g : A.L → ℂ := fun y => A.psiK ψ (t * x * A.NL y) with hg
  have hgadd : ∀ y m : A.L, g (y + m) = g y * A.kerL ψ (t * x) y m * A.psiK ψ (t * x * A.NL m) := by
    intro y m
    simp only [hg, Et.kerL, ← hpsi, hNadd]
    congr 1
    ring
  have hkadd : ∀ y y' m : A.L, A.kerL ψ (t * x) (y + y') m = A.kerL ψ (t * x) y m * A.kerL ψ (t * x) y' m := by
    intro y y' m
    simp only [Et.kerL, ← hpsi, star_add, add_mul, map_add (f := _), mul_add]
  have hmemD : ∀ y, y ∈ D ↔ ∀ m ∈ M, A.kerL ψ (t * x) y m = 1 := fun y => Set.ext_iff.1 hD y
  have hMD : M ≤ D := by
    intro m hm
    rw [hmemD]
    intro m' hm'
    have h := hgadd m m'
    have h1 : g (m + m') = 1 := hN _ (M.add_mem hm hm')
    have h2 : g m = 1 := hN _ hm
    rw [h1, h2, hN _ hm'] at h
    simpa using h.symm

  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro y
    have c1 : Continuous (fun m : A.L => Algebra.trace A.K A.L (star y * m)) :=
      IsModuleTopology.continuous_of_linearMap
        (((Algebra.trace A.K A.L).comp (LinearMap.mulLeft A.K (star y))).restrictScalars F)
    have c2 : Continuous (fun m : A.L => Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))) :=
      (IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)).comp (continuous_const.mul c1)
    have hU0 : {m : A.L | m ∈ M ∧ ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1} ∈ 𝓝 (0 : A.L) := by
      have hM : (M : Set A.L) ∈ 𝓝 (0 : A.L) := hMo.mem_nhds M.zero_mem
      have h0 : Metric.closedBall (0 : F) 1 ∈ 𝓝 (Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * (0 : A.L)))) := by
        simp only [mul_zero, map_zero]
        exact Metric.closedBall_mem_nhds 0 one_pos
      have hbound : {m : A.L | ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1} ∈ 𝓝 (0 : A.L) :=
        Filter.mem_of_superset ((c2.continuousAt (x := (0 : A.L))).preimage_mem_nhds h0)
        (fun m hm => (show ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1 by
          simpa [Metric.mem_closedBall, dist_zero_right] using hm))
      filter_upwards [hM, hbound] with m hmM hmBound
      exact ⟨hmM, hmBound⟩
    have hU1 := (continuous_sub_right y).continuousAt.preimage_mem_nhds (by rw [sub_self]; exact hU0)
    refine ContinuousAt.congr (f := fun _ => g y) continuousAt_const ?_
    filter_upwards [hU1] with z hz
    show g y = g z
    obtain ⟨hzM, hz1⟩ := hz
    have := hgadd y (z - y)
    rw [add_sub_cancel] at this
    rw [this, hN _ hzM, Et.kerL, Et.psiK, hψ.1 _ hz1]
    simp

  refine ⟨D, hDo, hDc, fun Λ hΛo hΛc hDΛ => ?_⟩
  have hmeas : ∀ S : Set A.L, IsOpen S → MeasurableSet S := fun S hS => hS.measurableSet
  have hint : IntegrableOn g (Λ : Set A.L) μ := hgc.continuousOn.integrableOn_compact' hΛc (hmeas _ hΛo)
  have hsplit : (Λ : Set A.L) = (D : Set A.L) ∪ ((Λ : Set A.L) \ (D : Set A.L)) :=
    (Set.union_diff_cancel (show (D : Set A.L) ⊆ Λ from hDΛ)).symm

  haveI : DiscreteTopology (A.L ⧸ D) := QuotientAddGroup.discreteTopology hDo
  have hmk : Continuous (QuotientAddGroup.mk : A.L → A.L ⧸ D) := continuous_quot_mk
  set S : A.L ⧸ D → Set A.L := fun q => ((Λ : Set A.L) \ (D : Set A.L)) ∩ QuotientAddGroup.mk ⁻¹' {q} with hS
  have hSo : ∀ q, MeasurableSet (S q) := fun q =>
    ((hmeas _ hΛo).diff (hmeas _ hDo)).inter (hmeas _ ((isOpen_discrete {q}).preimage hmk))
  have hzero : ∀ q, ∫ y in S q, g y ∂μ = 0 := by
    intro q
    by_cases hne : (S q).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, Measure.restrict_empty, integral_zero_measure]
    obtain ⟨y₀, ⟨hy₀Λ, hy₀D⟩, hy₀q⟩ := hne
    have hy₀ : ¬ ∀ m ∈ M, A.kerL ψ (t * x) y₀ m = 1 := fun h => hy₀D ((hmemD y₀).2 h)
    push_neg at hy₀
    obtain ⟨m₀, hm₀, hc⟩ := hy₀
    have hm₀D : m₀ ∈ D := hMD hm₀
    have hshift : ∀ y ∈ S q, g (m₀ + y) = A.kerL ψ (t * x) y₀ m₀ * g y := by
      intro y hy
      obtain ⟨-, hyq⟩ := hy
      have hrel : -y₀ + y ∈ D := by
        rw [← QuotientAddGroup.eq]
        exact (hy₀q.trans hyq.symm)
      have h1 : A.kerL ψ (t * x) y m₀ = A.kerL ψ (t * x) y₀ m₀ := by
        have := hkadd y₀ (-y₀ + y) m₀
        rw [add_neg_cancel_left, (hmemD _).1 hrel m₀ hm₀, mul_one] at this
        exact this
      rw [add_comm, hgadd, h1, hN _ hm₀]
      ring
    have hpre : (fun y => m₀ + y) ⁻¹' (S q) = S q := by
      ext y
      simp only [hS, Set.mem_preimage, Set.mem_inter_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
      have e1 : m₀ + y ∈ Λ ↔ y ∈ Λ := ⟨fun h => by simpa using Λ.sub_mem h (hDΛ hm₀D), fun h => Λ.add_mem (hDΛ hm₀D) h⟩
      have e2 : m₀ + y ∈ D ↔ y ∈ D := ⟨fun h => by simpa using D.sub_mem h hm₀D, fun h => D.add_mem hm₀D h⟩
      have e3 : (QuotientAddGroup.mk (m₀ + y) : A.L ⧸ D) = QuotientAddGroup.mk y := by
        rw [QuotientAddGroup.eq]
        simpa using D.neg_mem hm₀D
      rw [e1, e2, e3]
    have htr := (measurePreserving_add_left μ m₀).setIntegral_preimage_emb (measurableEmbedding_addLeft m₀) g (S q)
    rw [hpre] at htr
    have h2 : ∫ y in S q, g (m₀ + y) ∂μ = A.kerL ψ (t * x) y₀ m₀ * ∫ y in S q, g y ∂μ := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun (hSo q) (fun y hy => hshift y hy)
    rw [h2] at htr
    have h3 : (A.kerL ψ (t * x) y₀ m₀ - 1) * ∫ y in S q, g y ∂μ = 0 := by rw [sub_mul, htr]; ring
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc)
  have hfin : (QuotientAddGroup.mk '' (Λ : Set A.L) : Set (A.L ⧸ D)).Finite :=
    (hΛc.image hmk).finite_of_discrete
  have hunion : ((Λ : Set A.L) \ (D : Set A.L)) = ⋃ q ∈ hfin.toFinset, S q := by
    ext y
    simp only [hS, Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hy
      exact ⟨_, ⟨y, hy.1, rfl⟩, hy, rfl⟩
    · rintro ⟨_, _, hy, _⟩
      exact hy
  have hrest : ∫ y in (Λ : Set A.L) \ (D : Set A.L), g y ∂μ = 0 := by
    rw [hunion, integral_biUnion_finset]
    · exact Finset.sum_eq_zero (fun q _ => hzero q)
    · exact fun q _ => hSo q
    · intro q₁ _ q₂ _ hq
      refine Set.disjoint_left.2 ?_
      rintro y ⟨-, h1⟩ ⟨-, h2⟩
      exact hq ((Set.mem_singleton_iff.1 h1).symm.trans (Set.mem_singleton_iff.1 h2))
    · exact fun q _ => hint.mono_set (fun y hy => hy.1.1)
  show ∫ y in (Λ : Set A.L), g y ∂μ = ∫ y in (D : Set A.L), g y ∂μ
  rw [hsplit, setIntegral_union Set.disjoint_sdiff_right ((hmeas _ hΛo).diff (hmeas _ hDo))
    (hint.mono_set hDΛ) (hint.mono_set Set.diff_subset), hrest, add_zero]

end GlobalTheory.JR.WeilQuad
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem coord_structure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), e * e = e → star e = 1 - e → (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) ∧ (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) ∧ (∀ p, A.NL (Hyp.cc A e p) = p.1 * p.2) ∧ (∀ (ψ : AddChar F ℂ) (x : A.K) (p q : A.K × A.K), A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) ∧ (∀ (s : A.K) p, s • Hyp.cc A e p = Hyp.cc A e (s * p.1, s * p.2)) ∧ ∀ s : A.Kˣ, IsUnit (Hyp.cc A e ((s : A.K), 1)) := by
  intro F E _ _ _ _ _ A e hee hse
  obtain ⟨-, hinj, hnorm, htr, -⟩ := Et.quadratic_structure F E A
  have htrs : ∀ (a : A.K) (f : A.L),
      Algebra.trace A.K A.L (algebraMap A.K A.L a * f) = a * Algebra.trace A.K A.L f := by
    intro a f
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hone : ∀ f : A.L, star f = 1 - f → Algebra.trace A.K A.L f = 1 := by
    intro f hf
    apply hinj
    rw [htr, hf, map_one]
    ring
  have hte : Algebra.trace A.K A.L e = 1 := hone e hse
  have htf : Algebra.trace A.K A.L (1 - e) = 1 :=
    hone (1 - e) (by rw [star_sub, star_one, hse])
  have hst : ∀ p : A.K × A.K, star (Hyp.cc A e p) =
      algebraMap A.K A.L p.1 * (1 - e) + algebraMap A.K A.L p.2 * e := by
    intro p
    simp only [Hyp.cc, star_add, star_mul, star_sub, star_one, hse, A.star_K]
    ring
  have hme : ∀ p : A.K × A.K, Hyp.cc A e p * e = algebraMap A.K A.L p.1 * e := by
    intro p
    simp only [Hyp.cc]
    linear_combination (algebraMap A.K A.L p.1 - algebraMap A.K A.L p.2) * hee
  have hmf : ∀ p : A.K × A.K, Hyp.cc A e p * (1 - e) = algebraMap A.K A.L p.2 * (1 - e) := by
    intro p
    simp only [Hyp.cc]
    linear_combination (algebraMap A.K A.L p.2 - algebraMap A.K A.L p.1) * hee
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    simp only [Hyp.ci]
    rw [hme p, hmf p, htrs, htrs, hte, htf, mul_one, mul_one]
  · intro y
    simp only [Hyp.cc, Hyp.ci, htr, star_mul, star_sub, star_one, hse]
    linear_combination (2 * y - 2 * star y) * hee
  · intro p
    apply hinj
    rw [hnorm, hst, map_mul]
    simp only [Hyp.cc]
    linear_combination (-(algebraMap A.K A.L p.1 - algebraMap A.K A.L p.2) ^ 2) * hee
  · intro ψ x p q
    have hprod : star (Hyp.cc A e q) * Hyp.cc A e p =
        algebraMap A.K A.L (q.1 * p.2) * (1 - e) + algebraMap A.K A.L (q.2 * p.1) * e := by
      rw [hst]
      simp only [Hyp.cc, map_mul]
      linear_combination
        (algebraMap A.K A.L q.1 * algebraMap A.K A.L p.2 + algebraMap A.K A.L q.2 * algebraMap A.K A.L p.1
          - algebraMap A.K A.L q.1 * algebraMap A.K A.L p.1
          - algebraMap A.K A.L q.2 * algebraMap A.K A.L p.2) * hee
    have ht : Algebra.trace A.K A.L (star (Hyp.cc A e q) * Hyp.cc A e p) = q.1 * p.2 + q.2 * p.1 := by
      rw [hprod, map_add (f := _), htrs, htrs, hte, htf, mul_one, mul_one]
    simp only [Et.kerL, Hyp.kx, Et.psiK]
    rw [ht]
    rw [show x * (q.1 * p.2 + q.2 * p.1) = x * q.1 * p.2 + x * q.2 * p.1 by ring, map_add (f := _),
      AddChar.map_add_eq_mul]
  · intro s p
    simp only [Hyp.cc, Algebra.smul_def, map_mul]
    ring
  · intro s
    have hs : algebraMap A.K A.L (s : A.K) * algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine isUnit_iff_exists_inv.mpr ⟨Hyp.cc A e (((s⁻¹ : A.Kˣ) : A.K), 1), ?_⟩
    simp only [Hyp.cc, map_one]
    linear_combination
      (2 - algebraMap A.K A.L (s : A.K) - algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K)) * hee + e * e * hs

end GlobalTheory.JR.Hyp
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.Desc

theorem dvr_dvd_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a y : O}
    (ha : a ∈ IsLocalRing.maximalIdeal O) (hy : y ≠ 0) : ∃ k : ℕ, y ∣ a ^ k := by
  have hyt : IsDiscreteValuationRing.addVal O y ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hyt
  have ha1 : 1 ≤ IsDiscreteValuationRing.addVal O a := by
    rw [ENat.one_le_iff_ne_zero, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
    exact ha
  refine ⟨n, IsDiscreteValuationRing.addVal_le_iff_dvd.1 ?_⟩
  rw [IsDiscreteValuationRing.addVal_pow, ← hn]
  calc ((n : ℕ∞)) = n • (1 : ℕ∞) := by simp
    _ ≤ n • IsDiscreteValuationRing.addVal O a := nsmul_le_nsmul_right ha1 n

theorem smul_pow_integral (K : UQ) (B : InvAlg K) (a : K.O) (ha : K.Small a) (x : B.A) :
    ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := by
  have hxE : IsIntegral K.E x := Algebra.IsIntegral.isIntegral x
  obtain ⟨⟨m, hm⟩, hmx⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors K.O) x hxE
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  obtain ⟨k, w, hw⟩ := dvr_dvd_pow ha.2.1 hm0
  refine ⟨k, ?_⟩
  have hsm : (m • x : B.A) = (⟨m, hm⟩ : nonZeroDivisors K.O) • x := rfl
  have : (al K a ^ k) • x = algebraMap K.O B.A w * (m • x) := by
    rw [← map_pow, algebraMap_smul, hw, mul_comm, mul_smul, Algebra.smul_def]
  rw [this]
  exact isIntegral_algebraMap.mul (hsm ▸ hmx)

end GlobalTheory.UnitLemma.Desc
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

theorem norm_prod_mk_one {K : UQ} (B₁ B₂ : InvAlg K) (y : B₁.A) :
    Algebra.norm K.E ((y, 1) : B₁.A × B₂.A) = Algebra.norm K.E y := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul K.E (B₁.A × B₂.A) (y, 1) =
      LinearMap.prodMap (Algebra.lmul K.E B₁.A y) (Algebra.lmul K.E B₂.A 1) := by
    ext z <;> simp
  rw [h, LinearMap.det_prodMap, map_one, map_one, mul_one]

theorem chi_prod_inl : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ : ι₁ → B₁.A) (e₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (x : B₁.A × B₂.A), chi (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) x = chi B₁ e₁ S₁ x.1 := by
  intro K B₁ B₂ ι₁ ι₂ e₁ e₂ S₁ x
  have hS : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
      (S₁.map Function.Embedding.inl) = ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) := by
    unfold eS
    rw [Finset.sum_map]
    show (∑ i ∈ S₁, ((e₁ i, 0) : B₁.A × B₂.A)) = ((∑ i ∈ S₁, e₁ i, 0) : B₁.A × B₂.A)
    rw [Prod.ext_iff]
    simp [Prod.fst_sum, Prod.snd_sum]
  unfold chi
  rw [hS]
  have hx : (x * ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) + (1 - ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A)) : B₁.A × B₂.A) =
      ((x.1 * eS B₁ e₁ S₁ + (1 - eS B₁ e₁ S₁), 1) : B₁.A × B₂.A) := by
    ext <;> simp
  change K.eta (Algebra.norm K.E (x * ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) + (1 - ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A)))) = _
  rw [hx, norm_prod_mk_one]

end GlobalTheory.UnitLemma.Desc
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.finite_invariants_of_scalar_ne_one_twist : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ {G : Type} [Group G]
    (ρ : Representation O G M) (g : G) (a : O), a ≠ 1 → (∀ m, ρ g m = a • m) → Finite ρ.invariants := by
  first | exact @GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one | exact GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one | (intros; apply GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem valuation_pow_sub_pow_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω}
    (ha : A.valuation a ≤ 1) (hb : A.valuation b ≤ 1) (hab : A.valuation (a - b) < 1) (k : ℕ) :
    A.valuation (a ^ k - b ^ k) < 1 := by
  rw [← Commute.geom_sum₂_mul (Commute.all a b), map_mul]
  have hs : A.valuation (∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' ha _) (pow_le_one' hb _)
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hs) hab

theorem frob_pow_apply_sub_lt_one :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (q : ℕ) (σ : Ω ≃ₐ[F] Ω),
    Formalism.ConjugateSelfDual.IsFrob A q σ → ∀ (n : ℕ) (x : Ω), A.valuation x ≤ 1 → A.valuation ((σ ^ n) x - x ^ (q ^ n)) < 1 := by
  intro F Ω _ _ _ _ A q σ hσ n
  obtain ⟨hD, hF⟩ := hσ
  have hD' : σ ∈ ReciprocityTheory.Gal.Dec (F := F) A := hD
  have hle : ∀ y : Ω, A.valuation y ≤ 1 → A.valuation (σ y) ≤ 1 := by
    intro y hy
    rw [A.valuation_le_one_iff] at hy ⊢
    exact (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hD' y).mpr hy
  induction n with
  | zero =>
    intro x _
    simp
  | succ n ih =>
    intro x hx
    have e : (σ ^ (n + 1)) x - x ^ (q ^ (n + 1)) =
        σ ((σ ^ n) x - x ^ (q ^ n)) + ((σ x) ^ (q ^ n) - (x ^ q) ^ (q ^ n)) := by
      rw [pow_succ' σ n, AlgEquiv.mul_apply, map_sub, map_pow, ← pow_mul, ← pow_succ']
      ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_
    · exact (ReciprocityTheory.Gal.valuation_apply_lt_one_iff hD' _).mpr (ih x hx)
    · refine valuation_pow_sub_pow_lt_one A (hle x hx) ?_ (hF x hx) _
      rw [map_pow]; exact pow_le_one' hx _

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.period_data_comparison : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Module.Basis (Fin n) Qp V) (W W' : Matrix (Fin n) (Fin n) BdR), W * W' = 1 → (∀ i j, W i j ∈ PD.Fil 0) → (∀ i j, W' i j ∈ PD.Fil 0) → (∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) * W.map (PD.actdR g) = W) → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a → a = 0 := by
  first | exact @GlobalTheory.SplitJump.jump_eq_zero | exact GlobalTheory.SplitJump.jump_eq_zero | (intros; apply GlobalTheory.SplitJump.jump_eq_zero <;> assumption)
end

section


theorem _root_.GlobalTheory.T.vanish_at_hodgeTate_cocharacter : ∀ {C Γ n : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] [Fintype n] [DecidableEq n] (χ : Γ →* Cˣ), (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) → ∀ (ρ : Γ →* Matrix.GeneralLinearGroup n C), (∀ (g γ : Γ) (i j : n), g • (ρ γ : Matrix n n C) i j = (ρ γ : Matrix n n C) i j) → ∀ (P : Matrix.GeneralLinearGroup n C) (k : n → ℤ), (∀ g : Γ, (ρ g : Matrix n n C) * (P : Matrix n n C).map (fun a => g • a) = (P : Matrix n n C) * Matrix.diagonal (fun i => ((χ g ^ k i : Cˣ) : C))) → ∀ f : MvPolynomial (n × n) C, (∀ γ : Γ, MvPolynomial.eval (fun ij => (ρ γ : Matrix n n C) ij.1 ij.2) f = 0) → ∀ t : Cˣ, MvPolynomial.eval (fun ij => ((P : Matrix n n C) * Matrix.diagonal (fun i => ((t ^ k i : Cˣ) : C)) * ((P⁻¹ : Matrix.GeneralLinearGroup n C) : Matrix n n C)) ij.1 ij.2) f = 0 := by
  first | exact @GlobalTheory.HTCPoly.vanish_at_cocharacter | exact GlobalTheory.HTCPoly.vanish_at_cocharacter | (intros; apply GlobalTheory.HTCPoly.vanish_at_cocharacter <;> assumption)
end
