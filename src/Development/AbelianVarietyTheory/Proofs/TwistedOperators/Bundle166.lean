module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle156
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
public import Mathlib.Topology.Algebra.Group.OpenMapping
public import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.UnitaryDetAbs

open GlobalTheory.MixModel

theorem absE_det_matHom (D : D7) (W : HSp D) (h : GA D W) :
    GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 := by
  have hM := GlobalTheory.MixModel.mt_unitary W h
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hadj : (GlobalTheory.MixModel.adj (mt W h)).det = cA D (mt W h).det := by
    rw [GlobalTheory.MixModel.adj, Matrix.det_transpose, RingHom.map_det]; rfl
  have hG : IsUnit (GlobalTheory.MixModel.gA W).det := by
    have e : (GlobalTheory.MixModel.gA W).det = incA D W.gram.det := by
      rw [GlobalTheory.MixModel.gA, GlobalTheory.MixModel.rat, RingHom.map_det]; rfl
    rw [e]
    exact (GlobalTheory.MixModel.gram_isUnit_det W).map _
  rw [hadj] at hdet
  have key : cA D (mt W h).det * (mt W h).det = 1 := by
    have e2 : cA D (mt W h).det * (mt W h).det * (GlobalTheory.MixModel.gA W).det = 1 * (GlobalTheory.MixModel.gA W).det := by
      rw [one_mul]; nth_rewrite 2 [← hdet]; ring
    exact hG.mul_right_cancel e2
  have hu : GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det (matHom W h)) *
      Matrix.GeneralLinearGroup.det (matHom W h) = 1 := by
    ext
    exact key
  have h2 := congrArg (GlobalTheory.Doubling.absE D.host.F D.host.E) hu
  rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq] at h2
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

end GlobalTheory.UnitaryDetAbs
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoMean

theorem iterInt_continuous_periodic : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ r ∈ GlobalTheory.MixModel.ratMx D a b, f₁ r ∈ ratL W V) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → Continuous (fun s => ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∧ ∀ r ∈ GlobalTheory.MixModel.ratMx D a b, ∀ s, ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ (r + s) + f₂ z + f₃ y) ∂μ) ∂η = ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η := by
  intro D V W a b k f₁ f₃ f₂ hf₁ hf₂ hf₃ hadd hrat μ 𝓨 hcov η 𝓩 hη h𝓩 T hT hper
  obtain ⟨-, -, hμ1⟩ := hcov

  obtain ⟨-, -, -, -, -, K, hK, hKcov⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := T) hT.continuousOn
  have hbd : ∀ u, ‖T u‖ ≤ M := by
    intro u
    obtain ⟨γ, hγ, hγK⟩ := hKcov u
    have hγ' : γ ∈ ratL W V := by rw [GlobalTheory.MixModel.ratL_eq]; exact hγ
    rw [← hper γ hγ' u]
    exact hM _ hγK
  haveI : SecondCountableTopology (Mx D 1 k) := (GlobalTheory.MixModel.lattice_Mx D 1 k).2.2.1
  haveI : SecondCountableTopology (Mx D a b) := (GlobalTheory.MixModel.lattice_Mx D a b).2.2.1
  haveI : BorelSpace (Mx D 1 k) := ⟨rfl⟩
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩

  have hY : μ 𝓨 < ⊤ := by rw [hμ1]; exact ENNReal.one_lt_top
  have hZ : η 𝓩 < ⊤ := by
    obtain ⟨hg, -, hsc, -, hd, K', hK', hK'cov⟩ := GlobalTheory.MixModel.lattice_Mx D 1 k
    haveI : Countable (GlobalTheory.MixModel.ratMx D 1 k) :=
      TopologicalSpace.separableSpace_iff_countable.mp inferInstance
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK' hK'cov η h𝓩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ]; exact hY⟩
  haveI : IsFiniteMeasure (η.restrict 𝓩) := ⟨by rw [Measure.restrict_apply_univ]; exact hZ⟩

  have hIc : Continuous (fun p : Mx D a b × Mx D 1 k => ∫ y in 𝓨, T (f₁ p.1 + f₂ p.2 + f₃ y) ∂μ) := by
    set_option synthInstance.maxHeartbeats 200000 in
      refine continuous_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
    · intro p
      exact (hT.comp (continuous_const.add hf₃)).aestronglyMeasurable
    · intro p
      exact Filter.Eventually.of_forall fun y => hbd _
    · refine Filter.Eventually.of_forall fun y => hT.comp ?_
      exact ((hf₁.comp continuous_fst).add (hf₂.comp continuous_snd)).add continuous_const
  refine ⟨?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 200000 in
      refine continuous_of_dominated (bound := fun _ => M * μ.real 𝓨) ?_ ?_ (integrable_const _) ?_
    · intro s
      exact (hIc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro s
      exact Filter.Eventually.of_forall fun z =>
        norm_setIntegral_le_of_norm_le_const hY (fun y _ => hbd _)
    · exact Filter.Eventually.of_forall fun z => hIc.comp (continuous_id.prodMk continuous_const)
  · intro r hr s
    have h : ∀ z y, T (f₁ (r + s) + f₂ z + f₃ y) = T (f₁ s + f₂ z + f₃ y) := by
      intro z y
      have e : f₁ (r + s) + f₂ z + f₃ y = f₁ r + (f₁ s + f₂ z + f₃ y) := by
        rw [hadd]; abel
      rw [e, hper _ (hrat r hr)]
    simp only [h]

end GlobalTheory.IsoMean

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

open scoped Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoordUnfold

theorem isAddFundamentalDomain_prod {A B : Type} [AddGroup A] [AddGroup B] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SigmaFinite ν]
    {Γ : AddSubgroup A} {Δ : AddSubgroup B} {s : Set A} {t : Set B}
    (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  · have h1 : ∀ᵐ p ∂(μ.prod ν), ∃ g : Γ, g +ᵥ p.1 ∈ s :=
      Measure.quasiMeasurePreserving_fst.ae hs.ae_covers
    have h2 : ∀ᵐ p ∂(μ.prod ν), ∃ d : Δ, d +ᵥ p.2 ∈ t :=
      Measure.quasiMeasurePreserving_snd.ae ht.ae_covers
    filter_upwards [h1, h2] with p hg hd
    obtain ⟨g, hg⟩ := hg
    obtain ⟨d, hd⟩ := hd
    exact ⟨⟨((g : A), (d : B)), g.2, d.2⟩, hg, hd⟩
  · rintro ⟨⟨g, d⟩, hg, hd⟩ ⟨⟨g', d'⟩, hg', hd'⟩ hne
    have key : ((⟨(g, d), hg, hd⟩ : Γ.prod Δ) +ᵥ s ×ˢ t) ∩ ((⟨(g', d'), hg', hd'⟩ : Γ.prod Δ) +ᵥ s ×ˢ t) =
        (((⟨g, hg⟩ : Γ) +ᵥ s) ∩ ((⟨g', hg'⟩ : Γ) +ᵥ s)) ×ˢ (((⟨d, hd⟩ : Δ) +ᵥ t) ∩ ((⟨d', hd'⟩ : Δ) +ᵥ t)) := by
      ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_vadd_set_iff_neg_vadd_mem]
      exact ⟨fun ⟨⟨a1, a2⟩, a3, a4⟩ => ⟨⟨a1, a3⟩, a2, a4⟩, fun ⟨⟨a1, a3⟩, a2, a4⟩ => ⟨⟨a1, a2⟩, a3, a4⟩⟩
    show (μ.prod ν) (_ ∩ _) = 0
    rw [key, Measure.prod_prod]
    by_cases h : g = g'
    · subst h
      have hdd : (⟨d, hd⟩ : Δ) ≠ ⟨d', hd'⟩ := fun e => hne (by
        have := congrArg Subtype.val e
        simp only at this
        subst this; rfl)
      have := ht.aedisjoint hdd
      rw [show ν _ = 0 from this, mul_zero]
    · have hgg : (⟨g, hg⟩ : Γ) ≠ ⟨g', hg'⟩ := fun e => h (congrArg Subtype.val e)
      have := hs.aedisjoint hgg
      rw [show μ _ = 0 from this, zero_mul]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem integral_fundamentalDomain_eq_iterated : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ z z', f₂ (z + z') = f₂ z + f₂ z') → (∀ y y', f₃ (y + y') = f₃ y + f₃ y') → (∀ x : WO V W, ∃ s z y, x = f₁ s + f₂ z + f₃ y) → (∀ s z y, f₁ s + f₂ z + f₃ y = 0 → s = 0 ∧ z = 0 ∧ y = 0) → (∀ s z y, f₁ s + f₂ z + f₃ y ∈ ratL W V ↔ s ∈ GlobalTheory.MixModel.ratMx D a b ∧ z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∃ κ : ℝ, 0 < κ ∧ ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂ν = κ * ∫ s in 𝓨, (∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∂μ := by
  intro D V W a b k f₁ f₃ f₂ hc₁ hc₂ hc₃ ha₁ ha₂ ha₃ hsurj hinj hrat μ 𝓨 hμ η 𝓩 hη h𝓩 ν 𝓕 hν h𝓕
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  obtain ⟨j1, j2, j3, j4, j5, KZ, hKZ, hKZc⟩ := GlobalTheory.MixModel.lattice_Mx D 1 k
  obtain ⟨l1, l2, l3, l4, l5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI : BorelSpace (Mx D 1 k) := ⟨rfl⟩
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : Countable (GlobalTheory.MixModel.ratMx D a b) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D 1 k) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsTopologicalAddGroup (WO V W) := l1
  haveI : LocallyCompactSpace (WO V W) := l2
  haveI : SecondCountableTopology (WO V W) := l3
  haveI : T2Space (WO V W) := l4
  haveI : BaireSpace (WO V W) := BaireSpace.of_t2Space_locallyCompactSpace
  haveI : Countable (ratL W V) := by
    have : Countable (GlobalTheory.MixModel.ratMx D W.rank V.rank) :=
      TopologicalSpace.separableSpace_iff_countable.1 inferInstance
    exact this
  haveI := hμ.1

  have hZfin : η 𝓩 < ⊤ := by
    have hcov : 𝓩 ⊆ ⋃ γ : GlobalTheory.MixModel.ratMx D 1 k, ((γ +ᵥ KZ) ∩ 𝓩) := by
      intro x hx
      obtain ⟨γ, hγ, hγx⟩ := hKZc x
      refine Set.mem_iUnion.2 ⟨⟨-γ, neg_mem hγ⟩, Set.mem_vadd_set.2 ⟨γ + x, hγx, ?_⟩, hx⟩
      show -γ + (γ + x) = x
      abel
    calc η 𝓩 ≤ ∑' γ : GlobalTheory.MixModel.ratMx D 1 k, η ((γ +ᵥ KZ) ∩ 𝓩) :=
          (measure_mono hcov).trans (measure_iUnion_le _)
      _ = η KZ := (h𝓩.measure_eq_tsum KZ).symm
      _ < ⊤ := hKZ.measure_lt_top
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (η.restrict 𝓩) := ⟨by rw [Measure.restrict_apply_univ]; exact hZfin⟩

  let Ehom : (Mx D a b × (Mx D 1 k × Mx D a b)) →+ WO V W :=
    AddMonoidHom.mk' (fun p => f₁ p.1 + f₂ p.2.1 + f₃ p.2.2) (fun p q => by
      simp only [Prod.fst_add, Prod.snd_add, ha₁, ha₂, ha₃]; abel)
  have hEc : Continuous Ehom :=
    ((hc₁.comp continuous_fst).add (hc₂.comp (continuous_fst.comp continuous_snd))).add
      (hc₃.comp (continuous_snd.comp continuous_snd))
  have hEi : Function.Injective Ehom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨s, z, y⟩ h
    obtain ⟨h1, h2, h3⟩ := hinj s z y h
    simp [h1, h2, h3]
  have hEs : Function.Surjective Ehom := fun x => by
    obtain ⟨s, z, y, rfl⟩ := hsurj x
    exact ⟨(s, z, y), rfl⟩
  have hEo : IsOpenMap Ehom := AddMonoidHom.isOpenMap_of_sigmaCompact Ehom hEs hEc
  let Eq : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃+ WO V W := AddEquiv.ofBijective Ehom ⟨hEi, hEs⟩
  let H : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ₜ WO V W := Eq.toEquiv.toHomeomorphOfContinuousOpen hEc hEo
  let Ec : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ₜ+ WO V W :=
    { Eq with continuous_toFun := hEc, continuous_invFun := H.symm.continuous }
  have hEapp : ∀ s z y, Ec (s, z, y) = f₁ s + f₂ z + f₃ y := fun _ _ _ => rfl
  let Me : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ᵐ WO V W := H.toMeasurableEquiv
  have hMe : ∀ p, Me p = Ec p := fun _ => rfl

  set lam : Measure (Mx D a b × (Mx D 1 k × Mx D a b)) := μ.prod (η.prod μ) with hlam
  haveI : lam.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set m : Measure (WO V W) := lam.map Me with hm
  haveI : m.IsAddHaarMeasure := Ec.isAddHaarMeasure_map lam
  have hνm := Measure.isAddLeftInvariant_eq_smul ν m
  set c := Measure.addHaarScalarFactor ν m with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν m
  have hcne : (c : ENNReal) ≠ 0 := by exact_mod_cast hc.ne'

  set Γ : AddSubgroup (Mx D a b × (Mx D 1 k × Mx D a b)) :=
    (GlobalTheory.MixModel.ratMx D a b).prod ((GlobalTheory.MixModel.ratMx D 1 k).prod (GlobalTheory.MixModel.ratMx D a b)) with hΓ
  have hmemΓ : ∀ p, p ∈ Γ ↔ Ec p ∈ ratL W V := by
    rintro ⟨s, z, y⟩
    rw [hEapp, hrat]
    simp [Γ, AddSubgroup.mem_prod]
  have hFDP : IsAddFundamentalDomain Γ (𝓨 ×ˢ (𝓩 ×ˢ 𝓨)) lam :=
    isAddFundamentalDomain_prod hμ.2.1 (isAddFundamentalDomain_prod h𝓩 hμ.2.1)
  have hac : lam.map Me ≪ ν := by
    intro s hs
    rw [hνm, Measure.smul_apply] at hs
    exact (smul_eq_zero.1 hs).resolve_left hc.ne'
  have hqmp : QuasiMeasurePreserving Me lam ν := ⟨Me.measurable.aemeasurable, hac⟩
  let eΓ : ratL W V → Γ := fun g => ⟨Ec.symm g, (hmemΓ _).2 (by simpa using g.2)⟩
  have heΓ : Function.Bijective eΓ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun p => ⟨⟨Ec p, (hmemΓ p).1 p.2⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun q : Γ => Ec q.1) h
      simpa [eΓ] using this
    · simp [eΓ]
  haveI : Countable Γ := heΓ.2.countable
  have hFDE : IsAddFundamentalDomain Γ (Me ⁻¹' 𝓕) lam :=
    h𝓕.preimage_of_equiv hqmp heΓ (fun g p => by
      show Me ((Ec.symm g : _) + p) = (g : WO V W) + Me p
      rw [hMe, hMe, map_add (f := _), Ec.apply_symm_apply])
  refine ⟨(c : ℝ), by exact_mod_cast hc, fun T hT hper => ?_⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hT.continuousOn
  have hbd : ∀ x, ‖T x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hKc x
    rw [← hper γ hγ x]
    exact hC _ hx
  have hTE : Continuous fun p => T (Me p) := hT.comp Ec.continuous
  have e1 : ∫ u in 𝓕, T u ∂ν = (c : ℝ) • ∫ u in 𝓕, T u ∂m := by
    rw [hνm, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  have e2 : ∫ u in 𝓕, T u ∂m = ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam := setIntegral_map_equiv Me T 𝓕
  haveI : VAddInvariantMeasure Γ _ lam :=
    ⟨fun g _ hs => Measure.measure_preimage_of_map_eq_self (map_add_left_eq_self lam g.1)
      (measurable_const_vadd g).aemeasurable hs.nullMeasurableSet⟩
  have e3 : ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam = ∫ p in 𝓨 ×ˢ (𝓩 ×ˢ 𝓨), T (Me p) ∂lam :=
    hFDE.setIntegral_eq hFDP (fun g p => by
      show T (Me ((g : _) + p)) = T (Me p)
      rw [hMe, hMe, map_add (f := _)]
      exact hper _ ((hmemΓ _).1 g.2) _)
  have e4 : lam.restrict (𝓨 ×ˢ (𝓩 ×ˢ 𝓨)) = (μ.restrict 𝓨).prod ((η.restrict 𝓩).prod (μ.restrict 𝓨)) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
  rw [e1, e2, e3, e4, integral_prod _ (Integrable.of_bound hTE.aestronglyMeasurable C (ae_of_all _ fun p => hbd _)),
    Complex.real_smul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  have hs : Continuous fun q : Mx D 1 k × Mx D a b => T (Me (s, q)) := hTE.comp (Continuous.prodMk_right s)
  dsimp only
  rw [integral_prod _ (Integrable.of_bound hs.aestronglyMeasurable C (ae_of_all _ fun p => hbd _))]
  rfl

end GlobalTheory.CoordUnfold

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain

theorem IoPair.of_index_eq {D : D7} (hP : IoPair D) (k : Fin D.R.m) (a b : ℕ) (ha : a = k) (hb : b = k + 1)
    (V W : HSp D) (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (hθ : IsInfFam θ) (hC : ChainPar D k)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
    (hW : IsStepWeil k ψ V W ω) (hV : IsVacVec ψ θ M M' f)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hI : IsItW θ M M' ω (ptOf ψ θ M M' f) It)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (hJ : ∀ κ ∈ J, κ ∈ GfC V ∧ ω (κ, 1) f = χ κ • f)
    (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (hν : ν.IsHaarMeasure)
    (h𝓕 : MeasureTheory.IsFundamentalDomain (GQ W) 𝓕 ν)
    (J' : Set (GA D W)) (χ' : GA D W → ℂ) (C : Submodule ℂ (SmT M' →ₗ[ℂ] (GA D W → ℂ)))
    (hle : C ≤ MultT θ M' J' χ') :
    Lift.IoExists ν 𝓕 (thetaKO ω) (ptOf ψ θ M M' f) It C (MultT θ M J χ) := by
  subst ha hb
  exact hP k V W M M' θ ψ hθ hC ω f hW hV It hI J χ hJ ν 𝓕 hν h𝓕 J' χ' C hle

theorem ioYSt_of_ioPair (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : StepsOK R) (hL : LawsOK R)
    (hν : R.models_νY) (hν' : R.models_νY') (hI : R.chain_ItY) : IoYSt R := by
  intro t k hk
  have hkm : k < D.R.m := Nat.lt_of_succ_lt hk
  have hIt := hI
  have hInner := hν
  have hLast := hν'
  unfold RealDat.chain_ItY at hIt
  unfold RealDat.models_νY at hInner
  unfold RealDat.models_νY' at hLast

  have hmeas : (R.νY t (k + 1)).IsHaarMeasure ∧
      MeasureTheory.IsFundamentalDomain (GQ (Yc D (k + 1))) (R.fdY t (k + 1)) (R.νY t (k + 1)) := by
    by_cases h2 : k + 1 + 1 < D.R.m
    · exact ⟨(hInner t (k + 1) h2).1.1, (hInner t (k + 1) h2).2⟩
    · have atLast : ∀ j, j = D.R.m - 1 → (R.νY t j).IsHaarMeasure ∧
          MeasureTheory.IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
        rintro j rfl
        exact ⟨(hLast t).1.1, (hLast t).2⟩
      exact atLast (k + 1) (by omega)
  obtain ⟨hW, hV⟩ := hS.1 t ⟨k, hkm⟩ hk
  exact IoPair.of_index_eq hP ⟨k, hkm⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left hkm.le)
    (min_eq_left hk.le) (Yc D k) (Yc D (k + 1)) (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY t k)
    (R.vY t k) hW hV (R.ItY k) (hIt t k hk) _ _ (hL.1 t k hk) (R.νY t (k + 1)) (R.fdY t (k + 1))
    hmeas.1 hmeas.2 _ _ (R.CC t (k + 1)) le_rfl

end GlobalTheory.Chain
end

section

open Classical MeasureTheory

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

def colMat {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) : Matrix (Var ι d a) (Var ι d a) ℂ :=
  fun w v => if w.1 = v.1 ∧ w.2.1 = v.2.1 then g v.1 w.2.2 v.2.2 else 0

theorem colSub_eq_lsub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a) = GlobalTheory.JointHarm.FMul.lsub (colMat g) := by
  refine algHom_ext fun v => ?_
  rw [GlobalTheory.JointHarm.FMul.lsub_X, colSub, aeval_X]
  obtain ⟨τ, r, c⟩ := v
  simp only [colMat, Fintype.sum_prod_type, ite_and, apply_ite C, map_zero, ite_mul, zero_mul]
  simp

theorem colMat_conjTranspose {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colMat (d := d) g)ᴴ = colMat fun τ => (g τ)ᴴ := by
  ext w v
  simp only [colMat, conjTranspose_apply]
  by_cases h : v.1 = w.1 ∧ v.2.1 = w.2.1
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩, h.1]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1.symm, h'.2.symm⟩, star_zero]

theorem colSub_comp {d a : ℕ} (h g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colSub h : Pol ι d a →ₐ[ℂ] Pol ι d a).comp (colSub g) = colSub fun τ => h τ * g τ := by
  refine algHom_ext fun v => ?_
  rw [AlgHom.comp_apply]
  unfold colSub

  rw [aeval_X, aeval_X, map_sum]

  simp only [map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem colSub_one {d a : ℕ} : (colSub (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) : Pol ι d a →ₐ[ℂ] Pol ι d a) =
    AlgHom.id ℂ _ := by
  refine algHom_ext fun v => ?_
  rw [colSub, aeval_X, Finset.sum_eq_single v.2.2]
  · simp
  · intro b _ hb
    rw [Matrix.one_apply_ne hb]
    simp
  · simp

theorem fockS_colSub_unitary : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (u : ι → Matrix.unitaryGroup (Fin a) ℂ)
    (P Q : GlobalTheory.MinorFrame.Pol ι d a),
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) P)
      (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  intro ι _ a d u P Q
  rw [← Formalism.L2.DIV.fockL_apply, ← Formalism.L2.DIV.fockL_apply, colSub_eq_lsub, GlobalTheory.JointHarm.FMul.fockL_lsub_adj,
    ← colSub_eq_lsub, colMat_conjTranspose, ← colSub_eq_lsub, ← AlgHom.comp_apply, colSub_comp]
  have hu : (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)ᴴ * (u τ : Matrix (Fin a) (Fin a) ℂ)) = fun _ => 1 := by
    funext τ
    exact Matrix.mem_unitaryGroup_iff'.1 (u τ).2
  rw [hu, colSub_one, AlgHom.id_apply]

end GlobalTheory.MinorFrame
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_integral_matrices_separating_rationalPairing : ∀ (D : D7) (W : HSp D) (r : ℕ), ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E), (∀ j a b, IsIntegral ℤ (X j a b)) ∧ ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := by
  first | exact @GlobalTheory.RatPairSep.main | exact GlobalTheory.RatPairSep.main | (intros; apply GlobalTheory.RatPairSep.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.twistDatumValue_eq_prod_localResidueValues : ∀ (D : D7) (a b r : ℕ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)),
      omegaQ Q r ξ 1 y = ∏ PP ∈ Q, qLoc r PP (ξ PP) (y PP) := by
  first | exact @GlobalTheory.StepVec.omegaQ_one_eq_prod_qLoc | exact GlobalTheory.StepVec.omegaQ_one_eq_prod_qLoc | (intros; apply GlobalTheory.StepVec.omegaQ_one_eq_prod_qLoc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_isLocalLevelAtPrimeOfLevelDatum : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ),
    ∃ (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam := by
  first | exact @GlobalTheory.StepVec.exists_isLocLevel | exact GlobalTheory.StepVec.exists_isLocLevel | (intros; apply GlobalTheory.StepVec.exists_isLocLevel <;> assumption)
end
