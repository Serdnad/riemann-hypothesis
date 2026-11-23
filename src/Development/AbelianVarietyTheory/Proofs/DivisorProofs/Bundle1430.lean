module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1331
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle961
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
namespace GlobalTheory.SuppDen

variable {F : Type} [Field F] [NumberField F]

theorem norm_le_one_iff_mem (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    ‖y‖ ≤ 1 ↔ y ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F |
      ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

def denSet (κ : Type) (m : ℕ) : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
  {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), ‖(m : v.adicCompletion F) * y i v‖ ≤ 1}

theorem natCast_mul_apply (m : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((m : FiniteAdeleRing (𝓞 F) F) * a) v = (m : v.adicCompletion F) * a v := by
  have hm : (m : FiniteAdeleRing (𝓞 F) F) v = (m : v.adicCompletion F) := by
    induction m with
    | zero => rfl
    | succ n ih =>
      rw [Nat.cast_succ, Nat.cast_succ]
      change (n : FiniteAdeleRing (𝓞 F) F) v + 1 = _
      rw [ih]
  simp [hm]

theorem isOpen_denSet (κ : Type) [Finite κ] (m : ℕ) : IsOpen (denSet (F := F) κ m) := by
  have h : denSet (F := F) κ m = ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      (m : FiniteAdeleRing (𝓞 F) F) * y i) ⁻¹'
      {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [denSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, natCast_mul_apply,
      norm_le_one_iff_mem]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_integral.preimage ((continuous_const_mul _).comp (continuous_apply i))

theorem norm_mul_le_one_of_dvd {v : HeightOneSpectrum (𝓞 F)} {m m' : ℕ} (hd : m ∣ m')
    {z : v.adicCompletion F} (hz : ‖(m : v.adicCompletion F) * z‖ ≤ 1) :
    ‖(m' : v.adicCompletion F) * z‖ ≤ 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.cast_mul, mul_comm (m : v.adicCompletion F), mul_assoc, norm_mul]
  exact mul_le_one₀ (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v k) (norm_nonneg _) hz

theorem denSet_mono (κ : Type) {m m' : ℕ} (hd : m ∣ m') :
    denSet (F := F) κ m ⊆ denSet κ m' :=
  fun _ hy i v => norm_mul_le_one_of_dvd hd (hy i v)

theorem exists_denom (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : ℕ, 0 < d ∧ ∀ v : HeightOneSpectrum (𝓞 F), ‖(d : v.adicCompletion F) * a v‖ ≤ 1 := by
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => max 1 ‖a v‖₊).Finite := by
    apply (Filter.eventually_cofinite.1 a.2).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro hmem
    apply hv
    have : ‖a v‖ ≤ 1 := (norm_le_one_iff_mem v _).2 hmem
    exact max_eq_left (by exact_mod_cast this)
  obtain ⟨d, hd, -, h⟩ := GlobalTheory.SmoothForms.denom_global (F := F)
    (fun v => max 1 ‖a v‖₊) (fun v => le_max_left _ _) hf
  exact ⟨d, hd, fun v => h v _ (le_max_right _ _)⟩

theorem exists_mem_denSet (κ : Type) [Fintype κ] (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, 0 < m ∧ y ∈ denSet κ m := by
  classical
  choose d hd h using fun i => exists_denom (y i)
  exact ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i v =>
    norm_mul_le_one_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) (h i v)⟩

theorem support_bounded_denominators {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : κ → AF F, g (fun i => (x i).2) ≠ 0 →
      ∀ i v, ‖(M : Fv F v) * evFin F v (x i)‖ ≤ 1 := by
  classical
  have hK : IsCompact (tsupport g) := hg.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun n : ℕ => denSet (F := F) κ (n + 1))
    (fun n => isOpen_denSet κ _) (fun y _ => by
      obtain ⟨m, hm, hy⟩ := exists_mem_denSet κ y
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
      exact Set.mem_iUnion.2 ⟨n, by simpa using hy⟩)
  refine ⟨∏ n ∈ t, (n + 1), Finset.prod_pos fun n _ => n.succ_pos, fun x hx i v => ?_⟩
  have hy : (fun i => (x i).2) ∈ tsupport g := subset_tsupport _ hx
  obtain ⟨n, hn, hyn⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact denSet_mono κ (Finset.dvd_prod_of_mem (fun n : ℕ => n + 1) hn) hyn i v

end GlobalTheory.SuppDen
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.schwartz_bruhat_partial_evaluation : ∀ (k : Type) [TopologicalSpace k] [T2Space k] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ f ∈ SB (κ ⊕ κ' → k),
    (∀ x₁ : κ → k, (fun x₂ : κ' → k => f (Sum.elim x₁ x₂)) ∈ SB (κ' → k)) ∧
      ∀ l : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ, (fun x₁ : κ → k => l fun x₂ => f (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
  first | exact @GlobalTheory.SliceSB.slice_mem | exact GlobalTheory.SliceSB.slice_mem | (intros; apply GlobalTheory.SliceSB.slice_mem <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.SBBlocks

theorem isClosed_support_of_isLocallyConstant {Z : Type} [TopologicalSpace Z] {f : Z → ℂ}
    (hf : IsLocallyConstant f) : IsClosed (Function.support f) := by
  have : Function.support f = (f ⁻¹' {0})ᶜ := by ext; simp
  rw [this]; exact (hf.isOpen_fiber 0).isClosed_compl

theorem mem_SB_of_support_subset {Z : Type} [TopologicalSpace Z] {f : Z → ℂ} {C : Set Z}
    (hf : IsLocallyConstant f) (hC : IsCompact C) (hs : Function.support f ⊆ C) : f ∈ SB Z :=
  ⟨hf, HasCompactSupport.intro' (hC.of_isClosed_subset (isClosed_support_of_isLocallyConstant hf) hs)
    (isClosed_support_of_isLocallyConstant hf) fun _ hx => Function.notMem_support.1 hx⟩

theorem prod_decomp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X × Y → ℂ)
    (hh : h ∈ SB (X × Y)) :
    ∃ (m : ℕ) (a : Fin m → X → ℂ) (b : Fin m → Y → ℂ), (∀ j, a j ∈ SB X) ∧ (∀ j, b j ∈ SB Y) ∧
      ∀ x y, h (x, y) = ∑ j, a j x * b j y := by
  classical
  obtain ⟨hlc, hcs⟩ := hh
  have hK : IsCompact (tsupport h) := hcs.isCompact
  have hK1 : IsCompact (Prod.fst '' tsupport h) := hK.image continuous_fst
  have hK2 : IsCompact (Prod.snd '' tsupport h) := hK.image continuous_snd
  have hzero : ∀ x y, h (x, y) ≠ 0 → x ∈ Prod.fst '' tsupport h ∧ y ∈ Prod.snd '' tsupport h :=
    fun x y hne => ⟨⟨(x, y), subset_tsupport h hne, rfl⟩, ⟨(x, y), subset_tsupport h hne, rfl⟩⟩
  let s : Y → X → ℂ := fun y x => h (x, y)
  have hs : IsLocallyConstant s := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    have key : ∀ᶠ y in 𝓝 y₀, ∀ x ∈ Prod.fst '' tsupport h, h (x, y) = h (x, y₀) := by
      refine hK1.eventually_forall_of_forall_eventually (P := fun y x => h (x, y) = h (x, y₀)) ?_
      intro x _
      have h1 : IsLocallyConstant (fun z : Y × X => h (z.2, z.1)) := hlc.comp_continuous continuous_swap
      have h2 : IsLocallyConstant (fun z : Y × X => h (z.2, y₀)) :=
        hlc.comp_continuous (continuous_snd.prodMk continuous_const)
      filter_upwards [h1.eventually_eq (y₀, x), h2.eventually_eq (y₀, x)] with z hz1 hz2
      rw [hz1, hz2]
    filter_upwards [key] with y hy
    funext x
    by_cases hx : x ∈ Prod.fst '' tsupport h
    · exact hy x hx
    · show h (x, y) = h (x, y₀)
      rw [image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩),
        image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩)]
  have hsSB : ∀ y, s y ∈ SB X := fun y =>
    mem_SB_of_support_subset (hlc.comp_continuous (continuous_id.prodMk continuous_const)) hK1
      (fun x hx => (hzero x y hx).1)
  have hsne : ∀ y, s y ≠ 0 → y ∈ Prod.snd '' tsupport h := fun y hy => by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hy
    exact (hzero x y hx).2
  obtain ⟨t, ht⟩ := hK2.elim_finite_subcover (fun φ : X → ℂ => s ⁻¹' {φ}) (fun φ => hs.isOpen_fiber φ)
    (fun y _ => Set.mem_iUnion.2 ⟨s y, rfl⟩)
  let t' := t.filter (fun φ => φ ≠ 0 ∧ φ ∈ SB X)
  let bb : (X → ℂ) → Y → ℂ := fun φ y => if s y = φ then 1 else 0
  have hbSB : ∀ φ ∈ t', bb φ ∈ SB Y := by
    intro φ hφ
    have hφ0 : φ ≠ 0 := (Finset.mem_filter.1 hφ).2.1
    refine mem_SB_of_support_subset (hs.comp fun v => if v = φ then (1 : ℂ) else 0) hK2 ?_
    intro y hy
    have : s y = φ := by
      by_contra hne
      exact hy (if_neg hne)
    exact hsne y (this ▸ hφ0)
  have hsum : ∀ x y, h (x, y) = ∑ φ ∈ t', φ x * bb φ y := by
    intro x y
    have e1 : ∑ φ ∈ t', φ x * bb φ y = ∑ φ ∈ t', if s y = φ then φ x else 0 :=
      Finset.sum_congr rfl fun φ _ => by simp only [bb]; split_ifs <;> simp
    rw [e1, Finset.sum_ite_eq]
    split_ifs with hin
    · rfl
    · show s y x = 0
      by_contra hne
      have hy0 : s y ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
      apply hin
      obtain ⟨φ, hφ, hyφ⟩ := Set.mem_iUnion₂.1 (ht (hsne y hy0))
      have : s y = φ := hyφ
      exact Finset.mem_filter.2 ⟨this ▸ hφ, hy0, hsSB y⟩
  refine ⟨t'.card, fun j => (t'.equivFin.symm j : X → ℂ), fun j => bb (t'.equivFin.symm j),
    fun j => (Finset.mem_filter.1 (t'.equivFin.symm j).2).2.2, fun j => hbSB _ (t'.equivFin.symm j).2, ?_⟩
  intro x y
  rw [hsum x y, ← Finset.sum_coe_sort t']
  exact (Equiv.sum_comp t'.equivFin.symm (fun φ : t' => (φ : X → ℂ) x * bb φ y)).symm

theorem sum_prod_blocks {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (g : (κ ⊕ κ' → Af F) → ℂ) (hg : g ∈ SB (κ ⊕ κ' → Af F)) :
    ∃ (m : ℕ) (a : Fin m → (κ → Af F) → ℂ) (b : Fin m → (κ' → Af F) → ℂ), (∀ j, a j ∈ SB (κ → Af F)) ∧
      (∀ j, b j ∈ SB (κ' → Af F)) ∧ ∀ x x', g (Sum.elim x x') = ∑ j, a j x * b j x' := by
  let e : (κ ⊕ κ' → Af F) ≃ₜ (κ → Af F) × (κ' → Af F) := Homeomorph.sumArrowHomeomorphProdArrow
  have hh : g ∘ e.symm ∈ SB ((κ → Af F) × (κ' → Af F)) :=
    ⟨hg.1.comp_continuous e.symm.continuous, hg.2.comp_homeomorph e.symm⟩
  obtain ⟨m, a, b, ha, hb, hab⟩ := prod_decomp _ hh
  refine ⟨m, a, b, ha, hb, fun x x' => ?_⟩
  rw [← hab]
  show g _ = g (e.symm (x, x'))
  congr 1

end GlobalTheory.SBBlocks
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

theorem _root_.GlobalTheory.T.degree_nonneg_of_curveDegree_nonneg_over_zmod : ∀ (p : ℕ) [Fact p.Prime] (V : Scheme.{0}) [Algebra (ZMod p) Γ(V, ⊤)], IsProjOver (strHom (ZMod p) (X := V)) → topologicalKrullDim V ≤ 1 → ∀ N : LB V, N.IsLB → (∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) (N.pull i) 1) → 0 ≤ degOfRank (ZMod p) (toMod N) 1 := by
  first | exact @GlobalTheory.CurveDevissage.degOfRank_nonneg | exact GlobalTheory.CurveDevissage.degOfRank_nonneg | (intros; apply GlobalTheory.CurveDevissage.degOfRank_nonneg <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_eq_genericRank_mul : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → ∀ (ι : Type) [Fintype ι], topologicalKrullDim Z ≤ (Fintype.card ι : ℕ) → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (P : ι → LB Z), (∀ i, (P i).IsLB) → interNum κ G P = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) P := by
  first | exact @GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver | exact GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver | (intros; apply GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

namespace GlobalTheory.CompHS

theorem nonempty_cartier_of_locally_principal : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData),
    (∀ y : Y, ∃ (W : Y.affineOpens) (a : Γ(Y, W.1)), y ∈ W.1 ∧ a ∈ nonZeroDivisors Γ(Y, W.1) ∧
      I.ideal W = Ideal.span {a}) → Nonempty (Cartier I) := by
  intro Y I h
  obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq (I := I) h
  have hLB : D.lb.IsLB := by
    refine { cover := D.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      exact Units.ext (D.eq_trans_on i i le_rfl le_rfl (c := 1) (one_mul _).symm).symm
    · intro i j k
      have hi : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i := inf_le_left.trans inf_le_left
      have hj : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j := inf_le_left.trans inf_le_right
      have hk : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U k := inf_le_right
      refine Units.ext (D.eq_trans_on i k hi hk ?_)
      rw [D.trans_spec_on i j hi hj, D.trans_spec_on j k hj hk, ← mul_assoc]
      rfl
  refine ⟨{ P := D.lb, isLB := hLB, t := D.canonical, reg := fun i y hi => ?_, cut := ?_ }⟩
  · exact GlobalTheory.Cartier.isRegularFn_iff_germ.1 (D.regular i) y hi
  · refine ideal_ext_stalk fun y => ?_
    obtain ⟨i, hi⟩ := D.exists_mem y
    rw [stalkId_cutIdeal hLB _ i y hi, ← hD, D.stalkId_idealSheaf i y hi, Set.range_const]
    rfl

end GlobalTheory.CompHS
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

namespace GlobalTheory.CompHS.Modif

theorem geometricallyConnected_str : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (U : Y.Opens) (D : ℕ)
    (M : Modif p U D), SmoothOfRelativeDimension D p → GeometricallyConnected p → Dense (U : Set Y) →
    GeometricallyConnected M.str := by
  intro F _ Y p U D M hs hc hd
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : GeometricallyIntegral p := GlobalTheory.geometricallyIntegral_of_smooth p
  have : Nonempty Y := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Sp F))
    obtain ⟨y, -⟩ := p.surjective x
    exact ⟨y⟩
  obtain ⟨u, hu⟩ := hd.nonempty
  have : Surjective (U.ι ≫ p) := ⟨fun x => ⟨⟨u, hu⟩, Subsingleton.elim _ _⟩⟩
  have hU : GeometricallyIrreducible (U.ι ≫ p) := inferInstance
  have : IsIso (M.σ ∣_ U) := M.iso
  have e : M.opn.ι ≫ M.str = (M.σ ∣_ U) ≫ (U.ι ≫ p) := by
    show (M.opn.ι ≫ M.σ) ≫ p = _
    rw [← morphismRestrict_ι, Category.assoc]
  have hO : GeometricallyIrreducible (M.opn.ι ≫ M.str) := by
    have sq : IsPullback (M.σ ∣_ U) (M.opn.ι ≫ M.str) (U.ι ≫ p) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [e, Category.comp_id]⟩
    exact MorphismProperty.of_isPullback sq hU
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have hy : UniversallyOpen y := inferInstance
  have hf : UniversallyOpen fst := MorphismProperty.of_isPullback h.flip hy
  have hdense : Dense ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z) := M.dense.preimage fst.isOpenMap
  have hsq : IsPullback (fst ∣_ M.opn) ((fst ⁻¹ᵁ M.opn).ι ≫ snd) (M.opn.ι ≫ M.str) y :=
    (isPullback_morphismRestrict fst M.opn).paste_vert h
  have : IrreducibleSpace (fst ⁻¹ᵁ M.opn) :=
    hO.geometrically_irreducibleSpace y _ _ hsq
  have hirr : IsIrreducible ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z) := by
    have := (IrreducibleSpace.isIrreducible_univ (fst ⁻¹ᵁ M.opn)).image _
      (fst ⁻¹ᵁ M.opn).ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at this
  have : IrreducibleSpace Z := by
    have hc := hirr.closure
    rw [hdense.closure_eq] at hc
    exact irreducibleSpace_def Z |>.mpr hc
  exact (connectedSpace_iff_univ).mpr (IrreducibleSpace.isIrreducible_univ Z).isConnected

end GlobalTheory.CompHS.Modif
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.eventually_exists_ample_pow_sections_cutting_out_closed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∃ (r : ℕ) (κ : Fin r → (lbPow N l).Sec), (∀ i, GlobalTheory.secPull (κ i) (redι Z) = 0) ∧ (∀ i, ∀ y ∈ Z, y ∉ nonzeroLocus (κ i)) ∧ ∀ y, y ∉ Z → ∃ i, y ∈ nonzeroLocus (κ i) := by
  first | exact @GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out | exact GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out | (intros; apply GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.eventually_exists_lift_section_of_ample_pow_from_closed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∀ σ : ((lbPow N l).pull (redι Z)).Sec, ∃ s : (lbPow N l).Sec, GlobalTheory.secPull s (redι Z) = σ := by
  first | exact @GlobalTheory.LiftClosed.eventually_exists_secPull_eq | exact GlobalTheory.LiftClosed.eventually_exists_secPull_eq | (intros; apply GlobalTheory.LiftClosed.eventually_exists_secPull_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefFieldDescent

theorem interNum_one_nonneg_of_isNef {k : Type} [Field k] {V : Scheme.{0}} [Algebra k Γ(V, ⊤)]
    (hp : IsProjOver (strHom k (X := V))) (hd : topologicalKrullDim V ≤ 1) {N : LB V} (hN : IsNef k N) :
    0 ≤ interNum k (GlobalTheory.structureModule V) ![N] := by
  refine CurveDevissage.interNum_one_nonneg hp hd hN.isLB (fun Z i hi hZ _ ha hdZ => ?_) _ inferInstance
  have hpr : IsProper (strHom k (X := V)) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  have h := (isNef_iff_isClosedImmersion.1 hN).2 Z i hi hZ hdZ inferInstance
  rw [interNumOn, interNum_pushforward_of_isClosedImmersion ha _ (isLB_vecOne hN.isLB)] at h
  rw [topSelf_def]
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j; rfl

theorem isNef_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ L : LB Y, L.IsLB → (letI := algebraΓOfHom q; IsNef E (L.pull π)) → (letI := algebraΓOfHom p; IsNef k L) := by
  intro k E _ _ _ Y X p q π H hp L hL hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  refine ⟨hL, fun C hC => ?_⟩
  have H₁ : IsPullback (pullback.fst (redι C) π) (pullback.snd (redι C) π ≫ q) (redι C ≫ p)
      (spMap (algebraMap k E)) := (IsPullback.of_hasPullback (redι C) π).paste_vert H
  have hpC : IsProjOver (redι C ≫ p) := ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
  have hpr : IsProper (redι C ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hpC).1
  have hp' := ProjSpace.isProjOver_of_isPullback_spMap _ H₁ hpC
  have hd : topologicalKrullDim (pullback (redι C) π : Scheme.{0}) ≤ 1 :=
    (FieldExtDim.topologicalKrullDim_baseChange_le k E _ _ _ _ _ H₁).trans
      ((topologicalKrullDim_red C).trans hC.2).le
  have hLC := LB.isLB_pull hL (redι C)
  have key := FieldChangeInter.interNum_pull H₁ (isLB_vecOne hLC)
  letI := algebraΓOfHom (pullback.snd (redι C) π ≫ q)
  have hN' : IsNef E ((L.pull π).pull (pullback.snd (redι C) π)) :=
    hN.pull_of_isClosedImmersion _ fun _ => rfl
  have h0 := interNum_one_nonneg_of_isNef (k := E)
    (by rw [strHom_eq (f := pullback.snd (redι C) π ≫ q) fun _ => rfl]; exact hp') hd hN'
  rw [interNumRed_one_eq hL]
  refine (h0.trans_eq ?_).trans_eq key
  refine interNum_congr_cls E _ (isLB_vecOne hN'.isLB)
    (fun i => LB.isLB_pull (isLB_vecOne hLC i) _) fun i => ?_
  fin_cases i
  change pull _ (pull π (cls L hL)) = pull _ (pull (redι C) (cls L hL))
  simp only [← pull_comp, pullback.condition]

end GlobalTheory.NefFieldDescent
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.isAmple_tensor_nef_of_nonzeroSectionPow_induction : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ A M : LB X, IsAmpleLB A → IsNef k M → (∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r)) → IsAmpleLB (tens A M) := by
  first | exact @GlobalTheory.isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step | exact GlobalTheory.isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step | (intros; apply GlobalTheory.isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.algebraic_morse_exists_section_ample_sub_generated : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsGenerated B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  first | exact @GlobalTheory.exists_sec_of_ample_sub_generated | exact GlobalTheory.exists_sec_of_ample_sub_generated | (intros; apply GlobalTheory.exists_sec_of_ample_sub_generated <;> assumption)
end
