module

public import GroundTheory.FunctionField.PlaceDefs
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentValuationFibre
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle059
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import ReciprocityTheory.DualLattices.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.length_formula_sum_valuations : ∀ (k K A : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K] [CommRing A] [IsDomain A] [Algebra k A] [Algebra A K] [IsScalarTower k A K] [IsLocalRing A] [IsNoetherianRing A] [IsFractionRing A K] [Algebra.EssFiniteType k A], ¬ IsField A → ∀ f : A, f ≠ 0 → (((Module.length A (A ⧸ Ideal.span {f})).toNat * Module.finrank k (IsLocalRing.ResidueField A) : ℕ) : ℤ) = ∑ᶠ v ∈ {v : GroundTheory.FunctionField.Place k K | (∀ a : A, v.valuation (algebraMap A K a) ≤ 1) ∧ ∀ a ∈ IsLocalRing.maximalIdeal A, v.valuation (algebraMap A K a) < 1}, (v.deg : ℤ) * v.ord (algebraMap A K f) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.length_formula_sum_valuations | exact GlobalTheory.CompanionTheory.Relay.length_formula_sum_valuations | (intros; apply GlobalTheory.CompanionTheory.Relay.length_formula_sum_valuations <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullFlagFrame

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

theorem tri_solve {F : Type} [Field F] {N : ℕ} (T : Fin N → Fin N → F) (a : Fin N → F)
    (hT : ∀ j l, j < l → T j l = 0) (hd : ∀ j, T j j ≠ 0) (i : Fin N)
    (h : ∀ l, i < l → ∑ j, a j * T j l = 0) : ∀ j, i < j → a j = 0 := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨j₀, hj₀, ha₀⟩ := hne
  let S := Finset.univ.filter (fun j => i < j ∧ a j ≠ 0)
  have hS : S.Nonempty := ⟨j₀, by simp [S, hj₀, ha₀]⟩
  have hm : S.max' hS ∈ S := S.max'_mem hS
  obtain ⟨m, hmd⟩ : ∃ m, m = S.max' hS := ⟨_, rfl⟩
  rw [← hmd] at hm
  have hm' : i < m ∧ a m ≠ 0 := by simpa [S] using hm
  have hsum := h m hm'.1
  rw [Finset.sum_eq_single m] at hsum
  · exact mul_ne_zero hm'.2 (hd m) hsum
  · intro j _ hjm
    rcases lt_or_gt_of_ne hjm with hlt | hgt
    · rw [hT j m hlt, mul_zero]
    · have hz : a j = 0 := by
        by_contra hz
        have hjS : j ∈ S := by simp [S, hz, hm'.1.trans hgt]
        have := S.le_max' j hjS
        rw [← hmd] at this
        exact absurd this (not_le.2 hgt)
      rw [hz, zero_mul]
  · simp

section BC

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω₁ : Type} [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem mseg_bcCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (bcCoord x z) s =
      algebraMap Ω Ω₁ (mseg x (restrictChart s)) * ∏ k, z ⟨k, s (.inr k)⟩ := by
  simp [mseg, Fintype.prod_sum_type, bcCoord, joinCoord, restrictChart, map_prod]

theorem map_mem_chartRing_bc (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (bcCoord x z) s ≠ 0) {a : Ω}
    (ha : a ∈ chartRing O (mseg x) (restrictChart s)) :
    algebraMap Ω Ω₁ a ∈ chartRing O (mseg (bcCoord x z)) s := by
  have hZ : (∏ k, z ⟨k, s (.inr k)⟩) ≠ 0 := by
    intro h0
    exact hs (by rw [mseg_bcCoord, h0, mul_zero])
  induction ha using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨j, rfl⟩ := ht
    let j' : ∀ k : K ⊕ K', Sum.elim ι ι' k := fun k =>
      match k with
      | .inl k => j k
      | .inr k => s (.inr k)
    have hj : restrictChart j' = j := rfl
    have hz : (∏ k, z ⟨k, j' (.inr k)⟩) = ∏ k, z ⟨k, s (.inr k)⟩ := rfl
    have e : algebraMap Ω Ω₁ (mseg x j / mseg x (restrictChart s)) =
        mseg (bcCoord x z) j' / mseg (bcCoord x z) s := by
      rw [mseg_bcCoord, mseg_bcCoord, hj, hz, map_div₀, mul_div_mul_right _ _ hZ]
    rw [e]
    exact Algebra.subset_adjoin ⟨j', rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply O Ω Ω₁]
    exact Subalgebra.algebraMap_mem _ r
  | add s t _ _ hs ht => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hs ht
  | mul s t _ _ hs ht => rw [map_mul]; exact Subalgebra.mul_mem _ hs ht

variable {N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
  {V₁ : Type} [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]

theorem repr_bc (bc : V →ₗ[Ω] V₁) (w : Module.Basis (Fin N) Ω V) (w₁ : Module.Basis (Fin N) Ω₁ V₁)
    (hw : ∀ i, w₁ i = bc (w i)) (e : V) (j : Fin N) :
    w₁.repr (bc e) j = algebraMap Ω Ω₁ (w.repr e j) := by
  have h1 : bc e = ∑ i, algebraMap Ω Ω₁ (w.repr e i) • w₁ i := by
    conv_lhs => rw [← w.sum_repr e]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hw, algebraMap_smul]

  rw [h1, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
      mul_one]
  · intro i _ hij
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg hij,
      smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem isFlagFrame_bc (x : (Σ k, ι k) → Ω) (E : ChartBundle O (mseg x) N V)
    (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ) (h : IsFlagFrame x E w b)
    (z : (Σ k, ι' k) → Ω₁) (bc : V →ₗ[Ω] V₁) (w₁ : Module.Basis (Fin N) Ω₁ V₁)
    (hw : ∀ i, w₁ i = bc (w i)) (EB : ChartBundle O (mseg (bcCoord x z)) N V₁)
    (hp : IsPullBC O x z bc E EB) :
    IsFlagFrame (bcCoord x z) EB w₁ (fun i => pullDeg (K' := K') (b i)) := by
  classical
  refine ⟨fun s hs0 i => ?_⟩
  have hs : mseg (bcCoord x z) s ≠ 0 := hs0
  have hc : mseg x (restrictChart s) ≠ 0 := by
    intro h0
    exact hs (by rw [mseg_bcCoord, h0, map_zero, zero_mul])
  obtain ⟨u, hu, hup, hdiag, hgen⟩ :=
    FlagPairExt.exists_frame x E w b h (restrictChart s) hc
  have hx : ∀ k, x ⟨k, restrictChart s k⟩ ≠ 0 := fun k =>
    (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ k)
  have hM : ∀ i, (∏ k, x ⟨k, restrictChart s k⟩ ^ b i k) ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  have hMon : (∏ k : K ⊕ K', (bcCoord x z) ⟨k, s k⟩ ^ pullDeg (K' := K') (b i) k) =
      algebraMap Ω Ω₁ (∏ k, x ⟨k, restrictChart s k⟩ ^ b i k) := by
    rw [Fintype.prod_sum_type]
    simp [pullDeg, bcCoord, joinCoord, restrictChart, map_prod, map_zpow₀]
  have hbu : ∀ j, bc (u j) ∈ EB.lat s := by
    intro j
    rw [hp s hs]
    exact AddSubgroup.subset_closure ⟨1, Subalgebra.one_mem _, u j, hu j, (one_smul _ _).symm⟩
  have hgenL : ∀ v ∈ EB.lat s, ∃ a : Fin N → Ω₁,
      (∀ j, a j ∈ chartRing O (mseg (bcCoord x z)) s) ∧ v = ∑ j, a j • bc (u j) := by
    intro v hv
    rw [hp s hs] at hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, e, he, rfl⟩ := hv
      obtain ⟨t, ht, rfl⟩ := hgen e he
      refine ⟨fun j => a * algebraMap Ω Ω₁ (t j), fun j =>
        Subalgebra.mul_mem _ ha (map_mem_chartRing_bc x z s hs (ht j)), ?_⟩

      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← algebraMap_smul Ω₁ (t j), smul_smul]
    | zero => exact ⟨0, fun _ => Subalgebra.zero_mem _, by simp⟩
    | add v v' _ _ hv hv' =>
      obtain ⟨a, ha, rfl⟩ := hv
      obtain ⟨a', ha', rfl⟩ := hv'
      exact ⟨a + a', fun j => Subalgebra.add_mem _ (ha j) (ha' j), by
        simp [add_smul, Finset.sum_add_distrib]⟩
    | neg v _ hv =>
      obtain ⟨a, ha, rfl⟩ := hv
      exact ⟨-a, fun j => Subalgebra.neg_mem _ (ha j), by simp [Finset.sum_neg_distrib]⟩
  ext t
  constructor
  · rintro ⟨v, hv, htri, rfl⟩
    obtain ⟨a, ha, hav⟩ := hgenL v hv
    let T : Fin N → Fin N → Ω₁ := fun j l => algebraMap Ω Ω₁ (w.repr (u j) l)
    have hrepr : ∀ l, w₁.repr v l = ∑ j, a j * T j l := by
      intro l
      rw [hav]

      simp [T, map_sum, repr_bc bc w w₁ hw]
    have hT : ∀ j l, j < l → T j l = 0 := fun j l hjl => by simp [T, hup j l hjl]
    have hd : ∀ j, T j j ≠ 0 := fun j => by
      simp only [T, hdiag j]
      exact (map_ne_zero _).2 (hM j)
    have hz := tri_solve T a hT hd i fun l hl => by rw [← hrepr l]; exact htri l hl
    refine ⟨a i, ha i, ?_⟩
    rw [hrepr i, Finset.sum_eq_single i]
    · show a i * T i i = _
      rw [hMon]
      simp only [T, hdiag i]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · rw [hT j i hlt, mul_zero]
      · rw [hz j hgt, zero_mul]
    · simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a • bc (u i), EB.stable s a ha _ (hbu i), fun j hj => ?_, ?_⟩
    · simp [repr_bc bc w w₁ hw, hup i j hj]
    · rw [hMon]
      simp [repr_bc bc w w₁ hw, hdiag i]

end BC

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsFlagFrame (joinCoord x z) EB w (fun i => pullDeg (K' := K') (b i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → ∀ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsFlagFrame (bcCoord x z) EB w₁ (fun i => pullDeg (K' := K') (b i)) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E w b h
  refine ⟨?_, ?_⟩
  · intro K' _ _ ι' _ z EB hp
    exact isFlagFrame_bc (Ω₁ := Ω) (V₁ := V) x E w b h z LinearMap.id w (fun _ => rfl) EB hp
  · intro Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc w₁ hw EB hp
    exact isFlagFrame_bc x E w b h z bc w₁ hw EB hp

end GlobalTheory.CompanionTheory.Ar.Num.PullFlagFrame
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Num.Contract

noncomputable section

theorem rename_liftVar_mem_pointIdeal {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    {K K' : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {ι' : K' → Type}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {f : MRing ι R} (hf : f ∈ pointIdeal R x) :
    rename (liftVar ι') f ∈ pointIdeal R (joinCoord x z) := by
  have key : ((rename (Sum.inl : K → K ⊕ K') : MvPolynomial K Ω →ₐ[Ω] _).restrictScalars R).comp
      (pointConeMap R x) =
      (pointConeMap R (joinCoord x z)).comp (rename (liftVar ι')) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, liftVar, joinCoord]
  have hf0 : pointConeMap R x f = 0 := hf
  have h := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply, hf0, map_zero] at h
  exact h.symm

theorem lowered_lt {a : WithBot ℕ∞} {c d n : ℕ} (h : a < ((d + 1 + c : ℕ) : WithBot ℕ∞)) (hn : d < n) :
    WithBot.map (fun e : ℕ∞ => WithTop.map (fun m : ℕ => (m : ℤ) - c) e) a <
      ((n : ℕ) : WithBot (WithTop ℤ)) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) < (((d + 1 + c : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      exact absurd (WithBot.coe_lt_coe.mp h') (by simp)
    | coe m =>
      have h' : (((m : ℕ) : ℕ∞) : WithBot ℕ∞) < (((d + 1 + c : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      have hm : m < d + 1 + c := by exact_mod_cast WithBot.coe_lt_coe.mp h'
      show ((((m : ℤ) - c : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) <
        (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))

theorem dim_quot_le {A : Type*} [CommRing A] {I J : Ideal A} (h : I ≤ J) :
    ringKrullDim (A ⧸ J) ≤ ringKrullDim (A ⧸ I) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vNumL_eq_zero_of_dim_le {ϖ : O} (hϖ : Irreducible ϖ)
    {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ o, Fintype (ι' o)]
    {W : Ideal (MRing ι' O)} (hW : IsMultiProjPrime W) (hϖW : (C ϖ : MRing ι' O) ∈ W)
    {K : Type} [Fintype K] [DecidableEq K] (j : K ↪ K') {n : ℕ}
    (hdim : ringKrullDim (MRing ι' O ⧸ W) ≤ ((n + Fintype.card K' : ℕ) : WithBot ℕ∞))
    (hcon : GroundTheory.Heights₂.Heights.FieldNumbers.relDim
      (GroundTheory.Heights₂.Heights.FieldNumbers.contractPrime j (specialIdeal W)) <
        ((n : ℕ) : WithBot (WithTop ℤ)))
    (l : List (K' → ℤ)) (hl : l.length = n) (hlj : ∀ b ∈ l, ∀ o, o ∉ Set.range j → b o = 0) :
    vNumL W l = 0 := by
  subst hl
  obtain ⟨hQp, -, hrelIff, -⟩ :=
    SpecialIdealCorresp.full O ϖ hϖ K' ι' ⊥ W hW.isPrime hϖW
  have hQm := SpecialIdealMultiHomog.full O K' ι' W hW.multiHomog
  have hdimQ := SpecialQuotDim.full O ϖ hϖ K' ι' W hϖW
  change intNum (IsLocalRing.ResidueField O) (specialIdeal W) l.get = 0
  by_cases hcase : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞)
  · exact IntNumVanish.full (IsLocalRing.ResidueField O) K' ι' l.length (specialIdeal W) hQp hQm
      (Or.inr hcase) l.get
  · have hdimEq : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞) :=
      le_antisymm (hdimQ ▸ hdim) (not_lt.mp hcase)
    have hrelQ : GroundTheory.Heights₂.Heights.FieldNumbers.relDim (specialIdeal W) =
        ((l.length : ℕ) : WithBot (WithTop ℤ)) := by
      rw [GroundTheory.Heights₂.Heights.FieldNumbers.relDim, hdimEq]
      have : (((l.length + Fintype.card K' : ℕ) : ℤ) - Fintype.card K') = l.length := by
        push_cast; ring
      exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
    have hz := GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaContracted.full
      (IsLocalRing.ResidueField O) K K' j ι' (specialIdeal W)
      ⟨hQp, hQm, hrelIff.mp hW.relevant⟩ l.length hrelQ hcon (fun i => l.get i ∘ j)
    rw [← hz]
    congr 1
    funext i
    exact (SegreFlagCutContraction.pullDeg_comp_of_eq_zero j _
      (hlj _ (List.get_mem l i))).symm

theorem specialIdeal_le_contract {Ω : Type} [Field Ω] [Algebra O Ω]
    {K K' : Type} [Fintype K] [DecidableEq K] [DecidableEq K'] {ι : K → Type} [∀ k, Fintype (ι k)]
    {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι'))} (hW : pointIdeal O (joinCoord x z) ≤ W) :
    specialIdeal (pointIdeal O x) ≤
      (GroundTheory.Heights₂.Heights.FieldNumbers.contractPrime (Function.Embedding.inl : K ↪ K ⊕ K')
        (specialIdeal W) : Ideal (MRing ι (IsLocalRing.ResidueField O))) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  show rename (liftVar ι') (MvPolynomial.map (IsLocalRing.residue O) f) ∈ specialIdeal W
  rw [← MvPolynomial.map_rename]
  exact Ideal.mem_map_of_mem _ (hW (rename_liftVar_mem_pointIdeal x z hf))

theorem relDim_contract_lt {Ω : Type} [Field Ω] [Algebra O Ω] {ϖ : O} (hϖ : Irreducible ϖ)
    {K K' : Type} [Fintype K] [DecidableEq K] [DecidableEq K'] {ι : K → Type} [∀ k, Fintype (ι k)]
    {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {d n : ℕ} (hdn : d < n)
    (hV : IsModelOver (pointIdeal O x) d)
    {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι'))} (hW : pointIdeal O (joinCoord x z) ≤ W) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim
      (GroundTheory.Heights₂.Heights.FieldNumbers.contractPrime (Function.Embedding.inl : K ↪ K ⊕ K')
        (specialIdeal W)) < ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have hb := SpecialDimBound.full O ϖ hϖ K ι (pointIdeal O x) d hV
  exact lowered_lt (lt_of_le_of_lt (dim_quot_le (specialIdeal_le_contract x z hW)) hb) hdn

end

end GlobalTheory.CompanionTheory.Ar.Num.Contract

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem vNumL_pull_eq_zero_of_contracted : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d r : ℕ, 0 < r → IsModelOver (pointIdeal O x) d → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (W : Ideal (MRing (Sum.elim ι ι') O)), IsMultiProjPrime W → pointIdeal O (joinCoord x z) ≤ W → (C ϖ : MRing (Sum.elim ι ι') O) ∈ W → ∀ l : List (K → ℤ), l.length = d + r → ringKrullDim (MRing (Sum.elim ι ι') O ⧸ W) ≤ ((d + r + Fintype.card (K ⊕ K') : ℕ) : WithBot ℕ∞) → vNumL W (l.map (pullDeg (K' := K'))) = 0 := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d r hr hV K' _ _ ι' _ z W hW hPW hϖW l hl hdim
  refine Contract.vNumL_eq_zero_of_dim_le hϖ hW hϖW (Function.Embedding.inl : K ↪ K ⊕ K')
    (n := d + r) hdim (Contract.relDim_contract_lt hϖ x z (by omega) hV hPW)
    (l.map (pullDeg (K' := K'))) (by simpa using hl) ?_
  intro b hb o ho
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hb
  cases o with
  | inl k => exact absurd ⟨k, rfl⟩ ho
  | inr k => rfl

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem htd_restrict_coefficients : ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : R), HodgeTateSetting p v R Oe σ cp → ∀ H : HodgeTateDatum p g v R Oe σ cp, HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp ∧ ∃ H' : HodgeTateDatum p g v R ℤ_[p] AlgEquiv.refl cp, H'.AA = H.AA ∧ H'.Ht = H.Ht ∧ H'.Bt = H.Bt ∧ H'.E = H.E := by
  intro p _ g C _ v R _ _ _ Oe _ _ σ cp hS H
  refine ⟨⟨hS.integers, hS.p_lt, hS.p_ne, hS.cp_val, fun _ => rfl⟩,
    { ρ := H.ρ.comp (Algebra.ofId _ _)
      ρL := H.ρL.comp (algebraMap _ _)
      P := H.P
      PL := H.PL
      E := H.E
      E_alternating := H.E_alternating
      isUnit_det_E := H.isUnit_det_E
      E_equivariant := fun a => ?_
      projectors := ⟨H.projectors.1, H.projectors.2.1, H.projectors.2.2.1, fun a => H.projectors.2.2.2.1 _, fun a => H.projectors.2.2.2.2 _⟩
      Ht := H.Ht
      Bt := H.Bt
      Ht_equivariant := ⟨fun a => ?_, H.Ht_equivariant.2⟩
      form_eq_alt := H.form_eq_alt
      AA := H.AA
      h3 := fun a => H.h3 _
      h4 := H.h4
      h5 := H.h5
      φ := H.φ
      cotangent_surjective := H.cotangent_surjective
      cotangent_ker_eq := H.cotangent_ker_eq
      cotangent_linear := fun a => H.cotangent_linear _ }, rfl, rfl, rfl, rfl⟩
  · have := H.E_equivariant (algebraMap ℤ_[p] Oe a)
    rw [σ.commutes] at this
    exact this
  · have := H.Ht_equivariant.1 (algebraMap ℤ_[p] Oe a)
    rw [σ.commutes] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.GR
end
end
