module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle079
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Invariant.Profinite
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Mathlib.FieldTheory.Galois.Infinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.MeasureTheory.Group.LIntegral

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

open IsLocalRing

theorem exists_algEquiv_rootOfUnity_eq_pow (V K : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (V ⧸ maximalIdeal V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Algebra V Ω] [IsScalarTower V K Ω] :
    ∃ φ : Ω ≃ₐ[K] Ω, ∀ (x : Ω) (m : ℕ), (m : V) ∉ maximalIdeal V → x ^ m = 1 →
      φ x = x ^ Nat.card (V ⧸ maximalIdeal V) := by
  have : IsGalois K Ω := {}
  have hc : SMulCommClass (Ω ≃ₐ[K] Ω) V Ω := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    exact map_smul g _ _⟩
  let : TopologicalSpace (integralClosure V Ω) := ⊥
  have : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  have : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral V k := by
      have h2 : IsIntegral V (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff ).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have : FaithfulSMul V (integralClosure V Ω) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := integralClosure V Ω) (maximalIdeal V)
  let : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  let : Field (integralClosure V Ω ⧸ Q) := Ideal.Quotient.field _
  let : Fintype (V ⧸ maximalIdeal V) := Fintype.ofFinite _
  have : Algebra.IsAlgebraic (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) := by
    have hi : Algebra.IsIntegral (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) :=
      Ideal.Quotient.algebra_isIntegral_of_liesOver _ _
    exact hi.isAlgebraic
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) Q
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  have hu : Q.under V = maximalIdeal V := hQo.over.symm
  have hF : IsArithFrobAt V σ.1 Q := by
    intro x
    have h := DFunLike.congr_fun hσ (Ideal.Quotient.mk _ x)
    rw [← Ideal.Quotient.eq, map_pow, hu, Nat.card_eq_fintype_card]
    exact h
  refine ⟨σ.1, fun x m hm hx => ?_⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (by simp))
  have hxi : IsIntegral V x := IsIntegral.of_pow hm0 (by rw [hx]; exact isIntegral_one)
  have hmQ : ((m : ℕ) : integralClosure V Ω) ∉ Q := by
    intro h
    apply hm
    rw [← hu, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact h
  have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF (ζ := ⟨x, hxi⟩) (m := m)
    (Subtype.ext hx) hmQ
  rw [hu] at h
  exact congrArg Subtype.val h

theorem exists_frobenius_Kur (l : ℕ) [Fact l.Prime] :
    ∃ σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l),
      ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l := by
  have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  obtain ⟨φ, hφ⟩ := exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
    (Finite.of_equiv _ e.symm.toEquiv) (Om l)
  rw [hcard] at hφ
  have hφ' : ∀ (x : Om l) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → φ x = x ^ l := by
    intro x m hm hx
    refine hφ x m (fun h => hm ?_) hx
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
    exact h
  have hle : (MaximalUnramifiedExtension l).map (φ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩
    exact ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  refine ⟨((φ : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict (MaximalUnramifiedExtension l).toSubalgebra
    (fun x => hle ⟨x, x.2, rfl⟩), fun c m _ hlm hc => Subtype.ext ?_⟩
  exact hφ' c m hlm (congrArg Subtype.val hc)

end GlobalTheory.MemLoc
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeWeil

theorem inner_eq {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [MulAction G X] (x₀ : X)
    (μ' : Measure (MulAction.stabilizer G x₀)) [μ'.IsMulLeftInvariant] (f : G → ℝ≥0∞) (a b : G)
    (hab : a • x₀ = b • x₀) :
    ∫⁻ h, f (a * (h : G)) ∂μ' = ∫⁻ h, f (b * (h : G)) ∂μ' := by
  have hc : b⁻¹ * a ∈ MulAction.stabilizer G x₀ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hab, inv_smul_smul]
  rw [← lintegral_mul_left_eq_self (μ := μ') (fun h => f (b * (h : G))) ⟨_, hc⟩]
  simp [← mul_assoc]

theorem weil_formula : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), ∀ (μ' : Measure (MulAction.stabilizer G x₀)) (ν : Measure X), μ'.IsHaarMeasure → IsFiniteMeasureOnCompacts ν → ν ≠ 0 → (∀ g : G, ν.map (fun y => g • y) = ν) → ν {y | ¬ ∃ g : G, g • x₀ = y} = 0 → ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (s y * (h : G)) ∂μ' ∂ν := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x₀ μ' ν hμ' hνc hν0 hinv hnull
  obtain ⟨-, s₀, hs₀m, hs₀⟩ := GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section G X x₀
  have hcont : Continuous fun g : G => g • x₀ := continuous_id.smul continuous_const
  have hclosed : IsClosed ((MulAction.stabilizer G x₀ : Subgroup G) : Set G) :=
    isClosed_eq hcont continuous_const
  have hemb : IsClosedEmbedding (Subtype.val : MulAction.stabilizer G x₀ → G) :=
    hclosed.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace (MulAction.stabilizer G x₀) := hemb.locallyCompactSpace
  have : SecondCountableTopology (MulAction.stabilizer G x₀) :=
    hemb.isEmbedding.secondCountableTopology
  have : SigmaCompactSpace (MulAction.stabilizer G x₀) := inferInstance
  have : IsLocallyFiniteMeasure μ' := inferInstance
  have : SigmaFinite μ' := inferInstance
  have hae : ∀ᵐ y ∂ν, ∃ g : G, g • x₀ = y := hnull
  have hΦ : Measurable fun p : X × MulAction.stabilizer G x₀ => s₀ p.1 * (p.2 : G) :=
    (hs₀m.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  set μ : Measure G := (ν.prod μ').map
    (fun p : X × MulAction.stabilizer G x₀ => s₀ p.1 * (p.2 : G)) with hμ
  have key0 : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (s₀ y * (h : G)) ∂μ' ∂ν := by
    intro f hf
    rw [hμ, lintegral_map hf hΦ]
    exact lintegral_prod _ (hf.comp hΦ).aemeasurable
  have hleft : μ.IsMulLeftInvariant := by
    refine ⟨fun g => Measure.ext_of_lintegral _ fun f hf => ?_⟩
    have hF : Measurable fun y => ∫⁻ h, f (s₀ y * (h : G)) ∂μ' :=
      (hf.comp hΦ).lintegral_prod_right'
    rw [lintegral_map hf (measurable_const_mul g), key0 (fun a => f (g * a)) (hf.comp (measurable_const_mul g)),
      key0 f hf]
    conv_rhs => rw [← hinv g, lintegral_map hF (continuous_const_smul g).measurable]
    refine lintegral_congr_ae (hae.mono fun y hy => ?_)
    have h2 : ∃ k : G, k • x₀ = g • y := by
      obtain ⟨k, rfl⟩ := hy
      exact ⟨g * k, mul_smul _ _ _⟩
    have := inner_eq x₀ μ' f (g * s₀ y) (s₀ (g • y)) (by rw [mul_smul, hs₀ y hy, hs₀ _ h2])
    simpa [mul_assoc] using this
  have hfin : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.measurableSet
    have hL : IsCompact ((fun g : G => g • x₀) '' K) := hK.image hcont
    have hM : IsCompact ((Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K)) :=
      hemb.isCompact_preimage (hK.inv.mul hK)
    rw [← lintegral_indicator_one hKm, key0 _ (measurable_one.indicator hKm)]
    calc _ ≤ ∫⁻ y, ((fun g : G => g • x₀) '' K).indicator
            (fun _ => μ' ((Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K))) y ∂ν := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          by_cases hyK : y ∈ (fun g : G => g • x₀) '' K
          · rw [Set.indicator_of_mem hyK]
            obtain ⟨k, hk, hky⟩ := hyK
            rw [inner_eq x₀ μ' _ (s₀ y) k (by rw [hs₀ y hy]; exact hky.symm),
              ← lintegral_indicator_one hM.measurableSet]
            refine lintegral_mono fun h => ?_
            by_cases hh : k * (h : G) ∈ K
            · have : h ∈ (Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K) :=
                ⟨k⁻¹, by simpa using hk, k * h, hh, by simp⟩
              simp [Set.indicator_of_mem hh, Set.indicator_of_mem this]
            · simp [Set.indicator_of_notMem hh]
          · rw [Set.indicator_of_notMem hyK]
            have : ∀ h : MulAction.stabilizer G x₀, s₀ y * (h : G) ∉ K := fun h hh =>
              hyK ⟨_, hh, by
                have h1 : (h : G) • x₀ = x₀ := h.2
                simp only [mul_smul, h1, hs₀ y hy]⟩
            simp [Set.indicator_of_notMem (this _)]
      _ < ⊤ := by
          rw [lintegral_indicator_const hL.measurableSet]
          exact ENNReal.mul_lt_top hM.measure_lt_top hL.measure_lt_top
  have hne : μ Set.univ ≠ 0 := by
    rw [← lintegral_one, key0 _ measurable_const]
    simp only [lintegral_const, one_mul]
    exact mul_ne_zero (isOpen_univ.measure_ne_zero μ' Set.univ_nonempty)
      (by simpa using hν0)
  obtain ⟨n, hn⟩ : ∃ n, μ (compactCovering G n) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← iUnion_compactCovering G]
    exact measure_iUnion_null hcon
  have hpos : μ.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering G n) hn
  refine ⟨μ, ⟨⟩, fun f hf s hs => ?_⟩
  rw [key0 f hf]
  exact lintegral_congr_ae (hae.mono fun y hy =>
    inner_eq x₀ μ' f _ _ (by rw [hs y hy, hs₀ y hy]))

end GlobalTheory.GaugeWeil
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RigSq

variable {X Y : Scheme.{0}}

theorem gm_sq_g (L : LB X) (f : Y ⟶ X) (y : Y) (j j' : L.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ 2 := by
  have hp : f y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j) ⊓
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j') :=
    ⟨Set.mem_iInter.2 fun _ => hj, Set.mem_iInter.2 fun _ => hj'⟩
  show gm f y _ (∏ _k : Fin 1, (res _ (pullU (𝟙 X) _ (L.g j j'))) ^ (2 : ℤ)) = _
  rw [Fintype.prod_unique, map_zpow]
  refine (congrArg (· ^ (2 : ℤ)) ((gm_res f y _ hp _).trans (gm_pull f (𝟙 X) y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _))).trans ?_
  rw [Category.comp_id]
  exact zpow_two _ |>.trans (pow_two _).symm

theorem gm_rig {S : Scheme.{0}} {G : Over S} [GrpObj G] (R : RigLB G) (f : Y ⟶ (𝟙_ (Over S)).left) (y : Y)
    (j j' : R.L.ι) (hj : eSec G (f y) ∈ R.L.U j) (hj' : eSec G (f y) ∈ R.L.U j') :
    gm f y _ (R.rig.s (fun _ => j)) = gm (f ≫ eSec G) y _ (R.L.g j j') * gm f y _ (R.rig.s (fun _ => j')) := by
  have hp : f y ∈ (R.L.pull (eSec G)).U (fun _ => j) ⊓ (R.L.pull (eSec G)).U (fun _ => j') :=
    ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  have e := congrArg (gm f y _) (R.rigGen (fun _ => j) (fun _ => j'))
  rw [gm_res f y _ hp, map_mul, gm_res f y _ hp] at e
  refine e.trans (congrArg (· * _) ?_)
  show gm f y _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (R.L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f (eSec G) y (R.L.U j ⊓ R.L.U j') ⟨hj, hj'⟩ _)

theorem eSec_comp_toUnit {S : Scheme.{0}} (G : Over S) [GrpObj G] : eSec G ≫ (toUnit G).left = 𝟙 _ := by
  rw [eSec, ← Over.comp_left, show η[G] ≫ toUnit G = 𝟙 _ from toUnit_unique _ _]
  rfl

end GlobalTheory.RigSq

namespace GlobalTheory.RigSq

theorem exists_rescale : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L L' : RigLB G)
    (w : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen →
    ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)), w'.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (jL : L.L.ι) (jL' : L'.L.ι),
      eSec G (r z) ∈ L.L.U jL → eSec G (r z) ∈ L'.L.U jL' →
      gm r z _ (L.rig.s (fun _ => jL)) ^ 2 =
        gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (L'.rig.s (fun _ => jL')) ^ 2 := by
  intro S G _ L L' w hw
  have hπ := eSec_comp_toUnit G
  let W : L.L.ι × L'.L.ι → (𝟙_ (Over S)).left.Opens := fun p =>
    (L.L.pull (eSec G)).U (fun _ => p.1) ⊓ (L'.L.pull (eSec G)).U (fun _ => p.2)
  have hWle : ∀ p, W p ≤ eSec G ⁻¹ᵁ (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => p.1, fun _ => p.2) :=
    fun p x hx => ⟨Set.mem_iInter.2 fun _ => mem_pull.1 hx.1, Set.mem_iInter.2 fun _ => mem_pull.1 hx.2⟩
  let q : ∀ p, Γ((𝟙_ (Over S)).left, W p)ˣ := fun p =>
    res inf_le_left (L.rig.s (fun _ => p.1)) ^ 2 * (res inf_le_right (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ *
      (res (hWle p) (pullU (eSec G) _ (w.s (fun _ => p.1, fun _ => p.2))))⁻¹
  have hq : ∀ {Y : Scheme.{0}} (f : Y ⟶ (𝟙_ (Over S)).left) (y : Y) (p : L.L.ι × L'.L.ι), f y ∈ W p →
      gm f y (W p) (q p) = gm f y _ (L.rig.s (fun _ => p.1)) ^ 2 * (gm f y _ (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ *
        (gv w (f ≫ eSec G) y (fun _ => p.1) (fun _ => p.2))⁻¹ := by
    intro Y f y p hy
    simp only [q, map_mul, map_pow, map_inv]
    rw [gm_res f y _ hy, gm_res f y _ hy, gm_res f y _ hy, gm_pull f (eSec G) y _ (hWle p hy)]
    rfl
  obtain ⟨u, hu⟩ := glue_unit (X := (𝟙_ (Over S)).left) ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart L.isLB (eSec G x)
      obtain ⟨i', hi'⟩ := exists_chart L'.isLB (eSec G x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, i'), mem_pull.2 hi, mem_pull.2 hi'⟩) q (fun p p' x hx => by
      rw [hq _ x p hx.1, hq _ x p' hx.2]
      have h1 : eSec G x ∈ L.L.U p.1 := mem_pull.1 hx.1.1
      have h2 : eSec G x ∈ L'.L.U p.2 := mem_pull.1 hx.1.2
      have h1' : eSec G x ∈ L.L.U p'.1 := mem_pull.1 hx.2.1
      have h2' : eSec G x ∈ L'.L.U p'.2 := mem_pull.1 hx.2.2
      rw [gm_rig L (𝟙 _) x p.1 p'.1 h1 h1', gm_rig L' (𝟙 _) x p.2 p'.2 h2 h2',
        gm_isGen hw (𝟙 _ ≫ eSec G) x (fun _ => p.1) (fun _ => p'.1) (fun _ => p.2) (fun _ => p'.2)
          (Set.mem_iInter.2 fun _ => h1) (Set.mem_iInter.2 fun _ => h1')
          (Set.mem_iInter.2 fun _ => h2) (Set.mem_iInter.2 fun _ => h2'),
        gm_sq_g L.L (𝟙 _ ≫ eSec G) x p.1 p'.1 h1 h1', gm_sq_g L'.L (𝟙 _ ≫ eSec G) x p.2 p'.2 h2 h2']
      generalize gm (𝟙 _ ≫ eSec G) x _ (L.L.g p.1 p'.1) = A
      generalize gm (𝟙 _ ≫ eSec G) x _ (L'.L.g p.2 p'.2) = B
      generalize gm (𝟙 _) x _ (L.rig.s (fun _ => p'.1)) = C
      generalize gm (𝟙 _) x _ (L'.rig.s (fun _ => p'.2)) = D
      generalize gv w (𝟙 _ ≫ eSec G) x (fun _ => p'.1) (fun _ => p'.2) = E
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      abel)
  have hT : ∀ p, (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U p ≤ (toUnit G).left ⁻¹ᵁ ⊤ :=
    fun _ _ _ => trivial
  obtain ⟨w', hw'⟩ : ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)),
      ∀ p, w'.s p = w.s p * res (hT p) (pullU (toUnit G).left ⊤ u) :=
    ⟨⟨fun p => w.s p * res (hT p) (pullU (toUnit G).left ⊤ u)⟩, fun _ => rfl⟩
  refine ⟨w', ?_, ?_⟩
  · intro p p'
    rw [hw', hw']
    apply unit_ext
    intro x hx
    have e := congrArg (gm (𝟙 G.left) x _) (hw p p')
    rw [gm_res (𝟙 G.left) x _ hx, map_mul, gm_res (𝟙 G.left) x _ hx] at e
    simp only [map_mul, gm_res (𝟙 G.left) x _ hx, gm_res (𝟙 G.left) x _ hx.1, gm_res (𝟙 G.left) x _ hx.2]
    rw [e, _root_.mul_assoc]
  · intro Z r z jL jL' h1 h2
    have hy : r z ∈ W (jL, jL') := ⟨mem_pull.2 h1, mem_pull.2 h2⟩
    have hm : (r ≫ eSec G) z ∈ (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => jL, fun _ => jL') :=
      hWle (jL, jL') hy
    have hv : gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') =
        gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z ⊤ u := by
      show gm (r ≫ eSec G) z _ (w'.s (fun _ => jL, fun _ => jL')) = _
      erw [hw' (fun _ => jL, fun _ => jL')]
      rw [map_mul, gm_res _ z _ hm, gm_pull (r ≫ eSec G) (toUnit G).left z ⊤ trivial, Category.assoc, hπ,
        Category.comp_id]
      rfl
    rw [hv, ← gm_res r z (le_top : W (jL, jL') ≤ ⊤) hy u, hu (jL, jL'), hq r z (jL, jL') hy]
    generalize gm r z _ (L.rig.s (fun _ => jL)) = A
    generalize gm r z _ (L'.rig.s (fun _ => jL')) = B
    generalize gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') = E
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

end GlobalTheory.RigSq
end
end
