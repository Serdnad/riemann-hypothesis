module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle009
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle030
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle035
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle027

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial

noncomputable section

namespace GrassmannianFibreDegree

variable (n p : ℕ) [Fact p.Prime]

theorem span_eq_ker :
    (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) =
      RingHom.ker (Bridge.GeoNum.red (ι := plBlocks 1 1 n) p) :=
  (Bridge.GeoNum.ker_red p).symm

theorem isPrime : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).IsPrime := by
  rw [span_eq_ker]
  exact RingHom.ker_isPrime _

theorem isRelevant : IsRelevant (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) := by
  intro k
  refine ⟨plAnchor 1 n, ?_⟩
  rw [span_eq_ker, RingHom.mem_ker, Bridge.GeoNum.red, map_X]
  exact X_ne_zero _

theorem divSupp_eq :
    divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) = {Ideal.span {C (p : ℤ)}} := by
  have := isPrime n p
  ext W
  simp only [divSupp, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, isRelevant n p⟩

theorem ringKrullDim_quot :
    ringKrullDim (MRing (plBlocks 1 1 n) ⧸ (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))) =
      ((n + Fintype.card (Fin 1) : ℕ) : WithBot ℕ∞) := by
  rw [span_eq_ker, ringKrullDim_eq_of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective (Bridge.GeoNum.red_surjective p)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  have hc : Nat.card ((_ : Fin 1) × PlIdx 1 n) = n + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
    omega
  rw [ENat.card_eq_coe_natCard, hc, Fintype.card_fin]
  simp

def coordEquiv : (Σ _ : Unit, Fin (n + 1)) ≃ (Σ _ : Fin 1, PlIdx 1 n) :=
  Equiv.ofBijective (GrassmannianLinesProjective.coordMap n)
    ⟨(GrassmannianLinesProjective.isBlockMap n).2.1, GrassmannianLinesProjective.coordMap_surjective n⟩

theorem intNum_bot :
    NumbersDVR.intNum (ZMod p) (⊥ : Ideal (NumbersDVR.MRing (plBlocks 1 1 n) (ZMod p)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have h := FieldNumbers.Relabel.intNum_map_rename (F := ZMod p) (Equiv.ofUnique Unit (Fin 1))
    (coordEquiv n) (fun _ => Subsingleton.elim _ _)
    (⊥ : Ideal (NumbersDVR.MRing (FieldNumbers.ProjIdx n) (ZMod p)))
    (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ))
  rw [Ideal.map_bot] at h
  rw [h]
  exact FieldNumbers.intNum_projectiveSpace (ZMod p) n

theorem geoNum_span :
    geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have := isPrime n p
  have hV : IsMultiProjPrime (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) :=
    ⟨isPrime n p, ⟨{C (p : ℤ)}, fun f hf => ⟨0, by
      rw [Set.mem_singleton_iff.mp hf]
      exact Inter.Conservation.isMultiHomog_C _⟩, rfl⟩, isRelevant n p⟩
  rw [← Bridge.intNum_map_eq_geoNum p n _ hV (Ideal.mem_span_singleton_self _) (ringKrullDim_quot n p)]
  have hb : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).map
      (MvPolynomial.map (Int.castRingHom (ZMod p))) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (span_eq_ker n p).le
  rw [hb]
  exact intNum_bot n p

end GrassmannianFibreDegree


open GrassmannianFibreDegree in
theorem GrassFibreDegree.proof : GrassFibreDegree.Statement := by
  intro n p hp
  have : Fact p.Prime := ⟨hp⟩
  have := isPrime n p
  have hW : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) ∈
      divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) := by
    rw [divSupp_eq]
    rfl
  have hg : geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun j => ((fun _ : Fin n => fsMulti (plBlocks 1 1 n)) j).a) = 1 :=
    geoNum_span n p
  rw [GrassmannianLinesProjective.grassIdeal_eq_bot]
  unfold vertR
  rw [divSupp_eq, finsum_mem_singleton, if_neg (Inter.Conservation.not_horizontal hp hW),
    Inter.Conservation.charOf_eq hp hW, bot_sup_eq, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self, hg]
  simp

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace SectionQuotientLocal

variable {T : Type} {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

theorem coord_mem_sectionMod (t : T) : y ⟨(), t⟩ ∈ sectionMod y := by
  show ∀ c : Unit → T, (∀ k, y ⟨k, c k⟩ ≠ 0) → _ ∈ chartRingZ y c
  intro c _
  have hg : y ⟨(), t⟩ / y ⟨(), c ()⟩ ∈ chartRingZ y c := by
    unfold chartRingZ
    exact Algebra.subset_adjoin ⟨⟨(), t⟩, rfl⟩
  simpa [div_eq_mul_inv] using hg

theorem exists_mul_mem_of_mem_chartRingZ (m : Ideal (curveRing y)) (hm : m.IsPrime) (t : T)
    (h : ∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a)
    {z : K'} (hz : z ∈ chartRingZ y (fun _ => t)) :
    ∃ a b : curveRing y, b ∉ m ∧ (b : K') * z = a := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    exact h u
  | algebraMap r =>
    refine ⟨(r : curveRing y), 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, ?_⟩
    simp
  | add x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨b₂ * a₁ + b₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring
  | mul x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨a₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring

end SectionQuotientLocal


open SectionQuotientLocal in
theorem SectionQuotLocal.proof : SectionQuotLocal.Statement := by
  intro T _ K' _ _ y s _hy hs hsP m t hm hrat a b hb hba
  set x := aeval y s with hx_def
  have hx0 : x ≠ 0 := SectionQuotientFinite.aeval_ne_zero y hs hsP
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hba
    rcases mul_eq_zero.mp hba with h | h
    · have hb0 : b = 0 := by exact_mod_cast h
      exact hb (hb0 ▸ m.zero_mem)
    · exact hx0 h

  let e : sectionMod y := ⟨y ⟨(), t⟩, coord_mem_sectionMod y t⟩
  let φ : curveRing y →ₗ[curveRing y] sectionQuot y x :=
    LinearMap.toSpanSingleton (curveRing y) _ (Submodule.Quotient.mk e)
  have hφ : ∀ β : curveRing y, φ β = Submodule.Quotient.mk (β • e) := fun β => by
    simp [φ, Submodule.Quotient.mk_smul]
  have hφ0 : ∀ β : curveRing y, φ β = 0 ↔ ∃ γ : curveRing y, (γ : K') * x = β * y ⟨(), t⟩ := by
    intro β
    rw [hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_span_singleton]
    rfl
  have hle : Ideal.span {a} ≤ LinearMap.ker φ := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, hφ0]
    exact ⟨b, hba⟩
  let ψ : (curveRing y ⧸ Ideal.span {a}) →ₗ[curveRing y] sectionQuot y x := (Ideal.span {a}).liftQ φ hle

  have hker : ∀ q, ψ q = 0 → b • q = 0 := by
    intro q hq
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨γ, hγ⟩ := (hφ0 β).mp hq
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      Ideal.mem_span_singleton']
    refine ⟨γ, Subtype.ext ?_⟩
    push_cast
    apply mul_right_cancel₀ hyt
    rw [mul_assoc, ← hba, mul_assoc, ← hγ]
    ring

  have hsurj0 : ∀ n : sectionMod y, ∃ r : curveRing y, r ∉ m ∧ ∃ β : curveRing y, r • n = β • e := by
    intro n
    have hn : (n : K') ∈ chartLat y (fun _ => 1) 1 := n.2
    have hnt : (n : K') * (y ⟨(), t⟩)⁻¹ ∈ chartRingZ y (fun _ => t) := by
      simpa using hn (fun _ => t) (fun _ => hyt)
    obtain ⟨β, r, hr, hβ⟩ := exists_mul_mem_of_mem_chartRingZ y m hm t hrat hnt
    refine ⟨r, hr, β, Subtype.ext ?_⟩
    show (r : K') * n = β * y ⟨(), t⟩
    rw [← hβ]
    field_simp

  let S := m.primeCompl
  let Φ := IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (curveRing y ⧸ Ideal.span {a}))
    (LocalizedModule.mkLinearMap S (sectionQuot y x)) ψ
  have hΦ : ∀ q (r : S), Φ (LocalizedModule.mk q r) = LocalizedModule.mk (ψ q) r :=
    fun q r => IsLocalizedModule.map_LocalizedModules S _ q r
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z
    refine LocalizedModule.induction_on (β := fun z => Φ z = 0 → z = 0) (fun q r hz => ?_) z
    rw [hΦ, ← LocalizedModule.zero_mk r, LocalizedModule.mk_eq] at hz
    obtain ⟨u, hu⟩ := hz
    simp only [smul_zero, Submonoid.smul_def] at hu
    rw [← map_smul, ← map_smul] at hu
    have hq := hker _ hu
    rw [← LocalizedModule.zero_mk r, LocalizedModule.mk_eq]
    refine ⟨⟨b * u, S.mul_mem hb u.2⟩, ?_⟩
    simp only [smul_zero, Submonoid.smul_def, mul_smul]
    exact hq
  have hsurj : Function.Surjective Φ := by
    intro z
    refine LocalizedModule.induction_on (β := fun z => ∃ w, Φ w = z) (fun n r => ?_) z
    obtain ⟨n', rfl⟩ := Submodule.Quotient.mk_surjective _ n
    obtain ⟨r', hr', β, hβ⟩ := hsurj0 n'
    refine ⟨LocalizedModule.mk (Submodule.Quotient.mk β) (⟨r', hr'⟩ * r), ?_⟩
    rw [hΦ]
    have hψ : ψ (Submodule.Quotient.mk β) = Submodule.Quotient.mk (β • e) := by
      rw [← hφ]
      rfl
    rw [hψ, ← hβ, Submodule.Quotient.mk_smul]
    exact LocalizedModule.mk_cancel_common_left ⟨r', hr'⟩ r _
  have := hm
  let E := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization S
    (Localization.AtPrime m)
  unfold locLen
  rw [dite_eq_left hm, dite_eq_left hm, E.length_eq]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedGraphFibre

variable {K' : Type} [Fintype K'] {ι : K' → Type} [∀ k, Fintype (ι k)]


open Classical in
def vertWeight {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then 0 else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)

theorem vertR_eq_finsum (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) :
    vertR P L s = ∑ᶠ W, (divCycle P s W : ℝ) * vertWeight L W := by
  classical
  rw [vertR, finsum_mem_def]
  refine finsum_congr fun W => ?_
  simp only [Set.indicator, divCycle, Finsupp.ofSupportFinite_coe, vertWeight]
  by_cases hW : W ∈ divSupp P s
  · rw [if_pos hW, if_pos hW]
  · rw [if_neg hW, if_neg hW, Nat.cast_zero, zero_mul]

theorem finite_support (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) :
    (Function.support fun W => (divCycle P s W : ℝ) * vertWeight L W).Finite :=
  (divCycle P s).support.finite_toSet.subset fun W hW =>
    Finsupp.mem_support_iff.mpr fun h0 => hW (by simp [h0])

theorem vertR_sub (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s₁ s₂ : MRing ι)
    (E : Ideal (MRing ι)) (hhor : ¬ IsHorizontal E)
    (hE : (divCycle P s₂ E : ℤ) = divCycle P s₁ E + 1)
    (hW : ∀ W, ¬ IsHorizontal W → W ≠ E → divCycle P s₂ W = divCycle P s₁ W) :
    vertR P L s₁ - vertR P L s₂ = -((geoNum n E (fun j => (L j).a) : ℝ) * Real.log (charOf E)) := by
  classical
  rw [vertR_eq_finsum, vertR_eq_finsum, ← finsum_sub_distrib (finite_support P L s₁) (finite_support P L s₂)]
  have hpt : ∀ W, (divCycle P s₁ W : ℝ) * vertWeight L W - (divCycle P s₂ W : ℝ) * vertWeight L W =
      if W = E then -vertWeight L E else 0 := by
    intro W
    by_cases hWh : IsHorizontal W
    · have hne : W ≠ E := fun h => hhor (h ▸ hWh)
      simp [vertWeight, hWh, hne]
    · by_cases hWE : W = E
      · subst hWE
        have hR : (divCycle P s₂ W : ℝ) = divCycle P s₁ W + 1 := by exact_mod_cast hE
        rw [if_pos rfl, hR]
        ring
      · rw [if_neg hWE, hW W hWh hWE, sub_self]
  rw [finsum_congr hpt, finsum_eq_single _ E (fun W hW => if_neg hW), if_pos rfl]
  simp [vertWeight, hhor]

end StackedGraphFibre


open StackedGraphFibre in
theorem DualStackedGraphFibre.proof (hCyc : DualStackedExcCycle.Statement)
    (hSec : DualStackedExcGeoSecond.Statement) (hFir : DualStackedExcGeoFirst.Statement) :
    DualStackedGraphFibre.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab t L hL
  obtain ⟨E, hE, hhor, hEt⟩ := hCyc K i F F' T b b' a hi hlt hcov hab
  have key := vertR_sub (stackedGraph b' a) L (graphSecond t) (C (a t) * graphFirst t) E hhor (hEt t).1
    (hEt t).2
  have ha : ∀ s, a s ≠ 0 := fun s hs =>
    b.ne_zero s (Subtype.ext (by rw [hab s, hs, zero_smul]; rfl))
  refine ⟨fun hall => ?_, fun ⟨j, hj⟩ => ?_⟩
  · have hd : (fun j => (L j).a) = fun _ => degSecond := funext hall
    rw [key, hd, hSec K i F F' T b b' a hi hlt hcov hab E hE, ← DualLatticeIndex.proof K i F F' hlt.le,
      DualStackedDegreeAlt.relIndex_stacked hlt.le b b' a hab,
      Real.log_prod (fun s _ => abs_ne_zero.mpr (Int.cast_ne_zero.mpr (ha s)))]
  · rw [key, hFir K i F F' T b b' a hi hlt hcov hab E hE (fun j => (L j).a) hL ⟨j, hj⟩]
    simp

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

def IsExcCoords {K : Type} [Field K] [NumberField K] {i : ℕ} (F F' : HermLattice K i) {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) {k : Type} [Field k]
    (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) {m : ℕ} (g : Fin m → Fin i → K) (α : T → k)
    (M : T → Fin (m + 1) → k) : Prop :=
  Function.Surjective ρ ∧ ρ π = 0 ∧ y₀ ∈ F.lattice ∧ (∀ j, g j ∈ F'.lattice) ∧
    (∀ t, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b' t : Fin i → K) ⬝ᵥ (algebraMap (𝓞 K) K π • y₀) ∧
      ρ c = α t) ∧
    (∀ t, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b t : Fin i → K) ⬝ᵥ y₀ ∧ ρ c = M t 0) ∧
    (∀ t j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b t : Fin i → K) ⬝ᵥ g j ∧ ρ c = M t j.succ) ∧
    (∃ t, α t ≠ 0) ∧ (∃ t, M t 0 ≠ 0) ∧
    (∀ c : 𝓞 K, ρ c = 0 → ∀ φ ∈ dualLattice F', algebraMap (𝓞 K) K c • φ ∈ dualLattice F) ∧
    (∀ φ ∈ dualLattice F', ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ (algebraMap (𝓞 K) K π • y₀) →
      ρ c = 0 → φ ∈ dualLattice F) ∧
    (∀ φ ∈ dualLattice F, (∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ y₀ → ρ c = 0) →
      (∀ j, ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ g j → ρ c = 0) →
      φ ∈ Submodule.span ℤ {ψ | ∃ c : 𝓞 K, ρ c = 0 ∧ ∃ χ ∈ dualLattice F, ψ = algebraMap (𝓞 K) K c • χ})

def DualStackedExcCoords.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ (k : Type) (_ : Field k) (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M

def DualStackedExcBase.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      stackedBase b' a ≤ linPrime α M

def DualStackedExcChart.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      ∀ v u : T, ∃ N : ℕ, ∀ e ∈ linPrime α M,
        (graphFirst v * graphSecond u) ^ N * e ∈ stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u}

namespace DualStackedExcChartExample

open DualTopSimpleSubExample

end DualStackedExcChartExample

end

end GroundTheory.Heights₂.Heights
end
