module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle471
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle105
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle015
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.SmallFInF

section Helpers
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_valLe (c : kˣ) : IsOpen {t : k | valuation k t ≤ valuation k (c : k)} := by
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  have e : {t : k | valuation k t ≤ valuation k (c : k)} = (fun t => t / (c : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff, map_div₀,
      div_le_one₀ h0]
  rw [e]
  exact IsOpen.preimage (continuous_id.div_const _) Valuation.isOpen_integer

theorem isOpen_cosetM {n m : Type} [Fintype n] [Fintype m] (c : kˣ) (x : Matrix n m k) :
    IsOpen {y : Matrix n m k | ∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isOpen_valLe c).preimage (f := fun y : Matrix n m k => y i j - x i j) (by fun_prop)

theorem isCompact_ballM {n : Type} [Fintype n] (R : kˣ) :
    IsCompact {y : Matrix n n k | ∀ i j, valuation k (y i j) ≤ valuation k (R : k)} := by
  have h0 : 0 < valuation k (R : k) := zero_lt_iff.2 (by simp)
  have e : {y : Matrix n n k | ∀ i j, valuation k (y i j) ≤ valuation k (R : k)} =
      (fun z : Matrix n n k => (R : k) • z) '' {A | ∀ i j, A i j ∈ 𝒪[k]} := by
    ext y
    constructor
    · intro hy
      refine ⟨(R : k)⁻¹ • y, fun i j => ?_, ?_⟩
      · rw [Valuation.mem_integer_iff]
        simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
        rw [inv_mul_le_iff₀ h0, mul_one]; exact hy i j
      · simp [smul_smul]
    · rintro ⟨z, hz, rfl⟩ i j
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hz i j))
  rw [e]
  exact isCompact_intMatrix.image (continuous_const_smul _)

end Helpers

theorem smallF_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → 1 ≤ e → CondLE ϖ e ν → ¬ IsUnram ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u (1 / 2) ∈ F) → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → (∀ X, Ψ X ∈ F) → ∀ h : GL D k, smallF (haarVol J) ν Ψ (Y0 k σ * h.val) ∈ F := by
  intro k _ _ _ _ _ _ A A' D _ _ _ _ _ _ F J hJo hJK σ ν ϖ e hϖ he hcond hram hνF hapF c Ψ hΨ hΨF h
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨R, N, hbd, hper⟩ := GlobalTheory.T.exists_valuation_bound_and_periodic_frameBlock σ hϖ c hΨ h
  set Y := Y0 k σ * h.val with hY
  set cN : kˣ := ϖ ^ N with hcN
  set z : ℂ := (Fintype.card D : ℂ) / 2 with hz
  have hzF : ∀ u : kˣ, apow u z ∈ F := fun u => by
    have : apow u z = (apow u (1 / 2)) ^ (Fintype.card D) := by
      simp only [apow, hz]
      rw [← Complex.cpow_nat_mul]; congr 1; ring
    rw [this]; exact pow_mem (hapF u) _
  let Cs : Matrix A' A' k → Set (GL A' k) :=
    fun x => {g | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (cN : k)}
  have hCs_meas : ∀ x, MeasurableSet (Cs x) := fun x =>
    ((isOpen_cosetM cN x).preimage Units.continuous_val).measurableSet
  have hCs_eq : ∀ x y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (cN : k)) →
      Cs x = Cs y := by
    intro x y hxy
    ext g
    simp only [Cs, Set.mem_setOf_eq]
    constructor
    · intro hg i j
      have := Valuation.map_add_le (valuation k) (hg i j) ((Valuation.map_sub_swap _ _ _).le.trans (hxy i j))
      simpa using this
    · intro hg i j
      have := Valuation.map_add_le (valuation k) (hg i j) (hxy i j)
      simpa using this
  have hcoset : ∀ x, ∫ g in Cs x, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
    intro x
    by_cases hs : ∃ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (cN : k)) ∧ y.det = 0
    · obtain ⟨y, hy, hy0⟩ := hs
      rw [hCs_eq x y hy]
      rw [GlobalTheory.CosetVanish.integral_coset_singular_eq_zero (haarVol J) ν z hram cN y hy0]
      exact F.zero_mem
    · push_neg at hs
      exact GlobalTheory.T.integral_detChar_invertibleMatrixBall_mem_subfield F hJo hJK ν z hϖ hcond hνF hzF cN x hs

  let L : AddSubgroup (Matrix A' A' k) :=
    { carrier := {Z | ∀ i j, valuation k (Z i j) ≤ valuation k (cN : k)}
      add_mem' := fun ha hb i j => Valuation.map_add_le _ (ha i j) (hb i j)
      zero_mem' := fun i j => by simp
      neg_mem' := fun ha i j => by simpa using ha i j }
  let q : Matrix A' A' k → Matrix A' A' k ⧸ L := QuotientAddGroup.mk
  have hq : ∀ x y : Matrix A' A' k, q x = q y ↔ ∀ i j, valuation k (x i j - y i j) ≤ valuation k (cN : k) := by
    intro x y
    rw [QuotientAddGroup.eq]
    refine forall₂_congr fun i j => ?_
    show valuation k ((-x + y) i j) ≤ _ ↔ _
    rw [show (-x + y) i j = -(x i j - y i j) by simp; ring, Valuation.map_neg]

  obtain ⟨T0, hT0⟩ := (isCompact_ballM (n := A') R).elim_finite_subcover
    (fun y : Matrix A' A' k => {x : Matrix A' A' k | ∀ i j, valuation k (x i j - y i j) ≤ valuation k (cN : k)})
    (fun y => isOpen_cosetM cN y)
    (fun x _ => Set.mem_iUnion.2 ⟨x, fun i j => by simp⟩)
  classical
  let T : Finset (Matrix A' A' k ⧸ L) := T0.image q
  set f : GL A' k → ℂ := fun g => Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) z with hf
  have hdec : f = fun g => ∑ t ∈ T, ({g : GL A' k | q g.val = t}).indicator f g := by
    funext g
    by_cases h0 : f g = 0
    · rw [h0]; symm
      refine Finset.sum_eq_zero fun t _ => ?_
      simp [Set.indicator_apply, h0]
    · have hΨ0 : Ψ (g.val * Y) ≠ 0 := fun h1 => h0 (by simp [hf, h1])
      have hB := hbd g.val hΨ0
      obtain ⟨y, hyT, hy⟩ := Set.mem_iUnion₂.1 (hT0 hB)
      have hqt : q g.val ∈ T := Finset.mem_image.2 ⟨y, hyT, ((hq _ _).2 hy).symm⟩
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [Finset.sum_ite_eq]
      simp [hqt]
  show ∫ g, Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D : ℂ) / 2) ∂(haarVol J) ∈ F
  change ∫ g, f g ∂(haarVol J) ∈ F
  by_cases hint : Integrable f (haarVol J)
  · have hmeas : ∀ t, MeasurableSet {g : GL A' k | q g.val = t} := by
      intro t
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
      have : {g : GL A' k | q g.val = q y} = Cs y := by
        ext g; simp only [Set.mem_setOf_eq, Cs]; exact hq _ _
      rw [this]; exact hCs_meas y
    rw [hdec, integral_finsetSum _ (fun t _ => hint.indicator (hmeas t))]
    refine sum_mem fun t _ => ?_
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
    have hset : {g : GL A' k | q g.val = q y} = Cs y := by
      ext g; simp only [Set.mem_setOf_eq, Cs]; exact hq _ _
    rw [integral_indicator (hmeas _), hset]
    have hc : ∫ g in Cs y, f g ∂(haarVol J) =
        ∫ g in Cs y, Ψ (y * Y) * ((ν (gdet g) : ℂ) * apow (gdet g) z) ∂(haarVol J) := by
      refine setIntegral_congr_fun (hCs_meas y) fun g hg => ?_
      have h1 : g.val = y + (g.val - y) := by abel
      have h2 : Ψ (g.val * Y) = Ψ (y * Y) := by
        rw [h1, hper y (g.val - y) (fun i j => hg i j)]
      simp only [hf, h2, mul_assoc]
    rw [hc, integral_const_mul]
    exact F.mul_mem (hΨF _) (hcoset y)
  · rw [integral_undef hint]; exact F.zero_mem

end GlobalTheory.SmallFInF
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section

namespace GlobalTheory.HeckeEx

theorem frame_pull_eq_transition_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (yx zx : Sp ℂ ⟶ Xo.X) (p : ℕ)
  (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ)
  (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk zx ⟶ Xo.univ.t.G))
  (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
  Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  IsHolTo Set.univ (fun w => (e w).left) → IsHolTo Set.univ (fun w => (e' w).left) →
  (∀ w w', e (w + w') = e w * e w') → (∀ a ∈ Λ, e a = 1) → (∀ w, e' (h w) = ψp (e w)) →
  (∀ a ∈ Λ, h a ∈ Λ') →
  (∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) →
  (∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
    ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
      valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) →
  (∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
    ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
      b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
  (∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
    {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    Hm.IsHermitian →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (e z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ, ∀ j z, ‖χl a‖ = 1 ∧ (⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a))) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j j' z, ⊤ ≤ (e' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (e' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (e' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ', ∀ j z, ‖χl' a‖ = 1 ∧ (⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' a * Complex.exp (Real.pi * hermForm Hm' z a + Real.pi / 2 * hermForm Hm' a a) * fr' j (z + a))) →
  ∀ w i j, ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr' i (h w) = b i j (e w) * fr j ((p : ℂ) • w) := by
  intro E _ _ _ H Dw l Xo yx zx p ψp b g Λ Λ' e e' h hΛ hhe hhe' hadd hker hψ hΛΛ' hbn hbc hb0 hbd
    Hm χl fr hH hd hn hc h0 ha Hm' χl' fr' hHH hd' hc' h0' ha' w i j hi hj
  have e0 : e 0 = 1 := hker 0 (zero_mem Λ)
  have hpow : ∀ (n : ℕ) z, e ((n : ℂ) • z) = e z ^ n := by
    intro n z
    induction n with
    | zero => rw [Nat.cast_zero, zero_smul, e0, pow_zero]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have e'0 : e' 0 = 1 := by rw [← map_zero h, hψ, e0, map_one]
  have hpa : ∀ a ∈ Λ, (p : ℂ) • a ∈ Λ := fun a haa => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem haa p
  have per : ∀ a ∈ Λ, ∀ z, e (z + a) = e z := fun a haa z => by rw [hadd, hker a haa]; exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hsm : ∀ z a, hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a) = (p : ℂ) ^ 2 * hermForm Hm z a := fun z a => by
    rw [GlobalTheory.UnitFrameGen.hermForm_smul_left, GlobalTheory.UnitFrameGen.hermForm_smul_right, star_natCast]; ring
  have ho1 : ∀ V, IsOpen {z | ⊤ ≤ (e z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe V 0).1
  have ho1' : ∀ V, IsOpen {z | ⊤ ≤ (e' z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe' V 0).1
  have hch : Continuous h := h.toLinearMap.continuous_of_finiteDimensional
  have dh : Differentiable ℂ (fun z => h z) := (LinearMap.toContinuousLinearMap h.toLinearMap).differentiable
  have dsm : Differentiable ℂ (fun z : Fin g → ℂ => (p : ℂ) • z) := differentiable_id.const_smul (p : ℂ)
  have key := GlobalTheory.UnitFrameGen.frames_eq Λ hΛ
    (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι =>
      {w | ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.1 ∧ ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.2})
    (fun q => ((ho1' _).preimage hch).inter ((ho1 _).preimage (continuous_const_smul (p : ℂ))))
    (fun z => by
      obtain ⟨i', hi'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e' (h z)).left
      obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e ((p : ℂ) • z)).left
      exact ⟨(i', j'), hi', hj'⟩)
    (fun q a haa z hz => by
      refine ⟨?_, ?_⟩
      · rw [hψ, per a haa, ← hψ]; exact hz.1
      · rw [smul_add, per _ (hpa a haa)]; exact hz.2)
    (fun q z => b q.1 q.2 (e z) * fr q.2 ((p : ℂ) • z)) (fun q z => fr' q.1 (h z))
    (fun q q' z => valAt' (e' (h z)).left (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
      (Xo.univ.t.PP.L.g q.1 q'.1).val)
    (fun a z => Real.exp (Real.pi * (hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a)).re +
      Real.pi / 2 * (hermForm Hm ((p : ℂ) • a) ((p : ℂ) • a)).re))
    (fun q => ((hbd q.1 q.2).mono fun z hz => ⟨by rw [← hψ]; exact hz.1, by rw [← hpow]; exact hz.2⟩).mul
      ((hd q.2).comp dsm.differentiableOn fun z hz => hz.2))
    (fun q => (hd' q.1).comp dh.differentiableOn fun z hz => hz.1)
    (fun q z hz => mul_ne_zero (hbn q.1 q.2 (e z) (by rw [← hψ]; exact hz.1) (by rw [← hpow]; exact hz.2))
      (hn q.2 _ hz.2))
    (fun q q' z h1 h2 => by
      have e1 := hc q.2 q'.2 ((p : ℂ) • z) ((top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      have e2 := hbc q.1 q.2 q'.1 q'.2 (e z)
        (by rw [← hψ]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩)
        (by rw [← hpow]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      rw [hpow] at e1
      rw [hψ, e1]
      linear_combination e2 * fr q'.2 ((p : ℂ) • z))
    (fun q q' z h1 h2 => hc' q.1 q'.1 (h z) ((top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩))
    (fun q hz => by
      have z1 := hz.1
      have z2 := hz.2
      rw [map_zero] at z1
      rw [smul_zero] at z2
      rw [map_zero, smul_zero, h0' _ z1, h0 _ z2, e0]
      rw [e'0] at z1
      rw [e0] at z2
      exact hb0 q.1 q.2 z1 z2)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm _ _ _ _ _ (ha _ (hpa a haa) q.2 ((p : ℂ) • z)).1
        ((ha _ (hpa a haa) q.2 _).2 hz.2)
      rw [per a haa, smul_add, norm_mul, norm_mul, this]; ring)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm' _ _ _ _ _ (ha' _ (hΛΛ' a haa) q.1 (h z)).1
        ((ha' _ (hΛΛ' a haa) q.1 (h z)).2 hz.1)
      rw [hHH, hHH] at this
      rw [map_add (f := _), this, hsm, hsm])
  exact key (i, j) w ⟨hi, hj⟩

end GlobalTheory.HeckeEx
end
end

end

section

@[expose] public section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

theorem _root_.GlobalTheory.T.heckeIsogeny_appellHumbertFrame_pull_eq_transition_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (yx zx : Sp ℂ ⟶ Xo.X) (p : ℕ)
  (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ)
  (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk zx ⟶ Xo.univ.t.G))
  (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
  Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  IsHolTo Set.univ (fun w => (e w).left) → IsHolTo Set.univ (fun w => (e' w).left) →
  (∀ w w', e (w + w') = e w * e w') → (∀ a ∈ Λ, e a = 1) → (∀ w, e' (h w) = ψp (e w)) →
  (∀ a ∈ Λ, h a ∈ Λ') →
  (∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) →
  (∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
    ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
      valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) →
  (∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
    ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
      b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
  (∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
    {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    Hm.IsHermitian →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (e z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ, ∀ j z, ‖χl a‖ = 1 ∧ (⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a))) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j j' z, ⊤ ≤ (e' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (e' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (e' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ', ∀ j z, ‖χl' a‖ = 1 ∧ (⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' a * Complex.exp (Real.pi * hermForm Hm' z a + Real.pi / 2 * hermForm Hm' a a) * fr' j (z + a))) →
  ∀ w i j, ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr' i (h w) = b i j (e w) * fr j ((p : ℂ) • w) := by
  first | exact @GlobalTheory.HeckeEx.frame_pull_eq_transition_mul | exact GlobalTheory.HeckeEx.frame_pull_eq_transition_mul | (intros; apply GlobalTheory.HeckeEx.frame_pull_eq_transition_mul <;> assumption)

end
end
