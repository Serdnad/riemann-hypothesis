module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle142
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle145
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle146
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Localization.Finiteness
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010

@[expose] public section

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.SplitLift

section Lattice

variable {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_smul_mem (M : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • x ∈ M := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

theorem exists_split (Λ : Submodule R V) (hfg : Λ.FG) (hsp : Submodule.span K (Λ : Set V) = ⊤)
    (S I : Submodule K V) :
    ∃ W : Submodule K V, W ≤ S ∧ W ⊓ I = ⊥ ∧ S ≤ W ⊔ I ∧
      ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ W ∧ l - w ∈ I := by
  set M : Submodule R V := Λ ⊓ S.restrictScalars R with hM
  have hMfg : M.FG := by
    have : Module.Finite R Λ := Module.Finite.iff_fg.2 hfg
    exact (Module.Finite.iff_fg (N := M)).1
      (Module.Finite.of_injective (Submodule.inclusion (inf_le_left : M ≤ Λ))
        (Submodule.inclusion_injective _))
  have : Module.Finite R M := Module.Finite.iff_fg.2 hMfg
  let π : M →ₗ[R] (V ⧸ I) := (I.mkQ.restrictScalars R) ∘ₗ M.subtype
  have : Module.IsTorsionFree R (V ⧸ I) := Module.IsTorsionFree.trans K
  have : Module.Finite R (LinearMap.range π) := inferInstance
  have : Module.Flat R (LinearMap.range π) := inferInstance
  have : Module.FinitePresentation R (LinearMap.range π) :=
    Module.finitePresentation_of_finite R _
  have : Module.Projective R (LinearMap.range π) := Module.Flat.projective_of_finitePresentation
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π.rangeRestrict LinearMap.id
    π.surjective_rangeRestrict
  have hσ' : ∀ y, π (σ y) = (y : V ⧸ I) := fun y => by
    have := congrArg Subtype.val (LinearMap.congr_fun hσ y)
    simpa using this
  set N : Submodule R V := LinearMap.range (M.subtype ∘ₗ σ) with hN
  have key : ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ Submodule.span K (N : Set V) ∧ l - w ∈ I := by
    intro l hl hlS
    let y : LinearMap.range π := ⟨π ⟨l, hl, hlS⟩, _, rfl⟩
    refine ⟨(σ y : V), (σ y).2.1, Submodule.subset_span ⟨y, rfl⟩, ?_⟩
    rw [← Submodule.Quotient.eq]
    exact (hσ' y).symm
  have hinj : ∀ d : R, d ≠ 0 → algebraMap R K d ≠ 0 := fun d hd =>
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hd
  refine ⟨Submodule.span K (N : Set V), ?_, ?_, ?_, key⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    exact (σ y).2.2
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxI⟩
    obtain ⟨d, hd, y, hy⟩ := exists_smul_mem N hx
    have hy' : ((σ y : M) : V) = d • x := hy
    have h0 : (y : V ⧸ I) = 0 := by
      rw [← hσ' y]
      show I.mkQ ((σ y : M) : V) = 0
      rw [hy', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact I.smul_of_tower_mem d hxI
    have h1 : y = 0 := Subtype.ext h0
    rw [h1, map_zero, ← algebraMap_smul K d x] at hy'
    exact (smul_eq_zero.1 hy'.symm).resolve_left (hinj d hd)
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem (K := K) Λ (x := x) (by rw [hsp]; trivial)
    obtain ⟨w, -, hw, hwI⟩ := key _ hdx (S.smul_of_tower_mem d hx)
    have h1 : d • x ∈ Submodule.span K (N : Set V) ⊔ I :=
      Submodule.mem_sup.2 ⟨w, hw, _, hwI, by abel⟩
    rw [← algebraMap_smul K d x] at h1
    exact (Submodule.smul_mem_iff _ (hinj d hd)).1 h1

end Lattice

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

section Geometry
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem flip_zero {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem mem_wSp_iff (F F' : FlagD H r) (w : V) : w ∈ wSp F F' ↔ ∀ y ∈ V0 F F', H.B y w = 0 := by
  rw [wSp, mem_perp_iff]
  exact ⟨fun h y hy => flip_zero (h y hy), fun h y hy => flip_zero (h y hy)⟩

theorem hermFlagPair_isotropic_sup_le_commonSpace (F F' : FlagD H r) : F.X ⊔ F'.X ≤ V0 F F' := le_sup_left

theorem isotropicMeet_le_jointSpan (F F' : FlagD H r) : II F F' ≤ V0 F F' :=
  (inf_le_left.trans le_sup_left).trans (hermFlagPair_isotropic_sup_le_commonSpace F F')

theorem flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast b =>
    exact hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))

theorem X_perp (F : FlagD H r) {w x : V} (hw : ∀ a : Fin (r + 1), H.B (F.e a) w = 0) (hx : x ∈ F.X) :
    H.B x w = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    exact hw _
  exact this hx

theorem aniso_right {F F' : FlagD H r} {j : ℕ} {hj : j ≤ r} {c : K} (h : NFFull F F' j hj c)
    (hF : F.Aniso) : F'.Aniso := by
  obtain ⟨-, -, -, -, -, h6, -, -, h9⟩ := h
  intro w hw hww
  obtain ⟨x, hx, hwx⟩ := h9 w hw
  have h1 : H.B (w - x) (w - x) = 0 := by
    have a1 : H.B x (w - x) = 0 := hwx x (hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_right hx))
    have a2 : H.B w x = 0 := flip_zero (X_perp F' hw hx)
    rw [map_sub H.B, LinearMap.sub_apply, a1, map_sub, hww, a2]
    simp
  have h2 : w - x ∈ F.X := hF _ (fun a => hwx _ (flag_vector_mem_base_lattice F F' a)) h1
  have h3 : w - x ∈ F'.X := ((h6 _ h2).1 hwx).2
  simpa using add_mem h3 hx

end Geometry

theorem latTh_eq (F F' : FlagD H r) (hI : II F F' ≤ wSp F F') (Λ : Submodule (𝓞 K) V) :
    latTh F F' Λ = (Λ ⊓ rs (𝓞 K) (wSp F F')) ⊔ rs (𝓞 K) (II F F') := by
  have hu : ∀ y ∈ wSp F F', y ∈ uPerp F F' := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (hermFlagPair_isotropic_sup_le_commonSpace F F' hx)
  have hp : ∀ y ∈ wSp F F', y ∈ perp H (II F F') := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (isotropicMeet_le_jointSpan F F' hx)
  apply le_antisymm
  · rintro y ⟨⟨hy1, -⟩, hy3⟩
    obtain ⟨l, ⟨hl, -⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hy1
    refine Submodule.mem_sup.2 ⟨l, ⟨hl, ?_⟩, x, hx, rfl⟩
    have : l + x - x ∈ wSp F F' := sub_mem hy3 (hI hx)
    simpa using this
  · refine sup_le ?_ ?_
    · rintro l ⟨hl, hw⟩
      exact ⟨⟨Submodule.mem_sup_left ⟨hl, hp l hw⟩, hu l hw⟩, hw⟩
    · intro x hx
      exact ⟨⟨Submodule.mem_sup_right hx, hu x (hI hx)⟩, hI hx⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ s ∈ N.R, N.Split (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ _ hΛ
  obtain ⟨hfull, hlift, -, -, -, -, hw, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have hL := (isLatMod_top_bot_iff Λ).1 hΛ.1.1.1
  obtain ⟨W, hWS, hWI, hSW, hWΛ⟩ :=
    exists_split Λ hL.1 hΛ.1.1.1.2 (wSp N.F N.F') (II N.F N.F')
  have hW : IsLift N.F N.F' W :=
    ⟨fun w h => (mem_wSp_iff _ _ w).1 (hWS h), hWI, fun w h => hSW ((mem_wSp_iff _ _ w).2 h)⟩
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hA : N.F.Aniso := by
    intro w h1 h2
    by_contra hne
    have := N.posdef σ w h1 hne
    rw [h2] at this
    simp at this
  obtain ⟨f, hf, hf', hfix, hmap⟩ := Formalism.HermitianLatticeCounting.P.complementLiftTransitive K V H r N.F N.F' W N.Wt
    ⟨1, by rw [star_one]; norm_num⟩ hA (aniso_right hfull hA) hW hlift
  let s : V ≃ₗ[K] V := LinearEquiv.ofBijective f hf.2.1
  refine ⟨s, Subgroup.subset_closure ⟨hf, hf'⟩, ?_⟩
  have hI : II N.F N.F' ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_right
  have hWt : N.Wt ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_left
  rw [NF.Split, latTh_eq _ _ hI]
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro y ⟨hy, hyw⟩
    obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y s Λ).1 hy
    have hlw : l ∈ wSp N.F N.F' := by
      refine (mem_wSp_iff _ _ l).2 fun y hy => ?_
      rw [← hf.1, hfix y hy]
      exact (mem_wSp_iff _ _ _).1 hyw y hy
    obtain ⟨w, hw1, hw2, hw3⟩ := hWΛ l hl hlw
    refine Submodule.mem_sup.2 ⟨f w, ⟨Submodule.smul_mem_pointwise_smul w s Λ hw1, ?_⟩, l - w, hw3, ?_⟩
    · show f w ∈ N.Wt
      rw [← hmap]
      exact ⟨w, hw2, rfl⟩
    · show f w + (l - w) = f l
      rw [← hfix _ (isotropicMeet_le_jointSpan _ _ hw3), map_sub]
      abel
  · exact sup_le_sup_right (inf_le_inf_left _ fun x hx => hWt hx) _

end GlobalTheory.DegCnt.SplitLift
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.KType

theorem cdom_step {n : ℕ} {ε : Fin n → Bool} {ν μ : Fin n → ℝ} (h : CDom ε ν μ) {a b : Fin n}
    (hab : a < b) (he : ε a = ε b) : CDom ε (ν - Formalism.REAL.root a b) μ := by
  obtain ⟨c, hc, hs⟩ := h
  refine ⟨fun i j => c i j + (if j = b then if i = a then 1 else 0 else 0), ?_, ?_⟩
  · intro i j hij
    by_cases h0 : c i j = 0
    · by_cases hj : j = b
      · by_cases hi : i = a
        · subst hi; subst hj; exact ⟨hab, he⟩
        · simp [h0, hi] at hij
      · simp [h0, hj] at hij
    · exact hc i j h0
  · have : μ - (ν - Formalism.REAL.root a b) = (μ - ν) + Formalism.REAL.root a b := by abel
    rw [this, hs]
    simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem cdom_word {n : ℕ} {ε : Fin n → Bool} (μ : Fin n → ℝ) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) : CDom ε (μ + wordWeightShift w) μ := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, by simp, by simp [wordWeightShift]⟩
  | cons p w ih =>
    have hp := hw p List.mem_cons_self
    have := cdom_step (ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))) hp.2 hp.1.symm
    have e : μ + wordWeightShift (p :: w) = μ + wordWeightShift w - Formalism.REAL.root p.2 p.1 := by
      simp only [wordWeightShift, Formalism.REAL.root]; abel
    rw [e]; exact this

theorem not_cdom_add {n : ℕ} {ε : Fin n → Bool} (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ CDom ε (μ + Pi.single a 1 - Pi.single b 1) μ := by
  rintro ⟨c, hc, hs⟩
  have e : μ - (μ + Pi.single a 1 - Pi.single b 1) = Pi.single b (1 : ℝ) - Pi.single a 1 := by abel
  rw [e] at hs
  have h1 := congrArg heightFunctional hs
  rw [height_functional_root] at h1
  have hsum : heightFunctional (∑ i, ∑ j, (c i j : ℝ) • Formalism.REAL.root i j) ≤ 0 := by
    refine Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_
    · intro x y hx hy; rw [height_functional_add]; linarith
    · intro i _
      refine Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_
      · intro x y hx hy; rw [height_functional_add]; linarith
      · intro j _
        have h2 : heightFunctional ((c i j : ℝ) • Formalism.REAL.root i j) = (c i j : ℝ) * ((i : ℝ) - j) := by
          rw [← height_functional_root i j]
          simp only [heightFunctional, Formalism.REAL.root, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        rw [h2]
        by_cases h0 : c i j = 0
        · simp [h0]
        · have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (hc i j h0).1
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

theorem cdom_of_mem {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ V} (hR : KRel ε F) (hU : KUnit ε F) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε F μ x) (hy : y ∈ kSpan ε F x) (hy0 : y ≠ 0) (hw : IsWeight F ν y) :
    CDom ε ν μ := by
  by_contra hn
  rw [compact_span_eq_lowering hR hx] at hy
  have : lowSpan ε F x ≤ (ℂ ∙ y)ᗮ := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨w, hw', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    refine compact_weight_orthogonal V n ε F ν (μ + wordWeightShift w) y _ hU hw
      (word_action_weight hR hx.1 w (fun q hq => (hw' q hq).1)) ?_
    rintro rfl
    exact hn (cdom_word μ w hw')
  exact hy0 (inner_self_eq_zero.mp (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (this hy)))

theorem kType_iff : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsURepOn (UJset ε) σ → IsDer ε σ V E → (∀ (μ : Fin n → ℝ) (u : V), u ≠ 0 → KHighest ε E μ u → FiniteDimensional ℂ (kSpan ε E u) → IsKTypeOf ε σ μ ((kSpan ε E u).map V.subtype)) ∧ ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H) (u : V), IsKTypeOf ε σ μ S → S ≤ V → (u : H) ∈ S → u ≠ 0 → IsWtOn (Kset ε) σ μ (u : H) → KHighest ε E μ u ∧ (kSpan ε E u).map V.subtype = S ∧ FiniteDimensional ℂ (kSpan ε E u) := by
  intro n ε H _ _ _ σ V E hσ hD
  obtain ⟨-, hst, hwt⟩ := GlobalTheory.T.derivedModule_coefficients_and_stable_flows n ε H σ V E hσ hD
  have hR : KRel ε E := glRel_kRel ε E hD.1
  have hU : KUnit ε E := isUnitary_kUnit ε E hD.2.1
  have hIrr : KIrr := kIrr_of highestWeightExists_holds
    (kHiUniq_of compact_lowering_holds compact_weight_orthogonal (kOrth_of compact_lowering_holds compact_weight_orthogonal))
  have hmc : ∀ S : Submodule ℂ H, S ≤ V → (S.comap V.subtype).map V.subtype = S := by
    intro S hS
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hS]
  have hfd : ∀ S : Submodule ℂ H, S ≤ V → FiniteDimensional ℂ S →
      FiniteDimensional ℂ (S.comap V.subtype) := by
    intro S hS _
    exact (Submodule.comapSubtypeEquivOfLe hS).symm.finiteDimensional
  refine ⟨?_, ?_⟩
  · intro μ u hu0 hu hf
    have hfm : FiniteDimensional ℂ ((kSpan ε E u).map V.subtype) := inferInstance
    refine ⟨hfm, (hst _ hf).1 (compact_span_stable u), ?_, ?_, ?_⟩
    · intro S' hS' hK
      have hV : S' ≤ V := hS'.trans (Submodule.map_subtype_le V _)
      have hf' : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
      have hk : KStable ε E (S'.comap V.subtype) :=
        (hst _ (hfd S' hV hf')).2 (by rw [hmc S' hV]; exact hK)
      have hle : S'.comap V.subtype ≤ kSpan ε E u := by
        have := Submodule.comap_mono (f := V.subtype) hS'
        rwa [Submodule.comap_map_eq_of_injective V.injective_subtype] at this
      rcases hIrr V n ε E μ u hf hR hU hu _ hle hk with h | h
      · left; rw [← hmc S' hV, h, Submodule.map_bot]
      · right; rw [← hmc S' hV, h]
    · exact ⟨u, ⟨u, mem_compact_span_self u, rfl⟩, fun h => hu0 (Subtype.ext h), (hwt μ u).1 hu.1⟩
    · rintro ν _ ⟨y, hy, rfl⟩ hy0 hw
      exact cdom_of_mem hR hU hu hy (fun h => hy0 (by rw [h]; rfl)) ((hwt ν y).2 hw)
  · rintro μ S u ⟨hf, hK, hI, -, hC⟩ hV huS hu0 hw
    have hw' : IsWeight E μ u := (hwt μ u).2 hw
    have hfc := hfd S hV hf
    have hk : KStable ε E (S.comap V.subtype) := (hst _ hfc).2 (by rw [hmc S hV]; exact hK)
    have hle : kSpan ε E u ≤ S.comap V.subtype := compact_span_le_stable huS hk
    have hfk : FiniteDimensional ℂ (kSpan ε E u) := Submodule.finiteDimensional_of_le hle
    refine ⟨⟨hw', ?_⟩, ?_, hfk⟩
    · intro a b hab he
      by_contra hne
      exact not_cdom_add μ hab (hC _ (E a b u : V) (hk a b he u huS) (fun h => hne (Subtype.ext h))
        ((hwt _ _).1 (compact_weight_shift hR hw' he)))
    · rcases hI _ (Submodule.map_le_iff_le_comap.mpr hle) ((hst _ hfk).1 (compact_span_stable u)) with h | h
      · exfalso
        have : (u : H) ∈ (kSpan ε E u).map V.subtype := ⟨u, mem_compact_span_self u, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact hu0 (Subtype.ext this)
      · exact h

end GlobalTheory.Jet.KType
end
end

section

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.MeanDual

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def invT (g : MatInf E j) : MatInf E j := fun w a b => (Matrix.of (g w))⁻¹ b a

def trDual (Λ : Submodule (𝓞 E) (Fin j → E)) : Submodule (𝓞 E) (Fin j → E) where
  carrier := {y | ∀ x ∈ Λ, ∃ z : ℤ, Algebra.trace ℚ E (x ⬝ᵥ y) = 2 * (z : ℚ)}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z, hz⟩ := ha x hx
    obtain ⟨z', hz'⟩ := hb x hx
    exact ⟨z + z', by rw [dotProduct_add, map_add (f := _), hz, hz']; push_cast; ring⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c y hy x hx
    obtain ⟨z, hz⟩ := hy (c • x) (Λ.smul_mem c hx)
    refine ⟨z, ?_⟩
    rw [← hz, dotProduct_smul, smul_dotProduct]

theorem mem_trDual {Λ : Submodule (𝓞 E) (Fin j → E)} {y : Fin j → E} :
    y ∈ trDual E j Λ ↔ ∀ x ∈ Λ, ∃ z : ℤ, Algebra.trace ℚ E (x ⬝ᵥ y) = 2 * (z : ℚ) := Iff.rfl

theorem of_invT (g : MatInf E j) (w : InfinitePlace E) :
    Matrix.of (invT E j g w) = ((Matrix.of (g w))⁻¹)ᵀ := rfl

theorem of_mul (g h : MatInf E j) (w : InfinitePlace E) :
    Matrix.of ((g * h) w) = Matrix.of (g w) * Matrix.of (h w) := rfl

theorem matInf_ext {g h : MatInf E j} (H : ∀ w, Matrix.of (g w) = Matrix.of (h w)) : g = h :=
  funext fun w => Matrix.of.injective (H w)

theorem detNorm_pos_iff (g : MatInf E j) :
    0 < GlobalTheory.FlagMeas.detNorm E j g ↔ ∀ w, (Matrix.of (g w)).det ≠ 0 := by
  unfold GlobalTheory.FlagMeas.detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

theorem invT_mul (g h : MatInf E j) : invT E j (g * h) = invT E j g * invT E j h := by
  apply matInf_ext
  intro w
  rw [of_invT, of_mul, of_mul, of_invT, of_invT, Matrix.mul_inv_rev, Matrix.transpose_mul]

theorem detNorm_invT_pos_iff (g : MatInf E j) :
    0 < GlobalTheory.FlagMeas.detNorm E j (invT E j g) ↔ 0 < GlobalTheory.FlagMeas.detNorm E j g := by
  simp only [detNorm_pos_iff, of_invT, Matrix.det_transpose, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', ne_eq, inv_eq_zero]

theorem invT_invT {g : MatInf E j} (hg : 0 < GlobalTheory.FlagMeas.detNorm E j g) : invT E j (invT E j g) = g := by
  apply matInf_ext
  intro w
  rw [of_invT, of_invT, ← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 ((detNorm_pos_iff E j g).1 hg w))]

theorem detNorm_mul (g h : MatInf E j) : GlobalTheory.FlagMeas.detNorm E j (g * h) = GlobalTheory.FlagMeas.detNorm E j g * GlobalTheory.FlagMeas.detNorm E j h := by
  unfold GlobalTheory.FlagMeas.detNorm
  simp only [of_mul, Matrix.det_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]

theorem continuous_detNorm :
    Continuous (fun g : InfinitePlace E → Fin j → Fin j → ℂ => GlobalTheory.FlagMeas.detNorm E j g) := by
  unfold GlobalTheory.FlagMeas.detNorm
  refine continuous_finsetProd _ fun w _ => ?_
  refine Continuous.pow (Continuous.norm ?_) 2
  exact Continuous.matrix_det (A := fun g : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (g w))
    (continuous_apply w)

theorem measurableSet_detNorm_pos : MeasurableSet {g : MatInf E j | 0 < GlobalTheory.FlagMeas.detNorm E j g} :=
  (isOpen_lt continuous_const (continuous_detNorm E j)).measurableSet

end GlobalTheory.MeanDual
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.absolute_hermitian_volume_bound_arith : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (X : ℝ), 8 ≤ n → 2 ≤ X → 2 * Formalism.HermitianLatticesTheory.vInv E ≤ X → 2 * Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ X ^ 2 → volU 2 ^ Formalism.HermitianLatticesTheory.fDeg E * (4 ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E) * (1 + Formalism.HermitianLatticesTheory.fDeg E * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E)) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E)) * ∏ M ∈ Finset.Ioc 2 n, rankFac E M ≤ X ^ (n ^ 2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  first | exact @GlobalTheory.VolArith.volume_bound_arith | exact GlobalTheory.VolArith.volume_bound_arith | (intros; apply GlobalTheory.VolArith.volume_bound_arith <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.prod_five_factors_hermitian_volume : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (p q a : ℕ) (j : Fin a → ℕ), ∑ i, j i ≤ q → 2 * q + 2 ≤ p + q → cIw p q j ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * dimN (p + q) j / 2) * (∏ i, 2 ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * ∏ l ∈ Finset.Icc 2 (j i), zetaE E l)) / ∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), rankFac E M = kapBd E p q j := by
  first | exact @GlobalTheory.FiveFactors.prod_five_factors | exact GlobalTheory.FiveFactors.prod_five_factors | (intros; apply GlobalTheory.FiveFactors.prod_five_factors <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.representativeValuesVector_variation_unipotentOrbit : ∀ (B : RowsAut) (b ρ M : ℝ) (P : ℕ) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA) (W : Submodule B.I.E (Fin B.I.n → B.I.E)), StepBoundAt B b P → (∀ i, IsReps B (T i) (Fr i)) → 0 ≤ M → (∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B (P + 1), ‖vv B Fr u y‖ ≤ M * ‖u‖) → ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P, ‖vv B Fr u y - vv B Fr u x‖ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
  first | exact @GlobalTheory.PathVar.path_variation | exact GlobalTheory.PathVar.path_variation | (intros; apply GlobalTheory.PathVar.path_variation <;> assumption)
end
