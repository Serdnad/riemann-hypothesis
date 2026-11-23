module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle588
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle589
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle590
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle591
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle592
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ResidueCardinality.ArtinOntoB
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.LatDiag

variable {E : Type} [Field E] [NumberField E] {w : Pl E}

theorem unif_ne_zero {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ≠ 0 := by
  rintro rfl
  unfold IsUnifV at h
  rw [map_zero] at h
  exact WithZero.zero_ne_coe h

theorem unif_lt_one {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : Valued.v ϖ < 1 := by
  unfold IsUnifV at h
  rw [h]
  exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1)

theorem le_one_of_unif_mul {ϖ x : w.adicCompletion E} (h : IsUnifV E w ϖ)
    (hx : Valued.v (ϖ * x) < 1) : Valued.v x ≤ 1 := by
  unfold IsUnifV at h
  rw [map_mul, h] at hx
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]; exact zero_le
  obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp h0
  rw [← hm] at hx ⊢
  have h1 : Multiplicative.ofAdd (-1 : ℤ) * m < 1 := by exact_mod_cast hx
  have h2 : (-1 : ℤ) + Multiplicative.toAdd m < 0 := h1
  have h3 : m ≤ 1 := by
    show Multiplicative.toAdd m ≤ 0
    omega
  exact_mod_cast h3

theorem mem_max_iff (x : w.adicCompletionIntegers E) :
    x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) ↔
      Valued.v (x : w.adicCompletion E) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hx
    refine lt_of_le_of_ne x.2 fun h1 => hx ?_
    have hx0 : (x : w.adicCompletion E) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : w.adicCompletion E)⁻¹ ∈ w.adicCompletionIntegers E := by
      show Valued.v (x : w.adicCompletion E)⁻¹ ≤ 1
      rw [map_inv₀, h1, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hx0))
  · intro hx hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h1 : Valued.v (x : w.adicCompletion E) * Valued.v (y : w.adicCompletion E) = 1 := by
      rw [← map_mul]
      have : (x : w.adicCompletion E) * (y : w.adicCompletion E) = 1 := congrArg Subtype.val hy
      rw [this, map_one]
    have h2 : Valued.v (y : w.adicCompletion E) ≤ 1 := y.2
    have h3 := lt_of_le_of_lt (mul_le_of_le_one_right' h2) hx
    exact absurd h1 (ne_of_lt h3)

def posR {a i : ℕ} (hi : i ≤ a) (r : Fin i) : Fin a := Fin.castLE hi r

def posS {b j : ℕ} (s : Fin (b - j)) : Fin b := ⟨j + s, by have := s.2; omega⟩

theorem corner_mem {ϖ : w.adicCompletion E} {a b i j : ℕ} (hi : i ≤ a)
    (W : latD ϖ a b i j) (p : Fin i × Fin (b - j)) :
    ϖ * W.1 (posR hi p.1) (posS p.2) ∈ w.adicCompletionIntegers E := by
  have h := W.2 (posR hi p.1) (posS p.2)
  have hc : ((posR hi p.1 : Fin a) : ℕ) < i ∧ j ≤ ((posS p.2 : Fin b) : ℕ) :=
    ⟨p.1.2, Nat.le_add_right _ _⟩
  rw [if_pos hc] at h
  exact h

def cornerMap (ϖ : w.adicCompletion E) (a b i j : ℕ) (hi : i ≤ a) :
    latD ϖ a b i j →+
      (Fin i × Fin (b - j) → IsLocalRing.ResidueField (w.adicCompletionIntegers E)) where
  toFun W p := IsLocalRing.residue _ ⟨_, corner_mem hi W p⟩
  map_zero' := by
    funext p
    have : (⟨_, corner_mem hi (0 : latD ϖ a b i j) p⟩ : w.adicCompletionIntegers E) = 0 :=
      Subtype.ext (by simp)
    simp only [this, map_zero, Pi.zero_apply]
  map_add' X Y := by
    funext p
    have : (⟨_, corner_mem hi (X + Y) p⟩ : w.adicCompletionIntegers E) =
        ⟨_, corner_mem hi X p⟩ + ⟨_, corner_mem hi Y p⟩ :=
      Subtype.ext (by simp [mul_add])
    simp only [this, map_add (f := _), Pi.add_apply]

theorem cornerMap_apply (ϖ : w.adicCompletion E) (a b i j : ℕ) (hi : i ≤ a) (W : latD ϖ a b i j)
    (p : Fin i × Fin (b - j)) :
    cornerMap ϖ a b i j hi W p = IsLocalRing.residue _ ⟨_, corner_mem hi W p⟩ := rfl

theorem ker_cornerMap {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (a b i j : ℕ) (hi : i ≤ a)
    (hj : j ≤ b) :
    (cornerMap ϖ a b i j hi).ker = (intSub a b w).addSubgroupOf (latD ϖ a b i j) := by
  ext W
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro hW r s
    have hWp : ∀ p : Fin i × Fin (b - j), Valued.v (ϖ * W.1 (posR hi p.1) (posS p.2)) < 1 := by
      intro p
      have := congrFun hW p
      rw [cornerMap_apply, Pi.zero_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff] at this
      exact this
    by_cases hc : (r : ℕ) < i ∧ j ≤ (s : ℕ)
    · have := hWp (⟨r, hc.1⟩, ⟨s - j, by have := s.2; omega⟩)
      have hr : posR hi ⟨(r : ℕ), hc.1⟩ = r := Fin.ext rfl
      have hs : posS (j := j) (⟨(s : ℕ) - j, by have := s.2; omega⟩ : Fin (b - j)) = s :=
        Fin.ext (by simp [posS]; omega)
      simp only [hr, hs] at this
      exact le_one_of_unif_mul h this
    · have := W.2 r s
      rw [if_neg hc] at this
      exact this
  · intro hW
    funext p
    rw [cornerMap_apply, Pi.zero_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
    show Valued.v (ϖ * W.1 (posR hi p.1) (posS p.2)) < 1
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hW _ _)) (unif_lt_one h)

theorem cornerMap_surjective {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (a b i j : ℕ)
    (hi : i ≤ a) (hj : j ≤ b) : Function.Surjective (cornerMap ϖ a b i j hi) := by
  intro c
  choose x hx using fun p => IsLocalRing.residue_surjective (c p)
  have h0 := unif_ne_zero h
  let M : Matrix (Fin a) (Fin b) (w.adicCompletion E) := fun r s =>
    if hc : (r : ℕ) < i ∧ j ≤ (s : ℕ) then
      ϖ⁻¹ * (x (⟨r, hc.1⟩, ⟨s - j, by have := s.2; omega⟩) : w.adicCompletion E) else 0
  have hM : M ∈ latD ϖ a b i j := by
    intro r s
    by_cases hc : (r : ℕ) < i ∧ j ≤ (s : ℕ)
    · rw [if_pos hc]
      simp only [M, dif_pos hc]
      rw [mul_inv_cancel_left₀ h0]
      exact (x _).2
    · rw [if_neg hc]
      simp only [M, dif_neg hc]
      exact (Ov E w).zero_mem
  refine ⟨⟨M, hM⟩, ?_⟩
  funext p
  rw [cornerMap_apply, ← hx p]
  congr 1
  apply Subtype.ext
  have hc : ((posR hi p.1 : Fin a) : ℕ) < i ∧ j ≤ ((posS p.2 : Fin b) : ℕ) :=
    ⟨p.1.2, Nat.le_add_right _ _⟩
  show ϖ * M (posR hi p.1) (posS p.2) = _
  simp only [M, dif_pos hc]
  rw [mul_inv_cancel_left₀ h0]
  congr 2
  refine Prod.ext (Fin.ext rfl) (Fin.ext ?_)
  simp [posS]

theorem relIndex_intSub_latD (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (ϖ : w.adicCompletion E) (h : IsUnifV E w ϖ) (i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    (intSub a b w).relIndex (latD ϖ a b i j) = (qV E w) ^ (i * (b - j)) := by
  have hcard : Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) = qV E w := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue w]
    simp [qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [AddSubgroup.relIndex, ← ker_cornerMap h a b i j hi hj, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (cornerMap_surjective h a b i j hi hj), AddSubgroup.card_top,
    Nat.card_fun, hcard, Nat.card_prod, Nat.card_fin, Nat.card_fin]

end GlobalTheory.CompanionTheory.CtS.LatDiag
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem eFinalGlue_of (hCS : ConvStrip) (hCC : ConvComp) (hFS : FactorStep) (hLL : LimLists) (hOS : OneStep)
    (hFL : FactorLim) (hMC : MCloseFacts) (hPE : PairEmb) (hPS : PairSlices) (hST : SliceType) : InfinitesimalCharacterGlue := by
  intro hE3 hSep hLim hGraft hTw hTr hLV hAD hUn hInf E _ _ _ a b W₁ W₂ hW₁ hW₂
  obtain ⟨Ωs₁, hΩs₁, S₁⟩ := hFS hSep E a W₁ hW₁
  obtain ⟨Ωs₂, hΩs₂, S₂⟩ := hFS hSep E b W₂ hW₂
  obtain ⟨Ωf₁, hΩf₁, X₁⟩ := hLL hLim hTw E a Ωs₁ hΩs₁
  obtain ⟨Ωf₂, hΩf₂, X₂⟩ := hLL hLim hTw E b Ωs₂ hΩs₂
  refine ⟨Ωf₁, Ωf₂, hΩf₁, hΩf₂, fun K₁ K₂ hK₁ hK₂ => ?_⟩
  obtain ⟨Θs₁, hΘs₁, F₁⟩ := S₁ K₁ hK₁
  obtain ⟨Θs₂, hΘs₂, F₂⟩ := S₂ K₂ hK₂
  obtain ⟨Θf₁, hΘf₁, P₁⟩ := X₁ Θs₁ hΘs₁
  obtain ⟨Θf₂, hΘf₂, P₂⟩ := X₂ Θs₂ hΘs₂
  refine ⟨Θf₁, Θf₂, hΘf₁, hΘf₂, ?_⟩
  intro D ι _ M m₁ m₂ n₁ n₂ C lam lam₀ f hC hRep hcont hne hL hWL hTy hs1 hs2 ha1 ha2 hi1 hi2 heig hconv hR1 hR2 hgap hlam
  have hfar : ∀ᶠ k in atTop, ∀ τ, MClose (1 / 8) (m₁ k τ) (n₁ τ) ∧ MClose (1 / 8) (m₂ k τ) (n₂ τ) :=
    Filter.eventually_all.2 fun τ => hconv τ (1 / 8) (by norm_num)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hfar
  have h3 := fun k => hE3 E a b D ι M (f k) K₁ K₂ W₁ W₂ (m₁ k) (m₂ k) hK₁ hK₂ hW₁ hW₂ (hcont k) (hL k) (hWL k)
    (hTy k) (hs1 k) (hs2 k) (ha1 k) (ha2 k) (hi1 k) (hi2 k)
  have hone := fun k => hOS E a b ι K₁ K₂ W₁ W₂ Θs₁ Θs₂ Ωs₁ Ωs₂ (f (k + k₀)) (m₁ (k + k₀)) (m₂ (k + k₀)) hW₁ hW₂ F₁ F₂
    (hne _) (hTy _) (hs1 _) (hs2 _) (h3 _).2.2.1 (h3 _).2.2.2.1 (h3 _).2.2.2.2.1 (h3 _).2.2.2.2.2.1
    (h3 _).2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.2.1
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).1 (hgap τ).1)
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).2 (hgap τ).2)
    (h3 _).2.2.2.2.2.2.2.2.2.2
  choose t₁ t₂ G ψ₁ ψ₂ hr₁ hr₂ hg₁ hg₂ hl₁ hl₂ hG0 hGm hGt hGe hp₁ hp₁0 hc₁ hp₂ hp₂0 hc₂ using hone
  have hB : ∀ n : (E →+* ℂ) → Multiset ℂ, ∃ B : ℝ, ∀ τ, ∀ y ∈ n τ, ‖y‖ ≤ B := fun n => by
    classical
    obtain ⟨B, hB⟩ := ((Finset.univ.biUnion fun τ => (n τ).toFinset).image norm).finite_toSet.bddAbove
    refine ⟨B, fun τ y hy => hB ?_⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Multiset.mem_toFinset]
    exact ⟨y, ⟨τ, hy⟩, rfl⟩
  obtain ⟨B₁, hB₁⟩ := hB n₁
  obtain ⟨B₂, hB₂⟩ := hB n₂
  obtain ⟨φ₁, t₁', s₁, hφ₁, hC₁, hs₁R, hs₁G, hs₁L, hD₁, hI₁, hE₁⟩ := hFL hTr hGraft hInf E Θs₁ Θf₁ Ωs₁ Ωf₁ a t₁ ψ₁
    (fun k => m₁ (k + k₀)) n₁ (B₁ + 1 / 8) P₁ hRep hr₁ hg₁ hl₁ hp₁ hp₁0 hc₁
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (k + k₀) (by omega) τ).1 (hB₁ τ))
    (fun τ ε hε => ((tendsto_add_atTop_nat k₀).eventually (hconv τ ε hε)).mono fun _ h => h.1)
  obtain ⟨φ₂, t₂', s₂, hφ₂, hC₂, hs₂R, hs₂G, hs₂L, hD₂, hI₂, hE₂⟩ := hFL hTr hGraft hInf E Θs₂ Θf₂ Ωs₂ Ωf₂ b
    (fun k => t₂ (φ₁ k)) (fun k => ψ₂ (φ₁ k))
    (fun k => m₂ (φ₁ k + k₀)) n₂ (B₂ + 1 / 8) P₂ hRep (fun k => hr₂ _) (fun k => hg₂ _) (fun k => hl₂ _)
    (fun k => hp₂ _) (fun k => hp₂0 _) (fun k => hc₂ _)
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (φ₁ k + k₀) (by omega) τ).2 (hB₂ τ))
    (fun τ ε hε => (((tendsto_add_atTop_nat k₀).comp hφ₁.tendsto_atTop).eventually (hconv τ ε hε)).mono fun _ h => h.2)
  have hstab : ∀ {N : ℕ} {t : Tr E N}, t.Good → IsStable t.space := fun h => hTr E _ _ (disc_stable (good_disc h))
  have hG' := fun k => hPE E a b ι K₁ K₂ W₁ W₂ (t₁ (φ₁ (φ₂ k))).space (t₁' (φ₂ k)).space (t₂ (φ₁ (φ₂ k))).space (t₂' k).space
    (G (φ₁ (φ₂ k))) hW₁ hW₂ (hstab (hg₁ _)) (hstab (hg₂ _)) (hE₁ _) (hE₂ _) (hG0 _) (hGm _) (hGt _)
  choose G' hG'0 hG'm hG't hG'e using hG'
  have hCC₁ := (hCS E a _ _).1 (hCC E a _ _ φ₂ hC₁ hφ₂)
  have hCC₂ := (hCS E b _ _).1 hC₂
  obtain ⟨F, hF0, hFm, hFt, hFe⟩ := hLV hAD E a b ι (fun k => t₁' (φ₂ k)) t₂' s₁ s₂ K₁ K₂ W₁ W₂ C
    (fun k => lam (φ₁ (φ₂ k) + k₀)) lam₀ G' hK₁ hK₂ hW₁ hW₂ hC hs₁G hs₂G (fun k => hD₁ _) hD₂ hCC₁.1 hCC₂.1 hCC₁.2 hCC₂.2
    hG'0 hG'm hG't (fun k h hh => hG'e k h _ (hGe _ h _ (heig _ h hh)))
    (fun h hh => (hlam h hh).comp ((tendsto_add_atTop_nat k₀).comp (hφ₁.comp hφ₂).tendsto_atTop))
  obtain ⟨i, hi⟩ : ∃ i, F i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hF0 (funext hcon)
  obtain ⟨x, hx⟩ : ∃ x, F i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hi (funext hcon)
  have hsl := hPS E a b _ _ (F i) (hFm i)
  have hn₁ : sl₁ (F i) x.2 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.1 x.2).2 x.1
    rw [h] at this
    exact this.symm)
  have hn₂ : sl₂ (F i) x.1 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.2 x.1).2 x.2
    rw [h] at this
    exact this.symm)
  have hb₁ : s₁.space ≠ ⊥ := fun h => hn₁ (by simpa [h] using (hsl.1 x.2).1)
  have hb₂ : s₂.space ≠ ⊥ := fun h => hn₂ (by simpa [h] using (hsl.2 x.1).1)
  exact ⟨s₁, s₂, F, hs₁G, hs₂G, hUn E a s₁ n₁ hs₁G hb₁ hI₁ hR1, hUn E b s₂ n₂ hs₂G hb₂ hI₂ hR2, hs₁L, hs₂L,
    hI₁, hI₂, hF0, hFm, hFt, hFe⟩

theorem eFinalGlue : PositivityTheory.Rg.BcB.SpectralAccumulation.InfinitesimalCharacterGlue :=
  have hPS := GlobalTheory.T.pair_slices
  have hP1 := GlobalTheory.T.pair_first_step hPS
  have hP2 := GlobalTheory.T.pair_second_step hPS
  have hCE := GlobalTheory.T.capacity_equivalence
  have hDI := GlobalTheory.T.discrete_infimum
  have hTI := GlobalTheory.T.topological_infimum
  have hIE := GlobalTheory.T.infimum_of_equality
  have hCS := GlobalTheory.T.convergence_strip
  have hCC := GlobalTheory.T.convergence_composition
  have hMC := GlobalTheory.T.closure_facts_alt
  eFinalGlue_of hCS hCC GlobalTheory.T.factor_induction (GlobalTheory.T.limit_lists hCS GlobalTheory.T.convergence_shift hCC)
    (GlobalTheory.T.single_gluing hPS GlobalTheory.T.pair_restriction GlobalTheory.T.pair_finite_dimensional GlobalTheory.T.slice_type hP1 hP2 GlobalTheory.T.hull_generation hCE)
    (GlobalTheory.T.factor_limit hCC (GlobalTheory.T.limit_trees hCC) (GlobalTheory.T.leaf_bound_alt hDI hTI hIE) (GlobalTheory.T.convergence_infimum hDI hTI) hIE hCE hMC)
    hMC (GlobalTheory.T.pair_embedding hPS hP1 hP2) hPS GlobalTheory.T.slice_type

end GlobalTheory.CompanionTheory.EGlue

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.continuous_orbital_integral_unipotent : IkSch → Dom → OrbFin → Shift → JnBl → Ext0 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ Φ ∈ schwartzA θ B.rank n, Continuous (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.continuous_orb_shear | exact GlobalTheory.CompanionTheory.ColumnSplitting.continuous_orb_shear | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.continuous_orb_shear <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.zeta_polynomial_identity : ZpEq := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.zp_eq | exact GlobalTheory.CompanionTheory.ColumnSplitting.zp_eq | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.zp_eq <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integrable_theta_kernel_fibers : ZpEq → AcEq → JnPi → Ext0 → Fub4 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → ∀ Φ ∈ schwartzA θ B.rank n, ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) → Integrable (fun z => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) (nuT hn I μ x₀) ∧ ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂(nuT hn I μ x₀) = ∫ y, orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀) * conj (η y) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.Form.nuT_form | exact GlobalTheory.CompanionTheory.ColumnSplitting.Form.nuT_form | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.Form.nuT_form <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orbit_measure_concentrated_on_quadric : ZpEq → AcEq → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → nuT hn I μ x₀ {z | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧ ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp | exact GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orbit_measure_translation_invariant : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (y : Mx D W.rank t), (nuT hn I μ x₀).map (fun z => (z.1, z.2 + mm z.1 y)) = nuT hn I μ x₀ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant | exact GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.abscissa_convergence_identity : AcEq := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq | exact GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extension_by_zero_orbit_formula : Ext0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action | exact GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.iterated_integrals_four_factors : Fub4 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds | exact GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.joined_block_formula : JnBl := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.jnBl | exact GlobalTheory.CompanionTheory.ColumnSplitting.jnBl | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.jnBl <;> assumption)
end
