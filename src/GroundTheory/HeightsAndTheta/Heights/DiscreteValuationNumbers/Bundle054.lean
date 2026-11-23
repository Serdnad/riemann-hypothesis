module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle048
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutPreimage.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ), k < N → ∀ (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)),
      W.IsPrime → IsRelevant W → pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W →
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W →
      ∃ u : MRing (bundleIdx (bundleIdx ι M) M') O, u ∉ W ∧
        ∀ q ∈ pointIdeal O (flagClosurePt y w e φ φ' t k), ∃ n : ℕ,
          u ^ n * q ∈ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔
            (pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k)).map
              (rename (FieldNumbers.blockIncl secondFactorBlocks (bundleIdx (bundleIdx ι M) M')))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HomLocRingNoetherian

variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}

theorem component_form_mul {s : MRing ι R} {e : K → ℕ} (hs : IsMultiHomog s e) (d : K → ℕ)
    (h : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) (e + d) (s * h) =
      s * weightedHomogeneousComponent (blockWeight ι) d h := by
  classical
  let _ := weightedGradedAlgebra R (blockWeight ι)
  have hmem : s ∈ weightedHomogeneousSubmodule R (blockWeight ι) e :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs
  have := DirectSum.coe_decompose_mul_add_of_left_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight ι)) (j := d) (b := h) hmem
  rw [← weightedDecomposition.decompose'_apply R (blockWeight ι) (s * h) (e + d),
    ← weightedDecomposition.decompose'_apply R (blockWeight ι) h d]
  exact this

variable (P : Ideal (MRing ι R)) [P.IsPrime]

abbrev img : MRing ι R →+* FractionRing (MRing ι R ⧸ P) :=
  (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))).comp (Ideal.Quotient.mk P)

variable {P}


omit [DecidableEq K] in
theorem img_eq_zero_iff {f : MRing ι R} : img P f = 0 ↔ f ∈ P := by
  simp [img, Ideal.Quotient.eq_zero_iff_mem]

theorem img_component_congr (hP : IsMultiHomogIdeal P) {u v : MRing ι R} (huv : img P u = img P v)
    (d : K → ℕ) :
    img P (weightedHomogeneousComponent (blockWeight ι) d u) =
      img P (weightedHomogeneousComponent (blockWeight ι) d v) := by
  rw [← sub_eq_zero, ← map_sub, img_eq_zero_iff] at huv ⊢
  rw [← map_sub]
  exact hP _ huv d


omit [DecidableEq K] in
theorem img_ne_zero {W : Ideal (MRing ι R)} (hPW : P ≤ W) {t : MRing ι R} (ht : t ∉ W) :
    img P t ≠ 0 := fun h0 => ht (hPW (img_eq_zero_iff.mp h0))

theorem quot_mem {W : Ideal (MRing ι R)} {b : K → ℕ} {f g : MRing ι R} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) (hgW : g ∉ W) : img P f / img P g ∈ homLocRing P W :=
  Subring.subset_closure ⟨b, f, g, hf, hg, hgW, rfl⟩

end HomLocRingNoetherian


open HomLocRingNoetherian in
theorem HomLocRingNoetherian.proof (hmem : HomLocRingMem.Statement.{u}) :
    HomLocRingNoetherian.Statement.{u} := by
  intro R _ _ K _ _ ι _ P W _ hP hW _ hPW
  classical
  set S := MRing ι R
  set D := S ⧸ P
  set F := FractionRing D

  let T : Submonoid S :=
    { carrier := {s | (∃ e, IsMultiHomog s e) ∧ s ∉ W}
      one_mem' := ⟨⟨0, isWeightedHomogeneous_one R _⟩, (Ideal.ne_top_iff_one W).mp hW.ne_top⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨⟨_, ha.1.choose_spec.mul hb.1.choose_spec⟩, hW.mul_notMem ha.2 hb.2⟩ }
  let T' : Submonoid D := T.map (Ideal.Quotient.mk P)
  have hT' : T' ≤ nonZeroDivisors D := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ht.2 (hPW ?_)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  let B : Subalgebra D F := Localization.subalgebra F T' hT'
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing T' B inferInstance

  have rep : ∀ y ∈ B, ∃ (h t : S) (e : K → ℕ), IsMultiHomog t e ∧ t ∉ W ∧ y * img P t = img P h := by
    rintro y ⟨a, s, ⟨t, ⟨⟨e, hte⟩, htW⟩, rfl⟩, rfl⟩
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨h, t, e, hte, htW, IsLocalization.mk'_spec _ _ _⟩
  have hAB : ∀ x ∈ homLocRing P W, x ∈ B := by
    intro x hx
    refine (Subring.closure_le (t := B.toSubring)).mpr ?_ hx
    rintro _ ⟨b, f, g, hf, hg, hgW, rfl⟩
    exact ⟨Ideal.Quotient.mk P f, Ideal.Quotient.mk P g, ⟨g, ⟨⟨b, hg⟩, hgW⟩, rfl⟩,
      by rw [IsFractionRing.mk'_eq_div]⟩
  let j : homLocRing P W →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

  have key : ∀ (I : Ideal (homLocRing P W)) (z : homLocRing P W), j z ∈ I.map j → z ∈ I := by
    intro I z hz
    let Q : F → Prop := fun y => ∀ (s : S) (e : K → ℕ) (h : S), IsMultiHomog s e → s ∉ W →
      y * img P s = img P h → ∀ (d : K → ℕ) (t : S), IsMultiHomog t d → t ∉ W →
        ∃ a ∈ I, (a : F) = img P (weightedHomogeneousComponent (blockWeight ι) d h) / img P t
    have Q0 : Q 0 := by
      intro s e h _ _ hy d t _ _
      refine ⟨0, I.zero_mem, ?_⟩
      rw [zero_mul, eq_comm, img_eq_zero_iff] at hy
      rw [img_eq_zero_iff.mpr (hP h hy d), zero_div]
      rfl
    have Qadd : ∀ y₁ ∈ B, ∀ y₂ ∈ B, Q y₁ → Q y₂ → Q (y₁ + y₂) := by
      intro y₁ hy₁ y₂ hy₂ Q₁ Q₂ s e h hs hsW hy d t ht htW
      obtain ⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩ := rep y₁ hy₁
      obtain ⟨h₂, t₂, e₂, ht₂, ht₂W, hb₂⟩ := rep y₂ hy₂
      have hσ : IsMultiHomog (s * t₁ * t₂) (e + e₁ + e₂) := (hs.mul ht₁).mul ht₂
      have hσW : s * t₁ * t₂ ∉ W := hW.mul_notMem (hW.mul_notMem hsW ht₁W) ht₂W
      have hτ : IsMultiHomog (t₁ * t₂ * t) ((e₁ + e₂) + d) := (ht₁.mul ht₂).mul ht
      have hτW : t₁ * t₂ * t ∉ W := hW.mul_notMem (hW.mul_notMem ht₁W ht₂W) htW
      obtain ⟨a₁, ha₁I, ha₁⟩ := Q₁ _ _ (h₁ * (s * t₂)) hσ hσW
        (by simp only [map_mul]; rw [← hb₁]; ring) _ _ hτ hτW
      obtain ⟨a₂, ha₂I, ha₂⟩ := Q₂ _ _ (h₂ * (s * t₁)) hσ hσW
        (by simp only [map_mul]; rw [← hb₂]; ring) _ _ hτ hτW
      refine ⟨a₁ + a₂, I.add_mem ha₁I ha₂I, ?_⟩
      have hsum : img P (h₁ * (s * t₂) + h₂ * (s * t₁)) = img P ((t₁ * t₂) * h) := by
        simp only [map_mul, map_add (f := _)]; rw [← hb₁, ← hb₂, ← hy]; ring
      have hc := img_component_congr hP hsum ((e₁ + e₂) + d)
      rw [component_form_mul (ht₁.mul ht₂), map_add (f := _), map_add (f := _)] at hc
      have h1 := img_ne_zero hPW ht₁W
      have h2 := img_ne_zero hPW ht₂W
      have h3 := img_ne_zero hPW htW
      rw [Subring.coe_add, ha₁, ha₂, ← add_div, hc]
      simp only [map_mul]
      field_simp
    have Qgen : ∀ b ∈ B, ∀ a ∈ I, Q (b * (a : F)) := by
      intro b hb a haI s e h hs hsW hy d t ht htW
      obtain ⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩ := rep b hb
      obtain ⟨c, f, g, hf, hg, hgW, hfg⟩ := (hmem R K ι P W hW hPW a).mp a.2
      have hfg' : (a : F) = img P f / img P g := hfg
      have hg0 := img_ne_zero hPW hgW
      have hfa : img P f = a * img P g := by rw [hfg', div_mul_cancel₀ _ hg0]
      have hrel : img P (f * (h₁ * s)) = img P ((t₁ * g) * h) := by
        simp only [map_mul]; rw [hfa, ← hy, ← hb₁]; ring
      have hc := img_component_congr hP hrel (c + (d + e₁))
      rw [component_form_mul hf, show c + (d + e₁) = (e₁ + c) + d by abel,
        component_form_mul (ht₁.mul hg)] at hc
      have ha' := quot_mem (P := P) (W := W)
        (weightedHomogeneousComponent_isWeightedHomogeneous (d + e₁) (h₁ * s)) (ht.mul ht₁)
        (hW.mul_notMem htW ht₁W)
      refine ⟨a * ⟨_, ha'⟩, I.mul_mem_right _ haI, ?_⟩
      have h1 := img_ne_zero hPW ht₁W
      have h3 := img_ne_zero hPW htW
      rw [Subring.coe_mul, hfg']
      simp only [map_mul] at hc ⊢
      field_simp
      linear_combination hc
    have hspan : ∀ y ∈ I.map j, ∀ b : B, Q ((b : F) * (y : F)) := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨a, haI, rfl⟩ b
        exact Qgen b b.2 a haI
      · intro b
        simpa using Q0
      · intro y₁ y₂ _ _ Q₁ Q₂ b
        have := Qadd _ (b * y₁).2 _ (b * y₂).2 (Q₁ b) (Q₂ b)
        simpa [mul_add] using this
      · intro c y _ Qy b
        have := Qy (b * c)
        simpa [mul_assoc] using this
    obtain ⟨c, f, g, hf, hg, hgW, hfg⟩ := (hmem R K ι P W hW hPW z).mp z.2
    have hfg' : (z : F) = img P f / img P g := hfg
    have hg0 := img_ne_zero hPW hgW
    obtain ⟨a, haI, ha⟩ := hspan _ hz 1 g c f hg hgW
      (by show 1 * (z : F) * img P g = img P f; rw [one_mul, hfg', div_mul_cancel₀ _ hg0])
      c g hg hgW
    rw [hf.weightedHomogeneousComponent_same, ← hfg'] at ha
    exact (Subtype.ext ha : a = z) ▸ haI
  have hinj : Function.Injective (fun I : Ideal (homLocRing P W) => I.map j) := by
    intro I₁ I₂ h12
    have e : ∀ I : Ideal (homLocRing P W), (I.map j).comap j = I := fun I =>
      le_antisymm (fun z hz => key I z hz) Ideal.le_comap_map
    rw [← e I₁, ← e I₂]
    exact congrArg (Ideal.comap j) h12
  have hmono' : Monotone (fun I : Ideal (homLocRing P W) => I.map j) := fun _ _ h => Ideal.map_mono h
  have hmono : StrictMono (fun I : Ideal (homLocRing P W) => I.map j) :=
    hmono'.strictMono_of_injective hinj
  have : WellFoundedGT (Ideal B) := isNoetherian_iff'.mp (isNoetherianRing_iff.mp inferInstance)
  exact isNoetherianRing_iff.mpr (isNoetherian_iff'.mpr hmono.wellFoundedGT)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem HomLocRingIsLocal.proof (h : HomLocRingMem.Statement.{u}) : HomLocRingIsLocal.Statement.{u} := by
  intro R _ K _ ι P W _ hW hPW
  let F := FractionRing (MRing ι R ⧸ P)
  let φ : MRing ι R →+* F := (algebraMap (MRing ι R ⧸ P) F).comp (Ideal.Quotient.mk P)
  have hφ : ∀ a, φ a = 0 ↔ a ∈ P := by
    intro a
    simp only [φ, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hne : ∀ a, a ∉ W → φ a ≠ 0 := fun a ha h0 => ha (hPW ((hφ a).1 h0))
  have key : ∀ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b → IsMultiHomog g b → g ∉ W →
      ∀ hz : φ f / φ g ∈ homLocRing P W, IsUnit (⟨_, hz⟩ : homLocRing P W) ↔ f ∉ W := by
    intro b f g hf hg hgW hz
    constructor
    · rintro ⟨u, hu⟩ hfW
      obtain ⟨b', f', g', -, -, hg'W, hw⟩ :=
        (h R K ι P W hW hPW ((u⁻¹ : (homLocRing P W)ˣ) : homLocRing P W)).1 (u⁻¹ : (homLocRing P W)ˣ).1.2
      have h1 : (φ f / φ g) * (φ f' / φ g') = 1 := by
        have e := congrArg Subtype.val u.mul_inv
        rw [Subring.coe_mul, hu, Subring.coe_one] at e
        rw [← e]
        congr 1
        exact hw.symm
      have h2 : φ (f * f' - g * g') = 0 := by
        rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hne g hgW) (hne g' hg'W))] at h1
        rw [map_sub, map_mul, map_mul, h1, sub_self]
      have h3 : f * f' - g * g' ∈ W := hPW ((hφ _).1 h2)
      have h4 : g * g' ∈ W := by
        have := W.sub_mem (W.mul_mem_right f' hfW) h3
        simpa using this
      rcases hW.mem_or_mem h4 with h5 | h5
      exacts [hgW h5, hg'W h5]
    · intro hfW
      have hgf : φ g / φ f ∈ homLocRing P W := Subring.subset_closure ⟨b, g, f, hg, hf, hfW, rfl⟩
      refine IsUnit.of_mul_eq_one ⟨_, hgf⟩ ?_
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_one]
      rw [div_mul_div_comm, mul_comm (φ f) (φ g)]
      exact div_self (mul_ne_zero (hne g hgW) (hne f hfW))
  refine ⟨?_, key⟩
  have hnu : ∀ z : homLocRing P W, ¬ IsUnit z → ∃ (b : K → ℕ) (f g : MRing ι R),
      IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧ f ∈ W ∧ (z : F) = φ f / φ g := by
    intro z hz
    obtain ⟨b, f, g, hf, hg, hgW, hzfg⟩ := (h R K ι P W hW hPW z).1 z.2
    refine ⟨b, f, g, hf, hg, hgW, ?_, hzfg⟩
    by_contra hfW
    have hmem : φ f / φ g ∈ homLocRing P W := hzfg ▸ z.2
    have e : z = ⟨_, hmem⟩ := Subtype.ext hzfg
    exact hz (e ▸ (key b f g hf hg hgW hmem).2 hfW)
  refine IsLocalRing.of_nonunits_add ?_
  intro x y hx hy
  obtain ⟨b₁, f₁, g₁, hf₁, hg₁, hg₁W, hf₁W, hx'⟩ := hnu x hx
  obtain ⟨b₂, f₂, g₂, hf₂, hg₂, hg₂W, hf₂W, hy'⟩ := hnu y hy
  have hnum : IsMultiHomog (f₁ * g₂ + f₂ * g₁) (b₁ + b₂) :=
    IsWeightedHomogeneous.add (IsWeightedHomogeneous.mul hf₁ hg₂)
      (by rw [add_comm]; exact IsWeightedHomogeneous.mul hf₂ hg₁)
  have hden : IsMultiHomog (g₁ * g₂) (b₁ + b₂) := IsWeightedHomogeneous.mul hg₁ hg₂
  have hdenW : g₁ * g₂ ∉ W := fun h5 => (hW.mem_or_mem h5).elim hg₁W hg₂W
  have hsum : ((x + y : homLocRing P W) : F) = φ (f₁ * g₂ + f₂ * g₁) / φ (g₁ * g₂) := by
    rw [Subring.coe_add, hx', hy', div_add_div _ _ (hne g₁ hg₁W) (hne g₂ hg₂W), map_add (f := _), map_mul, map_mul,
      map_mul, mul_comm (φ g₁) (φ f₂)]
  have hmem : φ (f₁ * g₂ + f₂ * g₁) / φ (g₁ * g₂) ∈ homLocRing P W := hsum ▸ (x + y).2
  have e : x + y = ⟨_, hmem⟩ := Subtype.ext hsum
  rw [mem_nonunits_iff, e, key (b₁ + b₂) _ _ hnum hden hdenW hmem, not_not]
  exact W.add_mem (W.mul_mem_right _ hf₁W) (W.mul_mem_right _ hf₂W)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {A : Type*} [CommRing A] (L : Type*) [Field L] [Algebra A L]

def blowUpColon (I : Ideal A) : Submodule A L :=
  ⨆ n : ℕ, (Submodule.map (Algebra.linearMap A L) I) ^ n / (Submodule.map (Algebra.linearMap A L) I) ^ n

end Objects

section Lemmas

def BlowUpOverLocInChart.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (J : Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], IsMultiHomogIdeal P → W.IsPrime → P ≤ W → IsRelevant W →
    ∀ (N : K → ℕ) (u : J → MRing ι R), (∀ j, IsMultiHomog (u j) N) → ∀ j, u j ∉ P →
      blowUpOverLoc P W u ≤ Subring.closure ((homLocRing P W : Set (FractionRing (MRing ι R ⧸ P))) ∪
        Set.range fun k =>
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u k)) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u j)))

def ChartsInColon.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (L : Type u) [Field L] [Algebra A L] (J : Type) [Fintype J] (a : J → A) (f : L),
    (∀ j, algebraMap A L (a j) ≠ 0 →
      f ∈ Algebra.adjoin A (Set.range fun k => algebraMap A L (a k) / algebraMap A L (a j))) →
    f ∈ blowUpColon L (Ideal.span (Set.range a))

def BlowUpColonFinite.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (L : Type u) [Field L]
    [Algebra A L], Function.Injective (algebraMap A L) → ringKrullDim A = 1 →
    ∀ I : Ideal A, I ≠ ⊥ → (blowUpColon L I).FG

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
