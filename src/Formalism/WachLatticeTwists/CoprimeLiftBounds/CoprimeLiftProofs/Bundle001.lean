module

public import Formalism.WachLatticeTwists.CoprimeLiftBounds.FirstSummandRepresentation
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.CupKillAdm
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.LengthMapQuotLe
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Formalism.CharacterColumnKernels.IdempotentNormalForms.ColKer
import Formalism.CharacterColumnKernels.IdempotentNormalForms.ColKerChiOne

@[expose] public section

section

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

section T1
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]

lemma first_summand_action_mem (O : Type*) [CommRing O] [Algebra O A] (r : G →* A) (χ : G →* T'ˣ) (e₁ : A)
    (ε : G →* Oˣ) (g : G) (b : FirstSummandSubmodule O e₁) :
    ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((b : A) * r g⁻¹)) ∈ FirstSummandSubmodule O e₁ := by
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp b.2
  rw [LinearMap.mulLeft_apply] at hx
  show _ ∈ LinearMap.range (LinearMap.mulLeft O e₁)
  rw [LinearMap.mem_range]
  refine ⟨((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (x * r g⁻¹)), ?_⟩
  rw [LinearMap.mulLeft_apply, mul_smul_comm, mul_smul_comm, ← mul_assoc, hx]

def firstSummandRep (O : Type*) [CommRing O] [Algebra O A] (r : G →* A) (χ : G →* T'ˣ) (e₁ : A)
    (ε : G →* Oˣ) : Representation O G (FirstSummandSubmodule O e₁) where
  toFun g :=
    { toFun := fun b => ⟨_, first_summand_action_mem O r χ e₁ ε g b⟩
      map_add' := fun b b' => Subtype.ext (by
        show ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (((b : A) + (b' : A)) * r g⁻¹)) = _ + _
        rw [add_mul, smul_add, smul_add])
      map_smul' := fun c b => Subtype.ext (by
        show ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((c • (b : A)) * r g⁻¹)) =
          c • (((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((b : A) * r g⁻¹)))
        rw [smul_mul_assoc, smul_comm _ c, smul_comm _ c]) }
  map_one' := LinearMap.ext fun b => Subtype.ext (by
    show ((ε 1 : Oˣ) : O) • (((χ 1 : T'ˣ) : T') • ((b : A) * r 1⁻¹)) = (b : A)
    simp)
  map_mul' g h := LinearMap.ext fun b => Subtype.ext (by
    show ((ε (g * h) : Oˣ) : O) • (((χ (g * h) : T'ˣ) : T') • ((b : A) * r (g * h)⁻¹)) =
      ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') •
        ((((ε h : Oˣ) : O) • (((χ h : T'ˣ) : T') • ((b : A) * r h⁻¹))) * r g⁻¹))
    rw [map_mul, map_mul, mul_inv_rev, map_mul, Units.val_mul, Units.val_mul, smul_mul_assoc,
      smul_mul_assoc, mul_smul, mul_smul, mul_assoc,
      smul_comm ((χ g : T'ˣ) : T') ((ε h : Oˣ) : O)])

end T1

theorem t1 : FirstSummandRepresentation := by
  intro O A T' G _ _ _ _ _ _ r χ e₁ ε
  exact ⟨firstSummandRep O r χ e₁ ε, fun g b => rfl⟩

end Formalism.RepresentationBoundsCohomology.BR
end
end

section

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG Formalism.NG.ColumnGeneratorDecomposition Formalism.NG.ColKerChi

theorem rel : StatRel := by
  intro A T' G _ _ _ _ M _ _ r χ E e₁ δ ι _ D j Kc k0 φ l
  have hR : ∀ z ∈ colRelJ r χ E e₁ δ D j Kc k0, φ (Submodule.Quotient.mk z) = 0 := fun z hz => by
    rw [(Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]
  have hsing : ∀ (x : A) (v : A × (Fin (j l) → A) × A),
      x • Pi.single (M := fun l => A × (Fin (j l) → A) × A) l v = Pi.single l (x • v) := by
    intro x v
    funext k
    by_cases h : k = l
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have hsing2 : ∀ (x : A) (a : Fin (j l)) (t : A),
      x • (Pi.single a t : Fin (j l) → A) = Pi.single a (x * t) := by
    intro x a t
    funext k
    by_cases h : k = a
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have hgen : ∀ (x c : A) (s : Fin (j l) → A) (c₀ : A),
      x • (colGenJ (0 : Ymod r χ E) l c s c₀ : ColFreeJ A r χ E ι j) =
        colGenJ 0 l (x * c) (x • s) (x * c₀) := by
    intro x c s c₀
    show (x • (0 : Ymod r χ E), x • Pi.single (M := fun l => A × (Fin (j l) → A) × A) l (c, s, c₀)) =
      ((0 : Ymod r χ E), Pi.single (M := fun l => A × (Fin (j l) → A) × A) l (x * c, x • s, x * c₀))
    rw [smul_zero, hsing]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_smul]
    show φ (E • Submodule.Quotient.mk ((colGenJ (0 : Ymod r χ E) l 1 0 0 : ColFreeJ A r χ E ι j))) = 0
    rw [← Submodule.Quotient.mk_smul, hgen, mul_one, smul_zero, mul_zero]
    exact hR _ (Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))))
  · intro a
    have hz := hR (colGenJ (0 : Ymod r χ E) l 0 (Pi.single a (1 - e₁)) 0)
      (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨l, a, rfl⟩))))
    have e : (colGenJ (0 : Ymod r χ E) l 0 (Pi.single a (1 - e₁)) 0 : ColFreeJ A r χ E ι j) =
        (1 - e₁) • colGenJ (0 : Ymod r χ E) l 0 (Pi.single a 1) 0 := by
      rw [hgen, mul_zero, hsing2, mul_one]
    rw [e, Submodule.Quotient.mk_smul, map_smul, sub_smul, one_smul, sub_eq_zero] at hz
    exact hz.symm
  · have hz := hR (colGenJ (0 : Ymod r χ E) l 0 0 (algebraMap T' A δ - E))
      (Submodule.subset_span (Or.inl (Or.inr ⟨l, rfl⟩)))
    have e : (colGenJ (0 : Ymod r χ E) l 0 0 (algebraMap T' A δ - E) : ColFreeJ A r χ E ι j) =
        (algebraMap T' A δ - E) • (colGenJ (0 : Ymod r χ E) l 0 0 1 : ColFreeJ A r χ E ι j) := by
      rw [hgen, mul_zero, smul_zero, mul_one]
    rw [e, Submodule.Quotient.mk_smul, map_smul, sub_smul, sub_eq_zero] at hz
    exact hz
  · intro g hg
    have hz := hR (colGenJ (⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E) l
        ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) (fun a => -(algebraMap T' A δ * Kc l a g))
        (-(algebraMap T' A δ * k0 l g)))
      (Submodule.subset_span (Or.inr ⟨l, g, hg, rfl⟩))
    have key : (colGenJ (⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E) l
        ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) (fun a => -(algebraMap T' A δ * Kc l a g))
        (-(algebraMap T' A δ * k0 l g)) : ColFreeJ A r χ E ι j) =
        ((⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E), 0) +
          (((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) • (colGenJ (0 : Ymod r χ E) l 1 0 0 : ColFreeJ A r χ E ι j) +
          (∑ a, (-(algebraMap T' A δ * Kc l a g)) • colGenJ (0 : Ymod r χ E) l 0 (Pi.single a 1) 0 +
          (-(algebraMap T' A δ * k0 l g)) • (colGenJ (0 : Ymod r χ E) l 0 0 1 : ColFreeJ A r χ E ι j))) := by
      simp only [hgen, hsing2, mul_one, mul_zero, smul_zero]
      refine Prod.ext ?_ ?_
      · simp [colGenJ, Prod.fst_sum]
      · funext k
        by_cases hk : k = l
        · subst hk
          simp [colGenJ, Prod.snd_sum, Finset.sum_apply, funext_iff, Pi.single_apply]
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · simp [Prod.fst_sum]
          · funext a
            simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
          · simp [Prod.snd_sum]
        · simp [colGenJ, Prod.snd_sum, Finset.sum_apply, Pi.single_eq_of_ne hk]
    rw [key] at hz

    simp only [← Submodule.mkQ_apply, map_add (f := _), map_smul, map_sum] at hz
    have hz' : φ (yGen r χ E e₁ δ D j Kc k0 g) + ((uElt r χ g - 1) • φ (nuGen r χ E e₁ δ D j Kc k0 l) +
        (∑ a, (-(algebraMap T' A δ * Kc l a g)) • φ (sigGen r χ E e₁ δ D j Kc k0 l a) +
        (-(algebraMap T' A δ * k0 l g)) • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l))) = 0 := hz
    simp only [sub_smul, one_smul, neg_smul, mul_smul, Finset.sum_neg_distrib,
      ← Finset.smul_sum] at hz'
    rw [smul_add, ← sub_eq_zero, ← hz']
    abel

end Formalism.RepresentationBoundsCohomology.BR
end
end

section

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

lemma key_mul {O A T' G : Type*} [CommRing O] [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A]
    [Group G] (r : G →* A) (χ : G →* T'ˣ) (g : G) (c : O) (b x : A) :
    (c • (((χ g : T'ˣ) : T') • (b * r g⁻¹))) * (uElt r χ g * x) = c • (b * x) := by
  have hr : r g⁻¹ * r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  simp only [uElt, smul_mul_assoc, mul_smul_comm, smul_smul, Units.mul_inv, one_smul]
  rw [mul_assoc, ← mul_assoc (r g⁻¹), hr, one_mul]
  rw [smul_comm (((χ g)⁻¹ : T'ˣ) : T') c, smul_smul, Units.inv_mul, one_smul]

theorem rowCup : StatRowCup := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 Dw ε T₁ T₂ _ _ _ _ ρ₁ ρ₂
    inc π γ lam C₁ CN2 CN CA CP hinc hπ hγ hc2 hc1 hCP hH2 φ a ha hCa
  let Y := Ymod r χ E
  let ρY : Representation O Dw Y := resRep (uRep O (M := Y) r χ) Dw
  let ρA : Representation O Dw A := resRep (uRep O (M := A) r χ) Dw
  let ρM : Representation O Dw M := resRep (uRep O (M := M) r χ) Dw
  let β : T₁ →ₗ[O] Y →ₗ[O] Y := LinearMap.mk₂ O (fun b y => inc b • y)
    (fun b b' y => by rw [map_add (f := _), add_smul]) (fun c b y => by rw [map_smul, smul_assoc])
    (fun b y y' => smul_add _ _ _) (fun c b y => smul_comm _ _ _)
  let β' : T₁ →ₗ[O] A →ₗ[O] A := LinearMap.mk₂ O (fun b y => inc b • y)
    (fun b b' y => by rw [map_add (f := _), add_smul]) (fun c b y => by rw [map_smul, smul_assoc])
    (fun b y y' => smul_add _ _ _) (fun c b y => smul_comm _ _ _)
  let jm : Y →ₗ[O] A := Y.subtype.restrictScalars O
  let φ' : Y →ₗ[O] M := psiY r χ E e₁ δ D j Kc k0 φ
  have hφ' : ∀ (x : A) (y : Y), φ' (x • y) = x • φ' y := fun x y => map_smul
      (φ ∘ₗ (Submodule.mkQ _) ∘ₗ (LinearMap.inl A (Ymod r χ E) _)) x y
  exact cupKillAdm O Dw T₁ Y A Y A T₂ M (KO O) ρ₁ ρY ρA (twRep ε Y) (twRep ε A) ρ₂ ρM
    (twRep ε (KO O)) β β' γ jm jm π φ' (lam ∘ₗ φ') CN2 CN CA CP
    (fun g b y => Subtype.ext (by
      show inc (ρ₁ g b) * (uElt r χ (g : G) * (y : A)) = ((ε g : Oˣ) : O) • (inc b * (y : A))
      rw [hinc, key_mul]))
    (fun g b y => by
      show inc (ρ₁ g b) * (uElt r χ (g : G) * y) = ((ε g : Oˣ) : O) • (inc b * y)
      rw [hinc, key_mul])
    (fun g y => rfl) (fun g y => rfl) hπ (fun g y => hφ' _ y)
    (fun g y => by
      show (lam ∘ₗ φ') (((ε g : Oˣ) : O) • y) = ((ε g : Oˣ) : O) • (lam ∘ₗ φ') y
      rw [map_smul])
    (fun m n => rfl)
    (fun m n => by
      show γ (π m) (φ' n) = lam (φ' (inc m • n))
      rw [hγ, hφ'])
    (fun f hf => hCP _ f hf) hH2 a (fun h => yY r χ E (h : G)) E ha
    (fun g h => Subtype.ext (ycoc_mul r χ E (g : G) (h : G)))
    (fun g => by
      show ycoc r χ E (g : G) = uElt r χ (g : G) * E - E
      unfold ycoc uElt
      rw [sub_mul, one_mul])
    (hc2 a hCa) (hc1 a hCa)

end Formalism.RepresentationBoundsCohomology.BR
end
end
