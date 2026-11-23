module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Formalism.HermitianCurvature.FrameExists2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle134
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle138
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle051
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle140
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle118
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle141
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle055
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxMaps
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle024
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle018
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh


open Matrix in
theorem _root_.GlobalTheory.WigSh.exists_wigMap_chain_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : _root_.Formalism.FourierDecayAlt.Q.Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), _root_.Formalism.QuantumDeterminants.inWb (n + 1) r z → 0 < _root_.Formalism.QuantumDeterminants.Tz (n + 1) r z → _root_.Formalism.FourierDecayAlt.Q.IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → _root_.Formalism.FourierDecayAlt.Q.IsFrameOf (n + 1) r [z] B → (∀ j, j > l → L j < L l - (n₀ : ℤ)) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : _root_.Formalism.FourierDecayAlt.Q.Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), _root_.Formalism.FourierDecayAlt.Q.IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - (n₀ : ℝ))) ∧ _root_.GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ _root_.Formalism.FourierDecayAlt.Qr.CapSp (_root_.Formalism.FourierDecayAlt.Qr.subA (_root_.Formalism.FourierDecayAlt.Qr.EB π B)) (_root_.Formalism.FourierDecayAlt.Qr.shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, _root_.GlobalTheory.WigSh.wM (Function.update L l (L l - (j : ℤ))) M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l n₀
  induction n₀ with
  | zero =>
    intro hz hT hType hL hrel hB hgap
    refine ⟨V, inferInstance, inferInstance, inferInstance, π, fun _ => ContinuousLinearMap.id ℂ V,
      ?_, ?_, ?_⟩
    · simpa using hType
    · exact _root_.GlobalTheory.WigSh.wigMap_zero_of_contraction V V (n + 1) r z π π
        (ContinuousLinearMap.id ℂ V) (fun v => le_rfl) (fun h _ v => rfl)
    · intro M v _
      simp only [Finset.prod_range_zero, Complex.ofReal_one, one_smul,
        ContinuousLinearMap.id_apply]
      refine ext_inner_left ℂ fun w => ?_
      rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.id_apply]
  | succ m ih =>
    intro hz hT hType hL hrel hB hgap
    have hm : (0 : ℤ) ≤ m := Nat.cast_nonneg m
    have hgap' : ∀ j, j > l → L j < L l - (m : ℤ) := fun j hj => by
      have := hgap j hj
      push_cast at this
      linarith
    obtain ⟨V₁, i₁, i₂, i₃, π₁, A₁, hType₁, hA₁, hprod₁⟩ := ih hz hT hType hL hrel hB hgap'
    set L₁ := Function.update L l (L l - m) with hL₁def
    set u₁ := Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - m) with hu₁def
    have hL₁ : StrictAnti L₁ := by
      intro a b hab
      by_cases ha : a = l
      · subst ha
        have hb : b ≠ a := ne_of_gt hab
        rw [hL₁def, Function.update_self, Function.update_of_ne hb]
        have := hgap b hab
        push_cast at this
        linarith
      · by_cases hb : b = l
        · subst hb
          rw [hL₁def, Function.update_self, Function.update_of_ne ha]
          have := hL hab
          linarith
        · rw [hL₁def, Function.update_of_ne ha, Function.update_of_ne hb]
          exact hL hab
    have hne₁ : ∀ j : Fin (n + 1), L₁ j ≠ L₁ l - 1 := by
      intro j
      by_cases hj : j = l
      · subst hj
        omega
      · rw [hL₁def, Function.update_self, Function.update_of_ne hj]
        rcases lt_or_gt_of_ne hj with h | h
        · have := hL h
          omega
        · have := hgap j h
          push_cast at this
          omega
    have hrel₁ : ∀ j : Fin (n + 1),
        (u₁ ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L₁ j : ℂ) := by
      intro j
      by_cases hj : j = l
      · subst hj
        rw [hu₁def, hL₁def, Function.update_self, Function.update_self]
        have := hrel j
        push_cast at this ⊢
        linear_combination this
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [hu₁def, hL₁def, Function.update_of_ne hj, Function.update_of_ne hj']
        exact hrel j
    obtain ⟨V₂, j₁, j₂, j₃, π₂, A₂, hType₂, hA₂, hprod₂⟩ :=
      _root_.GlobalTheory.WignerStepLower.wigner_step_lowering V₁ n r z π₁ u₁ β L₁ B l hz hT hType₁ hL₁ hrel₁ hB hne₁
    refine ⟨V₂, j₁, j₂, j₃, π₂, fun ω => (A₁ ω).comp (A₂ ω), ?_,
      _root_.GlobalTheory.WigSh.wigMap_comp V V₁ V₂ (n + 1) r z π π₁ π₂ m 1 A₁ A₂ hA₁ hA₂, ?_⟩
    · have key : Function.update u₁ ((l : ℕ) + 1) (u₁ ((l : ℕ) + 1) - 1) =
          Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - ((m + 1 : ℕ) : ℝ)) := by
        rw [hu₁def, Function.update_idem, Function.update_self]
        congr 1
        push_cast
        ring
      rw [← key]
      exact hType₂
    · intro M v hv
      have hadj := _root_.GlobalTheory.adjoint_mem_CapSp_subA V V₁ n r z π π₁ B
        (A₁ (B (Fin.last n))) (_root_.Formalism.FourierDecayAlt.Qr.shf β M) ⟨hType.2.1, hType.2.2.1⟩ ⟨hType₁.2.1, hType₁.2.2.1⟩
        hType.2.2.2.1 hType₁.2.2.2.1 hB
        (fun h hh hfix => by
          have := hA₁.2.1 h hh (B (Fin.last n))
          rwa [hfix] at this) v hv
      simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
      rw [hprod₂ M _ hadj, map_smul, hprod₁ M v hv, Finset.prod_range_succ, Complex.ofReal_mul,
        mul_comm, mul_smul]

end GlobalTheory.WigSh
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

theorem _root_.GlobalTheory.T.wigner_step_raising_unitary_complement : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l + 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wP L M l : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.WigSh.wigner_step_raise | exact GlobalTheory.WigSh.wigner_step_raise | (intros; apply GlobalTheory.WigSh.wigner_step_raise <;> assumption)
end

section

namespace GlobalTheory.HatNF.SpanMul

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem gen_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {b : A} (hb : b ∈ bmon d) (H : List A)
    (hl : H.length = n) (hT : ∀ h ∈ H, h ∈ T) :
    b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod ∈ nfSpan d T i j n :=
  Submodule.subset_span ⟨b, hb, H, hl, hT, rfl⟩

theorem map_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) (f : A →ₗ[ℂ] A) (S : Submodule ℂ A)
    (h : ∀ b ∈ bmon d, ∀ H : List A, H.length = n → (∀ h ∈ H, h ∈ T) →
      f (b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod) ∈ S) :
    ∀ x ∈ nfSpan d T i j n, f x ∈ S := by
  have : nfSpan d T i j n ≤ S.comap f := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨b, hb, H, hl, hT, rfl⟩
    exact h b hb H hl hT
  exact fun x hx => this hx

theorem bdd_mul (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {b : A} (hb : b ∈ bmon d) :
    ∀ x ∈ nfSpan d T i j n, b * x ∈ nfSpan d T i j n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ b) _ ?_
  intro b' hb' H hl hT
  have := gen_mem d T i j n ((bmon d).mul_mem hb hb') H hl hT
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem di_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di) (T : Set A) (i j n : ℕ) :
    ∀ x ∈ nfSpan d T i j n, d.L.Di * x ∈ nfSpan d T (i + 1) j n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ d.L.Di) _ ?_
  intro b hb H hl hT
  have := gen_mem d T (i + 1) j n hb H hl hT
  rw [pow_succ', ← mul_assoc b, (hD b hb).eq] at this
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem gi_mul (d : Q.NFData P A) (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L))
    (hDG : Commute d.L.Di (TL.gI d.L)) (T : Set A) (i j n : ℕ) :
    ∀ x ∈ nfSpan d T i j n, TL.gI d.L * x ∈ nfSpan d T i (j + 1) n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ (TL.gI d.L)) _ ?_
  intro b hb H hl hT
  have := gen_mem d T i (j + 1) n hb H hl hT
  rw [pow_succ', ← mul_assoc (b * _), ((hG b hb).mul_left (hDG.pow_left i)).eq] at this
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem di_pow_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di) (T : Set A) (i j n k : ℕ) :
    ∀ x ∈ nfSpan d T i j n, d.L.Di ^ k * x ∈ nfSpan d T (i + k) j n := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact di_mul d hD T _ j n _ ih

theorem gi_pow_mul (d : Q.NFData P A) (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L))
    (hDG : Commute d.L.Di (TL.gI d.L)) (T : Set A) (i j n k : ℕ) :
    ∀ x ∈ nfSpan d T i j n, TL.gI d.L ^ k * x ∈ nfSpan d T i (j + k) n := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact gi_mul d hG hDG T i _ n _ ih

theorem one_letter_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di)
    (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L)) (hDG : Commute d.L.Di (TL.gI d.L)) (T T' : Set A)
    (i₀ j₀ n i j : ℕ) (u : A) (hu : ∀ X ∈ T', X * u ∈ nfSpan d T i₀ j₀ n) :
    ∀ x ∈ nfSpan d T' i j 1, x * u ∈ nfSpan d T (i₀ + i) (j₀ + j) n := by
  refine map_mem d T' i j 1 (LinearMap.mulRight ℂ u) _ ?_
  intro b hb H hl hT
  obtain ⟨X, rfl⟩ := List.length_eq_one_iff.1 hl
  have := bdd_mul d T _ _ n hb _ (di_pow_mul d hD T _ _ n i _
    (gi_pow_mul d hG hDG T _ _ n j _ (hu X (hT X (by simp)))))
  simpa only [LinearMap.mulRight_apply, mul_assoc, List.prod_cons, List.prod_nil, mul_one] using this

theorem mul_prod (d : Q.NFData P A) (T : Set A) (i j m : ℕ) (H : List A) (hT : ∀ h ∈ H, h ∈ T) :
    ∀ x ∈ nfSpan d T i j m, x * H.prod ∈ nfSpan d T i j (H.length + m) := by
  refine map_mem d T i j m (LinearMap.mulRight ℂ H.prod) _ ?_
  intro b hb H' hl hT'
  have := gen_mem d T i j (H.length + m) hb (H' ++ H) (by simp [hl, add_comm]) (by
    intro h hh
    rcases List.mem_append.1 hh with h1 | h1
    · exact hT' h h1
    · exact hT h h1)
  simpa only [LinearMap.mulRight_apply, mul_assoc, List.prod_append] using this

theorem span_mul : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ T : Set A, (∀ i j n, ∀ x ∈ nfSpan d T i j n, (∀ b ∈ bmon d, b * x ∈ nfSpan d T i j n) ∧ d.L.Di * x ∈ nfSpan d T (i + 1) j n ∧ TL.gI d.L * x ∈ nfSpan d T i (j + 1) n) ∧ ∀ a : ℕ, (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ i j n, ∀ X ∈ hats d.L, ∀ x ∈ nfSpan d T i j n, X * x ∈ nfSpan d T i (j + a) (n + 1) := by
  intro P A _ _ _ _ d hd T
  have h1 := GlobalTheory.T.hatLetter_mul_boundedFactor_mem_normalFormSpan P A d hd
  obtain ⟨h2, h3, hDG⟩ := GlobalTheory.T.hatLetters_pass_Di_gI_boundedFactors P A d hd
  have hD : ∀ b ∈ bmon d, Commute b d.L.Di := fun b hb => (h3 b hb).2.1
  have hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L) := fun b hb => (h3 b hb).2.2.1
  refine ⟨fun i j n x hx => ⟨fun b hb => bdd_mul d T i j n hb x hx, di_mul d hD T i j n x hx,
    gi_mul d hG hDG T i j n x hx⟩, ?_⟩
  intro a ha i j n X hX
  refine map_mem d T i j n (LinearMap.mulLeft ℂ X) _ ?_
  intro b hb H hl hT
  have e1 : ∀ k, X * b * d.L.Di ^ k ∈ nfSpan d (hats d.L) k 0 1 := by
    intro k
    induction k with
    | zero => simpa using h1 X hX b hb
    | succ k ih =>
      have := one_letter_mul d hD hG hDG _ _ 1 0 1 k 0 _ (fun Y hY => (h2 Y hY).1) _ ih
      rw [pow_succ, ← mul_assoc, add_comm k 1]
      exact this
  have e2 : ∀ k, X * b * d.L.Di ^ i * TL.gI d.L ^ k ∈ nfSpan d (hats d.L) i k 1 := by
    intro k
    induction k with
    | zero => simpa using e1 i
    | succ k ih =>
      have := one_letter_mul d hD hG hDG _ _ 0 1 1 i k _ (fun Y hY => (h2 Y hY).2) _ ih
      rw [zero_add] at this
      rw [pow_succ, ← mul_assoc, add_comm k 1]
      exact this
  have e3 := one_letter_mul d hD hG hDG T _ 0 a (H.length + 1) i j H.prod
    (fun Y hY => mul_prod d T 0 a 1 H hT Y (ha Y hY)) _ (e2 j)
  rw [zero_add, hl, add_comm a j] at e3
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using e3

end GlobalTheory.HatNF.SpanMul
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem vec_bigPt_eq_radial : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), (∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ x ∈ Q.DomR P.k P.r p.T.base.z p.T.base.z', gR P p.T.base x.1 x.2 = TBB.Gp p (TBB.bigPt P.r c) ∧ dR P p.T.base x.1 x.2 = ‖∏ l, c l‖ ∧ ∃ lam : ℝ, 0 < lam ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'), Top.IsRadOf P p.T.base Φ H → ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ = lam * nv Φ x := by
  intro Wp Wq _ _ _ _ _ _ P p c hc hG
  have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
    Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
  have hc' : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hc _
  have hz := Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ p.T.base.z_mem p.T.base.z'_mem p.T.base.sec hζ
  have hx : ((fun a : Fin P.r => c a.castSucc), NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r))) ∈
      Q.DomR P.k P.r p.T.base.z p.T.base.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR p.T.base.z_mem p.T.base.z'_mem p.T.base.sec
      (q := ((fun a : Fin P.r => c a.castSucc), c (Fin.last P.r))) ⟨hc', hζ⟩
  refine ⟨_, hx, ?_, ?_, ?_⟩
  · show Complex.normSq (∏ a : Fin P.r, c a.castSucc) *
        (Complex.normSq (Q.zetaL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r)
          (NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)))) - Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') =
        D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
    unfold D.ptG
    rw [hz, Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc c, Complex.normSq_mul]
    ring
  · show ‖(∏ a : Fin P.r, c a.castSucc) * Q.zetaL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r)
          (NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)))‖ = _
    rw [hz, Fin.prod_univ_castSucc c]
  · have hpos : 0 < ∏ a : Fin P.r,
        (if a.val < (Fin.last P.r).val then ‖c a.castSucc‖ ^ (Mdim P.k P.r a - 1) else 1 : ℝ) := by
      refine Finset.prod_pos fun a _ => ?_
      split_ifs
      · exact pow_pos (norm_pos_iff.2 (hc' a)) _
      · exact one_pos
    refine ⟨_, inv_pos.2 hpos, fun H Φ hΦ => ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p H c hc hG]
    unfold nv
    rw [hΦ _ hx]
    unfold Q.resG
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hpos.le,
      inv_mul_cancel_left₀ hpos.ne']
    have e : Q.wCell P.k P.r (Fin.last P.r) (fun a : Fin P.r => c a.castSucc) *
        NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)) =
        bigCell P.k P.r (fun a : Fin P.r => c a.castSucc) (p.T.base.μsec (c (Fin.last P.r))) := by
      unfold NF.muZ
      rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization _ _ _ _).1]
    rw [e]

end GlobalTheory.HatNF
end

section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

theorem jf_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (φ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.JF Bs (mulG Bs φ f) g = ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • B.JF Bs f g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (mulG Bs φ f) g ∂Bs.μSS =
    ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • ∫ p, JF.xiP Bs p • B.rho Bs p f g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho, mulG, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem cptCoef_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {f : B.Mat k r → (Wq →L[ℂ] Wp)} (hf : KB.CptCoef Bs f) :
    KB.CptCoef Bs (mulG Bs φ f) := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨δ, hδ, hG⟩⟩ := hf
  have hne : ∀ g, mulG Bs φ f g ≠ 0 → f g ≠ 0 := fun g h h0 => h (by simp [mulG, h0])
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat k r => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z'))
  exact ⟨Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hc hs, ⟨R, fun g hg h => hR g hg (hne g h)⟩,
    ⟨δ, hδ, fun g hg h => hG g hg (hne g h)⟩⟩

theorem radial_mulG : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), ∀ (φ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → LE.SmoothLog φ ∧ (KB.CptCoef Bs f → KB.CptCoef Bs (mulG Bs φ f))) ∧ ∀ (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W → Top.IsRadOf P Bs Φ f → Top.IsRadOf P Bs (W 0 Φ) (mulG Bs φ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs φ f
  refine ⟨fun hφ => ⟨hφ.comp Real.contDiff_exp, fun hf => cptCoef_mulG Bs hφ hf⟩, ?_⟩
  intro W Φ hW hΦ x hx
  have hcell := Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx
  have hpos : 0 < gR P Bs x.1 x.2 := by
    have := hcell.1.2.1
    rw [hcell.2.2.2] at this
    exact this
  have hld : LE.ld 0 φ (gR P Bs x.1 x.2) = φ (gR P Bs x.1 x.2) := by
    simp only [LE.ld, iteratedDeriv_zero, Real.exp_log hpos]
  rw [hW 0 Φ x.1 x.2, hΦ x hx]
  simp only [Q.resG]
  rw [jf_mulG, hcell.2.2.2, hld, smul_comm]
  rfl

end

end GlobalTheory.HatNF
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem _root_.GlobalTheory.T.goodPrimeWeightHypotheses_of_depthParameters : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), T.Q.Pins → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → Real.log D.R.k ≤ L.sc.L → ∀ j : ℕ, InR D j →
  GoodPage (numOf D L) j (T.Q.Dw j) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) Tp.nWn Tp.TO 100 L.sc.b L.sc.L := by
  first | exact @GlobalTheory.GoodDepth.goodPage_run | exact GlobalTheory.GoodDepth.goodPage_run | (intros; apply GlobalTheory.GoodDepth.goodPage_run <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem boxTup_of_columns : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxTupSt := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P ϖ hϖ Q hQ F _ _ _ _ v g g' π hg hg' hπ τ hτ hEL n D' A' G' _ _ pD pA pG U' PU _ oD' hx hact
    s s₂ t₀ t p w ζ x σ f h
  have hG := hL.globalFns
  have hk : 1 ≤ g' * g := Nat.mul_pos hg' hg
  have hA : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨bx₁, hbx₁⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F g'
  obtain ⟨bx, hbx⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F (g' * g)
  obtain ⟨p', hp'⟩ := BoxQk.exists_isBoxQk hG T.V n P.D.toPre D'.toPre pD F (g' * g) p
  have hw : ∀ i, (w i).IsGen := fun i => (h i).2.2.1
  obtain ⟨w', hw', hΦ⟩ := BoxPhi.phiRel_box hG T.V n P.D.toPre D'.toPre pD F (g' * g) p' p hp' w hw
  obtain ⟨σ', hσ', -⟩ := (expandsG_bijective_of_dvr hL hL2 hL4 hT T.V D' A' G' U' F (g' * g) hk).2 (bx t)
  let x' : TFK (R := T.V) F ⟶ A'.A := pA.lim.lift (Fan.mk _ x)
  have hx' : ∀ i, x' ≫ pA.pr i = x i := fun i => pA.lim.fac (Fan.mk _ x) ⟨i⟩
  have hπ' : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, _root_.mul_comm, hπ]
  refine ⟨bx₁ s, bx s₂, p', w', ∏ i, ζ i, x', bx t₀, bx t, σ', ⟨?_, ?_, ⟨hw', ?_, ?_⟩, ?_, ?_, ?_, ?_, hσ', ?_⟩, hx'⟩
  · have := NuBox.main T.V ϖ hϖ n P.D D' pD Q hQ F v g' s (bx₁ s) ((hbx₁ _ _).2 rfl) (fun _ => 0) (fun i => (h i).1)
    rw [Finset.sum_const_zero] at this
    exact this
  · exact BoxPull.main hL hL2 hL4 hT T.V n P.D D' pD F (𝓞 E) hx P.oD oD' hact (star π) g g' hg hg' hπ' s s₂ _ _
      (fun i => (h i).2.1) ((hbx₁ _ _).2 rfl) ((hbx _ _).2 rfl)
  · exact Finset.prod_ne_zero_iff.2 fun i _ => (h i).2.2.2.1
  · exact finOrd_box hL hL2 hL4 hT T.V n P.D D' pD F (g' * g) hk p' p hp' w w' hw hw' hΦ ζ (fun i => (h i).2.2.2.2.1)
  · exact ProdTorsion.qkToAk_box hL T.V _ n P.D D' P.A A' C.I.G.G G' pD pA pG U' P.U PU
      (expBijF_of_admissible_base hL hL2 T.V _ hA _ _ _ P.U) (expBijF_of_admissible_base hL hL2 T.V _ hA _ _ _ U') F (g' * g) hk
      p' p hp' x' x hx' (fun i => (h i).2.2.2.2.2.1)
  · intro i
    rw [← Category.assoc, hx']
    exact (h i).2.2.2.2.2.2.1
  · exact hΦ s₂ t₀ _ _ (fun i => (h i).2.2.2.2.2.2.2.1) ((hbx _ _).2 rfl) ((hbx _ _).2 rfl)
  · refine (isSmul_iff _ _ _).2 ?_
    calc
      bx t = bx (fun i => ζ i • t₀ i) :=
        congrArg bx (funext fun i => (isSmul_iff _ _ _).1 (h i).2.2.2.2.2.2.2.2.1)
      _ = (∏ i, ζ i) • bx t₀ := by simpa using bx.map_smul_univ ζ t₀
  · exact GlobalTheory.T.germ_boxProduct_eq_prod_germs hL hL2 hL4 hT E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT C.wPT
      C.chartT C.frameT C.primT τ hτ hEL n D' A' G' pD pA pG U' PU F (g' * g) hk σ t f σ' (bx t)
      (fun i => (h i).2.2.2.2.2.2.2.2.2) ((hbx _ _).2 rfl) hσ'

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.isBes_bessel_integral_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ ξ : Wp, IsBes R z π (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ) := by
  first | exact @GlobalTheory.be_apply_isBes | exact GlobalTheory.be_apply_isBes | (intros; apply GlobalTheory.be_apply_isBes <;> assumption)
end
