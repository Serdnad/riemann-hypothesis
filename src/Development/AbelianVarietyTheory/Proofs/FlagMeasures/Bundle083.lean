module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesGoodAlmostAllPlaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle077
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftRowMiddleSpaceIntegralPoint
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle056
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSymplecticBasisLocalExtension
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.Basic.Real.Basic
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle078
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem basis_of_span_mod_uniformiser {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ}
    (L₁ : Submodule O (Fin n → K)) (hfg : L₁.FG)
    (hspan : Submodule.span K (L₁ : Set (Fin n → K)) = ⊤)
    (C : Fin n → Fin n → K) (hC : ∀ j, C j ∈ L₁) (g : O)
    (hg : IsLocalRing.maximalIdeal O = Ideal.span {g})
    (hmod : ∀ x ∈ L₁, ∃ s ∈ Submodule.span O (Set.range C), ∃ z ∈ L₁, x = s + (g : K) • z) :
    ∃ fr : GL (Fin n) K, (fr : Matrix (Fin n) (Fin n) K) = Matrix.of (fun a j => C j a) ∧
      ∀ x : Fin n → K, x ∈ L₁ ↔ ∀ a, ((fr⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x a ∈ O := by
  classical
  set M : Matrix (Fin n) (Fin n) K := Matrix.of (fun a j => C j a) with hM
  set N : Submodule O (Fin n → K) := Submodule.span O (Set.range C) with hN
  have hsm : ∀ (c : O) (y : Fin n → K), c • y = (c : K) • y := fun c y => rfl
  have hNL : N ≤ L₁ := Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hC j)
  have hLN : L₁ ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O) hfg ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro x hx
      obtain ⟨s, hs, z, hz, rfl⟩ := hmod x hx
      refine Submodule.add_mem_sup hs ?_
      rw [← hsm]
      exact Submodule.smul_mem_smul (by rw [hg]; exact Ideal.mem_span_singleton_self g) hz
  have hCspan : Submodule.span K (Set.range C) = ⊤ := by
    rw [eq_top_iff, ← hspan, ← Submodule.span_span_of_tower O K (Set.range C)]
    exact Submodule.span_mono (fun x hx => hLN hx)
  have hMT : M.col = C := by ext j a; rfl
  have hsurj : Function.Surjective M.mulVec := by
    have h := Matrix.range_mulVecLin M
    rw [hMT, hCspan, LinearMap.range_eq_top] at h
    exact h
  have hunit : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  have hMv : ∀ w : Fin n → K, M *ᵥ w = ∑ j, w j • C j := by
    intro w; ext a
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinvM : ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M = 1 := hunit.unit.inv_mul
  have hMinv : M * ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := hunit.unit.mul_inv
  refine ⟨hunit.unit, rfl, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp (hLN hx)
    have hx' : x = M *ᵥ (fun j => (c j : K)) := by
      rw [hMv, ← hc]; simp only [hsm]
    intro a
    rw [hx', Matrix.mulVec_mulVec, hinvM, Matrix.one_mulVec]
    exact (c a).2
  · apply hNL
    set w := ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x with hw
    have hx' : x = M *ᵥ w := by rw [hw, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
    rw [hx', hMv]
    refine (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨fun j => ⟨w j, hx j⟩, ?_⟩
    simp only [hsm]

theorem first_components_basis :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (S : Set (Fin n → E ⊗[F] v.adicCompletion F)), (∀ j, c j ∈ loc v L) → (∀ x ∈ S, ∀ a, (sp (x a)).1 = 0) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range c ∪ S) y) → ∃ fr : GL (Fin n) (v.adicCompletion F), (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1) ∧ ∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x a ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ cm n J _ _ v sp _ hsp1 hint g hg L hL c S hc hS hmod
  classical
  let πv : (Fin n → E ⊗[F] v.adicCompletion F) → (Fin n → v.adicCompletion F) := fun y a => (sp (y a)).1
  let ι : (Fin n → E) → (Fin n → E ⊗[F] v.adicCompletion F) := fun l i => l i ⊗ₜ[F] (1 : v.adicCompletion F)
  have hfstO : ∀ r : intV E v, (sp (r : E ⊗[F] v.adicCompletion F)).1 ∈ v.adicCompletionIntegers F :=
    fun r => ((hint r).mp r.2).1
  have hπsmul : ∀ (r : intV E v) (y : Fin n → E ⊗[F] v.adicCompletion F),
      πv (r • y) = (⟨_, hfstO r⟩ : v.adicCompletionIntegers F) • πv y := by
    intro r y; funext a
    change (sp ((r : E ⊗[F] v.adicCompletion F) * y a)).1 = (sp (r : E ⊗[F] v.adicCompletion F)).1 * (sp (y a)).1
    rw [map_mul, Prod.fst_mul]
  have hproj : ∀ (T : Set (Fin n → E ⊗[F] v.adicCompletion F)) (y), y ∈ Submodule.span (intV E v) T →
      πv y ∈ Submodule.span (v.adicCompletionIntegers F) (πv '' T) := by
    intro T y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have h0 : πv 0 = 0 := by funext a; simp [πv]
      rw [h0]; exact zero_mem _
    | add x y _ _ hx hy =>
      have h0 : πv (x + y) = πv x + πv y := by funext a; simp [πv]
      rw [h0]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [hπsmul]; exact Submodule.smul_mem _ _ hx
  have hιπ_add : ∀ x y : Fin n → E, πv (ι (x + y)) = πv (ι x) + πv (ι y) := by
    intro x y; funext a; simp [πv, ι, TensorProduct.add_tmul]
  have hιπ_zero : πv (ι 0) = 0 := by funext a; simp [πv, ι]
  have hιπ_smul : ∀ (e : E) (x : Fin n → E), πv (ι (e • x)) = (sp (e ⊗ₜ[F] (1 : v.adicCompletion F))).1 • πv (ι x) := by
    intro e x; funext a
    change (sp ((e * x a) ⊗ₜ[F] (1 : v.adicCompletion F))).1 =
      (sp (e ⊗ₜ[F] (1 : v.adicCompletion F))).1 * (sp (x a ⊗ₜ[F] (1 : v.adicCompletion F))).1
    rw [show (e * x a) ⊗ₜ[F] (1 : v.adicCompletion F) =
      (e ⊗ₜ[F] (1 : v.adicCompletion F)) * (x a ⊗ₜ[F] (1 : v.adicCompletion F)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one], map_mul, Prod.fst_mul]
  have hφO : ∀ e : 𝓞 E, (sp ((e : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 ∈ v.adicCompletionIntegers F := by
    intro e
    have hm : (e : E) ⊗ₜ[F] (1 : v.adicCompletion F) ∈ intV E v := by
      unfold intV tensInt
      exact Subring.subset_closure (Or.inl ⟨⟨(e : E), by unfold intOE; exact RingHom.mem_range.mpr ⟨e, rfl⟩⟩, rfl⟩)
    exact hfstO ⟨_, hm⟩
  have hι : ∀ l ∈ L, ι l ∈ loc v L := fun l hl => Submodule.subset_span ⟨l, hl, rfl⟩
  let L₁ : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F) :=
    { carrier := {x | ∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a}
      add_mem' := by
        rintro x x' ⟨y, hy, hyx⟩ ⟨y', hy', hyx'⟩
        exact ⟨y + y', add_mem hy hy', fun a => by simp [hyx, hyx']⟩
      zero_mem' := ⟨0, zero_mem _, fun a => by simp⟩
      smul_mem' := by
        rintro r x ⟨y, hy, hyx⟩
        have h1r : ((1 : E) ⊗ₜ[F] (r : v.adicCompletion F)) ∈ intV E v :=
          (hint _).mpr ⟨by rw [hsp1]; exact r.2, by rw [hsp1]; exact r.2⟩
        refine ⟨(⟨_, h1r⟩ : intV E v) • y, Submodule.smul_mem _ _ hy, fun a => ?_⟩
        change (sp (((1 : E) ⊗ₜ[F] (r : v.adicCompletion F)) * y a)).1 = (r : v.adicCompletion F) * x a
        rw [map_mul, Prod.fst_mul, hsp1, hyx a] }
  let C : Fin n → Fin n → v.adicCompletion F := fun j => πv (c j)
  have hC : ∀ j, C j ∈ L₁ := fun j => ⟨c j, hc j, fun a => rfl⟩
  have hfg : L₁.FG := by
    obtain ⟨s, hs⟩ := (Module.Finite.iff_fg (N := L)).mp hL.1
    refine ⟨s.image (fun l => πv (ι l)), le_antisymm ?_ ?_⟩
    · rw [Finset.coe_image, Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      exact ⟨ι l, hι l (hs ▸ Submodule.subset_span hl), fun a => rfl⟩
    · rintro x ⟨y, hy, hyx⟩
      have hx : x = πv y := funext fun a => (hyx a).symm
      rw [hx]
      refine (Submodule.span_le.mpr ?_) (hproj (ι '' (L : Set (Fin n → E))) y hy)
      rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      rw [← hs] at hl
      induction hl using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
      | zero => rw [hιπ_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [hιπ_add]; exact add_mem hx hy
      | smul e x _ hx =>
        have h0 : πv (ι (e • x)) = (⟨_, hφO e⟩ : v.adicCompletionIntegers F) • πv (ι x) :=
          hιπ_smul (e : E) x
        rw [h0]; exact Submodule.smul_mem _ _ hx
  have hspan : Submodule.span (v.adicCompletion F) (L₁ : Set (Fin n → v.adicCompletion F)) = ⊤ := by
    have key : ∀ x ∈ Submodule.span E (L : Set (Fin n → E)),
        πv (ι x) ∈ Submodule.span (v.adicCompletion F) (L₁ : Set (Fin n → v.adicCompletion F)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨ι x, hι x hx, fun a => rfl⟩
      | zero => rw [hιπ_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [hιπ_add]; exact add_mem hx hy
      | smul e x _ hx => rw [hιπ_smul]; exact Submodule.smul_mem _ _ hx
    rw [Submodule.eq_top_iff']
    intro x
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ ?_)
    have h := key (fun j => if a = j then (1 : E) else 0) (by rw [hL.2]; trivial)
    convert h using 1
    funext j
    by_cases h' : a = j <;> simp [πv, ι, hsp1, h']
  have hmod' : ∀ x ∈ L₁, ∃ s ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range C), ∃ z ∈ L₁,
      x = s + (((g : ℕ) : v.adicCompletionIntegers F) : v.adicCompletion F) • z := by
    rintro x ⟨y, hy, hyx⟩
    obtain ⟨s, hs, z, hz, hyz⟩ := hmod y hy
    refine ⟨πv s, ?_, πv z, ⟨z, hz, fun a => rfl⟩, ?_⟩
    · refine (Submodule.span_le.mpr ?_) (hproj _ s hs)
      rintro _ ⟨w, hw, rfl⟩
      rcases hw with ⟨j, rfl⟩ | hw
      · exact Submodule.subset_span ⟨j, rfl⟩
      · have h0 : πv w = 0 := funext fun a => hS w hw a
        rw [h0]; exact zero_mem _
    · funext a
      rw [← hyx a, hyz]
      simp [πv]
  obtain ⟨fr, hfr, hmem⟩ :=
    basis_of_span_mod_uniformiser (v.adicCompletionIntegers F) L₁ hfg hspan C hC _ hg hmod'
  exact ⟨fr, hfr, hmem⟩

end GlobalTheory.St.G
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem not_forall_loc_eq_natCast_smul (v : HeightOneSpectrum (𝓞 F))
    (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (hdiag : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a))
    (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsLat L) (hn : 0 < n) :
    ¬ ∀ y ∈ loc v L, ∃ z ∈ loc v L, y = (g : E ⊗[F] v.adicCompletion F) • z := by
  classical
  intro h
  have hs := split_integral_local F E v sp hdiag
  have hint : ∀ r ∈ intV E v, (sp r).1 ∈ v.adicCompletionIntegers F := fun r hr => ((hs r).1 hr).1
  have hOE : ∀ c : 𝓞 E, inclE (F := F) (v.adicCompletion F) (c : E) ∈ intV E v := by
    intro c
    have hc : ((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ PI.SplitIntLoc.tensInt (v.adicCompletion F)
        (PI.SplitIntLoc.intOE E) (v.adicCompletionIntegers F).toSubring :=
      Subring.subset_closure (Or.inl ⟨⟨(c : E), c, rfl⟩, rfl⟩)
    exact hc
  have hv : Valued.v ((g : v.adicCompletion F)) < 1 := by
    have h1 : v.intValuation (g : 𝓞 F) < 1 := (v.intValuation_lt_one_iff_mem _).2 hg
    have h2 : ((g : v.adicCompletion F)) = algebraMap (𝓞 F) (v.adicCompletion F) (g : 𝓞 F) :=
      (map_natCast _ g).symm
    rw [h2]
    refine lt_of_eq_of_lt (v.valuedAdicCompletion_eq_valuation (g : 𝓞 F)) ?_
    rw [v.valuation_of_algebraMap]
    exact h1
  obtain ⟨hfin, hspan⟩ := hL
  obtain ⟨G, hG⟩ := Module.Finite.iff_fg.1 hfin
  have hgen : ∀ x ∈ L, (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ loc v L :=
    fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  set M : Submodule (v.adicCompletionIntegers F) (v.adicCompletion F) := Submodule.span _
    (Set.range fun p : G × Fin n => (sp (inclE (F := F) (v.adicCompletion F) ((p.1 : Fin n → E) p.2))).1) with hMdef
  have hMx : ∀ x ∈ L, ∀ i, (sp (inclE (F := F) (v.adicCompletion F) (x i))).1 ∈ M := by
    intro x hx i
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem s hsG => exact Submodule.subset_span ⟨(⟨s, hsG⟩, i), rfl⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using M.add_mem ha hb
    | smul c a _ ha =>
      have hc := hint _ (hOE c)
      have e : (sp (inclE (F := F) (v.adicCompletion F) ((c • a) i))).1 =
          (⟨_, hc⟩ : v.adicCompletionIntegers F) • (sp (inclE (F := F) (v.adicCompletion F) (a i))).1 := by
        rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, Prod.fst_mul, Algebra.smul_def]
        rfl
      rw [e]
      exact M.smul_mem _ ha
  have hM : ∀ y ∈ loc v L, ∀ i, (sp (y i)).1 ∈ M := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hxL, rfl⟩ := hx
      exact hMx x hxL
    | zero => intro i; simp
    | add a b _ _ ha hb => intro i; simpa using M.add_mem (ha i) (hb i)
    | smul r a _ ha =>
      intro i
      have hr := hint _ r.2
      have e : (sp ((r • a) i)).1 = (⟨_, hr⟩ : v.adicCompletionIntegers F) • (sp (a i)).1 := by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, Prod.fst_mul, Algebra.smul_def]
        rfl
      rw [e]
      exact M.smul_mem _ (ha i)
  have hle : M ≤ Ideal.span {((g : v.adicCompletionIntegers F))} • M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨⟨s, hsG⟩, i⟩, rfl⟩
    have hsL : s ∈ L := hG ▸ Submodule.subset_span hsG
    obtain ⟨z, hz, hyz⟩ := h _ (hgen s hsL)
    have e : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 =
        (g : v.adicCompletionIntegers F) • (sp (z i)).1 := by
      have hi : inclE (F := F) (v.adicCompletion F) (s i) = ((g : E ⊗[F] v.adicCompletion F) • z) i :=
        congrFun hyz i
      rw [hi, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Prod.fst_mul, Algebra.smul_def]
      simp
    change (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ∈
      ((Ideal.span {((g : v.adicCompletionIntegers F))} • M : Submodule _ _) : Set (v.adicCompletion F))
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hM z hz i)
  have hjac : Ideal.span {((g : v.adicCompletionIntegers F))} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨b, hb⟩ := hunit.exists_left_inv
    have hb' : (b : v.adicCompletion F) * (g : v.adicCompletion F) = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    have hbv : Valued.v (b : v.adicCompletion F) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) (v := v)).1 b.2
    have hlt : Valued.v ((b : v.adicCompletion F) * (g : v.adicCompletion F)) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left' hbv).trans_lt hv
    rw [hb', map_one] at hlt
    exact lt_irrefl _ hlt
  have hne : ∃ s ∈ G, ∃ i, s i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have hL0 : L = ⊥ := by
      rw [← hG, Submodule.span_eq_bot]
      intro s hs
      funext i
      exact hcon s hs i
    have h1 : (fun _ : Fin n => (1 : E)) ∈ Submodule.span E (L : Set (Fin n → E)) := hspan ▸ Submodule.mem_top
    rw [hL0, Submodule.bot_coe, Submodule.span_zero_singleton, Submodule.mem_bot] at h1
    exact one_ne_zero (congrFun h1 ⟨0, hn⟩)
  obtain ⟨s, hsG, i, hsi⟩ := hne
  have hu : IsUnit (sp (inclE (F := F) (v.adicCompletion F) (s i))) :=
    ((isUnit_iff_ne_zero.2 hsi).map (inclE (F := F) (v.adicCompletion F))).map sp
  have ha : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ≠ 0 :=
    (hu.map (RingHom.fst (v.adicCompletion F) (v.adicCompletion F))).ne_zero
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ M (Submodule.fg_span (Set.finite_range _)) hle hjac
  have hmem : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ∈ M := Submodule.subset_span ⟨(⟨s, hsG⟩, i), rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact ha hmem

end

theorem local_idempotent_cases :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (g : ℕ), (g : 𝓞 F) ∈ v.asIdeal → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → 0 < n → ∀ e : E ⊗[F] v.adicCompletion F, e * e = e → e * sigR σ (v.adicCompletion F) e = 0 → (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - e - sigR σ (v.adicCompletion F) e) • y = (g : E ⊗[F] v.adicCompletion F) • z) → sp e = (1, 0) ∨ sp e = (0, 1) := by
  intro F E _ _ _ _ _ σ n v sp hsw hdiag g hg L hL hn e he heo hfull
  have hse : sp (sigR σ (v.adicCompletion F) e) = ((sp e).2, (sp e).1) := by
    rw [hsw]
    rfl
  have hidem : sp e * sp e = sp e := by rw [← map_mul, he]
  have horth : sp e * ((sp e).2, (sp e).1) = 0 := by rw [← hse, ← map_mul, heo, map_zero]
  have ha : (sp e).1 * (sp e).1 = (sp e).1 := congrArg Prod.fst hidem
  have hb : (sp e).2 * (sp e).2 = (sp e).2 := congrArg Prod.snd hidem
  have hab : (sp e).1 * (sp e).2 = 0 := congrArg Prod.fst horth
  have ha' : (sp e).1 = 0 ∨ (sp e).1 = 1 := by
    have h0 : (sp e).1 * ((sp e).1 - 1) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hb' : (sp e).2 = 0 ∨ (sp e).2 = 1 := by
    have h0 : (sp e).2 * ((sp e).2 - 1) = 0 := by rw [mul_sub, mul_one, hb, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases ha' with ha0 | ha1 <;> rcases hb' with hb0 | hb1
  · exfalso
    have he0 : e = 0 := sp.injective (by rw [map_zero]; exact Prod.ext ha0 hb0)
    apply not_forall_loc_eq_natCast_smul v sp hdiag g hg L hL hn
    intro y hy
    obtain ⟨z, hz, hyz⟩ := hfull y hy
    refine ⟨z, hz, ?_⟩
    rw [he0, map_zero, sub_zero, sub_zero, one_smul] at hyz
    exact hyz
  · exact Or.inr (Prod.ext ha0 hb1)
  · exact Or.inl (Prod.ext ha1 hb0)
  · exfalso
    rw [ha1, hb1, one_mul] at hab
    exact one_ne_zero hab

end GlobalTheory.St.G
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.globalHermitianFrames_good_almost_all_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), {p | ¬ Good (G.S p)}.Finite := by
  first | exact @GlobalTheory.HL.StdPlace.good_almost_all | exact GlobalTheory.HL.StdPlace.good_almost_all | (intros; apply GlobalTheory.HL.StdPlace.good_almost_all <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.pattern_unitriangular_strong_approximation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (m : ℕ) (I : Fin m → Fin m → Prop), (∀ i j, I i j → i < j) → (∀ i j l, I i j → I j l → I i l) → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ s : ∀ p, Matrix (Fin m) (Fin m) (A.loc p).Ep, (∀ p i j, ¬ I i j → s p i j = if i = j then 1 else 0) → {p | ¬ IsIntM (A.L p) (s p)}.Finite → ∃ t : Matrix (Fin m) (Fin m) E, (∀ i j, ¬ I i j → t i j = if i = j then 1 else 0) ∧ ∀ p i j, ∃ o ∈ (A.L p).O, ((s p)⁻¹ * t.map (A.loc p).ιE - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  first | exact @GlobalTheory.HL.pattern_strong_approx | exact GlobalTheory.HL.pattern_strong_approx | (intros; apply GlobalTheory.HL.pattern_strong_approx <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_corner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inl p))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inl p))) → degB r β ≤ degB r (.inr (.inr (.inl p))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.LiftCorner.lift_corner | exact GlobalTheory.SnMass.VolN.LiftCorner.lift_corner | (intros; apply GlobalTheory.SnMass.VolN.LiftCorner.lift_corner <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inl p) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inl p) → degB r β ≤ degB r (.inl p) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.LiftEntry.lift_entry | exact GlobalTheory.SnMass.VolN.LiftEntry.lift_entry | (intros; apply GlobalTheory.SnMass.VolN.LiftEntry.lift_entry <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_antidiagonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → ℝ), l ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inr a))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inr a))) → degB r β ≤ degB r (.inr (.inr (.inr a))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.exists_lift_antidiag | exact GlobalTheory.SnMass.VolN.exists_lift_antidiag | (intros; apply GlobalTheory.SnMass.VolN.exists_lift_antidiag <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.lift_row_middleSpace_integralPoint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → Fin (k + 1) → ℂ), l ∈ homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inl a)) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inl a)) → degB r β ≤ degB r (.inr (.inl a)) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.RowLift.lift_row | exact GlobalTheory.SnMass.VolN.RowLift.lift_row | (intros; apply GlobalTheory.SnMass.VolN.RowLift.lift_row <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.skewLattice_inverseDifferentPow_covolume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t : ℕ) (c : ℝ), 0 < c → HasDom volume (skewLat (σ : E →+* E) (dInv E (2 * t)) c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * (t : ℝ)) * c ^ Fintype.card (InfinitePlace E))) := by
  first | exact @GlobalTheory.SnMass.SkewVol.skew_covol_dInv | exact GlobalTheory.SnMass.SkewVol.skew_covol_dInv | (intros; apply GlobalTheory.SnMass.SkewVol.skew_covol_dInv <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory.HL.SAN

theorem _root_.GlobalTheory.T.hermitian_symplectic_basis_local_extension : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : ∀ i j, sig (Hm j i) = Hm i j) (X Y : Fin r → Fin N → E) (T : Finset (Fin r)) (hXY : ∀ a b, hq sig Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hq sig Hm (X a) (X b) = 0) (hYY : ∀ a b, hq sig Hm (Y a) (Y b) = 0) (up : ∀ p, Fin N → (A.loc p).Ep) (sp : ∀ p, (A.loc p).Ep) (horth : ∀ p, ∀ a ∈ T, hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (A.bc p (X a)) = 0 ∧ hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (A.bc p (Y a)) = 0) (hs : ∀ p, sp p + (A.L p).cj (sp p) = hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) (hint : {p | ¬ ((∀ j, up p j ∈ (A.L p).O) ∧ sp p ∈ (A.L p).O)}.Finite) (d : ∀ p, ((A.loc p).Fp)ˣ) (hd : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite), ∃ (u : Fin N → E) (s : E), (∀ a ∈ T, hq sig Hm u (X a) = 0 ∧ hq sig Hm u (Y a) = 0) ∧ s + sig s = hq sig Hm u u ∧ ∀ p, (∀ j, ∃ o ∈ (A.L p).O, (A.loc p).ιE (u j) - up p j = algebraMap (A.loc p).Fp (A.loc p).Ep (d p) * o) ∧ ∃ o ∈ (A.L p).O, (A.loc p).ιE s - sp p = algebraMap (A.loc p).Fp (A.loc p).Ep (d p) * o := by
  first | exact @GlobalTheory.HL.EichlerParams.strong_approx_params | exact GlobalTheory.HL.EichlerParams.strong_approx_params | (intros; apply GlobalTheory.HL.EichlerParams.strong_approx_params <;> assumption)
end

section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.ncard_primitiveTuplesWithGramMatrix_residueRing : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (m n : ℕ), 2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) → (q : ℝ) ^ (2 * n * m - m ^ 2) ≤ 2 * (Set.ncard (sols c n G) : ℝ) ∧ (Set.ncard (sols c n G) : ℝ) ≤ 2 * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  first | exact @GlobalTheory.GramCount.ncard_sols_residue | exact GlobalTheory.GramCount.ncard_sols_residue | (intros; apply GlobalTheory.GramCount.ncard_sols_residue <;> assumption)
end

section

namespace GlobalTheory

theorem coveringO_holds : Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO := by
  apply Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.coveringO_of_transference
  intro E _ _ _ Λ _ _ lam hlam hdual x
  exact transferenceCover_holds E Λ lam hlam hdual x

end GlobalTheory
end
