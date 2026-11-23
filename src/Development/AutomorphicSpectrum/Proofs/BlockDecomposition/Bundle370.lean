module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle351
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetClosedOpenSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle128
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle356
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.smooth_vector_fixed_small_shear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V), IsSmooth T → ∀ v : V, ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, T (levi k (n + 1) (shearGL n b)) v = v := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.shear_fix_vector | exact GlobalTheory.CompanionTheory.MirPair.shear_fix_vector | (intros; apply GlobalTheory.CompanionTheory.MirPair.shear_fix_vector <;> assumption)
end

section

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_threshold_mem_box {m : ℕ} (y : Fin m → k) (t₀ : kˣ) :
    ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      ∀ t : kˣ, valuation k (t₁ : k) ≤ valuation k (t : k) → y ∈ box m t := by
  classical
  have hstep : ∀ (S : Finset (Fin m)), ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      ∀ j ∈ S, valuation k (y j) ≤ valuation k (t₁ : k) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨t₀, le_rfl, by simp⟩
    | insert a S _ ih =>
      obtain ⟨t₁, h0, h1⟩ := ih
      by_cases hle : valuation k (y a) ≤ valuation k (t₁ : k)
      · refine ⟨t₁, h0, fun j hj => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hle
        · exact h1 j hj
      · have hlt := lt_of_not_ge hle
        have hya : y a ≠ 0 := by
          intro h0'
          rw [h0', map_zero] at hlt
          exact not_lt_zero' hlt
        refine ⟨Units.mk0 (y a) hya, ?_, fun j hj => ?_⟩
        · simpa using h0.trans hlt.le
        · rcases Finset.mem_insert.1 hj with rfl | hj
          · simp
          · simpa using (h1 j hj).trans hlt.le
  obtain ⟨t₁, h0, h1⟩ := hstep Finset.univ
  exact ⟨t₁, h0, fun t ht j => (h1 j (Finset.mem_univ j)).trans ht⟩

variable [MeasurableSpace k] [BorelSpace k]

theorem setIntegral_box_add (ν : Measure k) [ν.IsAddHaarMeasure] {m : ℕ} (t : kˣ) {y : Fin m → k}
    (hy : y ∈ box m t) (f : (Fin m → k) → ℂ) :
    ∫ x in (box m t : Set (Fin m → k)), f (x + y) ∂(piHaar ν m) =
      ∫ x in (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) := by
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : (piHaar ν m).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hpre : (fun x => x + y) ⁻¹' (box m t : Set (Fin m → k)) = box m t := by
    ext x
    exact (box m t).add_mem_cancel_right hy
  have := (measurePreserving_add_right (piHaar ν m) y).setIntegral_preimage_emb
    (measurableEmbedding_addRight y) f (box m t : Set (Fin m → k))
  rwa [hpre] at this

theorem wt_sub (ψ : AddChar k Circle) (n : ℕ) (x y : Fin (n + 1) → k) :
    wt ψ n (x - y) = ((ψ (y (Fin.last n)) : Circle) : ℂ) * wt ψ n x := by
  have h : -(x - y) (Fin.last n) = y (Fin.last n) + -x (Fin.last n) := by
    simp only [Pi.sub_apply]; ring
  simp only [wt]
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem wt_add (ψ : AddChar k Circle) (n : ℕ) (x y : Fin (n + 1) → k) :
    wt ψ n (x + y) = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * wt ψ n x := by
  have h : -(x + y) (Fin.last n) = -y (Fin.last n) + -x (Fin.last n) := by
    simp only [Pi.add_apply]; ring
  simp only [wt]
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem EvVal_translate : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (y : Fin (n + 1) → k) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (uM (n + 1) y) v) v' (((ψ (y (Fin.last n)) : Circle) : ℂ) * A) ∧ EvVal ν ψ T B v (T' (uM (n + 1) y) v') (((ψ (-y (Fin.last n)) : Circle) : ℂ) * A) := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T T' B s _ _ hB y v v' A hA
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨t₁, h01, h1⟩ := exists_threshold_mem_box y t₀
  obtain ⟨hc1, hc2, -⟩ := GlobalTheory.T.mirabolic_coefficient_translation T T' B s hB
  refine ⟨⟨t₁, fun t ht => ?_⟩, ⟨t₁, fun t ht => ?_⟩⟩
  · have hy := h1 t ht
    have hJ := ht₀ t (h01.trans ht)
    have key := setIntegral_box_add ν t hy (fun x => wt ψ n (x - y) * coef T B v v' x)
    simp only [add_sub_cancel_right] at key
    have e1 : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) (T (uM (n + 1) y) v) v' =
        ∫ x in (box (n + 1) t : Set (Fin (n + 1) → k)), wt ψ n x * coef T B v v' (x + y)
          ∂(piHaar ν (n + 1)) := by
      simp only [JJ, hc1]
    rw [e1, key, ← hJ, JJ, ← integral_const_mul]
    simp only [wt_sub, mul_assoc]
  · have hy := h1 t ht
    have hy' : -y ∈ box (n + 1) t := neg_mem hy
    have hJ := ht₀ t (h01.trans ht)
    have key := setIntegral_box_add ν t hy' (fun x => wt ψ n (x + y) * coef T B v v' x)
    simp only [← sub_eq_add_neg, sub_add_cancel] at key
    have e1 : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v (T' (uM (n + 1) y) v') =
        ∫ x in (box (n + 1) t : Set (Fin (n + 1) → k)), wt ψ n x * coef T B v v' (x - y)
          ∂(piHaar ν (n + 1)) := by
      simp only [JJ, hc2]
    rw [e1, key, ← hJ, JJ, ← integral_const_mul]
    simp only [wt_add, mul_assoc]

end GlobalTheory.CompanionTheory.MirPair

end
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_pairing_depth_vanishing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (b : Fin (n + 1) → k) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V'), valuation k (b (Fin.last n)) < 1 → T (levi k (n + 1) (shearGL n b)) v = v → (∀ x, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M) → ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = JJ ν ψ T B M v (T' (levi k (n + 1) (shearGL n b)) v') := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear | exact GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear | (intros; apply GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear <;> assumption)
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_coefficient_continuous : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), IsSmooth T → ∀ (v : V) (v' : V'), Continuous (coef T B v v') := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.continuous_coef | exact GlobalTheory.CompanionTheory.MirPair.continuous_coef | (intros; apply GlobalTheory.CompanionTheory.MirPair.continuous_coef <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.twisted_jacquet_closed_open_sequence : ∀ {G M Z VC VO AC AO : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    [AddCommGroup Z] [Module ℂ Z] [AddCommGroup VC] [Module ℂ VC] [AddCommGroup VO] [Module ℂ VO]
    [AddCommGroup AC] [Module ℂ AC] [AddCommGroup AO] [Module ℂ AO]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U))
    (hdir : ∀ L₁ L₂ : Subgroup G, L₁ ≤ U → L₂ ≤ U → IsCompact (L₁ : Set G) → IsCompact (L₂ : Set G) →
      ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧ L₁ ≤ L ∧ L₂ ≤ L)
    (s : M →* G) (c : M →* ℂˣ) (ρ : Representation ℂ M (TwJacquet (cInd H σ) U θ))
    (hρ : ∀ (m : M) (f : cIndSpace H σ), ρ m (Submodule.Quotient.mk f) =
      ((c m : ℂˣ) : ℂ) • Submodule.Quotient.mk (cInd H σ (s m) f))
    (C : Set G) (hCc : IsClosed C) (hHC : ∀ h ∈ H, ∀ x ∈ C, h * x ∈ C) (hCU : ∀ x ∈ C, ∀ u ∈ U, x * u ∈ C)
    (πC : Representation ℂ M VC) (πO : Representation ℂ M VO)
    (aC : Representation ℂ M AC) (aO : Representation ℂ M AO)
    (jC : VC →ₗ[ℂ] AC) (jO : VO →ₗ[ℂ] AO) (hjC : Function.Injective jC) (hjO : Function.Injective jO)
    (hjCe : ∀ m v, jC (πC m v) = aC m (jC v)) (hjOe : ∀ m v, jO (πO m v) = aO m (jO v))
    (eC : cIndSpace H σ →ₗ[ℂ] AC) (eO : cIndSpace H σ →ₗ[ℂ] AO)
    (hC1 : ∀ (u : U) f, eC (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eC f)
    (hO1 : ∀ (u : U) f, eO (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eO f)
    (hCs : ∀ m f, aC m (eC f) = ((c m : ℂˣ) : ℂ) • eC (cInd H σ (s m) f))
    (hOs : ∀ m f, aO m (eO f) = ((c m : ℂˣ) : ℂ) • eO (cInd H σ (s m) f))
    (hCmem : ∀ f, ∃ v, jC v = eC f)
    (hOmem : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → ∃ v, jO v = eO f)
    (hConto : ∀ v, ∃ f, eC f = jC v)
    (hOonto : ∀ v, ∃ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) ∧ eO f = jO v)
    (hCoff : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → eC f = 0)
    (hlocC : ∀ f, eC f = 0 → ∀ p ∈ C, AvgVanish H σ U θ f p)
    (hlocO : ∀ f, eO f = 0 → ∀ p, p ∉ C → AvgVanish H σ U θ f p),
  ∃ S : Subrepresentation ρ, Nonempty ((subQuot S ⊥).Equiv πO) ∧ Nonempty ((subQuot ⊤ S).Equiv πC) := by
  intro G M Z VC VO AC AO _ _ _ _ _ _ _ _ _ _ _ _ _ _
    H σ U hUn θ hθ hdir s c ρ hρ C hCc hHC hCU πC πO aC aO jC jO hjC hjO hjCe hjOe
    eC eO hC1 hO1 hCs hOs hCmem hOmem hConto hOonto hCoff hlocC hlocO
  have kC : twKer (cInd H σ) U θ ≤ LinearMap.ker eC := Submodule.span_le.2 (by
    rintro _ ⟨u, v, rfl⟩
    show eC _ = 0
    rw [map_sub, hC1, map_smul, sub_self])
  have kO : twKer (cInd H σ) U θ ≤ LinearMap.ker eO := Submodule.span_le.2 (by
    rintro _ ⟨u, v, rfl⟩
    show eO _ = 0
    rw [map_sub, hO1, map_smul, sub_self])
  have ECmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eC kC (Submodule.Quotient.mk f) = eC f := fun f => rfl
  have EOmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eO kO (Submodule.Quotient.mk f) = eO f := fun f => rfl
  refine Glue.extension_of_maps ρ πC πO aC aO jC jO hjC hjO hjCe hjOe
    ((twKer (cInd H σ) U θ).liftQ eC kC) ((twKer (cInd H σ) U θ).liftQ eO kO) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro m y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hρ, map_smul, ECmk, ECmk, hCs]
  · intro m y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hρ, map_smul, EOmk, EOmk, hOs]
  · intro y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact hCmem f
  · intro v
    obtain ⟨f, hf⟩ := hConto v
    exact ⟨Submodule.Quotient.mk f, hf⟩
  · intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hv⟩ := Glue.glue H σ U hUn θ hθ hdir C hCc hHC hCU f (hlocC f hy)
    have e : (Submodule.Quotient.mk f : TwJacquet (cInd H σ) U θ) = Submodule.Quotient.mk g :=
      (Submodule.Quotient.eq _).2 hg
    obtain ⟨v, hv'⟩ := hOmem g hv
    exact ⟨v, by rw [e, EOmk, hv']⟩
  · intro y hyC hyO
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hv⟩ := Glue.glue H σ U hUn θ hθ hdir Set.univ isClosed_univ (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial) f (fun p _ => by
        by_cases hp : p ∈ C
        · exact hlocC f hyC p hp
        · exact hlocO f hyO p hp)
    have hg0 : g = 0 := Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => hv x trivial)))
    rw [hg0, sub_zero] at hg
    exact (Submodule.Quotient.mk_eq_zero _).2 hg
  · intro v
    obtain ⟨f, hf, he⟩ := hOonto v
    exact ⟨Submodule.Quotient.mk f, hCoff f hf, he⟩
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj

section Alg

variable (k : Type) [Field k]

def rGL {a b : ℕ} (h : a = b) : GL (Fin a) k ≃* GL (Fin b) k := h ▸ MulEquiv.refl _

theorem rGL_apply {a b : ℕ} (h : a = b) (g : GL (Fin a) k) (r c : Fin b) :
    ((rGL k h g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k) r c =
      (g : Matrix (Fin a) (Fin a) k) (Fin.cast h.symm r) (Fin.cast h.symm c) := by
  subst h
  rfl

theorem rGL_rGL {a b : ℕ} (h : a = b) (h' : b = a) (g : GL (Fin a) k) : rGL k h' (rGL k h g) = g := by
  subst h
  rfl

theorem continuous_rGL [TopologicalSpace k] {a b : ℕ} (h : a = b) : Continuous (rGL k h) := by
  subst h
  exact continuous_id

theorem castM_val {a b : ℕ} (h : a = b) (h' : a + 1 = b + 1) (M : Mir k a) :
    ((castM k h M : Mir k b) : GL (Fin (b + 1)) k) = rGL k h' (M : GL (Fin (a + 1)) k) := by
  subst h
  rfl

theorem mirProj_eq_one_of_unip (n : ℕ) (u : Mir k n) (v : Multiplicative (Fin n → k))
    (hu : (u : GL (Fin (n + 1)) k) = unip k n v) : mirabolicProjection k n u = 1 := by
  ext i j
  show blockMat k n ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j = _
  rw [hu]
  simp [blockMat, unip, colMat, Fin.castSucc_ne_last, one_apply]
  change (if i.castSucc = j.castSucc then (1 : k) else 0) = if i = j then 1 else 0
  simp

theorem ePG_true_val (i t : ℕ) (b : Fin t) : ((ePG i t ⟨true, b⟩ : Fin (i + t + 1)) : ℕ) = i + b := by
  simp [ePG]

theorem ePG_false_castSucc_val (i t : ℕ) (a : Fin i) :
    ((ePG i t ⟨false, Fin.castSucc a⟩ : Fin (i + t + 1)) : ℕ) = a := by
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem wGL_conj_apply (i t : ℕ) (A : GL (Fin ((i + 1) + t + 1)) k) (r c : Fin ((i + 1) + t + 1)) :
    (((wGL k i t)⁻¹ * A * wGL k i t : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) r c =
      (A : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (piPerm i t r) (piPerm i t c) := by
  have e1 : (((wGL k i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) = Equiv.Perm.permMatrix k (piPerm i t) := rfl
  have e2 : ((wGL k i t : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) = Equiv.Perm.permMatrix k (piPerm i t)⁻¹ := rfl
  rw [Units.val_mul, Units.val_mul, e1, e2, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Matrix.submatrix_apply, Equiv.Perm.inv_def]

theorem piPerm_cast (i t : ℕ) (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) (h : i + (t + 1) + 1 = (i + 1) + t + 1) :
    piPerm i t (Fin.cast h (ePG i (t + 1) s)) = eGP (i + 1) t s := by
  simp [piPerm]

theorem proj_eq (i t : ℕ) (h : Mir k ((i + 1) + t + 1)) (d : Fin (t + 1) → k) (M : Mir k ((i + 1) + t))
    (x : Mir k ((i + 1) + t + 1))
    (e : dEmb k i t d * wEl k i t * sEmb k _ M = h * wEl k i t * x) :
    (M : GL (Fin ((i + 1) + t + 1)) k) =
      ((wGL k i t)⁻¹ * mirabolicProjection k _ h * wGL k i t) * mirabolicProjection k _ x := by
  have e1 := congrArg (mirabolicProjection k ((i + 1) + t + 1)) e
  rw [map_mul, map_mul, map_mul, map_mul] at e1
  have h1 : mirabolicProjection k ((i + 1) + t + 1) (dEmb k i t d) = 1 := mirProj_eq_one_of_unip k _ _ _ rfl
  have h2 : mirabolicProjection k ((i + 1) + t + 1) (wEl k i t) = wGL k i t := GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi k _ _
  have h3 : mirabolicProjection k ((i + 1) + t + 1) (sEmb k _ M) = (M : GL (Fin ((i + 1) + t + 1)) k) :=
    GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi k _ _
  rw [h1, h2, h3, one_mul] at e1
  rw [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, e1, mul_assoc]

end Alg

theorem exists_parab_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), ∃ Θ : Mir k ((i + 1) + t + 1) → GL (Fin (i + (t + 1) + 1)) k, Continuous Θ ∧ Θ 1 = 1 ∧
    ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) → ∀ (d : Fin (t + 1) → k) (m : Mir k (i + (t + 1)))
      (x : Mir k ((i + 1) + t + 1)), dEmb k i t d * wEl k i t * sO k i t m = h * wEl k i t * x →
      ∃ p ∈ parab k (ePG i (t + 1)), (m : GL (Fin (i + (t + 1) + 1)) k) = p * Θ x := by
  intro k _ _ _ _ i t
  have hn : (i + 1) + t + 1 = i + (t + 1) + 1 := by omega
  refine ⟨fun x => rGL k hn (mirabolicProjection k _ x),
    (continuous_rGL k hn).comp (GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k _), by simp, ?_⟩
  intro h hh d m x e
  have e2 := proj_eq k i t h d (castM k (by omega) m) x e
  rw [castM_val k _ hn.symm] at e2
  refine ⟨rGL k hn ((wGL k i t)⁻¹ * mirabolicProjection k _ h * wGL k i t), ?_, ?_⟩
  · rw [mem_parab_iff]
    intro a b u v hab
    cases a <;> cases b <;> first | exact absurd hab (by decide) | skip
    rw [rGL_apply, wGL_conj_apply, piPerm_cast, piPerm_cast]
    have hh' : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1)) := hh
    have h0 := mem_parab_iff.1 hh' true false u (Fin.castSucc v) (by decide)
    have e3 : Fin.castSucc (eGP (i + 1) t ⟨true, u⟩) = ePG (i + 1) (t + 1) ⟨true, u⟩ :=
      Fin.ext (by rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val, ePG_true_val])
    have e4 : Fin.castSucc (eGP (i + 1) t ⟨false, v⟩) = ePG (i + 1) (t + 1) ⟨false, Fin.castSucc v⟩ :=
      Fin.ext (by rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val, ePG_false_castSucc_val])
    show ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val
      (Fin.castSucc (eGP (i + 1) t ⟨true, u⟩)) (Fin.castSucc (eGP (i + 1) t ⟨false, v⟩)) = 0
    rw [e3, e4]
    exact h0
  · have e5 := congrArg (rGL k hn) e2
    rw [rGL_rGL, map_mul] at e5
    exact e5

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.bump_translate_mem_submodule : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (ρ : Representation ℂ H W) (K₁ K₂ : Subgroup G) (h₂₁ : K₂ ≤ K₁)
    (hK₁c : IsCompact (K₁ : Set G)) (hK₂o : IsOpen (K₂ : Set G)) (v : W)
    (hv : ∀ a : H, (a : G) ∈ K₁ → ρ a v = v) (S : Submodule ℂ (cIndSpace H ρ))
    (hS : ∀ g, ∀ b ∈ S, cInd H ρ g b ∈ S) (b : cIndSpace H ρ) (hb : IsBump H ρ K₂ 1 v b) (hbS : b ∈ S)
    (B : cIndSpace H ρ) (hB : IsBump H ρ K₁ 1 v B), B ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Avg.bump_mem_of_bump | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Avg.bump_mem_of_bump | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Avg.bump_mem_of_bump <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.closed_cell_right_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), ∀ p ∈ Cl k i t, ∀ m, p * sO k i t m ∈ Cl k i t := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.continuous_shifted_orbit_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), Continuous (sO k i t) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_submodule_of_bumps : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (y : cIndSpace H ρ) (hy : ∀ g, ∀ x ∈ K, y.1.1.1 (g * x) = y.1.1.1 g)
    (S : Submodule ℂ (cIndSpace H ρ)) (hS : ∀ c B, IsBump H ρ K c (y.1.1.1 c) B → B ∈ S), y ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.mem_of_bumps | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.mem_of_bumps | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.mem_of_bumps <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibInvK

theorem fibV_mul_right_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ b' ∈ K₁, ∀ g : GL (Fin (i + t)) k, fibV b (g * b') = fibV b g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ c K₁ hK z b hval hzero b' hb' g
  have hβ : GlobalTheory.BZMir.levi k (i + t) b' ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK := by
    show ∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt (i + t) c, ∃ a ∈ K₁,
      GlobalTheory.BZMir.levi k (i + t) b' = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y * GlobalTheory.BZMir.levi k (i + t) a
    exact ⟨0, zero_mem _, b', hb', by rw [GlobalTheory.CompanionTheory.BZPsiPG.uM_zero, one_mul]⟩
  have key : ∀ p : GlobalTheory.BZMir.Mir k (i + t), ∀ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
      b.1.1.1 (p * β) = b.1.1.1 p := by
    intro p β hβ
    by_cases hp : ∃ h : GlobalTheory.BZMir.Leib.HPG k i t,
        ∃ β₀ ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : GlobalTheory.BZMir.Mir k (i + t)) * β₀
    · obtain ⟨h, β₀, hβ₀, rfl⟩ := hp
      rw [mul_assoc, hval h (β₀ * β) (Subgroup.mul_mem _ hβ₀ hβ), hval h β₀ hβ₀]
    · have hp' : ¬ ∃ h : GlobalTheory.BZMir.Leib.HPG k i t,
          ∃ β₀ ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
            p * β = (h : GlobalTheory.BZMir.Mir k (i + t)) * β₀ := by
        rintro ⟨h, β₀, hβ₀, he⟩
        refine hp ⟨h, β₀ * β⁻¹, Subgroup.mul_mem _ hβ₀ (Subgroup.inv_mem _ hβ), ?_⟩
        rw [← mul_assoc, ← he, mul_inv_cancel_right]
      rw [hzero _ hp', hzero _ hp]
  funext v
  unfold GlobalTheory.CompanionTheory.BZPsiPG.fibV
  rw [map_mul, ← mul_assoc]
  exact key _ _ hβ

end GlobalTheory.CompanionTheory.BZPsiPG.FibInvK

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.locally_constant_coset_indicator_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z) (c : k), c ≠ 0 → HasCompactSupport φ → (∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v) → ∃ A : Finset (Fin t → k), ∀ v, φ v = ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => φ a) v := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_sum_coset_indicators | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_sum_coset_indicators | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_sum_coset_indicators <;> assumption)
end
