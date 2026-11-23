module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle345
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairAlternatingNeOnCycloKernel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOrbitHasNearbyFixedPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle346
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle220
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.eulerSystemTameClass_scale_enlarge_coefficients : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c c' : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (a : Qbar l), c.O ≤ c'.O → a ∈ c'.O → Tame c W y n w ψ → Tame c' W (fun s => a • y s) n w ψ := by
  first | exact @GlobalTheory.Ord2.tame_scale | exact GlobalTheory.Ord2.tame_scale | (intros; apply GlobalTheory.Ord2.tame_scale <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.height_commutator_invariance : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (c : Coef l) (W : R2 Ω l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ φ ∈ H0g W, ∀ g ∈ N0g W, ∀ h ∈ N0g W, Cg n (ht W y z u (φ * (g * h * g⁻¹ * h⁻¹)) - ht W y z u φ) ((mat W φ - 1).det * (om (y h) (z g) - om (y g) (z h))) := by
  first | exact @GlobalTheory.Ord2.ht_commutator | exact GlobalTheory.Ord2.ht_commutator | (intros; apply GlobalTheory.Ord2.ht_commutator <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.greenbergOrdinary_of_vanishing_on_cycloKernel : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W), (∀ g ∈ N0g W, y g = 0) → Gr W A y := by
  first | exact @GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial | exact GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial | (intros; apply GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.cocycle_pair_alternating_ne_on_cycloKernel : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W), ∀ z ∈ Z1 (Loc.colRep (dual1 W)), (∃ g ∈ N0g W, y g ≠ 0) → (∃ g ∈ N0g W, z g ≠ 0) → ∃ g ∈ N0g W, ∃ h ∈ N0g W, om (y h) (z g) ≠ om (y g) (z h) := by
  first | exact @GlobalTheory.Ord2.exists_om_ne_swap_on_N0g | exact GlobalTheory.Ord2.exists_om_ne_swap_on_N0g | (intros; apply GlobalTheory.Ord2.exists_om_ne_swap_on_N0g <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KumFix

theorem pow_val_add {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] {ζ : Ω} (h : ζ ^ n = 1) (a b : ZMod n) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) n, pow_add, pow_mul, h, one_pow, mul_one]

theorem isClosed_of_le {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H N U : Subgroup Γ)
    (hH : IsClosed (H : Set Γ)) (hU : IsOpen (U : Set Γ)) (hNH : N ≤ H) (hUN : ∀ s ∈ H, s ∈ U → s ∈ N) :
    IsClosed (N : Set Γ) := by
  have h1 : IsOpen ((U.subgroupOf H : Subgroup H) : Set H) := hU.preimage continuous_subtype_val
  have h2 : IsOpen ((N.subgroupOf H : Subgroup H) : Set H) :=
    Subgroup.isOpen_mono (H₁ := U.subgroupOf H) (fun s hs => hUN s s.2 hs) h1
  have h3 : IsClosed ((N.subgroupOf H : Subgroup H) : Set H) := Subgroup.isClosed_of_isOpen _ h2
  have h4 := hH.isClosedMap_subtype_val _ h3
  convert h4 using 1
  ext s
  constructor
  · intro hs
    exact ⟨⟨s, hNH hs⟩, hs, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ht

theorem exists_eigen {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {n : ℕ} [NeZero n] (H : Subgroup (G ℚ Ω))
    (hH : IsClosed (H : Set (G ℚ Ω))) (ζ : Ω) (hζ : ζ ^ n = 1) (hfix : ∀ s ∈ H, s ζ = ζ) (χ : G ℚ Ω → ZMod n)
    (hχ : ∀ s ∈ H, ∀ t ∈ H, χ (s * t) = χ s + χ t) (U : Subgroup (G ℚ Ω)) (hU : IsOpen (U : Set (G ℚ Ω)))
    (hUχ : ∀ s ∈ H, s ∈ U → χ s = 0) : ∃ w : Ω, w ≠ 0 ∧ ∀ s ∈ H, s w = ζ ^ (χ s).val * w := by
  classical
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n)] at hζ
    exact zero_ne_one hζ
  have h1 : χ 1 = 0 := by
    have := hχ 1 H.one_mem 1 H.one_mem
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hinv : ∀ s ∈ H, χ s⁻¹ = -χ s := by
    intro s hs
    have := hχ s⁻¹ (H.inv_mem hs) s hs
    rw [inv_mul_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  let N : Subgroup (G ℚ Ω) :=
    { carrier := {s | s ∈ H ∧ χ s = 0}
      mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, by rw [hχ a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨H.one_mem, h1⟩
      inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, by rw [hinv a ha.1, ha.2, neg_zero]⟩ }
  have hNc : IsClosed (N : Set (G ℚ Ω)) :=
    isClosed_of_le H N U hH hU (fun s hs => hs.1) (fun s hs hsU => ⟨hs, hUχ s hs hsU⟩)
  have hNfix : (IntermediateField.fixedField N).fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, hNc⟩
  let E := IntermediateField.fixedField N
  let ι := {k : ZMod n // ∃ g ∈ H, χ g = k}
  choose r hrH hrχ using fun k : ι => k.2
  let f : ι → (E →* Ω) := fun k =>
    { toFun := fun x => r k (x : Ω)
      map_one' := by simp
      map_mul' := fun x y => by simp }
  have hf : Function.Injective f := by
    intro j k hjk
    have hm : (r j)⁻¹ * r k ∈ N := by
      rw [← hNfix, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have e : r j x = r k x := DFunLike.congr_fun hjk ⟨x, hx⟩
      rw [AlgEquiv.mul_apply, ← e]
      exact (r j).symm_apply_apply x
    have h2 := hm.2
    rw [hχ _ (H.inv_mem (hrH j)) _ (hrH k), hinv _ (hrH j), hrχ, hrχ] at h2
    exact Subtype.ext (neg_add_eq_zero.mp h2)
  have hli := (linearIndependent_monoidHom E Ω).comp f hf
  have hex : ∃ x : E, ∑ k : ι, ζ ^ (-(k : ZMod n)).val * r k (x : Ω) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := Fintype.linearIndependent_iff.mp hli (fun k => ζ ^ (-(k : ZMod n)).val) (by
      funext x
      rw [Finset.sum_apply]
      exact hcon x) ⟨0, 1, H.one_mem, h1⟩
    exact pow_ne_zero _ hζ0 this
  obtain ⟨x, hx⟩ := hex
  refine ⟨_, hx, fun s hs => ?_⟩
  let e : ι ≃ ι :=
    { toFun := fun k => ⟨χ s + k, s * r k, H.mul_mem hs (hrH k), by rw [hχ _ hs _ (hrH k), hrχ]⟩
      invFun := fun k => ⟨-χ s + k, s⁻¹ * r k, H.mul_mem (H.inv_mem hs) (hrH k), by
        rw [hχ _ (H.inv_mem hs) _ (hrH k), hrχ, hinv s hs]⟩
      left_inv := fun k => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }

  rw [map_sum, Finset.mul_sum, ← Equiv.sum_comp e (fun k : ι => ζ ^ (χ s).val * (ζ ^ (-(k : ZMod n)).val * r k (x : Ω)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hm : (r (e k))⁻¹ * (s * r k) ∈ N := by
    refine ⟨H.mul_mem (H.inv_mem (hrH _)) (H.mul_mem hs (hrH k)), ?_⟩
    rw [hχ _ (H.inv_mem (hrH _)) _ (H.mul_mem hs (hrH k)), hinv _ (hrH _), hχ _ hs _ (hrH k), hrχ, hrχ]
    exact neg_add_cancel _
  have hx1 : ((r (e k))⁻¹ * (s * r k)) (x : Ω) = x := (IntermediateField.mem_fixedField_iff N x).mp x.2 _ hm
  have hx2 : s (r k (x : Ω)) = r (e k) (x : Ω) := by
    have := congrArg (r (e k)) hx1
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
    rw [← this]
    exact ((r (e k)).apply_symm_apply _).symm
  rw [map_mul, map_pow, hfix s hs, hx2, ← mul_assoc, ← pow_val_add hζ]
  congr 3
  change -(k : ZMod n) = χ s + -(χ s + k)
  ring

theorem exists_kumVal : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (H : Subgroup (G ℚ Ω)), IsClosed (H : Set (G ℚ Ω)) → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → (∀ s ∈ H, s ζ = ζ) → ∀ χ : G ℚ Ω → ZMod (l ^ m), (∀ s ∈ H, ∀ t ∈ H, χ (s * t) = χ s + χ t) → ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → (∀ s ∈ H, s ∈ U → χ s = 0) → ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ H, s u = u) ∧ ∀ s ∈ H, GlobalTheory.Col.KumVal (l := l) m ζ u s (χ s) := by
  intro l _ Ω _ _ _ m H hH ζ hζ hfix χ hχ U hU hUχ
  haveI : NeZero (l ^ m) := ⟨(pow_pos (Fact.out : l.Prime).pos m).ne'⟩
  obtain ⟨w, hw0, hw⟩ := exists_eigen H hH ζ hζ.pow_eq_one hfix χ hχ U hU hUχ
  refine ⟨w ^ (l ^ m), pow_ne_zero _ hw0, fun s hs => ?_, fun s hs => ⟨w, rfl, hw s hs⟩⟩
  rw [map_pow, hw s hs, mul_pow, ← pow_mul, mul_comm (χ s).val, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

end GlobalTheory.KumFix
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.PerFix

variable {l : ℕ} [Fact l.Prime]

theorem norm_aut (σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l) (y : Qbar l) : ‖σ y‖ = ‖y‖ :=
  (spectralNorm_eq_of_equiv σ y).symm

def inertiaC (c : Coef l) : Subgroup (Qbar l ≃ₐ[ℚ_[l]] Qbar l) where
  carrier := {σ | (∀ b ∈ c.O, σ b = b) ∧ ∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1}
  one_mem' := ⟨fun b _ => rfl, fun y _ => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨hσ1, hσ2⟩ ⟨hτ1, hτ2⟩
    refine ⟨fun b hb => ?_, fun y hy => ?_⟩
    · show σ (τ b) = b
      rw [hτ1 b hb, hσ1 b hb]
    · show ‖σ (τ y) - y‖ < 1
      have e : σ (τ y) - y = (σ (τ y) - τ y) + (τ y - y) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hσ2 _ ((norm_aut τ y).le.trans hy)) (hτ2 y hy))
  inv_mem' := by
    rintro σ ⟨hσ1, hσ2⟩
    refine ⟨fun b hb => ?_, fun y hy => ?_⟩
    · show σ.symm b = b
      exact σ.symm_apply_eq.2 (hσ1 b hb).symm
    · show ‖σ.symm y - y‖ < 1
      have e : σ.symm y - y = σ.symm (y - σ y) := by simp
      rw [e, norm_aut, norm_sub_rev]
      exact hσ2 y hy

theorem exists_fixed_near : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ c₁ : ℕ, ∀ (k : ℕ) (x : Qbar l), ‖x‖ ≤ 1 →
  (∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → Cg k (σ x) x) →
  ∃ x' : Qbar l, ‖x'‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c x' ∧ Cg (k - c₁) x x' := by
  intro l _ c
  obtain ⟨C, -, hC⟩ := GlobalTheory.AxLemma.ax_lemma l
  have hl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
    rw [show ((l : ℕ) : Qbar l) = (((l : ℕ) : ℚ_[l]) : Qbar l) from (map_natCast _ _).symm,
      PadicAlgCl.norm_extends, Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt C hl1
  refine ⟨c₁, fun k x hx hfix => ?_⟩
  by_cases hk : k ≤ c₁
  · refine ⟨0, by simp, fun σ _ _ => map_zero σ, ?_⟩
    have h0 : k - c₁ = 0 := by omega
    simpa [Cg, h0] using hx
  · obtain ⟨y, hyH, hxy⟩ := hC (inertiaC c) x ‖((l : ℕ) : Qbar l) ^ k‖ (fun g hg => hfix g hg.1 hg.2)
    have hlpos : (0 : ℝ) < l := by linarith
    have key : C * ‖((l : ℕ) : Qbar l) ^ k‖ ≤ ‖((l : ℕ) : Qbar l) ^ (k - c₁)‖ := by
      rw [norm_pow, norm_pow, hl]
      have e : (l : ℝ)⁻¹ ^ k = (l : ℝ)⁻¹ ^ (k - c₁) * (l : ℝ)⁻¹ ^ c₁ := by
        rw [← pow_add]; congr 1; omega
      rw [e, mul_comm, mul_assoc]
      apply mul_le_of_le_one_right (by positivity)
      rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
      linarith
    have hxy' := hxy.trans key
    have hle1 : ‖((l : ℕ) : Qbar l) ^ (k - c₁)‖ ≤ 1 := by
      rw [norm_pow, hl]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hl1.le)
    refine ⟨y, ?_, fun σ h1 h2 => hyH σ ⟨h1, h2⟩, hxy'⟩
    have e : y = x + (y - x) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx ((norm_sub_rev y x).le.trans (hxy'.trans hle1)))

end GlobalTheory.PerFix
end
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem isDefGram_map {E K : Type} [Field E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) (f : E →+* K)
    (hf : ∀ x, star (f x) = f (cE x)) {n : ℕ} (A : Matrix (Fin n) (Fin n) E)
    (hA : ∀ φ : E →+* ℂ, (A.map φ).PosDef) : IsDefGram (A.map f) := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    have h := congrFun (congrFun (hA (σ.comp f)).isHermitian.eq a) b
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply] at h ⊢
    rw [hf]
    apply σ.injective
    have h2 := hc (σ.comp f) (A b a)
    simp only [RingHom.comp_apply] at h h2
    rw [h2]
    exact h
  · intro a b ψ
    simp only [Matrix.map_apply]
    rw [hf]
    exact hc (ψ.comp f) _
  · intro φ
    rw [Matrix.map_map]
    exact hA (φ.comp f)

theorem map_inv_of_isUnit_det {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) (hA : IsUnit A.det) : (A.map f)⁻¹ = A⁻¹.map f := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA]
  simp

theorem isUnit_det_map {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) : IsUnit (A.map f).det ↔ IsUnit A.det := by
  have : (A.map f).det = f A.det := by rw [RingHom.map_det]; rfl
  rw [this, isUnit_iff_ne_zero, isUnit_iff_ne_zero, map_ne_zero]

private theorem selfDualE_full {E : Type} [Field E] [NumberField E] {n : ℕ}
    (cE : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsSelfDualE cE J L) :
    Submodule.IsFullLattice E L := by
  classical
  haveI : Submodule.IsLattice E L := hL.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hL.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin n → E) → E := fun x => Formalism.UG.hform cE J x y
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) s f
  have ha0 : (algebraMap (𝓞 E) E a) ≠ 0 :=
    (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 E) (Fin n → E) := {
    carrier := {x | ∃ b : 𝓞 E, (b : E) = (algebraMap (𝓞 E) E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f, Formalism.UG.hform]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : E) + c = _
      rw [hb, hc]
      simp [f, Formalism.UG.hform, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom cE c * b, ?_⟩
      simp only [map_mul, hb, f, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def,
        RingOfIntegers.mapRingHom_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring }
  have hsP : (s : Set (Fin n → E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 E) E a) • y ∈ L := by
    apply (hL.2 _).2
    intro x hx
    obtain ⟨b, hb⟩ := (hs ▸ Submodule.span_le.mpr hsP) hx
    refine ⟨b, ?_⟩
    change (b : E) = _
    rw [hb]
    simp only [f, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 E) E a) • y ∈ Submodule.span E (L : Set (Fin n → E)) :=
    Submodule.subset_span hy
  have := (Submodule.span E (L : Set (Fin n → E))).smul_mem (algebraMap (𝓞 E) E a)⁻¹ hy'
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem defGram_selfDual_of_embedding : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) → ∀ (ι : Type) (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) → ∀ τ, IsDefGram (gramK emb J τ) ∧ IsDefGram (gramKd emb J τ) ∧ ∀ L : Submodule (𝓞 E) (Fin n → E), IsSelfDualE cE J L → IsSelfDualK (gramK emb J τ) (tauLat emb τ L) ∧ IsSelfDualK (gramKd emb J τ) (dualFr (tauLat emb τ L)) := by
  intro E K _ _ _ _ _ cE hc ι emb hemb n J hJ τ
  obtain ⟨φ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hdet : IsUnit J.det :=
    (isUnit_det_map φ₀ J).1 ((Matrix.isUnit_iff_isUnit_det _).1 (hJ φ₀).isUnit)
  have h1 : IsDefGram (gramK emb J τ) := isDefGram_map cE hc (emb τ) (hemb τ) J hJ
  have hdK : IsUnit (gramK emb J τ).det := (isUnit_det_map (emb τ) J).2 hdet
  refine ⟨h1, ?_, ?_⟩
  · have e : gramKd emb J τ = ((J⁻¹)ᵀ).map (emb τ) := by
      unfold gramKd
      rw [map_inv_of_isUnit_det _ _ hdet, Matrix.transpose_map]
    rw [e]
    refine isDefGram_map cE hc (emb τ) (hemb τ) _ fun φ => ?_
    rw [Matrix.transpose_map, ← map_inv_of_isUnit_det _ _ hdet]
    exact (hJ φ).inv.transpose
  · intro L hL
    have hfull := selfDualE_full cE J L hL
    have hl : Submodule.IsFullLattice K (tauLat emb τ L) := GlobalTheory.T.lattice_extension_along_field_embedding_duals.1 E K ι n emb τ L hfull
    have hd : hdualFr (gramK emb J τ) (tauLat emb τ L) = tauLat emb τ L :=
      GlobalTheory.T.lattice_extension_along_field_embedding_duals.2.1 E K ι n emb cE τ (hemb τ) J L L hdet hfull hL.2
    refine ⟨⟨hl.toIsLattice, hd⟩, (GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.1 K n _ _ hdK hl).1.toIsLattice, ?_⟩
    have h := GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.2 K n _ _ h1.1 hdK hl
    rw [hd] at h
    exact h

end GlobalTheory.TestLat
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

theorem _root_.GlobalTheory.T.cyclotomic_dvd_of_aeval_primitive_root_inertia_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ n) → ∀ R : Polynomial (fixA A), Polynomial.aeval z R = 0 → Polynomial.cyclotomic (l ^ n) (fixA A) ∣ R := by
  first | (exact @GlobalTheory.RecOne.CycDvd.cyclotomic_dvd) | (exact GlobalTheory.RecOne.CycDvd.cyclotomic_dvd) | (intros; apply GlobalTheory.RecOne.CycDvd.cyclotomic_dvd  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

theorem memE_inv_of_mem : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (d : Qbar l), d ∈ c.O → d ≠ 0 → MemE c d⁻¹ := by
  intro l _ c d hd hd0
  set x : c.O := ⟨d, hd⟩ with hxdef
  have hx0 : x ≠ 0 := fun h => hd0 (congrArg Subtype.val h)
  set L : c.O := ((l : ℕ) : c.O) with hLdef
  have hLval : (L : Qbar l) = ((l : ℕ) : Qbar l) := by simp [hLdef]
  have hL0 : L ≠ 0 := by
    intro h
    have : ((l : ℕ) : Qbar l) = 0 := by rw [← hLval, h]; rfl
    have h1 := (norm_natCast_l (l := l))
    rw [this, norm_zero] at h1
    have : (0:ℝ) < (l:ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
    linarith
  have hLnu : ¬ IsUnit L := by
    rintro ⟨u, hu⟩
    have h1 : ((u : c.O) : Qbar l) * ((u⁻¹ : c.Oˣ) : c.O) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
    have hn2 : ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ ≤ 1 := norm_le_one_of_mem_coef c (SetLike.coe_mem _)
    have hu' : ((u : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by rw [hu, hLval]
    rw [hu'] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have h3 := norm_natCast_l_lt_one (l := l)
    have h4 : ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hn2) h3
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨v, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨m, u', hLu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hL0 hϖ
  have hm : m ≠ 0 := by
    rintro rfl
    apply hLnu
    rw [hLu, pow_zero, mul_one]; exact u'.isUnit
  have hϖL : ϖ ∣ L := by
    rw [hLu]
    exact Dvd.dvd.mul_left (dvd_pow_self ϖ hm) _
  have hdiv : x ∣ L ^ v := by
    rw [hxu]
    exact (Units.mul_left_dvd).2 (pow_dvd_pow_of_dvd hϖL v)
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨v, ?_⟩
  have hq' : ((l : ℕ) : Qbar l) ^ v = d * (q : Qbar l) := by
    have := congrArg (fun y : c.O => (y : Qbar l)) hq
    simpa [hLval, hxdef] using this
  rw [hq', mul_comm d, mul_assoc, mul_inv_cancel₀ hd0, mul_one]
  exact q.2

end GlobalTheory.Ord2

end
end
