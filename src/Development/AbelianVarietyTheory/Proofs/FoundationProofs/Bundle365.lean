module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle353
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle355
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle356
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
public import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoLOfEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle358
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
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp.KinfCompact

section Mat

variable {p q n : ℕ} {A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ}
  {G m : Matrix (Fin n) (Fin n) ℂ}

end Mat

variable {D : D7}

theorem isClosed_realPts (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  have : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  exact isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const

theorem continuous_realMat {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    Continuous fun h => infMat D.sp.cm.sig V.gram (θ τ) h := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ τ = θ₀ (tauE D τ) := SmoothForms.RealPts.infEmb_unique _ _ _ (hθ τ) (hθ₀ _)
  rw [e]
  exact ((GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1 (tauE D τ)).2.2.2.1

end GlobalTheory.Cusp.KinfCompact

end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem sum_act_upper_rep : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (N l : ℕ) [Fact l.Prime] (q M : ℕ), 0 < q → Nat.Coprime q M → ∀ b : X.Fn l,
    (∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b) →
    ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] b =
      ∑ j ∈ Finset.range q, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b := by
  intro Ω _ _ _ ε X N l _ q M hq hqM b hb
  have hT : ∀ t : ℤ, X.act l !![1, t; 0, 1] b = b := by
    intro t
    let T : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hmem : T ∈ Gam N l := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [CongruenceSubgroup.Gamma1_mem]
        refine ⟨?_, ?_, ?_⟩ <;> simp [T]
      · rw [CongruenceSubgroup.Gamma0_mem]
        simp [T]
    exact hb T hmem
  have he : IsCoprime (M : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd_natCast_natCast] using hqM.symm
  exact (Tower.sum_act_upper_mul_unit X l b hT q (M : ℤ) hq he).symm

end GlobalTheory.KZ.ES
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b) = X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) := by
  first | exact @GlobalTheory.KZ.GammaZeroComm.galB_act_comm | exact GlobalTheory.KZ.GammaZeroComm.galB_act_comm | (intros; apply GlobalTheory.KZ.GammaZeroComm.galB_act_comm <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.galoisAction_upperTriangular_hecke_reindex_on_B : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ) (e : ℤ), 0 < q → (∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e) → ∀ (j : ℤ), ∀ b ∈ X.B N l w, X.galB l s (X.act l !![1, j; 0, (q : ℤ)] b) = X.act l !![1, j * e; 0, (q : ℤ)] (X.galB l s b) := by
  first | exact @GlobalTheory.KZ.GalUpper.galB_act_upper | exact GlobalTheory.KZ.GalUpper.galB_act_upper | (intros; apply GlobalTheory.KZ.GalUpper.galB_act_upper <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.galois_commutes_hecke_action : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ b ∈ X.BSet N l w, ∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, ∀ s : Ω ≃ₐ[ℚ] Ω, X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  first | exact @GlobalTheory.KZ.GamComm.act_galB_comm | exact GlobalTheory.KZ.GamComm.act_galB_comm | (intros; apply GlobalTheory.KZ.GamComm.act_galB_comm <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.cupProductDualTwist_isTwoCocycle_unramified : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (W : R2 Ω l) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → ContainsAbove S l → (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) → a ∈ Z1 (Loc.colRep W) → b ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, a s i ∈ c.O) → (∀ s i, b s i ∈ c.O) → Unr W a → Unr (dual1 W) b → Coc2 c n S (cup W a b) := by
  first | exact @GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt | exact GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt | (intros; apply GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_commutator_det_nonzero : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ φ ∈ ⁅H0g W, H0g W⁆, (mat W φ - 1).det ≠ 0 := by
  first | exact @GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one | exact GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one | (intros; apply GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

theorem _root_.GlobalTheory.T.exists_kummer_element_fixed_field_closed_subgroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (H : Subgroup (G ℚ Ω)), IsClosed (H : Set (G ℚ Ω)) → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → (∀ s ∈ H, s ζ = ζ) → ∀ χ : G ℚ Ω → ZMod (l ^ m), (∀ s ∈ H, ∀ t ∈ H, χ (s * t) = χ s + χ t) → ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → (∀ s ∈ H, s ∈ U → χ s = 0) → ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ H, s u = u) ∧ ∀ s ∈ H, GlobalTheory.Col.KumVal (l := l) m ζ u s (χ s) := by
  first | exact @GlobalTheory.KumFix.exists_kumVal | exact GlobalTheory.KumFix.exists_kumVal | (intros; apply GlobalTheory.KumFix.exists_kumVal <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

theorem _root_.GlobalTheory.T.exists_inertiaFixed_near_almostFixed_coefficients : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ c₁ : ℕ, ∀ (k : ℕ) (x : Qbar l), ‖x‖ ≤ 1 →
  (∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → Cg k (σ x) x) →
  ∃ x' : Qbar l, ‖x'‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c x' ∧ Cg (k - c₁) x x' := by
  first | exact @GlobalTheory.PerFix.exists_fixed_near | exact GlobalTheory.PerFix.exists_fixed_near | (intros; apply GlobalTheory.PerFix.exists_fixed_near <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KZ.Cmp

variable {l : ℕ} [Fact l.Prime]

def chSum (F : PowerSeries (Qbar l)) (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Qbar l :=
  ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval F (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val)

def gSum (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Qbar l :=
  ∑ b : (ZMod (l ^ m))ˣ, ψ b * z ^ (b : ZMod (l ^ m)).val

def rSum (φ : DirichletCharacter (Qbar l) l) (e : ℕ) (F : PowerSeries (Qbar l)) (r : ℕ) (ξ : Qbar l) : Qbar l :=
  ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass F r ξ x

def InComp (φ : DirichletCharacter (Qbar l) l) (e : ℕ) {m : ℕ} (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Prop :=
  ∀ b : (ZMod (l ^ m))ˣ, b ^ (l - 1) = 1 →
    ‖ψ⁻¹ (b : ZMod (l ^ m)) - (((b : ZMod (l ^ m)).val : Qbar l) ^ e) * φ (((b : ZMod (l ^ m)).val : ℕ) : ZMod l)‖ < 1

theorem tval_sub_C_mul (F G : PowerSeries (Qbar l)) (a : Qbar l) (N : ℕ) (z : Qbar l) :
    tval (F - PowerSeries.C a * G) N z = tval F N z - a * tval G N z := by
  unfold tval
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_sub, PowerSeries.coeff_C_mul]; ring

theorem tval_C_mul (G : PowerSeries (Qbar l)) (a : Qbar l) (N : ℕ) (z : Qbar l) :
    tval (PowerSeries.C a * G) N z = a * tval G N z := by
  unfold tval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [PowerSeries.coeff_C_mul]; ring

end GlobalTheory.KZ.Cmp
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

namespace GlobalTheory.LambdaValuationPowers

theorem htCoL_sum : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (c : Coef l) (j : Ω →+* Qbar l)
    (ι : Type) [Fintype ι] (a : ι → Qbar l) (Z : ι → ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ)
    (y : (ZMod (l ^ m))ˣ) (h : ι → Qbar l),
    (∀ i, ‖a i‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c (a i)) → (∀ i, GlobalTheory.LambdaValuationPowers.HTCoL A c j (Z i) m c₀ y (h i)) →
    GlobalTheory.LambdaValuationPowers.HTCoL A c j (fun r s y' => ∑ i, a i * Z i r s y') m c₀ y (∑ i, a i * h i) := by
  intro l _ Ω _ _ A c j ι _ a Z m c₀ y h ha hZ
  choose q o w hint hcg using hZ
  let e : Fin (Fintype.card (Σ i, Fin (q i))) ≃ (Σ i, Fin (q i)) := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Σ i, Fin (q i)), fun k => a (e k).1 * o (e k).1 (e k).2, fun k => w (e k).1 (e k).2, ?_, ?_⟩
  · intro k
    obtain ⟨h1, h2, h3⟩ := hint (e k).1 (e k).2
    refine ⟨?_, ?_, h3⟩
    · rw [norm_mul]; exact mul_le_one₀ (ha _).1 (norm_nonneg _) h1
    · intro σ hσ hσ'
      rw [map_mul, (ha _).2 σ hσ hσ', h2 σ hσ hσ']
  · intro s hs hcyc
    have hre : (∑ k : Fin (Fintype.card (Σ i, Fin (q i))), a (e k).1 * o (e k).1 (e k).2 * (j (s (w (e k).1 (e k).2)) - j (w (e k).1 (e k).2)))
        = ∑ i, a i * ∑ r, o i r * (j (s (w i r)) - j (w i r)) := by
      rw [Equiv.sum_comp e (fun x => a x.1 * o x.1 x.2 * (j (s (w x.1 x.2)) - j (w x.1 x.2)))]
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    unfold Cg
    rw [hre]
    have key : (l : Qbar l) ^ c₀ * (∑ i, a i * Z i m s y) -
        ((l : Qbar l) ^ c₀ * (∑ i, a i * h i) * lamv l m s + ∑ i, a i * ∑ r, o i r * (j (s (w i r)) - j (w i r)))
        = ∑ i, a i * ((l : Qbar l) ^ c₀ * Z i m s y - ((l : Qbar l) ^ c₀ * h i * lamv l m s + ∑ r, o i r * (j (s (w i r)) - j (w i r)))) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_sub, mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [key]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul]
    have := hcg i s hs hcyc
    unfold Cg at this
    calc ‖a i‖ * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (ha i).1 (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact this

end GlobalTheory.LambdaValuationPowers
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.defGram_selfDual_after_field_embedding : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) → ∀ (ι : Type) (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) → ∀ τ, IsDefGram (gramK emb J τ) ∧ IsDefGram (gramKd emb J τ) ∧ ∀ L : Submodule (𝓞 E) (Fin n → E), IsSelfDualE cE J L → IsSelfDualK (gramK emb J τ) (tauLat emb τ L) ∧ IsSelfDualK (gramKd emb J τ) (dualFr (tauLat emb τ L)) := by
  first | exact @GlobalTheory.TestLat.defGram_selfDual_of_embedding | exact GlobalTheory.TestLat.defGram_selfDual_of_embedding | (intros; apply GlobalTheory.TestLat.defGram_selfDual_of_embedding <;> assumption)
end
