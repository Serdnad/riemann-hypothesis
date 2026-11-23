module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle891
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle892
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial TensorProduct

namespace GlobalTheory.ChainStab

theorem hw_rowHom (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    ∃ μ : Fin r → ℕ, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (Formalism.GradedWeylDivisibility.hw R hn ν) μ := by
  unfold Formalism.GradedWeylDivisibility.hw
  exact ⟨_, IsWeightedHomogeneous.prod _ _ _ fun s _ => (Formalism.GradedWeylDivisibility.lpMinor_rowHom R _ _ _).pow _⟩

theorem homZ_of_homN {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℕ)
    (h : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f μ) :
    IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f (fun i => (μ i : ℤ)) := by
  intro m hm
  rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast, h hm]

theorem applyWord_homZ {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ)
    (hf : IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f μ) (w : List (Fin r × Fin r × ℕ)) :
    ∃ μ' : Fin r → ℤ, IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) (Formalism.GradedWeylDivisibility.applyWord R w f) μ' := by
  induction w with
  | nil => exact ⟨μ, hf⟩
  | cons x w ih =>
    obtain ⟨μ', h⟩ := ih
    exact ⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_G_of_homog x.1 x.2.1 _ μ' h x.2.2⟩

theorem comp_of_homZ {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ)
    (hf : IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f μ) (m : Fin r → ℕ) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f = f ∨
      weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f = 0 := by
  classical
  by_cases hg : f = 0
  · right; rw [hg, map_zero]
  · obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.1 hg
    have hN : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m0) := by
      intro d hd
      have h1 := hf hd
      have h2 := hf hm0
      rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast] at h1 h2
      funext i
      exact_mod_cast congrFun (h1.trans h2.symm) i
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hN)]
    split_ifs
    · left; rfl
    · right; rfl

theorem weyl_comp_mem (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (m : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  obtain ⟨μ0, h0⟩ := hw_rowHom R hn ν
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨μ, hμ⟩ := applyWord_homZ _ _ (homZ_of_homN _ _ h0) w
    rcases comp_of_homZ _ μ hμ m with h | h <;> rw [h]
    · exact Submodule.subset_span ⟨w, rfl⟩
    · exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem tprod_mem_tensSub {O : Type} [CommRing O] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module O (A i)] (B : ∀ i, Submodule O (A i)) (x : ∀ i, A i) (hx : ∀ i, x i ∈ B i) :
    PiTensorProduct.tprod O x ∈ tensSub B :=
  LinearMap.mem_range.2 ⟨PiTensorProduct.tprod O (fun i => ⟨x i, hx i⟩), by rw [PiTensorProduct.map_tprod]; rfl⟩

theorem map_mem_tensSub {O : Type} [CommRing O] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module O (A i)] (B : ∀ i, Submodule O (A i)) (f : ∀ i, A i →ₗ[O] A i)
    (hf : ∀ i, ∀ x ∈ B i, f i x ∈ B i) (y : ⨂[O] i, A i) (hy : y ∈ tensSub B) :
    PiTensorProduct.map f y ∈ tensSub B := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
  refine LinearMap.mem_range.2 ⟨PiTensorProduct.map (fun i => (f i).restrict (hf i)) z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  rfl

variable {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] {lam : ι → ℕ → ℕ}

theorem grp_stab (s : Finset ι) (g : ι → GL (Fin N) O) :
    ∀ y ∈ tensSub (chainB (deltaIn O N lam) s), grp O N lam g y ∈ tensSub (chainB (deltaIn O N lam) s) := by
  intro y hy
  have h1 : grp O N lam g = PiTensorProduct.map
      (fun i => Formalism.UG.dualWeylRep O N N (res N (lam i)) (g i)) := rfl
  rw [h1]
  refine map_mem_tensSub _ _ (fun i x hx => ?_) y hy
  unfold chainB at hx ⊢
  split_ifs at hx ⊢ with hi
  · exact Submodule.mem_top
  · exact Formalism.UG.P.weyl_module_GL_stable O N N le_rfl (res N (lam i)) (g i) x.1 hx

theorem proj_stab (s : Finset ι) (τ : ι) (w : Fin N → ℕ) (a : Module.End O (NablaT O N lam))
    (ha : IsProj O N lam τ w a) :
    ∀ y ∈ tensSub (chainB (deltaIn O N lam) s), a y ∈ tensSub (chainB (deltaIn O N lam) s) := by
  intro y hy
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    rw [map_smul, PiTensorProduct.map_tprod, map_smul]
    refine Submodule.smul_mem _ c ?_
    let x : ∀ i, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i)) := fun i => (f i : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i)))
    have hc := Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N (res N (lam τ)) w _ (x τ).2
    change a (PiTensorProduct.tprod O x) ∈ _
    rw [ha x ⟨_, hc⟩ rfl]
    apply tprod_mem_tensSub
    intro i
    by_cases hi : i = τ
    · subst hi
      rw [Function.update_self]
      have hf := (f i).2
      unfold chainB at hf ⊢
      split_ifs at hf ⊢ with hs
      · exact Submodule.mem_top
      · exact weyl_comp_mem O le_rfl (res N (lam i)) w _ hf
    · rw [Function.update_of_ne hi]
      exact (f i).2
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ (h₁ (LinearMap.mem_range_self _ _)) (h₂ (LinearMap.mem_range_self _ _))

end GlobalTheory.ChainStab

namespace GlobalTheory.ExpFrame

open GlobalTheory.ChainStab

theorem alg_chainB_stable : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (s : Finset ι) (a : alg O N lam),
    ∀ x ∈ tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s), a • x ∈ tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s) := by
  intro O _ _ _ _ N ι _ _ lam s a
  let L := tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s)
  let St : Subalgebra O (Module.End O (NablaT O N lam)) :=
    { carrier := {f | ∀ x ∈ L, f x ∈ L}
      mul_mem' := fun ha hb x hx => ha _ (hb x hx)
      add_mem' := fun ha hb x hx => L.add_mem (ha x hx) (hb x hx)
      algebraMap_mem' := fun c x hx => by
        rw [Module.algebraMap_end_apply]; exact L.smul_mem c hx }
  have hle : alg O N lam ≤ St := Algebra.adjoin_le (by
    rintro f (⟨g, rfl⟩ | ⟨τ, w, hf⟩)
    · exact grp_stab s g
    · exact proj_stab s τ w f hf)
  intro x hx
  exact hle a.2 x hx

end GlobalTheory.ExpFrame

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord defTerm)
open GlobalTheory.CMVal (modUnits unitRel)

namespace GlobalTheory.HilbFam.BrVal

theorem card_realEmb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
  · intro τ τ' hτ
    ext y
    have := DFunLike.congr_fun hτ y
    simpa using this
  · intro φ
    have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
    exact ⟨hr.embedding, by ext y; simp⟩

theorem prod_cpow_ofReal {J : Type} (s : Finset J) (f : J → ℝ) (hf : ∀ i, 0 ≤ f i) (r : ℂ) :
    ∏ i ∈ s, ((f i : ℝ) : ℂ) ^ r = (((∏ i ∈ s, f i : ℝ)) : ℂ) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i)]

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem defTerm_eq (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (σ : ℂ) (x : E) :
    defTerm φ k z σ x =
      (∏ i, defCoord φ z x i)⁻¹ ^ k * ((‖∏ i, defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ) := by
  unfold defTerm
  rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, norm_prod,
    prod_cpow_ofReal _ _ (fun _ => norm_nonneg _)]

theorem defCoord_mul (φ : I → E →+* ℂ) (z : I → ℂ) (a x : E) (i : I) (ha : starRingEnd ℂ (φ i a) = φ i a) :
    defCoord φ z (a * x) i = φ i a * defCoord φ z x i := by
  simp only [defCoord, map_mul, ha]; ring

end GlobalTheory.HilbFam.BrVal

namespace GlobalTheory.HilbFam.BrVal

theorem isGVal_of_isEisValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (k : ℕ) (z : I → ℂ) (G : ℂ), Nonempty I → Even k → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsEisValue φ k Λ z G → IsGVal k L (fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + z (e.symm j) * 1) ((((n : ℂ) ^ Module.finrank ℚ (FR E))⁻¹) ^ k * G) := by
  intro E _ _ _ I _ _ φ e θ τ Λ L n k z G hI hk hφ hθ hn hL hG
  obtain ⟨i0⟩ := hI
  set T : (Fin 2 → FR E) → E := fun x ↦ (x 0 : E) * θ + (x 1 : E) with hT
  have hTb : Function.Bijective T := GlobalTheory.HilbFam.EBasis.bijective_pair E (φ i0) θ (by
    rw [hθ i0, UpperHalfPlane.coe_im]; exact (UpperHalfPlane.im_pos τ).ne')
  have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set B : (Fin 2 → FR E) → E := fun x ↦ (n : E)⁻¹ * T x with hB
  have hBinj : Function.Injective B := fun x y h ↦ hTb.1 (mul_left_cancel₀ (inv_ne_zero hnE) h)
  have hB0 : B 0 = 0 := by simp [hB, hT]
  have hLB : ∀ x, x ∈ L ↔ B x ∈ Λ := by
    intro x
    rw [hL x]
    constructor
    · rintro ⟨y, hy, hny⟩
      have : B x = y := by
        show (n : E)⁻¹ * ((x 0 : E) * θ + (x 1 : E)) = y
        rw [← hny, ← mul_assoc, inv_mul_cancel₀ hnE, one_mul]
      rw [this]; exact hy
    · intro h
      exact ⟨B x, h, by
        show (n : E) * ((n : E)⁻¹ * ((x 0 : E) * θ + (x 1 : E))) = _
        rw [← mul_assoc, mul_inv_cancel₀ hnE, one_mul]⟩
  have hBu : ∀ (u : (OF E)ˣ) (x : Fin 2 → FR E), B (u • x) = algebraMap (OF E) E (u : OF E) * B x := by
    intro u x
    have h0 : ∀ j, (((u • x) j : FR E) : E) = (((u : OF E) : FR E) : E) * ((x j : FR E) : E) := by
      intro j
      rw [Pi.smul_apply, Units.smul_def, Algebra.smul_def]
      rfl
    simp only [hB, hT, h0]
    show _ = (((u : OF E) : FR E) : E) * _
    ring
  have hcoord : ∀ (x : Fin 2 → FR E) (i : I),
      coord (fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + z (e.symm j) * 1) x (e i)
        = (n : ℂ) * defCoord φ z (B x) i := by
    intro x i
    have h1 : T x = (n : E) * B x := by simp only [hB]; rw [← mul_assoc, mul_inv_cancel₀ hnE, one_mul]
    have h2 : defCoord φ z (T x) i = (n : ℂ) * defCoord φ z (B x) i := by
      rw [h1, defCoord_mul φ z _ _ i (by simp)]; simp
    rw [← h2]
    simp only [coord, defCoord, hT, map_add (f := _), map_mul, hφ, hθ, Equiv.symm_apply_apply, Complex.conj_ofReal]
    ring
  set b : Emb (FR E) → ℂ := fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ)) with hb
  set a : Emb (FR E) → ℂ := fun j ↦ 1 + z (e.symm j) * 1 with ha
  set d := Module.finrank ℚ (FR E) with hd
  have hcard : Fintype.card I = d := by
    rw [Fintype.card_congr e, hd, ← card_realEmb (FR E)]
  have hprod : ∀ x, ∏ j, coord b a x j = ((n : ℂ) ^ d) * ∏ i, defCoord φ z (B x) i := by
    intro x
    rw [← Equiv.prod_comp e]
    simp only [hcoord, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  set c : ℂ → ℂ := fun σ ↦ (((n : ℂ) ^ d)⁻¹) ^ k * ((((n : ℝ) ^ d : ℝ)) : ℂ) ^ (-2 * σ) with hc
  have hterm : ∀ σ x, gTerm k σ b a x = c σ * defTerm φ k z σ (B x) := by
    intro σ x
    rw [defTerm_eq, gTerm, hprod, hc]
    simp only
    rw [_root_.mul_inv, _root_.mul_pow, norm_mul, norm_pow, Complex.norm_natCast, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
    ring
  have hBne : ∀ x, x ≠ 0 → B x ≠ 0 := fun x hx h ↦ hx (hBinj (h.trans hB0.symm))
  let ι : cls L → modUnits Λ := fun q ↦ ⟨Quotient.mk _ (B q.1.out), B q.1.out, (hLB _).1 q.2.1, hBne _ q.2.2, rfl⟩
  have hinj : Function.Injective ι := by
    intro q1 q2 h
    have h' : Quotient.mk (unitRel (E := E)) (B q1.1.out) = Quotient.mk _ (B q2.1.out) := congrArg Subtype.val h
    obtain ⟨u, hu⟩ := Quotient.exact h'
    rw [← hBu] at hu
    have hx := hBinj hu
    apply Subtype.ext
    rw [← Quotient.out_eq q1.1, ← Quotient.out_eq q2.1]
    exact (Quotient.sound (MulAction.mem_orbit_iff.2 ⟨u, hx.symm⟩)).symm
  have hsurj : Function.Surjective ι := by
    rintro ⟨p, y, hy, hy0, hp⟩
    obtain ⟨x, hx⟩ := hTb.2 ((n : E) * y)
    have hBx : B x = y := by
      show (n : E)⁻¹ * T x = y
      rw [hx, ← mul_assoc, inv_mul_cancel₀ hnE, one_mul]
    have hxL : x ∈ L := (hLB x).2 (hBx ▸ hy)
    have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (hBx ▸ hB0)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (𝓞 (FR E))ˣ (Fin 2 → FR E)) x)))
    set q0 := Quotient.mk (MulAction.orbitRel (𝓞 (FR E))ˣ (Fin 2 → FR E)) x with hq0
    have hmem : q0 ∈ cls L := by
      refine ⟨?_, ?_⟩
      · rw [← hg, Units.smul_def]; exact L.smul_mem _ hxL
      · rw [← hg]; intro h0; exact hx0 ((smul_eq_zero_iff_eq g).1 h0)
    refine ⟨⟨q0, hmem⟩, ?_⟩
    apply Subtype.ext
    show Quotient.mk _ (B q0.out) = p
    rw [← hp, ← hg, hBu g x, hBx]
    exact (Quotient.sound (show (unitRel (E := E)).r y (algebraMap (OF E) E (g : OF E) * y) from ⟨g, rfl⟩)).symm
  have hval : ∀ σ (q : cls L), gTerm k σ b a q.1.out = c σ * defTerm φ k z σ (ι q).1.out := by
    intro σ q
    obtain ⟨u, hu⟩ : (unitRel (E := E)).r (B q.1.out) (ι q).1.out :=
      Quotient.exact (Quotient.out_eq (ι q).1).symm
    rw [hu, ← hBu, ← hterm, GlobalTheory.HilbFam.gTerm_unit_smul (FR E) k σ b a u q.1.out hk]
  have hsum : ∀ σ S, HasSum (fun p : modUnits Λ ↦ defTerm φ k z σ p.1.out) S →
      HasSum (fun q : cls L ↦ gTerm k σ b a q.1.out) (c σ * S) := by
    intro σ S h
    simp only [hval]
    exact ((Equiv.hasSum_iff (Equiv.ofBijective ι ⟨hinj, hsurj⟩)).2 h).mul_left (c σ)
  have hc0 : c 0 = (((n : ℂ) ^ d)⁻¹) ^ k := by simp [hc]
  refine ⟨fun hk2 ↦ ?_, fun hk2 ↦ ?_⟩
  · have hd0 : ∀ x : E, defTerm φ k z 0 x = ∏ i, (defCoord φ z x i)⁻¹ ^ k := by
      intro x; simp [defTerm]
    rw [← hc0]
    refine hsum 0 G ?_
    simp only [hd0]
    exact hG.1 hk2
  · obtain ⟨H, hHd, hHs, hH0⟩ := hG.2 hk2
    subst hk2
    have hn' : ((((n : ℝ) ^ d : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
    have hcd : Differentiable ℂ c := fun σ ↦
      (differentiableAt_const _).mul (((differentiableAt_const (-2 : ℂ)).mul differentiableAt_id).const_cpow (Or.inl hn'))
    refine ⟨fun σ ↦ c σ * H σ, hcd.differentiableOn.mul hHd, fun σ hσ ↦ hsum σ _ (hHs σ hσ), ?_⟩
    rw [hH0, ← hc0]

end GlobalTheory.HilbFam.BrVal
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hasSum_iteratedDeriv_hilbertEisenstein_splitLattice : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (u : List (Emb F)), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, lag k (u.count i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)) (iterD u (fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  first | exact @GlobalTheory.HilbFam.hasSum_iterD_gval_split | exact GlobalTheory.HilbFam.hasSum_iterD_gval_split | (intros; apply GlobalTheory.HilbFam.hasSum_iterD_gval_split <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (f : C →ₐc[k] A), Function.Surjective f ↔ Module.finrank k (A ⧸ kerIdeal f) = 1 := by
  first | exact @GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one | exact GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one | (intros; apply GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.exists_quotient_finiteCommGroupScheme_closedSubgroup : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : A →ₐc[k] C), Function.Surjective π → ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra k B) (_ : IsCocomm k B) (_ : Module.Finite k B) (j : B →ₐc[k] A), Function.Injective j ∧ kerIdeal j = RingHom.ker π ∧ ∀ (D : Type) [CommRing D] [Bialgebra k D] (f : D →ₐc[k] A), kerIdeal f ≤ RingHom.ker π → ∀ d, f d ∈ Set.range j := by
  first | exact @GlobalTheory.HopfQuot.exists_quotient | exact GlobalTheory.HopfQuot.exists_quotient | (intros; apply GlobalTheory.HopfQuot.exists_quotient <;> assumption)
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open GlobalTheory.EtC

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma isEmpty_of_isUnit_zero (U : Scheme) (h : IsUnit (0 : Γ(U, ⊤))) : IsEmpty U := by
  constructor
  intro x
  have h01 : (0 : Γ(U, ⊤)) = 1 := isUnit_zero_iff.1 h
  have := congrArg (U.presheaf.germ ⊤ x trivial).hom h01
  rw [map_zero, map_one] at this
  exact zero_ne_one this

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma isEmpty_of_prim_zero (U : Scheme)
    (ζ : _root_.GlobalTheory.EtC.Prim 0 Γ(U, ⊤)) : IsEmpty U :=
  isEmpty_of_isUnit_zero U (by simpa using ζ.2.1)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma sec_eq_of_isEmpty' {R : Type} [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R) (U : Scheme)
    [IsEmpty U] (a b : _root_.GlobalTheory.EtC.Sec F U) : a = b :=
  (_root_.GlobalTheory.EtC.sec_ext_glue R F U).1 a b
    ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun _ _ h => h.elim⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.twPair_spec (q : ℕ) (i j : ℤ) :
    _root_.GlobalTheory.EtC.IsTwPair (_root_.GlobalTheory.EtC.twPair q i j) := by
  by_cases hq : q = 0
  · subst hq
    unfold _root_.GlobalTheory.EtC.IsTwPair
    intro U ζ
    haveI := isEmpty_of_prim_zero U ζ
    exact sec_eq_of_isEmpty' _ _ _ _
  · haveI : NeZero q := ⟨hq⟩
    exact (_root_.GlobalTheory.EtC.TwPairUniq.main q i j).1

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.kumT_spec (q : ℕ) : _root_.GlobalTheory.EtC.IsKum q (_root_.GlobalTheory.EtC.kumT q) := by
  by_cases hq : q = 0
  · subst hq
    unfold _root_.GlobalTheory.EtC.IsKum
    refine ⟨fun V U g v h => ?_, fun U ζ v w _ => ?_⟩
    · haveI := isEmpty_of_isUnit_zero U (by simpa using h)
      haveI : IsEmpty V := ⟨fun x => IsEmpty.false (g.base x)⟩
      exact sec_eq_of_isEmpty' _ _ _ _
    · haveI := isEmpty_of_prim_zero U ζ
      exact sec_eq_of_isEmpty' _ _ _ _
  · haveI : NeZero q := ⟨hq⟩
    exact _root_.GlobalTheory.EtC.KummerSplit.isKum_kumT q

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.restrMap_spec {S R : Type} [CommRing S] [CommRing R] (φ : R →+* S)
    (F : _root_.GlobalTheory.EtC.Shv S) (U : Scheme.{0}) (a : _root_.GlobalTheory.EtC.Sec F U) :
    (_root_.GlobalTheory.EtC.restrMap φ F).app U 0
        (_root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι S F) a) =
      _root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι R ((_root_.GlobalTheory.EtC.restr φ).obj F))
        (show _root_.GlobalTheory.EtC.Sec ((_root_.GlobalTheory.EtC.restr φ).obj F) U from a) :=
  _root_.GlobalTheory.EtC.restrMap_spec' R S φ F U a

end GlobalTheory.EtC

end
end
