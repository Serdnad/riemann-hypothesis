module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle185
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine

structure CoverW {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V) : Prop where
  adj : ∀ P x, ∃ b, ∀ y, ⟪R₁.ι x, R₁.ι (B P y)⟫_ℂ = ⟪R₂.ι y, R₂.ι b⟫_ℂ
  src : ∀ Z ∈ upq p q, ∀ P y, B (fockAct1 p q r s Z P) y = R₁.HK.act Z (B P y)
  tgt : ∀ Z ∈ upq r s, ∀ P y, B (fockAct2 p q r s Z P) y + B P (R₂.HK.act Z y) = 0

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure SemiW (τ : D.what₂.Tau) (aS aT : ℚ) (A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ) : Prop where
  bdd : ∀ φ u, ∃ c : ℝ, ∀ y : M'.sm τ, ‖⟪u, A φ y⟫_ℂ‖ ≤ c * ‖(y : M'.H τ)‖
  eqK : ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ φ, ∃ φ', φ'.totalDegree ≤ φ.totalDegree ∧ ∀ y, A φ' y = M.σ τ h (A φ y)
  invK : ∀ k ∈ Formalism.REAL.Kset (M'.ε τ), ∀ φ, ∃ φ', φ'.totalDegree ≤ φ.totalDegree ∧
    ∀ y y' : M'.sm τ, (y' : M'.H τ) = M'.σ τ k y → A φ' y' = A φ y
  src : ∀ X ∈ lieAt V τ, ∀ φ y u, HasDerivAt (fun t : ℝ => ⟪u, M.rep τ (NormedSpace.exp (t • X)) (A φ y)⟫_ℂ)
    ⟪u, A (srcOp M M' τ aT X φ) y⟫_ℂ 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ φ (y y' : M'.sm τ),
    HasDerivAt (fun t : ℝ => M'.rep τ (NormedSpace.exp (t • Y)) y) (y' : M'.H τ) 0 →
      A (tgtOp M M' τ aS Y φ) y + A φ y' = 0

structure LocW (τ : D.what₂.Tau) (aS aT : ℚ) (A : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ) : Prop where
  kS : ∀ P y, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) (A P y)
  kT : ∀ P u, ∃ b : M'.H τ, Formalism.MainNotions.S.IsKFin (M'.ε τ) (M'.σ τ) b ∧ ∀ y : M'.sm τ, ⟪u, A P y⟫_ℂ = ⟪b, (y : M'.H τ)⟫_ℂ
  src : ∀ X ∈ lieAt V τ, ∀ P y u, HasDerivAt (fun t : ℝ => ⟪u, M.rep τ (NormedSpace.exp (t • X)) (A P y)⟫_ℂ)
    ⟪u, A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * X.trace) • P) y⟫_ℂ 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ P (y y' : M'.sm τ),
    HasDerivAt (fun t : ℝ => M'.rep τ (NormedSpace.exp (t • Y)) y) (y' : M'.H τ) 0 →
      A (locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y + A P y' = 0

theorem eq_mul_prod_of_partial {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} (l : ∀ i, A i → ℂ)
    (F : (∀ i, A i) → ℂ) (h : ∀ i a, ∃ c : ℂ, ∀ x, F (Function.update a i x) = c * l i x) :
    ∃ c : ℂ, ∀ a, F a = c * ∏ i, l i (a i) := by

  have key : ∀ (a : ∀ i, A i) (i : ι) (x : A i),
      F (Function.update a i x) * l i (a i) = F a * l i x := by
    intro a i x
    obtain ⟨c, hc⟩ := h i a
    have h1 := hc (a i)
    rw [Function.update_eq_self] at h1
    rw [hc x, h1]
    ring
  by_cases hF : ∀ a, F a = 0
  · exact ⟨0, fun a => by simp [hF a]⟩
  push_neg at hF
  obtain ⟨a₀, ha₀⟩ := hF
  have hl : ∀ i, l i (a₀ i) ≠ 0 := by
    intro i hi
    obtain ⟨c, hc⟩ := h i a₀
    have h1 := hc (a₀ i)
    rw [Function.update_eq_self, hi, mul_zero] at h1
    exact ha₀ h1

  have main : ∀ s : Finset ι, ∀ a : ∀ i, A i, (∀ j, j ∉ s → a j = a₀ j) →
      F a * ∏ j ∈ s, l j (a₀ j) = F a₀ * ∏ j ∈ s, l j (a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha
      rw [show a = a₀ from funext fun j => ha j (by simp)]
    | @insert i s hi ih =>
      intro a ha
      have hoff : ∀ j, j ∉ s → Function.update a i (a₀ i) j = a₀ j := by
        intro j hj
        by_cases hji : j = i
        · subst hji
          simp
        · rw [Function.update_of_ne hji]
          exact ha j (by simp [hji, hj])
      have e1 := ih _ hoff
      have e2 := key (Function.update a i (a₀ i)) i (a i)
      simp only [Function.update_idem, Function.update_eq_self, Function.update_self] at e2
      have hprod : ∏ j ∈ s, l j (Function.update a i (a₀ i) j) = ∏ j ∈ s, l j (a j) :=
        Finset.prod_congr rfl fun j hj => by
          have hji : j ≠ i := fun e => hi (e ▸ hj)
          rw [Function.update_of_ne hji]
      rw [hprod] at e1
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      calc F a * (l i (a₀ i) * ∏ j ∈ s, l j (a₀ j))
          = (F a * l i (a₀ i)) * ∏ j ∈ s, l j (a₀ j) := by ring
        _ = (F (Function.update a i (a₀ i)) * l i (a i)) * ∏ j ∈ s, l j (a₀ j) := by rw [e2]
        _ = l i (a i) * (F (Function.update a i (a₀ i)) * ∏ j ∈ s, l j (a₀ j)) := by ring
        _ = l i (a i) * (F a₀ * ∏ j ∈ s, l j (a j)) := by rw [e1]
        _ = F a₀ * (l i (a i) * ∏ j ∈ s, l j (a j)) := by ring
  have hP : ∏ j, l j (a₀ j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hl j
  refine ⟨F a₀ / ∏ j, l j (a₀ j), fun a => ?_⟩
  rw [div_mul_eq_mul_div, eq_div_iff hP]
  exact main Finset.univ a fun j hj => absurd (Finset.mem_univ j) hj

end GlobalTheory.Chain.RealLine

end
end

section

noncomputable section

namespace GlobalTheory.MonomialRangeMembership

open MvPolynomial

theorem monomial_mem_range_glue {D : Formalism.BasicNotions.D7} {a b : ℕ}
    (m : Formalism.IndefR.Datum.FVar D b a →₀ ℕ) :
    (monomial m (1 : ℂ) : Formalism.IndefR.Links.PolF D b a) ∈
      Set.range (GlobalTheory.Chain.RealIt.glue (D := D) (a := a) (b := b)) := by
  refine ⟨fun τ => ∏ s : Fin b × Fin a, X s ^ m (τ, s), ?_⟩
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  unfold GlobalTheory.Chain.RealIt.glue
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [map_prod, map_pow, rename_X]

theorem span_range_glue : ∀ {D : Formalism.BasicNotions.D7} {a b : Nat}, @Eq (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.span Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing) (@Set.range (Formalism.IndefR.Links.PolF D b a) (@Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.what₂ D) → GlobalTheory.Chain.RealIt.LPol b a) (@GlobalTheory.Chain.RealIt.glue D a b))) (@Top.top (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.instTop Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing))) := by
  intro D a b
  rw [eq_top_iff, ← (basisMonomials (Formalism.IndefR.Datum.FVar D b a) ℂ).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  rw [coe_basisMonomials]
  exact monomial_mem_range_glue m

end GlobalTheory.MonomialRangeMembership
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem exists_finite_support {ι : Type} {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    (x : ⨂[ℂ] i, E i) : ∃ F : ∀ i, Submodule ℂ (E i), (∀ i, FiniteDimensional ℂ (F i)) ∧
      ∀ G : ∀ i, Submodule ℂ (E i), (∀ i, F i ≤ G i) →
        x ∈ LinearMap.range (PiTensorProduct.map fun i => (G i).subtype) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine ⟨fun i => ℂ ∙ f i, fun i => inferInstance, fun G hG => ?_⟩
    refine LinearMap.mem_range.mpr
      ⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hG i (Submodule.mem_span_singleton_self (f i))⟩ : G i)), ?_⟩
    rw [map_smul, PiTensorProduct.map_tprod]
    rfl
  | add x y hx hy =>
    obtain ⟨F₁, h₁, k₁⟩ := hx
    obtain ⟨F₂, h₂, k₂⟩ := hy
    refine ⟨fun i => F₁ i ⊔ F₂ i, fun i => ?_, fun G hG => ?_⟩
    · haveI := h₁ i
      haveI := h₂ i
      infer_instance
    · exact add_mem (k₁ G fun i => le_trans le_sup_left (hG i)) (k₂ G fun i => le_trans le_sup_right (hG i))

theorem ellT_pure (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  unfold ellT
  rw [PiTensorProduct.lift.tprod]
  simp

private lemma eq_zero_of_ellT_map_eq_zero (M : DSModel V S) {K : D.what₂.Tau → Type} [∀ τ, NormedAddCommGroup (K τ)]
    [∀ τ, InnerProductSpace ℂ (K τ)] [hK : ∀ τ, FiniteDimensional ℂ (K τ)] (j : ∀ τ, K τ →ₗ[ℂ] M.H τ)
    (hj : ∀ τ a b, ⟪j τ a, j τ b⟫_ℂ = ⟪a, b⟫_ℂ) (z : ⨂[ℂ] τ, K τ)
    (hz : ∀ w, ellT M w (PiTensorProduct.map j z) = 0) : z = 0 := by
  classical
  let b := fun τ => stdOrthonormalBasis ℂ (K τ)
  let B := Basis.piTensorProduct (fun τ => (b τ).toBasis)
  have key : ∀ p, B.coord p = ellT M (fun τ => j τ (b τ (p τ))) ∘ₗ PiTensorProduct.map j := by
    intro p
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Module.Basis.coord_apply, B,
      Basis.piTensorProduct_repr_tprod_apply, PiTensorProduct.map_tprod, ellT_pure, hj,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  refine B.forall_coord_eq_zero_iff.mp fun p => ?_
  rw [key, LinearMap.comp_apply]
  exact hz _

theorem ellT_separates (M : DSModel V S) (x : ⨂[ℂ] τ, M.H τ) (hx : ∀ w, ellT M w x = 0) : x = 0 := by
  obtain ⟨F, hF, hx'⟩ := exists_finite_support x
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp (hx' F fun _ => le_rfl)
  have hy : y = 0 := eq_zero_of_ellT_map_eq_zero M (K := fun τ => F τ) (hK := hF) (fun τ => (F τ).subtype)
    (fun τ a b => rfl) y hx
  rw [hy, map_zero]

theorem inclT_injective (M : DSModel V S) : Function.Injective (inclT M) := by
  unfold inclT
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨F, hF, hy'⟩ := exists_finite_support y
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp (hy' F fun _ => le_rfl)
  have hz : z = 0 := eq_zero_of_ellT_map_eq_zero M (K := fun τ => F τ) (hK := hF)
    (fun τ => (M.sm τ).subtype ∘ₗ (F τ).subtype) (fun τ a b => rfl) z (by
      intro w
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hy, map_zero])
  rw [hz, map_zero]

theorem fr_conj_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have hPQ : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  rw [← M.fr_gram τ] at hg'
  show Formalism.REAL.inUJ (M.ε τ) _
  unfold Formalism.REAL.inUJ
  calc (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)
      = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by rw [hg']
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (M.ε τ) := by rw [hPQ]; simp

open Classical in
theorem actT_pure (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ ρ, M.H ρ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  unfold actT
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases h : ρ = τ
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem tensorLaw : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), TensorLaw M := by
  intro D V S M
  classical
  refine ⟨fun x hx => ellT_separates M x hx, inclT_injective M, ?_, ?_, ?_⟩
  · intro τ
    obtain ⟨-, -, ⟨⟨h1, -⟩, -⟩, -⟩ := M.ds τ
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
    have hr : M.rep τ 1 = 1 := by
      show M.σ τ (M.fr τ * 1 * (M.fr τ)⁻¹) = 1
      rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd, h1]
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.id_apply]
    rw [actT_pure]
    simp [hr]
  · intro τ g hg g' hg'
    obtain ⟨-, -, ⟨⟨-, hmul⟩, -⟩, -⟩ := M.ds τ
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
    have hQP : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
    have hsplit : M.fr τ * (g * g') * (M.fr τ)⁻¹ =
        (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
      calc M.fr τ * (g * g') * (M.fr τ)⁻¹ = M.fr τ * g * ((M.fr τ)⁻¹ * M.fr τ) * g' * (M.fr τ)⁻¹ := by
            rw [hQP, Matrix.mul_one, Matrix.mul_assoc (M.fr τ) g g']
        _ = _ := by simp only [Matrix.mul_assoc]
    have hr : M.rep τ (g * g') = (M.rep τ g).comp (M.rep τ g') := by
      show M.σ τ (M.fr τ * (g * g') * (M.fr τ)⁻¹) = (M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)).comp (M.σ τ (M.fr τ * g' * (M.fr τ)⁻¹))
      rw [hsplit]
      exact hmul _ (fr_conj_mem M τ hg) _ (fr_conj_mem M τ hg')
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [actT_pure, actT_pure, actT_pure, hr]
    congr 1
    simp [Function.update_idem]
  · intro τ g _ w
    obtain ⟨hc, -⟩ := M.ds τ
    haveI : CompleteSpace (M.H τ) := hc
    refine ⟨Function.update w τ (ContinuousLinearMap.adjoint (M.rep τ g) (w τ)), ?_⟩
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [actT_pure, ellT_pure, ellT_pure]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    by_cases h : ρ = τ
    · subst h
      simp [ContinuousLinearMap.adjoint_inner_left]
    · simp [Function.update_of_ne h]

end GlobalTheory.Chain.RealIt

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.PolyIso

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

theorem sgn_mul_self (x : Bool) : sgn x * sgn x = 1 := by cases x <;> simp [sgn]

variable {p q r s a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b)

def fwd : LPol b a →ₐ[ℂ] Pol p q r s :=
  aeval fun v => sgn (ε v.2) • (X (e.symm v.2, e'.symm v.1) : Pol p q r s)

def bwd : Pol p q r s →ₐ[ℂ] LPol b a :=
  aeval fun l => sgn (ε (e l.1)) • (X (e' l.2, e l.1) : LPol b a)

theorem fwd_X (c : Ix r s) (x : Ix p q) :
    fwd ε e e' (X (e' c, e x)) = sgn (ε (e x)) • (X (x, c) : Pol p q r s) := by
  simp [fwd]

def kap : LPol b a ≃ₐ[ℂ] Pol p q r s :=
  AlgEquiv.ofAlgHom (fwd ε e e') (bwd ε e e')
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨x, c⟩
      simp [fwd, bwd, smul_smul, sgn_mul_self])
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp [fwd, bwd, smul_smul, sgn_mul_self])

theorem pderiv_fwd (c : Ix r s) (x : Ix p q) (P : LPol b a) :
    pderiv (x, c) (fwd ε e e' P) = sgn (ε (e x)) • fwd ε e e' (pderiv (e' c, e x) P) := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [fwd]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P v hP =>
    obtain ⟨i, j⟩ := v
    obtain ⟨d, rfl⟩ := e'.surjective i
    obtain ⟨y, rfl⟩ := e.surjective j
    have h : pderiv (x, c) (fwd ε e e' (X (e' d, e y))) =
        sgn (ε (e x)) • fwd ε e e' (pderiv (e' c, e x) (X (e' d, e y) : LPol b a)) := by
      rw [fwd_X, Derivation.map_smul, pderiv_X, pderiv_X]
      by_cases hx : x = y
      · by_cases hc : c = d
        · subst hx hc; simp
        · simp [Ne.symm hc]
      · simp [Ne.symm hx]
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, h, hP]
    simp only [smul_eq_mul, map_add (f := _), map_mul, smul_add, mul_smul_comm]

variable {ε ε' e e'}

theorem linePos_iff (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) :
    linePos ((x, c) : Ln p q r s) = true ↔ ε' (e' c) = ε (e x) := by
  rw [h x, h' c]
  rcases x with x | x <;> rcases c with c | c <;> simp [linePos]

theorem fwd_mulX (c : Ix r s) (x : Ix p q) (P : LPol b a) :
    fwd ε e e' (sgn (ε (e x)) • (X (e' c, e x) * P)) = X (x, c) * fwd ε e e' P := by
  rw [map_smul, map_mul, fwd_X, smul_mul_assoc, smul_smul, sgn_mul_self, one_smul]

theorem fwd_rai (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) (P : LPol b a) :
    fwd ε e e' (rai ε ε' (e' c) (e x) P) = raiB (x, c) (fwd ε e e' P) := by
  unfold rai raiB
  by_cases hl : ε' (e' c) = ε (e x)
  · rw [if_pos hl, if_pos ((linePos_iff h h' x c).2 hl)]
    exact fwd_mulX c x P
  · rw [if_neg hl, if_neg (mt (linePos_iff h h' x c).1 hl)]
    simp [pderiv_fwd]

theorem fwd_low (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) (P : LPol b a) :
    fwd ε e e' (low ε ε' (e' c) (e x) P) = lowB (x, c) (fwd ε e e' P) := by
  unfold low lowB
  by_cases hl : ε' (e' c) = ε (e x)
  · rw [if_pos hl, if_pos ((linePos_iff h h' x c).2 hl)]
    simp [pderiv_fwd]
  · rw [if_neg hl, if_neg (mt (linePos_iff h h' x c).1 hl)]
    exact fwd_mulX c x P

theorem act_eq_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Mat p q →ₗ[ℂ] V) (Z : Mat p q) :
    f Z = ∑ x, ∑ y, Z x y • f (Eab x y) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]

  simp only [map_sum, ← map_smul, Eab, Matrix.smul_single, smul_eq_mul, mul_one]

theorem fwd_locS (h : SignCompat ε e) (h' : SignCompat ε' e') (Z : Mat p q) (P : LPol b a) :
    fwd ε e e' (locS ε ε' (Matrix.reindex e e Z) P) = fockAct1 p q r s Z (fwd ε e e' P) := by
  rw [act_eq_sum (fockAct1 p q r s) Z, locS, ← e.sum_comp]

  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [fockAct1_Eab, ← e'.sum_comp]

  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, Matrix.reindex_apply,
  Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [omE, LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, fwd_rai h h', fwd_low h h']
  congr 1
  by_cases hxy : x = y <;> simp [hxy]

theorem fwd_locT (h : SignCompat ε e) (h' : SignCompat ε' e') (Z : Mat r s) (P : LPol b a) :
    fwd ε e e' (locT ε ε' (Matrix.reindex e' e' Z) P) = fockAct2 p q r s Z (fwd ε e e' P) := by
  rw [act_eq_sum (fockAct2 p q r s) Z, locT, ← e'.sum_comp]

  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← e'.sum_comp]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [fockAct2_Eab, ← e.sum_comp]

  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, Matrix.reindex_apply,
  Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [omE, LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, fwd_rai h h', fwd_low h h']
  congr 1
  by_cases hcd : c = d <;> simp [hcd]

theorem exists_isPolyIso : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a)
    (e' : Ix r s ≃ Fin b), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε' e' →
    ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ :=
  fun _ _ _ _ _ _ ε _ e e' h h' =>
    ⟨(kap ε e e').toLinearEquiv, fun Z P => fwd_locS h h' Z P, fun Z P => fwd_locT h h' Z P⟩

end GlobalTheory.Chain.RealIt.PolyIso

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.typePlaceDatum_blockTriangular_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, G PP ∈ blockTri (blkOf r t) ∧ H PP ∈ blockTri (blkOf r t) ∧ upperLeftBlock ha (G PP) = upperLeftBlock hb (H PP)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G PP))) * (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (H PP)))⁻¹ * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹)) : ℂˣ) : ℂ) * omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) y := by
  first | exact @GlobalTheory.StepLaw.omegaG_blockTri_move | exact GlobalTheory.StepLaw.omegaG_blockTri_move | (intros; apply GlobalTheory.StepLaw.omegaG_blockTri_move <;> assumption)
end
