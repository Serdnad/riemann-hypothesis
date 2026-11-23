module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle058
public import ReciprocityTheory.SemistableReduction.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle415
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.StepData ValuativeRel Matrix

namespace GlobalTheory.StepData
open GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reGL_symm_mem_KO {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    (g : GL b k) : (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  have hinv : ((reGL e).symm g)⁻¹ = (reGL e).symm g⁻¹ := (map_inv _ _).symm
  rw [mem_KO, mem_KO, hinv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 (e i) (e j), fun i j => h2 (e i) (e j)⟩

variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

omit [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] in
theorem blk_ixSucc_inl {j : ℕ} (a : Ix r t j) : (ixSucc r t j (.inl a)).blk = a.blk := by
  rcases a with x | ⟨i, s⟩ <;> rfl

omit [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] in
theorem blk_ixSucc_inr {j : ℕ} (s : t) : (ixSucc r t j (.inr s)).blk = j + 1 := rfl

omit [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] in
theorem Ix.blk_le {j : ℕ} (a : Ix r t j) : a.blk ≤ j := by
  rcases a with x | ⟨i, s⟩
  · exact Nat.zero_le _
  · exact i.isLt

private theorem mem_reindex_J_iff {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (P : TypeDatum k a) (e : a ≃ b) (g : GL b k) : g ∈ (P.reindex e).J ↔ (reGL e).symm g ∈ P.J :=
  Level.mem_map

theorem mem_iter_principal (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : GL (Ix r t j) k) :
    g ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ g ∈ KO k (Ix r t j) ∧
      (∀ a b : Ix r t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧ MaxM (g.val.toBlocks₁₁ - 1) := by
  revert g
  induction j with
  | zero =>
    intro g
    rw [TypeDatum.iter_zero, mem_reindex_J_iff]
    change (reGL (ixZero r t)).symm g ∈ KOne k r ↔ _
    have e0 : ((reGL (ixZero r t)).symm g).val - 1 = g.val.toBlocks₁₁ - 1 := by
      rw [reGL_symm_val]; rfl
    constructor
    · intro hg
      refine ⟨(reGL_symm_mem_KO (ixZero r t) g).1 (KOne_le_KO hg), ?_, ?_⟩
      · intro a b hab
        exfalso
        rcases a with x | ⟨i, _⟩
        · exact Nat.not_lt_zero _ hab
        · exact i.elim0
      · rw [← e0]; exact mem_KOne.1 hg
    · rintro ⟨-, -, h1⟩
      rw [mem_KOne, e0]; exact h1
  | succ j ih =>
    intro g
    rw [TypeDatum.iter_succ, mem_reindex_J_iff, TypeDatum.step_J, TypeDatum.mem_stepJ_iff, reGL_symm_mem_KO]
    have hv : ∀ x y, ((reGL (ixSucc r t j)).symm g).val x y = g.val (ixSucc r t j x) (ixSucc r t j y) := by
      intro x y; rw [reGL_symm_val]; rfl
    constructor
    · rintro ⟨hK, ⟨g', hg', e'⟩, h21⟩
      obtain ⟨-, hlow, h11⟩ := (ih g').1 hg'
      have hg'v : ∀ x y, g'.val x y = g.val (ixSucc r t j (.inl x)) (ixSucc r t j (.inl y)) := by
        intro x y; rw [e']; exact hv (.inl x) (.inl y)
      refine ⟨hK, ?_, ?_⟩
      · intro a b hab
        obtain ⟨x, rfl⟩ := (ixSucc r t j).surjective a
        obtain ⟨y, rfl⟩ := (ixSucc r t j).surjective b
        rcases x with x | s <;> rcases y with y | s'
        · rw [← hg'v]
          rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          exact hlow x y hab
        · rw [blk_ixSucc_inr, blk_ixSucc_inl] at hab
          have := Ix.blk_le x
          omega
        · rw [← hv]; exact h21 s y
        · rw [blk_ixSucc_inr, blk_ixSucc_inr] at hab
          omega
      · have hb : g'.val.toBlocks₁₁ = g.val.toBlocks₁₁ := by
          ext i i'; exact hg'v (.inl i) (.inl i')
        rw [← hb]; exact h11
    · rintro ⟨hK, hlow, h11⟩
      have hK' : (reGL (ixSucc r t j)).symm g ∈ KO k (Ix r t j ⊕ t) := (reGL_symm_mem_KO _ g).2 hK
      have h21 : MaxM ((reGL (ixSucc r t j)).symm g).val.toBlocks₂₁ := by
        intro s y
        show valuation k (((reGL (ixSucc r t j)).symm g).val (.inr s) (.inl y)) < 1
        rw [hv]
        apply hlow
        rw [blk_ixSucc_inr, blk_ixSucc_inl]
        exact Nat.lt_succ_of_le (Ix.blk_le y)
      refine ⟨hK, ?_, h21⟩
      obtain ⟨⟨g', hg'K, e'⟩, -⟩ := exists_diag_blocks hK' h21
      refine ⟨g', (ih g').2 ⟨hg'K, ?_, ?_⟩, e'⟩
      · intro x y hxy
        rw [e']
        show valuation k (((reGL (ixSucc r t j)).symm g).val (.inl x) (.inl y)) < 1
        rw [hv]
        apply hlow
        rwa [blk_ixSucc_inl, blk_ixSucc_inl]
      · have hb : g'.val.toBlocks₁₁ = g.val.toBlocks₁₁ := by
          ext i i'
          rw [e']
          exact hv (.inl (.inl i)) (.inl (.inl i'))
        rw [hb]; exact h11

theorem lam_iter_principal (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ)
    (g : ((TypeDatum.principal k r).iter t μ hμ j).J) (d : Fin j → kˣ)
    (hd : ∀ c, (d c : k) = (Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val c).det) :
    ((TypeDatum.principal k r).iter t μ hμ j).lam g = ∏ c : Fin j, μ (c.val + 1) (d c) := by
  revert g d hd
  induction j with
  | zero =>
    intro g d hd
    rw [Fin.prod_univ_zero]
    exact (Level.map_lam (reGL (ixZero r t)) (TypeDatum.principal k r).toLevel g).trans rfl
  | succ j ih =>
    intro g d hd
    have hmem : (reGL (ixSucc r t j)).symm (g : GL (Ix r t (j + 1)) k) ∈
        ((TypeDatum.principal k r).iter t μ hμ j).stepJ t := g.2
    have hv : ∀ x y, ((reGL (ixSucc r t j)).symm (g : GL (Ix r t (j + 1)) k)).val x y =
        (g : GL (Ix r t (j + 1)) k).val (ixSucc r t j x) (ixSucc r t j y) := by
      intro x y; rw [reGL_symm_val]; rfl
    obtain ⟨-, ⟨g', hg', e'⟩, -, -, ⟨D, -, eD⟩⟩ := ((TypeDatum.principal k r).iter t μ hμ j).mem_stepJ.1 hmem
    have hstep := ((TypeDatum.principal k r).iter t μ hμ j).step_lam_eq (μ (j + 1)) (hμ _) ⟨_, hmem⟩
      ⟨g', hg'⟩ e' D eD
    have hre := Level.map_lam (reGL (ixSucc r t j))
      (((TypeDatum.principal k r).iter t μ hμ j).step t (μ (j + 1)) (hμ _)).toLevel g
    refine hre.trans (hstep.trans ?_)
    have hD : Matrix.GeneralLinearGroup.det D = d (Fin.last j) := by
      ext
      rw [hd (Fin.last j)]
      show (D : Matrix t t k).det = _
      rw [eD]
      congr 1
    rw [Fin.prod_univ_castSucc, ih ⟨g', hg'⟩ (fun c => d c.castSucc) (fun c => by
      show ((d c.castSucc : kˣ) : k) = _
      rw [hd c.castSucc]
      congr 1
      ext s s'
      show (g : GL (Ix r t (j + 1)) k).val (.inr (c.castSucc, s)) (.inr (c.castSucc, s')) =
        g'.val (.inr (c, s)) (.inr (c, s'))
      rw [e']
      exact (hv (.inl (.inr (c, s))) (.inl (.inr (c, s')))).symm), hD]
    simp only [Fin.val_castSucc, Fin.val_last]

theorem iter_principal_spec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, GlobalTheory.SplitWeil.IsTame (μ j)) (j : ℕ), (∀ g : GL (Ix r t j) k, g ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ g ∈ GlobalTheory.SplitWeil.KO k (Ix r t j) ∧ (∀ a b : Ix r t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧ MaxM (g.val.toBlocks₁₁ - 1)) ∧ ∀ (g : ((TypeDatum.principal k r).iter t μ hμ j).J) (d : Fin j → kˣ), (∀ c, (d c : k) = (Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val c).det) → ((TypeDatum.principal k r).iter t μ hμ j).lam g = ∏ c : Fin j, μ (c.val + 1) (d c) :=
  fun μ hμ j => ⟨fun g => mem_iter_principal μ hμ j g, fun g d hd => lam_iter_principal μ hμ j g d hd⟩

end GlobalTheory.StepData
end

section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.HopfQuot

section
variable {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]

theorem ev_mulRight_comul_of_primitive (l : Λ →ₗ[R] R)
    (hl : ∀ x, ev Λ l (Coalgebra.comul x) = algebraMap R Λ (l x)) (b : Λ)
    (hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) (u : Λ) :
    ev Λ (l ∘ₗ LinearMap.mulRight R b) (Coalgebra.comul u) =
      l (u * b) • (1 : Λ) - l u • b := by
  have h1 : ∀ w : Λ ⊗[R] Λ, ev Λ l (w * (b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b)) =
      ev Λ l w * b + ev Λ (l ∘ₗ LinearMap.mulRight R b) w := by
    intro w
    induction w with
    | add u v hu hv =>
      simp only [add_mul, map_add (f := _), hu, hv]
      ring
    | tmul u v => simp [mul_add]
  have h2 := hl (u * b)
  rw [Bialgebra.comul_mul, hb, h1, hl, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] at h2
  rw [← h2]
  ring

theorem coact_ev_mulRight_of_primitive (ρ : B →ₐ[R] B ⊗[R] Λ)
    (hassoc : ∀ a, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ a)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ a))
    (l : Λ →ₗ[R] R) (hl : ∀ x, ev Λ l (Coalgebra.comul x) = algebraMap R Λ (l x)) (b : Λ)
    (hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) (f : B) :
    ρ (ev B (l ∘ₗ LinearMap.mulRight R b) (ρ f)) =
      ev B (l ∘ₗ LinearMap.mulRight R b) (ρ f) ⊗ₜ[R] 1 - ev B l (ρ f) ⊗ₜ[R] b := by
  set l' := l ∘ₗ LinearMap.mulRight R b with hl'
  let F : B ⊗[R] (Λ ⊗[R] Λ) →ₗ[R] B ⊗[R] Λ := ((ev Λ l').restrictScalars R).lTensor B
  have h1 : ∀ w : B ⊗[R] Λ, ρ (ev B l' w) =
      F (TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ w)) := by
    intro w
    induction w with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a b =>
      rw [ev_tmul, map_smul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      generalize ρ a = w
      induction w with
      | add u v hu hv => simp only [map_add (f := _), smul_add, add_tmul, hu, hv]
      | tmul u v => simp [F]
  have h2 : ∀ w : B ⊗[R] Λ, F ((Coalgebra.comul (R := R)).lTensor B w) =
      ev B l' w ⊗ₜ 1 - ev B l w ⊗ₜ b := by
    intro w
    induction w with
    | add a c ha hc =>
      simp only [map_add (f := _), add_tmul, ha, hc]
      abel
    | tmul a c =>
      have := ev_mulRight_comul_of_primitive l hl b hb c
      rw [← hl'] at this
      simp only [F, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, this, ev_tmul,
        tmul_sub, smul_tmul]
      rfl
  rw [h1, hassoc, h2]

end

theorem exists_coact_eq_add_of_primitive : ∀ {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] B ⊗[R] Λ), (∀ a, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ a)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ a)) → (∀ a, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ a)) = a) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) → ∀ b : Λ, cobOne R Λ b = 0 → ∃ x : B, ρ x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  intro R Λ B _ _ _ _ _ _ _ ρ hassoc hcounit hsurj b hb0
  have hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb0
    exact hb0
  obtain ⟨-, -, hff, -⟩ := finite_faithfullyFlat_ker ρ hassoc hcounit hsurj
  set B₀ := AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) with hB₀
  let I : Ideal B₀ :=
    { carrier := {y | ∃ x : B, ρ x = x ⊗ₜ[R] 1 + (y : B) ⊗ₜ[R] b}
      add_mem' := by
        rintro y z ⟨x, hx⟩ ⟨x', hx'⟩
        refine ⟨x + x', ?_⟩
        rw [map_add (f := _), hx, hx', Subalgebra.coe_add, add_tmul, add_tmul]
        abel
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro t y ⟨x, hx⟩
        have ht : ρ t = (t : B) ⊗ₜ 1 := t.2
        refine ⟨t * x, ?_⟩
        rw [map_mul, ht, hx]
        simp [mul_add] }
  obtain ⟨n, l, T, hl, hT⟩ := exists_integrals R Λ
  have hmem : ∀ k f, ev B (l k) (ρ f) ∈ I.map (algebraMap B₀ B) := by
    intro k f
    refine Ideal.mem_map_of_mem (algebraMap B₀ B)
      (x := ⟨ev B (l k) (ρ f), ev_mem_equalizer ρ hassoc _ (hl k) f⟩) ?_
    refine ⟨-ev B (l k ∘ₗ LinearMap.mulRight R b) (ρ f), ?_⟩
    rw [map_neg, coact_ev_mulRight_of_primitive ρ hassoc _ (hl k) b hb, neg_tmul]
    abel
  have hall : ∀ k z, ev B (l k) z ∈ I.map (algebraMap B₀ B) := by
    intro k z
    obtain ⟨w, rfl⟩ := hsurj z
    induction w with
    | add u v hu hv =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hu hv
    | tmul u v =>
      have : (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) u * ρ v = u • ρ v := by
        rw [Algebra.smul_def]
        rfl
      rw [Algebra.TensorProduct.productMap_apply_tmul, this, map_smul]
      exact Ideal.mul_mem_left _ _ (hmem k v)
  have h1 : (1 : B) ∈ I.map (algebraMap B₀ B) := by
    have : (1 : B) = ∑ k, ev B (l k) (1 ⊗ₜ T k) := by
      have h := hT 1
      simp only [mul_one, Bialgebra.counit_one] at h
      simp [← Finset.sum_smul, h]
    rw [this]
    exact Ideal.sum_mem _ fun k _ => hall k _
  have h2 : (1 : B₀) ∈ I := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) I, Ideal.mem_comap, map_one]
    exact h1
  exact h2

end GlobalTheory.HopfQuot
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.affineHilbertSchemeFunctor_isSheaf_zariski : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ), Presieve.IsSheaf Scheme.zariskiTopology (GlobalTheory.HilbAff.functor A B r) := by
  first | (exact @GlobalTheory.HilbAff.isSheaf_functor) | (exact GlobalTheory.HilbAff.isSheaf_functor) | (intros; apply GlobalTheory.HilbAff.isSheaf_functor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

theorem _root_.GlobalTheory.T.isHilbertSchemeRepresentable_of_open_cover : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsHilbRep (z ∣_ W) r) → IsHilbRep z r := by
  first | (exact @GlobalTheory.HilbGlue.isHilbRep_of_cover) | (exact GlobalTheory.HilbGlue.isHilbRep_of_cover) | (intros; apply GlobalTheory.HilbGlue.isHilbRep_of_cover <;> assumption)
end

section

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

theorem _root_.GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace : ∀ (n : ℕ), 0 < n → MeasurePreserving (fun p : UnitSphereC n × Ioi (0:ℝ) => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n))) ((sphereProb n).prod (radProb n)) (gaussProb n) := by
  first | exact @GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb | exact GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb | (intros; apply GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb <;> assumption)
end

section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

namespace GlobalTheory.DiagVol

theorem rowElt_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k),
    (∀ s, y s ∈ 𝒪[k]) → (∀ s, ¬ ordL c t < ordL c s → y s = 0) →
    ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0) := by
  intro k _ _ _ _ n _ _ c t y hy h0
  set E : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of (fun r s => if r = t then y s else 0) with hE
  have yt : y t = 0 := h0 t (lt_irrefl _)
  have hEE : E * E = 0 := by
    ext r s
    simp [hE, Matrix.mul_apply, yt]
  have h1 : (1 + E) * (1 - E) = 1 := by
    simp only [add_mul, mul_sub, one_mul, mul_one, hEE]; abel
  have h2 : (1 - E) * (1 + E) = 1 := by
    simp only [sub_mul, mul_add, one_mul, mul_one, hEE]; abel
  let M : GL (n ⊕ Fin c) k := ⟨1 + E, 1 - E, h1, h2⟩
  refine ⟨M, Subgroup.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
  · have key : ∀ p, (∀ s, lev p s ≤ lev p t → y s = 0) → M ∈ N k n c p := by
      intro p hp
      rw [Model.mem_N_iff]
      intro r s hrs
      show (1 + E) r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
      rw [Matrix.add_apply, hE, Matrix.of_apply]
      split_ifs with hr
      · subst hr; rw [hp s hrs, add_zero]
      · rw [add_zero]
    unfold symN
    rcases t with x | i
    · refine Subgroup.mem_sup_left (key _ fun s hs => h0 s ?_)
      rcases s with z | j <;> simp [ordL, lev] at hs ⊢ <;> omega
    · refine Subgroup.mem_sup_right (key _ fun s hs => h0 s ?_)
      rcases s with z | j <;> simp [ordL, lev] at hs ⊢ <;> omega
  · rw [mem_KO_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      simp only [Matrix.add_apply, hE, Matrix.of_apply, Matrix.one_apply]
      refine add_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hy _
    · show (1 - E) i j ∈ 𝒪[k]
      simp only [Matrix.sub_apply, hE, Matrix.of_apply, Matrix.one_apply]
      refine sub_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hy _

end GlobalTheory.DiagVol
end

section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

namespace GlobalTheory.DiagVol

theorem colE_mem_symN_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (t : n ⊕ Fin c) (y : n ⊕ Fin c → k) (hy : ∀ r, y r ∈ 𝒪[k])
    (hz : ∀ r, ¬ ordL c r < ordL c t → y r = 0) :
    ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c),
      x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0) := by
  set E : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of (fun r s => if s = t then y r else 0) with hE
  have hyt : y t = 0 := hz t (lt_irrefl _)
  have hEE : E * E = 0 := by
    ext r s
    simp only [hE, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [Finset.sum_eq_single t]
    · simp [hyt]
    · intro u _ hu; simp [hu]
    · intro h; exact absurd (Finset.mem_univ t) h
  have h1 : (1 + E) * (1 - E) = 1 := by
    have : (1 + E) * (1 - E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  have h2 : (1 - E) * (1 + E) = 1 := by
    have : (1 - E) * (1 + E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  let x : GL (n ⊕ Fin c) k := ⟨1 + E, 1 - E, h1, h2⟩
  have hone : ∀ i j : n ⊕ Fin c, (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hEi : ∀ i j, E i j ∈ 𝒪[k] := by
    intro i j
    simp only [hE, Matrix.of_apply]
    split_ifs
    · exact hy i
    · exact zero_mem _
  have hInN : ∀ p : ℕ, (∀ r, y r ≠ 0 → lev p r < lev (n := n) (c := c) p t) → InN p x := by
    intro p hp r s hrs
    show (1 + E) r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
    rw [Matrix.add_apply, add_eq_left]
    simp only [hE, Matrix.of_apply]
    split_ifs with h
    · subst h
      by_contra hne
      exact absurd hrs (not_le.2 (hp r hne))
    · rfl
  refine ⟨x, Subgroup.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
  · show x ∈ N k n c ((c + 1) / 2) ⊔ N k n c (c / 2 + 1)
    cases t with
    | inr j =>
      refine Subgroup.mem_sup_left (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))
      have hlt : ordL c r < ordL c (Sum.inr j : n ⊕ Fin c) := by
        by_contra h; exact hr (hz r h)
      cases r with
      | inl a => simp [ordL, lev] at hlt ⊢; omega
      | inr i => simp [ordL, lev] at hlt ⊢; omega
    | inl a0 =>
      refine Subgroup.mem_sup_right (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))
      have hlt : ordL c r < ordL c (Sum.inl a0 : n ⊕ Fin c) := by
        by_contra h; exact hr (hz r h)
      cases r with
      | inl a => simp [ordL, lev] at hlt ⊢
      | inr i => simp [ordL, lev] at hlt ⊢; omega
  · refine (mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      rw [Matrix.add_apply]; exact add_mem (hone i j) (hEi i j)
    · show (1 - E) i j ∈ 𝒪[k]
      rw [Matrix.sub_apply]; exact sub_mem (hone i j) (hEi i j)

end GlobalTheory.DiagVol
end
